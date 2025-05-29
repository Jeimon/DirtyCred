#include "GlobalCtx.h"
#include "StructAnalyzer.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h" // For errs()
#include "PageAnalyzer.h"
#include <cctype> // Added for std::isdigit
#include <list> // For std::list in findStoresToMemoryPointedBy
#include <map>
#include <set>

using namespace llvm;

std::string lastMatchedKeyStructName;

// only care about case where all indices are constantint
void get_gep_indicies(GetElementPtrInst *gep, Indices &indices) {
    if (!gep)
      return;
    // replace all non-constant with zero
    // because they are literally an array...
    // and we are only interested in the type info
    for (auto i = gep->idx_begin(); i != gep->idx_end(); ++i) {
      ConstantInt *idc = dyn_cast_or_null<ConstantInt>(i);
      if (idc)
        indices.push_back(idc->getSExtValue());
      else
        indices.push_back(0);
    }
  }

static std::string getBaseNameIfSuffixedString(Function *F) {
    if (!F) return "";
    StringRef fullName = F->getName();
    size_t dotPos = fullName.rfind('.');
    // Ensure dot is present, not the first character, and there's something after it.
    if (dotPos != StringRef::npos && dotPos > 0 && dotPos < fullName.size() - 1) {
        StringRef suffix = fullName.substr(dotPos + 1);
        bool allDigits = !suffix.empty(); // Suffix must not be empty
        for (char c : suffix) {
            if (!isdigit(c)) {
                allDigits = false;
                break;
            }
        }
        if (allDigits) {
            return fullName.substr(0, dotPos).str();
        }
    }
    return ""; // Not suffixed in the .NNNN pattern or doesn't meet criteria.
}


bool isPageAllocator (Function *func) {
    std::string name = func->getName().str();
    // page alloc
	if (!name.compare("__get_free_pages") ||
    !name.compare("get_zeroed_page"))
        return true;

    if (!name.compare("__alloc_pages_nodemask") ||
        !name.compare("__alloc_pages") ||
        !name.compare("alloc_pages_current") ||
        !name.compare("alloc_pages") ||
        !name.compare("alloc_pages_vma"))
        return true;

    if (!name.compare("kbase_mem_pool_alloc_pages"))
        return true;

    if (!name.compare("alloc_pages_node") ||
        !name.compare("alloc_pages_exact_node") ||
        !name.compare("alloc_pages_exact") ||
        !name.compare("alloc_pages_exact_nid"))
        return true;

    // pagemap
    if (!name.compare("__page_cache_alloc"))
        return true;

    if (!name.compare("find_or_create_page"))
        return true;
    return false;
}



bool usedInStore(GetElementPtrInst *gep) {
    ValueList worklist;
    ValueSet visited;
    worklist.push_back(gep);
    Value *po;

    while(worklist.size()) {
        po = worklist.front();
        worklist.pop_front();
        if (visited.find(po) != visited.end())
            continue;
        visited.insert(po);

        for (auto user : gep->users()) {
            if (ConstantExpr *cxpr = dyn_cast_or_null<ConstantExpr>(user)) {
                Instruction *cxpri = cxpr->getAsInstruction();
                worklist.push_back(cxpri);
                continue;
            }
            else if (Instruction *i = dyn_cast_or_null<Instruction>(user)) {
                switch (i->getOpcode()) {
                    case (Instruction::PHI):
                    case (BitCastInst::BitCast):
                    case (Instruction::IntToPtr):
                    case (Instruction::PtrToInt): {
                        worklist.push_back(i);
                    }
                    case (Instruction::Store): {
                        return true;
                    }
                }
            }
        }
    }
    return false;
}

bool PageAnalyzerPass::doInitialization(Module *M) {
    return false;
}

// Helper function to get base struct name if suffixed (e.g., struct.name.123 -> struct.name)
static std::string getBaseStructName(llvm::StringRef fullName) {
    if (fullName.empty()) return "";
    size_t dotPos = fullName.rfind('.');
    // Check if there's a dot, it's not the first char, and there's something after it
    if (dotPos != llvm::StringRef::npos && dotPos > 0 && dotPos < fullName.size() - 1) {
        llvm::StringRef suffix = fullName.substr(dotPos + 1);
        bool suffixIsNumeric = !suffix.empty();
        for (char c : suffix) {
            if (!std::isdigit(c)) {
                suffixIsNumeric = false;
                break;
            }
        }
        if (suffixIsNumeric) {
            return fullName.substr(0, dotPos).str(); // Return part before dot
        }
    }
    return fullName.str(); // Return full name if no recognized numeric suffix
}

bool PageAnalyzerPass::isKeyStruct(StructType *st, Indices &indices) {
    if (st == nullptr || indices.size() == 0)
        return false;

    if (indices.size() ==  1) {
        std::string currentStructNameBase = getBaseStructName(st->getStructName());
        for (auto const& sf: KeyStructField) {
            if (indices.front() == sf.second && currentStructNameBase == sf.first.str()) {
                this->currentMatchedKeyStructName = sf.first.str();
                this->currentMatchedKeyStructFieldIndex = sf.second;
                return true;
            }
        }
    } else {
        int field = indices.front();
        Indices next_indices = indices;
        next_indices.pop_front();
        
        if (field < 0 || st->getNumElements() <= static_cast<unsigned>(field))
            return false;
        
        StructType *nextSt = dyn_cast_or_null<StructType>(st->getElementType(field));
        if (nextSt) {
            return isKeyStruct(nextSt, next_indices);
        }
    }
    return false;
}

// 新实现的辅助方法，用于 KeyStructField GEP 分析
void PageAnalyzerPass::analyzeKeyStructFieldGEPs(llvm::Module *M) {
    for (auto &F : *M) {
        if (!F.hasName()) continue;
        for (auto i = inst_begin(F), e = inst_end(F); i != e; i++) {
            Instruction *I = &*i;

            if (auto gep = dyn_cast_or_null<GetElementPtrInst>(I)) {
                Type * source = gep->getSourceElementType();
                Indices indices; 
                get_gep_indicies(gep, indices);
                
                if (indices.empty()) { 
                    continue;
                }
                indices.pop_front(); 

                if (ArrayType *arr = dyn_cast_or_null<ArrayType>(source)) {
                    source = arr->getArrayElementType();
                }
                StructType *st = dyn_cast_or_null<StructType>(source);

                if (!st || !st->hasName()) { 
                    continue;
                }

                Indices indices_for_call = indices; 
                
                this->currentMatchedKeyStructName = "";
                this->currentMatchedKeyStructFieldIndex = -1;

                if(isKeyStruct(st, indices_for_call)) {
                    Function* gepFunc = gep->getFunction();
                    std::string gepFuncBaseName = getBaseNameIfSuffixedString(gepFunc); 
                    std::string effectiveGepFuncName = !gepFuncBaseName.empty() ? gepFuncBaseName : (gepFunc ? gepFunc->getName().str() : "UNKNOWN_FUNCTION");

                    errs() << "Found GEP for a key struct field in Func [" << effectiveGepFuncName << "]: " << *gep << "\n";
                    
                    if (usedInStore(gep)) {
                        errs() << "  -> This GEP is used in a store operation.\n";
                        errs() << "  -> Key Struct Name (from match): " << this->currentMatchedKeyStructName << "\n"; 
                        
                        Function *targetFunc = gep->getFunction(); 
                        bool inserted = Ctx->pageAllocation.insert(targetFunc).second;
                        if (inserted) {
                            errs() << "  -> Added function to pageAllocation: " << effectiveGepFuncName << "\n\n";
                        } else {
                            errs() << "  -> Function already in pageAllocation: " << effectiveGepFuncName << "\n";
                        }
                    }      
                }
            }
        }
    }
}

bool PageAnalyzerPass::doModulePass(Module *M) {

    
    return false; 
}

void PageAnalyzerPass::findAllocationTypeSources(llvm::Module *M) {
    std::map<int64_t, std::set<std::string>> typeToTargetFunctions;
    const int KBASE_ALLOC_CREATE_ARG_INDEX = 2;

    for (auto &FuncIter : *M) { 
        Function &F = FuncIter; 
        if (!F.hasName()) continue;

        for (auto i = inst_begin(F), e = inst_end(F); i != e; ++i) {
            Instruction *I = &*i;
            if (auto CI = dyn_cast_or_null<CallInst>(I)) {
                Function *callee = CI->getCalledFunction();
                if (callee && callee->hasName()) {
                    std::string calleeBaseName = getBaseNameIfSuffixedString(callee);
                    std::string effectiveCalleeName = !calleeBaseName.empty() ? calleeBaseName : callee->getName().str();

                    if (effectiveCalleeName == "kbase_alloc_create") {
                        if (CI->arg_size() > KBASE_ALLOC_CREATE_ARG_INDEX) {
                            Value *typeArg = CI->getArgOperand(KBASE_ALLOC_CREATE_ARG_INDEX);
                            if (auto *constInt = dyn_cast<ConstantInt>(typeArg)) {
                                int64_t memType = constInt->getSExtValue();
                                
                                std::list<Function *> worklist;
                                std::set<Function *> visitedPath; 

                                if (F.hasName()) { 
                                   worklist.push_back(&F);
                                }
                                
                                errs() << "DEBUG: Found call to kbase_alloc_create by Func [" << F.getName().str() 
                                       << "] with Type: " << memType << ". Starting reverse trace...\n"; 

                                std::string initialCallerName = F.getName().str(); 

                                while(!worklist.empty()) {
                                    Function *currentFunc = worklist.front();
                                    worklist.pop_front();

                                    if (!currentFunc || !currentFunc->hasName() || visitedPath.count(currentFunc)) {
                                        continue;
                                    }
                                    visitedPath.insert(currentFunc);
                                    
                                    std::string currentFuncBaseName = getBaseNameIfSuffixedString(currentFunc);
                                    std::string effectiveCurrentFuncName = !currentFuncBaseName.empty() ? currentFuncBaseName : currentFunc->getName().str();
                                    
                                    if (effectiveCurrentFuncName != initialCallerName) { 
                                        errs() << "  DEBUG: Tracing path... -> " << effectiveCurrentFuncName << "\n";
                                    }

                                    bool isTargetFunction = false; // Flag to check if currentFunc is one of the targets
                                    if (effectiveCurrentFuncName == "kbase_mem_alias" ||
                                        effectiveCurrentFuncName == "kbase_mem_import" ||
                                        effectiveCurrentFuncName == "kbase_mem_alloc") {
                                        
                                        errs() << "    DEBUG: Found Target! Path leads to: " << effectiveCurrentFuncName 
                                               << " (Original kbase_alloc_create caller: " << initialCallerName 
                                               << ", Type: " << memType << ")\n";
                                        typeToTargetFunctions[memType].insert(effectiveCurrentFuncName);
                                        isTargetFunction = true; // Set the flag
                                    }

                                    // 如果当前函数是目标函数之一，则停止从此函数继续向上追踪
                                    if (isTargetFunction) {
                                        continue; // Skip finding callers for this target function
                                    }

                                    // 如果不是目标函数，则继续查找其调用者
                                    if (Ctx) { 
                                        auto it = Ctx->Callers.find(currentFunc);
                                        if (it != Ctx->Callers.end()) {
                                            const CallInstSet &callersOfCurrentFunc = it->second;
                                            for (CallInst *callerCI : callersOfCurrentFunc) {
                                                Function *callerFunc = callerCI->getFunction(); 
                                                if (callerFunc && callerFunc->hasName() && !visitedPath.count(callerFunc)) {
                                                    worklist.push_back(callerFunc);
                                                }
                                            }
                                        }
                                        llvm::Module *Mod = currentFunc->getParent();
                                        if (Mod) {
                                            if (!currentFuncBaseName.empty()) { 
                                                Function *baseFunc = Mod->getFunction(currentFuncBaseName);
                                                if (baseFunc && baseFunc != currentFunc) {
                                                    auto itBase = Ctx->Callers.find(baseFunc);
                                                    if (itBase != Ctx->Callers.end()) {
                                                        for (CallInst *ci_from_base : itBase->second) { 
                                                            Function *cf = ci_from_base->getFunction(); 
                                                            if (cf && cf->hasName() && !visitedPath.count(cf)) {
                                                                worklist.push_back(cf);
                                                            }
                                                        }
                                                    }
                                                }
                                            } else { 
                                                StringRef funcNameRef = currentFunc->getName();
                                                for (Function &SuffixedF : *Mod) {
                                                    if (!SuffixedF.hasName() || &SuffixedF == currentFunc) continue;
                                                    std::string baseOfSuffixed = getBaseNameIfSuffixedString(&SuffixedF);
                                                    if (!baseOfSuffixed.empty() && baseOfSuffixed == funcNameRef.str()) {
                                                        auto itSuffixed = Ctx->Callers.find(&SuffixedF);
                                                        if (itSuffixed != Ctx->Callers.end()) {
                                                            for (CallInst *ci_from_suffixed : itSuffixed->second) { 
                                                                Function *cf = ci_from_suffixed->getFunction(); 
                                                                if (cf && cf->hasName() && !visitedPath.count(cf)) {
                                                                    worklist.push_back(cf);
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                } 
                                if (visitedPath.size() > 1 && worklist.empty()) { 
                                     errs() << "  DEBUG: End of trace for kbase_alloc_create called by " << initialCallerName << " (Type: " << memType << ")\n\n"; 
                                } else if (worklist.empty() && 
                                           !typeToTargetFunctions.count(memType)) { // Check if memType key exists
                                     // If worklist is empty and NO target was found for this memType during this specific trace initiated by initialCallerName
                                     // This condition might be tricky if multiple kbase_alloc_create calls share the same memType
                                     // A more precise check would be if a flag specific to *this trace* indicates a target was found.
                                     // For now, this means if the global map for this memType is still empty after this trace, it implies no target found *by this trace if it was the first for this type*.
                                     errs() << "  DEBUG: Trace for " << initialCallerName << " (Type: " << memType << ") did not reach any target.\n\n";
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // 打印结果
    errs() << "\n--- Allocation Type to Target Function Analysis ---\n";
    if (typeToTargetFunctions.empty()) {
        errs() << "No allocation type to target function paths found.\n";
    } else {
        for (auto const& [typeVal, funcNames] : typeToTargetFunctions) {
            std::string typeStr;
            switch (typeVal) {
                case 0: typeStr = "KBASE_MEM_TYPE_NATIVE"; break;
                case 1: typeStr = "KBASE_MEM_TYPE_IMPORTED_UMM"; break;
                case 2: typeStr = "KBASE_MEM_TYPE_IMPORTED_USER_BUF"; break;
                case 3: typeStr = "KBASE_MEM_TYPE_ALIAS"; break;
                default: typeStr = "UNKNOWN_TYPE (" + std::to_string(typeVal) + ")"; break;
            }
            errs() << "Memory Type: " << typeStr << " can reach:\n";
            for (const auto& funcName : funcNames) {
                errs() << "  -> " << funcName << "\n";
            }
        }
    }
    errs() << "--- End of Analysis ---\n\n";
}

bool PageAnalyzerPass::doFinalization(Module *M) {
    return false;
}