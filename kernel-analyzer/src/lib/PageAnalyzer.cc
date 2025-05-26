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
#include "PageAnalyzer.h"
#include <cctype> // Added for std::isdigit

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
        for (auto sf: KeyStructField) {
            // Compare base name with sf.first
            if (indices.front() == sf.second && currentStructNameBase == sf.first) {
                lastMatchedKeyStructName = sf.first.str();
                return true;
            }
        }
    } else {
        int field = indices.front();
        indices.pop_front();
        if (field < 0 || st->getNumElements() <= field)
            return false;
        return isKeyStruct(dyn_cast_or_null<StructType>(st->getElementType(field)), indices);
    }
    return false;
}



bool PageAnalyzerPass::doModulePass(Module *M) {
    for (auto &F : *M) {
        for (auto i = inst_begin(F), e = inst_end(F); i != e; i++) {
          Instruction *I = &*i;
        //   // you can remove this if needed
        //   // First: find page allocation location
        //   if (auto CI = dyn_cast_or_null<CallInst>(I)) {
        //     Function *callee = CI->getCalledFunction();
        //     if (callee && isPageAllocator(callee))
        //         Ctx->pageAllocation.insert(callee);
        //   }

          // Second: find store instructions that store to certain struct field
          if (auto gep = dyn_cast_or_null<GetElementPtrInst>(I)) {
            Type * source = gep->getSourceElementType();
            Indices indices; // Will contain all GEP indices initially
            get_gep_indicies(gep, indices);
            
            if (indices.empty()) { // Should have at least one index for the base pointer
                continue;
            }
            indices.pop_front(); // Remove the 0th GEP index (for the base pointer itself)
                                 // 'indices' now contains only the field/element indices.

            if (ArrayType *arr = dyn_cast_or_null<ArrayType>(source)) {
                source = arr->getArrayElementType();
            }
            StructType *st = dyn_cast_or_null<StructType>(source);

            if (!st) { // isKeyStruct expects a valid starting struct type
                continue;
            }

            // Create a copy of 'indices' to pass to isKeyStruct,
            // because isKeyStruct modifies its Indices argument (by calling pop_front).
            Indices indices_for_call = indices; 
            if(isKeyStruct(st, indices_for_call)) {
                errs() << "Found GEP for a key struct field in Func [" << gep->getFunction()->getName() << "]: " << *gep << "\n";
                if (usedInStore(gep)) {
                     // the current version does not add the resitriction
                    //  should we add the restriction? the source operand should come from the page allocator?
                    // errs() << "Found GEP for a key struct field in Func [" << gep->getFunction()->getName() << "]: " << *gep << "\n";
                    errs() << "  -> Key Struct Name: " << lastMatchedKeyStructName << "\n";
                    Function *targetFunc = gep->getFunction();
                    bool inserted = Ctx->pageAllocation.insert(targetFunc).second;
                    if (inserted) {
                        errs() << "  -> Added function to pageAllocation: " << targetFunc->getName() << "\n\n";
                    } else {
                        errs() << "  -> Function already in pageAllocation: " << targetFunc->getName() << "\n";
                    }
                }      
            }
               
          }
        }
    }
    return false;
}

bool PageAnalyzerPass::doFinalization(Module *M) {
    return false;
}