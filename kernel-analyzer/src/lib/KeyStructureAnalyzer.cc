#include "KeyStructureAnalyzer.h"
#include "GlobalCtx.h"      // For GlobalContext, Ctx->Callers
#include "Annotation.h"     // For RES_REPORT

#include <llvm/IR/Instructions.h>
#include <llvm/IR/Argument.h>
#include <llvm/IR/GlobalValue.h>
#include <llvm/IR/InstIterator.h> // For instructions()
#include <llvm/Support/raw_ostream.h>
#include <llvm/ADT/StringRef.h>
#include <queue> // For std::queue in backwardTrace
#include <ctype.h> // For isdigit

using namespace llvm;

// Helper function to get base name if suffixed (e.g., func.123 -> func)
// Copied and adapted from CallGraph.cc
static std::string getBaseNameIfSuffixedString(llvm::Function *F) {
    if (!F) return "";
    StringRef fullName = F->getName();
    size_t dotPos = fullName.rfind('.');
    if (dotPos != StringRef::npos && dotPos > 0 && dotPos < fullName.size() - 1) {
        StringRef suffix = fullName.substr(dotPos + 1);
        bool allDigits = !suffix.empty();
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
    return ""; // Not suffixed or doesn't meet criteria, return empty or consider returning full name
}

KeyStructureAnalyzer::KeyStructureAnalyzer(GlobalContext* Ctx) : Ctx(Ctx) {}

void KeyStructureAnalyzer::analyzePathForKeyStructures(
    llvm::Function* targetFunction,
    const std::vector<llvm::Function*>& callPath,
    llvm::Function* entryPointFunction,
    const std::string& pathIdentifierString
) {
    if (!targetFunction) {
        RES_REPORT("  Error in KeyStructureAnalyzer: Target function is null for path: " << pathIdentifierString << "\n");
        return;
    }

    std::set<llvm::Value*> pathKeyStructures;
    bool analysis_was_attempted = false;

    // --- Mode Check: Local analysis or path analysis? ---
    bool is_local_analysis = (!callPath.empty() && callPath.size() == 1 && callPath[0] == targetFunction);

    if (is_local_analysis) {
        // --- Perform local-only analysis for mgm_vmf_insert_pfn_prot ---
        RES_REPORT("\n  Performing in-function analysis for: " << targetFunction->getName().str() << "\n");
        bool call_found = false;
        for (Instruction &I : instructions(*targetFunction)) {
            if (CallInst *CI = dyn_cast<CallInst>(&I)) {
                if (!CI->isIndirectCall()) continue;
                if (auto *LI = dyn_cast<LoadInst>(CI->getCalledOperand())) {
                    if (auto *GEP = dyn_cast<GetElementPtrInst>(LI->getPointerOperand())) {
                        llvm::Type* srcElemType = GEP->getSourceElementType();
                        if (auto *ST = dyn_cast<StructType>(srcElemType)) {
                            if (ST->hasName() && ST->getName().contains("struct.memory_group_manager_device")) {
                                if (GEP->getNumIndices() == 3) {
                                    auto* idx2 = dyn_cast<ConstantInt>(GEP->getOperand(2));
                                    auto* idx3 = dyn_cast<ConstantInt>(GEP->getOperand(3));
                                    if (idx2 && idx2->getZExtValue() == 0 && idx3 && idx3->getZExtValue() == 5) {
                                        if (CI->arg_size() > 4) {
                                            analysis_was_attempted = true;
                                            call_found = true;
                                            llvm::Value* fifth_arg = CI->getArgOperand(4);
                                            RES_REPORT("    Found indirect call. Tracing 5th argument locally...\n");
                                            backwardTraceForKeyStructure(fifth_arg, pathIdentifierString, pathKeyStructures, callPath, entryPointFunction);
                                            goto local_analysis_reporting;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        local_analysis_reporting:;
        if (!call_found) {
            RES_REPORT("    Warning: Did not find expected indirect call in " << targetFunction->getName().str() << "\n");
        }
    } else {
        // --- Original full-path analysis logic ---
        if (callPath.empty() || !entryPointFunction) {
             RES_REPORT("  Error in KeyStructureAnalyzer: Call path is empty or entry point function is null for path: " << pathIdentifierString << "\n");
            return;
        }

        unsigned arg_idx_to_analyze = 3; // Default to 4th argument (0-indexed)
        unsigned min_args_required = 4;  // Default requirement for 4th argument
        std::string arg_description_str = "4th";

        std::string funcNameStr = targetFunction->getName().str();
        if (funcNameStr == "kbase_mmu_insert_single_page") {
            arg_idx_to_analyze = 2; // Analyze 3rd argument
            min_args_required = 3;  // Min args for 3rd argument
            arg_description_str = "3rd";
        }

        if (targetFunction->arg_size() >= min_args_required) {
            analysis_was_attempted = true;
            llvm::Argument* targetArgument = nullptr;
            unsigned current_arg_idx = 0;
            for (llvm::Argument &arg : targetFunction->args()) {
                if (current_arg_idx == arg_idx_to_analyze) {
                    targetArgument = &arg;
                    break;
                }
                current_arg_idx++;
            }

            if (targetArgument) {
                std::string targetArgNameStr = targetArgument->hasName() ? targetArgument->getName().str() : "unnamed_arg";
                RES_REPORT("  Analyzing origin of " << arg_description_str << " argument ('" << targetArgNameStr << "') for root interface: " << funcNameStr << " in path: " << pathIdentifierString << "\n");
                backwardTraceForKeyStructure(targetArgument, pathIdentifierString, pathKeyStructures, callPath, entryPointFunction);
            } else {
                RES_REPORT("  Error: Could not retrieve " << arg_description_str << " argument for root interface: " << funcNameStr << " (expected index " << arg_idx_to_analyze << ", " << targetFunction->arg_size() << " args available)\n");
            }
        } else {
            RES_REPORT("  Root interface " << funcNameStr << " has " << targetFunction->arg_size() << " arguments (fewer than " << min_args_required << "). Skipping Key structure analysis for " << arg_description_str << " arg.\n");
        }
    }

    if (!pathKeyStructures.empty()) {
        RES_REPORT("    Potential Key Structures identified for path '" << pathIdentifierString << "':\n");
        for (llvm::Value* val : pathKeyStructures) {
            std::string valStr;
            llvm::raw_string_ostream rso(valStr);
            val->print(rso);
            
            llvm::Type* valType = val->getType();
            std::string typeStr;
            llvm::raw_string_ostream rtso(typeStr);
            valType->print(rtso);

            RES_REPORT("      - Value: " << rso.str() << " | Type: " << rtso.str());
            if (llvm::Instruction *I = llvm::dyn_cast<llvm::Instruction>(val)) {
                if (I->getFunction() && I->getFunction()->hasName()) {
                     RES_REPORT(" (In Function: " << I->getFunction()->getName().str() << ")");
                }
            } else if (llvm::Argument *A = llvm::dyn_cast<llvm::Argument>(val)) {
                 if (A->getParent() && A->getParent()->hasName()) {
                    RES_REPORT(" (Argument of Function: " << A->getParent()->getName().str() << ")");
                 }
            } else if (llvm::GlobalValue *GV = llvm::dyn_cast<llvm::GlobalValue>(val)) {
                if (GV->hasName()) {
                    RES_REPORT(" (GlobalVariable: " << GV->getName().str() << ")");
                } else {
                    RES_REPORT(" (Anonymous GlobalValue)");
                }
            }

            RES_REPORT("\n");
        }
    } else {
        if (analysis_was_attempted) { 
             RES_REPORT("    No specific Key structures identified for path: " << pathIdentifierString << "\n");
        }
    }
    RES_REPORT("\n"); // Extra newline for readability
}

void KeyStructureAnalyzer::backwardTraceForKeyStructure(
    llvm::Value* startValue,
    const std::string& pathIdentifier,
    std::set<llvm::Value*>& potentialKeyStructures,
    const std::vector<llvm::Function*>& currentCallPath,
    llvm::Function* rootInterfaceFuncForThisPath // This is the function at the top of the current trace segment (e.g. original path.back())
) {
    if (!startValue) return;

    std::queue<llvm::Value*> analysisQueue;
    std::set<llvm::Value*> visitedInThisTrace;

    analysisQueue.push(startValue);

    unsigned iterations = 0;
    const unsigned MAX_ITERATIONS = 200;

    while (!analysisQueue.empty() && iterations < MAX_ITERATIONS) {
        iterations++;
        llvm::Value* current = analysisQueue.front();
        analysisQueue.pop();

        if (!visitedInThisTrace.insert(current).second) {
            continue;
        }

        
        llvm::Function* funcContainingCurrentVal = nullptr;
        if (llvm::Instruction* I = llvm::dyn_cast<llvm::Instruction>(current)) {
            funcContainingCurrentVal = I->getFunction();
        } else if (llvm::Argument* A = llvm::dyn_cast<llvm::Argument>(current)) {
            funcContainingCurrentVal = A->getParent();
        }

        if (funcContainingCurrentVal) {
            std::string currentFuncBaseName = getBaseNameIfSuffixedString(funcContainingCurrentVal);
            if (currentFuncBaseName.empty() && funcContainingCurrentVal->hasName()) {
                 currentFuncBaseName = funcContainingCurrentVal->getName().str();
            }

            if (currentFuncBaseName == "kbase_user_buf_map") {
                llvm::Module* M = funcContainingCurrentVal->getParent(); // Module of kbase_user_buf_map
                if (M) {
                    llvm::StructType* keyStructType = llvm::StructType::getTypeByName(M->getContext(), "struct.kbase_alloc_import_user_buf");
                    if (keyStructType) {
                        potentialKeyStructures.clear();
                        llvm::PointerType* ptrToKeyStructType = llvm::PointerType::getUnqual(keyStructType);
                        llvm::Constant* keyStructMarker = llvm::ConstantPointerNull::get(ptrToKeyStructType);
                        potentialKeyStructures.insert(keyStructMarker);
                        return; // Terminate this trace as per request for this specific case
                    } else {
                        RES_REPORT("    Warning: Struct type 'struct.kbase_alloc_import_user_buf' not found in module context. Path: " << pathIdentifier << "\n");
                    }
                }
            }
        }
        // END OF NEW LOGIC for kbase_user_buf_map context

        if (llvm::CallInst* CI = llvm::dyn_cast<llvm::CallInst>(current)) {
            if (llvm::Function* calledFunc = CI->getCalledFunction()) {
                std::string baseName = getBaseNameIfSuffixedString(calledFunc);
                if (baseName.empty()) { 
                    if (calledFunc->hasName()) baseName = calledFunc->getName().str();
                }

                if (baseName == "kbase_get_gpu_phy_pages" || baseName == "kbase_get_cpu_phy_pages") {
                    llvm::Module* M = CI->getModule();
                    if (M) {
                        llvm::StructType* keyStructType = llvm::StructType::getTypeByName(M->getContext(), "struct.kbase_mem_phy_alloc");
                        if (keyStructType) {
                            potentialKeyStructures.clear(); 
                            llvm::PointerType* ptrToKeyStructType = llvm::PointerType::getUnqual(keyStructType);
                            llvm::Constant* keyStructMarker = llvm::ConstantPointerNull::get(ptrToKeyStructType);
                            potentialKeyStructures.insert(keyStructMarker);
                            return; 
                        } else {
                            RES_REPORT("    Warning: Struct type 'kbase_mem_phy_alloc' not found in module context. Path: " << pathIdentifier << "\n");
                        }
                    }
                }
            }
        }
        // === END MODIFIED LOGIC ===

        bool isPotentialKeyStructure = false; 
        llvm::Type* currentType = current->getType();

        if (currentType->isPointerTy()) {
            llvm::Type* pointedType = currentType->getPointerElementType();
            if (pointedType->isStructTy()) {
                if (llvm::StructType* ST = llvm::dyn_cast<llvm::StructType>(pointedType)) {
                    if (ST->getNumElements() > 1) { 
                        isPotentialKeyStructure = true;
                    }
                }
            }
        }
        
        if (llvm::AllocaInst* AI = llvm::dyn_cast<llvm::AllocaInst>(current)) {
            llvm::Type* allocatedType = AI->getAllocatedType();
            if (allocatedType->isStructTy()) {
                 if (llvm::StructType* ST = llvm::dyn_cast<llvm::StructType>(allocatedType)) {
                    if (ST->getNumElements() > 1) { 
                        isPotentialKeyStructure = true;
                    }
                }
            }
        }

        if (isPotentialKeyStructure) {
            potentialKeyStructures.insert(current);
        }

        if (llvm::GetElementPtrInst* GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(current)) {
            bool hasVariableIndex = false;
            // Start from 1 to skip the pointer operand
            for (unsigned i = 1; i < GEP->getNumOperands(); ++i) {
                if (!llvm::isa<llvm::ConstantInt>(GEP->getOperand(i))) {
                    hasVariableIndex = true;
                    break;
                }
            }

            if (hasVariableIndex) {
                // This is likely an array access (e.g., pages[i]).
                // We should trace where the array 'pages' comes from, so we trace the pointer operand.
                analysisQueue.push(GEP->getPointerOperand());
            } else {
                // All indices are constants, indicating a direct field access (e.g., map->alloc).
                // This is the source structure we are looking for. Report it and stop.
                potentialKeyStructures.insert(GEP->getPointerOperand());
            }
            // In either case, we've handled the GEP, so skip the generic instruction processing.
            continue;
        }

        if (llvm::Instruction* I = llvm::dyn_cast<llvm::Instruction>(current)) {
            for (Use &U : I->operands()) {
                Value *operand = U.get();
                if (llvm::isa<llvm::Constant>(operand) && !llvm::isa<llvm::GlobalValue>(operand)) {
                    continue;
                }
                analysisQueue.push(operand);
            }
        } else if (llvm::Argument* current_arg = llvm::dyn_cast<llvm::Argument>(current)) {
            llvm::Function* callee_function = current_arg->getParent();
            unsigned arg_no = current_arg->getArgNo();

            // Check if we are at the designated root for THIS path segment
            if (callee_function == rootInterfaceFuncForThisPath) {
                // We've reached the function that was considered the 'entry' or 'root' for this specific backward trace segment.
                // No further upward tracing from this argument in this context.
                continue; 
            }

            // If we are in local-only analysis mode, don't trace arguments up the call chain.
            if (currentCallPath.size() <= 1) {
                continue;
            }

            // Find the specific caller in the path to trace the argument back to.
            // The currentCallPath is ordered from target (path[0]) to entry (path.back()).
            // If current_arg is in callee_function, we need to find where callee_function is in currentCallPath
            // and then look at currentCallPath[i+1] as its caller in this specific path.
            llvm::Function* specific_caller_in_path = nullptr;
            for (size_t i = 0; i < currentCallPath.size(); ++i) {
                if (currentCallPath[i] == callee_function) {
                    if (i + 1 < currentCallPath.size()) { // i+1 is the caller in the path vector
                        specific_caller_in_path = currentCallPath[i+1];
                    }
                    break;
                }
            }

            if (specific_caller_in_path && Ctx) { 
                auto it_callers = Ctx->Callers.find(callee_function);
                if (it_callers != Ctx->Callers.end()) {
                    const CallInstSet& all_calling_instructions = it_callers->second;
                    for (llvm::CallInst* call_inst : all_calling_instructions) {
                        // Ensure this call instruction is from the specific caller we identified in the path
                        if (call_inst->getFunction() == specific_caller_in_path) {
                            if (arg_no < call_inst->arg_size()) {
                                llvm::Value* actual_arg_at_callsite = call_inst->getArgOperand(arg_no);
                                if (actual_arg_at_callsite) {
                                    analysisQueue.push(actual_arg_at_callsite);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    // Optional: Log if MAX_ITERATIONS reached
} 