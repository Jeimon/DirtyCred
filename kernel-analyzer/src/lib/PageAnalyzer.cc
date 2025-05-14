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
#include "llvm/IR/InstrTypes.h" // For TerminatorInst

#include "PageAnalyzer.h"

using namespace llvm;

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

    if (!name.compare("kbase_mem_alloc_page"))
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


bool PageAnalyzerPass::isPageStruct(StructType *st, Indices &indices) {
    if (st == nullptr || indices.size() == 0)
        return false;

    if (indices.size() ==  1) {
        for (auto sf: pageStructField) {
            if (indices.front() == sf.second && st->getStructName().str() == sf.first) {
                return true;
            }
        }
    } else {
        int field = indices.front();
        indices.pop_front();
        if (field < 0 || st->getNumElements() <= field)
            return false;
        return isPageStruct(dyn_cast_or_null<StructType>(st->getElementType(field)), indices);
    }
    return false;
}


bool PageAnalyzerPass::doModulePass(Module *M) {
    for (auto &F : *M) {
        for (auto i = inst_begin(F), e = inst_end(F); i != e; i++) {
          Instruction *I = &*i;
          // you can remove this if needed
          // First: find page allocation location
          if (auto CI = dyn_cast_or_null<CallInst>(I)) {
            Function *callee = CI->getCalledFunction();
            if (callee && isPageAllocator(callee))
                Ctx->pageAllocation.insert(callee);
          }

          // Second: find store instructions that store to certain struct field
          if (auto gep = dyn_cast_or_null<GetElementPtrInst>(I)) {
            Type * source = gep->getSourceElementType();
            Indices indices;
            get_gep_indicies(gep, indices);
            indices.pop_front();

            if (ArrayType *arr = dyn_cast_or_null<ArrayType>(source)) {
                source = arr->getArrayElementType();
            }
            StructType *st = dyn_cast_or_null<StructType>(source);

            if(isPageStruct(st, indices)) {
                // errs() << "found: " << *gep << "\n";
                if (usedInStore(gep)) {
                     // the current version does not add the resitriction
                    //  should we add the restriction? the source operand should come from the page allocator?
                    Ctx->pageAllocation.insert(gep->getFunction());
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

PageCtrlStruct PageAnalyzerPass::findControlStructureForMapOperand(
    llvm::CallInst *mapCallInst,
    int physMemArgIdx,
    unsigned searchDepth
) {
    if (!mapCallInst || physMemArgIdx < 0 || (unsigned)physMemArgIdx >= mapCallInst->getNumArgOperands()) {
        return PageCtrlStruct(); // Return empty struct if input is invalid
    }

    llvm::Value *startValue = mapCallInst->getArgOperand(physMemArgIdx);
    std::set<llvm::Value*> visited;
    return backwardTraceValue(startValue, searchDepth, visited);
}

PageCtrlStruct PageAnalyzerPass::backwardTraceValue(
    llvm::Value* currentValue,
    unsigned currentDepth,
    std::set<llvm::Value*>& visited
) {
    if (currentDepth == 0 || !currentValue) {
        return PageCtrlStruct(); // Depth limit reached or null value
    }

    // Avoid cycles and re-processing
    if (visited.count(currentValue)) {
        return PageCtrlStruct();
    }
    visited.insert(currentValue);

    // 1. Check if currentValue itself is a GEP revealing a struct
    if (llvm::GetElementPtrInst *gep = llvm::dyn_cast<llvm::GetElementPtrInst>(currentValue)) {
        llvm::Type *sourceElementType = gep->getSourceElementType();
        if (llvm::StructType *st = llvm::dyn_cast<llvm::StructType>(sourceElementType)) {
            if (st->isOpaque()) { // Try to resolve opaque struct type by looking at the module
                if (gep->getModule()) {
                    llvm::StructType* resolvedSt = llvm::StructType::getTypeByName(gep->getContext(), st->getName());
                    if (resolvedSt) st = resolvedSt;
                }
            }
            // Found a GEP that operates on a struct type.
            // The base pointer of this GEP is the instance of the struct.
            return PageCtrlStruct{st, gep->getPointerOperand(), gep};
        }
        // If it's a GEP but not on a struct, trace its base pointer
        return backwardTraceValue(gep->getPointerOperand(), currentDepth -1, visited);
    }

    // 2. If it's an instruction, trace its operands
    if (llvm::Instruction *inst = llvm::dyn_cast<llvm::Instruction>(currentValue)) {
        if (llvm::isa<llvm::TerminatorInst>(inst) && !llvm::isa<llvm::CallInst>(inst)) {
             // Stop at terminators other than calls, usually not part of data-flow for operands
            return PageCtrlStruct();
        }

        switch (inst->getOpcode()) {
            case llvm::Instruction::BitCast:
            case llvm::Instruction::AddrSpaceCast: // Handle address space casts too
            //llvm::Instruction::PtrToInt: // PtrToInt and IntToPtr can break type analysis, handle with care
            //llvm::Instruction::IntToPtr: // or exclude for a simpler version.
                return backwardTraceValue(inst->getOperand(0), currentDepth - 1, visited);
            
            case llvm::Instruction::Load:
                // Trace the pointer operand of the load
                return backwardTraceValue(inst->getOperand(0), currentDepth - 1, visited);

            case llvm::Instruction::Call: 
            case llvm::Instruction::Invoke:
            {
                llvm::CallSite cs(inst);
                // Simplified: Stop at calls. More advanced: model known functions or trace return values.
                // For functions like get_page, kmap, etc., one might inter-procedurally analyze or use summaries.
                // This simplified version does not do that.
                return PageCtrlStruct(); 
            }

            case llvm::Instruction::PHI:
            {
                llvm::PHINode *phi = llvm::cast<llvm::PHINode>(inst);
                // For PHI nodes, can try to trace incoming values. 
                // For simplicity, pick the first one or try all (could be complex).
                // Here, we just try the first incoming value for a simpler trace.
                if (phi->getNumIncomingValues() > 0) {
                    return backwardTraceValue(phi->getIncomingValue(0), currentDepth - 1, visited);
                }
                return PageCtrlStruct();
            }
            
            case llvm::Instruction::Select:
            {
                llvm::SelectInst *sel = llvm::cast<llvm::SelectInst>(inst);
                // Could trace true, false, or both. For simplicity, try true value.
                PageCtrlStruct res = backwardTraceValue(sel->getTrueValue(), currentDepth - 1, visited);
                if (res.IdentifiedStructTy) return res;
                return backwardTraceValue(sel->getFalseValue(), currentDepth -1, visited);
            }

            // Add other cases as needed e.g. AllocaInst if we want to see if it's an alloca of a struct
             case llvm::Instruction::Alloca:
             {
                llvm::AllocaInst *allocaInst = llvm::cast<llvm::AllocaInst>(inst);
                if (llvm::StructType *st = llvm::dyn_cast<llvm::StructType>(allocaInst->getAllocatedType())){
                     if (st->isOpaque()) { 
                        if (allocaInst->getModule()) {
                            llvm::StructType* resolvedSt = llvm::StructType::getTypeByName(allocaInst->getContext(), st->getName());
                            if (resolvedSt) st = resolvedSt;
                        }
                    }
                    return PageCtrlStruct{st, allocaInst, nullptr};
                }
                return PageCtrlStruct();
             }

            default:
                // For other instructions, if they have operands, one might try to trace them.
                // However, for a simplified version, we might stop.
                // If an instruction has a single non-constant operand, try tracing it.
                if (inst->getNumOperands() == 1 && !llvm::isa<llvm::Constant>(inst->getOperand(0))) {
                     return backwardTraceValue(inst->getOperand(0), currentDepth -1, visited);
                }
                return PageCtrlStruct();
        }
    } 
    // 3. If it's an Argument, stop. (Inter-procedural would be needed to go further)
    else if (llvm::isa<llvm::Argument>(currentValue)) {
        return PageCtrlStruct();
    }
    // 4. If it's a Constant (and not a GEP ConstantExpr, handled by dyn_cast<GEP> if it becomes an Inst),
    // usually we stop unless it's a GlobalVariable holding a struct.
    else if (llvm::GlobalVariable *gv = llvm::dyn_cast<llvm::GlobalVariable>(currentValue)) {
        llvm::PointerType *pty = llvm::dyn_cast<llvm::PointerType>(gv->getType());
        if (pty) {
            if (llvm::StructType *st = llvm::dyn_cast<llvm::StructType>(pty->getElementType())) {
                if (st->isOpaque()) {
                     if (gv->getParent()) { // getParent() for Module
                        llvm::StructType* resolvedSt = llvm::StructType::getTypeByName(gv->getContext(), st->getName());
                        if (resolvedSt) st = resolvedSt;
                    }
                }
                return PageCtrlStruct{st, gv, nullptr};
            }
        }
    }
    // Note: ConstantExpr GEPs are not directly handled here unless they are first cast to Instruction.
    // A more robust solution would use Value::stripPointerCasts() and handle ConstantExpr GEPs.

    return PageCtrlStruct(); // Default: not found or unhandled type
}