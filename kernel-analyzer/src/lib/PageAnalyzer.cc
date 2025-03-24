
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