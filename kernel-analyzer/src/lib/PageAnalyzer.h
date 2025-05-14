#ifndef _PAGE_H
#define _PAGE_H

/*
 * main function
 *
 * Copyright (C) 2025 Jinmeng Zhou
 *
 * For licensing details see LICENSE
 */

#include "Common.h"
#include "GlobalCtx.h"
#include <utility>
#include <set>
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Instructions.h"

// Simplified structure to hold information about the found control struct
struct PageCtrlStruct {
    llvm::StructType *IdentifiedStructTy = nullptr;
    llvm::Value *StructInstanceValue = nullptr; // e.g., the base of the GEP or Alloca
    llvm::GetElementPtrInst* OriginatingGEP = nullptr; // GEP that revealed the struct
    // Add other fields if necessary
};

class PageAnalyzerPass : public IterativeModulePass {
public:
  std::set<std::pair<llvm::StringRef, int>> pageStructField = {
    std::make_pair("struct.pci_filp_private", 0),
    std::make_pair("struct.vm_fault", 8),
  };
  // Please check if these struct definitions are removed in LLVM IR
  // If so, you need to use the annotation in this project to attach user-customized metadata to IR, which
  // requires to modify the Clang/LLVM compiler and uses the modified compilter to generate .bc file.
  // Otherwise, I recommend using our type-recovery tool.

public:
  PageAnalyzerPass(GlobalContext *Ctx_)
        : IterativeModulePass(Ctx_, "PageAnalysis") {}

  virtual bool doInitialization(llvm::Module *);
  virtual bool doFinalization(llvm::Module *);
  virtual bool doModulePass(llvm::Module *);
  bool isPageStruct(llvm::StructType *st, Indices& indices);

  // New method for finding control structure
  PageCtrlStruct findControlStructureForMapOperand(
      llvm::CallInst *mapCallInst,
      int physMemArgIdx,
      unsigned searchDepth
  );

private: // Add a private section for the helper
  PageCtrlStruct backwardTraceValue(
    llvm::Value* currentValue, 
    unsigned currentDepth,
    std::set<llvm::Value*>& visited
  );
};

#endif