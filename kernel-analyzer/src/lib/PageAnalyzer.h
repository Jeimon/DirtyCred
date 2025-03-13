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

  virtual bool doInitialization(Module *);
  virtual bool doFinalization(Module *);
  virtual bool doModulePass(Module *);
  bool isPageStruct(StructType *st, Indices& indices);
};

#endif