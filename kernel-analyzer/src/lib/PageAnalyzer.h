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
  std::set<std::pair<llvm::StringRef, int>> KeyStructField = {
    // std::make_pair("struct.pci_filp_private", 0),
    // std::make_pair("struct.vm_fault", 8),

    std::make_pair("struct.kbase_context", 14),
    std::make_pair("struct.kbase_mem_phy_alloc", 4),
    std::make_pair("struct.kbase_alloc_import_user_buf", 3),
    std::make_pair("struct.kbase_queue", 2),
    std::make_pair("struct.kbase_device", 7),
    std::make_pair("struct.kbase_csf_device", 10),
  };

  std::set<llvm::StringRef> map_wrapper_functions = {
  "kbase_mmu_insert_pages_no_flush",
  "kbase_mmu_insert_pages",
  "kbase_mmu_insert_pages_skip_status_update",
  "kbase_mmu_insert_aliased_pages",
  "kbase_mmu_insert_single_page",
  "kbase_mmu_update_pages_no_flush",
  };

  std::set<std::pair<llvm::StringRef, int>> TypeField = {
    std::make_pair("struct.kbase_mem_phy_alloc", 9),
  };
  // Please check if these struct definitions are removed in LLVM IR
  // If so, you need to use the annotation in this project to attach user-customized metadata to IR, which
  // requires to modify the Clang/LLVM compiler and uses the modified compilter to generate .bc file.
  // Otherwise, I recommend using our type-recovery tool.

public:
  PageAnalyzerPass(GlobalContext *Ctx_)
        : IterativeModulePass(Ctx_, "PageAnalysis"), 
          currentMatchedKeyStructName(""), 
          currentMatchedKeyStructFieldIndex(-1) {}

  virtual bool doInitialization(Module *);
  virtual bool doFinalization(Module *);
  virtual bool doModulePass(Module *);
  std::string currentMatchedKeyStructName;
  int currentMatchedKeyStructFieldIndex;
  void findStoresToMemoryPointedBy(llvm::GetElementPtrInst *gep_to_field_itself, llvm::Function *F, const std::string &descriptive_field_name);
  bool isKeyStruct(StructType *st, Indices& indices);
  void findAllocationTypeSources(llvm::Module *M);
  void analyzeKeyStructFieldGEPs(llvm::Module *M);
  void findMapTypeSources(llvm::Module *M);

  bool analyzePathForMapWrapper(llvm::BasicBlock* currentBB,
                                std::set<llvm::Function*>& visitedFunctionsInPath,
                                std::set<llvm::BasicBlock*>& visitedBlocksInCurrentFuncScope,
                                int currentDepth,
                                const int maxDepth);
};

#endif