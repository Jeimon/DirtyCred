#ifndef _GLOBAL_H
#define _GLOBAL_H

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Analysis/AliasAnalysis.h>
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/Path.h>
#include <llvm/Support/raw_ostream.h>

#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>

#include "Common.h"
#include "StructAnalyzer.h"

using namespace llvm;
using namespace std;

typedef std::vector<std::pair<llvm::Module *, llvm::StringRef>> ModuleList;
typedef std::unordered_map<llvm::Module *, llvm::StringRef> ModuleMap;
typedef std::unordered_map<std::string, llvm::Function *> FuncMap;
typedef std::unordered_map<std::string, llvm::GlobalVariable *> GObjMap;
typedef std::list<int> Indices;
typedef std::list<Value *> ValueList;
typedef std::unordered_set<Value *> ValueSet;

/****************** Call Graph **************/
typedef unordered_map<string, llvm::Function *> NameFuncMap;
typedef llvm::SmallPtrSet<llvm::CallInst *, 8> CallInstSet;
typedef llvm::SmallPtrSet<llvm::Function *, 32> FuncSet;
typedef std::unordered_map<std::string, FuncSet> FuncPtrMap;
typedef llvm::DenseMap<llvm::Function *, CallInstSet> CallerMap;
typedef llvm::DenseMap<llvm::CallInst *, FuncSet> CalleeMap;
/****************** end Call Graph **************/

/****************** Alias **************/
typedef DenseMap<Value *, SmallPtrSet<Value *, 16>> PointerAnalysisMap;
typedef unordered_map<Function *, PointerAnalysisMap> FuncPointerAnalysisMap;
typedef unordered_map<Function *, AAResults *> FuncAAResultsMap;
/****************** end Alias **************/

/****************** mbuf Leak API **************/

/****************** end mbuf Leak API **************/

/****************** Flexible Structural Object Identification **************/

typedef std::unordered_map<std::string, StructInfo *> LeakStructMap;

typedef llvm::SmallPtrSet<llvm::Instruction *, 32> InstSet;
typedef std::unordered_map<std::string, InstSet> AllocInstMap;
typedef std::unordered_map<std::string, InstSet> LeakInstMap;
typedef std::unordered_map<std::string, FuncSet> AllocSyscallMap;
typedef std::unordered_map<std::string, FuncSet> LeakSyscallMap;

typedef llvm::SmallPtrSet<llvm::Module *, 32> ModuleSet;
typedef std::unordered_map<std::string, ModuleSet> StructModuleMap;

typedef llvm::SmallPtrSet<llvm::StructType *, 32> StructTypeSet;
typedef llvm::DenseMap<llvm::Module *, StructTypeSet> ModuleStructMap;

typedef std::unordered_map<std::string, InstSet> LeakerList;

typedef std::unordered_map<unsigned, InstSet> StoreMap;

/**************** End Flexible Structural Object Identification ************/

/****************** Flexible Structural Object Evaluation **************/

typedef std::unordered_map<std::string, std::vector<unsigned>> LeakerLayout;
// typedef llvm::DenseMap<llvm::Value*, unsigned> SliceMap;
typedef llvm::SmallPtrSet<llvm::ICmpInst *, 32> ICmpInstSet;
typedef std::unordered_map<std::string, ICmpInstSet> LeakerICmpMap;

/**************** End Flexible Structural Object Evaluation ************/

static std::set<llvm::StringRef> AllocAPIs = {
    "__kmalloc",
    "__kmalloc_node",
    "kmalloc",
    "kvzalloc",
    "kmalloc_node",
    "kmalloc_array",
    "kzalloc",
    "kmalloc_array_node",
    "kzalloc_node",
    "kcalloc_node",
    "kcalloc",
    "kmem_cache_alloc",
    "kmem_cache_alloc_node",
    "kmem_cache_zalloc",
    "sk_alloc",
};


static std::set<llvm::StringRef> funcDumpPath = {
  "mmu_insert_pages_no_flush",
  // "kbase_mem_pool_alloc_pages",
};



class GlobalContext {
private:
  // pass specific data
  std::map<std::string, void *> PassData;

public:
  bool add(std::string name, void *data) {
    if (PassData.find(name) != PassData.end())
      return false;

    PassData[name] = data;
    return true;
  }

  void *get(std::string name) {
    std::map<std::string, void *>::iterator itr;

    itr = PassData.find(name);
    if (itr != PassData.end())
      return itr->second;
    else
      return nullptr;
  }

  FuncSet IRFuncDumpPath;
  FuncSet pageAllocation;

  // StructAnalyzer
  StructAnalyzer structAnalyzer;

  // Map global object name to object definition
  GObjMap Gobjs;

  // Map global function name to function defination
  FuncMap Funcs;

  // Map function pointers (IDs) to possible assignments
  FuncPtrMap FuncPtrs;

  // functions whose addresses are taken
  FuncSet AddressTakenFuncs;

  // Map a callsite to all potential callee functions.
  CalleeMap Callees;

  // Map a function to all potential caller instructions.
  CallerMap Callers;

  // Indirect call instructions
  std::vector<CallInst *> IndirectCallInsts;

  // Map function signature to functions
  DenseMap<size_t, FuncSet> sigFuncsMap;

  // Map global function name to function.
  NameFuncMap GlobalFuncs;

  // Unified functions -- no redundant inline functions
  DenseMap<size_t, Function *> UnifiedFuncMap;
  set<Function *> UnifiedFuncSet;

  /****** Alias Analysis *******/
  FuncPointerAnalysisMap FuncPAResults;
  FuncAAResultsMap FuncAAResults;

  /****** Leak struct **********/
  LeakStructMap leakStructMap;

  /****************** Flexible Structural Object Identification **************/

  // map structure to allocation site
  AllocInstMap allocInstMap;

  // map structure to leak site
  LeakInstMap leakInstMap;

  // map structure to syscall entry reaching allocation site
  AllocSyscallMap allocSyscallMap;

  // map structure to syscall entry reaching leak site
  LeakSyscallMap leakSyscallMap;

  // map module to set of used flexible structure
  ModuleStructMap moduleStructMap;

  // map flexible structure to module
  StructModuleMap structModuleMap;

  LeakerList leakerList;

  // mbuf leak api
  FuncSet LeakAPIs;

  // device permission allow function list and deny function list
  FuncSet devAllowList;
  FuncSet devDenyList;

  /**************** End Flexible Structural Object Identification ************/

  /****************** Flexible Structural Object Evaluation **************/
  LeakerLayout leakerLayout;
  LeakerICmpMap leakerICmpMap;
  /**************** End Flexible Structural Object Evaluation ************/

  // A factory object that knows how to manage AndersNodes
  // AndersNodeFactory nodeFactory;

  ModuleList Modules;

  ModuleMap ModuleMaps;
  std::set<std::string> InvolvedModules;
};

class IterativeModulePass {
protected:
  GlobalContext *Ctx;
  const char *ID;

public:
  IterativeModulePass(GlobalContext *Ctx_, const char *ID_)
      : Ctx(Ctx_), ID(ID_) {}

  // run on each module before iterative pass
  virtual bool doInitialization(llvm::Module *M) { return true; }

  // run on each module after iterative pass
  virtual bool doFinalization(llvm::Module *M) { return true; }

  // iterative pass
  virtual bool doModulePass(llvm::Module *M) { return false; }

  virtual void run(ModuleList &modules);
};

#endif

kbase_ioctl -> kbase_api_mem_import -> kbase_mem_import.2401 -> kbase_gpu_mmap.1554 -> kbase_add_va_region.959 -> kbase_jit_evict -> kbase_mem_free_region.1482 -> kbase_free_alloced_region.938 -> kbase_sticky_resource_release_force.1187 -> release_sticky_resource_meta -> kbase_unmap_external_resource.1271 -> kbase_mem_umm_unmap -> kbase_mmu_teardown_imported_pages -> mmu_teardown_pages -> mmu_flush_invalidate_teardown_pages -> mmu_flush_invalidate -> release_ctx -> kbasep_js_runpool_release_ctx.4507 -> kbasep_js_runpool_release_ctx_and_katom_retained_state.1333 -> kbase_js_sched_all.3727 -> kbase_js_sched.1112 -> kbase_pm_context_active_handle_suspend.1785 -> kbasep_pm_context_active_handle_suspend_locked -> kbase_arbiter_pm_vm_event.1409 -> kbase_arbiter_pm_vm_os_prepare_suspend -> kbase_pm_driver_suspend -> resume_job_scheduling -> kbase_resume_suspended_soft_jobs.1422 -> kbase_process_soft_job.1259 -> kbase_ext_res_process -> kbase_sticky_resource_acquire.1185 -> kbase_map_external_resource.1295 -> kbase_user_buf_from_pinned_to_gpu_mapped -> kbase_user_buf_map -> kbase_mmu_insert_pages_skip_status_update -> mmu_insert_pages_no_flush [You have reached an entry]

kbase_ioctl -> kbase_api_mem_import -> kbase_mem_import.2401 -> kbase_gpu_mmap.1554 -> kbase_add_va_region.959 -> kbase_jit_evict -> kbase_mem_free_region.1482 -> kbase_free_alloced_region.938 -> kbase_sticky_resource_release_force.1187 -> release_sticky_resource_meta -> kbase_unmap_external_resource.1271 -> kbase_mem_umm_unmap -> kbase_mmu_teardown_imported_pages -> mmu_teardown_pages -> mmu_flush_invalidate_teardown_pages -> mmu_flush_invalidate -> release_ctx -> kbasep_js_runpool_release_ctx.4507 -> kbasep_js_runpool_release_ctx_and_katom_retained_state.1333 -> kbase_js_sched_all.1241 -> kbase_js_sched.1112 -> kbase_pm_context_active_handle_suspend.1785 -> kbasep_pm_context_active_handle_suspend_locked -> kbase_arbiter_pm_vm_event.1409 -> kbase_arbiter_pm_vm_os_prepare_suspend -> kbase_pm_driver_suspend -> resume_job_scheduling -> kbase_resume_suspended_soft_jobs.1422 -> kbase_process_soft_job.1259 -> kbase_ext_res_process -> kbase_sticky_resource_acquire.1185 -> kbase_map_external_resource.1295 -> kbase_user_buf_from_pinned_to_gpu_mapped -> kbase_user_buf_map -> kbase_mmu_insert_pages_skip_status_update -> mmu_insert_pages_no_flush [You have reached an entry]

