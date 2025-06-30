#ifndef _CALL_GRAPH_H
#define _CALL_GRAPH_H

#include "GlobalCtx.h"
#include <string>
#include <vector>
#include <map>
#include <llvm/IR/Function.h>
#include "KeyStructureAnalyzer.h"
#include <llvm/Support/raw_ostream.h>

#ifndef _CALL_GRAPH_H_STRUCT_DEF_
#define _CALL_GRAPH_H_STRUCT_DEF_


struct CallTreeNode {
    llvm::Function* func;
    std::string displayName;
    std::map<llvm::Function*, CallTreeNode*> children;

    CallTreeNode(llvm::Function* f, const std::string& name) : func(f), displayName(name) {}

    ~CallTreeNode() = default;

    CallTreeNode(const CallTreeNode&) = delete;
    CallTreeNode& operator=(const CallTreeNode&) = delete;
};

#endif

class CallGraphPass : public IterativeModulePass {
private:
  llvm::Function *getFuncDef(llvm::Function *F);
  bool runOnFunction(llvm::Function *);
  void processInitializers(llvm::Module *, llvm::Constant *,
                           llvm::GlobalValue *, std::string);
  bool findCallees(llvm::CallInst *, FuncSet &);
  bool isCompatibleType(llvm::Type *T1, llvm::Type *T2);
  bool findCalleesByType(llvm::CallInst *, FuncSet &);
  bool mergeFuncSet(FuncSet &S, const std::string &Id, bool InsertEmpty);
  bool mergeFuncSet(std::string &Id, const FuncSet &S, bool InsertEmpty);
  bool mergeFuncSet(FuncSet &Dst, const FuncSet &Src);
  bool findFunctions(llvm::Value *, FuncSet &);
  bool findFunctions(llvm::Value *, FuncSet &,
                     llvm::SmallPtrSet<llvm::Value *, 4>);
  void recursiveDumpPaths(llvm::Function *currentFunc, unsigned int currentDepth, std::vector<llvm::Function*> &path, FuncSet &visitedNodesInDFS, std::map<llvm::Function*, CallTreeNode*>& activeTreeNodes);
  GlobalContext *Ctx;
  std::unique_ptr<KeyStructureAnalyzer> KSA;

public:
  std::map<const llvm::Function*, std::map<llvm::Function*, CallTreeNode*>> PerFunctionCallTrees;

  CallGraphPass(GlobalContext *Ctx_) : IterativeModulePass(Ctx_, "CallGraph"), Ctx(Ctx_) {
    KSA = std::make_unique<KeyStructureAnalyzer>(Ctx);
  }
  virtual bool doInitialization(llvm::Module *);
  virtual bool doFinalization(llvm::Module *);
  virtual bool doModulePass(llvm::Module *);

  // debug
  void dumpFuncPtrs();
  void dumpCallees();
  void dumpCallers();
  void dumpCallPathsForFunc(llvm::Function *targetFunc, unsigned int limits);
  void analyzeMgmProtIndirectCalls(llvm::Module *M);
  void getrootmapinterface(llvm::Module *M);
};

#endif
