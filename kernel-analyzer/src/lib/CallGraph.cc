/*
 * Call graph construction
 *
 * Copyright (C) 2012 Xi Wang, Haogang Chen, Nickolai Zeldovich
 * Copyright (C) 2015 - 2016 Chengyu Song
 * Copyright (C) 2016 Kangjie Lu
 *
 * For licensing details see LICENSE
 */

#include <llvm/ADT/StringExtras.h>
#include <llvm/Analysis/CallGraph.h>
// #include <llvm/IR/CallSite.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Pass.h>
#include <llvm/Support/Debug.h>

#include "Annotation.h"
#include "GlobalCtx.h"
#include "llvm/IR/Function.h"
#include "CallGraph.h"
#include <llvm/Support/raw_ostream.h> // For outs(), errs()

using namespace llvm;

// Define the global tree node maps
// These should be accessible if you plan to use them from KAMain.cc directly after the pass runs.
// If CallGraph.h doesn't declare them as extern, they are private to this .cc file unless exposed via getters.
// For simplicity with the current request, defining them here. If CallGraph.h included extern decls, this would be the definition.

// Static helper function to get or create a node in the specified map
static CallTreeNode* getOrCreateNodeInTree(llvm::Function* func, 
                                         const std::string& displayName, 
                                         std::map<llvm::Function*, CallTreeNode*>& nodeMap) {
    if (!func) return nullptr;

    auto it = nodeMap.find(func);
    if (it != nodeMap.end()) {
        return it->second;
    }
    CallTreeNode* newNode = new CallTreeNode(func, displayName);
    nodeMap[func] = newNode;
    return newNode;
}

Function *CallGraphPass::getFuncDef(Function *F) {
  FuncMap::iterator it = Ctx->Funcs.find(getScopeName(F));
  if (it != Ctx->Funcs.end())
    return it->second;
  else
    return F;
}

bool CallGraphPass::isCompatibleType(Type *T1, Type *T2) {
  if (T1->isPointerTy()) {
    if (!T2->isPointerTy())
      return false;

    Type *ElT1 = T1->getPointerElementType();
    Type *ElT2 = T2->getPointerElementType();
    // assume "void *" and "char *" are equivalent to any pointer type
    if (ElT1->isIntegerTy(8) /*|| ElT2->isIntegerTy(8)*/)
      return true;

    return isCompatibleType(ElT1, ElT2);
  } else if (T1->isArrayTy()) {
    if (!T2->isArrayTy())
      return false;

    Type *ElT1 = T1->getArrayElementType();
    Type *ElT2 = T2->getArrayElementType();
    return isCompatibleType(ElT1, ElT1);
  } else if (T1->isIntegerTy()) {
    // assume pointer can be cased to the address space size
    if (T2->isPointerTy() &&
        T1->getIntegerBitWidth() == T2->getPointerAddressSpace())
      return true;

    // assume all integer type are compatible
    if (T2->isIntegerTy())
      return true;
    else
      return false;
  } else if (T1->isStructTy()) {
    StructType *ST1 = cast<StructType>(T1);
    StructType *ST2 = dyn_cast<StructType>(T2);
    if (!ST2)
      return false;

    // literal has to be equal
    if (ST1->isLiteral() != ST2->isLiteral())
      return false;

    // literal, compare content
    if (ST1->isLiteral()) {
      unsigned numEl1 = ST1->getNumElements();
      if (numEl1 != ST2->getNumElements())
        return false;

      for (unsigned i = 0; i < numEl1; ++i) {
        if (!isCompatibleType(ST1->getElementType(i), ST2->getElementType(i)))
          return false;
      }
      return true;
    }

    // not literal, use name?
    return ST1->getStructName().equals(ST2->getStructName());
  } else if (T1->isFunctionTy()) {
    FunctionType *FT1 = cast<FunctionType>(T1);
    FunctionType *FT2 = dyn_cast<FunctionType>(T2);
    if (!FT2)
      return false;

    if (!isCompatibleType(FT1->getReturnType(), FT2->getReturnType()))
      return false;

    // assume varg is always compatible with varg?
    if (FT1->isVarArg()) {
      if (FT2->isVarArg())
        return true;
      else
        return false;
    }

    // compare args, again ...
    unsigned numParam1 = FT1->getNumParams();
    if (numParam1 != FT2->getNumParams())
      return false;

    for (unsigned i = 0; i < numParam1; ++i) {
      if (!isCompatibleType(FT1->getParamType(i), FT2->getParamType(i)))
        return false;
    }
    return true;
  } else {
    // errs() << "Unhandled Types:" << *T1 << " :: " << *T2 << "\n";
    return T1->getTypeID() == T2->getTypeID();
  }
}

bool CallGraphPass::findCalleesByType(CallInst *CI, FuncSet &FS) {
  // CallSite CS(CI);
  // errs() << *CI << "\n";
  for (Function *F : Ctx->AddressTakenFuncs) {

    // just compare known args
    if (F->getFunctionType()->isVarArg()) {
      // errs() << "VarArg: " << F->getName() << "\n";
      // report_fatal_error("VarArg address taken function\n");
    } else if (F->arg_size() != CI->arg_size()) {
      // errs() << "ArgNum mismatch: " << F.getName() << "\n";
      continue;
    } else if (!isCompatibleType(F->getReturnType(), CI->getType())) {
      continue;
    }

    if (F->isIntrinsic()) {
      // errs() << "Intrinsic: " << F.getName() << "\n";
      continue;
    }

    // type matching on args
    bool Matched = true;
    auto AI = CI->arg_begin();
    for (Function::arg_iterator FI = F->arg_begin(), FE = F->arg_end();
         FI != FE; ++FI, ++AI) {
      // check type mis-match
      Type *FormalTy = FI->getType();
      Type *ActualTy = (*AI)->getType();

      if (isCompatibleType(FormalTy, ActualTy))
        continue;
      else {
        Matched = false;
        break;
      }
    }

    if (Matched)
      FS.insert(F);
  }

  return false;
}

bool CallGraphPass::mergeFuncSet(FuncSet &S, const std::string &Id,
                                 bool InsertEmpty) {
  FuncPtrMap::iterator i = Ctx->FuncPtrs.find(Id);
  if (i != Ctx->FuncPtrs.end())
    return mergeFuncSet(S, i->second);
  else if (InsertEmpty)
    Ctx->FuncPtrs.insert(std::make_pair(Id, FuncSet()));
  return false;
}

bool CallGraphPass::mergeFuncSet(std::string &Id, const FuncSet &S,
                                 bool InsertEmpty) {
  FuncPtrMap::iterator i = Ctx->FuncPtrs.find(Id);
  if (i != Ctx->FuncPtrs.end())
    return mergeFuncSet(i->second, S);
  else if (!S.empty())
    return mergeFuncSet(Ctx->FuncPtrs[Id], S);
  else if (InsertEmpty)
    Ctx->FuncPtrs.insert(std::make_pair(Id, FuncSet()));
  return false;
}

bool CallGraphPass::mergeFuncSet(FuncSet &Dst, const FuncSet &Src) {
  bool Changed = false;
  for (FuncSet::const_iterator i = Src.begin(), e = Src.end(); i != e; ++i) {
    assert(*i);
    Changed |= Dst.insert(*i).second;
  }
  return Changed;
}

bool CallGraphPass::findFunctions(Value *V, FuncSet &S) {
  SmallPtrSet<Value *, 4> Visited;
  return findFunctions(V, S, Visited);
}

bool CallGraphPass::findFunctions(Value *V, FuncSet &S,
                                  SmallPtrSet<Value *, 4> Visited) {
  if (!Visited.insert(V).second)
    return false;

  // real function, S = S + {F}
  if (Function *F = dyn_cast<Function>(V)) {
    // prefer the real definition to declarations
    F = getFuncDef(F);
    return S.insert(F).second;
  }

  // bitcast, ignore the cast
  if (CastInst *B = dyn_cast<CastInst>(V))
    return findFunctions(B->getOperand(0), S, Visited);

  // const bitcast, ignore the cast
  if (ConstantExpr *C = dyn_cast<ConstantExpr>(V)) {
    if (C->isCast()) {
      return findFunctions(C->getOperand(0), S, Visited);
    }
    // FIXME GEP
  }

  if (GetElementPtrInst *G = dyn_cast<GetElementPtrInst>(V)) {
    return false;
  } else if (isa<ExtractValueInst>(V)) {
    return false;
  }

  if (isa<AllocaInst>(V)) {
    return false;
  }

  if (BinaryOperator *BO = dyn_cast<BinaryOperator>(V)) {
    Value *op0 = BO->getOperand(0);
    Value *op1 = BO->getOperand(1);
    if (!isa<Constant>(op0) && isa<Constant>(op1))
      return findFunctions(op0, S, Visited);
    else if (isa<Constant>(op0) && !isa<Constant>(op1))
      return findFunctions(op1, S, Visited);
    else
      return false;
  }

  // PHI node, recursively collect all incoming values
  if (PHINode *P = dyn_cast<PHINode>(V)) {
    bool Changed = false;
    for (unsigned i = 0; i != P->getNumIncomingValues(); ++i)
      Changed |= findFunctions(P->getIncomingValue(i), S, Visited);
    return Changed;
  }

  // select, recursively collect both paths
  if (SelectInst *SI = dyn_cast<SelectInst>(V)) {
    bool Changed = false;
    Changed |= findFunctions(SI->getTrueValue(), S, Visited);
    Changed |= findFunctions(SI->getFalseValue(), S, Visited);
    return Changed;
  }

  // arguement, S = S + FuncPtrs[arg.ID]
  if (Argument *A = dyn_cast<Argument>(V)) {
    bool InsertEmpty = isFunctionPointer(A->getType());
    return mergeFuncSet(S, getArgId(A), InsertEmpty);
  }

  // return value, S = S + FuncPtrs[ret.ID]
  if (CallInst *CI = dyn_cast<CallInst>(V)) {
    // update callsite info first
    FuncSet &FS = Ctx->Callees[CI];
    // FS.setCallerInfo(CI, &Ctx->Callers);
    findFunctions(CI->getCalledOperand(), FS);
    bool Changed = false;
    for (Function *CF : FS) {
      bool InsertEmpty = isFunctionPointer(CI->getType());
      Changed |= mergeFuncSet(S, getRetId(CF), InsertEmpty);
    }
    return Changed;
  }

  // loads, S = S + FuncPtrs[struct.ID]
  if (LoadInst *L = dyn_cast<LoadInst>(V)) {
    std::string Id = getLoadId(L);
    if (!Id.empty()) {
      bool InsertEmpty = isFunctionPointer(L->getType());
      return mergeFuncSet(S, Id, InsertEmpty);
    } else {
      Function *f = L->getParent()->getParent();
      // errs() << "Empty LoadID: " << f->getName() << "::" << *L << "\n";
      return false;
    }
  }

  // ignore other constant (usually null), inline asm and inttoptr
  if (isa<Constant>(V) || isa<InlineAsm>(V) || isa<IntToPtrInst>(V))
    return false;

  // V->dump();
  // report_fatal_error("findFunctions: unhandled value type\n");
  // errs() << "findFunctions: unhandled value type: " << *V << "\n";
  return false;
}

bool CallGraphPass::findCallees(CallInst *CI, FuncSet &FS) {
  Function *CF = CI->getCalledFunction();
  // real function, S = S + {F}
  if (CF) {
    // prefer the real definition to declarations
    CF = getFuncDef(CF);
    return FS.insert(CF).second;
  }

  // save called values for point-to analysis
  Ctx->IndirectCallInsts.push_back(CI);

#ifdef TYPE_BASED
  // use type matching to concervatively find
  // possible targets of indirect call
  return findCalleesByType(CI, FS);
#else
  // use assignments based approach to find possible targets
  return findFunctions(CI->getCalledOperand(), FS);
#endif
}

bool CallGraphPass::runOnFunction(Function *F) {

  // Lewis: we don't give a shit to functions in .init.text
  if (F->hasSection() && F->getSection().str() == ".init.text")
    return false;
  bool Changed = false;

  for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
    Instruction *I = &*i;
    // map callsite to possible callees
    if (CallInst *CI = dyn_cast<CallInst>(I)) {
      // ignore inline asm or intrinsic calls
      if (CI->isInlineAsm() ||
          (CI->getCalledFunction() && CI->getCalledFunction()->isIntrinsic()))
        continue;

      // might be an indirect call, find all possible callees
      FuncSet &FS = Ctx->Callees[CI];
      if (!findCallees(CI, FS))
        continue;

#ifndef TYPE_BASED
      // looking for function pointer arguments
      for (unsigned no = 0, ne = CI->arg_size(); no != ne; ++no) {
        Value *V = CI->getArgOperand(no);
        if (!isFunctionPointerOrVoid(V->getType()))
          continue;

        // find all possible assignments to the argument
        FuncSet VS;
        if (!findFunctions(V, VS))
          continue;

        // update argument FP-set for possible callees
        for (Function *CF : FS) {
          if (!CF) {
            WARNING("NULL Function " << *CI << "\n");
            assert(0);
          }
          std::string Id = getArgId(CF, no);
          Changed |= mergeFuncSet(Ctx->FuncPtrs[Id], VS);
        }
      }
#endif
    }
#ifndef TYPE_BASED
    if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
      // stores to function pointers
      Value *V = SI->getValueOperand();
      if (isFunctionPointerOrVoid(V->getType())) {
        std::string Id = getStoreId(SI);
        if (!Id.empty()) {
          FuncSet FS;
          findFunctions(V, FS);
          Changed |= mergeFuncSet(Id, FS, isFunctionPointer(V->getType()));
        } else {
          // errs() << "Empty StoreID: " << F->getName() << "::" << *SI << "\n";
        }
      }
    } else if (ReturnInst *RI = dyn_cast<ReturnInst>(I)) {
      // function returns
      if (isFunctionPointerOrVoid(F->getReturnType())) {
        Value *V = RI->getReturnValue();
        std::string Id = getRetId(F);
        FuncSet FS;
        findFunctions(V, FS);
        Changed |= mergeFuncSet(Id, FS, isFunctionPointer(V->getType()));
      }
    }
#endif
  }

  return Changed;
}

// collect function pointer assignments in global initializers
void CallGraphPass::processInitializers(Module *M, Constant *C, GlobalValue *V,
                                        std::string Id) {
  // structs
  if (ConstantStruct *CS = dyn_cast<ConstantStruct>(C)) {
    StructType *STy = CS->getType();

    if (!STy->hasName() && Id.empty()) {
      if (V != nullptr)
        Id = getVarId(V);
      else
        Id = "bullshit"; // Lewis: quick fix for V is nullptr
    }

    for (unsigned i = 0; i != STy->getNumElements(); ++i) {
      Type *ETy = STy->getElementType(i);
      if (ETy->isStructTy()) {
        std::string new_id;
        if (Id.empty())
          new_id = STy->getStructName().str() + "," + std::to_string(i);
        else
          new_id = Id + "," + std::to_string(i);
        processInitializers(M, CS->getOperand(i), NULL, new_id);
      } else if (ETy->isArrayTy()) {
        // nested array of struct
        processInitializers(M, CS->getOperand(i), NULL, "");
      } else if (isFunctionPointer(ETy)) {
        // found function pointers in struct fields
        if (Function *F = dyn_cast<Function>(CS->getOperand(i))) {
          std::string new_id;
          if (!STy->isLiteral()) {
            if (STy->getStructName().startswith("struct.anon.") ||
                STy->getStructName().startswith("union.anon")) {
              if (Id.empty())
                new_id = getStructId(STy, M, i);
            } else {
              new_id = getStructId(STy, M, i);
            }
          }
          if (new_id.empty()) {
            assert(!Id.empty());
            new_id = Id + "," + std::to_string(i);
          }
          Ctx->FuncPtrs[new_id].insert(getFuncDef(F));
        }
      }
    }
  } else if (ConstantArray *CA = dyn_cast<ConstantArray>(C)) {
    // array, conservatively collects all possible pointers
    for (unsigned i = 0; i != CA->getNumOperands(); ++i)
      processInitializers(M, CA->getOperand(i), V, Id);
  } else if (Function *F = dyn_cast<Function>(C)) {
    // global function pointer variables
    if (V) {
      std::string Id = getVarId(V);
      Ctx->FuncPtrs[Id].insert(getFuncDef(F));
    }
  }
}

bool CallGraphPass::doInitialization(Module *M) {

  KA_LOGS(1, "[+] Initializing " << M->getModuleIdentifier() << "\n");
  // collect function pointer assignments in global initializers
  for (GlobalVariable &G : M->globals()) {
    if (G.hasInitializer())
      processInitializers(M, G.getInitializer(), &G, "");
  }

  for (Function &F : *M) {
    // Lewis: we don't give a shit to functions in .init.text
    if (F.hasSection() && F.getSection().str() == ".init.text")
      continue;
    // collect address-taken functions
    if (F.hasAddressTaken())
      Ctx->AddressTakenFuncs.insert(&F);

    for (auto name: funcDumpPath) {
      if (F.getName() == name) {
        (Ctx->IRFuncDumpPath).insert(&F);
      }
    }
  }

  return false;
}

bool CallGraphPass::doFinalization(Module *M) {

  // update callee and caller mapping
  for (Function &F : *M) {
    for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
      // map callsite to possible callees
      if (CallInst *CI = dyn_cast<CallInst>(&*i)) {
        FuncSet &FS = Ctx->Callees[CI];
        // calculate the caller info here
        for (Function *CF : FS) {
          CallInstSet &CIS = Ctx->Callers[CF];
          CIS.insert(CI);
        }
      }
    }
  }

  return false;
}

bool CallGraphPass::doModulePass(Module *M) {
  bool Changed = true, ret = false;
  while (Changed) {
    Changed = false;
    for (Function &F : *M)
      Changed |= runOnFunction(&F);
    ret |= Changed;
  }
  return ret;
}

// debug
void CallGraphPass::dumpFuncPtrs() {
  raw_ostream &OS = outs();
  for (FuncPtrMap::iterator i = Ctx->FuncPtrs.begin(), e = Ctx->FuncPtrs.end();
       i != e; ++i) {
    // if (i->second.empty())
    //    continue;
    OS << i->first << "\n";
    FuncSet &v = i->second;
    for (FuncSet::iterator j = v.begin(), ej = v.end(); j != ej; ++j) {
      OS << "  " << ((*j)->hasInternalLinkage() ? "f" : "F") << " "
         << (*j)->getName().str() << "\n";
    }
  }
}

void CallGraphPass::dumpCallees() {
  RES_REPORT("\n[dumpCallees]\n");
  raw_ostream &OS = outs();
  OS << "Num of Callees: " << Ctx->Callees.size() << "\n";
  for (CalleeMap::iterator i = Ctx->Callees.begin(), e = Ctx->Callees.end();
       i != e; ++i) {

    CallInst *CI = i->first;
    FuncSet &v = i->second;
    // only dump indirect call?
    /*
    if (CI->isInlineAsm() || CI->getCalledFunction() || v.empty())
         continue;
     */

    Function *F = CI->getParent()->getParent();
    OS << "Caller:" << F->getName().str() << ";";
    /*
    OS << "CS:" << *CI << "\n";
    const DebugLoc &LOC = CI->getDebugLoc();
    OS << "LOC: ";
    LOC.print(OS);
    OS << "^@^";
    */
#if 0
        for (FuncSet::iterator j = v.begin(), ej = v.end();
             j != ej; ++j) {
            //OS << "\t" << ((*j)->hasInternalLinkage() ? "f" : "F")
            //    << " " << (*j)->getName() << "\n";
            OS << (*j)->getName() << "::";
        }
#endif

    v = Ctx->Callees[CI];
    OS << "Callees";
    for (FuncSet::iterator j = v.begin(), ej = v.end(); j != ej; ++j) {
      OS << ":" << (*j)->getName();
    }
    /*
    if (v.empty()) {
        OS << "!!EMPTY =>" << *CI->getCalledValue()<<"\n";
        OS<< "Uninitialized function pointer is dereferenced!\n";
    }
    */
    OS << "\n";
  }
  RES_REPORT("\n[End of dumpCallees]\n");
}

void CallGraphPass::dumpCallers() {
  RES_REPORT("\n[dumpCallers]\n");
  for (auto M : Ctx->Callers) {
    Function *F = M.first;
    CallInstSet &CIS = M.second;
    RES_REPORT("F : " << getScopeName(F) << "\n");

    for (CallInst *CI : CIS) {
      Function *CallerF = CI->getParent()->getParent();
      RES_REPORT("\t");
      if (CallerF && CallerF->hasName()) {
        RES_REPORT("(" << getScopeName(CallerF) << ") ");
      } else {
        RES_REPORT("(anonymous) ");
      }

      RES_REPORT(*CI << "\n");
    }
  }
  RES_REPORT("\n[End of dumpCallers]\n");
}


static const char *_builtin_syscall_prefix[] = {
  "compat_SyS_", "compat_sys_",       "SyS_",        "sys_",
  "__x64_sys",   "__x32_compat_sys_", "__ia32_sys_", "__ia32_compat_sys_"};


bool isSyscall(StringRef str) {
  for (int i = 0; i < 8; i++)
    if (str.startswith(_builtin_syscall_prefix[i]))
      return true;
  return false;
}

FuncSet visited;

// Static helper function within CallGraph.cc
// Returns base name if suffixed like ".NNNN", otherwise empty string.
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

// dumpCallPathsForFunc now determines the specific tree to use from PerFunctionCallTrees
void CallGraphPass::dumpCallPathsForFunc(llvm::Function *targetFunc, unsigned int limits) {
    if (!targetFunc) {
        // Optional: RES_REPORT or log if targetFunc is null
        return;
    }

    // Get or create the specific tree (map of nodes) for this targetFunc
    // from the PerFunctionCallTrees member map.
    // The key is targetFunc itself.
    std::map<llvm::Function*, CallTreeNode*>& specificTreeNodes = this->PerFunctionCallTrees[targetFunc];
    // Note: Using operator[] will default-construct an empty map if targetFunc is not yet a key.

    std::vector<llvm::Function*> currentPathData;
    FuncSet visitedInThisTraversal; 

    // Call the recursive helper, passing the reference to the specific tree nodes map
    recursiveDumpPaths(targetFunc, limits, currentPathData, visitedInThisTraversal, specificTreeNodes);
}

// recursiveDumpPaths now takes a reference to the specific tree map to populate
// void CallGraphPass::recursiveDumpPaths(llvm::Function *currentFunc,
//                                        unsigned int currentDepth,
//                                        std::vector<llvm::Function*> &path,
//                                        FuncSet &visitedNodesInDFS,
//                                        std::map<llvm::Function*, CallTreeNode*>& activeTreeNodes) { // Last param changed
//     if (!currentFunc) return;

//     if (currentDepth >= 100) {
//         std::string pathStr;
//         for (int i = path.size() - 1; i >= 0; --i) {
//             llvm::Function* funcInPath = path[i];
//             std::string funcNameForDisplay;
//             if (funcInPath) {
//                 std::string baseName = getBaseNameIfSuffixedString(funcInPath);
//                 funcNameForDisplay = !baseName.empty() ? baseName : funcInPath->getName().str();
//             } else { funcNameForDisplay = "[[INVALID_FUNC_IN_PATH]]"; }
//             pathStr += funcNameForDisplay;
//             if (i > 0) pathStr += " -> ";
//         }
//         RES_REPORT(pathStr + " ... [Path too deep, limit reached]\n");
//         return;
//     }

//     if (visitedNodesInDFS.count(currentFunc)) {
//         return;
//     }

//     path.push_back(currentFunc);
//     visitedNodesInDFS.insert(currentFunc);

//     CallInstSet callers = Ctx->Callers[currentFunc];
//     if (callers.empty() && !isSyscall(currentFunc->getName())) {
//         std::string baseNameStr = getBaseNameIfSuffixedString(currentFunc);
//         if (!baseNameStr.empty()) {
//             llvm::Module *M = currentFunc->getParent();
//             if (M) {
//                 llvm::Function *baseFunc = M->getFunction(baseNameStr);
//                 if (baseFunc && baseFunc != currentFunc) {
//                     auto it = Ctx->Callers.find(baseFunc);
//                     if (it != Ctx->Callers.end() && !it->second.empty()) {
//                         callers = it->second;
//                     }
//                 }
//             }
//         }
//     }

//     if (callers.empty() || isSyscall(currentFunc->getName())) {
//         std::string pathStr;
//         for (int i = path.size() - 1; i >= 0; --i) {
//             llvm::Function* funcInPath = path[i];
//             std::string funcNameForDisplay;
//             if (funcInPath) {
//                 std::string baseName = getBaseNameIfSuffixedString(funcInPath);
//                 funcNameForDisplay = !baseName.empty() ? baseName : funcInPath->getName().str();
//             } else { funcNameForDisplay = "[[INVALID_FUNC_IN_PATH]]"; }
//             pathStr += funcNameForDisplay;
//             if (i > 0) { pathStr += " -> "; }
//         }
//         RES_REPORT(pathStr);
//         RES_REPORT(" [You have reached an entry]\n\n");

//         // Tree building logic now uses the passed 'activeTreeNodes' reference
//         CallTreeNode* parentTreeNode = nullptr;
//         // Iterate path from entry point (last in 'path' vector) down to target (first in 'path' vector)
//         for (int i = path.size() - 1; i >= 0; --i) {
//             llvm::Function* pathFunc = path[i];
//             if (!pathFunc) continue;

//             std::string funcNameForDisplay;
//             std::string baseName = getBaseNameIfSuffixedString(pathFunc);
//             funcNameForDisplay = !baseName.empty() ? baseName : pathFunc->getName().str();
//             if (funcNameForDisplay.empty() && pathFunc) funcNameForDisplay = pathFunc->getName().str(); 
//             if (funcNameForDisplay.empty()) funcNameForDisplay = "[[UNKNOWN_FUNC]]";

//             CallTreeNode* currentTreeNode = getOrCreateNodeInTree(pathFunc, funcNameForDisplay, activeTreeNodes);
//             if (!currentTreeNode) continue;

//             if (parentTreeNode) {
//                 if (parentTreeNode->children.find(pathFunc) == parentTreeNode->children.end()) {
//                     parentTreeNode->children[pathFunc] = currentTreeNode;
//                 }
//             }
//             parentTreeNode = currentTreeNode;
//         }
//     } else {
//         // Recursive step
//         FuncSet processedCallers;
//         for (llvm::CallInst *ci : callers) {
//             llvm::Function *callerFunc = ci->getFunction();
//             if (callerFunc && !processedCallers.count(callerFunc)) {
//                 processedCallers.insert(callerFunc);
//                 // Pass 'activeTreeNodes' down in the recursive call
//                 recursiveDumpPaths(callerFunc, currentDepth + 1, path, visitedNodesInDFS, activeTreeNodes);
//             }
//         }
//     }

//     visitedNodesInDFS.erase(currentFunc);
//     path.pop_back();
// }
// recursiveDumpPaths now takes a reference to the specific tree map to populate
void CallGraphPass::recursiveDumpPaths(llvm::Function *currentFunc,
                                       unsigned int currentDepth,
                                       std::vector<llvm::Function*> &path,
                                       FuncSet &visitedNodesInDFS,
                                       std::map<llvm::Function*, CallTreeNode*>& activeTreeNodes) {
    if (!currentFunc) return;

    if (currentDepth >= 100) {
        std::string pathStr;
        for (int i = path.size() - 1; i >= 0; --i) {
            llvm::Function* funcInPath = path[i];
            std::string funcNameForDisplay;
            if (funcInPath) {
                std::string baseName = getBaseNameIfSuffixedString(funcInPath);
                funcNameForDisplay = !baseName.empty() ? baseName : funcInPath->getName().str();
                // funcNameForDisplay = funcInPath->getName().str();
            } else { funcNameForDisplay = "[[INVALID_FUNC_IN_PATH]]"; }
            pathStr += funcNameForDisplay;
            if (i > 0) pathStr += " -> ";
        }
        RES_REPORT(pathStr + " ... [Path too deep, limit reached]\n");
        return;
    }

    if (visitedNodesInDFS.count(currentFunc)) {
        return;
    }
 
    path.push_back(currentFunc);
    visitedNodesInDFS.insert(currentFunc);

    // --- START MODIFICATION ---
    CallInstSet aggregatedCallers;
    llvm::Module *M = currentFunc->getParent();

    // 1. Add direct callers of currentFunc
    auto itCurrent = Ctx->Callers.find(currentFunc);
    if (itCurrent != Ctx->Callers.end()) {
        aggregatedCallers.insert(itCurrent->second.begin(), itCurrent->second.end());
    }

    if (M) { // Ensure module context is available
        std::string baseNameOfCurrent = getBaseNameIfSuffixedString(currentFunc);

        if (!baseNameOfCurrent.empty()) {
            // currentFunc is a suffixed version (e.g., "foo.1234").
            // Add callers of its base function ("foo").
            llvm::Function *baseFunc = M->getFunction(baseNameOfCurrent);
            if (baseFunc && baseFunc != currentFunc) { // Make sure baseFunc is valid and not currentFunc itself
                auto itBase = Ctx->Callers.find(baseFunc);
                if (itBase != Ctx->Callers.end()) {
                    aggregatedCallers.insert(itBase->second.begin(), itBase->second.end());
                }
            }
        } else {
            // currentFunc is a base name (e.g., "foo") or not suffixed in the .NNNN pattern.
            // Add callers of all its suffixed versions (e.g., "foo.1", "foo.2345").
            StringRef currentFuncNameRef = currentFunc->getName();
            for (llvm::Function &PotentialSuffixedF : *M) {
                if (&PotentialSuffixedF == currentFunc) continue; // Skip itself

                std::string baseNameOfPotential = getBaseNameIfSuffixedString(&PotentialSuffixedF);
                // Check if PotentialSuffixedF is a suffixed version of currentFunc
                if (!baseNameOfPotential.empty() && baseNameOfPotential == currentFuncNameRef) {
                    auto itSuffixed = Ctx->Callers.find(&PotentialSuffixedF);
                    if (itSuffixed != Ctx->Callers.end()) {
                        aggregatedCallers.insert(itSuffixed->second.begin(), itSuffixed->second.end());
                    }
                }
            }
        }
    }
    // --- END MODIFICATION ---

    // Now, use aggregatedCallers instead of the old 'callers' variable
    if (aggregatedCallers.empty() || isSyscall(currentFunc->getName())) {
        // Path termination logic (entry point or syscall reached)
        std::string pathStr;
        for (int i = path.size() - 1; i >= 0; --i) {
            llvm::Function* funcInPath = path[i];
            std::string funcNameForDisplay;
            if (funcInPath) {
                std::string baseName = getBaseNameIfSuffixedString(funcInPath);
                funcNameForDisplay = !baseName.empty() ? baseName : funcInPath->getName().str();
                // funcNameForDisplay = funcInPath->getName().str();
            } else { funcNameForDisplay = "[[INVALID_FUNC_IN_PATH]]"; }
            pathStr += funcNameForDisplay;
            if (i > 0) { pathStr += " -> "; }
        }
        RES_REPORT(pathStr);
        RES_REPORT(" [You have reached an entry]\n\n");

        CallTreeNode* parentTreeNode = nullptr;
        for (int i = path.size() - 1; i >= 0; --i) {
            llvm::Function* pathFunc = path[i];
            if (!pathFunc) continue;

            std::string funcNameForDisplay;
            std::string baseName = getBaseNameIfSuffixedString(pathFunc);
            funcNameForDisplay = !baseName.empty() ? baseName : pathFunc->getName().str();
            // funcNameForDisplay = pathFunc->getName().str();
            if (funcNameForDisplay.empty() && pathFunc) funcNameForDisplay = pathFunc->getName().str(); 
            if (funcNameForDisplay.empty()) funcNameForDisplay = "[[UNKNOWN_FUNC]]";

            CallTreeNode* currentTreeNode = getOrCreateNodeInTree(pathFunc, funcNameForDisplay, activeTreeNodes);
            if (!currentTreeNode) continue;

            if (parentTreeNode) {
                if (parentTreeNode->children.find(pathFunc) == parentTreeNode->children.end()) {
                    parentTreeNode->children[pathFunc] = currentTreeNode;
                }
            }
            parentTreeNode = currentTreeNode;
        }
    } else {
        // Recursive step
        FuncSet processedCallers; // To avoid redundant recursive calls for the same caller function
        for (llvm::CallInst *ci : aggregatedCallers) {
            // The function that CONTAINS this call instruction is the actual caller function
            llvm::Function *callerFunc = ci->getParent()->getParent(); 
            if (callerFunc && !processedCallers.count(callerFunc)) {
                processedCallers.insert(callerFunc);
                recursiveDumpPaths(callerFunc, currentDepth + 1, path, visitedNodesInDFS, activeTreeNodes);
            }
        }
    }

    visitedNodesInDFS.erase(currentFunc);
    path.pop_back();
}


