#ifndef KEY_STRUCTURE_ANALYZER_H
#define KEY_STRUCTURE_ANALYZER_H

#include <llvm/IR/Function.h>
#include <llvm/IR/Value.h>
#include <set>
#include <vector>
#include <string>

// Forward declaration
struct GlobalContext;

class KeyStructureAnalyzer {
public:
    explicit KeyStructureAnalyzer(GlobalContext* Ctx);

    // Analyzes a given call path for key structures and reports findings.
    // - targetFunction: The root function of the path (path[0]).
    // - callPath: The complete call path vector (from targetFunction to entryPointFunction).
    // - entryPointFunction: The entry point of this specific trace (path.back() or equivalent).
    // - pathIdentifierString: A string representation of the path for logging.
    void analyzePathForKeyStructures(
        llvm::Function* targetFunction,
        const std::vector<llvm::Function*>& callPath,
        llvm::Function* entryPointFunction,
        const std::string& pathIdentifierString
    );

private:
    GlobalContext* Ctx; // Pointer to the global context, needed for Ctx->Callers

    // The backward tracing logic.
    void backwardTraceForKeyStructure(
        llvm::Value* startValue,
        const std::string& pathIdentifier,
        std::set<llvm::Value*>& potentialKeyStructures,
        const std::vector<llvm::Function*>& currentCallPath,
        llvm::Function* rootInterfaceFuncForThisPath
    );
};

#endif // KEY_STRUCTURE_ANALYZER_H 