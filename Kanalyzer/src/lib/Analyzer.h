#ifndef ANALYZER_GLOBAL_H
#define ANALYZER_GLOBAL_H

#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Instructions.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Support/Path.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Analysis/AliasAnalysis.h>
#include "llvm/Support/CommandLine.h"
#include <map>
#include <unordered_map>
#include <set>
#include <unordered_set>
#include <iostream>
#include <fstream>
#include <sstream>
#include <string>

#include "Common.h"
#include "llvm-diff.h"


// 
// typedefs
// pair module to its file name.
typedef vector< pair<llvm::Module*, llvm::StringRef> > ModuleList;

// pair kernelmodule to its firmwaremodule//
typedef vector< pair<llvm::Module*, llvm::Module*> > ModulePairList;

typedef vector< std::tuple<llvm::Function*,  std::string,  llvm::Function*,  std::string> > FuncPairList;

// Mapping module to its file name.
typedef std::unordered_map<llvm::Module*, llvm::StringRef> ModuleNameMap;

// The set of all functions.
typedef llvm::SmallPtrSet<llvm::Function*, 8> FuncSet;

// Mapping from function name to function.
typedef std::unordered_map<string, llvm::Function*> NameFuncMap;

// Mapping from function to the coressponding variable set.
typedef std::unordered_map<llvm::Function*, std::vector<Value*>*> FuncVarMap;

// The set of all call Instructions.
typedef llvm::SmallPtrSet<llvm::CallInst*, 8> CallInstSet;

// Mapping from function name to CallInstSet. Namely obtain all call instructions of a function.
typedef DenseMap<Function*, CallInstSet> CallerMap;

// Mapping from CallInst to function set. Namely obtain all potencial functions of a call instruction.
typedef DenseMap<CallInst *, FuncSet> CalleeMap;



struct GlobalContext {

	GlobalContext() {
		// Initialize statistucs.
		NumSecurityChecks = 0;
		NumCondStatements = 0;
	}

	unsigned NumSecurityChecks;
	unsigned NumCondStatements;

	// Map global function name to function.
	NameFuncMap GlobalFuncs;

	// Map all function name to function.
	NameFuncMap AllFuncs;

	FuncVarMap VarOfFunc;

	// Functions whose addresses are taken.
	FuncSet AddressTakenFuncs;

	// Map a callsite to all potential callee functions.
	CalleeMap Callees;

	// Map a function to all potential caller instructions.
	CallerMap Callers;

	// Indirect call instructions.
	std::vector<CallInst *>IndirectCallInsts;

	// Unified functions -- no redundant inline functions
	DenseMap<size_t, Function *>UnifiedFuncMap;
	set<Function *>UnifiedFuncSet;

	// Map function signature to functions
	DenseMap<size_t, FuncSet>sigFuncsMap;

	// Modules.
	ModuleList  Modules;
	ModuleNameMap ModuleMaps;
	set<string> InvolvedModules;

	// SecurityChecksPass
	// Functions handling errors
	set<string> ErrorHandleFuncs;
	std::multimap<std::string, std::string> LockFuncs;
	
	std::multimap<std::string, std::string> PairFuncs;

	std::map<std::string, std::pair<uint8_t, int8_t>> InitFuncs;

	std::map<std::string, std::pair<uint8_t, int8_t>> ResourceReleaseFuncs;

	std::set<std::string> HeapAllocFuncs;

	map<string, std::tuple<int8_t, int8_t, int8_t>> CopyFuncs;
	
	// Identified sanity checks
	DenseMap<Function *, set<SecurityCheck>> SecurityCheckSets;
	DenseMap<Function *, set<Value *>> CheckInstSets;
};


class IterativeModulePass {
protected:
	GlobalContext *Ctx;
	const char * ID;
public:
	IterativeModulePass(GlobalContext *Ctx_, const char *ID_)
		: Ctx(Ctx_), ID(ID_) { }

	// Run on each module before iterative pass.
	virtual bool doInitialization(llvm::Module *M)
		{ return true; }

	// Run on each module after iterative pass.
	virtual bool doFinalization(llvm::Module *M)
		{ return true; }

	// Iterative pass.
	virtual bool doModulePass(llvm::Module *M)
		{ return false; }

	virtual void run(ModuleList &modules);
};

#endif
