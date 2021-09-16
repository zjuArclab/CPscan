//===-- Analyzer.cc - the kernel-analysis framework--------------===//
//
// This file implements the analysis framework. It calls the pass for
// building call-graph and the pass for finding deleted security operation.
//
// ===-----------------------------------------------------------===//

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/Path.h"
#include <memory>
#include <vector>
#include <sstream>
#include <sys/resource.h>
#include "Analyzer.h"
#include "CallGraph.h"
#include "Config.h"
#include "SecurityChecks.h"
#include "llvm-diff.h"

using namespace llvm;

// Command line parameters.
cl::list<string> InputFilenames(
    cl::Positional, cl::OneOrMore, cl::desc("<input bitcode files>"));

cl::opt<unsigned> VerboseLevel(
    "verbose-level", cl::desc("Print information at which verbose level"),
    cl::init(0));

cl::opt<bool> SecurityChecks(
    "sc", 
    cl::desc("Identify sanity checks"), 
    cl::NotHidden, cl::init(false));

GlobalContext KGlobalCtx, FGlobalCtx;


void IterativeModulePass::run(ModuleList &modules) {

  ModuleList::iterator i, e;
  OP << "[" << ID << "] Initializing " << modules.size() << " modules ";
  bool again = true;
  while (again) {
    again = false;
    for (i = modules.begin(), e = modules.end(); i != e; ++i) {
      again |= doInitialization(i->first);
      OP << ".";
    }
  }
  OP << "\n";

  unsigned iter = 0, changed = 1;
  while (changed) {
    ++iter;
    changed = 0;
    unsigned counter_modules = 0;
    unsigned total_modules = modules.size();
    for (i = modules.begin(), e = modules.end(); i != e; ++i) {
      OP << "[" << ID << " / " << iter << "] ";
      OP << "[" << ++counter_modules << " / " << total_modules << "] ";
      OP << "[" << i->second << "]\n";

      bool ret = doModulePass(i->first);
      if (ret) {
        ++changed;
        OP << "\t [CHANGED]\n";
      } else
        OP << "\n";
    }
    OP << "[" << ID << "] Updated in " << changed << " modules.\n";
  }

  OP << "[" << ID << "] Postprocessing ...\n";
  again = true;
  while (again) {
    again = false;
    for (i = modules.begin(), e = modules.end(); i != e; ++i) {
      again |= doFinalization(i->first);
    }
  }

  OP << "[" << ID << "] Done!\n\n";
}

void LoadStaticData(GlobalContext *GCtx) {
	SetErrorHandleFuncs(GCtx->ErrorHandleFuncs);
	SetCopyFuncs(GCtx->CopyFuncs);
  SetLockFuncs(GCtx->LockFuncs);
  SetPairFuncs(GCtx->PairFuncs);

  SetRRFuncs((GCtx->ResourceReleaseFuncs));

  SetHeapAllocFuncs(GCtx->HeapAllocFuncs);
  
  SetInitFuncs(GCtx->InitFuncs);
}

void ProcessResults(GlobalContext *GCtx) {
}

int main(int argc, char **argv) {

	// Print a stack trace if we signal out.
	sys::PrintStackTraceOnErrorSignal(argv[0]);
	PrettyStackTraceProgram X(argc, argv);
	llvm_shutdown_obj Y;  
	cl::ParseCommandLineOptions(argc, argv, "global analysis\n");
	SMDiagnostic Err;
  ModulePairList modulepairlist;

	// Loading modules
	OP << "Total " << InputFilenames.size() << " file(s)\n";
	for (unsigned i = 0; i < InputFilenames.size(); ++i) {
		LLVMContext *LLVMCtxKernel = new LLVMContext();
    LLVMContext *LLVMCtxFirmware = new LLVMContext();
    StringRef MKName = InputFilenames[i];
    string firmwarename = strdup(InputFilenames[i].data());
    
    firmwarename.replace(firmwarename.find("3.3.8.k"),7,"3.3.8.f");
    StringRef MFName = StringRef(firmwarename);
    if(LLVMCtxKernel==NULL)
      OP<<"ERROR, LLVMCtxKernel is NULL\n";
    if(LLVMCtxKernel==NULL)
      OP<<"ERROR, LLVMCtxFirmware is NULL\n";

    unique_ptr<Module> MK = parseIRFile(MKName, Err, *LLVMCtxKernel);
		unique_ptr<Module> MF = parseIRFile(MFName, Err, *LLVMCtxFirmware);
		if (MK == NULL) {
			OP << argv[0] << ": MK, Analyzer, error loading file "<< MKName << "\n";
			continue;
		}
    if (MF == NULL) {
			OP << argv[0] << ":MF, Analyzer,  error loading file "<< MFName << "\n";
			continue;
		}

		Module *ModuleKernel = MK.release();
    Module *ModuleFirmware = MF.release();
    if (ModuleKernel == NULL) {
			OP << argv[0] << ": MK, Analyzer, error releasing file.\n";
			continue;
		}
    if (ModuleFirmware == NULL) {
			OP << argv[0] << ":MF, Analyzer,  error releasing file.\n ";
			continue;
		}
    StringRef KernelMName = StringRef(strdup(MKName.data()));
		StringRef FirmwareMName = StringRef(strdup(MFName.data()));
    KGlobalCtx.Modules.push_back(make_pair(ModuleKernel, KernelMName));
		FGlobalCtx.Modules.push_back(make_pair(ModuleFirmware, FirmwareMName));
		KGlobalCtx.ModuleMaps[ModuleKernel] = KernelMName;
    FGlobalCtx.ModuleMaps[ModuleFirmware] = FirmwareMName;
    modulepairlist.push_back(make_pair(ModuleKernel, ModuleFirmware));
	}

	LoadStaticData(&KGlobalCtx);
  LoadStaticData(&FGlobalCtx);
	CallGraphPass KCGPass(&KGlobalCtx);
	KCGPass.run(KGlobalCtx.Modules);
  CallGraphPass FCGPass(&FGlobalCtx);
	FCGPass.run(FGlobalCtx.Modules);
  Check_OMP(&modulepairlist, &KGlobalCtx, &FGlobalCtx);
   
	return 0;
}
