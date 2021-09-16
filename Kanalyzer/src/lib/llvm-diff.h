#include <llvm/IR/Module.h>
#include <llvm/Analysis/TargetLibraryInfo.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/IR/DebugInfo.h>
#include <unistd.h>
#include <bitset>
#include <chrono>
#include "CFG-diff.h"
#include "Analyzer.h"

using namespace llvm;
using namespace std;

#define scheck 0
#define uintial 1
#define ulock 2
#define pfunc 3
#define resourcerelease 4

#define MultiThread 1
#define Number_of_threads 8000


//using namespace boost;
//Start of new added
typedef vector< pair<llvm::Module*, llvm::StringRef> > ModuleList;

typedef vector< pair<llvm::Module*, llvm::Module*> > ModulePairList;

typedef std::unordered_map<llvm::Module*, llvm::StringRef> ModuleNameMap;

struct replaceresult replace_all(string& str, string& old_value, string& new_value);  

string normalizeBB(string str);

void RecordBCFiles(char *basePath, vector<string> BCList);

string Statics(ModuleList &modules);

map<string, string> ObtainPairOfBCfile(char *FirmwareBCDir, char *KernelBCDir);

char* Convertstr2char(string s);

Instruction* ObtainConds(Instruction *Inst);

vector<Value*> ObtainConds(Function *F);

void CompareConds(Function *F, vector<Value*> FConds, Function *K, vector<Value*> KConds);

void PraseCond(ICmpInst *IC );

void PraseInst(Instruction *I);

void unrollLoops_k(Function *F);

void unrollLoops_l(Function *F);

void rewritting(Function *F, GlobalContext *GlobalCtx);

Instruction* FindFirstValidateInst(BasicBlock *curBB);

unsigned getICmpCode(const ICmpInst *ICI, bool InvertPred);

bool IsSecurityCheckStopExe(Function *F, Instruction *I);

void *CompareCFG(void *cmpParas);

string filterIR_dbg(string str, string filter);

string filterIR_dbg_r(string str, string filter,string split);

string filterIR_metadata(string str);
string filterIR_tbaa(string str);
string Filter(string str);
string Filter_V1(string BBContend);
bbl_info InitBBL();
void AddChild(bbl_info b, int childNo);
vector<int>  Obtainchildren(ChildrenNode childList);
void FindParent_sibling(std::map<int, bbl_info> basicBlockInfo);

std::pair<int, double> CompareCFG_GM_cmp(Function *F, Function *K, string MKName, GlobalContext *KGlobalCtx, GlobalContext *FGlobalCtx);

void Check_OMP(ModulePairList *modulepairlist, struct GlobalContext *KGlobalCtx, struct GlobalContext *FGlobalCtx);

void Check_OMP_GM_cmp( ModulePairList *modulepairlist,  GlobalContext *KGlobalCtx,  GlobalContext *FGlobalCtx);

void Check_Deleted_Func( ModulePairList *modulepairlist,  GlobalContext *KGlobalCtx,  GlobalContext *FGlobalCtx);

void TranverseBC( ModulePairList *modulepairlist,  GlobalContext *KGlobalCtx,  GlobalContext *FGlobalCtx);
//End of new added
void TranverseF( Function *F);
