#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/PassManager.h"
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
#include "llvm/IR/CFG.h" 
#include "llvm/Transforms/Utils/BasicBlockUtils.h" 
#include "llvm/IR/IRBuilder.h"
#include <llvm/IR/DebugInfo.h>
#include <llvm/Pass.h>
#include <llvm/IR/Instructions.h>
#include "llvm/IR/Instruction.h"
#include <llvm/Support/Debug.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Constants.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Analysis/CallGraph.h>
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"  
#include "llvm/IR/InstrTypes.h" 
#include "llvm/IR/BasicBlock.h" 
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include <llvm/IR/InlineAsm.h>
#include <iostream>
#include <memory>
#include <vector>
#include <sstream>
#include <map>
#include <sys/resource.h>
#include<queue>
#include "Analyzer.h"
#include "Config.h"
#include "Common.h"
#include "MCS.hpp"

using namespace boost;
using namespace std;
using namespace llvm;

#define RecordDate "09-16"
#define kernel_eddition "3-3-8"


#define SourceCode_DIR "/CPscan/Kanalyzer/data/sourceCode/linux-"
#define SRC_DIR  "/CPscan/Kanalyzer/src/"
#define DATA_DIR  "/CPscan/Kanalyzer/data/bcfs/"



/*
nohup ./kanalyzer  -sc @../bcList/linux-stable-3.3.8.k-filteredBC.txt >> nohup/09-16/nohup-3.3.8-omp 2>&1 &
*/






#ifndef CFG_diff
#define CFG_diff
#define finegrain 0
#define Threshhod 0.6
#define Threshhod_process_0 0.1

#define Threshhod_process_1 0.9
#define Threshhod_process_1_2 0.85

#define Threshhod_process_2 0.7

#define Threshhod_process_3 0.5
#define Threshhod_process_4 0.4
#define SizeofLargeCFG 0


#define RECORD
#define InstRaioThreshhod  0.25
#define RelatedVetexRaioThreshhod  0.5
#define InstCMPThreshhod  0.2
#define InstCMPThreshhod_2 0.4
#define InstCMPThreshhod_3 0.7
#define DiffNum 10
#define TraceUse
#define analyzeDeleteSS
#define BUFFERSIZE 3000000
#define DumpSIZE 3000
#define NUM_THREADS  40000
#define NewBasicBlockID 1000
#define MultiThread 1
#define splitSize 6


typedef std::multimap<Value*, Instruction*> USESEQ; 

typedef std::pair<Instruction*, stack<string>> mul_key;

// key: <Instruction *inst, string pattern> value: vector<Instruction*>
typedef std::multimap<mul_key, vector<Instruction*>> mul_USESEQ;

typedef std::tuple<Value*, vector<Instruction*> , Value*, vector<Instruction*>> CVRecord;

typedef std::tuple<mul_key, vector<vector<Instruction*>> , mul_key, vector<vector<Instruction*>>> m_CVRecord;

typedef USESEQ::iterator USESEQIterator;
typedef mul_USESEQ::iterator mul_USESEQIterator;

typedef std::tuple< int, vector<int>, vector<string>, vector<int>,  vector<int>,  vector<string>, vector<string>>  Feature;

typedef std::pair<int,vector<string>> ShortInst;

typedef std::tuple<std::pair<llvm::Instruction*, int>,std::pair<llvm::Instruction*, int>, int> IdenticalInst;

typedef std::tuple<double, vector<IdenticalInst>, map<llvm::Instruction*, int>, float, string, double> SigMatchResult;

typedef std::tuple<Instruction*, std::vector<USESEQ>,Instruction*, std::vector<USESEQ>>  InstMatchItem;

typedef std::tuple<std::map<int, std::vector<int>>, string, vector<int>> NToOneResult;

typedef std::tuple<std::map<int, std::vector<int>>, std::map<int, std::vector<int>>, vector<int>, std::map<int, int>> SplitResult;


struct replaceresult{
        string str;
        int replace;
} ;

typedef struct Parent *ParentNode;
typedef struct Parent{
    int  Data;
    ParentNode Next;
}parent;

typedef struct Children *ChildrenNode;
typedef struct Children{
    int  Data;
    ChildrenNode Next;
}child;

typedef struct Silibing *SilbingNode;
typedef struct Silibing{
    int  Data;
    SilbingNode Next;
}silbling;



typedef struct BBL_Info *bbl_info;
typedef struct BBL_Info{
    //string contend;
    int BBLID;
    size_t BBhash;
    int CMPtime = 0;
    llvm::BasicBlock* bbl;
    vector<llvm::Instruction*> Instructions;
    ParentNode parentnode;
    ChildrenNode childrennode;
    SilbingNode silibingnode;
    // Sensitive Instruction within a basic block
    map<llvm::Instruction*, int> Sensitive_Info; 
    Feature Inbbfeature;
    std::vector<int> ConnectedMCSNodes;
    std::map<int, pair<double, SigMatchResult>> MatchRecords;
}bbl;

typedef std::map<int,bbl_info> Mapbbl;

typedef struct sensitive_item{
    int bbl_NO;
    int type;
    llvm::Instruction *inst;
}Sensitive_item;

struct CmpParas{
   Function *F; 
   Function *K; 
   int  thread_id;
   char *message;
   string KBCName; 
   string FBCName; 
   struct GlobalContext *KGlobalCtx; 
   struct GlobalContext *FGlobalCtx;
   pthread_mutex_t *mutex;
};

typedef struct sensitive_info_of_function{
    llvm::Function *F;
    int size;
    Sensitive_item sen_list[200];
}Sensitive_Info_of_Functions;



struct thread_data{
   int  thread_id;
   char *message;
   pthread_mutex_t *mutex;
};

// The element (i.e., field) of the tracked object.
// Define UserGraph
struct Element {
	// The offset(in bytes) of current element into the base of the 
	// tracked object. It can be negative.
	int offset;
	// The size of the element.
	unsigned size;
	// Reference hierarchy is to understand if a pointer (pointing to 
	// the current element) is directly or indirectly (recursively) 
	// pointing to the tracked object. The “indirectness” is decreased 
	// by one by LoadInst; but increased by one by StoreInst.
	int refHierarchy;
	// If a GEP instruciton does not have constant indices, the 
	// obtained element will be unknown. In this case, we will label it 
	// as unknown to be conservative, and do not do initialization 
	// analysis but only reachability analysis for it.
	bool unknownOffset;

	// The upper element that contains current element.
	Element *parentEle;


	Element() {
		parentEle = NULL;
	}

	Element(Element *Ele) {
		memcpy(this, Ele, sizeof(Element));
	}

	Element(Value *Alloc, const DataLayout *DL) {
		// Stack allocation
		if (AllocaInst *AI = dyn_cast<AllocaInst>(Alloc)) {
			// Static allocation
			if (AI->isStaticAlloca()) {
				Type *allocTy = AI->getAllocatedType();
				unsigned tySize = DL->getTypeAllocSize(allocTy);
				unsigned arraySize = 
					cast<ConstantInt>(AI->getArraySize())->getZExtValue();
				size = tySize * arraySize;;
				unknownOffset = false;
			}
			// Dynamic alloaction
			else {
				size = 0;
				unknownOffset = true;
			}
		}
		// Heap allocation
		else if (CallInst *CI = dyn_cast<CallInst>(Alloc)){
			Value *SizeArg = CI->getArgOperand(0);
			ConstantInt *CSizeArg = dyn_cast<ConstantInt>(SizeArg);
			// Static malloc -- its size is constant
			if (CSizeArg) {
				size = CSizeArg->getZExtValue();
				unknownOffset = false;
			}
			// Dynamic malloc
			else {
				size = 0;
				unknownOffset = true;
			}
		}
		else 
			report_fatal_error("Unrecognized allocation");

		offset = 0;
		// Originally, it is a pointer to the allocated memory.
		refHierarchy = -1;
		parentEle = NULL;
	}

	// Set the offset and size of current element based on the 
	// given GEP instruction.
	bool UpdateByGEP(GEPOperator *GEP, const DataLayout *DL);

};

struct BBNode;

struct UserNode {
	UserNode(Value *U, Element *Ele) {
		this->U = U;
		ele = Ele;
	}
	Value *U;
	std::set<UserNode *>nextUserNodes;
	std::set<UserNode *>preUserNodes;

	Element *ele;

	BBNode *BBN;

	std::set<uint8_t *>flagsCaches;
};

struct BBNode {
	BasicBlock *BB;
	// Do not change order
	std::list<UserNode *>userNodes;

	void Insert(UserNode *UN);
};

typedef std::map<BasicBlock *, BBNode *> BBMap;
typedef std::set< std::pair<BBNode *, BasicBlock *> > BBPairSet;

struct UserGraph {

	UserNode *FirstUN;
	BBNode *FirstBBN;

	BBMap involvedBBs;

	// The set of being used values, including alias
	std::set<Value *> usedValues;

	// Build the user graph of the given value
	UserGraph(Value *V, Value *StartUser, Element *Ele) {

		// No users
		if (V->use_empty()) {
			return;
		}

		usedValues.insert(V);

		FirstUN = new UserNode(V, Ele);
		FirstBBN = new BBNode();
		FirstUN->BBN = FirstBBN;
		FirstBBN->BB = GetBasicBlock(V);
		involvedBBs[FirstBBN->BB] = FirstBBN;

		PutUserInBB(V, Ele, StartUser);

		if (FirstBBN->userNodes.size()) { 
			FirstUN->nextUserNodes.insert(FirstBBN->userNodes.front());
			FirstBBN->userNodes.front()->preUserNodes.insert(FirstUN);
		}
		FirstBBN->userNodes.push_front(FirstUN);

		// Connect BBNodes
		BBPairSet BBSet;
		ConnectUserNodes(FirstBBN, FirstBBN->BB, &BBSet);
	}

	~UserGraph() {

		for (auto BBI : involvedBBs) {
			for (UserNode *UN : BBI.second->userNodes) {
				for (uint8_t *Flags : UN->flagsCaches)
					free(Flags);
				delete UN;
			}
			delete BBI.second;
		}
	}

	BasicBlock *GetBasicBlock(Value *V) {

		BasicBlock *BB = NULL;
		if (Instruction *I = dyn_cast<Instruction>(V))
			BB = I->getParent();
		else if (Argument *Arg = dyn_cast<Argument>(V))
			BB = &(Arg->getParent()->getEntryBlock());
		else {
			User *U = dyn_cast<User>(V);
			assert (!U->use_empty());
			if (Instruction *I = dyn_cast<Instruction>(U->user_back()))
				BB = I->getParent();
			else
				report_fatal_error("Unknown type of value");
		}

		return BB;
	}

	bool Dominate(Value *A, Value *B, BasicBlock *BB) {
		if (A == B)
			return false;
		if (isa<Argument>(A))
			return true;

		assert(isa<Instruction>(B));

		Instruction *IA = dyn_cast<Instruction>(A);
		if (!IA) {
			User *U = dyn_cast<User>(A);
			IA = dyn_cast<Instruction>(U->user_back());
		}

		for (BasicBlock::iterator i = BB->begin(), 
				e = BB->end(); i != e; ++i) {
			Instruction *I = &*i;
			if (I == IA)
				return true;
			if (I == B)
				return false;
		}

		return false;
	}

	// Get all reachable basic blocks of the value.
	void GetReachableBBs(Value *V, std::set<BasicBlock *> *BBs);
	// Put the users of the given value into the corresponding BBNode.
	void PutUserInBB(Value *V, Element *Ele,
			Value *StartUser, bool IsNew = true);

	// Connect user nodes into UserGraph.
	void ConnectUserNodes(BBNode *From, BasicBlock *ToSucc, 
			BBPairSet *BBSet);

	// Disconnect basic block nodes.
	void DisconnectBBNodes(BBNode *From);

	// Merge the users of the given value into this graph.
	void MergeUsers(Value *V, Element *Ele, Value *StartUser);

	// Print user graph.
	void PrintUserNode(UserNode *UN, std::set<UserNode *> *Printed);
	void PrintGraph(Value *V);
};
// end of define UserGraph

bool Is_element_in_vector(std::vector<int> v,int element);
bool Is_element_in_stingvector(multimap<std::string, std::string> PairsFuncs,string element);
int dump_buffer(string logs, string file_to_dump);
int dump_buffer1(string logs, string file_to_dump);
void DumpDeletedBBInfo(string analysisfile, bbl_info b, string dumpfile);
void searchQueue(std::queue<int>  q);
bbl_info search_Mapbbl(Mapbbl m_KbasicBlockInfo, int kcommon_vetex);
Mapbbl convert_Mapbbl(Mapbbl m_KbasicBlockInfo);
vector<int> ObtainParentList(bbl_info b);
vector<int> ObtainChildrenList(bbl_info b);
vector<int> ObtainSilbingList(bbl_info b);
bool IsValideOperand(Value *operand);
void DeleElem(vector<int> *v, int e);
void AddCMPItem(bbl_info bbl, int basicblockID, double Similarity, SigMatchResult smr);
std::map<int,int>  ObtainRelatedVetex(bbl_info b, std::vector<int> common_node );
bool IsInMCS(std::map<int,int> *MCSMap, int BBIDK);
int IsSensitive(llvm::BasicBlock *bbl, struct GlobalContext *GlobalCtx);
std::map<int,int>  ObtainCandicateVetex(std::map<int,int> *relatedvetex , int type );
// SigMatchResult SigMatch(bbl_info rk, bbl_info rf);
SigMatchResult SigMatch(bbl_info rk, bbl_info rf, std::map<int,int> *MCSMap);
//Feature bblFeature(llvm::BasicBlock *bbl);
Feature bblFeature(vector<Instruction*> Instructions);
void Missing_Instructions(llvm::BasicBlock *bblk, llvm::BasicBlock *bblf);
void Printmap(map<llvm::Instruction*, int> v);
std::vector<int> ObtainRemainVetex(std::vector<int> remain_graph, std::map<int,int> relatedvetex);
std::pair<Sensitive_Info_of_Functions*, std::set<int>> ObtainsensitiveBBLset(Mapbbl *basicBlockInfo,std::vector<int> common_node);
void UpdateVetex(int basicblockIDk, std::queue<int> *kcommon_subgraph,
std::vector<int> *kcommon_node, std::vector<int> *remain_graph1, set<int> *SScfgk, int basicblockIDf, std::queue<int> *fcommon_subgraph,
std::vector<int> *fcommon_node,std::vector<int> *remain_graph2, set<int> *SScfgf,std::map<int,int> *MCSMap);
void UpdateVetex(int basicblockID, std::vector<int> * remain_graph, set<int> SScfg);
void UpdateVetex(int basicblockID, std::vector<int> *remain_graph);
void UpdateVetex(int basicblockIDk,std::queue<int> *kcommon_subgraph,
std::vector<int> *kcommon_node, std::vector<int> *remain_graph1, int basicblockIDf, std::queue<int> *fcommon_subgraph,
std::vector<int> *fcommon_node,std::vector<int> *remain_graph2,std::map<int,int> *MCSMap);
void UpdateDeletedBBlist(int basicblockIDk,std::vector<int> 
*remain_graph1,set<int> *SScfgk,std::vector<int> *DeletedBBlist);
void UpdatedeletedSSlist(map<llvm::Instruction*, int> *deletedSSlist, std::map<llvm::Instruction*, int> *DeletedSSlists);
string getFileExt(const string& s, const string& delimiter);
string DeleteFileExt(const string& s, const string& delimiter);
void UpdateDeletedBBlistN(int basicblockIDk,std::vector<int> 
*remain_graph1,std::vector<int> *DeletedBBlist);
int FindNode(std::map<int,int> *MCSMap, int kcommon_vetex);
void AnalyzeDeleteSS(std::map<llvm::Instruction*, int> *deletedSSlistr,  std::map<int,int> *MCSMap,std::vector<int> *remain_graph2, Mapbbl *KbasicBlockInfo, Mapbbl *FbasicBlockInfo,  string filename);
void PrintmapII(std::map<int,int>  krelatedvetex);
void RecordLog(char* local_msg, char* logs, string filename);
void RecordLog(char* local_msg, string logs, string filename);
void RecordLog(char* local_msg, char* logs, string filename, pthread_mutex_t *mutex);
void RecordLog(char* local_msg, string logs, string filename, pthread_mutex_t *mutex);
void Printmap(map<llvm::Instruction*, int> v);
void PrintSet(set<int> s);
void PrintVectorI(vector<int> v);
std::set<int> MergeNode(set<int> left, set<int> right, set<int> L, set<int> R);
std::set<int> MergeNode(set<int> left, set<int> right);
void ContainCheck(bbl_info b);
void DeleteItem(std::vector<int> *V, int Ele);
bbl_info ObtainBBInfo(int BBLID, Mapbbl *basicBlockInfo);
bbl_info ObtainBBInfo(BasicBlock *BB, Mapbbl *basicBlockInfo);
void PrinteDSO(map<llvm::Instruction*, int> v, Mapbbl KbasicBlockInfo);
std::tuple<int,int,int,int,int>  TypeCount(map<llvm::Instruction*, int> v);
vector<int> FindMCSNode(std::map<int,int> *MCSMap, int pos);
void DumpIRMAP(std::map<int, Instruction*> *IRMAP, string file_to_dump);
double ObtainneighborSimilarity(bbl_info rk,  bbl_info rf, std::map<int,int> *MCSMap);
void DumpInputInfo(Mapbbl *KbasicBlockInfo, Mapbbl *FbasicBlockInfo, Sensitive_Info_of_Functions *sk, Sensitive_Info_of_Functions *sf, std::map<int,int> *MCSMap, string file_to_dump);
string DumpMCSMap(std::map<int,int> *MCSMap);
string DumpMCS(std::map<int,int> *MCSMap );
string DumpFunction(Function *F);
bbl_info  ConstructNewBasicBlock(bbl_info bbl0, bbl_info bbl1);
void printFunctionMessage(Function *F);
string getBlockName(BasicBlock *bb);
std::vector<Value*> Getargs(Function *F);
int FindPos(Value *op, Instruction *I);
void GraphMatch(Function *K, Mapbbl KBasicBlockInfo, Function *F, Mapbbl FBasicBlockInfo, string processfilename_tmp, std::map<int, int> *MCSMap );
//void DumpsensitiveBBInst(std::map<int, Instruction*> *sensitiveBBInst, string file_to_dump);
void GenerateDeletedSoNew(set<int> SScfgk,std::queue<int> *kcommon_subgraph,std::vector<int> *kcommon_node,Mapbbl KbasicBlockInfo,std::vector<int> *remain_graph1,
        set<int> SScfgf,std::queue<int> *fcommon_subgraph,std::vector<int> *fcommon_node,Mapbbl FbasicBlockInfo , std::vector<int> *remain_graph2,
        std::map<int,int> *MCSMap, std::vector<int> *DeletedBBlist, std::map<llvm::Instruction*, int> *DeletedSSlists,char*  local_msg, string filename) ;   
std::tuple<bool, string, string> CheckUseSequence(Instruction *deletedInst, Instruction *instk,  string filename, Mapbbl *KbasicBlockInfo, Mapbbl *FbasicBlockInfo,
                 std::vector<int> *remain_graph2, std::map<int,int> *MCSMap, int type);  
// End of Func definition

struct first_index_t {
    typedef vertex_property_tag kind;
  };
typedef property<first_index_t, std::string> FirstNameProperty;
typedef adjacency_list<vecS, vecS, directedS, 
                         FirstNameProperty> MyGraphType;

typedef adjacency_list<vecS, vecS, directedS,
    property<vertex_name_t, std::string,  
    property<vertex_index_t, unsigned long long> >,
    property<edge_name_t, std::string> > Graph;

typedef property_map<Graph, vertex_name_t>::type VertexNameMap;
typedef property_map<Graph, vertex_index_t>::type VertexIndexMap;
typedef property_map<Graph, edge_name_t>::type EdgeNameMap;

typedef boost::graph_traits<Graph>::vertex_descriptor Vertex;
typedef boost::graph_traits<Graph>::edge_descriptor Edge;
typedef graph_traits<Graph>::vertex_iterator vertex_iter;


template <typename GraphFirst,
          typename GraphSecond,
          typename BCName,
          typename FuncName,
          typename KBBLINFO,
          typename FBBLINFO,
          typename KGlobalCTX,
          typename FGlobalCTX,
          typename LocalMessage,
          typename Mutex>
          
struct User_callback {

    typedef typename graph_traits<Graph>::vertices_size_type VertexSizeFirst;

    User_callback(const GraphFirst& graph1, //cfgK
                 const GraphSecond& graph2, //cfgF
                 const BCName& bcname,
                 const FuncName& funcname,
                 const KBBLINFO& KbasicBlockInfo, 
                 const FBBLINFO& FbasicBlockInfo,
                 const KGlobalCTX& KGlobalCtx,
                 const FGlobalCTX& FGlobalCtx,
                 const LocalMessage& local_msg) :
    m_graph1(graph1), m_graph2(graph2), m_bcname(bcname), m_funcname(funcname), m_KbasicBlockInfo(KbasicBlockInfo), m_FbasicBlockInfo(FbasicBlockInfo), m_KGlobalCtx(KGlobalCtx), m_FGlobalCtx(FGlobalCtx),m_local_msg(local_msg){}

    template <typename CorrespondenceMapFirstToSecond,
                typename CorrespondenceMapSecondToFirst>
    bool operator()(CorrespondenceMapFirstToSecond correspondence_map_1_to_2,
                    CorrespondenceMapSecondToFirst correspondence_map_2_to_1,
                    VertexSizeFirst subgraph_size) {

        // Fill membership map for first graph
        typedef typename property_map<Graph, vertex_index_t>::type VertexIndexMap;
        typedef shared_array_property_map<bool, VertexIndexMap> MembershipMap;
        
        MembershipMap membership_map1(num_vertices(m_graph1),
                                    get(vertex_index, m_graph1));

        fill_membership_map<Graph>(m_graph1, correspondence_map_1_to_2, membership_map1);

        // Generate filtered graphs using membership map
        typedef typename membership_filtered_graph_traits<Graph, MembershipMap>::graph_type
        MembershipFilteredGraph;

        MembershipFilteredGraph subgraph1 =
        make_membership_filtered_graph(m_graph1, membership_map1);
        string filename =getFileExt(m_bcname,"/");
        

        // Print out correspondences between vertices
        int EdgeNoofSub_graph =0;
        int VetexNoofSub_graph =0;
        int EdgeNoofm_graph2 =0;
        int VetexNoofm_graph2 =0;
        int EdgeNoofm_graph1 =0;
        int VetexNoofm_graph1 =0;
        // Dump MCS
        //string mcs_contend = "MCS:\"";
        std::vector<int> kcommon_node;
        std::queue<int> kcommon_subgraph;
        std::vector<int> fcommon_node;
        std::queue<int> fcommon_subgraph;
        std::vector<int> remain_graph1;
        std::vector<int> remain_graph2;
        std::map<int,int> MCSMap;
        BGL_FORALL_VERTICES_T(vertex1, m_graph1, GraphFirst) {
        // Skip unmapped vertices
            if (get(correspondence_map_1_to_2, vertex1) != graph_traits<GraphSecond>::null_vertex()) {
                int v2 = get(correspondence_map_1_to_2, vertex1);
                #ifdef Debug_SO
                std::cout << vertex1 << " <-> " << get(correspondence_map_1_to_2, vertex1) << std::endl;
                #endif
                kcommon_subgraph.push(vertex1);
                fcommon_subgraph.push(v2);
                kcommon_node.push_back(vertex1);
                fcommon_node.push_back(v2);
                MCSMap.insert(make_pair(vertex1,v2));
            }
        }
        string TimeRecord_mcgregor =  (string)DATA_DIR+ "../result/TimeRecord/new-TimeRecord/Log-mcgregor-"+ RecordDate + "-" +kernel_eddition+".txt";
        string Log_mcgregor =  "\n{\"MKName\":\""  + m_bcname + "\",\n\"FName\":\"" + m_funcname + "\",\n\"MSCSize\":\"" + getIntContent(MCSMap.size())  + "\",\n" +  DumpMCS(&MCSMap) +"\n}" ; 
        
        return (true);
    }

    private:
    
    const GraphFirst& m_graph1;
    const GraphSecond& m_graph2;
    const KBBLINFO& m_KbasicBlockInfo;
    const FBBLINFO& m_FbasicBlockInfo;
    const BCName& m_bcname;
    const FuncName& m_funcname;
    const KGlobalCTX& m_KGlobalCtx;
    const FGlobalCTX& m_FGlobalCtx;
    const LocalMessage& m_local_msg;
    VertexSizeFirst m_max_subgraph_size;
};

void graphMatch();
VertexNameMap  GenerateGraph(Graph graph);
void AddNode(VertexNameMap vname_map_simple, Graph graph, unsigned int Hash);
void AddEdge(unsigned int Hash1, unsigned int Hash2, Graph graph);

#endif
