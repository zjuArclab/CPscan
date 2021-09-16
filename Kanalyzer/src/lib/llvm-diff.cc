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
#include <regex>
#include <string>
#include <fstream>
#include <sstream>
#include <iostream>
#include <ctime>
#include <future>
#include <thread>
#include <chrono>
#include <dirent.h>
#include <string.h>
#include <stdlib.h>
#include <vector>
#include <map> 
#include <functional>
#include <regex>
#include <typeinfo>
#include <bits/stdc++.h> 
#include <memory>
#include <sstream>
#include <sys/resource.h>
#include "Analyzer.h"
#include "CallGraph.h"
#include "Config.h"
#include "Common.h"
#include "CFG-diff.h"
#include "SensitiveCheck.h"
#include <pthread.h>
#include <sys/signal.h>  
#include <sys/types.h>
#include <sys/stat.h>
#include <omp.h>
using namespace llvm;
using namespace std;
int NoofdeletedSO = 0;
// Global variable
vector<string> BCList; 
int NotIdenticalFunc = 0;
int No_SC = 0;
int NO_UI = 0;
int NO_UL = 0;
int NO_UP = 0;
int NO_RR = 0;
int potencial_delete_security_operation = 0;
clock_t CompareTime;


void Print_Sensitive_Info_of_Functions(vector<Sensitive_Info_of_Functions*> v){
    vector<Sensitive_Info_of_Functions*>::iterator iter;
    int i=0;
    for(iter = v.begin();iter!=v.end();iter++){
        Sensitive_Info_of_Functions* sfk = *iter;
        if(sfk->size!=0){
            OP<<"Function name is : "<<sfk->F->getName()<<"\n";
            for(int i=0;i<sfk->size;i++){
                OP<<"\nbbl_NO:  "<<sfk->sen_list[i].bbl_NO<<", "<<" security type: "<<sfk->sen_list[i].type<<", "
                <<"Instruction"<<*(sfk->sen_list[i].inst);
            } 
        }
    }
}

char* Convertstr2char(string FirmwareAddr){
	char *FirmwareAddress = new char[FirmwareAddr.length() + 1];
  	strcpy(FirmwareAddress, FirmwareAddr.c_str());
	return FirmwareAddress;
}

// Get splitted string by  the delimiter
string splitstring(const string& s, const string& delimiter) {
   size_t i = s.rfind(delimiter, s.length());
   if (i != string::npos) {
      return(s.substr(0, i));
   }
   return("");
}

string removenumbers(const string& str) {
    string s = str;
    char dot = '.';
    while(isdigit(*(s.end()-1)) || *(s.end()-1)== dot ){
        s = s.substr(0, s.length()- 1);
    }
    return  s; 
}


void stringreplace(std::string& str, const std::string& from, const std::string& to) {
    size_t start_pos = 0;
    while((start_pos = str.find(from, start_pos)) != std::string::npos) {
        str.replace(start_pos, from.length(), to);
        start_pos += to.length(); // In case 'to' contains 'from', like replacing 'x' with 'yx'
    }
}

string filterIR(const string& s, const string& delimiter) {
   size_t i = s.rfind(delimiter, s.length());
   if (i != string::npos) {
      return(s.substr(0, i));
   }
   return("");
}

struct replaceresult replace_all(string& str, string& old_value, string& new_value)   {  
    replaceresult rr;
    int replace = 0; 
    for(string::size_type  pos(0);   pos!=string::npos;   pos+=new_value.length())   {   
        if((pos=str.find(old_value,pos))!=string::npos){
            char c = str[pos+old_value.length()];
            if(c >='0' && c<='9')
              continue;
            else{
             str.replace(pos,old_value.length(),new_value);
             replace = 1;
            }  
        } 
        else  break;   
    }  
    rr = {str, replace};
    return   rr;   
}  
string normalizeBB(string str) {
    smatch result;
    replaceresult rr;
    string regex_str("\\%\\d+");
    string str_result=str;
    regex pattern1(regex_str,regex::icase);
    string::const_iterator iter = str.begin();
    string::const_iterator iterEnd= str.end();
    string temp; // which is used to store variables e.g. %1, %2, %3, and so on.
    int count = 0;
    while (std::regex_search(iter,iterEnd,result,pattern1)){
        string variable("VA");
        string normalized = variable.append(to_string(count));
        temp=result[0];
        rr = replace_all(str_result, temp, normalized);
        iter = result[0].second; 
        str_result = rr.str;
        int replace = rr.replace;
        if(replace)
            count++;
        
    }
    return(str_result);
}

string filterIR_dbg(string str, string filter) {
    smatch result;
    replaceresult rr;
    string str_result=str;
    regex pattern2(filter,regex::icase);
    string::const_iterator iter = str.begin();
    string::const_iterator iterEnd= str.end();
    string temp; // which is used to store variables e.g. %1, %2, %3, and so on.
    int count = 0;
    while (std::regex_search(iter,iterEnd,result,pattern2))
    {
        string variable(" ");
        temp=result[0];
        rr = replace_all(str_result, temp, variable);
        iter = result[0].second; 
        str_result = rr.str;
        int replace = rr.replace;
        if(replace)
            count++;
    }
    return(str_result);
}

string filterIR_dbg_r(string str, string filter,string split) {
    smatch result;
    replaceresult rr;
    string str_result=str;
    regex pattern2(filter,regex::icase);
    string::const_iterator iter = str.begin();
    string::const_iterator iterEnd= str.end();
    string temp; 
    int count = 0;
    while (std::regex_search(iter,iterEnd,result,pattern2))
    {
        
        temp=result[0];
        string variable = splitstring(temp,split);
        rr = replace_all(str_result, temp, variable);
        iter = result[0].second; 
        str_result = rr.str;
        int replace = rr.replace;
        if(replace)
            count++;
    }
    return(str_result);
}

string filterIR_dbg_r(string str, string filter) {
    smatch result;
    replaceresult rr;
    string str_result=str;
    regex pattern2(filter,regex::icase);
    string::const_iterator iter = str.begin();
    string::const_iterator iterEnd= str.end();
    string temp; 
    int count = 0;
    while (std::regex_search(iter,iterEnd,result,pattern2))
    {
        
        temp=result[0];
        string variable = removenumbers(temp);
        rr = replace_all(str_result, temp, variable);
        iter = result[0].second; 
        str_result = rr.str;
        int replace = rr.replace;
        if(replace)
            count++;
    }
    return(str_result);
}

string Filter(string BBContend){
    stringreplace(BBContend,"tail call ","call ");
    BBContend = filterIR_dbg(BBContend,"tail call void \\@llvm\\.prefetch.*\\)"); 
    BBContend = filterIR_dbg(BBContend,"asm sideeffect.*\\!srcloc \\!\\d+"); 
    BBContend = filterIR_dbg(BBContend,"\\!dbg \\!\\d+"); 
    BBContend = filterIR_dbg(BBContend,"\\!tbaa \\!\\d+"); 
    BBContend = filterIR_dbg(BBContend,"metadata \\!\\d+"); 
    BBContend = filterIR_dbg(BBContend,"\\!prof \\!\\d+"); 
    BBContend = filterIR_dbg(BBContend,"align \\d+"); 
    BBContend = filterIR_dbg(BBContend,"\\!misexpect \\!\\d+"); 
    BBContend = filterIR_dbg(BBContend,"\\!llvm.loop \\!\\d+"); 
    BBContend = filterIR_dbg(BBContend,"signext \\d+"); 
    BBContend = filterIR_dbg(BBContend,"\\!srcloc \\!\\d+"); 
    BBContend = filterIR_dbg(BBContend," \\#\\d+"); 
    BBContend = filterIR_dbg_r(BBContend,"(\\%)?struct\\.(_|[a-zA-Z]|[0-9])*\\.\\d+", "."); 
    BBContend = filterIR_dbg_r(BBContend,"\\%(_|[a-zA-Z]|\\.)+\\d+");
    BBContend = filterIR_dbg_r(BBContend,"\\@(_|[a-zA-Z]|\\.)*\\d+");
    BBContend = filterIR_dbg_r(BBContend,"getelementptr inbound((?!i32|i64).)*, (i32|i64) 0, (i32|i64) \\d+", ","); 
    BBContend = normalizeBB(BBContend);
    return BBContend;
}

string Filter_V1(string BBContend){
    stringreplace(BBContend,"tail call ","call ");
    BBContend = filterIR_dbg(BBContend,"tail call void \\@llvm\\.prefetch.*\\)"); 
    BBContend = filterIR_dbg(BBContend,"asm sideeffect.*\\!srcloc \\!\\d+"); 
    BBContend = filterIR_dbg(BBContend,"\\!dbg \\!\\d+"); 
    BBContend = filterIR_dbg(BBContend,"\\!tbaa \\!\\d+"); 
    BBContend = filterIR_dbg(BBContend,"metadata \\!\\d+"); 
    BBContend = filterIR_dbg(BBContend,"\\!prof \\!\\d+"); 
    BBContend = filterIR_dbg(BBContend,"align \\d+"); 
    BBContend = filterIR_dbg(BBContend,"\\!misexpect \\!\\d+"); 
    BBContend = filterIR_dbg(BBContend,"\\!llvm.loop \\!\\d+"); 
    BBContend = filterIR_dbg(BBContend,"signext \\d+"); 
    BBContend = filterIR_dbg(BBContend,"\\!srcloc \\!\\d+"); 
    BBContend = filterIR_dbg(BBContend," \\#\\d+"); 
    BBContend = filterIR_dbg_r(BBContend,"(\\%)?struct\\.(_|[a-zA-Z]|[0-9])*\\.\\d+", "."); 
    BBContend = filterIR_dbg_r(BBContend,"\\%(_|[a-zA-Z]|\\.)+\\d+");
    BBContend = filterIR_dbg_r(BBContend,"\\@(_|[a-zA-Z]|\\.)*\\d+");
    BBContend = normalizeBB(BBContend);
    return BBContend;
}

bbl_info InitBBL(){
    bbl_info b =new bbl; 
    b->parentnode=new parent; 
    b->parentnode->Next=NULL;
    b->childrennode= new child;
    b->childrennode->Next=NULL;
    b->silibingnode = new silbling;
    b->silibingnode->Next=NULL;
    return b;
}
void AddChild(bbl_info b, int childNo){
    if(b==NULL)
        OP<<"\nbbl does not exist.";
    else{
        ChildrenNode newchild = new child;
        newchild->Data = childNo;
        newchild->Next=NULL;
        ChildrenNode c = b->childrennode; 
        while(c->Next){
            c=c->Next;
        }
        c->Next=newchild;
    }
}

vector<int>  Obtainchildren(ChildrenNode childList){
    vector<int> children;
    if(childList==NULL)
        OP<< "Empty List.\n";
    else{
        ChildrenNode c = childList->Next; 
        while(c){
            children.push_back(c->Data);
            c=c->Next;
        }
    }
    return  children;
}

void InsertParent(ParentNode parentList, int parentID){
    if(parentList==NULL)
        OP<<"Empty ParentList.\n";
    else{
        ParentNode p = parentList;
        while(p->Next && (p->Next->Data != parentID)){
            p=p->Next;
        }
        if(p->Next==NULL){
            ParentNode newparent = new parent;
            newparent->Data = parentID;
            newparent->Next = NULL;
            p->Next = newparent;
        }
    }
}

void IndsertSibling(SilbingNode  silbingList, int it, vector<int> children){
    if(silbingList==NULL)
        OP<<"Empty silbingList.\n";
    else{
        SilbingNode s;
        for (auto brother : children){
            if(brother != it){
                s = silbingList;
                while(s->Next && (s->Next->Data != brother)){
                    s=s->Next;
                }
                if(s->Next == NULL){
                    SilbingNode newbrother = new silbling;
                    newbrother->Data = brother;
                    newbrother-> Next = NULL;
                    s->Next = newbrother;
                }
            }
        }
    }
}

// std::map<int,bbl_info>  Mapbbl
void FindParent_sibling(Mapbbl basicBlockInfo){
    Mapbbl::iterator iter;
    for (iter=basicBlockInfo.begin(); iter!=basicBlockInfo.end(); iter++)
    {
        int basicblockID = iter->first ;
        OP<<basicblockID<<" ";
        bbl_info b = iter->second;
        vector<int> children;
        ChildrenNode childList =  b->childrennode;
        children = Obtainchildren(childList);
        for (auto it : children){
            if(it){
                bbl_info  childInfo = basicBlockInfo[it];
                SilbingNode  silbingList = childInfo->silibingnode;
                ParentNode parentList = childInfo->parentnode;
                int parentID = basicblockID;
                InsertParent(parentList, parentID);
                IndsertSibling(silbingList, it, children);
            }   
        }
    }
}


// print the parent, chidren, and sibling nodes of a basic block.
void Print(Mapbbl basicBlockInfo){
    Mapbbl::iterator iter;
    for (iter=basicBlockInfo.begin(); iter!=basicBlockInfo.end(); iter++){
        int basicblockID = iter->first ;
        bbl_info b = iter->second;
        OP<<"basicblockID is "<< basicblockID <<" \n";
        ChildrenNode childList =  b->childrennode;
        if(childList==NULL)
        OP<< "Empty ChildList.\n";
        else{
            ChildrenNode c = childList->Next; 
            while(c){
                OP<< " child is  "<<c->Data<<" ";
                c=c->Next;
            }
        }
        OP<<"\n";
        SilbingNode  silbingList = b->silibingnode;
        if(silbingList==NULL)
        OP<< "Empty silbingList.\n";
        else{
            SilbingNode s = silbingList->Next; 
            while(s){
                OP<< " brother is  "<<s->Data<<" ";
                s=s->Next;
            }
        }
        OP<<"\n";
        ParentNode parentList = b->parentnode;
        if(parentList==NULL)
        OP<< "Empty parentList.\n";
        else{
            ParentNode p = parentList->Next; 
            while(p){
                OP<< " parent is  "<<p->Data<<" ";
                p=p->Next;
            }
        }
        OP<<"\n";
    }
}


string Statics(ModuleList &modules)
{
    int Total = 0;
    int Max = 0;
    int Min =10;
    int TotalBBL =0;
    int zero = 0; // 0-10
    int small = 0; // 0-10
    int media = 0; // 10-20
    int large = 0; // 20 -30
    int larger = 0; //30 -50
    int verylarge = 0 ; // 50 - 100
    int superlarge = 0 ; // >100
    ModuleList::iterator i, e;
    for (i = modules.begin(), e = modules.end(); i != e; ++i) {
        Module *Module = i->first;
        int FuncNo = Module->size();
        if(FuncNo > Max)
            Max = FuncNo;
        if(FuncNo < Min)
            Min = FuncNo;
        Total = Total + FuncNo;
        for (Module::iterator f = Module->begin(), fe = Module->end(); 
                f != fe; ++f) {
                Function *F = &*f;
                // the number of basic block within a function;
                int bbl = F->size();
                TotalBBL = TotalBBL + bbl;
                if (bbl ==0)
                    zero++;
                else if( bbl>0 and bbl <=10)
                    small++;
                else if( bbl>10 and bbl <=20)
                    media++;
                else if( bbl>20 and bbl <=30)
                    large++;
                else if( bbl>30 and bbl <=50)
                    larger++;
                else if( bbl>50 and bbl <=100)
                    verylarge++; 
                else if( bbl>100)
                    superlarge++;                         
        }
          
    }
    string content = "No. of BC: " + getIntContent(modules.size()) + "; Total Func: " + getIntContent(Total)  +  "; zero :"  +  getIntContent(zero) + "; small :"  + 
     getIntContent(small) + "; media :"  +  getIntContent(media) + "; large :"  +  getIntContent(large) + "; larger :"  +  getIntContent(larger)
     + "; verylarge :"  +  getIntContent(verylarge) + "; superlarge :"  +  getIntContent(superlarge) + "\n";
    
    //dump_buffer1(string(kernel_eddition) + ": "+content, "/CPscan/Kanalyzer/data/result/cpscan-delBBInfo/Total-Func.txt");
    return content;
    
}

bool IsSecurityCheck(Function *F, Instruction *I) {
    if (F->empty())
            return false;
    if (F->size() > MAX_BLOCKS_SUPPORT)
        return false;
    Instruction *Inst = &*I;
	Value *Cond = NULL;
    if (isa<BranchInst>(Inst) || isa<SwitchInst>(Inst)) {
		BranchInst *BI = dyn_cast<BranchInst>(Inst);
		SwitchInst *SI = NULL;
		if (BI) {
			if (BI->getNumSuccessors() < 2)
				return false;
		} 
		else {
			SI = dyn_cast<SwitchInst>(Inst);
			if (SI->getNumSuccessors() < 2)
				return false;
		}
        if (BI)
			Cond = BI->getCondition();
		else
			Cond = SI->getCondition();
    }
    else if (SelectInst *SI = dyn_cast<SelectInst>(Inst)) {
		Cond = SI->getCondition();
	}
    if (Cond) {
        return true;
    }
    return false;
}




void CheckCodeReImp(Function *K, Function *F, GlobalContext *FGlobalCtx){
    if(F->size()==1 && K->size() !=1){
        OP<<"\nDo not need check.";
	for (Function::iterator FB_iter = F->begin(); FB_iter != F->end(); ++FB_iter){
            BasicBlock *FcurBB = &*FB_iter;
       	    for (BasicBlock::iterator iter = FcurBB->begin(); iter != FcurBB->end(); iter++) {
                Instruction *Inst = &*iter;
                if(isa<CallInst>(Inst)){
		    CallInst *CI = dyn_cast<CallInst>(Inst);
                    if(CI){
                        StringRef FuncName = CI->getParent()->getParent()->getName();
                        F = FGlobalCtx->AllFuncs[FuncName];
                    }

                }
            }
        }
    }

}

bool Identical(Function *K, Function *F){
    string KContend("");
    string FContend("");
    std::hash<std::string> Fhasher, Khasher;
    for (Function::iterator KB_iter = K->begin(); KB_iter != K->end(); ++KB_iter){
        BasicBlock *KcurBB = &*KB_iter;
        string KcurBBContend("");
        raw_string_ostream krso(KcurBBContend);
        for (BasicBlock::iterator KI_iter = KcurBB->begin(); KI_iter != KcurBB->end(); ++KI_iter) {
            Instruction *Inst = &*KI_iter;
            if(!Inst)
                continue;
            krso<<*Inst; 
        }
        KcurBBContend = krso.str();
        KcurBBContend = Filter(KcurBBContend);
        KContend = KContend + KcurBBContend;

    }
    for (Function::iterator FB_iter = F->begin(); FB_iter != F->end(); ++FB_iter){
        BasicBlock *FcurBB = &*FB_iter;
        string FcurBBContend("");
        raw_string_ostream frso(FcurBBContend);
        for (BasicBlock::iterator FI_iter = FcurBB->begin(); FI_iter != FcurBB->end(); ++FI_iter) {
            Instruction *Inst = &*FI_iter;
            if(!Inst)
                continue;
            frso<<*Inst; 
        } 
        FcurBBContend = frso.str();
        FcurBBContend = Filter(FcurBBContend);
        FContend = FContend + FcurBBContend;  
    }
    auto KBBhashed = Khasher(KContend);
    auto FBBhashed = Fhasher(FContend);
    
    if(KBBhashed==FBBhashed){
        return true;
    }
    else{
        return false;
    }
}


bool PatchAnalysis(string MKName, string FunName, std::map<llvm::Instruction*, int> *deletedSSlistr){
    double res = 0.0;
    
    string GitDir = (string)DATA_DIR + "../result/linux";
    string ShellDir = (string)SRC_DIR+ "scrips/find-so-remove.sh";
    
    string QueryTime = "\"2009-08-08 00:00:00\"";
    std::map<std::string, std::string> CommitTime;
    CommitTime.insert(make_pair("2.6.20","\"2006-12-14 00:00:00\""));
    CommitTime.insert(make_pair("2.6.36.4","\"2010-08-02 00:00:00\""));
    CommitTime.insert(make_pair("3.5.7","\"2012-06-03 00:00:00\""));
    CommitTime.insert(make_pair("3.10","\"2013-5-12 00:00:00\""));
    CommitTime.insert(make_pair("3.18","\"2014-10-20 00:00:00\""));
    CommitTime.insert(make_pair("4.1.0","\"2015-04-27 00:00:00\""));
    CommitTime.insert(make_pair("4.14.151","\"2015-04-27 00:00:00\""));
    CommitTime.insert(make_pair("4.4.198","\"2015-11-16 00:00:00\""));
    CommitTime.insert(make_pair("4.9.37","\"2016-10-16 00:00:00\""));
    CommitTime.insert(make_pair("4.9.37.hisi","\"2016-10-16 00:00:00\""));
    CommitTime.insert(make_pair("4.9.51","\"2016-10-16 00:00:00\""));
    CommitTime.insert(make_pair("4.9.198","\"2016-10-16 00:00:00\""));
    size_t pos;
    if(MKName.find(".k")!=string::npos) 
    	pos = MKName.rfind(".k", MKName.length());
    else
    	pos = MKName.rfind(".f", MKName.length());
    string eddition = MKName.substr(0, pos);
    string filename = MKName.substr(pos+3, MKName.length());
    filename.replace(filename.find(".bc"),3,".c");
    pos = eddition.rfind("stable-", eddition.length());
    eddition = eddition.substr(pos+7, eddition.length());
    string kernel_dir = (string)SourceCode_DIR + "stable-"+eddition+".k"; 
    if(CommitTime.find(eddition)!=CommitTime.end())
	QueryTime = CommitTime[eddition];
    string FPRecord =  (string)DATA_DIR+ "../result/"+RecordDate+"/FPRecord-"+kernel_eddition+".txt";
    int count = 0;
    for(std::map<llvm::Instruction*, int>::iterator iter = deletedSSlistr->begin(); iter != deletedSSlistr->end(); iter++){
        int type = iter->second;
        Instruction *Inst = iter->first;
        StringRef funcName = Inst->getParent()->getParent()->getName();
        std::string DeletedSS = "";
        llvm::raw_string_ostream rso(DeletedSS);
        DILocation *Loc = getSourceLocation(Inst);
        if (!Loc)
            continue;
        int lineno = Loc->getLine();
        rso<<*Inst; 
        DeletedSS= rso.str();
        string command = "bash "+ ShellDir + " " + GitDir + " " + QueryTime + " " + filename+ " " + "\""+FunName+ "\""  + " \"" + kernel_dir  +"\" " + getIntContent(lineno) +
		" " + RecordDate + " " +kernel_eddition;
        int result = std::system(Convertstr2char(command));
        if(result == 256){
            count++;
            dump_buffer1(MKName + " +" + getIntContent(lineno) + ": "+funcName.str() + ": Patched\n", FPRecord);
        }
        else if(result == 512){
            dump_buffer1(MKName + " +" + getIntContent(lineno) + ": "+funcName.str() + ": PatchAnalyze-Failed\n", FPRecord);
        }
        else if(result == 0){
            dump_buffer1(MKName + " +" + getIntContent(lineno) + ": "+funcName.str() + ": Unpatched\n", FPRecord);
        }
    }
    if(deletedSSlistr->size() >0)
        res = (count)/(deletedSSlistr->size());
    if(res>= 0.5)
        return true;
    else
        return false;    
}

void GetDeletedLines(std::map<int,int> MCSMap, std::vector<int>DeletedBBlist, Mapbbl KbasicBlockInfo,  Mapbbl FbasicBlockInfo, string analysisfile){   
    string dumpfile = "/CPscan/Kanalyzer/data/result/cpscan-delBBInfo/deleBBInfo" + (string)(kernel_eddition) + ".csv";
    if(DeletedBBlist.size() > 0){
        for(std::vector<int>::iterator iter= DeletedBBlist.begin();
          iter != DeletedBBlist.end(); iter++ ){
            int DeletedBB = *iter;
            if(IsInMCS(&MCSMap, DeletedBB))
              continue;
            bbl_info Deletedbbl =  ObtainBBInfo(DeletedBB, &KbasicBlockInfo);
            DumpDeletedBBInfo(analysisfile, Deletedbbl, dumpfile);   
        }
    }
}

void AnalyzelargeCFG_OMP(Function *F, Function *K, string MKName, GlobalContext *KGlobalCtx, GlobalContext *FGlobalCtx)
{ 
   
    std::map<int, Instruction*> KFIRMAP, FFIRMAP;
    char*  local_msg = (char*)calloc(BUFFERSIZE , sizeof(unsigned char));  
    if(local_msg==NULL)
        OP<<"ERROR calloc.\n";
    Sensitive_Info_of_Functions *sfk, *sff;  
    sfk=new(Sensitive_Info_of_Functions);
    sff=new(Sensitive_Info_of_Functions);
    if(!sfk || !sff)
        OP<<"Malloc Sensitive_Info_of_Functions Error!\n";
    sfk->F = K;
    sff->F = F;
    sfk->size = 0;
    sff->size = 0;
    string FuncFName = F->getName();
    
    if(K==NULL || F==NULL)
        OP<<"Empty function Error!\n";
    Graph cfgK(K->size()), cfgF(F->size()), MSC;
    Mapbbl KbasicBlockInfo; 
    Mapbbl FbasicBlockInfo;
    std::error_code error;
    std::map<BasicBlock*, int> basicBlockMap;
    int FbbCount = 0, KbbCount = 0;  
    // We define FContend to record IR within a function and get the Hash of FContend to determine if functions are identical.
    string FContend = "", KContend = "";
    std::hash<std::string> Fhasher, Khasher;

    // #define scheck 0  the type of security check is 0
    // #define uintial 1  the type of uninitialized  is 1
    // #define ulock 2  the type of lock and unlock is 2
    // #define pfunc 3  the type of pair of function is 3
 
    int sensitive_inst_in_funck = 0;
    int sensitive_inst_in_funck_type0 = 0;
    int sensitive_inst_in_funck_type1 = 0;
    int sensitive_inst_in_funck_type2 = 0;
    int sensitive_inst_in_funck_type3 = 0;
    int sensitive_inst_in_funck_type4 = 0;
    // Obtain CFG of function K, tranverse basic blocks of K.
    for (Function::iterator KB_iter = K->begin(); KB_iter != K->end(); ++KB_iter){
        // Obtain the current basic block.
        BasicBlock *KcurBB = &*KB_iter;
        // bbl_info stores the information of basic block, including parent sibling and children list, sensitive operations in the basic block.
        bbl_info  Kcur_bbl_info= InitBBL();
        Kcur_bbl_info->bbl = KcurBB;
        // We define BBContend to record IR within a basic block and get the Hash of BBContend to determine if BB is identical.  
        std::string name = KcurBB->getName().str();
        int KfromCountNum;
        int KtoCountNum;
        if (basicBlockMap.find(KcurBB) != basicBlockMap.end()){
            KfromCountNum = basicBlockMap[KcurBB];
        }
        else{
            KfromCountNum = KbbCount;
            basicBlockMap[KcurBB] = KbbCount++;
        }
        #ifdef TEST_GM
        OP << "\nKcurBB\t" << KfromCountNum << " [shape=record, label=\"{ BB" << KfromCountNum << ":\\l\\l";
        #endif
        
        Kcur_bbl_info->BBLID = KfromCountNum;

        Instruction *KFirstInst = FindFirstValidateInst(KcurBB);
        KFIRMAP.insert(make_pair(KfromCountNum, KFirstInst));

        std::string KcurBBContend = "";
        llvm::raw_string_ostream krso(KcurBBContend);
        
        std:string split = ";";
        bool sensitive = false;
        string  FnName;
        
        for (BasicBlock::iterator KI_iter = KcurBB->begin(); KI_iter != KcurBB->end(); ++KI_iter) {
            Instruction *Inst = &*KI_iter;
            if(!Inst)
                continue;
            KI_iter->print(krso);  
            Kcur_bbl_info->Instructions.push_back(Inst);
            Function *K = KcurBB->getParent();
            //If Inst is a branchInst, SwitchInst, or SelectInst, we perform security check
            if(isa<BranchInst>(Inst) || isa<SwitchInst>(Inst) || isa<SelectInst>(Inst)) {
                //  IC is the ICmpInst in a condition.
                #ifdef TEST_GM
                    OP<<"\n"<<*Inst;
                    OP<<"Condition.\n";
                    printSourceCodeInfoInst(Inst);
                #endif
                Instruction *IC = NULL;
                SensitiveChecksPass KSCPass(KGlobalCtx, "SecurityCheck");
                // We determine that if an instruction is a security check 
                // If Inst is a security check or a condition inst that has a branch return void, we record it in the Sensitive_Info of a basic block
                if(KSCPass.IsSecurityCheck(K,Inst) || IsSecurityCheckStopExe(K,Inst)) {
                    sensitive_inst_in_funck_type0++;
                    (Kcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,scheck));
                    Value *Cond = NULL;
                    if(isa<BranchInst>(Inst)){
                        BranchInst *BIk = dyn_cast<BranchInst>(Inst);
                        Cond = BIk->getCondition();
                    }
                    else if(isa<SwitchInst>(Inst)){
                        SwitchInst *SIk = dyn_cast<SwitchInst>(Inst);
                        Cond = SIk->getCondition(); 
                    }
                    else{
                        SelectInst *SIk = dyn_cast<SelectInst>(Inst);
                        Cond = SIk->getCondition();
                    }
                    if(Cond) 
                        IC  = dyn_cast<ICmpInst>(Cond); 
                    // sfk records Sensitive_Info_of_Functions (no more than 200), including the ID of the basic block, the type of security operation, and the corresponding sensitive instruction.
                    sfk->sen_list[sfk->size].bbl_NO = KfromCountNum;
                    sfk->sen_list[sfk->size].type = scheck;
                    if(IC !=NULL)
                        sfk->sen_list[sfk->size++].inst = IC;
                    else
                        sfk->sen_list[sfk->size++].inst = Inst; 
                    #ifdef TEST_GM
                        OP<<"Sensitive KInstruction in condition branch:\t"<< *Inst<<"\n";
                    #endif  
              }
            }
            //If Inst is a CallInst, we check if the called function are the sensitive functions.
            else if(isa<CallInst>(Inst)){
                CallInst *CI = dyn_cast<CallInst>(Inst);
                FnName = getCalledFuncName(CI);
                //  If the called function is a lock/unlock function, we record it in the Sensitive_Info of a basic block.
                if(Is_element_in_stingvector((KGlobalCtx->LockFuncs), FnName)) {
                    (Kcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,ulock));
                    sensitive_inst_in_funck_type2++;
                    sfk->sen_list[sfk->size].bbl_NO = KfromCountNum;
                    sfk->sen_list[sfk->size].type = ulock;
                    sfk->sen_list[sfk->size++].inst = Inst;
                    #ifdef TEST_GM
                        OP<<"Sensitive lock function: "<< *Inst<<" The called function name is: "<<FnName<<"\n";
                    #endif       
                }
                // If the called function must be used in a pair, we record it in the Sensitive_Info of a basic block.
                else if(Is_element_in_stingvector((KGlobalCtx->PairFuncs), FnName)){
                    (Kcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,pfunc));
                    sensitive_inst_in_funck_type3++;
                    sfk->sen_list[sfk->size].bbl_NO = KfromCountNum;
                    sfk->sen_list[sfk->size].type = pfunc;
                    sfk->sen_list[sfk->size++].inst = Inst;   
                    #ifdef TEST_GM
                        OP<<"Sensitive pair function: "<< *Inst<<" The called function name is: "<<FnName<<"\n";
                    #endif     
                } 
                else if((KGlobalCtx->ResourceReleaseFuncs).count(FnName)){
                    (Kcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,resourcerelease));
                    sensitive_inst_in_funck_type4++;
                    sfk->sen_list[sfk->size].bbl_NO = KfromCountNum;
                    sfk->sen_list[sfk->size].type = pfunc;
                    sfk->sen_list[sfk->size++].inst = Inst;   
                    #ifdef TEST_GM
                        OP<<"Sensitive RR function: "<< *Inst<<" The called function name is: "<<FnName<<"\n";
                    #endif     
                } 
                // If the called function performs initialization (included in CopyFuncs，or contain key string "init"), we record it in the Sensitive_Info of a basic block. 
                else if((KGlobalCtx->InitFuncs).count(FnName)||(KGlobalCtx->CopyFuncs).count(FnName)|| FnName.find("init")!=string::npos  || FnName.find("INIT")!=string::npos){
                    (Kcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,uintial));
                    #ifdef TEST_GM
                        OP<<"Sensitive init function: "<< *Inst<<" The called function name is: "<<FnName<<"\n";
                    #endif
                    sensitive_inst_in_funck_type1++;
                    sfk->sen_list[sfk->size].bbl_NO = KfromCountNum;
                    sfk->sen_list[sfk->size].type = uintial;
                    sfk->sen_list[sfk->size++].inst = Inst;        
                } 
            }
        }

        Feature Kcur_bblfeature = bblFeature(Kcur_bbl_info->Instructions);
        Kcur_bbl_info->Inbbfeature = Kcur_bblfeature;
        #ifdef TEST_GM_NORM
            OP << "\nBB"<<KfromCountNum<<" Original KcurBBContend\t" << KcurBBContend;
        #endif
        KcurBBContend = Filter(KcurBBContend);
        std::hash<std::string> KCurhasher;
        auto KcurBBhashed = KCurhasher(KcurBBContend);
        Kcur_bbl_info->BBhash = KcurBBhashed;
        #ifdef TEST_GM_NORM 
            OP <<"\nNormalized KcurBBContend: \n" << KcurBBContend<<"\nKSuccBBhashed is:\t" << KcurBBhashed;
        #endif   
        KContend = KContend + KcurBBContend;
        int Ksucc_no = 0; // the number of successor
        int KCursucc_no = 0; // the i-th successor
        // Deal with the Successor of current basic block.
        for (succ_iterator PI = succ_begin(KcurBB), E = succ_end(KcurBB); PI != E; ++PI) 
            Ksucc_no = Ksucc_no +1;
        // Visit the succerors of a basic block
        for (succ_iterator PI = succ_begin(KcurBB), E = succ_end(KcurBB); PI != E; ++PI) {
            BasicBlock *KSuccBB = *PI;
            KCursucc_no = KCursucc_no +1;
            if (basicBlockMap.find(KSuccBB) != basicBlockMap.end()){
                KtoCountNum = basicBlockMap[KSuccBB];   
            }
            else{
                KtoCountNum = KbbCount;
                basicBlockMap[KSuccBB] = KbbCount++;
            }
            #ifdef TEST_GM
            OP << "\tBB" << KfromCountNum<< "-> BB"<< KtoCountNum << ";\n";
            #endif
            AddChild(Kcur_bbl_info, KtoCountNum);
        }
       KbasicBlockInfo[KfromCountNum] = Kcur_bbl_info;
       
    }
    // If there are no any sensitive operations in kernel function , we will not analyze the corresponding firmware function


    string KIRMAPPath = DeleteFileExt(MKName,".bc");
    //DumpIRMAP(&KFIRMAP, KIRMAPPath+"/"+FuncFName+".irmap");
    
    
    auto Khashed = Khasher(KContend); 
    #ifdef TEST_GM 
        OP << "\nKhashed:\t" << Khashed << "\n";
    #endif

     // Obtain CFG of function F
    int sensitive_inst_in_funcf = 0;
    int sensitive_inst_in_funcf_type0 = 0;
    int sensitive_inst_in_funcf_type1 = 0;
    int sensitive_inst_in_funcf_type2 = 0;
    int sensitive_inst_in_funcf_type3 = 0;
    int sensitive_inst_in_funcf_type4 = 0;
    
    for (Function::iterator FB_iter = F->begin(); FB_iter != F->end(); ++FB_iter){
        // Obtain the current basic block.
        BasicBlock* FcurBB = &*FB_iter;
        bbl_info Fcur_bbl_info= InitBBL();
        Fcur_bbl_info->bbl = FcurBB;
        // We define BBContend to record IR within a basic block and get the Hash of BBContend to determine if BB is identical.  
        int FfromCountNum;
        int FtoCountNum;
        if (basicBlockMap.find(FcurBB) != basicBlockMap.end()){
            FfromCountNum = basicBlockMap[FcurBB];
        }
        else{
            FfromCountNum = FbbCount;
            basicBlockMap[FcurBB] = FbbCount++;
        }
        #ifdef TEST_GM 
        OP << "\nFcurBB\tBB" << FfromCountNum << " [shape=record, label=\"{BB" << FfromCountNum << ":\\l\\l";
        #endif
        // Obtain the hash of curBB
        Fcur_bbl_info->BBLID = FfromCountNum;

        Instruction *FFirstInst = FindFirstValidateInst(FcurBB);
        FFIRMAP.insert(make_pair(FfromCountNum, FFirstInst));

        std::string FcurBBContend = "";
        llvm::raw_string_ostream frso(FcurBBContend);
       
        string FnName;
        
        for (BasicBlock::iterator FI_iter = FcurBB->begin(); FI_iter != FcurBB->end(); ++FI_iter){
            Instruction *Inst = &*FI_iter;
            if(!Inst)
                continue;
            FI_iter->print(frso);
            Function *F = FcurBB->getParent();
            Fcur_bbl_info->Instructions.push_back(Inst);
            if(isa<BranchInst>(Inst) || isa<SwitchInst>(Inst) || isa<SelectInst>(Inst)) {
                #ifdef TEST_GM
                OP<<"\n"<<*Inst;
                OP<<"Condition.\n";
                printSourceCodeInfoInst(Inst);
                #endif
                Instruction *IC = NULL;
                SensitiveChecksPass FSCPass(FGlobalCtx, "SecurityCheck");
                if(FSCPass.IsSecurityCheck(F,Inst) || IsSecurityCheckStopExe(F,Inst)) {
                    (Fcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,scheck));
                    sensitive_inst_in_funcf_type0++;
                    Value *Cond = NULL;
                    if(isa<BranchInst>(Inst)){
                        BranchInst *BIf = dyn_cast<BranchInst>(Inst);
                        Cond = BIf->getCondition();  
                    }
                    else if(isa<SwitchInst>(Inst)){
                        SwitchInst *SIf = dyn_cast<SwitchInst>(Inst);
                        Cond = SIf->getCondition(); 
                    }
                    else{
                        SelectInst *SIf = dyn_cast<SelectInst>(Inst);
                        Cond = SIf->getCondition();
                    }
                    if(Cond)
                        IC  = dyn_cast<ICmpInst>(Cond);    
                    sff->sen_list[sff->size].bbl_NO = FfromCountNum;
                    sff->sen_list[sff->size].type = scheck; 
                    if(IC != NULL)
                        sff->sen_list[sff->size++].inst = IC;
                    else
                        sff->sen_list[sff->size++].inst = Inst; 
                    #ifdef TEST_GM 
                    OP<<"Sensitive FInstruction in condition branch:\t"<< *Inst<<"\n";
                    #endif 
              }
            }
            else if(isa<CallInst>(Inst)){
                CallInst *CI = dyn_cast<CallInst>(Inst);
                FnName = getCalledFuncName(CI);
                if(Is_element_in_stingvector((FGlobalCtx->LockFuncs), FnName)) {
                    (Fcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,ulock));
                    sensitive_inst_in_funcf_type2++;
                    sff->sen_list[sff->size].bbl_NO = FfromCountNum;
                    sff->sen_list[sff->size].type = ulock;
                    sff->sen_list[sff->size++].inst = Inst;
                   
                }
                else if(Is_element_in_stingvector((FGlobalCtx->PairFuncs), FnName)){
                    (Fcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,pfunc));
                    sensitive_inst_in_funcf_type3++;
                    sff->sen_list[sff->size].bbl_NO = FfromCountNum;
                    sff->sen_list[sff->size].type = pfunc;
                    sff->sen_list[sff->size++].inst = Inst;
                     
                } 
                else if((FGlobalCtx->ResourceReleaseFuncs).count(FnName)){
                    (Fcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,resourcerelease));
                    sensitive_inst_in_funcf_type4++;
                    sff->sen_list[sff->size].bbl_NO = FfromCountNum;
                    sff->sen_list[sff->size].type = pfunc;
                    sff->sen_list[sff->size++].inst = Inst;   
                     
                } 
                else if((FGlobalCtx->InitFuncs).count(FnName)||(FGlobalCtx->CopyFuncs).count(FnName)|| FnName.find("init")!=string::npos|| FnName.find("INIT")!=string::npos){
                    (Fcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,uintial));
                    sensitive_inst_in_funcf_type1++;
                    sff->sen_list[sff->size].bbl_NO = FfromCountNum;
                    sff->sen_list[sff->size].type = uintial;
                    sff->sen_list[sff->size++].inst = Inst;  
                    
                } 
            }    
        }
        
        Feature Fcur_bblfeature = bblFeature(Fcur_bbl_info->Instructions);        
        Fcur_bbl_info->Inbbfeature = Fcur_bblfeature;
        
        FcurBBContend = Filter(FcurBBContend);
        std::hash<std::string> FCurhasher;
        auto FcurBBhashed = FCurhasher(FcurBBContend);
        Fcur_bbl_info->BBhash = FcurBBhashed;
       
        FContend = FContend + FcurBBContend;
        int Fsucc_no = 0;  // the number of successor
        int FCursucc_no = 0; // the i-th successor
        // Deal with the Successor of current basic block.
        for (BasicBlock *FSuccBB : successors(FcurBB))
            Fsucc_no = Fsucc_no +1;
        for (BasicBlock *FSuccBB : successors(FcurBB)){
            FCursucc_no = FCursucc_no +1; 
            if (basicBlockMap.find(FSuccBB) != basicBlockMap.end()){
                FtoCountNum = basicBlockMap[FSuccBB];   
            }
            else{
                FtoCountNum = FbbCount;
                basicBlockMap[FSuccBB] = FbbCount++;
            }
            
            AddChild(Fcur_bbl_info,FtoCountNum);
        }
        FbasicBlockInfo[FfromCountNum] = Fcur_bbl_info;  
    }

    string FIRMAPPath = DeleteFileExt(MKName,".bc");
    
    sensitive_inst_in_funck = sensitive_inst_in_funck_type1+sensitive_inst_in_funck_type2+sensitive_inst_in_funck_type3+sensitive_inst_in_funck_type0;
    sensitive_inst_in_funcf = sensitive_inst_in_funcf_type1+sensitive_inst_in_funcf_type2+sensitive_inst_in_funcf_type3+sensitive_inst_in_funcf_type0;
  
    if(sensitive_inst_in_funck_type1 > sensitive_inst_in_funcf_type1||
       sensitive_inst_in_funck_type2 > sensitive_inst_in_funcf_type2||
       sensitive_inst_in_funck_type3 > sensitive_inst_in_funcf_type3||
       sensitive_inst_in_funck_type0 > sensitive_inst_in_funcf_type0){
            potencial_delete_security_operation++;
                
       }
        
    auto Fhashed = Fhasher(FContend);  
   
    if(Fhashed != Khashed)
    {
        FindParent_sibling(KbasicBlockInfo);
        FindParent_sibling(FbasicBlockInfo);

        OP<<"\nHash is different.";
        #ifdef  RECORD
        string Tmp = "BCName:\t"+MKName+".\tFunction Name:\t"+FuncFName+" \n";
        //RecordLog(local_msg, Tmp,FuncFName, mutex);
        #endif
        OP<<"\nAnalyze sensitive operations.";
        
        std::vector<int> kcommon_node;
        std::queue<int> kcommon_subgraph;
        std::vector<int> fcommon_node;
        std::queue<int> fcommon_subgraph;
        std::vector<int> remain_graph1;
        std::vector<int> remain_graph2;    
        for(auto kbI : KbasicBlockInfo) { 
            remain_graph1.push_back(kbI.first);
        } 
         for(auto fbI : FbasicBlockInfo) { 
            remain_graph2.push_back(fbI.first);
        } 
        std::map<int,int> MCSMap;
        OP<<"Different function pair:\t"<<FuncFName<<"\n";
        NotIdenticalFunc++;
        OP<<"sensitive insts in a K funcs\n";
        std::pair<Sensitive_Info_of_Functions*, std::set<int>> ssk = ObtainsensitiveBBLset(&KbasicBlockInfo, kcommon_node);
        OP<<"sensitive insts in a F funcs\n";
        std::pair<Sensitive_Info_of_Functions*, std::set<int>> ssf = ObtainsensitiveBBLset(&FbasicBlockInfo, fcommon_node);
        Sensitive_Info_of_Functions *sk = ssk.first; 
        Sensitive_Info_of_Functions *sf = ssf.first; 
        // The set of basic blocks that contain sensitive operation and are not int the MSC 
        set<int> SScfgk = ssk.second ;
        set<int> SScfgf = ssf.second ;

        
        // the deleted sensitive operations in SScfgk
        std::vector<int>DeletedBBlist; 
        // DeletedSSlists stores the deleted instruction and the corresponding  basic block ID in firmware, if there is no matching BBL ID, we set it to be -1.
        std::map<llvm::Instruction*, int> DeletedSSlists; 
        

        string inputfile =  DeleteFileExt(MKName,".bc")+"/"+ FuncFName+".input"; 
        string processfilename = DeleteFileExt(MKName,".bc")+"/"+ FuncFName+".process"; 
        string processfilename_tmp = DeleteFileExt(MKName,".bc")+"/"+ FuncFName+".process_tmp"; 
        string outputfile = DeleteFileExt(MKName,".bc")+"/"+ FuncFName+".json"; 
        
        

        GenerateDeletedSoNew(SScfgk,&kcommon_subgraph,&kcommon_node,KbasicBlockInfo,&remain_graph1,
        SScfgf,&fcommon_subgraph,&fcommon_node, FbasicBlockInfo,&remain_graph2,
        &MCSMap, &DeletedBBlist, &DeletedSSlists, local_msg, processfilename);

        GetDeletedLines(MCSMap, DeletedBBlist, KbasicBlockInfo, FbasicBlockInfo, processfilename);
        
        PatchAnalysis(MKName, F->getName(), &DeletedSSlists);
        if(DeletedSSlists.size() != 0){
            
            std::tuple<int,int,int,int,int> typecount = TypeCount(DeletedSSlists);
            No_SC += get<0>(typecount);
            NO_UI += get<1>(typecount);
            NO_UL += get<2>(typecount);
            NO_UP += get<3>(typecount);
            NO_RR += get<4>(typecount);
            NoofdeletedSO += DeletedSSlists.size();
            AnalyzeDeleteSS(&DeletedSSlists, &MCSMap, &remain_graph2, &KbasicBlockInfo, &FbasicBlockInfo,  outputfile);
        }
        else
            OP <<"\033[34mlarge CFG, after analysis, BCName is:\t"<<MKName<<";\t"<<FuncFName<<"\tis OK. \033[0m\n";
    }
    
}

// record whether F and K are the same, the time, the size of MCS.
std::tuple<int, double, int, string> AnalyzelargeCFG_OMP_GM_cmp(Function *F, Function *K, string MKName, GlobalContext *KGlobalCtx, GlobalContext *FGlobalCtx)
{ 
    
    std::map<int, Instruction*> KFIRMAP, FFIRMAP;
    
    int sameGraph = 1;
    clock_t totalstartTime, totalendTime;

    char*  local_msg = (char*)calloc(BUFFERSIZE , sizeof(unsigned char));  
    if(local_msg==NULL)
        OP<<"ERROR calloc.\n";
    Sensitive_Info_of_Functions *sfk, *sff;  
    sfk=new(Sensitive_Info_of_Functions);
    sff=new(Sensitive_Info_of_Functions);
    if(!sfk || !sff)
        OP<<"Malloc Sensitive_Info_of_Functions Error!\n";
    sfk->F = K;
    sff->F = F;
    sfk->size = 0;
    sff->size = 0;
    string FuncFName = F->getName();
    OP<<"\n\033[34m BCName:\t"<<MKName<<".\tFunction Name:\t"<<FuncFName<<"\033[0m\n";
    
    if(K==NULL || F==NULL)
        OP<<"Empty function Error!\n";
    Graph cfgK(K->size()), cfgF(F->size()), MSC;
    Mapbbl KbasicBlockInfo; 
    Mapbbl FbasicBlockInfo;
    std::error_code error;
    std::map<BasicBlock*, int> basicBlockMap;
    int FbbCount = 0, KbbCount = 0;  
    // We define FContend to record IR within a function and get the Hash of FContend to determine if functions are identical.
    string FContend = "", KContend = "";
    std::hash<std::string> Fhasher, Khasher;

   
    int sensitive_inst_in_funck = 0;
    int sensitive_inst_in_funck_type0 = 0;
    int sensitive_inst_in_funck_type1 = 0;
    int sensitive_inst_in_funck_type2 = 0;
    int sensitive_inst_in_funck_type3 = 0;
    // Obtain CFG of function K, tranverse basic blocks of K.
    for (Function::iterator KB_iter = K->begin(); KB_iter != K->end(); ++KB_iter){
        // Obtain the current basic block.
        BasicBlock *KcurBB = &*KB_iter;
        // bbl_info stores the information of basic block, including parent sibling and children list, sensitive operations in the basic block.
        bbl_info  Kcur_bbl_info= InitBBL();
        Kcur_bbl_info->bbl = KcurBB;
        // We define BBContend to record IR within a basic block and get the Hash of BBContend to determine if BB is identical.  
        std::string name = KcurBB->getName().str();
        int KfromCountNum;
        int KtoCountNum;
        if (basicBlockMap.find(KcurBB) != basicBlockMap.end()){
            KfromCountNum = basicBlockMap[KcurBB];
        }
        else{
            KfromCountNum = KbbCount;
            basicBlockMap[KcurBB] = KbbCount++;
        }
        #ifdef TEST_GM
        OP << "\nKcurBB\t" << KfromCountNum << " [shape=record, label=\"{ BB" << KfromCountNum << ":\\l\\l";
        #endif
        // Obtain the hash of curBB
        Kcur_bbl_info->BBLID = KfromCountNum;

        Instruction *KFirstInst = FindFirstValidateInst(KcurBB);
        KFIRMAP.insert(make_pair(KfromCountNum, KFirstInst));

        std::string KcurBBContend = "";
        llvm::raw_string_ostream krso(KcurBBContend);
        
        std:string split = ";";
        bool sensitive = false;
        string  FnName;
        
        for (BasicBlock::iterator KI_iter = KcurBB->begin(); KI_iter != KcurBB->end(); ++KI_iter) {
            Instruction *Inst = &*KI_iter;
            if(!Inst)
                continue;
            KI_iter->print(krso);  
            Kcur_bbl_info->Instructions.push_back(Inst);
            Function *K = KcurBB->getParent();
            //If Inst is a branchInst, SwitchInst, or SelectInst, we perform security check
            if(isa<BranchInst>(Inst) || isa<SwitchInst>(Inst) || isa<SelectInst>(Inst)) {
                //  IC is the ICmpInst in a condition.
                #ifdef TEST_GM
                OP<<"\n"<<*Inst;
                OP<<"Condition.\n";
                printSourceCodeInfoInst(Inst);
                #endif
                Instruction *IC = NULL;
                SensitiveChecksPass KSCPass(KGlobalCtx, "SecurityCheck");
                // We determine that if an instruction is a security check 
                // If Inst is a security check or a condition inst that has a branch return void, we record it in the Sensitive_Info of a basic block
                if(KSCPass.IsSecurityCheck(K,Inst) || IsSecurityCheckStopExe(K,Inst)) {
                    sensitive_inst_in_funck_type0++;
                    (Kcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,scheck));
                    Value *Cond = NULL;
                    if(isa<BranchInst>(Inst)){
                        BranchInst *BIk = dyn_cast<BranchInst>(Inst);
                        Cond = BIk->getCondition();
                    }
                    else if(isa<SwitchInst>(Inst)){
                        SwitchInst *SIk = dyn_cast<SwitchInst>(Inst);
                        Cond = SIk->getCondition(); 
                    }
                    else{
                        SelectInst *SIk = dyn_cast<SelectInst>(Inst);
                        Cond = SIk->getCondition();
                    }
                    if(Cond) 
                        IC  = dyn_cast<ICmpInst>(Cond); 
                    // sfk records Sensitive_Info_of_Functions (no more than 200), including the ID of the basic block, the type of security operation, and the corresponding sensitive instruction.
                    sfk->sen_list[sfk->size].bbl_NO = KfromCountNum;
                    sfk->sen_list[sfk->size].type = scheck;
                    if(IC !=NULL)
                        sfk->sen_list[sfk->size++].inst = IC;
                    else
                        sfk->sen_list[sfk->size++].inst = Inst; 
                    #ifdef TEST_GM
                    OP<<"Sensitive KInstruction in condition branch:\t"<< *Inst<<"\n";
                    #endif  
              }
            }
            //If Inst is a CallInst, we check if the called function are the sensitive functions.
            else if(isa<CallInst>(Inst)){
                CallInst *CI = dyn_cast<CallInst>(Inst);
                FnName = getCalledFuncName(CI);
                //  If the called function is a lock/unlock function, we record it in the Sensitive_Info of a basic block.
                if(Is_element_in_stingvector((KGlobalCtx->LockFuncs), FnName)) {
                    (Kcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,ulock));
                    sensitive_inst_in_funck_type2++;
                    sfk->sen_list[sfk->size].bbl_NO = KfromCountNum;
                    sfk->sen_list[sfk->size].type = ulock;
                    sfk->sen_list[sfk->size++].inst = Inst;
                    #ifdef TEST_GM
                    OP<<"Sensitive lock function: "<< *Inst<<" The called function name is: "<<FnName<<"\n";
                    #endif       
                }
                // If the called function must be used in a pair, we record it in the Sensitive_Info of a basic block.
                else if(Is_element_in_stingvector((KGlobalCtx->PairFuncs), FnName)){
                    (Kcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,pfunc));
                    sensitive_inst_in_funck_type3++;
                    sfk->sen_list[sfk->size].bbl_NO = KfromCountNum;
                    sfk->sen_list[sfk->size].type = pfunc;
                    sfk->sen_list[sfk->size++].inst = Inst;   
                    #ifdef TEST_GM
                    OP<<"Sensitive pair function: "<< *Inst<<" The called function name is: "<<FnName<<"\n";
                    #endif     
                } 
                // If the called function performs initialization (included in CopyFuncs，or contain key string "init"), we record it in the Sensitive_Info of a basic block. 
                else if((KGlobalCtx->InitFuncs).count(FnName)||(KGlobalCtx->CopyFuncs).count(FnName)|| FnName.find("init")!=string::npos  || FnName.find("INIT")!=string::npos){
                    (Kcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,uintial));
                    #ifdef TEST_GM
                    OP<<"Sensitive init function: "<< *Inst<<" The called function name is: "<<FnName<<"\n";
                    #endif
                    sensitive_inst_in_funck_type1++;
                    sfk->sen_list[sfk->size].bbl_NO = KfromCountNum;
                    sfk->sen_list[sfk->size].type = uintial;
                    sfk->sen_list[sfk->size++].inst = Inst;        
                } 
            }
        }

        Feature Kcur_bblfeature = bblFeature(Kcur_bbl_info->Instructions);
        Kcur_bbl_info->Inbbfeature = Kcur_bblfeature;
        #ifdef TEST_GM_NORM
        OP << "\nBB"<<KfromCountNum<<" Original KcurBBContend\t" << KcurBBContend;
        #endif
        KcurBBContend = Filter(KcurBBContend);
        std::hash<std::string> KCurhasher;
        auto KcurBBhashed = KCurhasher(KcurBBContend);
        Kcur_bbl_info->BBhash = KcurBBhashed;
        #ifdef TEST_GM_NORM 
        OP <<"\nNormalized KcurBBContend: \n" << KcurBBContend<<"\nKSuccBBhashed is:\t" << KcurBBhashed;
        #endif   
        KContend = KContend + KcurBBContend;
        int Ksucc_no = 0; // the number of successor
        int KCursucc_no = 0; // the i-th successor
        // Deal with the Successor of current basic block.
        for (succ_iterator PI = succ_begin(KcurBB), E = succ_end(KcurBB); PI != E; ++PI) 
            Ksucc_no = Ksucc_no +1;
        // Visit the succerors of a basic block
        for (succ_iterator PI = succ_begin(KcurBB), E = succ_end(KcurBB); PI != E; ++PI) {
            BasicBlock *KSuccBB = *PI;
            KCursucc_no = KCursucc_no +1;
            if (basicBlockMap.find(KSuccBB) != basicBlockMap.end()){
                KtoCountNum = basicBlockMap[KSuccBB];   
            }
            else{
                KtoCountNum = KbbCount;
                basicBlockMap[KSuccBB] = KbbCount++;
            }
            #ifdef TEST_GM
            OP << "\tBB" << KfromCountNum<< "-> BB"<< KtoCountNum << ";\n";
            #endif
            AddChild(Kcur_bbl_info, KtoCountNum);
        }
       KbasicBlockInfo[KfromCountNum] = Kcur_bbl_info;
       
    }
    // If there are no any sensitive operations in kernel function , we will not analyze the corresponding firmware function


    string KIRMAPPath = DeleteFileExt(MKName,".bc");
    
    
    auto Khashed = Khasher(KContend); 
    #ifdef TEST_GM 
    OP << "\nKhashed:\t" << Khashed << "\n";
    #endif

     // Obtain CFG of function F
    int sensitive_inst_in_funcf = 0;
    int sensitive_inst_in_funcf_type0 = 0;
    int sensitive_inst_in_funcf_type1 = 0;
    int sensitive_inst_in_funcf_type2 = 0;
    int sensitive_inst_in_funcf_type3 = 0;
    
    for (Function::iterator FB_iter = F->begin(); FB_iter != F->end(); ++FB_iter){
        // Obtain the current basic block.
        BasicBlock* FcurBB = &*FB_iter;
        bbl_info Fcur_bbl_info= InitBBL();
        Fcur_bbl_info->bbl = FcurBB;
        // We define BBContend to record IR within a basic block and get the Hash of BBContend to determine if BB is identical.  
        int FfromCountNum;
        int FtoCountNum;
        if (basicBlockMap.find(FcurBB) != basicBlockMap.end()){
            FfromCountNum = basicBlockMap[FcurBB];
        }
        else{
            FfromCountNum = FbbCount;
            basicBlockMap[FcurBB] = FbbCount++;
        }
        #ifdef TEST_GM 
        OP << "\nFcurBB\tBB" << FfromCountNum << " [shape=record, label=\"{BB" << FfromCountNum << ":\\l\\l";
        #endif
        // Obtain the hash of curBB
        Fcur_bbl_info->BBLID = FfromCountNum;

        Instruction *FFirstInst = FindFirstValidateInst(FcurBB);
        FFIRMAP.insert(make_pair(FfromCountNum, FFirstInst));

        std::string FcurBBContend = "";
        llvm::raw_string_ostream frso(FcurBBContend);
       
        string FnName;
        
        for (BasicBlock::iterator FI_iter = FcurBB->begin(); FI_iter != FcurBB->end(); ++FI_iter){
            Instruction *Inst = &*FI_iter;
            if(!Inst)
                continue;
            FI_iter->print(frso);
            Function *F = FcurBB->getParent();
            Fcur_bbl_info->Instructions.push_back(Inst);
            if(isa<BranchInst>(Inst) || isa<SwitchInst>(Inst) || isa<SelectInst>(Inst)) {
                #ifdef TEST_GM
                OP<<"\n"<<*Inst;
                OP<<"Condition.\n";
                printSourceCodeInfoInst(Inst);
                #endif
                Instruction *IC = NULL;
                SensitiveChecksPass FSCPass(FGlobalCtx, "SecurityCheck");
                if(FSCPass.IsSecurityCheck(F,Inst) || IsSecurityCheckStopExe(F,Inst)) {
                    (Fcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,scheck));
                    sensitive_inst_in_funcf_type0++;
                    Value *Cond = NULL;
                    if(isa<BranchInst>(Inst)){
                        BranchInst *BIf = dyn_cast<BranchInst>(Inst);
                        Cond = BIf->getCondition();  
                    }
                    else if(isa<SwitchInst>(Inst)){
                        SwitchInst *SIf = dyn_cast<SwitchInst>(Inst);
                        Cond = SIf->getCondition(); 
                    }
                    else{
                        SelectInst *SIf = dyn_cast<SelectInst>(Inst);
                        Cond = SIf->getCondition();
                    }
                    if(Cond)
                        IC  = dyn_cast<ICmpInst>(Cond);    
                    sff->sen_list[sff->size].bbl_NO = FfromCountNum;
                    sff->sen_list[sff->size].type = scheck; 
                    if(IC != NULL)
                        sff->sen_list[sff->size++].inst = IC;
                    else
                        sff->sen_list[sff->size++].inst = Inst; 
                    #ifdef TEST_GM 
                    OP<<"Sensitive FInstruction in condition branch:\t"<< *Inst<<"\n";
                    #endif 
              }
            }
            else if(isa<CallInst>(Inst)){
                CallInst *CI = dyn_cast<CallInst>(Inst);
                FnName = getCalledFuncName(CI);
                if(Is_element_in_stingvector((FGlobalCtx->LockFuncs), FnName)) {
                    (Fcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,ulock));
                    sensitive_inst_in_funcf_type2++;
                    sff->sen_list[sff->size].bbl_NO = FfromCountNum;
                    sff->sen_list[sff->size].type = ulock;
                    sff->sen_list[sff->size++].inst = Inst;
                    #ifdef TEST_GM 
                    OP<<"Sensitive lock function: "<< *Inst<<" The called function name is: "<<FnName<<"\n";
                    #endif   
                }
                else if(Is_element_in_stingvector((FGlobalCtx->PairFuncs), FnName)){
                    (Fcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,pfunc));
                    sensitive_inst_in_funcf_type3++;
                    sff->sen_list[sff->size].bbl_NO = FfromCountNum;
                    sff->sen_list[sff->size].type = pfunc;
                    sff->sen_list[sff->size++].inst = Inst;
                    #ifdef TEST_GM 
                    OP<<"Sensitive pair function: "<< *Inst<<" The called function name is: "<<FnName<<"\n";
                    #endif        
                } 
                else if((FGlobalCtx->InitFuncs).count(FnName)||(FGlobalCtx->CopyFuncs).count(FnName)|| FnName.find("init")!=string::npos|| FnName.find("INIT")!=string::npos){
                    (Fcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,uintial));
                    sensitive_inst_in_funcf_type1++;
                    sff->sen_list[sff->size].bbl_NO = FfromCountNum;
                    sff->sen_list[sff->size].type = uintial;
                    sff->sen_list[sff->size++].inst = Inst;  
                    #ifdef TEST_GM 
                    OP<<"Sensitive init function: "<< *Inst<<" The called function name is: "<<FnName<<"\n";
                    #endif
                } 
            }    
        }
        
        Feature Fcur_bblfeature = bblFeature(Fcur_bbl_info->Instructions);        
        Fcur_bbl_info->Inbbfeature = Fcur_bblfeature;
        #ifdef TEST_GM_NORM 
        OP << "BB"<<FfromCountNum<< " Original FcurBBContend:\n" << FcurBBContend;
        #endif
        FcurBBContend = Filter(FcurBBContend);
        std::hash<std::string> FCurhasher;
        auto FcurBBhashed = FCurhasher(FcurBBContend);
        Fcur_bbl_info->BBhash = FcurBBhashed;
        #ifdef TEST_GM_NORM 
        OP <<"\nNormalized FcurBBContend:\n" << FcurBBContend<<"\nFcurBBhashed is:\t" << FcurBBhashed;
        #endif    
        FContend = FContend + FcurBBContend;
        int Fsucc_no = 0;  // the number of successor
        int FCursucc_no = 0; // the i-th successor
        // Deal with the Successor of current basic block.
        for (BasicBlock *FSuccBB : successors(FcurBB))
            Fsucc_no = Fsucc_no +1;
        for (BasicBlock *FSuccBB : successors(FcurBB)){
            FCursucc_no = FCursucc_no +1; 
            if (basicBlockMap.find(FSuccBB) != basicBlockMap.end()){
                FtoCountNum = basicBlockMap[FSuccBB];   
            }
            else{
                FtoCountNum = FbbCount;
                basicBlockMap[FSuccBB] = FbbCount++;
            }
            #ifdef TEST_GM 
            OP << "\tBB" << FfromCountNum<< "-> BB"<< FtoCountNum << ";\n";
            #endif
            AddChild(Fcur_bbl_info,FtoCountNum);
        }
        FbasicBlockInfo[FfromCountNum] = Fcur_bbl_info;  
    }

    string FIRMAPPath = DeleteFileExt(MKName,".bc");
    

    sensitive_inst_in_funck = sensitive_inst_in_funck_type1+sensitive_inst_in_funck_type2+sensitive_inst_in_funck_type3+sensitive_inst_in_funck_type0;
    sensitive_inst_in_funcf = sensitive_inst_in_funcf_type1+sensitive_inst_in_funcf_type2+sensitive_inst_in_funcf_type3+sensitive_inst_in_funcf_type0;
  
    if(sensitive_inst_in_funck_type1 > sensitive_inst_in_funcf_type1||
       sensitive_inst_in_funck_type2 > sensitive_inst_in_funcf_type2||
       sensitive_inst_in_funck_type3 > sensitive_inst_in_funcf_type3||
       sensitive_inst_in_funck_type0 > sensitive_inst_in_funcf_type0){
            potencial_delete_security_operation++;
            #ifdef TEST_GM 
            OP<<" sensitive_inst_in_funck_type0 is : "<< sensitive_inst_in_funck_type0<<"\n";
            OP<<" sensitive_inst_in_funck_type1 is : "<< sensitive_inst_in_funck_type1<<"\n";
            OP<<" sensitive_inst_in_funck_type2 is : "<< sensitive_inst_in_funck_type2<<"\n";
            OP<<" sensitive_inst_in_funck_type3 is : "<< sensitive_inst_in_funck_type3<<"\n";
            OP<<" sensitive_inst_in_funcf_type0 is : "<< sensitive_inst_in_funcf_type0<<"\n";
            OP<<" sensitive_inst_in_funcf_type1 is : "<< sensitive_inst_in_funcf_type1<<"\n";
            OP<<" sensitive_inst_in_funcf_type2 is : "<< sensitive_inst_in_funcf_type2<<"\n";
            OP<<" sensitive_inst_in_funcf_type3 is : "<< sensitive_inst_in_funcf_type3<<"\n";
            OP<<"sensitive func: "<<FuncFName<<"\n";
            #endif
            
       }
        
    auto Fhashed = Fhasher(FContend);  
   
    if(Fhashed != Khashed)
        sameGraph = 0; 
    
    FindParent_sibling(KbasicBlockInfo);
    FindParent_sibling(FbasicBlockInfo);

    
    std::vector<int> kcommon_node;
    std::queue<int> kcommon_subgraph;
    std::vector<int> fcommon_node;
    std::queue<int> fcommon_subgraph;
    std::vector<int> remain_graph1;
    std::vector<int> remain_graph2;    
    for(auto kbI : KbasicBlockInfo) { 
        remain_graph1.push_back(kbI.first);
    } 
        for(auto fbI : FbasicBlockInfo) { 
        remain_graph2.push_back(fbI.first);
    } 
    std::map<int,int> MCSMap;
    OP<<"Different function pair:\t"<<FuncFName<<"\n";
    NotIdenticalFunc++;
    OP<<"sensitive insts in a K funcs\n";
    std::pair<Sensitive_Info_of_Functions*, std::set<int>> ssk = ObtainsensitiveBBLset(&KbasicBlockInfo, kcommon_node);
    OP<<"sensitive insts in a F funcs\n";
    std::pair<Sensitive_Info_of_Functions*, std::set<int>> ssf = ObtainsensitiveBBLset(&FbasicBlockInfo, fcommon_node);
    Sensitive_Info_of_Functions *sk = ssk.first; 
    Sensitive_Info_of_Functions *sf = ssf.first; 
    // The set of basic blocks that contain sensitive operation and are not int the MSC 
    set<int> SScfgk = ssk.second ;
    set<int> SScfgf = ssf.second ;

    
    // the deleted sensitive operations in SScfgk
    std::vector<int>DeletedBBlist; 
    // DeletedSSlists stores the deleted instruction and the corresponding  basic block ID in firmware, if there is no matching BBL ID, we set it to be -1.
    std::map<llvm::Instruction*, int> DeletedSSlists; 
    
   

    string inputfile =  DeleteFileExt(MKName,".bc")+"/"+ FuncFName+".input"; 
    string processfilename = DeleteFileExt(MKName,".bc")+"/"+ FuncFName+".process"; 
    string processfilename_tmp = DeleteFileExt(MKName,".bc")+"/"+ FuncFName+".process_tmp"; 
    string outputfile = DeleteFileExt(MKName,".bc")+"/"+ FuncFName+".output"; 
    
  

    totalstartTime = clock();

    GenerateDeletedSoNew(SScfgk,&kcommon_subgraph,&kcommon_node,KbasicBlockInfo,&remain_graph1,
    SScfgf,&fcommon_subgraph,&fcommon_node, FbasicBlockInfo,&remain_graph2,
    &MCSMap, &DeletedBBlist, &DeletedSSlists, local_msg, processfilename);

    totalendTime=clock();

    string mcs_contend = "\"MCS\":\"" + DumpMCS(&MCSMap) + "\",\n\"sensitive_inst_in_funck_type0\": \""  +  getIntContent(sensitive_inst_in_funck_type0)+
    "\",\n\"sensitive_inst_in_funck_type1\": \""  +  getIntContent(sensitive_inst_in_funck_type1) + "\",\n\"sensitive_inst_in_funck_type2\": \""  +  getIntContent(sensitive_inst_in_funck_type2)+
    "\",\n\"sensitive_inst_in_funck_type3\": \""  +  getIntContent(sensitive_inst_in_funck_type3) + "\",\n\"sensitive_inst_in_funcf_type0\": \""  +  getIntContent(sensitive_inst_in_funcf_type0)+
    "\",\n\"sensitive_inst_in_funcf_type1\": \""  +  getIntContent(sensitive_inst_in_funcf_type1) + "\",\n\"sensitive_inst_in_funcf_type2\": \""  +  getIntContent(sensitive_inst_in_funcf_type2)+
    "\",\n\"sensitive_inst_in_funcf_type3\": \""  +  getIntContent(sensitive_inst_in_funcf_type3)+ "\"\n";
    
    double analyeTime = (double)(totalendTime - totalstartTime) / CLOCKS_PER_SEC ;
    return make_tuple(sameGraph, analyeTime, MCSMap.size(), mcs_contend);  
}

// search if the function  name is in the set
bool searchfunc(string funcname,  vector<string> funcSet){
    for(vector<string>::iterator iter =funcSet.begin(); iter!=funcSet.end();iter++ ){
        if(funcname ==*iter)
            return true;
    }
    return false;
}

// The Inst that can reach to Return Inst by one branch basic block (one hop)
bool OneHopRetInst(Instruction *I){
    Instruction *Inst = &*I;
    if(isa<BranchInst>(Inst)){
        BranchInst *BI = dyn_cast<BranchInst>(Inst);
        if(BI->getNumSuccessors() < 2)
        {
            for(succ_iterator PI = succ_begin(BI->getParent()), E = succ_end(BI->getParent()); PI != E; ++PI)
            {
                BasicBlock *SuccBB = *PI;
                if(SuccBB->size()== 1)
                for (BasicBlock::iterator I_iter = SuccBB->begin(); I_iter != SuccBB->end(); ++I_iter) 
                    {
                        Instruction *instruction = &*I_iter;
                        
                        if(isa<ReturnInst>(instruction)) 
                            return true;  
                    }
            }
        }
    }
    return false;
}

//  Check if  one of the succssors is of Instruction *I is "return void"
bool IsSecurityCheckStopExe(Function *F, Instruction *I){
    Instruction *Inst = &*I;
    if (isa<BranchInst>(Inst) || isa<SwitchInst>(Inst)){
		BranchInst *BI = dyn_cast<BranchInst>(Inst);
		SwitchInst *SI = NULL;
		if (BI) {
			if (BI->getNumSuccessors() < 2)
				return false;
		} 
		else {
			SI = dyn_cast<SwitchInst>(Inst);
			if (SI->getNumSuccessors() < 2)
				return false;
		}
        if (BI) 
            {
                for(succ_iterator PI = succ_begin(BI->getParent()), E = succ_end(BI->getParent()); PI != E; ++PI)
                {
                    BasicBlock *SuccBB = *PI;
                    if(SuccBB->size()== 1)
                    for (BasicBlock::iterator I_iter = SuccBB->begin(); I_iter != SuccBB->end(); ++I_iter) 
                        {
                            Instruction *instruction = &*I_iter;
                            if(isa<ReturnInst>(instruction) || OneHopRetInst(instruction)) 
                                return true;
                            
                        }
                }
            }
        else
			{
                for(succ_iterator PI = succ_begin(SI->getParent()), E = succ_end(SI->getParent()); PI != E; ++PI)
                {
                    BasicBlock *SuccBB = *PI;
                    if(SuccBB->size()== 1)
                    for (BasicBlock::iterator I_iter = SuccBB->begin(); I_iter != SuccBB->end(); ++I_iter) 
                        {
                            Instruction *instruction = &*I_iter;
                    
                            if(isa<ReturnInst>(instruction) || OneHopRetInst(instruction)) 
                                return true;
                        }
                }
            }
    }
    else if (SelectInst *SI = dyn_cast<SelectInst>(Inst)) 
       {
            for(succ_iterator PI = succ_begin(SI->getParent()), E = succ_end(SI->getParent()); PI != E; ++PI)
            {
                BasicBlock *SuccBB = *PI;
                if(SuccBB->size()== 1)
                for (BasicBlock::iterator I_iter = SuccBB->begin(); I_iter != SuccBB->end(); ++I_iter) 
                    {
                        Instruction *instruction = &*I_iter;
                        
                        if(isa<ReturnInst>(instruction) || OneHopRetInst(instruction)) 
                            return true;
                    }
            }
        } 
		
	
    return false;
}



// Function Check_OMP finds and analyzes the deleted security operation in Iot firmware.
void TranverseBC( ModulePairList *modulepairlist,  GlobalContext *KGlobalCtx,  GlobalContext *FGlobalCtx)
{
    string content = "";
    ModuleNameMap KMNM = KGlobalCtx->ModuleMaps;
    ModuleNameMap FMNM = FGlobalCtx->ModuleMaps;
    ModulePairList MP = *modulepairlist;
    for(int it = 0; it<modulepairlist->size(); ++it){
        Module *ModuleKernel = (MP[it]).first;
        Module *ModuleFirmware = (MP[it]).second;
        int FuncKernel = ModuleKernel->size();
        int FuncFirmware = ModuleFirmware->size();
        string MKName = KMNM[ModuleKernel];
        string MFName = FMNM[ModuleFirmware];
        for (Module::iterator f = ModuleKernel->begin(), fe = ModuleKernel->end(); 
                f != fe; ++f) {
                Function *F = &*f;
                if (F->empty())
                    continue;
                
                for (Function::iterator KB_iter = F->begin(); KB_iter != F->end(); ++KB_iter){
                    BasicBlock *KcurBB = &*KB_iter;
                    for (BasicBlock::iterator KI_iter = KcurBB->begin(); KI_iter != KcurBB->end(); ++KI_iter) {
                        Instruction *Inst = &*KI_iter;
                        OP<<"\n"<<*Inst;
                        for(auto U : Inst->users()){
                                OP<<"\nU is:\t"<<*U;
                            }
                    }
                }
        }
    }
}

void TranverseF( Function *F)
{    
   
    for (Function::iterator KB_iter = F->begin(); KB_iter != F->end(); ++KB_iter){
        BasicBlock *KcurBB = &*KB_iter;
        for (BasicBlock::iterator KI_iter = KcurBB->begin(); KI_iter != KcurBB->end(); ++KI_iter) {
            Instruction *Inst = &*KI_iter;
           
            if(getInstContent(Inst).find("epread")!=string::npos )
            for(auto U : Inst->users()){
                    OP<<"\nU is:\t"<<*U << " + line"<< GetLocation(U);
                }
            if(getInstContent(Inst).find("%154")!=string::npos ){
                for(int i = 0; i < Inst->getNumOperands(); i++){    
                    Value *operand = Inst->getOperand(i); 
                    for(auto U : operand->users()){
                    OP<<"\noperand U is:\t"<<*U << " + line"<< GetLocation(U);
                }
                }
            }
            
        }
    } 
}

void Check_Deleted_Func( ModulePairList *modulepairlist,  GlobalContext *KGlobalCtx,  GlobalContext *FGlobalCtx)
{  
    int MapFucByName = 0;
    // curBC indicates the ID of a .bc file that is being analyzed.
    int curBC = 0;
    int curFuc = 0;
    int DeletedFunc = 0;
    clock_t totalstartTime, totalendTime;
    totalstartTime = clock();
    ModuleNameMap KMNM = KGlobalCtx->ModuleMaps;
    ModuleNameMap FMNM = FGlobalCtx->ModuleMaps;
    ModulePairList MP = *modulepairlist;
    ModulePairList::iterator iter;
    FuncPairList  funcpairlist;
    
    for(int it = 0; it<modulepairlist->size(); ++it){
        curBC ++;
       
        Module *ModuleKernel = (MP[it]).first;
        Module *ModuleFirmware = (MP[it]).second;
        int FuncKernel = ModuleKernel->size();
        int FuncFirmware = ModuleFirmware->size();
        string MKName = KMNM[ModuleKernel];
        string MFName = FMNM[ModuleFirmware];
        
        
        for (Module::iterator k = ModuleKernel->begin(), ke = ModuleKernel->end(); 
            k != ke; ++k) {
           
            Function *K = &*k;
            if (K->empty())
                continue;          
            if (K->size() > MAX_BLOCKS_SUPPORT)
                continue;
            bool flag = false;
            curFuc++;
            // obtain func name of .bc file in Firmware
            for (Module::iterator f = ModuleFirmware->begin(), fe = ModuleFirmware->end(); 
            f != fe; ++f) {
                Function *F = &*f;
                if (F->empty())
                    continue;
                if (F->size() > MAX_BLOCKS_SUPPORT)
                    continue;
                
                if (F->getName() == K->getName()){
                    flag = true;
                    if(Identical(K, F))
                        break;
                    funcpairlist.push_back(make_tuple(K,MKName,F,MFName));
                    
                    break;
                }
            }
            if(flag == false)
                DeletedFunc ++;
        }
    }
    dump_buffer1(string(kernel_eddition) + ": " + getIntContent(DeletedFunc), "/CPscan/Kanalyzer/data/result/cpscan-delBBInfo/DeletedFunc.txt");
}
void Check_OMP( ModulePairList *modulepairlist,  GlobalContext *KGlobalCtx,  GlobalContext *FGlobalCtx)
{    
    // MapFucByName defines the number of function pairs of kernel functions and firmware functions, which are mapped by function name.
    int MapFucByName = 0;
    // curBC indicates the ID of a .bc file that is being analyzed.
    int curBC = 0;
    int curFuc = 0;
    clock_t totalstartTime, totalendTime;
    clock_t FuncAnalyzeSTime, FuncAnalyzeETime;
    totalstartTime = clock();
    ModuleNameMap KMNM = KGlobalCtx->ModuleMaps;
    ModuleNameMap FMNM = FGlobalCtx->ModuleMaps;
    ModulePairList MP = *modulepairlist;
    ModulePairList::iterator iter;
    FuncPairList  funcpairlist;
    double FuncAnalyzeTime ;
    

    string result_Dir = (string)DATA_DIR+"../result/"+RecordDate;
    if(!IsPathExist(Convertstr2char(result_Dir))){
        const int dir_err = mkdir(Convertstr2char(result_Dir) , 0777 );
        if (dir_err !=0)
            OP<<"Error creating directory!n";
    } 
    string FPRecord =  (string)DATA_DIR+ "../result/"+RecordDate+"/FPRecord-"+kernel_eddition+".txt";
    if (FILE *file = fopen(Convertstr2char(FPRecord), "r")){
        if(remove(Convertstr2char(FPRecord))==0)
            OP<<"delete sucessfully.";
    }
    string SSInfoDir =  (string)DATA_DIR+ "../result/"+RecordDate+"/SSINFO-"+kernel_eddition+".txt";
    if (FILE *file = fopen(Convertstr2char(SSInfoDir), "r")){
        if(remove(Convertstr2char(SSInfoDir))==0)
            OP<<"delete sucessfully.";
    }
    
    string staticsDir = (string)DATA_DIR+ "../result/TimeRecord/Statics-"+ RecordDate + "-" +kernel_eddition+".txt";
    if (FILE *file = fopen(Convertstr2char(staticsDir), "r")){
        if(remove(Convertstr2char(staticsDir))==0)
            OP<<"delete sucessfully.";
    }
    string dumpfile = "/CPscan/Kanalyzer/data/result/cpscan-delBBInfo/deleBBInfo" + (string)(kernel_eddition) + ".csv";
    if (FILE *file = fopen(Convertstr2char(dumpfile), "r")){
        if(remove(Convertstr2char(dumpfile))==0)
            OP<<"delete sucessfully.";
    }
    
    
    #ifdef MultiThread
        int MaxThread = omp_get_max_threads();
        omp_set_num_threads(MaxThread);
        int numProcs = omp_get_num_procs();
        #pragma omp parallel for num_threads(numProcs-15)
    #endif
    {
        for(int it = 0; it<modulepairlist->size(); ++it){
            curBC ++;
            
            Module *ModuleKernel = (MP[it]).first;
            Module *ModuleFirmware = (MP[it]).second;
            int FuncKernel = ModuleKernel->size();
            int FuncFirmware = ModuleFirmware->size();
            string MKName = KMNM[ModuleKernel];
            string MFName = FMNM[ModuleFirmware];
            
            
            for (Module::iterator f = ModuleFirmware->begin(), fe = ModuleFirmware->end(); 
                f != fe; ++f) {
               
                Function *F = &*f;
                if (F->empty())
                    continue;
                if (F->size() > MAX_BLOCKS_SUPPORT)
                    continue;
                curFuc++;
                // obtain func name of .bc file in Firmware
                for (Module::iterator k = ModuleKernel->begin(), ke = ModuleKernel->end(); 
                k != ke; ++k) {
                    Function *K = &*k;
                    if (K->empty())
                    continue;          
                    if (K->size() > MAX_BLOCKS_SUPPORT)
                    continue;
                    if (F->getName() == K->getName()){
                        if(Identical(K, F))
                            break;
                        funcpairlist.push_back(make_tuple(K,MKName,F,MFName));
                        OP<<"\n Function K:"<< K->getName()<<" Function F: "<< F->getName();
                        break;
                    }
                }
            }
        }
    }
    OP<<"\nfuncpairlist.size is: "<<funcpairlist.size();

    #ifdef MultiThread
        OP<<"\nMUlti in function pair analysis.";
        MaxThread = omp_get_max_threads();
        omp_set_num_threads(MaxThread);
        #pragma omp parallel for
    #endif
    
    
    
    for(int funit = 0; funit < funcpairlist.size(); ++funit){
        Function *K = get<0>(funcpairlist[funit]);
        string MKName = get<1>(funcpairlist[funit]);
        Function *F = get<2>(funcpairlist[funit]);
        string MFName = get<3>(funcpairlist[funit]);    
        unrollLoops_l(F);
        unrollLoops_l(K);
        rewritting(F, FGlobalCtx);
        rewritting(K, KGlobalCtx);
        FuncAnalyzeSTime=clock();
        AnalyzelargeCFG_OMP(F, K, MKName, KGlobalCtx, FGlobalCtx);
        FuncAnalyzeETime=clock();
        FuncAnalyzeTime = FuncAnalyzeTime + (double)(FuncAnalyzeETime - FuncAnalyzeSTime) / CLOCKS_PER_SEC;
    }                        
    
    MapFucByName = funcpairlist.size();
   
}


void Check_OMP_GM_cmp( ModulePairList *modulepairlist,  GlobalContext *KGlobalCtx,  GlobalContext *FGlobalCtx)
{    
      
    
    // MapFucByName defines the number of function pairs of kernel functions and firmware functions, which are mapped by function name.
    int MapFucByName = 0;
    // curBC indicates the ID of a .bc file that is being analyzed.
    int curBC = 0;
    int curFuc = 0;
    clock_t totalstartTime, totalendTime;
    totalstartTime = clock();
    ModuleNameMap KMNM = KGlobalCtx->ModuleMaps;
    ModuleNameMap FMNM = FGlobalCtx->ModuleMaps;
    ModulePairList MP = *modulepairlist;
    ModulePairList::iterator iter;
    FuncPairList  funcpairlist;

    string result_Dir = (string)DATA_DIR+"../result/"+RecordDate;
    if(!IsPathExist(Convertstr2char(result_Dir))){
        const int dir_err = mkdir(Convertstr2char(result_Dir) , 0777 );
        if (dir_err !=0)
            OP<<"Error creating directory!n";
    } 
    string FPRecord =  (string)DATA_DIR+ "../result/"+RecordDate+"/FPRecord-"+kernel_eddition+".txt";
    if (FILE *file = fopen(Convertstr2char(FPRecord), "r")){
    if(remove(Convertstr2char(FPRecord))==0)
        OP<<"delete sucessfully.";
    }
    string SSInfoDir =  (string)DATA_DIR+ "../result/"+RecordDate+"/SSINFO-"+kernel_eddition+".txt";
    if (FILE *file = fopen(Convertstr2char(SSInfoDir), "r")){
    if(remove(Convertstr2char(SSInfoDir))==0)
        OP<<"delete sucessfully.";
    }

    
    #ifdef MultiThread
        //OP<<"\nMUlti.";
        int MaxThread = omp_get_max_threads();
        omp_set_num_threads(MaxThread);
        #pragma omp parallel for
        //OP << "\nThread: "<< omp_get_thread_num()<< ". Nthreads " <<   omp_get_num_threads()<<". MaxThread: "<<MaxThread;
    #endif
    {
        for(int it = 0; it<modulepairlist->size(); ++it){
            curBC ++;
            //OP<<"curBC is:\t"<<curBC<<"\n"; 
            Module *ModuleKernel = (MP[it]).first;
            Module *ModuleFirmware = (MP[it]).second;
            int FuncKernel = ModuleKernel->size();
            int FuncFirmware = ModuleFirmware->size();
            string MKName = KMNM[ModuleKernel];
            string MFName = FMNM[ModuleFirmware];
            OP<<"\nKBCName is:"<<MKName;
            OP<<"\nFBCName is:"<<MFName;
            
            for (Module::iterator f = ModuleFirmware->begin(), fe = ModuleFirmware->end(); 
                f != fe; ++f) {
                // BigCFG is utilized to store functions that are not easy to match 
                Function *F = &*f;
                if (F->empty())
                    continue;
                if (F->size() > MAX_BLOCKS_SUPPORT)
                    continue;
                curFuc++;
                // obtain func name of .bc file in Firmware
                for (Module::iterator k = ModuleKernel->begin(), ke = ModuleKernel->end(); 
                k != ke; ++k) {
                    Function *K = &*k;
                    if (K->empty())
                    continue;
                    if (K->size() > MAX_BLOCKS_SUPPORT)
                    continue;
                    //if(F->getName() == "mtd_ioctl")
                    if (F->getName() == K->getName()){
                        if(Identical(K, F))
                            break;
                        funcpairlist.push_back(make_tuple(K,MKName,F,MFName));
                        OP<<"\n Function K:"<< K->getName()<<" Function F: "<< F->getName();
                        break;
                    }
                }
            }
        }
    }
    OP<<"\nfuncpairlist.size is: "<<funcpairlist.size();
    
    string TimeLog_cpscan = "";
    string TimeRecord_cpscan =  (string)DATA_DIR+ "../result/TimeRecord/new-TimeRecord/TimeLog-cpscan-"+ RecordDate + "-" +kernel_eddition+".txt";
    string TimeRecord_mcgregor =  (string)DATA_DIR+ "../result/TimeRecord/new-TimeRecord/TimeLog-mcgregor-"+ RecordDate + "-" +kernel_eddition+".txt";
    
    for(int funit = 0; funit < funcpairlist.size(); ++funit){
        
        Function *K = get<0>(funcpairlist[funit]);
        string MKName = get<1>(funcpairlist[funit]);
        Function *F = get<2>(funcpairlist[funit]);
        string MFName = get<3>(funcpairlist[funit]);  
       
        string content  =  "****************Function***************\n";
        //content = content + DumpFunction(F);
        unrollLoops_l(F);
        unrollLoops_l(K);
        OP<<"\nbp01.";	
        content = content +  "\n**************** Unloop Function***************\n";
       
        rewritting(F, FGlobalCtx);
	    
        rewritting(K, KGlobalCtx);
	   
        content = content +  "\n**************** Rewritting Function***************\n";
       
        
        std::pair<int, double> mcgregor;
        mcgregor = CompareCFG_GM_cmp(F, K, MKName, KGlobalCtx, FGlobalCtx);
        string TimeLog_mcgregor =  "MKName:" + MKName + ";FName:" + (K->getName()).str()  + ";KSize:" + getIntContent(K->size()) + ";FSize:" + getIntContent(F->size()) 
         + ";mcgregor_sameGraph:" + getIntContent(mcgregor.first) + ";mcgregor_time:" + getDoubleContent(mcgregor.second) + "\n" ; 
        dump_buffer1(TimeLog_mcgregor, TimeRecord_mcgregor);        
    } 
                  
    
    
    
    MapFucByName = funcpairlist.size();  
    totalendTime=clock();
    
}


Instruction* FindFirstValidateInst(BasicBlock *curBB){
    for (BasicBlock::iterator KI_iter = curBB->begin(); KI_iter != curBB->end(); ++KI_iter) {
        Instruction *Inst = &*KI_iter;
        string Tmp = getInstContent(Inst);
        if(Tmp.find("=")!=string::npos)
            return Inst;
        }
    return &*(curBB->begin());
}

/* 
    CompareCFG will generate the MSC of two graphs (CFG of kernel function and firmware function)
    Sensitive_Info_of_Functions is utilized to store all the sensitive operation in a function
        llvm::Function *F;
        int size;
        struct sensitive_item sen_list[200];
*/
 void CompareCFG(Function *F, Function *K, string MKName, GlobalContext *KGlobalCtx, GlobalContext *FGlobalCtx)
{  
    // record basic block ID and the first instruction to map with IR
    std::map<int, Instruction*> KFIRMAP, FFIRMAP;

    char* local_msg = (char*)calloc(BUFFERSIZE , sizeof(unsigned char));  
    if(local_msg==NULL)
        OP<<"ERROR calloc.\n";
    
    Sensitive_Info_of_Functions *sfk, *sff;  
    sfk=new(Sensitive_Info_of_Functions);
    sff=new(Sensitive_Info_of_Functions);
    if(!sfk || !sff)
        OP<<"Malloc Sensitive_Info_of_Functions Error!\n";
    sfk->F = K;
    sff->F = F;
    sfk->size = 0;
    sff->size = 0;
    string FuncFName = F->getName();
    Graph cfgK(K->size()), cfgF(F->size()), MSC;
    Mapbbl KbasicBlockInfo,  FbasicBlockInfo;

    User_callback<Graph,Graph,string,string, Mapbbl, Mapbbl, struct GlobalContext*, struct GlobalContext*, char*, pthread_mutex_t*> user_callback 
    (cfgK,cfgF,MKName,FuncFName,KbasicBlockInfo,FbasicBlockInfo,KGlobalCtx, FGlobalCtx, local_msg);
    std::vector<string> VetexK, VetexF;

    VertexNameMap Kvname_map_simple = get(vertex_name, cfgK);
    VertexIndexMap  Kvname_index_simple = get(vertex_index,cfgK);
    EdgeNameMap Kedge_name = get(edge_name, cfgK);

    VertexNameMap Fvname_map_simple = get(vertex_name, cfgF);
    VertexIndexMap  Fvname_index_simple = get(vertex_index,cfgF);
    EdgeNameMap Fedge_name = get(edge_name, cfgF);

    std::error_code error;
    std::map<BasicBlock*, int> basicBlockMap;
    
    int FbbCount = 0,  KbbCount = 0;    
    string FContend = "",  KContend = "";
    std::hash<std::string> Fhasher, Khasher;
    
    int sensitive_inst_in_funck = 0;
    int sensitive_inst_in_funck_type0 = 0;
    int sensitive_inst_in_funck_type1 = 0;
    int sensitive_inst_in_funck_type2 = 0;
    int sensitive_inst_in_funck_type3 = 0;
    
    // Obtain CFG of function K, tranverse basic blocks of K
    for (Function::iterator KB_iter = K->begin(); KB_iter != K->end(); ++KB_iter){
        // Obtain the current basic block.
        BasicBlock *KcurBB = &*KB_iter;
        // store the info of basic block, including parent sibling and children list, sensitive operations;
        bbl_info  Kcur_bbl_info= InitBBL();
        Kcur_bbl_info->bbl = KcurBB;
        // We define BBContend to record IR within a basic block and get the Hash of BBContend to determine if BB is identical.  
        std::string name = KcurBB->getName().str();
        int KfromCountNum;
        int KtoCountNum;
        if (basicBlockMap.find(KcurBB) != basicBlockMap.end()){
            KfromCountNum = basicBlockMap[KcurBB];
        }
        else{
            KfromCountNum = KbbCount;
            basicBlockMap[KcurBB] = KbbCount++;
        }
        #ifdef TEST_GM
        OP << "\nKcurBB" <<"\tBB" << KfromCountNum << "\t[shape=record, label=\"{BB"<< KfromCountNum << ":\\l\\l";
        #endif
        // Obtain the hash of curBB
        Kcur_bbl_info->BBLID = KfromCountNum;
        // We need to record KfromCountNum
        // We need to record  KcurBB->begin()
        
        Instruction *KFirstInst = FindFirstValidateInst(KcurBB);  
        KFIRMAP.insert(make_pair(KfromCountNum, KFirstInst));

        std::string KcurBBContend = "";
        llvm::raw_string_ostream krso(KcurBBContend);
        
        std:string split = ";";
        bool sensitive = false;
        string  FnName;

        for (BasicBlock::iterator KI_iter = KcurBB->begin(); KI_iter != KcurBB->end(); ++KI_iter) {
            KI_iter->print(krso); 
            Instruction *Inst = &*KI_iter;
            Function *K = KcurBB->getParent();
            Kcur_bbl_info->Instructions.push_back(Inst);
            //If Inst is a branchInst, SwitchInst, or SelectInst, we perform security check
            if(isa<BranchInst>(Inst) || isa<SwitchInst>(Inst) || isa<SelectInst>(Inst)) {
                #ifdef TEST_GM
                OP<<"\n"<<*Inst;
                OP<<"Condition.\n";
                printSourceCodeInfoInst(Inst);
                #endif
                Instruction *IC = NULL;
                SensitiveChecksPass KSCPass(KGlobalCtx, "SecurityCheck");
                if(KSCPass.IsSecurityCheck(K,Inst) || IsSecurityCheckStopExe(K,Inst)) {
                    sensitive_inst_in_funck_type0++;
                    (Kcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,scheck));
                    #ifdef TEST_GM
                    OP<<"Sensitive KInstruction in condition branch:\t"<< *Inst<<"\n";
                    #endif
                    Value *Cond = NULL;
                    if(isa<BranchInst>(Inst)){
                        BranchInst *BIk = dyn_cast<BranchInst>(Inst);
                        Cond = BIk->getCondition();
                    }
                    else if(isa<SwitchInst>(Inst)){
                        SwitchInst *SIk = dyn_cast<SwitchInst>(Inst);
                        Cond = SIk->getCondition(); 
                    }
                    else{
                        SelectInst *SIk = dyn_cast<SelectInst>(Inst);
                        Cond = SIk->getCondition();
                    }
                    if(Cond) 
                        IC  = dyn_cast<ICmpInst>(Cond); 
                    sfk->sen_list[sfk->size].bbl_NO = KfromCountNum;
                    sfk->sen_list[sfk->size].type = scheck;
                    if(IC !=NULL)
                        sfk->sen_list[sfk->size++].inst = IC;
                    else
                        sfk->sen_list[sfk->size++].inst = Inst;   
              }
            }
            else if(isa<CallInst>(Inst)){
                CallInst *CI = dyn_cast<CallInst>(Inst);
                FnName = getCalledFuncName(CI);
                #ifdef TEST_GM
                OP<<"The Called FnName is:\t"<<FnName<<"\n";
                #endif
                if(Is_element_in_stingvector((KGlobalCtx->LockFuncs), FnName)) {
                    (Kcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,ulock));
                    #ifdef TEST_GM
                    OP<<"Sensitive lock function:\t"<< *Inst<<" "<<FnName<<"\n";
                    #endif
                    sensitive_inst_in_funck_type2++;
                    sfk->sen_list[sfk->size].bbl_NO = KfromCountNum;
                    sfk->sen_list[sfk->size].type = ulock;
                    sfk->sen_list[sfk->size++].inst = Inst;        
                }
                else if(Is_element_in_stingvector((KGlobalCtx->PairFuncs), FnName)){
                    (Kcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,pfunc));
                    #ifdef TEST_GM
                    OP<<"Sensitive pair function:\t"<< *Inst<<" "<<FnName<<"\n";
                    #endif
                    sensitive_inst_in_funck_type3++;
                    sfk->sen_list[sfk->size].bbl_NO = KfromCountNum;
                    sfk->sen_list[sfk->size].type = pfunc;
                    sfk->sen_list[sfk->size++].inst = Inst;        
                } 
                else if((KGlobalCtx->InitFuncs).count(FnName)||(KGlobalCtx->CopyFuncs).count(FnName)|| FnName.find("init")!=string::npos|| FnName.find("INIT")!=string::npos){
                    (Kcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,uintial));
                    #ifdef TEST_GM
                    OP<<"Sensitive init function:\t"<< *Inst<<" "<<FnName<<"\n";
                    #endif
                    sensitive_inst_in_funck_type1++;
                    sfk->sen_list[sfk->size].bbl_NO = KfromCountNum;
                    sfk->sen_list[sfk->size].type = uintial;
                    sfk->sen_list[sfk->size++].inst = Inst;        
                }    
            }
        }
        
       
        KcurBBContend = Filter(KcurBBContend);
        std::hash<std::string> KCurhasher;
        auto KcurBBhashed = KCurhasher(KcurBBContend);
        Kcur_bbl_info->BBhash = KcurBBhashed;
        KContend = KContend + KcurBBContend;
        int Ksucc_no = 0; 
        int KCursucc_no = 0; 
        for (succ_iterator PI = succ_begin(KcurBB), E = succ_end(KcurBB); PI != E; ++PI) 
            Ksucc_no = Ksucc_no +1;
        for (succ_iterator PI = succ_begin(KcurBB), E = succ_end(KcurBB); PI != E; ++PI){
            BasicBlock *KSuccBB = *PI;
            KCursucc_no = KCursucc_no +1;
            if (basicBlockMap.find(KSuccBB) != basicBlockMap.end()){
                KtoCountNum = basicBlockMap[KSuccBB];   
            }
            else{
                KtoCountNum = KbbCount;
                basicBlockMap[KSuccBB] = KbbCount++;
            }
           
            AddChild(Kcur_bbl_info, KtoCountNum);
            
            std::string KSuccBBContend = "";
            llvm::raw_string_ostream KSuccrso(KSuccBBContend);
            std::hash<std::string> KSucchasher;
            for (BasicBlock::iterator KJ_iter = KSuccBB->begin(); KJ_iter != KSuccBB->end(); ++KJ_iter) 
                    KJ_iter->print(KSuccrso);

           
            KSuccBBContend = Filter(KSuccBBContend);
            auto KSuccBBhashed = KSucchasher(KSuccBBContend);

            // Generate Graph 

            boost::put(Kvname_map_simple, KfromCountNum, to_string(KcurBBhashed));
            boost::put(Kvname_map_simple, KtoCountNum, to_string(KSuccBBhashed));
            // Attribute of edge;
            Edge  edgek;
            bool insertedk;
            if(Ksucc_no==1){
                    tie(edgek, insertedk) = add_edge(KfromCountNum, KtoCountNum, cfgK);  Kedge_name[edgek] = "F"; 
                }
            else if(Ksucc_no==2) {
                if(KCursucc_no==1){
                        tie(edgek, insertedk) = add_edge(KfromCountNum, KtoCountNum, cfgK);  Kedge_name[edgek] = "Y"; 
                    }
                else{
                        tie(edgek, insertedk) = add_edge(KfromCountNum, KtoCountNum, cfgK);  Kedge_name[edgek] = "N";
                }
            }
            else{
                tie(edgek, insertedk) = add_edge(KfromCountNum, KtoCountNum, cfgK);  Kedge_name[edgek] = "S"; 
            }   
        }
       KbasicBlockInfo[KfromCountNum] = Kcur_bbl_info;
       
    }
   
    string KIRMAPPath = DeleteFileExt(MKName,".bc");
    
    auto Khashed = Khasher(KContend); 

    #ifdef TEST_GM 
    OP  << "\nKhashed\n" <<  Khashed ;
    #endif
    

     // Obtain CFG of function F
    int sensitive_inst_in_funcf = 0;
    int sensitive_inst_in_funcf_type0 = 0;
    int sensitive_inst_in_funcf_type1 = 0;
    int sensitive_inst_in_funcf_type2 = 0;
    int sensitive_inst_in_funcf_type3 = 0;
    
    for (Function::iterator FB_iter = F->begin(); FB_iter != F->end(); ++FB_iter){
       
        BasicBlock* FcurBB = &*FB_iter;
        bbl_info Fcur_bbl_info= InitBBL();
        Fcur_bbl_info->bbl = FcurBB;
        
        int FfromCountNum;
        int FtoCountNum;
        if (basicBlockMap.find(FcurBB) != basicBlockMap.end())
        {
            FfromCountNum = basicBlockMap[FcurBB];
        }
        else
        {
            FfromCountNum = FbbCount;
            basicBlockMap[FcurBB] = FbbCount++;
        }
        #ifdef TEST_GM 
        OP<<"\nFcurBB:\tBB" << FfromCountNum << " [shape=record, label=\"{BB" << FfromCountNum << ":\\l\\l";
        #endif
        // Obtain the hash of curBB
        Fcur_bbl_info->BBLID = FfromCountNum;

        Instruction *FFirstInst =FindFirstValidateInst(FcurBB);
        FFIRMAP.insert(make_pair(FfromCountNum, FFirstInst));

        std::string FcurBBContend = "";
        llvm::raw_string_ostream frso(FcurBBContend);
        
        string FnName;

        for (BasicBlock::iterator FI_iter = FcurBB->begin(); FI_iter != FcurBB->end(); ++FI_iter) 
        {
            Instruction *Inst = &*FI_iter;
            FI_iter->print(frso);
            Function *F = FcurBB->getParent();
            Fcur_bbl_info->Instructions.push_back(Inst);
            if(isa<BranchInst>(Inst) || isa<SwitchInst>(Inst) || isa<SelectInst>(Inst)) {
                Instruction *IC = NULL;
                SensitiveChecksPass FSCPass(FGlobalCtx, "SecurityCheck");
                if(FSCPass.IsSecurityCheck(F,Inst) || IsSecurityCheckStopExe(F,Inst)) {
                    (Fcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,scheck));
                   
                    sensitive_inst_in_funcf_type0++;
                    Value *Cond = NULL;
                    if(isa<BranchInst>(Inst)){
                        BranchInst *BIf = dyn_cast<BranchInst>(Inst);
                        Cond = BIf->getCondition();  
                    }
                    else if(isa<SwitchInst>(Inst)){
                        SwitchInst *SIf = dyn_cast<SwitchInst>(Inst);
                        Cond = SIf->getCondition(); 
                    }
                    else{
                        SelectInst *SIf = dyn_cast<SelectInst>(Inst);
                        Cond = SIf->getCondition();
                    }
                    if(Cond)
                        IC  = dyn_cast<ICmpInst>(Cond);    
                    sff->sen_list[sff->size].bbl_NO = FfromCountNum;
                    sff->sen_list[sff->size].type = scheck; 
                    if(IC != NULL)
                        sff->sen_list[sff->size++].inst = IC;
                    else
                        sff->sen_list[sff->size++].inst = Inst;  
              }
            }
            else if(isa<CallInst>(Inst)){
                CallInst *CI = dyn_cast<CallInst>(Inst);
                FnName = getCalledFuncName(CI);
                if(Is_element_in_stingvector((FGlobalCtx->LockFuncs), FnName)) {
                    (Fcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,ulock));
                    
                    sensitive_inst_in_funcf_type2++;
                    sff->sen_list[sff->size].bbl_NO = FfromCountNum;
                    sff->sen_list[sff->size].type = ulock;
                    sff->sen_list[sff->size++].inst = Inst;        
                }
                else if(Is_element_in_stingvector((FGlobalCtx->PairFuncs), FnName)){
                    (Fcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,pfunc));
                   
                    sensitive_inst_in_funcf_type3++;
                    sff->sen_list[sff->size].bbl_NO = FfromCountNum;
                    sff->sen_list[sff->size].type = pfunc;
                    sff->sen_list[sff->size++].inst = Inst;        
                } 
                else if((FGlobalCtx->InitFuncs).count(FnName)||(FGlobalCtx->CopyFuncs).count(FnName)|| FnName.find("init")!=string::npos|| FnName.find("INIT")!=string::npos){
                    (Fcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,uintial));
                   
                    sensitive_inst_in_funcf_type1++;
                    sff->sen_list[sff->size].bbl_NO = FfromCountNum;
                    sff->sen_list[sff->size].type = uintial;
                    sff->sen_list[sff->size++].inst = Inst;  
                } 
            }    
        }

      
        FcurBBContend = Filter(FcurBBContend);
        std::hash<std::string> FCurhasher;
        auto FcurBBhashed = FCurhasher(FcurBBContend);
        Fcur_bbl_info->BBhash = FcurBBhashed;
       
        FContend = FContend + FcurBBContend;
        int Fsucc_no = 0;  
        int FCursucc_no = 0; 
        for (BasicBlock *FSuccBB : successors(FcurBB))
            Fsucc_no = Fsucc_no +1;
        for (BasicBlock *FSuccBB : successors(FcurBB)){
            FCursucc_no = FCursucc_no +1; 
            if (basicBlockMap.find(FSuccBB) != basicBlockMap.end()){
                FtoCountNum = basicBlockMap[FSuccBB];   
            }
            else{
                FtoCountNum = FbbCount;
                basicBlockMap[FSuccBB] = FbbCount++;
            }
           
            AddChild(Fcur_bbl_info,FtoCountNum);
            // Obtain the hash of SuccBB
            std::string FSuccBBContend = "";
            llvm::raw_string_ostream FSuccrso(FSuccBBContend);
            std::hash<std::string> FSucchasher;
            for (BasicBlock::iterator FJ_iter = FSuccBB->begin(); FJ_iter != FSuccBB->end(); ++FJ_iter) 
                FJ_iter->print(FSuccrso);

           
            FSuccBBContend = Filter(FSuccBBContend);
            auto FSuccBBhashed = FSucchasher(FSuccBBContend);
           

            boost::put(Fvname_map_simple, FfromCountNum, to_string(FcurBBhashed));
            boost::put(Fvname_map_simple, FtoCountNum, to_string(FSuccBBhashed));
            
            Edge  edgef;
            bool insertedf;
            if(Fsucc_no==1){
                tie(edgef, insertedf) = add_edge(FfromCountNum, FtoCountNum, cfgF);  Fedge_name[edgef] = "F";
            }
            else if(Fsucc_no==2) {
                if(FCursucc_no==1){
                    tie(edgef, insertedf) = add_edge(FfromCountNum, FtoCountNum, cfgF);  Fedge_name[edgef] = "Y"; 
                }
                else{
                    tie(edgef, insertedf) = add_edge(FfromCountNum, FtoCountNum, cfgF);  Fedge_name[edgef] = "N";
                }
            }
            else
                tie(edgef, insertedf) = add_edge(FfromCountNum, FtoCountNum, cfgF);  Fedge_name[edgef] = "S";   
        }
        FbasicBlockInfo[FfromCountNum] = Fcur_bbl_info;  
    }

    string FIRMAPPath = DeleteFileExt(MKName,".bc");
    
    sensitive_inst_in_funck = sensitive_inst_in_funck_type1+sensitive_inst_in_funck_type2+sensitive_inst_in_funck_type3+sensitive_inst_in_funck_type0;
    sensitive_inst_in_funcf = sensitive_inst_in_funcf_type1+sensitive_inst_in_funcf_type2+sensitive_inst_in_funcf_type3+sensitive_inst_in_funcf_type0;
  
    if(sensitive_inst_in_funck_type1 > sensitive_inst_in_funcf_type1||
       sensitive_inst_in_funck_type2 > sensitive_inst_in_funcf_type2||
       sensitive_inst_in_funck_type3 > sensitive_inst_in_funcf_type3||
       sensitive_inst_in_funck_type0 > sensitive_inst_in_funcf_type0){
            potencial_delete_security_operation++;         
       }
        
    auto Fhashed = Fhasher(FContend);  
   
    if(Fhashed != Khashed)
    {
       
        NotIdenticalFunc++;
        int NodeNoK =0;
        int NodeNoF =0;
        int edgeNoK =0;
        int edgeNoF =0;
        #ifdef TEST_GM 
        std::pair<vertex_iter, vertex_iter> kvp;
        for (kvp = vertices(cfgK); kvp.first != kvp.second; ++kvp.first) 
        {
            Vertex kv = *kvp.first;
            NodeNoK ++;
        }
        boost::graph_traits< Graph >::edge_iterator eik, ei_endk;
        for (boost::tie(eik, ei_endk) = edges(cfgK); eik != ei_endk; ++eik)
            edgeNoK++;

        print_graph(cfgF);
        std::pair<vertex_iter, vertex_iter> fvp;
      
        for (fvp = vertices(cfgF); fvp.first != fvp.second; ++fvp.first) 
        {
            Vertex fv = *fvp.first;
            NodeNoF ++;
        }
        boost::graph_traits< Graph >::edge_iterator eif, ei_endf;
        for (boost::tie(eif, ei_endf) = edges(cfgF); eif != ei_endf; ++eif)
            edgeNoF++;
        #endif

        
        FindParent_sibling(KbasicBlockInfo);
        FindParent_sibling(FbasicBlockInfo);
        
        
        
        mcgregor_common_subgraphs_maximum_unique
               (cfgK,
                cfgF,
                Kvname_index_simple,
                Fvname_index_simple,
                make_property_map_equivalent(Kedge_name, Fedge_name),
                make_property_map_equivalent(Kvname_map_simple, Fvname_map_simple),
                false,
                user_callback);
    }
    
}

std::pair<int, double> CompareCFG_GM_cmp(Function *F, Function *K, string MKName, GlobalContext *KGlobalCtx, GlobalContext *FGlobalCtx)
{  
    // record basic block ID and the first instruction to map with IR
    std::map<int, Instruction*> KFIRMAP, FFIRMAP;
    int sameGraph = 1;
    char* local_msg = (char*)calloc(BUFFERSIZE , sizeof(unsigned char));  
    if(local_msg==NULL)
        OP<<"ERROR calloc.\n";

    clock_t totalstartTime, totalendTime;
    
    Sensitive_Info_of_Functions *sfk, *sff;  
    sfk=new(Sensitive_Info_of_Functions);
    sff=new(Sensitive_Info_of_Functions);
    if(!sfk || !sff)
        OP<<"Malloc Sensitive_Info_of_Functions Error!\n";
    sfk->F = K;
    sff->F = F;
    sfk->size = 0;
    sff->size = 0;
    string FuncFName = F->getName();
    Graph cfgK(K->size()), cfgF(F->size()), MSC;
    Mapbbl KbasicBlockInfo,  FbasicBlockInfo;

    User_callback<Graph,Graph,string,string, Mapbbl, Mapbbl, struct GlobalContext*, struct GlobalContext*, char*, pthread_mutex_t*> user_callback 
    (cfgK,cfgF,MKName,FuncFName,KbasicBlockInfo,FbasicBlockInfo,KGlobalCtx, FGlobalCtx, local_msg);
    std::vector<string> VetexK, VetexF;

    VertexNameMap Kvname_map_simple = get(vertex_name, cfgK);
    VertexIndexMap  Kvname_index_simple = get(vertex_index,cfgK);
    EdgeNameMap Kedge_name = get(edge_name, cfgK);

    VertexNameMap Fvname_map_simple = get(vertex_name, cfgF);
    VertexIndexMap  Fvname_index_simple = get(vertex_index,cfgF);
    EdgeNameMap Fedge_name = get(edge_name, cfgF);

    std::error_code error;
    std::map<BasicBlock*, int> basicBlockMap;
    
    int FbbCount = 0,  KbbCount = 0;    
    string FContend = "",  KContend = "";
    std::hash<std::string> Fhasher, Khasher;
    
    int sensitive_inst_in_funck = 0;
    int sensitive_inst_in_funck_type0 = 0;
    int sensitive_inst_in_funck_type1 = 0;
    int sensitive_inst_in_funck_type2 = 0;
    int sensitive_inst_in_funck_type3 = 0;
    
    // Obtain CFG of function K, tranverse basic blocks of K
    for (Function::iterator KB_iter = K->begin(); KB_iter != K->end(); ++KB_iter){
        // Obtain the current basic block.
        BasicBlock *KcurBB = &*KB_iter;
        // store the info of basic block, including parent sibling and children list, sensitive operations;
        bbl_info  Kcur_bbl_info= InitBBL();
        Kcur_bbl_info->bbl = KcurBB;
        // We define BBContend to record IR within a basic block and get the Hash of BBContend to determine if BB is identical.  
        std::string name = KcurBB->getName().str();
        int KfromCountNum;
        int KtoCountNum;
        if (basicBlockMap.find(KcurBB) != basicBlockMap.end()){
            KfromCountNum = basicBlockMap[KcurBB];
        }
        else{
            KfromCountNum = KbbCount;
            basicBlockMap[KcurBB] = KbbCount++;
        }
       
        // Obtain the hash of curBB
        Kcur_bbl_info->BBLID = KfromCountNum;
       
        
        Instruction *KFirstInst = FindFirstValidateInst(KcurBB);  
        KFIRMAP.insert(make_pair(KfromCountNum, KFirstInst));

        std::string KcurBBContend = "";
        llvm::raw_string_ostream krso(KcurBBContend);
        
        std:string split = ";";
        bool sensitive = false;
        string  FnName;

        for (BasicBlock::iterator KI_iter = KcurBB->begin(); KI_iter != KcurBB->end(); ++KI_iter) {
            KI_iter->print(krso); 
            Instruction *Inst = &*KI_iter;
            Function *K = KcurBB->getParent();
            Kcur_bbl_info->Instructions.push_back(Inst);
            if(isa<BranchInst>(Inst) || isa<SwitchInst>(Inst) || isa<SelectInst>(Inst)) {
               
                Instruction *IC = NULL;
                SensitiveChecksPass KSCPass(KGlobalCtx, "SecurityCheck");
                if(KSCPass.IsSecurityCheck(K,Inst) || IsSecurityCheckStopExe(K,Inst)) {
                    sensitive_inst_in_funck_type0++;
                    (Kcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,scheck));
                    Value *Cond = NULL;
                    if(isa<BranchInst>(Inst)){
                        BranchInst *BIk = dyn_cast<BranchInst>(Inst);
                        Cond = BIk->getCondition();
                    }
                    else if(isa<SwitchInst>(Inst)){
                        SwitchInst *SIk = dyn_cast<SwitchInst>(Inst);
                        Cond = SIk->getCondition(); 
                    }
                    else{
                        SelectInst *SIk = dyn_cast<SelectInst>(Inst);
                        Cond = SIk->getCondition();
                    }
                    if(Cond) 
                        IC  = dyn_cast<ICmpInst>(Cond); 
                    sfk->sen_list[sfk->size].bbl_NO = KfromCountNum;
                    sfk->sen_list[sfk->size].type = scheck;
                    if(IC !=NULL)
                        sfk->sen_list[sfk->size++].inst = IC;
                    else
                        sfk->sen_list[sfk->size++].inst = Inst;   
              }
            }
            else if(isa<CallInst>(Inst)){
                CallInst *CI = dyn_cast<CallInst>(Inst);
                FnName = getCalledFuncName(CI);
               
                if(Is_element_in_stingvector((KGlobalCtx->LockFuncs), FnName)) {
                    (Kcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,ulock));
                   
                    sensitive_inst_in_funck_type2++;
                    sfk->sen_list[sfk->size].bbl_NO = KfromCountNum;
                    sfk->sen_list[sfk->size].type = ulock;
                    sfk->sen_list[sfk->size++].inst = Inst;        
                }
               
                else if(Is_element_in_stingvector((KGlobalCtx->PairFuncs), FnName)){
                    (Kcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,pfunc));
                   
                    sensitive_inst_in_funck_type3++;
                    sfk->sen_list[sfk->size].bbl_NO = KfromCountNum;
                    sfk->sen_list[sfk->size].type = pfunc;
                    sfk->sen_list[sfk->size++].inst = Inst;        
                } 
               
                else if((KGlobalCtx->InitFuncs).count(FnName)||(KGlobalCtx->CopyFuncs).count(FnName)|| FnName.find("init")!=string::npos|| FnName.find("INIT")!=string::npos){
                    (Kcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,uintial));
                   
                    sensitive_inst_in_funck_type1++;
                    sfk->sen_list[sfk->size].bbl_NO = KfromCountNum;
                    sfk->sen_list[sfk->size].type = uintial;
                    sfk->sen_list[sfk->size++].inst = Inst;        
                }    
            }
        }
        
      
        KcurBBContend = Filter(KcurBBContend);
        std::hash<std::string> KCurhasher;
        auto KcurBBhashed = KCurhasher(KcurBBContend);
        Kcur_bbl_info->BBhash = KcurBBhashed;
       
        KContend = KContend + KcurBBContend;
        int Ksucc_no = 0; 
        int KCursucc_no = 0; 
        for (succ_iterator PI = succ_begin(KcurBB), E = succ_end(KcurBB); PI != E; ++PI) 
            Ksucc_no = Ksucc_no +1;
        for (succ_iterator PI = succ_begin(KcurBB), E = succ_end(KcurBB); PI != E; ++PI){
            BasicBlock *KSuccBB = *PI;
            KCursucc_no = KCursucc_no +1;
            if (basicBlockMap.find(KSuccBB) != basicBlockMap.end()){
                KtoCountNum = basicBlockMap[KSuccBB];   
            }
            else{
                KtoCountNum = KbbCount;
                basicBlockMap[KSuccBB] = KbbCount++;
            }
           
            AddChild(Kcur_bbl_info, KtoCountNum);
            // Obtain the hash of SuccBB
            std::string KSuccBBContend = "";
            llvm::raw_string_ostream KSuccrso(KSuccBBContend);
            std::hash<std::string> KSucchasher;
            for (BasicBlock::iterator KJ_iter = KSuccBB->begin(); KJ_iter != KSuccBB->end(); ++KJ_iter) 
                    KJ_iter->print(KSuccrso);

           
            KSuccBBContend = Filter(KSuccBBContend);
            auto KSuccBBhashed = KSucchasher(KSuccBBContend);
           

            boost::put(Kvname_map_simple, KfromCountNum, to_string(KcurBBhashed));
            boost::put(Kvname_map_simple, KtoCountNum, to_string(KSuccBBhashed));
            
            Edge  edgek;
            bool insertedk;
            if(Ksucc_no==1){
                    tie(edgek, insertedk) = add_edge(KfromCountNum, KtoCountNum, cfgK);  Kedge_name[edgek] = "F"; 
                }
            else if(Ksucc_no==2) {
                if(KCursucc_no==1){
                        tie(edgek, insertedk) = add_edge(KfromCountNum, KtoCountNum, cfgK);  Kedge_name[edgek] = "Y"; 
                    }
                else{
                        tie(edgek, insertedk) = add_edge(KfromCountNum, KtoCountNum, cfgK);  Kedge_name[edgek] = "N";
                }
            }
            else{
                tie(edgek, insertedk) = add_edge(KfromCountNum, KtoCountNum, cfgK);  Kedge_name[edgek] = "S"; 
            }   
        }
       KbasicBlockInfo[KfromCountNum] = Kcur_bbl_info;
       
    }
    
    string KIRMAPPath = DeleteFileExt(MKName,".bc");
   
    auto Khashed = Khasher(KContend); 

    int sensitive_inst_in_funcf = 0;
    int sensitive_inst_in_funcf_type0 = 0;
    int sensitive_inst_in_funcf_type1 = 0;
    int sensitive_inst_in_funcf_type2 = 0;
    int sensitive_inst_in_funcf_type3 = 0;
    
    for (Function::iterator FB_iter = F->begin(); FB_iter != F->end(); ++FB_iter){
        // Obtain the current basic block.
        BasicBlock* FcurBB = &*FB_iter;
        bbl_info Fcur_bbl_info= InitBBL();
        Fcur_bbl_info->bbl = FcurBB;
        // We define BBContend to record IR within a basic block and get the Hash of BBContend to determine if BB is identical.  
        //std::string name = FcurBB->getName().str();
        int FfromCountNum;
        int FtoCountNum;
        if (basicBlockMap.find(FcurBB) != basicBlockMap.end())
        {
            FfromCountNum = basicBlockMap[FcurBB];
        }
        else
        {
            FfromCountNum = FbbCount;
            basicBlockMap[FcurBB] = FbbCount++;
        }
       
        // Obtain the hash of curBB
        Fcur_bbl_info->BBLID = FfromCountNum;

        Instruction *FFirstInst =FindFirstValidateInst(FcurBB);
        FFIRMAP.insert(make_pair(FfromCountNum, FFirstInst));

        std::string FcurBBContend = "";
        llvm::raw_string_ostream frso(FcurBBContend);
        
        string FnName;
       
        for (BasicBlock::iterator FI_iter = FcurBB->begin(); FI_iter != FcurBB->end(); ++FI_iter) 
        {
            Instruction *Inst = &*FI_iter;
            FI_iter->print(frso);
            Function *F = FcurBB->getParent();
            Fcur_bbl_info->Instructions.push_back(Inst);
            if(isa<BranchInst>(Inst) || isa<SwitchInst>(Inst) || isa<SelectInst>(Inst)) {
               
                Instruction *IC = NULL;
                SensitiveChecksPass FSCPass(FGlobalCtx, "SecurityCheck");
                if(FSCPass.IsSecurityCheck(F,Inst) || IsSecurityCheckStopExe(F,Inst)) {
                    (Fcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,scheck));
                   
                    sensitive_inst_in_funcf_type0++;
                    Value *Cond = NULL;
                    if(isa<BranchInst>(Inst)){
                        BranchInst *BIf = dyn_cast<BranchInst>(Inst);
                        Cond = BIf->getCondition();  
                    }
                    else if(isa<SwitchInst>(Inst)){
                        SwitchInst *SIf = dyn_cast<SwitchInst>(Inst);
                        Cond = SIf->getCondition(); 
                    }
                    else{
                        SelectInst *SIf = dyn_cast<SelectInst>(Inst);
                        Cond = SIf->getCondition();
                    }
                    if(Cond)
                        IC  = dyn_cast<ICmpInst>(Cond);    
                    sff->sen_list[sff->size].bbl_NO = FfromCountNum;
                    sff->sen_list[sff->size].type = scheck; 
                    if(IC != NULL)
                        sff->sen_list[sff->size++].inst = IC;
                    else
                        sff->sen_list[sff->size++].inst = Inst;  
              }
            }
            else if(isa<CallInst>(Inst)){
                CallInst *CI = dyn_cast<CallInst>(Inst);
                FnName = getCalledFuncName(CI);
                if(Is_element_in_stingvector((FGlobalCtx->LockFuncs), FnName)) {
                    (Fcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,ulock));
                   
                    sensitive_inst_in_funcf_type2++;
                    sff->sen_list[sff->size].bbl_NO = FfromCountNum;
                    sff->sen_list[sff->size].type = ulock;
                    sff->sen_list[sff->size++].inst = Inst;        
                }
                else if(Is_element_in_stingvector((FGlobalCtx->PairFuncs), FnName)){
                    (Fcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,pfunc));
                   
                    sensitive_inst_in_funcf_type3++;
                    sff->sen_list[sff->size].bbl_NO = FfromCountNum;
                    sff->sen_list[sff->size].type = pfunc;
                    sff->sen_list[sff->size++].inst = Inst;        
                } 
                else if((FGlobalCtx->InitFuncs).count(FnName)||(FGlobalCtx->CopyFuncs).count(FnName)|| FnName.find("init")!=string::npos|| FnName.find("INIT")!=string::npos){
                    (Fcur_bbl_info->Sensitive_Info).insert(make_pair(Inst,uintial));
                   
                    sensitive_inst_in_funcf_type1++;
                    sff->sen_list[sff->size].bbl_NO = FfromCountNum;
                    sff->sen_list[sff->size].type = uintial;
                    sff->sen_list[sff->size++].inst = Inst;  
                } 
            }    
        }

       
        FcurBBContend = Filter(FcurBBContend);
        std::hash<std::string> FCurhasher;
        auto FcurBBhashed = FCurhasher(FcurBBContend);
        Fcur_bbl_info->BBhash = FcurBBhashed;
       
        FContend = FContend + FcurBBContend;
        int Fsucc_no = 0;  
        int FCursucc_no = 0; 
        for (BasicBlock *FSuccBB : successors(FcurBB))
            Fsucc_no = Fsucc_no +1;
        for (BasicBlock *FSuccBB : successors(FcurBB)){
            FCursucc_no = FCursucc_no +1; 
            if (basicBlockMap.find(FSuccBB) != basicBlockMap.end()){
                FtoCountNum = basicBlockMap[FSuccBB];   
            }
            else{
                FtoCountNum = FbbCount;
                basicBlockMap[FSuccBB] = FbbCount++;
            }
           
            AddChild(Fcur_bbl_info,FtoCountNum);
            
            std::string FSuccBBContend = "";
            llvm::raw_string_ostream FSuccrso(FSuccBBContend);
            std::hash<std::string> FSucchasher;
            for (BasicBlock::iterator FJ_iter = FSuccBB->begin(); FJ_iter != FSuccBB->end(); ++FJ_iter) 
                FJ_iter->print(FSuccrso);

           
            FSuccBBContend = Filter(FSuccBBContend);
            auto FSuccBBhashed = FSucchasher(FSuccBBContend);
           

            boost::put(Fvname_map_simple, FfromCountNum, to_string(FcurBBhashed));
            boost::put(Fvname_map_simple, FtoCountNum, to_string(FSuccBBhashed));
           
            Edge  edgef;
            bool insertedf;
            if(Fsucc_no==1){
                tie(edgef, insertedf) = add_edge(FfromCountNum, FtoCountNum, cfgF);  Fedge_name[edgef] = "F";
            }
            else if(Fsucc_no==2) {
                if(FCursucc_no==1){
                    tie(edgef, insertedf) = add_edge(FfromCountNum, FtoCountNum, cfgF);  Fedge_name[edgef] = "Y"; 
                }
                else{
                    tie(edgef, insertedf) = add_edge(FfromCountNum, FtoCountNum, cfgF);  Fedge_name[edgef] = "N";
                }
            }
            else
                tie(edgef, insertedf) = add_edge(FfromCountNum, FtoCountNum, cfgF);  Fedge_name[edgef] = "S";   
        }
        FbasicBlockInfo[FfromCountNum] = Fcur_bbl_info;  
    }

    string FIRMAPPath = DeleteFileExt(MKName,".bc");
   
    
    sensitive_inst_in_funck = sensitive_inst_in_funck_type1+sensitive_inst_in_funck_type2+sensitive_inst_in_funck_type3+sensitive_inst_in_funck_type0;
    sensitive_inst_in_funcf = sensitive_inst_in_funcf_type1+sensitive_inst_in_funcf_type2+sensitive_inst_in_funcf_type3+sensitive_inst_in_funcf_type0;
  
    if(sensitive_inst_in_funck_type1 > sensitive_inst_in_funcf_type1||
       sensitive_inst_in_funck_type2 > sensitive_inst_in_funcf_type2||
       sensitive_inst_in_funck_type3 > sensitive_inst_in_funcf_type3||
       sensitive_inst_in_funck_type0 > sensitive_inst_in_funcf_type0){
            potencial_delete_security_operation++;     
       }
        
    auto Fhashed = Fhasher(FContend);  
    
    if(Fhashed != Khashed)
        sameGraph = 0;
    
    
    NotIdenticalFunc++;
    int NodeNoK =0;
    int NodeNoF =0;
    int edgeNoK =0;
    int edgeNoF =0;
    #ifdef TEST_GM 
    std::pair<vertex_iter, vertex_iter> kvp;
    for (kvp = vertices(cfgK); kvp.first != kvp.second; ++kvp.first) 
    {
        Vertex kv = *kvp.first;
        NodeNoK ++;
    }
    boost::graph_traits< Graph >::edge_iterator eik, ei_endk;
    for (boost::tie(eik, ei_endk) = edges(cfgK); eik != ei_endk; ++eik)
        edgeNoK++;

    print_graph(cfgF);
    std::pair<vertex_iter, vertex_iter> fvp;
    for (fvp = vertices(cfgF); fvp.first != fvp.second; ++fvp.first) 
    {
        Vertex fv = *fvp.first;
        NodeNoF ++;
    }
    boost::graph_traits< Graph >::edge_iterator eif, ei_endf;
    for (boost::tie(eif, ei_endf) = edges(cfgF); eif != ei_endf; ++eif)
        edgeNoF++;
    #endif

    
    FindParent_sibling(KbasicBlockInfo);
    FindParent_sibling(FbasicBlockInfo);
   
    totalstartTime = clock();
    mcgregor_common_subgraphs_maximum_unique
            (cfgK,
            cfgF,
            Kvname_index_simple,
            Fvname_index_simple,
            make_property_map_equivalent(Kedge_name, Fedge_name),
            make_property_map_equivalent(Kvname_map_simple, Fvname_map_simple),
            false,
            user_callback);
    
    totalendTime = clock();


    double analyeTime = (double)(totalendTime - totalstartTime) / CLOCKS_PER_SEC ;
    
    return make_pair(sameGraph, analyeTime);
}

Instruction* ObtainConds(Instruction *Inst){
    Value *Cond = NULL;
    Instruction *IC = NULL;
    if(isa<BranchInst>(Inst)){
        BranchInst *BI = dyn_cast<BranchInst>(Inst);
        Cond = BI->getCondition();
       
    }
    else if(isa<SwitchInst>(Inst)){
        SwitchInst *SI = dyn_cast<SwitchInst>(Inst);
        Cond = SI->getCondition(); 
    }
    else{
        SelectInst *SI = dyn_cast<SelectInst>(Inst);
        Cond = SI->getCondition();
    }
    if(isa<ICmpInst>(Cond))
        IC  = dyn_cast<ICmpInst>(Cond); 
    else 
        IC = dyn_cast<Instruction>(Cond);
    
    return IC;
}

unsigned getICmpCode(const ICmpInst *ICI, bool InvertPred) 
{
   ICmpInst::Predicate Pred = InvertPred ? ICI->getInversePredicate()
                                     : ICI->getPredicate();
   switch (Pred) {
       // False -> 0
     case ICmpInst::ICMP_UGT: return 1;  // 001
     case ICmpInst::ICMP_SGT: return 1;  // 001
     case ICmpInst::ICMP_EQ:  return 2;  // 010
     case ICmpInst::ICMP_UGE: return 3;  // 011
     case ICmpInst::ICMP_SGE: return 3;  // 011
     case ICmpInst::ICMP_ULT: return 4;  // 100
     case ICmpInst::ICMP_SLT: return 4;  // 100
     case ICmpInst::ICMP_NE:  return 5;  // 101
     case ICmpInst::ICMP_ULE: return 6;  // 110
     case ICmpInst::ICMP_SLE: return 6;  // 110
       // True -> 7
     default:
       llvm_unreachable("Invalid ICmp predicate!");
   }
 }
 


Instruction* ObtainSplitInst(BasicBlock *FcurBB, Instruction *IC, std::vector<Value*> *fargs){
    // trace the value in ICMP inst till a store Inst or function parameters.
    string contend = getInstContent(IC);
    for(BasicBlock::iterator iter = FcurBB->end(); iter!= FcurBB->begin(); iter--){
        if(&*iter == IC){
            while(iter != FcurBB->begin()){
                iter --;
                Instruction *instr = &*iter;
                int NumOperands = instr->getNumOperands();
                // if one of the papameter is a function parameter, then stop.
                for(int count = 0; count < NumOperands; count++){
                    Value *operand = instr->getOperand(count); 
                    if(!IsValideOperand(operand))
                        continue;
                    if(isa<GlobalVariable>(operand)){
                        return &*iter;
                    }
                    if((find(fargs->begin(), fargs->end(), operand) != fargs->end())){
                        return &*iter;
                    }
                }   
                if(isa<StoreInst>(instr)){
                   
                   return &*--iter;
                }
                
            }
            return  NULL;
        }
    }
    return  NULL;
}


void rewritting(Function *F, GlobalContext *GlobalCtx){
    if (F->isDeclaration())
        return;
    // Obtain the arguments list of a function
    std::vector<Value*> fargs;
    for (Function::arg_iterator iters = F->arg_begin(), itere = F->arg_end();
                             iters != itere; ++iters){
           
            fargs.push_back(&*iters);
        }
    
    for (Function::iterator FB_iter = F->begin(); FB_iter != F->end(); ++FB_iter){
      BasicBlock *FcurBB = &*FB_iter;
    
      // We find the propogragation of function parameters
      for(BasicBlock::iterator iter = FcurBB->begin(); iter!= FcurBB->end(); iter++){
            Instruction *instr = &*iter;
            if( isa<StoreInst>(instr) && (find(fargs.begin(), fargs.end(),  instr->getOperand(0)) != fargs.end())){
                fargs.push_back(instr->getOperand(1));
            }
            else if(isa<LoadInst>(instr) && (find(fargs.begin(), fargs.end(),  instr->getOperand(0)) != fargs.end())){
                fargs.push_back(instr);
                
            }
            else if(isa<GetElementPtrInst>(instr) && (find(fargs.begin(), fargs.end(),  instr->getOperand(0)) != fargs.end())){
                fargs.push_back(instr);
                
            }
            else if(isa<AllocaInst>(instr) && (find(fargs.begin(), fargs.end(),  instr) == fargs.end())){
                fargs.push_back(instr);
                
            }
      }

      if(FcurBB->size()>splitSize)
      {
       
        Instruction *LastInst = &*(--FcurBB->end());
        if (isa<BranchInst>(LastInst) || isa<SwitchInst>(LastInst) || isa<SelectInst>(LastInst)){
            Value *Cond = NULL;
            Instruction *IC = NULL;
            BranchInst *BI = dyn_cast<BranchInst>(LastInst);
            SwitchInst *SI = dyn_cast<SwitchInst>(LastInst);;
            SelectInst *SIK = dyn_cast<SelectInst>(LastInst);
            if (BI) {
                if (BI->getNumSuccessors() < 2)
                    continue;
                Cond = BI->getCondition();  
            } 
            else if(SI){
                if (SI->getNumSuccessors() < 2)
                    continue;
                Cond = SI->getCondition(); 
            }
            else if(SIK) {
                if (SIK->getNumSuccessors() < 2)
                    continue;    
                Cond = SIK->getCondition();
            }
            if(Cond){
                IC  = dyn_cast<ICmpInst>(Cond); 
                if(IC){
                   
                    Instruction *splitInst = ObtainSplitInst(FcurBB, IC, &fargs);
                    if(splitInst){
                       
                        FcurBB->splitBasicBlock(splitInst);
                        ++FB_iter;
                    }
                }
                 else{
                     IC  = dyn_cast<Instruction>(Cond);
                     if(IC){
                         Instruction *splitInst = ObtainSplitInst(FcurBB, IC, &fargs);
                         if(splitInst){
                             FcurBB->splitBasicBlock(splitInst);
                             ++FB_iter;
                         }
                     }
                 }
            }
        }
      }
    }
}


void unrollLoops_old(Function *F) {
    // Return true if the primary definition of this global value is outside of the current translation unit.
    if (F->isDeclaration())
        return;

    DominatorTree DT = DominatorTree();
    // Compute a dominator tree for the given function.
    DT.recalculate(*F);
    // LoopInfo class is used to identify natural loops.
    LoopInfo *LI = new LoopInfo();
    LI->releaseMemory();
    LI->analyze(DT);

    // Collect all loops in the function
    set<Loop *> LPSet;
    for (LoopInfo::iterator i = LI->begin(), e = LI->end(); i!=e; ++i) {

        Loop *LP = *i;
        LPSet.insert(LP);

        list<Loop *> LPL;

        LPL.push_back(LP);
        while (!LPL.empty()) {
            LP = LPL.front();
            LPL.pop_front();
            vector<Loop *> SubLPs = LP->getSubLoops();
            for (auto SubLP : SubLPs) {
                LPSet.insert(SubLP);
                LPL.push_back(SubLP);
            }
        }
    }

   
    for (Loop *LP : LPSet) {

        
        BasicBlock *HeaderB = LP->getHeader();
       

        unsigned NumBE = LP->getNumBackEdges();

        SmallVector<BasicBlock *, 4> LatchBS;
       
        LP->getLoopLatches(LatchBS);

        for (BasicBlock *LatchB : LatchBS) {
            if (!HeaderB || !LatchB) {
                OP<<"ERROR: Cannot find Header Block or Latch Block\n";
                continue;
            }
       
            Instruction *TI = LatchB->getTerminator();

            if (LatchB->getSingleSuccessor() != NULL) {
                int Numdominate = 0;
                
                for (succ_iterator sit = succ_begin(HeaderB); 
                        sit != succ_end(HeaderB); ++sit) {  

                    BasicBlock *SuccB = *sit;
                    
                    BasicBlockEdge BBE = BasicBlockEdge(HeaderB, SuccB);
                  
                    if (DT.dominates(BBE, LatchB)){
                        continue;
                    }
                    else {
                        Numdominate++;
                        TI->setSuccessor(0, SuccB);
                    }
                }   
                if(Numdominate!=1){ 
                    TI->setSuccessor(0, LatchB);
                }
            }
            else {
                for (int i = 0; i < TI->getNumSuccessors(); ++i) {

                    BasicBlock *SuccB = TI->getSuccessor(i);

                    if (SuccB == HeaderB){
                        BasicBlock* targetbb;
                        if(i!=0)
                            targetbb=TI->getSuccessor(0);
                        else
                            targetbb=TI->getSuccessor(1);

                        TI->setSuccessor(i, targetbb);
                        continue;
                    }
                    else{
                        /*  
                        TI->setSuccessor(0, SuccB);
                        //TI->setSuccessor(1, SuccB);//Add here
                        */
                    }

                }   
            }
        }
    }
}


void unrollLoops_l(Function *F) {

 if (F->isDeclaration())
  return;

 DominatorTree DT = DominatorTree();
 DT.recalculate(*F);
 LoopInfo *LI = new LoopInfo();
 LI->releaseMemory();
 LI->analyze(DT);

 // Collect all loops in the function
 set<Loop *> LPSet;
 for (LoopInfo::iterator i = LI->begin(), e = LI->end(); i!=e; ++i) {

  Loop *LP = *i;
  LPSet.insert(LP);

  list<Loop *> LPL;

  LPL.push_back(LP);
  while (!LPL.empty()) {
   LP = LPL.front();
   LPL.pop_front();
   vector<Loop *> SubLPs = LP->getSubLoops();
   for (auto SubLP : SubLPs) {
    LPSet.insert(SubLP);
    LPL.push_back(SubLP);
   }
  }
 }


 for (Loop *LP : LPSet) {

  BasicBlock *HeaderB = LP->getHeader();
  unsigned NumBE = LP->getNumBackEdges();
  SmallVector<BasicBlock *, 4> LatchBS;

  LP->getLoopLatches(LatchBS);

  for (BasicBlock *LatchB : LatchBS) {
   if (!HeaderB || !LatchB) {
    OP<<"ERROR: Cannot find Header Block or Latch Block\n";
    continue;
   }

   Instruction *TI = LatchB->getTerminator();

   if (LatchB->getSingleSuccessor() != NULL) {
    int Numdominate = 0;
    
    for (succ_iterator sit = succ_begin(HeaderB); 
      sit != succ_end(HeaderB); ++sit) {  

     BasicBlock *SuccB = *sit;
    
     BasicBlockEdge BBE = BasicBlockEdge(HeaderB, SuccB);
     if (DT.dominates(BBE, LatchB)){
      continue;
     }
     else {
      Numdominate++;
      TI->setSuccessor(0, SuccB);
     }
    }

    if(Numdominate!=1){
     TI->setSuccessor(0, LatchB);
    }
   }
   // Case 2:
   else {
    for (int i = 0; i < TI->getNumSuccessors(); ++i) {

     BasicBlock *SuccB = TI->getSuccessor(i);

     if (SuccB == HeaderB){
      BasicBlock* targetbb;
      if(i!=0)
       targetbb=TI->getSuccessor(0);
      else
       targetbb=TI->getSuccessor(1);
      Value *Cond = NULL;
      BranchInst *BI = dyn_cast<BranchInst>(TI);
      if(BI){
       if(BI->isConditional())
           Cond = BI->getCondition();
      }
      if(Cond){
       Constant *Ct = dyn_cast<Constant>(Cond);
       
       if(Ct && Ct->isOneValue() && targetbb != TI->getSuccessor(0)){
        continue;
       }
      }

      TI->setSuccessor(i, targetbb);
      continue;
     }
     else{
      /* 
      TI->setSuccessor(0, SuccB);
      //TI->setSuccessor(1, SuccB);//Add here
      */
     }

    } 
   }
  }

  Instruction *HeaderB_TI = HeaderB->getTerminator();
  map<BasicBlock *,int> HeaderB_Follow_BBs;
  HeaderB_Follow_BBs.clear();
  for(int i = 0; i < HeaderB_TI->getNumSuccessors(); ++i){
   BasicBlock *SuccB = HeaderB_TI->getSuccessor(i);
   if(SuccB == HeaderB)
    continue;

   HeaderB_Follow_BBs[SuccB] = i;
  }

  for (BasicBlock *LatchB : LatchBS) {
   if (!HeaderB || !LatchB) {
    OP<<"ERROR: Cannot find Header Block or Latch Block\n";
    continue;
   }
   
   Instruction *LatchB_TI = LatchB->getTerminator();
   for (int i = 0; i < LatchB_TI->getNumSuccessors(); ++i) {
    BasicBlock *SuccB = LatchB_TI->getSuccessor(i);
    if(HeaderB_Follow_BBs.count(SuccB) != 0 && SuccB!= LatchB){
     HeaderB_TI->setSuccessor( HeaderB_Follow_BBs[SuccB],HeaderB);
    }
   }

  }
 }
}
