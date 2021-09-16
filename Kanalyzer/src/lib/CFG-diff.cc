#include "boost/thread/thread.hpp"  
#include <boost/graph/adjacency_list.hpp>
#include <iostream>
#include <memory>
#include <algorithm>
#include <vector>
#include <sstream>
#include <exception>
#include <sys/resource.h>
#include "MCS.hpp"
#include "CFG-diff.h"
#include <stdlib.h>
#include <queue>
#include <stack>
#include <pthread.h>
#include "Analyzer.h"
#include "CallGraph.h"
#include "SensitiveCheck.h"
#include "Common.h"
#include <sys/signal.h>  

int    Tpye_Security_check = 0;
int    Tpye_lock = 0;
int    Tpye_missing_init = 0;
int    Tpye_missing_RR = 0;
int    Tpye_pair = 0;



bool Is_element_in_vector(std::vector<int> v,int element){
    std::vector<int>::iterator it;
    it=find(v.begin(),v.end(),element);
    if (it!=v.end()){
        return true;
    }
    else{
        return false;
    }
}

bool Is_element_in_vector(std::vector<string> v,string element){
    std::vector<string>::iterator it;
    it=find(v.begin(),v.end(),element);
    if (it!=v.end()){
        return true;
    }
    else{
        return false;
    }
}

bool Is_element_in_stingvector(multimap<std::string, std::string> PairsFuncs,string element){
    multimap<std::string, std::string>::iterator iter;
    for(iter = PairsFuncs.begin(); iter != PairsFuncs.end(); iter++) {
        if(iter->first==element || iter->second==element)
          return true;
    }
    return false;
}

string splitStr(const string& s, const string& delimiter) {
   size_t i = s.rfind(delimiter, s.length());
   if (i != string::npos) {
      return(s.substr(0, i));
   }
   return("");
}

float getMold(const vector<int>& vec){   
        int n = vec.size();
        float sum = 0.0;
        for (int i = 0; i<n; ++i)
            sum += vec[i] * vec[i];
        return sqrt(sum);
}


int dump_buffer(string logs, string file_to_dump){
    char *content = (char*)logs.c_str();
    FILE* fp;
    char *filename=(char*)file_to_dump.c_str();
    if ((fp = fopen(filename, "w")) == NULL){
      OP<<"failed to open file.\n";
      return -1;  
    } 
    fwrite( content, sizeof(unsigned char), strlen(content), fp);
    fclose(fp);
    return 0;
}


int dump_buffer(string logs, string file_to_dump, int mode){
    char *content = (char*)logs.c_str();
    FILE* fp;
    char *filename=(char*)file_to_dump.c_str();
    if(mode ==0){
    if ((fp = fopen(filename, "w")) == NULL){
      OP<<"failed to open file.\n";
      return -1;  
    } }
    else{
    if ((fp = fopen(filename, "a")) == NULL){
      OP<<"failed to open file.\n";
      return -1;  
    }
    }
    fwrite( content, sizeof(unsigned char), strlen(content), fp);
    fclose(fp);
    return 0;
}


int dump_buffer1(string logs, string file_to_dump){
    char *content = (char*)logs.c_str();
    FILE* fp;
    char *filename=(char*)file_to_dump.c_str();
    if ((fp = fopen(filename, "a+")) == NULL){
      OP<<"failed to open file.\n";
      return -1;  
    } 
    fwrite( content, sizeof(unsigned char), strlen(content), fp);
    fclose(fp);
    return 0;
}


float getSimilarity(const vector<int>& lhs, const vector<int>& rhs){
    int n = lhs.size();
    assert(n == rhs.size());
    float tmp = 0.0;  //内积
    for (int i = 0; i<n; ++i)
        tmp += lhs[i] * rhs[i];
    return tmp / (getMold(lhs)*getMold(rhs));
}


void DeleElem(vector<int> *v, int e){
  std::vector<int>::iterator iter=std::find(v->begin(),v->end(),e);
  if(iter!=v->end())
  v->erase(iter);
}

void DeleElem(vector<string> v, string e){
  std::vector<string>::iterator iter=std::find(v.begin(),v.end(),e);
  if(iter!=v.end())
  v.erase(iter);
}

Mapbbl convert_Mapbbl(Mapbbl m_KbasicBlockInfo){
    Mapbbl basicBlockInfo;
    Mapbbl::const_iterator iter(m_KbasicBlockInfo.begin());
    bbl_info b = NULL;
    while(iter != m_KbasicBlockInfo.end()) {
        basicBlockInfo[iter->first]=iter->second;
        iter++;
    }
    return basicBlockInfo;   
}

string ValuetoString(Value *V){
    std::string Str;
    raw_string_ostream convertTostr(Str);
    V->print(convertTostr);
    return Str;
}

 std::pair<Sensitive_Info_of_Functions*, std::set<int>> ObtainsensitiveBBLset(Mapbbl *basicBlockInfo, std::vector<int> common_node){
   
    Sensitive_Info_of_Functions *siof; 
    siof=new(Sensitive_Info_of_Functions);
    std::set<int> sscfg;
    siof->size = 0;
    Mapbbl::iterator iter(basicBlockInfo->begin());
    while(iter != basicBlockInfo->end()){
        int bblID = iter->first;
        bbl_info b = iter->second;
        siof->F = b->bbl->getParent();
        
        map<llvm::Instruction*, int> sensitive_info = b->Sensitive_Info;
       
        if(sensitive_info.size()>0 && !Is_element_in_vector(common_node, bblID) ){
          sscfg.insert(bblID);
          for(std::map<llvm::Instruction*, int>::iterator it = sensitive_info.begin(); 
              it != sensitive_info.end(); ++it){
            Instruction *Inst = it->first;
            int type = it->second;
            siof->sen_list[siof->size].bbl_NO = bblID;
            siof->sen_list[siof->size].type = type;
            siof->sen_list[siof->size++].inst = Inst;
          } 
        }
        iter++;
    }
    return make_pair(siof, sscfg);
}


bbl_info search_Mapbbl(Mapbbl m_KbasicBlockInfo, int common_vetex){
    Mapbbl::const_iterator iter(m_KbasicBlockInfo.begin());
    bbl_info b = NULL;
    while(iter != m_KbasicBlockInfo.end()) {
        if (iter->first == common_vetex){
          b=iter->second;
          break;
          }
        iter++;
    }
    return b;   
}


vector<int> ObtainParentList(bbl_info b){
  ParentNode p;
  vector<int> parentnodes;
  if(b !=NULL)
    p = b->parentnode;
  if(p!=NULL)
  {
      ParentNode p1 = p->Next; 
      while(p1){
          parentnodes.push_back(p1->Data);
          p1=p1->Next;
      }
  }
  return parentnodes;
}

vector<int> ObtainChildrenList(bbl_info b){
  vector<int> childrennodes;
  ChildrenNode c;
  if(b !=NULL)
   c = b->childrennode;
  
  if(c !=NULL )
  {
      ChildrenNode c1 = c->Next; 
      while(c1){
          childrennodes.push_back(c1->Data);
          c1=c1->Next;
      }
  }
  return childrennodes;
}


vector<int> ObtainSilbingList(bbl_info b){
  SilbingNode s;
  vector<int> silibingnodes;
  if(b !=NULL)
    s = b->silibingnode;
  if(s!=NULL)
  {
      SilbingNode s1 = s->Next; 
      while(s1){
          silibingnodes.push_back(s1->Data);
          s1=s1->Next;
      }
  }
  return silibingnodes;
}


std::map<int,int>  ObtainCandicateVetex(std::map<int,int> *relatedvetex , int type ){
  std::map<int,int> CandicateVetex;
  std::map<int,int>::iterator iter;
  for(iter=relatedvetex->begin(); iter!=relatedvetex->end(); iter++){
    if(iter->second==type)
        CandicateVetex[iter->first]=iter->second;
  }
  return CandicateVetex;
}


string DumpVectorI(vector<int> v){
  string content = "";
  for(std::vector<int>::iterator it = v.begin(); it != v.end(); ++it)
    content = content + " "+ getIntContent(*it);
  content = content + "\n ";
  return content;
}

string DumpVectorI(vector<string> v){
  string content = "";
  for(std::vector<string>::iterator it = v.begin(); it != v.end(); ++it)
    content = content + " "+ (*it);
  content = content + "\n ";
  return content;
}


string DumpVectorI(vector<Instruction*> v){
  string content = "";
  for(vector<Instruction*>::iterator it = v.begin(); it != v.end(); ++it){
    content = content + " "+ getInstContent(*it) + " + " + getIntContent(GetLocation(*it)) ;
  }
  return content;
}



string Dumpset(std::set<int> v){
  string content = "";
  for(std::set<int>::iterator it = v.begin(); it != v.end(); ++it)
    content = content + " "+ getIntContent(*it);
  content = content + "\n ";
  return content;
}


string DumpVectorI(int *Matrix, int row, int colmn ){
  int i, j; 
  string content = "\n";
  for(i = 0; i < row; i++) 
  { 
    for(j = 0; j < colmn; j++) 
      content = content + " " + getIntContent(*(Matrix + i * colmn + j));
    content = content + "\n";
  } 
  return content;
}



string Dumpstack(stack<string> record){
  string pattern = "";
  stack<string> record_tmp = record;
  while(!record_tmp.empty()) {
        pattern = pattern + record_tmp.top();
        record_tmp.pop();
      }
  return pattern;
}


string DumpUseSeq(mul_USESEQ useSeqk){
  string content = "";
  mul_USESEQ::iterator iter, beg, end;
  int count = 0;
  for(mul_USESEQ::iterator iterk = useSeqk.begin(), itere = useSeqk.end(); iterk != itere; iterk = useSeqk.upper_bound(iterk->first)){
    mul_key opk = iterk->first;
    beg = useSeqk.lower_bound(opk);
    end = useSeqk.upper_bound(opk);
    count++;
    if(count == 1)
      content = content + "{\n\"opk\": \"" + getInstContent(opk.first)+ Dumpstack(opk.second)+ "\",\n\"use\": \"";
    else
      content = content + ",{\n\"opk\": \"" + getInstContent(opk.first)+ Dumpstack(opk.second)+ "\",\n\"use\": \"";
    for(iter = beg; iter != end; iter++)
      content = content + DumpVectorI(iter->second) ;
    content = content + "\"}";
  }
  return content;
}


string DumpUseSeq(USESEQ useSeqk){
  string content = "";
  USESEQ::iterator iter, beg, end;
  int count = 0;
  for(USESEQ::iterator iterk = useSeqk.begin(), itere = useSeqk.end(); iterk != itere; iterk = useSeqk.upper_bound(iterk->first)){
    Value *opk = iterk->first;
    beg = useSeqk.lower_bound(opk);
    end = useSeqk.upper_bound(opk);
    count++;
    if( count == 1 )
    content = content + "{\n\"opk\": \"" + getValueContent(opk)+ " +" + getIntContent(GetLocation(opk))+ "\",\n\"use\": \"";
    else
    content = content + ",{\n\"opk\": \"" + getValueContent(opk) + " +" + getIntContent(GetLocation(opk))+ "\",\n\"use\": \"";
    for(iter = beg; iter != end; iter++)
      content = content +  getInstContent(iter->second) + " +" + getIntContent(GetLocation(iter->second));
    content = content + "\"}";
  }
  return content;
}

void PrintVectorI(vector<int> v){
  for(std::vector<int>::iterator it = v.begin(); it != v.end(); ++it)
    std::cout << *it<<" ";
  std::cout << "\n ";
}


void PrintVectorS(vector<string> v){
  for(std::vector<string>::iterator it = v.begin(); it != v.end(); ++it)
    std::cout <<*it<< " \n";
}
void PrintSet(set<int> s){
   for(std::set<int>::iterator it = s.begin(); it != s.end(); it++)
    std::cout << *it<< " ";
  std::cout << "\n ";
 }


string DumpSet(set<int> s){
  string content ="";
  for(std::set<int>::iterator it = s.begin(); it != s.end(); it++){
    //std::cout << *it<< " ";
    content = content + " "+ getIntContent(*it);
   }
  std::cout << "\n ";
  content = content + " \n";
  return content;
 }

void Printmap(map<llvm::Instruction*, int> v){
  int i = 0;
  for(std::map<llvm::Instruction*, int>::iterator it = v.begin(); it != v.end(); ++it){
    Instruction *Inst = it->first;
    i++;
    std::cout <<it->second<<"\n";
  } 
  std::cout << "\n ";
}

string Dumpmap(map<llvm::Instruction*, int> v){
  string content = "";
  int i = 0;
  for(std::map<llvm::Instruction*, int>::iterator it = v.begin(); it != v.end(); ++it){
    Instruction *Inst = it->first;
    content=content+"\n"+getInstContent(Inst) + " "+ getIntContent(it->second);
    i++;
    std::cout <<it->second<<"\n";
  } 
  std::cout << "\n ";
  return content;
}


string Dumpmap(std::map<int, std::vector<int>> K1FN){
  string content = "{";
  for(std::map<int, std::vector<int>>::iterator iter = K1FN.begin(); iter!=K1FN.end();iter++){
    content = content +"\nOne BBLID: " +getIntContent(iter->first) + "\n N BBLID:";
    for(std::vector<int>::iterator iter1  = iter->second.begin(); iter1!=iter->second.end(); iter1++)
      content = content + " "+ getIntContent(*iter1) +" ";
  }
  content = content +"}\n";
  return content;
}

void DumpDeletedBBInfo(string analysisfile, bbl_info b, string dumpfile){
  string content = "";
  BasicBlock *BB = b->bbl;
  for (BasicBlock::iterator KI_iter = BB->begin(); KI_iter != BB->end(); ++KI_iter) {
      Instruction *Inst = &*KI_iter;
      if(!Inst)
          continue;
      content = content +analysisfile + " +" + getIntContent(GetLocation(Inst)) + "\n";    
  }
  dump_buffer1(content,  dumpfile);
}


void PrinteDSO(map<llvm::Instruction*, int> v, Mapbbl KbasicBlockInfo){
  int i = 0;
  for(std::map<llvm::Instruction*, int>::iterator it = v.begin(); it != v.end(); ++it){
    Instruction *Inst = it->first;
    OP<<i<<" :"<<*Inst<<"   ";
    i++;
    BasicBlock *BB=Inst->getParent();
    for(auto Kb: KbasicBlockInfo){
      
      bbl_info b = Kb.second;
      BasicBlock *bbl = b->bbl;
      int bblID = b->BBLID;
      if(BB==bbl)
          OP<<"["<<bblID<<"]\n";
    }
  }
}

std::tuple<int,int,int,int,int>  TypeCount(map<llvm::Instruction*, int> v){
  int sc = 0;
  int ui = 0;
  int ul = 0;
  int up = 0;
  int resourcer = 0;
  for(std::map<llvm::Instruction*, int>::iterator it = v.begin(); it != v.end(); ++it){
    Instruction *Inst = it->first;
    int sstype = it->second;
    if(sstype == scheck)
      sc ++;
    else if(sstype == uintial)
      ui++;
    else if(sstype == ulock)
      ul++;
    else if(sstype == pfunc)
      up++;
    else if(sstype == resourcerelease)
      resourcer++;
  }
  return make_tuple(sc, ui, ul, up, resourcer);
}

void PrintmapII(std::map<int,int>  s){
  for(std::map<int,int>::iterator it = s.begin(); it != s.end(); it++)
    std::cout << it->first<< " ";
  std::cout << "\n ";
}

string DumpmapII(std::map<int,int>  s){
  string content = "";
  for(std::map<int,int>::iterator it = s.begin(); it != s.end(); it++){
    content = content + " " +getIntContent(it->first);
    std::cout << it->first<< " ";
  }
  std::cout << "\n ";
  content= content+"\n";
  return content;
}

string Dumpmap(std::map<Value*,Value*>  s){
  string content = "";
  for(std::map<Value*,Value*>::iterator it = s.begin(); it != s.end(); it++){
    content = content + "  opk: " +getValueContent(it->first) + " +"+getIntContent(GetLocation(it->first))+ " opf:"+ getValueContent(it->second)+ " +"+getIntContent(GetLocation(it->second));
  }
  return content;
}

string Dumpmap(std::map<mul_key, mul_key> s){
  string content = "";
  for(std::map<mul_key, mul_key> ::iterator it = s.begin(); it != s.end(); it++){
    content = content + "  opk: " +getValueContent((it->first).first) + " +"+getIntContent(GetLocation((it->first).first))+ " opf:"+ getValueContent((it->second).first)+ " +"+getIntContent(GetLocation((it->second).first));
  }
  return content;
}


void DeleSensitiveItem(map<llvm::Instruction*, int> *v, Instruction *I){
  map<llvm::Instruction*, int>::iterator key = v->find(I);
  if(key!=v->end())
    v->erase(key);
}


bool IdenticalShortInst(ShortInst e1, ShortInst e2){
  int opcode1 = e1.first;
  vector<string> instoperandsType1 = e1.second;
  int opcode2 = e2.first;
  vector<string> instoperandsType2 = e2.second;
  if(opcode1!=opcode2 || instoperandsType1.size()!= instoperandsType2.size())
    return false;
  else{
    for(int i = 0; i<instoperandsType1.size(); i++){
      if(instoperandsType1[i]!=instoperandsType2[i])
        return false;
    }
  }
  return true;
}


std::pair<int, vector<int>> Counters(vector<string> v, string e){
  int count=0;
  int p=0;
  vector<int> position;
  std::vector<string>::iterator iter;
  for(iter=v.begin();iter!=v.end();iter++){
    if(*iter == e){
        count ++;
        position.push_back(p);
    } 
    p++;
  }
  return make_pair(count, position);
}


double InstsequenceSimilarity(vector<string> KInstSequence,vector<string> FInstSequence){
  vector<string> LongerInstSequence, shorterInstSequence;
  int shorter = 0;
  double instsequencesimilarity = 0;
  int ksize = KInstSequence.size();
  int fsize = FInstSequence.size();
  if(ksize<=fsize){
    shorterInstSequence = KInstSequence;
    LongerInstSequence = FInstSequence;
    shorter = ksize;
  }
  else{
    shorterInstSequence = FInstSequence;
    LongerInstSequence = KInstSequence;
    shorter = fsize;
  }
  double dis =  editInstDistDPInstNew(LongerInstSequence, shorterInstSequence);
  instsequencesimilarity = 1-double(dis*1.0/shorter);
  return instsequencesimilarity; 
}

// Determine the similarity of sensitive instructions
double CompareInst(llvm::Instruction *Instk, llvm::Instruction *Instf){
  double similarity = 0;
  string Instypek = Instk->getOpcodeName();
  string Instypef = Instf->getOpcodeName();
  if(Instypek!=Instypef || Instk->getNumOperands()!=Instf->getNumOperands())
    return 0;
  else{
      ICmpInst *ICk =NULL;
      ICmpInst *ICf =NULL;

      if(isa<ICmpInst>(Instk) && isa<ICmpInst>(Instf)){
        ICk = dyn_cast<ICmpInst>(Instk);
        ICf = dyn_cast<ICmpInst>(Instf);
      }
      else if (isa<BranchInst>(Instk) || isa<SwitchInst>(Instk)|| isa<SelectInst>(Instk)) {
        Value *Condk = NULL;
        Value *Condf = NULL;
        OP<<"inst is branch inst\n";
        if(isa<BranchInst>(Instk)){
          BranchInst *BIk = dyn_cast<BranchInst>(Instk);
          BranchInst *BIf = dyn_cast<BranchInst>(Instf);
          if (BIk->getNumSuccessors() >1 && BIf->getNumSuccessors() > 1){
              Condf = BIf->getCondition();
              Condk = BIk->getCondition();
          }    
        }
        else if(isa<SwitchInst>(Instk)){
          SwitchInst *SIk = dyn_cast<SwitchInst>(Instk);
          SwitchInst *SIf = dyn_cast<SwitchInst>(Instf);
          if (SIk->getNumSuccessors() >1 && SIf->getNumSuccessors() > 1){
            Condf = SIf->getCondition(); 
            Condk = SIk->getCondition(); 
          }  
        }
        else{
          SelectInst *SIk = dyn_cast<SelectInst>(Instk);
          SelectInst *SIf = dyn_cast<SelectInst>(Instf) ;
          Condk = SIk->getCondition();
          Condf = SIf->getCondition();
        }
        if (Condk && Condf){
          ICk = dyn_cast<ICmpInst>(Condk);
          ICf = dyn_cast<ICmpInst>(Condf);
        } 
      }
      
      
      std::string kIContend = "";
      llvm::raw_string_ostream krso(kIContend);
      std::string fIContend = "";
      llvm::raw_string_ostream frso(fIContend);

      std::string koperand1 = "";
      llvm::raw_string_ostream koperandso1(koperand1);
      std::string foperand1 = "";
      llvm::raw_string_ostream foperandso1(foperand1);

      std::string koperand0 = "";
      llvm::raw_string_ostream koperandso0(koperand0);
      std::string foperand0 = "";
      llvm::raw_string_ostream foperandso0(foperand0);
      string contend = "\n***********************************************";
      if(ICk && ICf){ 
        double tmp = 0; 
        ICk->print(krso);
        ICf->print(frso);

        
        if(getICmpCode(ICk, 0)== getICmpCode(ICf, 0)){
          tmp++;
        }
      
      (ICk->getOperand(0)->getType())->print(koperandso0);
      (ICf->getOperand(0)->getType())->print(foperandso0);
      if( koperandso0.str() == (foperandso0.str())){
          tmp++;
          
        } 
        
        (ICk->getOperand(1)->getType())->print(koperandso1);
        (ICf->getOperand(1)->getType())->print(foperandso1);
        if( koperandso1.str() == (foperandso1.str()))
          tmp++;  
        similarity = (tmp+1)/4; 
      }
      else{
        Instk->print(krso); 
        Instf->print(frso);
        contend = contend + " \n kIContend:"+kIContend+ "\n fIContend: "+fIContend;

        double tmp = 0; 
        contend = contend +"\nBefore enter loop, tmp:" + getIntContent(tmp);
        contend = contend + " \n NumOperands:"+ getIntContent(Instk->getNumOperands())+"\n";
        for(int i=0;i<Instk->getNumOperands();i++){
          std::string koperand = "";
          llvm::raw_string_ostream koperandso(koperand);
          std::string foperand = "";
          llvm::raw_string_ostream foperandso(foperand);

          (Instk->getOperand(i)->getType())->print(koperandso);
          (Instf->getOperand(i)->getType())->print(foperandso);
          contend = contend + "\nkoperand:" + koperand+". koperand size:"+getIntContent( koperand.size())+ " foperand:  "+ foperand+".foperand size:"+getIntContent( foperand.size());
          if( koperand.size() != 0  && (koperandso.str()==foperandso.str()) ){
              tmp++;
            }
        }
        contend = contend +"\ntmp:" + getIntContent(tmp);
        if(tmp!=0 && Instk->getNumOperands() !=0 )
            similarity = (tmp+1)/(Instk->getNumOperands()+1);
      }
      
      kIContend = Filter(kIContend); 
      fIContend = Filter(fIContend); 
      if(kIContend.compare(fIContend) == 0 ){
        if(kIContend.find("kfree")!=string::npos){
          contend = contend + "\nthis is a kfree inst. " + getInstContent( (Instruction*)Instk->getOperand(0)) + getInstContent((Instruction*)Instf->getOperand(0));
          contend = contend +"\nFilter operand instk. "+ Filter(getInstContent( (Instruction*)Instk->getOperand(0)));
          contend = contend +"\nFilter operand instf. "+ Filter(getInstContent((Instruction*)Instf->getOperand(0)));
          if(Filter(getInstContent( (Instruction*)Instk->getOperand(0))) == Filter(getInstContent((Instruction*)Instf->getOperand(0))))
            similarity = 1.0;
          else
            similarity = 0.5;  
        }
        else{
            similarity=1.0;
        }
      }
      

      contend = contend +"\n Inst similarity is :"+ getDoubleContent(similarity)+"\n";
      if((kIContend.find("memset")!=string::npos) || (kIContend.find("memcpy")!=string::npos) || (kIContend.find("init")!=string::npos)||(kIContend.find("INIT")!=string::npos)
      ||(kIContend.find("[")!=string::npos)){
        similarity = 1 - (double)StrminDistance(kIContend, fIContend)/(double)kIContend.length();
      }    
  }
  
  return similarity;
}

double CompareInst_New(llvm::Instruction *Instk, llvm::Instruction *Instf){  
  string contend = "\n***********************************************";
  double similarity = 0;
  if((getInstContent(Instk)).find("memcpy")!=string::npos){
    if((getInstContent(Instf)).find("skb_put_data")!=string::npos){ 
      similarity = 1.0;
      return similarity;
    }
  }
  string Instypek = Instk->getOpcodeName();
  string Instypef = Instf->getOpcodeName();
  if(Instypek!=Instypef || Instk->getNumOperands()!=Instf->getNumOperands())
    return 0;
  else{
      ICmpInst *ICk =NULL;
      ICmpInst *ICf =NULL;

      if(isa<ICmpInst>(Instk) && isa<ICmpInst>(Instf)){
        ICk = dyn_cast<ICmpInst>(Instk);
        ICf = dyn_cast<ICmpInst>(Instf);
      }
      else if (isa<BranchInst>(Instk) || isa<SwitchInst>(Instk)|| isa<SelectInst>(Instk)) {
        Value *Condk = NULL;
        Value *Condf = NULL;
        if(isa<BranchInst>(Instk)){
          BranchInst *BIk = dyn_cast<BranchInst>(Instk);
          BranchInst *BIf = dyn_cast<BranchInst>(Instf);
          contend = contend +"\n BR";
          if (BIk->getNumSuccessors() >1 && BIf->getNumSuccessors() > 1){
              Condf = BIf->getCondition();
              Condk = BIk->getCondition();
             
          } 
          contend = contend + "\nCondk: " + getValueContent(Condk);
          contend = contend + "\nCondf: " + getValueContent(Condf);
        }
        else if(isa<SwitchInst>(Instk)){
          SwitchInst *SIk = dyn_cast<SwitchInst>(Instk);
          SwitchInst *SIf = dyn_cast<SwitchInst>(Instf);
          if (SIk->getNumSuccessors() >1 && SIf->getNumSuccessors() > 1){
            Condf = SIf->getCondition(); 
            Condk = SIk->getCondition(); 
          }  
        }
        else{
          SelectInst *SIk = dyn_cast<SelectInst>(Instk);
          SelectInst *SIf = dyn_cast<SelectInst>(Instf) ;
          Condk = SIk->getCondition();
          Condf = SIf->getCondition();
        }
        if (Condk && Condf){
          ICk = dyn_cast<ICmpInst>(Condk);
          ICf = dyn_cast<ICmpInst>(Condf);
        } 
      }
      
      
      std::string kIContend = "";
      llvm::raw_string_ostream krso(kIContend);
      std::string fIContend = "";
      llvm::raw_string_ostream frso(fIContend);

      std::string koperand1 = "";
      llvm::raw_string_ostream koperandso1(koperand1);
      std::string foperand1 = "";
      llvm::raw_string_ostream foperandso1(foperand1);

      std::string koperand0 = "";
      llvm::raw_string_ostream koperandso0(koperand0);
      std::string foperand0 = "";
      llvm::raw_string_ostream foperandso0(foperand0);
      
      if(ICk && ICf){ 
        double tmp = 0; 
        ICk->print(krso);
        ICf->print(frso);

        
        if(getICmpCode(ICk, 0)== getICmpCode(ICf, 0)){
          tmp++;
        }
      
        (ICk->getOperand(0)->getType())->print(koperandso0);
        (ICf->getOperand(0)->getType())->print(foperandso0);
        if( (koperandso0.str() == foperandso0.str()) || (koperandso0.str()=="i32" &&foperandso0.str() =="i64") || (koperandso0.str()=="i64" &&foperandso0.str() =="i32") )
            tmp++;
        // determine that whether the second operand are the same
        (ICk->getOperand(1)->getType())->print(koperandso1);
        (ICf->getOperand(1)->getType())->print(foperandso1);
        if( (koperandso1.str() == foperandso1.str()) || (koperandso0.str()=="i32" &&foperandso0.str() =="i64") || (koperandso0.str()=="i64" &&foperandso0.str() =="i32") )
          tmp++;  
        similarity = (tmp+1)/4; 
      }
      else{
        Instk->print(krso); 
        Instf->print(frso);
        contend = contend + " \nkIContend:"+kIContend+ "\nfIContend: "+fIContend;

        double tmp = 0; 
        contend = contend + "\nICk:"+ getInstContent(ICk);
        contend = contend + "\nICf:"+ getInstContent(ICf);
        contend = contend +"\nBefore enter loop, tmp:" + getIntContent(tmp);
        contend = contend + " \n NumOperands:"+ getIntContent(Instk->getNumOperands())+"\n";
        for(int i=0;i<Instk->getNumOperands();i++){
          std::string koperand = "";
          llvm::raw_string_ostream koperandso(koperand);
          std::string foperand = "";
          llvm::raw_string_ostream foperandso(foperand);

          (Instk->getOperand(i)->getType())->print(koperandso);
          (Instf->getOperand(i)->getType())->print(foperandso);
          contend = contend + "\nkoperand:" + koperand+". koperand size:"+getIntContent( koperand.size())+ " foperand:  "+ foperand+".foperand size:"+getIntContent( foperand.size());
          if( koperand.size() != 0  && (koperandso.str()==foperandso.str()) ){
              tmp++;
            }
        }
        contend = contend +"\ntmp:" + getIntContent(tmp);
        if(tmp!=0 && Instk->getNumOperands() !=0 )
            similarity = (tmp+1)/(Instk->getNumOperands()+1);
      }
      
      kIContend = Filter(kIContend); 
      fIContend = Filter(fIContend); 
      if(kIContend.compare(fIContend) == 0 ){
        // if Instk and Instf are kfree instruction, we need to further compare the operand of the two instruction.
        if(kIContend.find("kfree")!=string::npos){
          // compare the operand of the two instruction
          contend = contend + "\nthis is a kfree inst. " + getInstContent( (Instruction*)Instk->getOperand(0)) + getInstContent((Instruction*)Instf->getOperand(0));
          contend = contend +"\nFilter operand instk. "+ Filter(getInstContent( (Instruction*)Instk->getOperand(0)));
          contend = contend +"\nFilter operand instf. "+ Filter(getInstContent((Instruction*)Instf->getOperand(0)));
          if(Filter(getInstContent( (Instruction*)Instk->getOperand(0))) == Filter(getInstContent((Instruction*)Instf->getOperand(0))))
            similarity = 1.0;
          else
            similarity = 0.5;
          contend = contend +"\nstring similarity is :"+ getDoubleContent(similarity)+"\n";   
          return similarity;  
        }
        else{
            similarity=1.0;
        }
        #ifdef CMPInst
        OP<< "inst similarity is :"<<similarity<<"\n";   
        contend = contend +"\n string similarity is :"+ getDoubleContent(similarity)+"\n";  
        #endif
      }
      
      contend = contend +"\nLog2, Inst similarity is :"+ getDoubleContent(similarity)+"\n";
      if((kIContend.find("memset")!=string::npos) || (kIContend.find("memcpy")!=string::npos) || (kIContend.find("init")!=string::npos)||(kIContend.find("INIT")!=string::npos)
      ||(kIContend.find("[")!=string::npos)||(kIContend.find("lock")!=string::npos)||(kIContend.find("call")!=string::npos)){
        similarity = 1 - (double)StrminDistance(kIContend, fIContend)/(double)kIContend.length();
      }
      contend = contend +"\nLog Inst similarity is :"+ getDoubleContent(similarity)+"\n";
  }
  
  return similarity;
}

Value* Getopf(Value *opkp, Value *opfp, Instruction *instk){
  Value *opf = NULL;
  int pos  = -1;

  Instruction *IK = dyn_cast<Instruction>(opkp);
  Instruction *IF = dyn_cast<Instruction>(opfp);
  
  
  if((opkp != NULL) && (instk != NULL))
    pos = FindPos(opkp, instk);
  if(pos != -1)
    opf = IF->getOperand(pos);
  return opf;
}


Instruction* GetassignInst(Instruction *instk){
  Instruction *assignValue = NULL;

  int Line_k = GetLocation(instk);

  for(auto U : instk->users()){
    Instruction *Inst = dyn_cast<Instruction>(U);
    if(Inst==NULL)
      continue;
    if(isa<StoreInst>(Inst)){
        int Line = GetLocation(Inst);
        if(Line < Line_k)
          assignValue = Inst;
        else
          break;
    }    
  }
  return  assignValue;
}




std::tuple<Instruction*, Instruction*, bool> CompareSource(Instruction *instk, std::map<mul_key, mul_key> CriticalValue)
{
    Instruction *cvk = NULL;
    Instruction *cvf = NULL;

    Value *operandk = NULL;
    Value *operandf = NULL;

    bool identical = false;
    
    for(std::map<mul_key, mul_key>::iterator iter = CriticalValue.begin(); iter != CriticalValue.end(); iter++ )
    { 
      mul_key opk = iter->first;
      mul_key opf = iter->second;
      Instruction *IK = opk.first;
      std::stack<string> patternk = opk.second;
      Instruction *IF = opf.first;
      std::stack<string> patternf = opf.second;
      
      BasicBlock *BBK = IK->getParent();
      BasicBlock *BBF = IF->getParent();
      
      if(BBK == NULL|| BBF == NULL)
        continue;
      BasicBlock::iterator iterK = BBK->end();
      BasicBlock::iterator iterF = BBF->end();
      int length = patternk.size()-1;
      cvk = IK;
      cvf = IF;
      operandk = cvk;
      operandf = cvf;
      while(length){
          cvk = dyn_cast<Instruction>(operandk);
          if(isa<GetElementPtrInst>(cvk)){
           operandk = cvk->getOperand(0);
           
          }  
          else if(isa<LoadInst>(cvk)){
            operandk = cvk->getOperand(0);
            
          }    
          else if(isa<StoreInst>(cvk)){
            if(cvk->getOperand(1) == cvk)
              operandk = cvk->getOperand(0);
              
          }
          else if(isa<BitCastInst>(cvk)){
            operandk = cvk->getOperand(0);
          }
          length --;
      }
      length = patternf.size()-1;
      while(length){
          cvf = dyn_cast<Instruction>(operandf);
          if(isa<GetElementPtrInst>(cvf)){
           operandf = cvf->getOperand(0);
          }  
          else if(isa<LoadInst>(cvf)){
            operandf = cvf->getOperand(0);  
          }    
          else if(isa<StoreInst>(cvf)){
            if(cvf->getOperand(1) == cvf)
              operandf = cvf->getOperand(0);    
          }
          else if(isa<BitCastInst>(cvf)){
            operandf = cvf->getOperand(0);
          }
          length --;
      }

      if( (cvk != NULL) && (cvf != NULL)){
        
        if(Filter(getValueContent(cvk)) == Filter(getValueContent(cvf)))
          identical =true;
          return make_tuple(cvk, cvf, identical);
      }
    }
    return make_tuple(cvk, cvf, identical);
}

std::tuple<Instruction*, Instruction*, bool> CompareSource(Instruction *instk, std::map<Value*, Value*> CriticalValue){

  Value *opf = NULL;
  Instruction *instf = NULL;

  bool identical = false;
  if(CriticalValue.size() == 0){
    identical = false;
    return make_tuple(instk, instf, identical);
  }

  if(CriticalValue.find(instk) != CriticalValue.end())
    opf = CriticalValue.find(instk)->second;

  

  // If in CriticalValue, there does not record pair<opk,opf>, then find opf through the propogation of opk i.e. pair<opkp,opfp>
  std::map<Value*, Value*>::iterator iter = CriticalValue.begin();
  
  while((opf == NULL) && (iter != CriticalValue.end())){
      Value *opkp = iter->first;
      Value *opfp = iter->second;
      opf = Getopf(opkp, opfp, instk);
      iter++;
  }

  if(opf == NULL){

    identical = false;
    return make_tuple(instk, instf, identical);
  }

  instf = dyn_cast<Instruction>(opf);
  
  if(instf == NULL || instk == NULL ){
    identical = false;
    return make_tuple(instk, instf, identical);
  }
  
  if(Filter(getInstContent(instk)) != Filter(getValueContent(opf))){
    identical = false;
    return make_tuple(instk, instf, identical);
  }
  
  Function *K = instk->getParent()->getParent();
  Function *F = instf->getParent()->getParent();

  std::vector<Value*> Kfargs = Getargs(K);
  std::vector<Value*> Ffargs = Getargs(F);

  if((std::find(Kfargs.begin(), Kfargs.end(), instk) != Kfargs.end()) && (std::find(Ffargs.begin(), Ffargs.end(), instf) != Kfargs.end())){
    identical = true;
    return make_tuple(instk, instf, identical);
  }
    
  
  Instruction *assignInstk = GetassignInst(instk);
  Instruction *assignInstf = GetassignInst(instf);
  
  if(assignInstk == NULL || assignInstf == NULL){
    identical = false;
    return make_tuple(instk, instf, identical);
  }

  if(Filter(getInstContent(assignInstk)) != Filter(getInstContent(assignInstf))){
    identical = false;
    return make_tuple(assignInstk, assignInstf, identical);
  }
  else{
    identical = true;
    return make_tuple(assignInstk, assignInstf, identical);
  }
}




void UpdateVetex(int basicblockIDk, std::queue<int> *kcommon_subgraph,
std::vector<int> *kcommon_node, std::vector<int> *remain_graph1, set<int> *SScfgk, int basicblockIDf, std::queue<int> *fcommon_subgraph,
std::vector<int> *fcommon_node,std::vector<int> *remain_graph2, set<int> *SScfgf,std::map<int,int> *MCSMap){ 
  kcommon_node->push_back(basicblockIDk);
  fcommon_node->push_back(basicblockIDf);
  MCSMap->insert(make_pair(basicblockIDk,basicblockIDf));
  kcommon_subgraph->push(basicblockIDk);
  fcommon_subgraph->push(basicblockIDf);
  set<int>::iterator iterk,iterf;
  if(SScfgk->size()!=0)
  for (iterk=SScfgk->begin(); iterk!=SScfgk->end();)
    {
        if(*iterk == basicblockIDk)
            SScfgk->erase(iterk++);
        else
            iterk++;
    }
  if(SScfgf->size()!=0)
  for (iterf=SScfgf->begin(); iterf!=SScfgf->end();)
    {
        if(*iterf == basicblockIDf)
            SScfgf->erase(iterf++);
        else
            iterf++;
    } 
  if(remain_graph1->size()!=0)
  	DeleElem(remain_graph1,basicblockIDk);
  if(remain_graph2->size()!=0)
  	DeleElem(remain_graph2,basicblockIDf);
}

void UpdateVetex(int basicblockIDf, std::queue<int> *fcommon_subgraph,
std::vector<int> *fcommon_node,std::vector<int> *remain_graph2){
  fcommon_subgraph->push(basicblockIDf);
  fcommon_node->push_back(basicblockIDf);
  if(remain_graph2->size()!=0)
    DeleElem(remain_graph2,basicblockIDf);
}


void UpdateVetex(int basicblockID, std::vector<int> *remain_graph, set<int> *SScfg){
  if(remain_graph->size()!=0)
    DeleElem(remain_graph,basicblockID);
  set<int>::iterator iterk;
  if(SScfg->size()!=0)
  for (iterk=SScfg->begin(); iterk!=SScfg->end();)
    {
        if(*iterk == basicblockID)
            SScfg->erase(iterk++);
        else
            iterk++;
    }
}

void UpdateVetex(int basicblockID, std::vector<int> *remain_graph){
  if(remain_graph->size()!=0)
    DeleElem(remain_graph,basicblockID);
}

void UpdateVetex(int basicblockIDk,std::queue<int> *kcommon_subgraph,
std::vector<int> *kcommon_node, std::vector<int> *remain_graph1, int basicblockIDf, std::queue<int> *fcommon_subgraph,
std::vector<int> *fcommon_node,std::vector<int> *remain_graph2,std::map<int,int> *MCSMap){
  kcommon_subgraph->push(basicblockIDk);
  kcommon_node->push_back(basicblockIDk);
  fcommon_subgraph->push(basicblockIDf);
  fcommon_node->push_back(basicblockIDf);
  MCSMap->insert(make_pair(basicblockIDk,basicblockIDf));
  if(remain_graph1->size()!=0)
  DeleElem(remain_graph1,basicblockIDk);
  if(remain_graph2->size()!=0)
  DeleElem(remain_graph2,basicblockIDf);
}

//  in UpdateBB, we need to  remove the seneitive Inst in rk according to IdenticalInst
void UpdateBB( int flag, vector<IdenticalInst> *identicalInsts, bbl_info rk){
  
  map<llvm::Instruction*, int> *Sensitive_Info = &(rk->Sensitive_Info);
  map<llvm::Instruction*, int>::iterator iter1;
  vector<IdenticalInst>::iterator iter2;
  
  Printmap(rk->Sensitive_Info);
  
  for(iter2=identicalInsts->begin();iter2!=identicalInsts->end();iter2++)
  {
    
    Instruction *inst =  NULL;
    int bblID = -1;
    if(flag){
      Instruction *inst = get<0>(*iter2).first;
      
      int bblID = get<0>(*iter2).second;
    }
    else{
      Instruction *inst = get<1>(*iter2).first;
      int bblID = get<1>(*iter2).second;
    }
    for(iter1 = Sensitive_Info->begin(); iter1!=Sensitive_Info->end();){
      if((iter1->first == inst && iter1->second == bblID) )
        Sensitive_Info->erase(iter1++);
      else
          iter1++;
    }
  }
   
   Printmap(rk->Sensitive_Info);
}

int GetUseNo(USESEQ useSeqk){
  std::set<int> Lines;
  for (USESEQ::iterator iterk = useSeqk.begin(), itere = useSeqk.end(); iterk != itere; ++iterk) {
      Value *op = iterk->first;
      Instruction *I = iterk->second; 
      int LineInfo = GetLocation(I);  
      Lines.insert(LineInfo);
  }
  return Lines.size();
}

int GetUseNo(mul_USESEQ useSeqk){
  std::set<int> Lines;
  for(mul_USESEQ::iterator iterk = useSeqk.begin(), itere = useSeqk.end(); iterk != itere; ++iterk){        
      std::pair<Instruction*, stack<string>> op = iterk->first;  // key
      vector<Instruction*> opkUse = iterk->second; 
      Instruction *I = opkUse.back(); 
      int LineInfo = GetLocation(I);  
      Lines.insert(LineInfo); 
  }
  return Lines.size();
}

string getFileExt(const string& s, const string& delimiter) {
   size_t i = s.rfind(delimiter, s.length());
   if (i != string::npos) {
      return(s.substr(i+1, s.length() - i));
   }

   return("");
}

string DeleteFileExt(const string& s, const string& delimiter) {
   size_t i = s.rfind(delimiter, s.length());
   if (i != string::npos) {
      //return(s.substr(i+1, s.length() - i));
      return(s.substr(0,i));
   }
   return("");
}


void UpdateBB(bbl_info rl, bbl_info rs){
  rl->CMPtime = 1;
  BasicBlock *bl=rl->bbl; 
  BasicBlock *bs=rs->bbl;
  vector<llvm::Instruction*> LInstruction = rl->Instructions;
  vector<llvm::Instruction*> SInstruction = rs->Instructions;
  int BInstSize = LInstruction.size();
  int AInstSize ;
  vector<string>  SInsStrtSequence;

  for (vector<llvm::Instruction*>::iterator s_iter = SInstruction.begin(); s_iter != SInstruction.end(); s_iter++) { 
    Instruction *Inst = *s_iter; 
    string Inst_str("");
    raw_string_ostream stream(Inst_str);
    stream << *Inst;  
    Inst_str = stream.str(); 
    Inst_str = Filter(Inst_str);
    SInsStrtSequence.push_back(Inst_str);
  }
  
  for (vector<llvm::Instruction*>::iterator iter = (rl->Instructions).begin(); iter != (rl->Instructions).end()-1; ) { 
    Instruction *Inst = *iter; 
    string Inst_str("");
    raw_string_ostream stream(Inst_str);
    stream << *Inst;  
    Inst_str = stream.str(); 
    Inst_str = Filter(Inst_str);
    if(Is_element_in_vector(SInsStrtSequence,Inst_str)){
      (rl->Instructions).erase(iter);
      SInsStrtSequence.erase(std::find(SInsStrtSequence.begin(),SInsStrtSequence.end(),Inst_str));
    }  
    else
      iter++;
    }
    for (vector<llvm::Instruction*>::iterator bbl_iter = LInstruction.begin(); bbl_iter != LInstruction.end(); bbl_iter++) { 
      Instruction *Inst = *bbl_iter; 
    }
    AInstSize = LInstruction.size();
    if((float)(BInstSize-AInstSize)/(float)BInstSize>0.3)
      rl->CMPtime = 1;
    else
      rl->CMPtime = 0;
}


void UpdateDeletedBBlist(int basicblockIDk,std::vector<int> 
*remain_graph1,set<int> *SScfgk,std::vector<int> *DeletedBBlist){
  if(remain_graph1->size()!=0)
  DeleElem(remain_graph1,basicblockIDk);
  set<int>::iterator iterk;
  for (iterk=SScfgk->begin(); iterk!=SScfgk->end();)
    {  
        if(*iterk == basicblockIDk){
          SScfgk->erase(iterk++);
        }
        else
          iterk++;  
    }
  DeletedBBlist->push_back(basicblockIDk);
}

void UpdateDeletedBBlistN(int basicblockIDk,std::vector<int> 
*remain_graph1,std::vector<int> *DeletedBBlist){
  DeleElem(remain_graph1,basicblockIDk);
  DeletedBBlist->push_back(basicblockIDk);
}


std::vector<int> ObtainRemainVetex(std::vector<int> remain_graph, std::map<int,int> relatedvetex){
  std::vector<int> RemainVetex;
  std::vector<int> relatedVetex;
  std::map<int,int>::iterator iter;
  for(iter = relatedvetex.begin(); iter != relatedvetex.end(); iter++){
    relatedVetex.push_back(iter->first);
  }
  set_difference(remain_graph.begin(),remain_graph.end(),relatedVetex.begin(),
  relatedVetex.end(),inserter(RemainVetex,RemainVetex.begin()));
  return RemainVetex;
}

string DumpsensitiveBBInst(Sensitive_Info_of_Functions *siof){
  string content = "\n";
  int bblID;
  int type;
  Instruction *Inst;
  string LineInfo;
  if(siof==NULL)
       content = "\nSensitiveBBInst is Empty.";
    else{
        for(int i=0;i<siof->size;i++){
          bblID = siof->sen_list[i].bbl_NO;
          type = siof->sen_list[i].type;
          Inst = siof->sen_list[i].inst;
          LineInfo = ObtainSourceCodeInfoInst(Inst);
          content = content + "\n{" + "  \"BBLID\":" + "\"" +getIntContent(bblID)+ "\", " +
                    "  \"Type\":" + "\"" +getIntContent(type)+ "\", " + "  \"LineInfo\":" + "\"" +LineInfo+ "\"}";
        }
    }
    return content;
}

void DumpIRMAP(std::map<int, Instruction*> *IRMAP, string file_to_dump){
    if(IRMAP==NULL || IRMAP->size()==0)
        OP<<"\nIRMAP is Empty.";
    else{
        FILE* fp;
        char *filename=(char*)file_to_dump.c_str();
        if ((fp = fopen(filename, "w+")) == NULL){
        OP<<file_to_dump;
        OP<<"failed to open file.\n";
        } 
        string content;
        for(std::map<int, Instruction*>::iterator iter = IRMAP->begin(); iter != IRMAP->end(); iter++){
            int basicblockID = iter->first;
            Instruction *Inst = iter->second;
            content+="Node";
            content+=getIntContent(basicblockID);
            content+=getInstContent(Inst);
            content+="\n";
        }
        char *Content = (char*)content.c_str();
        if(Content != NULL){
          fwrite( Content, sizeof(unsigned char), strlen(Content), fp);
          fclose(fp);
        }
    }
}

string DumpMCSMap(std::map<int,int> *MCSMap ){
    string content ="\"";
    if(MCSMap==NULL || MCSMap->size()==0)
        content = "\"MCSMap is Empty.";
    else{
        for(std::map<int,int>::iterator iter = MCSMap->begin(); iter != MCSMap->end(); iter++){
            content = content +"\\n["+ getIntContent(iter->first)+"<-->"+ getIntContent(iter->second)+"]";
        }
    }
    content = content +"\"";
    return content;
}

string DumpMCS(std::map<int,int> *MCSMap ){
    string content ="";
    if(MCSMap==NULL || MCSMap->size()==0)
        content = "MCSMap is Empty";
    else{
        for(std::map<int,int>::iterator iter = MCSMap->begin(); iter != MCSMap->end(); iter++){
            content = content +"\\n["+ getIntContent(iter->first)+"<-->"+ getIntContent(iter->second)+"]";
        }
    }
    return content;
}

string DumpBasicBlockInfo(Mapbbl *basicBlockInfo){
    string content ="";
    if(basicBlockInfo == NULL)
      content = "\nBasicBlockInfo is Empty.";
    else{ 
      for (Mapbbl::iterator iter=basicBlockInfo->begin(); iter!=basicBlockInfo->end(); iter++){
          int basicblockID = iter->first ;
          bbl_info b = iter->second;
          content = content + "\n\"BB"+getIntContent(basicblockID)+"\":{";
          // children
          ChildrenNode childList =  b->childrennode;
          if(childList==NULL)
            content = content + "\n\"children\":{}";
          else{
              ChildrenNode c = childList->Next; 
              content = content + "\n\"children\":{";
              while(c){
                  content = content + getIntContent(c->Data)+" ";
                  c=c->Next;
              }
              content = content + "}";
          }
          // Silbing
          SilbingNode  silbingList = b->silibingnode;
          if(silbingList==NULL)
            content = content + "\n\"silbing\":{}";
          else{
              SilbingNode s = silbingList->Next; 
              content = content + "\n\"silbing\":{";
              while(s){
                  content = content + getIntContent(s->Data)+" ";
                  s=s->Next;
              }
              content = content + "}";
          }
          // Parent
          ParentNode parentList = b->parentnode;
          if(parentList==NULL)
            content = content + "\n\"parent\":{}";
          else{
              ParentNode p = parentList->Next; 
              content = content + "\n\"parent\":{";
              while(p){
                  content = content + getIntContent(p->Data)+" ";
                  p=p->Next;
              }
              content = content + "}";
          }
          content = content + "}";
  
      }
    }
    return content;
}

string DumpFunction(Function *F){
  string content;
  int KbbCount = 0;   

  std::map<BasicBlock*, int> basicBlockMap;
  for (Function::iterator FB_iter = F->begin(); FB_iter != F->end(); ++FB_iter){
      BasicBlock *KcurBB = &*FB_iter;
      int KfromCountNum;
      int KtoCountNum;
      int Linefrom, LineTo;
      
      if (basicBlockMap.find(KcurBB) != basicBlockMap.end()){
            KfromCountNum = basicBlockMap[KcurBB];
            Instruction *I = &*(KcurBB->begin());
            Linefrom = GetLocation(I);
      }
      else{
            KfromCountNum = KbbCount;
            basicBlockMap[KcurBB] = KbbCount++;
      }
      #ifdef TEST_GM
        OP << "\nKcurBB" <<"\tBB" << KfromCountNum << "\t[shape=record, label=\"{BB"<< KfromCountNum << ":\\l\\l";
        content  = content + "\nKcurBB" + "\tBB" + getIntContent(KfromCountNum) + " +" + getIntContent(Linefrom) ;
      #endif
      
      std::string KcurBBContend = "";
      llvm::raw_string_ostream krso(KcurBBContend);

      
      for (BasicBlock::iterator KI_iter = KcurBB->begin(); KI_iter != KcurBB->end(); ++KI_iter) {
            KI_iter->print(krso); 
      }
      //content = content + KcurBBContend;
      for (succ_iterator PI = succ_begin(KcurBB), E = succ_end(KcurBB); PI != E; ++PI){
            BasicBlock *KSuccBB = *PI;
            if (basicBlockMap.find(KSuccBB) != basicBlockMap.end()){
                KtoCountNum = basicBlockMap[KSuccBB];   
            }
            else{
                KtoCountNum = KbbCount;
                basicBlockMap[KSuccBB] = KbbCount++;
            }
            #ifdef TEST_GM
            OP << "\nBB" << KfromCountNum<< "-> BB"
                << KtoCountNum << ";\n";
            content  = content +  "\nBB" +getIntContent( KfromCountNum)+ "-> BB"
                +getIntContent(KtoCountNum) + ";\n";
            #endif
      }
  }
  return content;
}

//Used for debug
void printFunctionMessage(Function *F){

    if(!F)
        return;
    
    for(Function::iterator b = F->begin(); 
        b != F->end(); b++){
        BasicBlock * bb = &*b;
        for (BasicBlock *Succ : successors(bb)) {
  }
    }

}


string getBlockName(BasicBlock *bb){
    if(bb == NULL)
        return "NULL block";
    std::string Str;
    raw_string_ostream OS(Str);
    bb->printAsOperand(OS,false);
    return OS.str();
}

void DumpInputInfo(Mapbbl *KbasicBlockInfo, Mapbbl *FbasicBlockInfo, Sensitive_Info_of_Functions *sk, Sensitive_Info_of_Functions *sf, std::map<int,int> *MCSMap, string file_to_dump){
  FILE* fp;
  char *filename=(char*)file_to_dump.c_str();
  if ((fp = fopen(filename, "w+")) == NULL){
  OP<<"failed to open file.\n";
  } 
  else{
    string content = "";
    if(KbasicBlockInfo != NULL && KbasicBlockInfo->size()!=0){
      string KBasicBlockInfo = DumpBasicBlockInfo(KbasicBlockInfo);
      content += KBasicBlockInfo;
    }
    if(FbasicBlockInfo != NULL && FbasicBlockInfo->size()!=0){
      string FBasicBlockInfo = DumpBasicBlockInfo(FbasicBlockInfo);
      content += FBasicBlockInfo;
    }
    if(sk != NULL){
      content += "\nsensitive KInst\n";
      string KsensitiveBBInst = DumpsensitiveBBInst(sk);
      content += KsensitiveBBInst;
    }
    if(sf != NULL ){
      content += "\nsensitive FInst\n";
      string FsensitiveBBInst = DumpsensitiveBBInst(sf);
      content += FsensitiveBBInst;
    }
    if(MCSMap !=NULL && MCSMap->size()!=0){
      string MCS = DumpMCSMap(MCSMap);
      content += MCS;
    }
    char *Content = (char*)content.c_str();
    fwrite( Content, sizeof(unsigned char), strlen(Content), fp);
    fclose(fp);
  }

}

string DumpVectorString(std::vector<string> *V){
 string content = "[";
 if(V == NULL || V->size() == 0)
    content = "Empty.";
  else{
      for(std::vector<string>::iterator iter = V->begin(); iter != V->end(); iter++){
        string s = *iter;
        content = content + "\n{\"Value\" : " + "\" "  + s +  "\"}";
        if(iter != --V->end())
          content = content + ",";
      }
  }
  content = content + "]";
  return content;
}

string DumpArgs(std::vector<Value*> *args){
 string content = "[";
 if(args == NULL || args->size() == 0)
    content = "Empty.";
  else{
      OP<< "\nDumpArgs args size:"<< args->size()<<"\n";
      for(std::vector<Value*>::iterator iter = args->begin(); iter != args->end(); iter++){
        Value *arg = *iter;
        content = content + "\n{\"Value\" : " + "\" " + getValueContent(arg)+ "\",\n\"Lineno\" : " + "\" " + getIntContent(GetLocation(arg)) +  "\"}";
        if(iter != --args->end())
          content = content + ",";
      }
  }
  content = content + "]";
  return content;
}

string DumpDeletedSSO(std::map<llvm::Instruction*, int> *deletedSSlistr, Mapbbl *KbasicBlockInfo){
  string content = "[";
  int bblID;
  int  type;
  Instruction *Inst;
  string LineInfo;
  if(deletedSSlistr==NULL)
       content = "Empty.";
  else{
      for(std::map<llvm::Instruction*, int>::iterator iter = deletedSSlistr->begin(); iter != deletedSSlistr->end(); iter++){
        type = iter->second;
        Inst = iter->first;
        StringRef funcName = Inst->getParent()->getParent()->getName();
        LineInfo = ObtainSourceCodeInfoInst(Inst);
        content = content + "\n{\"Function\" : " + "\" " + funcName.str()+ "\",\n\"Inst\" : " + "\" " + getInstContent(Inst) + "\"," + "  \n\"type\" : " + "\"" +getIntContent(type)+ "\",  \n\"BBLID\" : " + "\"" +getIntContent(ObtainBBInfo(Inst->getParent(), KbasicBlockInfo)->BBLID)+ "\", "  + "  \n\"LineInfo\" : " + "\"" +LineInfo+ "\"}";
        if(iter != --deletedSSlistr->end())
          content = content + ",";
      }
  }
   content = content + "]";
  return content;
}

// Check if a basic block contains if condition and return the instruction
void ContainCheck(bbl_info b) {
    if(b==NULL)
      return;
    BasicBlock *BB = b->bbl;
    if(BB==NULL)
      OP<<"ERROR, BB is a NULL pointer.\n";
    for (BasicBlock::iterator I_iter = BB->begin(); I_iter != BB->end(); ++I_iter){
        Instruction *Inst = &*I_iter;
        Instruction *IC = NULL;
	      Value *Cond = NULL;
        if(Inst==NULL)
          continue;
        if (isa<BranchInst>(Inst) || isa<SwitchInst>(Inst)) {
            BranchInst *BI = dyn_cast<BranchInst>(Inst);
            SwitchInst *SI = NULL;
            if (BI) {
                if (BI->getNumSuccessors() < 2)
                    continue;
            } 
            else {
                SI = dyn_cast<SwitchInst>(Inst);
                if (SI->getNumSuccessors() < 2)
                    continue;
            }
            if (BI){
                Cond = BI->getCondition();
            }        
            else{
                Cond = SI->getCondition();      
            }
        }
        else if (SelectInst *SI = dyn_cast<SelectInst>(Inst)) {
            Cond = SI->getCondition();
        }  
        if(Cond){
          IC  = dyn_cast<ICmpInst>(Cond);    
          if(IC!=NULL)
            b->Sensitive_Info.insert(make_pair(Inst,scheck));  
        }    
    }   
}

// We calculate the similarity of the neighbor of two basic blocks
double ObtainneighborSimilarity(bbl_info rk,  bbl_info rf, std::map<int,int> *MCSMap){
  double neighborSimilarity = 0;

  vector<int> kp = ObtainParentList(rk);     
  
  vector<int> kc = ObtainChildrenList(rk);
 
  vector<int> ks = ObtainSilbingList(rk);
  
  vector<int> tmpk, kunion;
  set_union(kp.begin(),kp.end(),kc.begin(),kc.end(),back_inserter(tmpk));
  set_union(tmpk.begin(),tmpk.end(),ks.begin(),ks.end(),back_inserter(kunion));

  vector<int> fp = ObtainParentList(rf);     
   
  vector<int> fc = ObtainChildrenList(rf);
  
  vector<int> fs = ObtainSilbingList(rf);

  vector<int> tmpf, funion;
  set_union(fp.begin(),fp.end(),fc.begin(),fc.end(),back_inserter(tmpf));
  set_union(tmpf.begin(),tmpf.end(),fs.begin(),fs.end(),back_inserter(funion));

  int insersection = 0;
  for(std::vector<int>::iterator iter =kunion.begin();iter != kunion.end();iter++ ){
   
    std::map<int,int>::const_iterator pos = MCSMap->find(*iter);
    if (pos != MCSMap->end()){
        if(find(funion.begin(), funion.end(), pos->second) != funion.end())
        insersection++;
    }
  }
  if(kunion.size() && funion.size())
    neighborSimilarity = (double)insersection/(kunion.size()<funion.size()?  kunion.size(): funion.size());
  else
    neighborSimilarity = 0;
  return neighborSimilarity;
}

SigMatchResult SigMatch(bbl_info rk, bbl_info rf, std::map<int,int> *MCSMap){

  double weight11 = 0.1;  double weight21 = 0.1; 
  double weight12 = 0.2;  double weight22 = 0;  
  double weight13 = 0.3;  double weight23 = 0.3;
  double weight14 = 0.7;  double weight24 = 0.9;
  double weight15 = 0.3;  double weight25 = 0.3;
  bool changweight21 = false;

  string content = "\n\"SigMatch\":{";
  double IsMatch = 0; 
  vector<IdenticalInst> identicalInsts;
  SigMatchResult smr;
  map<llvm::Instruction*, int> DeletedSSlist;
  if(rf==NULL || rk==NULL){
    OP<<"Invaild bbl info.\n";
  }
  llvm::BasicBlock *bblk =  rk->bbl;
  llvm::BasicBlock *bblf =  rf->bbl;

  int BBLIDf = rf->BBLID;
  int BBLIDk = rk->BBLID;
  content = content +"\"BBLK\":" +getIntContent(BBLIDk)+"  \"BBLF\":" +getIntContent(BBLIDf);
  vector<llvm::Instruction*> KInstruction = rk->Instructions;
  vector<llvm::Instruction*> FInstruction = rf->Instructions;
  map<llvm::Instruction*, int> sensitive_Infok = rk->Sensitive_Info;
  map<llvm::Instruction*, int> sensitive_Infof = rf->Sensitive_Info; // Problems

  // if br instruction in firmware is not treated as a sensitive instruction, we manually add the br instruction into sensitive_Infof 
  if(BBLIDf < NewBasicBlockID){
    Instruction *lastInst =  &*(--bblf->end());
    if((lastInst)&&((isa<BranchInst>(lastInst))|| (isa<SwitchInst>(lastInst))|| (isa<SelectInst>(lastInst))) && (sensitive_Infof.find(lastInst) == sensitive_Infof.end()))
      sensitive_Infof.insert(make_pair(lastInst, scheck));
    }
 
  double identicalInst = 0.0; 
  double MaxidenticalInst = 0.0;  
  double SwitchidenticalInst = 0.0;  
  double AverageidenticalInst = 0.0;  
  #ifdef Debug_SM
    OP<<"sensitive_InfoK in basic block rk \n";
    Printmap(sensitive_Infok);
    OP<<"sensitive_InfoF in basic block rf\n";
    Printmap(sensitive_Infof);
  #endif
  content = content + "\nsensitive_InfoK" +Dumpmap(sensitive_Infok) + "\nsensitive_InfoF" +Dumpmap(sensitive_Infof);
  int Size_of_sensitive_Infok = sensitive_Infok.size();
  

  for(std::map<llvm::Instruction*, int>::iterator itk=sensitive_Infok.begin();
              itk != sensitive_Infok.end();itk++){
    bool IsInstkMatched = false; 
    Instruction *Instk = itk->first;
    int sensitive_typek = itk->second;
    for(std::map<llvm::Instruction*, int>::iterator itf=sensitive_Infof.begin();
              itf != sensitive_Infof.end();itf++){
      Instruction *Instf = itf->first; 
      int sensitive_typef = itf->second;
      if(!Instk || !Instf)
        continue;
      if(sensitive_typek != sensitive_typef)
        continue;
      else{
        identicalInst = CompareInst_New(Instk,Instf);
        content = content + "\nInstk: "+ getInstContent(Instk) + " Instf: "+getInstContent(Instf) +   "  identicalInst:" + getDoubleContent(identicalInst);
        
        
        if(identicalInst>=0.75){  
            if(isa<SwitchInst>(Instk)){
                changweight21 = true;
                weight21 = 0.4;
                SwitchidenticalInst = identicalInst;
            }
            MaxidenticalInst = identicalInst > MaxidenticalInst ? identicalInst : MaxidenticalInst;
            AverageidenticalInst += identicalInst;
            std::pair<Instruction*, int> pairk = make_pair(Instk,rk->BBLID);
            std::pair<Instruction*, int> pairf = make_pair(Instf,rf->BBLID);
            
            DeleSensitiveItem(&sensitive_Infof,Instf); 
            IsInstkMatched = true ;
            content = content + "\nInstk: "+ getInstContent(Instk) + "\nInstf: "+getInstContent(Instf) + ";  similarity: "+ getDoubleContent(identicalInst) +"Matched: True";
           
            identicalInsts.push_back(make_tuple(pairk,pairf,identicalInst));
            break;
          }
        }
    }
   
    if(IsInstkMatched == false){
      DeletedSSlist[Instk]=sensitive_typek;
      content = content + "\nInstk: "+ getInstContent(Instk) +" is deleted.";
    }
  }
  if(Size_of_sensitive_Infok==0)
    AverageidenticalInst = 0;
  else{
    if(changweight21)
      AverageidenticalInst = SwitchidenticalInst;
    else
      AverageidenticalInst = AverageidenticalInst/Size_of_sensitive_Infok;
  }
  
  
  #ifdef Debug_SM
  OP<<" AverageidenticalInst "<<AverageidenticalInst<<"\n";
  #endif
  content = content + "\nAverageidenticalInst: "+getDoubleContent(AverageidenticalInst);
  
  
  Feature featuref = rf->Inbbfeature;
  int FTotalInst = get<0>(featuref); 
  vector<int> FInstSequence = get<1>(featuref); 
  vector<string> FInstVarSequence = get<2>(featuref);
  vector<int> FInstCount = get<3>(featuref); 
  vector<int> FBinaryOperatorSequence = get<4>(featuref); 
  vector<string> FFuncallSequence = get<5>(featuref); 
  

  Feature featurek = rk->Inbbfeature;
  int KTotalInst = get<0>(featurek);                                         
  vector<int> KInstSequence = get<1>(featurek);
  vector<string> KInstVarSequence = get<2>(featurek);
  vector<int> KInstCount = get<3>(featurek);
  vector<int> KBinaryOperatorSequence = get<4>(featurek);
  vector<string> KFuncallSequence = get<5>(featurek);

  double InstCountsimilarity= getSimilarity(FInstCount, KInstCount)*0.9;  
  
  int longerSeq = KTotalInst > FTotalInst ? KTotalInst : FTotalInst;
  int shoterSeq = KTotalInst < FTotalInst ? KTotalInst : FTotalInst;
  float InstRaio = (float)abs(FTotalInst-KTotalInst)/(float)longerSeq; 
  
  double funcsequenceSimilarity = 0;
  double FuncDistance = 0;
  
  
  vector<string> LongerFSequence, shorterFSequence;
  if(KFuncallSequence.size()<=FFuncallSequence.size()){
    shorterFSequence = KFuncallSequence;
    LongerFSequence = FFuncallSequence;
  }
  else{
    shorterFSequence = FFuncallSequence;
    LongerFSequence = KFuncallSequence;
  }
  
  if(LongerFSequence.size()==0)
    funcsequenceSimilarity = 0 ;
  else{
    FuncDistance =  editInstDistDPInstNew(LongerFSequence, shorterFSequence);
    funcsequenceSimilarity = 1-double(FuncDistance/(min(KFuncallSequence.size(),FFuncallSequence.size())+1));   
  }
  
  
  double instsequencesimilarity = InstsequenceSimilarity(KInstVarSequence,FInstVarSequence); 
  double neighborSimilarity = ObtainneighborSimilarity(rk, rf, MCSMap);
  if(InstRaio <= InstRaioThreshhod){ 
    IsMatch = AverageidenticalInst * weight11 + InstCountsimilarity * weight12 + 
    funcsequenceSimilarity* weight13 + instsequencesimilarity*weight14+ neighborSimilarity*weight15;
  }
  else{ 
    IsMatch = AverageidenticalInst * weight21 + InstCountsimilarity * weight22 + 
    funcsequenceSimilarity* weight23 + instsequencesimilarity*weight24+ neighborSimilarity*weight25;
  }
  return  make_tuple(IsMatch, identicalInsts, DeletedSSlist, InstRaio, content, instsequencesimilarity);
}


SigMatchResult SigMatch_Mul2One(bbl_info rk, bbl_info rf, std::map<int,int> *MCSMap){

  double weight11 = 0.1;  double weight21 = 0.1; 
  double weight12 = 0.2;  double weight22 = 0; 
  double weight13 = 0.3;  double weight23 = 0.3;
  double weight14 = 0.7;  double weight24 = 0.9;
  double weight15 = 0.3;  double weight25 = 0.3;
  bool changweight21 = false;

  string content = "\n\"SigMatch\":{";
  double IsMatch = 0; 
 
  vector<IdenticalInst> identicalInsts;
  SigMatchResult smr;
  map<llvm::Instruction*, int> DeletedSSlist;
  if(rf==NULL || rk==NULL){
    OP<<"Invaild bbl info.\n";
  }
  llvm::BasicBlock *bblk =  rk->bbl;
  llvm::BasicBlock *bblf =  rf->bbl;

  int BBLIDf = rf->BBLID;
  int BBLIDk = rk->BBLID;
  content = content +"\"BBLK\":" +getIntContent(BBLIDk)+"  \"BBLF\":" +getIntContent(BBLIDf);
  vector<llvm::Instruction*> KInstruction = rk->Instructions;
  vector<llvm::Instruction*> FInstruction = rf->Instructions;
  map<llvm::Instruction*, int> sensitive_Infok = rk->Sensitive_Info;
  map<llvm::Instruction*, int> sensitive_Infof = rf->Sensitive_Info; 
  if(BBLIDf < NewBasicBlockID){
    Instruction *lastInst =  &*(--bblf->end());
    if((lastInst)&&((isa<BranchInst>(lastInst))|| (isa<SwitchInst>(lastInst))|| (isa<SelectInst>(lastInst))) && (sensitive_Infof.find(lastInst) == sensitive_Infof.end()))
      sensitive_Infof.insert(make_pair(lastInst, scheck));
    }
  
  double identicalInst = 0.0; 
  double MaxidenticalInst = 0.0;  
  double SwitchidenticalInst = 0.0;  
  double AverageidenticalInst = 0.0; 
  #ifdef Debug_SM
    OP<<"sensitive_InfoK in basic block rk \n";
    Printmap(sensitive_Infok);
    OP<<"sensitive_InfoF in basic block rf\n";
    Printmap(sensitive_Infof);
  #endif
  content = content + "\nsensitive_InfoK" +Dumpmap(sensitive_Infok) + "\nsensitive_InfoF" +Dumpmap(sensitive_Infof);
  int Size_of_sensitive_Infok = sensitive_Infok.size();
  

  for(std::map<llvm::Instruction*, int>::iterator itk=sensitive_Infok.begin();
              itk != sensitive_Infok.end();itk++){
    bool IsInstkMatched = false; 
    Instruction *Instk = itk->first;
    int sensitive_typek = itk->second;
   
    for(std::map<llvm::Instruction*, int>::iterator itf=sensitive_Infof.begin();
              itf != sensitive_Infof.end();itf++){
      Instruction *Instf = itf->first; 
      int sensitive_typef = itf->second;
     
      #ifdef Debug_SM
      OP<<"sensitive_typek: "<<sensitive_typek<<"    sensitive_typef: "<<sensitive_typef<<"\n";
      content = content + "\nsensitive_typek" + getIntContent(sensitive_typek) +"    sensitive_typef: "+ getIntContent(sensitive_typef);
      #endif
      
      if(!Instk || !Instf)
        continue;
    
      if(sensitive_typek != sensitive_typef)
        continue;
      else{
        identicalInst = CompareInst_New(Instk,Instf);
        content = content + "\nInstk: "+ getInstContent(Instk) + " Instf: "+getInstContent(Instf) +   "  identicalInst:" + getDoubleContent(identicalInst);
        #ifdef Debug_SM
        OP<<"The similarity of two instructions is: "<<identicalInst<<"\n";
        #endif
        if(identicalInst>=0.75){  
            if(isa<SwitchInst>(Instk)){
                changweight21 = true;
                weight21 = 0.4;
                SwitchidenticalInst = identicalInst;
            }
            MaxidenticalInst = identicalInst > MaxidenticalInst ? identicalInst : MaxidenticalInst;
            AverageidenticalInst += identicalInst;
            std::pair<Instruction*, int> pairk = make_pair(Instk,rk->BBLID);
            std::pair<Instruction*, int> pairf = make_pair(Instf,rf->BBLID);
            DeleSensitiveItem(&sensitive_Infof,Instf); 
            IsInstkMatched = true ;
            content = content + "\nInstk: "+ getInstContent(Instk) + "\nInstf: "+getInstContent(Instf) + ";  similarity: "+ getDoubleContent(identicalInst) +"Matched: True";
            identicalInsts.push_back(make_tuple(pairk,pairf,identicalInst));
            break;
          }
        }
    }
    if(IsInstkMatched == false){
      DeletedSSlist[Instk]=sensitive_typek;
      content = content + "\nInstk: "+ getInstContent(Instk) +" is deleted.";
    }
  }
  if(Size_of_sensitive_Infok==0)
    AverageidenticalInst = 0;
  else{
    if(changweight21)
      AverageidenticalInst = SwitchidenticalInst;
    else
      AverageidenticalInst = AverageidenticalInst/Size_of_sensitive_Infok;
  }
  
  
  #ifdef Debug_SM
  OP<<" AverageidenticalInst "<<AverageidenticalInst<<"\n";
  #endif
  content = content + "\nAverageidenticalInst: "+getDoubleContent(AverageidenticalInst);
  
  
  Feature featuref = rf->Inbbfeature;
  int FTotalInst = get<0>(featuref); 
  vector<int> FInstSequence = get<1>(featuref); 
  vector<string> FInstVarSequence = get<2>(featuref);
  vector<int> FInstCount = get<3>(featuref); 
  vector<int> FBinaryOperatorSequence = get<4>(featuref); 
  vector<string> FFuncallSequence = get<5>(featuref); 
  

  
  Feature featurek = rk->Inbbfeature;
  int KTotalInst = get<0>(featurek);                                        
  vector<int> KInstSequence = get<1>(featurek);
  vector<string> KInstVarSequence = get<2>(featurek);
  vector<int> KInstCount = get<3>(featurek);
  vector<int> KBinaryOperatorSequence = get<4>(featurek);
  vector<string> KFuncallSequence = get<5>(featurek);
  double InstCountsimilarity= getSimilarity(FInstCount, KInstCount)*0.9;  
  
  int longerSeq = KTotalInst > FTotalInst ? KTotalInst : FTotalInst;
  int shoterSeq = KTotalInst < FTotalInst ? KTotalInst : FTotalInst;
  float InstRaio = (float)abs(FTotalInst-KTotalInst)/(float)longerSeq; 
  
  double funcsequenceSimilarity = 0;
  double FuncDistance = 0;
 
  
  vector<string> LongerFSequence, shorterFSequence;
  if(KFuncallSequence.size()<=FFuncallSequence.size()){
    shorterFSequence = KFuncallSequence;
    LongerFSequence = FFuncallSequence;
  }
  else{
    shorterFSequence = FFuncallSequence;
    LongerFSequence = KFuncallSequence;
  }
  
  if(LongerFSequence.size()==0)
    funcsequenceSimilarity = 0 ;
  else{
    FuncDistance =  editInstDistDPInstNew(LongerFSequence, shorterFSequence);
    funcsequenceSimilarity = 1-double(FuncDistance/(min(KFuncallSequence.size(),FFuncallSequence.size())+1));   
  }
  
  
  double instsequencesimilarity = InstsequenceSimilarity(KInstVarSequence,FInstVarSequence);
  double neighborSimilarity = ObtainneighborSimilarity(rk, rf, MCSMap);

  if(InstRaio <= InstRaioThreshhod){ 
    IsMatch = AverageidenticalInst * weight11 + InstCountsimilarity * weight12 + 
    funcsequenceSimilarity* weight13 + instsequencesimilarity*weight14;
  }
  else{ 
    IsMatch = AverageidenticalInst * weight21 + InstCountsimilarity * weight22 + 
    funcsequenceSimilarity* weight23 + instsequencesimilarity*weight24;
  }
  return  make_tuple(IsMatch, identicalInsts, DeletedSSlist, InstRaio, content, instsequencesimilarity);
}

Feature bblFeature(vector<Instruction*> Instructions){
  Feature feature;
  string FnName;
  vector<int> InstSequence;
  vector<int> InstCount;
  vector<int> BinaryOperatorSequence;
  vector<std::pair<int,vector<string>>> InstVarSequence;
  vector<string> InsStrtSequence;
  vector<string> InsStrtSequence_LineInfo;
  vector<string> FuncallSequence;
  int InstTotalCount=0; 
  
  int AugI=0, GlobalVI=0, alI=0, phI=0, boI=0, calcuaddrI=0, LSI=0, CMPI=0, transferI=0, CallI=0,otherI=0,GPI=0;
  for (vector<Instruction*>::iterator bbl_iter = Instructions.begin(); bbl_iter != Instructions.end(); ++bbl_iter) {
        InstTotalCount++;
        Instruction *Inst = *bbl_iter; 
        if(!Inst)
          continue;
        string SourceCodeInfo = ObtainSourceCodeInfoInst(Inst);
        string Inst_str("");
        
        raw_string_ostream stream(Inst_str);
        stream<<*Inst;        
        Inst_str = stream.str(); 
        Inst_str = Filter(Inst_str);
        InsStrtSequence.push_back(Inst_str);
        InsStrtSequence_LineInfo.push_back(Inst_str + SourceCodeInfo);
      
        int NumOperands = Inst->getNumOperands();
        vector<string> instoperandsType; 
        for(int i=0; i<NumOperands; i++){
  
          auto eachOperand = Inst->getOperand(i)->getName();
   
          auto type = Inst->getOperand(i)->getType();
          std::string type_str = "";
          llvm::raw_string_ostream rso(type_str);
          type->print(rso);
          instoperandsType.push_back(type_str);
        }
        int opc = Inst->getOpcode(); 
        string Instype = Inst->getOpcodeName(); 
        InstSequence.push_back(opc);  
        InstVarSequence.push_back(make_pair(opc,instoperandsType));
        
        if(isa<Argument>(Inst)){
            AugI++;
        }
        if(isa<GlobalVariable>(Inst))
            GlobalVI++;
        if(isa<GetElementPtrInst>(Inst))
            GPI++;
        else if(isa<ConstantInt>(Inst)){
            ConstantInt* CI = dyn_cast<ConstantInt>(Inst);
            llvm::APInt constIntValue = CI->getValue();
            Inst->getOpcodeName();
            }
        else if(isa<ConstantFP>(Inst)){
            ConstantFP* FI = dyn_cast<ConstantFP>(Inst);
            llvm::APFloat Floatvalue = FI->getValueAPF();
            float fpval = Floatvalue.convertToFloat(); 
        }
        else if(isa<ConstantArray>(Inst)){
            ConstantArray* AI = dyn_cast<ConstantArray>(Inst);
        }
        else if(isa<AllocaInst>(Inst))
            alI++;
        else if(isa<llvm::PHINode>(Inst))
            phI++;
        else if(isa<llvm::BinaryOperator>(Inst)){
            BinaryOperator *BO = dyn_cast<BinaryOperator>(Inst);
            string Instype = BO->getOpcodeName();
            int operation = BO->getOpcode();
            BinaryOperatorSequence.push_back(operation);
            boI++;
        }
        else if(isa<BitCastInst>(Inst)||isa<GetElementPtrInst>(Inst))
            calcuaddrI++;
        else if(isa<LoadInst>(Inst)||isa<StoreInst>(Inst))
            LSI++;
        else if(isa<ICmpInst>(Inst) || isa<CmpInst>(Inst))
            CMPI++;
        else if(isa<BranchInst>(Inst) || isa<SwitchInst>(Inst) ||isa<SelectInst>(Inst)) {
            transferI++;
        }
        else if(isa<CallInst>(Inst)){
              CallI++;
              CallInst *CI = dyn_cast<CallInst>(Inst);
              FnName = getCalledFuncName(CI);
              FuncallSequence.push_back(FnName); 
              }
        else{
          otherI++;
        }
  }

  InstCount.push_back(alI);  
  InstCount.push_back(phI); 
  InstCount.push_back(boI); 
  InstCount.push_back(AugI); 
  InstCount.push_back(CallI); 
  InstCount.push_back(CMPI);  
  InstCount.push_back(transferI); 
  InstCount.push_back(CallI);
  InstCount.push_back(otherI); 
  feature =make_tuple(InstTotalCount,InstSequence,InsStrtSequence,InstCount,BinaryOperatorSequence,FuncallSequence,InsStrtSequence_LineInfo);
  return feature;
}


int ObtainBBID(BasicBlock *BB , Mapbbl *KbasicBlockInfo){
  int BBID = -1;
  for(std::map<int,bbl_info>::iterator it = KbasicBlockInfo->begin(); it!= KbasicBlockInfo->end();it++){
    bbl_info b = it->second;
    if(BB == b->bbl){
      BBID = it->first;
      break;
    }   
  }
  return BBID;
}

bbl_info ObtainBBInfo(BasicBlock *BB, Mapbbl *basicBlockInfo)
{
  bbl_info bbl = NULL;
  for(std::map<int,bbl_info>::iterator it = basicBlockInfo->begin(); it!= basicBlockInfo->end();it++){
    if(it->second->bbl == BB){
        bbl = it->second;
        break;
     }     
  }
  return bbl;
}

bbl_info ObtainBBInfo(int BBLID, Mapbbl *basicBlockInfo){
  bbl_info bbl = NULL;
  Mapbbl::const_iterator pos = basicBlockInfo->find(BBLID);
  if (pos != basicBlockInfo->end()) 
    bbl = pos->second;
  return bbl;
}

std::set<BasicBlock*> ObtainBBs(std::set<int> S, Mapbbl *basicBlockInfo){
  std::set<BasicBlock*> BBInfo;
  for(auto s: S){
    bbl_info bbInfo = ObtainBBInfo(s, basicBlockInfo);
    if(bbInfo){
      BasicBlock *BB =  bbInfo->bbl;
      BBInfo.insert(BB);
    } 
  }
  return BBInfo;
}

// return the position of a inst in a basic block

int FindPosition(BasicBlock *BB, Instruction *I){
  int position = 0;
  for(BasicBlock::iterator iter=BB->begin();iter != BB->end(); iter++){
    Instruction *inst = &*iter;
    if(inst == I)
      return position;
    else
      position++;
  }
  return -1;
}



Instruction* getInst(Instruction *inst, int i){
  if(i>0){
    Instruction *after = inst;
    while(i>0){
      after = after->getNextNode();
      i--;
    }
    return after;
  }
  else if( i == 0)
    return inst;
  else{
    Instruction *previous = inst;
    while(i<0){
      previous = previous->getPrevNode();
      i++;
    }
    return previous;
  }
}

string getContext(Instruction *inst, int scope, BasicBlock *BB){
  string content = "";
  if(inst == NULL)
    return content;
  content = getInstContent(inst);
  for(int i = 1; i<=scope; i++){     
    Instruction *previous = getInst(inst, -i);
    if(previous != NULL)
      content = content + getInstContent(previous);
    Instruction *after = getInst(inst, i);
    if(after != NULL)
      content = content + getInstContent(after); 
  }
  return content;
}

Instruction* FilterCandidate(std::vector<Instruction*>  candidateInst, Instruction *intk,  BasicBlock*BBf){
  if(candidateInst.size() == 0)
    return NULL;
  else if(candidateInst.size() == 1)
    return candidateInst[0];
  else{
      BasicBlock *BBk = intk->getParent();
      std::vector<Instruction*> newcandidateIns1;
      string Stringintk1 = getContext(intk, 1, BBk);
      for(std::vector<Instruction*>::iterator iter1 = candidateInst.begin(); iter1 !=candidateInst.end(); iter1++ ){
          string Stringiter1 = getContext(*iter1, 1, BBf);
          if(Filter(Stringintk1) == Filter(Stringiter1))
            newcandidateIns1.push_back(*iter1);      
      }
      if(newcandidateIns1.size() == 0)
        return candidateInst[0];
      else if(newcandidateIns1.size() == 1)
        return newcandidateIns1[0];
      else{
        std::vector<Instruction*> newcandidateIns2;
        string Stringintk2 = getContext(intk, 2, BBk);
        for(std::vector<Instruction*>::iterator iter2 = newcandidateIns1.begin(); iter2 !=newcandidateIns1.end(); iter2++ ){
            string Stringiter2 = getContext(*iter2, 2, BBf);
            if(Filter(Stringintk2) == Filter(Stringiter2))
              newcandidateIns2.push_back(*iter2);      
        }
        if(newcandidateIns2.size() == 0)
          return newcandidateIns1[0];
        else if(newcandidateIns2.size() == 1)
          return newcandidateIns2[0];
        else{
          std::vector<Instruction*> newcandidateIns3;
          string Stringintk3 = getContext(intk, 3, BBk);
          for(std::vector<Instruction*>::iterator iter3 = newcandidateIns2.begin(); iter3 !=newcandidateIns2.end(); iter3++ ){
              string Stringiter3 = getContext(*iter3, 3, BBf);
              if(Filter(Stringintk3) == Filter(Stringiter3))
                newcandidateIns3.push_back(*iter3);      
          }
          if(newcandidateIns3.size() == 0)
            return newcandidateIns2[0];
          else
            return newcandidateIns3[0];
        } 
      }
    }
}


std::pair<Instruction*, int>  IsInMCS(std::map<int,int> *MCSMap, int BBIDk, Instruction *intk,  Mapbbl *FbasicBlockInfo){
  std::vector<Instruction*> candidateInst;
  string content = "\nInstruction: " + getInstContent(intk) + "\nBBIDk: " + getIntContent(BBIDk);
  int BBIDf = -1;
  BasicBlock *BBf;
  Instruction *instf=NULL;
  bbl_info bf=NULL;
  // If BBIDk in MCS
  for(std::map<int,int>::iterator it = MCSMap->begin(); it!=MCSMap->end();it++){
      if(it->first == BBIDk){
          BBIDf = it->second;
          if(BBIDf!= -1){
            for(std::map<int,bbl_info>::iterator it = FbasicBlockInfo->begin(); it!= FbasicBlockInfo->end();it++){
              if(it->first == BBIDf){
                  bf = it->second;
                  break;
              } 
            }
            if(bf!=NULL){
              BBf = bf->bbl;
              for(BasicBlock::iterator iter = BBf->begin();iter != BBf->end(); ++iter){
                Instruction *inst = &*iter;
                if(Filter(getInstContent(intk)) == Filter(getInstContent(inst)))
                  candidateInst.push_back(inst);     
              }
            } 
            instf = FilterCandidate(candidateInst, intk, BBf);      
          }
          break;
      }
  }
  
  return make_pair(instf,BBIDf) ;
}


bool Searchqueue(std::queue<Value*> q,  std::vector<Value*> VisitedElem, Value *x){ 
  std::queue<Value*> tmp = q;
  while(!tmp.empty()){
    if(tmp.front() == x)
      return true; 
    else
      tmp.pop();
  }
  for(std::vector<Value*>::iterator iter = VisitedElem.begin(); iter != VisitedElem.end(); iter++){
    if(*iter == x)
      return true;
  }
  return false;
} 

bool Searchqueue(std::queue<mul_key> q,  std::vector<mul_key> VisitedElem, mul_key x){ 
  std::queue<mul_key> tmp = q;
  while(!tmp.empty()){
    if(tmp.front() == x)
      return true; 
    else
      tmp.pop();
  }
  for(std::vector<mul_key>::iterator iter = VisitedElem.begin(); iter != VisitedElem.end(); iter++){
    if(*iter == x)
      return true;
  }
  return false;
} 

bool SearchUseSeq(USESEQ UseSeq, std::pair<Value*, Instruction*> pair){
    for(USESEQ::iterator it = UseSeq.begin(); it!=UseSeq.end();it++){
      if(it->first == pair.first && it->second == pair.second)
      //if( it->second == pair.second)
        return true;
    }
    return false;
}

bool SearchUseSeq(mul_USESEQ UseSeq, std::pair<mul_key, vector<Instruction*>> pair){
    for(mul_USESEQ::iterator it = UseSeq.begin(); it!=UseSeq.end();it++){
      if(it->first == pair.first && it->second == pair.second)
        return true;
    }
    return false;
}


void TranverseQueue(std::queue<Value*> queue){
  std::queue<Value*> q = queue;
  while (!q.empty()){
    Value *tmp = q.front();
    OP<<"\n"<<*tmp ;
    q.pop();
    }
}
/* 
Obtain the use sequence of an operand.
UseSeq (vector<std::pair<Value*, Instruction*>>) is used to store a value and the corresponding use( an instruction). 
q (a queue)is used to store the related values, e.g. if we trace the use of variable a, and we find that  a is assigned to b, then we also need to track the use sequence of b.
*/
//USESEQ is multimap<Value*, Instruction*>
USESEQ ObtainUseSeq(Value *operand){
  string content = "";
  content = content +"\nObtainUseSeq-1-27:\t";
  //OP<< "\nObtainUseSeq-1-27:\t";
  USESEQ UseSeq;
  std::queue<Value*> q;
  std::vector<Value*> VisitedElem;
  if(operand!=NULL)
    q.push(operand);
  
  while(!q.empty()){
    Value *op = q.front();
    q.pop();
   
    VisitedElem.push_back(op);
    int count = 0;

    for(auto U : op->users()){
          count++;
          Instruction *Inst = dyn_cast<Instruction>(U);
          if(Inst==NULL)
            continue;
         
          if(!SearchUseSeq(UseSeq, make_pair(op,Inst))){
            UseSeq.insert(make_pair(op,Inst));
            content = content +"\ninsert op: "+ getValueContent(op) + "\nInst:" + getInstContent(Inst)+ " +"+getIntContent( GetLocation(Inst));
          } 
         
          if(isa<StoreInst>(Inst)){ 
            StoreInst *Store = dyn_cast<StoreInst>(Inst) ; 
            Value *assignedValS = Store->getPointerOperand();
            if(!(assignedValS->getType())->isPointerTy()){
              OP<<"\nassignedValS is not a pointer.";
              continue;
            } 
            
            if(!Searchqueue(q, VisitedElem, assignedValS)){
              q.push(assignedValS); 
             
            }
          }
          //If the use is a Load inst, %a=load %struct.sk** %b
          else if(isa<LoadInst>(Inst)){ 
            LoadInst *Load = dyn_cast<LoadInst>(Inst);  
             if(!(Load->getType())->isPointerTy()){
              OP<<"\nLoad is not a pointer.";
              continue;
            } 
            if(!Searchqueue(q, VisitedElem, Load)){
              q.push(Load);
              
            }  
          }
          else if(isa<GetElementPtrInst>(Inst)){
            GetElementPtrInst *GPI = dyn_cast<GetElementPtrInst>(Inst); 
            if(!Searchqueue(q, VisitedElem, GPI)){
              q.push(GPI); 
             
            }
          }
          else if(isa<BitCastInst>(Inst)){
            BitCastInst *BCI = dyn_cast<BitCastInst>(Inst);  
            if(!Searchqueue(q, VisitedElem, BCI)){
              q.push(BCI); 
              
            } 
          }
          //a truncation of integer types
          else if(isa<TruncInst>(Inst)){
            TruncInst *TI = dyn_cast<TruncInst>(Inst);
            if(!Searchqueue(q, VisitedElem, TI)){
              q.push(TI);
              
            } 
          }
          else if(isa<SExtInst>(Inst)){
            SExtInst *SEI =dyn_cast<SExtInst>(Inst);
            if(!Searchqueue(q, VisitedElem, SEI)){
              q.push(SEI); 
             
            }
          }
          else if(isa<ZExtInst>(Inst)){
            ZExtInst *ZEI =dyn_cast<ZExtInst>(Inst);
            if(!Searchqueue(q, VisitedElem, ZEI)){
              q.push(ZEI); 
              
            }
          }
          else if(isa<IntToPtrInst>(Inst)){
            IntToPtrInst *ITP =dyn_cast<IntToPtrInst>(Inst);
            if(!Searchqueue(q, VisitedElem, ITP)){
              q.push(ITP); 
             
            }
          }
          else if(isa<PtrToIntInst>(Inst)){
            PtrToIntInst *PTI =dyn_cast<PtrToIntInst>(Inst);
            if(!Searchqueue(q, VisitedElem, PTI)){
              q.push(PTI); 
              
            }
          }
          else if(isa<ExtractValueInst>(Inst)){
            ExtractValueInst *EVI =dyn_cast<ExtractValueInst>(Inst);
            if(!Searchqueue(q, VisitedElem, EVI)){
              q.push(EVI); 
              
            }
          }
          else if(isa<ExtractElementInst>(Inst)){
            ExtractElementInst *EEI =dyn_cast<ExtractElementInst>(Inst);
            if(!Searchqueue(q, VisitedElem, EEI)){
              q.push(EEI); 
              
            }
          }
          else if(isa<BinaryOperator>(Inst)){
            BinaryOperator *BOI =  dyn_cast<BinaryOperator>(Inst);
            if(!(BOI->getType())->isPointerTy()){
              continue;
            }   
            if(!Searchqueue(q, VisitedElem, BOI)){
              q.push(BOI);
              
            }
          }
          
        } 
    
  }
  return UseSeq;
}


// inst is the original getelement instr, object_use is one use of %mskbl
string  Check_Pattern (Instruction *Inst, mul_USESEQ *useSeqk, Value *object , stack<string> Record){
  string content = "";
  
  std::queue<mul_key> Queue;
  std::vector<mul_key> VisitedElem;
  
  Queue.push(make_pair(Inst, Record));
  while(!Queue.empty()){
      mul_key op = Queue.front();
      Queue.pop();
      VisitedElem.push_back(op);

      Instruction *inst = op.first;

      stack<string> record = op.second;

      stack<string> record_tmp = record;

      string pattern = "";
      int pattern_length = record_tmp.size();

      while(!record_tmp.empty()) {
            pattern = pattern + record_tmp.top();
            record_tmp.pop();
      }

      for(auto U : object->users()){
          
          Instruction *object_use = dyn_cast<Instruction>(U);
          if(object_use == NULL)
            continue;
          
          content = content + "\nobject_use:" + getInstContent(object_use)+ " + " + getIntContent(GetLocation(object_use));
          
          string object_useSeq = "";
          vector<Instruction*> Inst_useSeqs ;

          BasicBlock *BB = object_use->getParent();
          content = content + "\nTranverse BB:";
         
          BasicBlock::iterator iter = BB->begin();
         
          while (iter != BB->end()) {
              Instruction *eachInst = &*iter;
              content = content + "\neachInst:" + getInstContent(eachInst);
              
              if((getInstContent(eachInst)) == (getInstContent(object_use))){
                BasicBlock::iterator iter_tmp  = iter;     
                int i = 0;
                while( (i < pattern_length) && (iter_tmp != BB->end()) ){
                    content = content + "\niter" + getInstContent(&*iter_tmp) ;
                    object_useSeq = object_useSeq + Filter_V1(getInstContent(&*iter_tmp));
                    Inst_useSeqs.push_back(&*iter_tmp);
                    i++;
                    iter_tmp++;
                }
                if(object_useSeq == pattern){
                  Instruction *NextInst = &*iter_tmp;
                  if(!SearchUseSeq(*useSeqk, make_pair(make_pair(inst, record), Inst_useSeqs)))
                    useSeqk->insert(make_pair(make_pair(inst, record), Inst_useSeqs));// determin propogation
                  
                  stack<string> record_tmp = record;

                  if(isa<StoreInst>(NextInst)){
                    StoreInst *Store = dyn_cast<StoreInst>(NextInst);  
                    if( (Store != NULL) && (Store->getOperand(0) == inst))
                    {
                      Value *assignedValS = Store->getOperand(1);
                      if(!(assignedValS->getType())->isPointerTy()){
                            iter++;
                            continue;
                        }
                      record_tmp.push(getValueContent(assignedValS)); 
                      if(!Searchqueue(Queue, VisitedElem, make_pair(NextInst, record_tmp))){    
                          Queue.push(make_pair(NextInst, record_tmp));
                         
                      }
                    }
                  }
                  else if(isa<LoadInst>(NextInst)){
                    LoadInst *Load = dyn_cast<LoadInst>(NextInst); 
                    if( (Load != NULL) && (Load->getOperand(0) == inst)){
                        if(!(Load->getType())->isPointerTy()){
                          iter++;
                          continue;
                        }
                        record_tmp.push(getInstContent(Load));
                        if(!Searchqueue(Queue, VisitedElem, make_pair(NextInst, record_tmp))){    
                          Queue.push(make_pair(NextInst, record_tmp));
                          
                        }  
                    }
                  }
                  else if(isa<GetElementPtrInst>(NextInst)){
                    GetElementPtrInst *GPI = dyn_cast<GetElementPtrInst>(NextInst); 
                    if( (GPI != NULL) && (GPI->getOperand(0) == inst)){
                        record_tmp.push(getInstContent(GPI));
                        if(!Searchqueue(Queue, VisitedElem, make_pair(NextInst, record_tmp))){    
                          Queue.push(make_pair(NextInst, record_tmp));
                         
                        }
                    }
                  }
                  else if(isa<BitCastInst>(NextInst)){
                    BitCastInst *BCI = dyn_cast<BitCastInst>(NextInst);  
                    if( (BCI != NULL) && (BCI->getOperand(0) == inst)){
                        record_tmp.push(getInstContent(BCI));
                        if(!Searchqueue(Queue, VisitedElem, make_pair(NextInst, record_tmp))){    
                          Queue.push(make_pair(NextInst, record_tmp));
                         
                        } 
                    }
                  }
                  else if(isa<TruncInst>(NextInst)){
                    TruncInst *TI = dyn_cast<TruncInst>(NextInst);
                    if( (TI != NULL) && (TI->getOperand(0) == inst)){
                        record_tmp.push(getInstContent(TI));
                        if(!Searchqueue(Queue, VisitedElem, make_pair(NextInst, record_tmp))){    
                          Queue.push(make_pair(NextInst, record_tmp));
                          
                        } 
                    }
                  }
                  else if(isa<SExtInst>(NextInst)){
                    SExtInst *SEI =dyn_cast<SExtInst>(NextInst);
                    if( (SEI != NULL) && (SEI->getOperand(0) == inst)){
                        record_tmp.push(getInstContent(SEI));
                        if(!Searchqueue(Queue, VisitedElem, make_pair(NextInst, record_tmp))){    
                        Queue.push(make_pair(NextInst, record_tmp));
                       
                        }
                    }
                  }
                  else if(isa<ZExtInst>(NextInst)){
                    ZExtInst *ZEI =dyn_cast<ZExtInst>(NextInst);
                    if( (ZEI != NULL) && (ZEI->getOperand(0) == inst)){
                        record_tmp.push(getInstContent(ZEI));
                        if(!Searchqueue(Queue, VisitedElem, make_pair(NextInst, record_tmp))){    
                          Queue.push(make_pair(NextInst, record_tmp));
                          
                        }
                    }
                  }
                  else if(isa<IntToPtrInst>(NextInst)){
                    IntToPtrInst *ITP =dyn_cast<IntToPtrInst>(NextInst);
                    if( (ITP != NULL) && (ITP->getOperand(0) == inst)){
                        record_tmp.push(getInstContent(ITP));
                        if(!Searchqueue(Queue, VisitedElem, make_pair(NextInst, record_tmp))){    
                          Queue.push(make_pair(NextInst, record_tmp));
                         
                        }
                    }
                  }
                  else if(isa<PtrToIntInst>(NextInst)){
                    PtrToIntInst *PTI =dyn_cast<PtrToIntInst>(NextInst);
                    if( (PTI != NULL) && (PTI->getOperand(0) == inst)){
                        record_tmp.push(getInstContent(PTI));
                        if(!Searchqueue(Queue, VisitedElem, make_pair(NextInst, record_tmp))){    
                          Queue.push(make_pair(NextInst, record_tmp));
                          
                        }
                    }
                  }
                  else if(isa<ExtractValueInst>(NextInst)){
                    ExtractValueInst *EVI =dyn_cast<ExtractValueInst>(NextInst);
                    if( (EVI != NULL) && (EVI->getOperand(0) == inst)){
                        record_tmp.push(getInstContent(EVI));
                        if(!Searchqueue(Queue, VisitedElem, make_pair(NextInst, record_tmp))){    
                          Queue.push(make_pair(NextInst, record_tmp));
                        
                        }
                    }
                  }
                  else if(isa<ExtractElementInst>(NextInst)){
                    ExtractElementInst *EEI =dyn_cast<ExtractElementInst>(NextInst);
                    if( (EEI != NULL) && (EEI->getOperand(0) == inst)){
                        record_tmp.push(getInstContent(EEI));
                        if(!Searchqueue(Queue, VisitedElem, make_pair(NextInst, record_tmp))){    
                          Queue.push(make_pair(NextInst, record_tmp));
                         
                        }
                    }
                  }
                  else if(isa<BinaryOperator>(NextInst)){
                    BinaryOperator *BOI =  dyn_cast<BinaryOperator>(NextInst);
                    OP<<"\nBOI:"<<*BOI;
                    if( (BOI != NULL) && (BOI->getOperand(0) == inst)){
                        if(!(BOI->getType())->isPointerTy()){
                          OP<<"\nBOI is not a pointer.";
                          iter++;
                          continue;
                        }   
                        record_tmp.push(getInstContent(BOI));
                        if(!Searchqueue(Queue, VisitedElem, make_pair(NextInst, record_tmp))){    
                          Queue.push(make_pair(NextInst, record_tmp));
                         
                        }
                    }
                  }

                }
              }
              iter++;
          }

      }
  }
  return content;
}


// inst is a getelement inst, record is the pattern, object is a local variable 
std::pair<mul_USESEQ, Value*> ObtainUseSeq(Instruction *inst,  std::vector<Value*> *args){
  // typedef std::multimap<std::pair<Instruction*, string>, vector<Instruction*>> mul_USESEQ;
  mul_USESEQ useSeqk;
  string content =  "\noperand: "+ getValueContent(inst) + " + " + getIntContent(GetLocation(inst));  
  // ObtainPatter 
  stack<string> record;
  Value *object = inst->getOperand(0);
  vector<Value*> VisitedElem;
  record.push(Filter_V1(getInstContent(inst)));
  while((args != NULL) && (args->size() != 0) && (find(args->begin(), args->end(), object) == args->end()) && (find(VisitedElem.begin(), VisitedElem.end(), object) == VisitedElem.end())){
    VisitedElem.push_back(object);
    Instruction *inst_sub = dyn_cast<Instruction>(object);
    // OP<<"\ninst_sub"<<*inst_sub;
    if(inst_sub == NULL)
      break;
    else{
      
      record.push(Filter_V1(getInstContent(inst_sub)));
      if(isa<GetElementPtrInst>(inst_sub))
        object = inst_sub->getOperand(0);
        
      else if(isa<LoadInst>(inst_sub))
        object = inst_sub->getOperand(0);
        
      else if(isa<StoreInst>(inst_sub)){
        if(inst_sub->getOperand(1) == object)
          object = inst_sub->getOperand(0);
      }
      else if(isa<BitCastInst>(inst_sub)){
        object = inst_sub->getOperand(0);
      }
    }
  }
 
  Check_Pattern(inst, &useSeqk, object, record); 
  return make_pair(useSeqk, object);
}



void PrintUseSeq(vector<vector<Instruction*>> UseSeq){
  for(vector<vector<Instruction*>>::iterator i=UseSeq.begin();i!=UseSeq.end(); i++){
    
    for(vector<Instruction*>::iterator inst=i->begin(); inst!=i->end(); inst++){
      if(*inst!=NULL)
      OP<<" "<<**inst<<"\n ";
    }
    OP<<"\n";
  }
}


void PrintUseSeq( vector<USESEQ>  *UseSeq){
  for( vector<USESEQ> ::iterator i = UseSeq->begin();i != UseSeq->end(); i++){
    OP<<"\nuseseq: ";
    for(USESEQ::iterator inst=i->begin(); inst!=i->end(); inst++){
      Value *operand = inst->first;
      Instruction *I = inst->second;
      OP<<"\nValue is:\t"<<*operand<<".\t instruction is:\t"<<*I;
    }
  }
}


void PrintMCS(std::map<int,int> *MCSMap){
  for(std::map<int,int>::iterator it =MCSMap->begin(); it!= MCSMap->end();it++){
    OP<<"[ "<<it->first<<"<-->"<<it->second<<"]\n";
  }
}


bool IsInMCS(std::map<int,int> *MCSMap, int BBIDK){
  for(std::map<int,int>::iterator it =MCSMap->begin(); it!= MCSMap->end();it++){
    if(it->first == BBIDK)
      return true;
  }
  return false;
}

bool IsValideOperand(Value *operand){
    if(operand == NULL)
          return false;
    else if(isa<ConstantExpr>(operand)){ //a constant value that is initialized with an expression using other constant values
       return false;
    }
    else if(isa<ConstantPointerNull>(operand)){
      OP<<"\noperandf is a NULL pointer.";
       return false;
    }
    else if(isa<ConstantDataSequential>(operand)){
       return false;
    }
    else if(isa<ConstantVector>(operand)){
       return false;
    }
    else if(isa<ConstantStruct>(operand)){ 
       return false;
    }
    else if(isa<ConstantArray >(operand)){
       return false;
    }
    else if(isa<ConstantInt>(operand)){
       return false;
    }
    else if(isa<ConstantFP>(operand)){
       return false;
    }
   else if(getValueContent(operand).find("preds")!=string::npos)
       return false;
   else if(getValueContent(operand).find("declare")!=string::npos)
       return false;
  else
    return true;
}


bool IsValideOperand(Instruction *instf, stack<string> record){
  stack<string> record_tmp = record;
  string pattern = "";
  int pattern_length = record_tmp.size();

  while(!record_tmp.empty()) {
        pattern = pattern + record_tmp.top();
        record_tmp.pop();
  }
  BasicBlock *BB = instf->getParent();
  BasicBlock::iterator iter = BB->end();
  while (iter != BB->begin()) {
      Instruction *eachInst = &*iter;
      if((getInstContent(eachInst)) == (getInstContent(instf))){
        stack<string> opf;
        string object_useSeq;
        BasicBlock::iterator iter_tmp  = iter;     
        int i = pattern_length;
        while( (i > 0) && (iter_tmp != BB->begin()) ){
            opf.push(Filter_V1(getInstContent(&*iter_tmp))); 
            i--;
            iter_tmp--;
        }
        while(!opf.empty()) {
            object_useSeq = object_useSeq + opf.top();
            opf.pop();
        }
        if(object_useSeq == pattern)
          return true;
      }
      iter--;
  }
  return false;
}

void InitializeBBLInfo(bbl_info b){
  vector<llvm::Instruction*> Insts;
  BasicBlock *BB = b->bbl;
  for(BasicBlock::iterator iter = BB->begin(); iter != BB->end(); ++iter){
    Instruction *inst = &*iter;
    Insts.push_back(inst);
  }
  b->Instructions = Insts;
}

Instruction* FindInstInBBL(BasicBlock *bf, Instruction *IK){
  Instruction *IF = NULL;
  for(BasicBlock::iterator iter = bf->begin(); iter != bf->end(); ++iter){
    Instruction *inst = &*iter;
    double similarity = CompareInst(IK,inst);
    if(similarity==1){
      IF = inst;
    } 
  } 
  return IF;  
}
// We find that value *op is the ith operand in Instruction *I
int FindPos(Value *op, Instruction *I){
  int pos = -1;
  for(int i=0; i<I->getNumOperands();i++){
      if(op == I->getOperand(i)){
         pos = i;
         break;
      }    
   }
   return pos;    
}
vector<Instruction*> FindUseList(USESEQ useSeqk, Value *op){
  vector<Instruction*> uselist;
  std::pair<USESEQIterator, USESEQIterator> result = useSeqk.equal_range(op);
  for (USESEQIterator it = result.first; it != result.second; it++)
        uselist.push_back(it->second);
  return uselist;
}

vector<vector<Instruction*>> FindUseList(mul_USESEQ useSeqk, mul_key op){
  vector<vector<Instruction*>>  uselist;
  std::pair<mul_USESEQIterator, mul_USESEQIterator> result = useSeqk.equal_range(op);
  for (mul_USESEQIterator it = result.first; it != result.second; it++)
        uselist.push_back(it->second);
  return uselist;
}

bool IsExist(Instruction *eachuse, vector<Instruction*>opfUses){
  bool exist = false;
  string contend = "";
  for(auto opfuse : opfUses){
    Instruction *fuse = dyn_cast<Instruction>(opfuse);
      if(Filter_V1(getInstContent(opfuse)) == Filter_V1(getInstContent(eachuse))){
       
        contend = contend + "\nComparedeachuse:" +  "+" +getIntContent( GetLocation(eachuse))+ "  opfuse: " +  "+" + getIntContent( GetLocation(fuse));
        exist = true;
        break;
      } 
  }
  if(!exist)
    contend = contend + "\nDeletedeachuse:" + Filter_V1(getInstContent(eachuse)) + "+" +getIntContent( GetLocation(eachuse));
  return exist;
}

bool IsExist(Instruction *eachuse, vector<vector<Instruction*>>opfUses){
  bool exist = false;
  string contend = "";
  for(auto opfUse : opfUses){
    Instruction *opfuse = opfUse[0];
    if(Filter_V1(getInstContent(opfuse)) == Filter_V1(getInstContent(eachuse))){
      contend = contend + "\neachuse:" + Filter_V1(getInstContent(eachuse)) + "+" + getIntContent( GetLocation(eachuse))+ "  opfuse: " + Filter_V1(getInstContent(opfuse))+ "+" + getIntContent( GetLocation(opfuse));
      exist = true;
      break;
    } 
  }
  if(!exist)
    contend = contend + "\nDeletedeachuse:" + Filter_V1(getInstContent(eachuse)) + "+" +getIntContent( GetLocation(eachuse));
  return exist;
}


string ObtainBU(std::vector<std::set<BasicBlock*>> Kbound){
  string contend ="";
  for(auto k : Kbound){
     for(auto bb : k){
       if(bb){
         for (BasicBlock::iterator KI_iter = bb->begin(); KI_iter != bb->end(); ++KI_iter) {
            Instruction *Inst = &*KI_iter;
            contend = contend + "\\n" + " +" + getIntContent(GetLocation(Inst));
            break;
         }
       }
     }
  }
  return contend;
}

string CompareUseList(vector<Instruction*> opkUselist, vector<Instruction*> opfUselist, Instruction *instk){
  string Stringinstk = Filter(getInstContent(instk));
  vector<Instruction*> tmp ;
  // we determine that if it is a false positive. For instance, if in bblk, there is a icmp a,b there is also a 
  // icmp instruction in bblf, then the reported deleted so is a false positive.
  for(vector<Instruction*>::iterator iterf=opfUselist.begin(); iterf != opfUselist.end(); iterf++){
      Instruction *If = *iterf;
      double InstSimilarity = CompareInst(instk, If);
      if(Filter(getInstContent(If)) == Stringinstk || InstSimilarity>0.7)
        return "FP";
   }
  
  for(vector<Instruction*>::iterator iterk=opkUselist.begin(); iterk != opkUselist.end(); iterk++){
        Instruction *Ik = *iterk;
        if(Ik != instk){
          tmp.push_back(Ik);
        }  
  }
  // We compare opkUselist and opfUselist
  if(tmp.size()!=opfUselist.size())
    return "N";
  for(int i = 0; i< opfUselist.size();i++){
    Instruction *IF =  opfUselist[i];
    Instruction *IK =  tmp[i]; // sequence should be the same
    double InstSimilarity = CompareInst(IK, IF); 
    if(InstSimilarity < 0.7){
      return "N";
    }   
  }
  return "Y";
}


string CompareUseList(vector<vector<Instruction*>> opkUselist, vector<vector<Instruction*>> opfUselist, Instruction *instk){
  string Stringinstk = Filter(getInstContent(instk));
  vector<vector<Instruction*>> tmp ;
  //OP<<"\nStringinstk:"<<Stringinstk;
  // we determine that if it is a false positive. For instance, if in bblk, there is a icmp a,b there is also a 
  // icmp instruction in bblf, then the reported deleted so is a false positive.
  for(vector<vector<Instruction*>>::iterator iterf=opfUselist.begin(); iterf != opfUselist.end(); iterf++){
      vector<Instruction*> eachuse = *iterf;
      Instruction *If = eachuse.back();
      double InstSimilarity = CompareInst(instk, If);
      if(Filter(getInstContent(If)) == Stringinstk || InstSimilarity > 0.7)
        return "FP";
   }
  // We need to exclude the deleted so.
  
  for(vector<vector<Instruction*>>::iterator iterk=opkUselist.begin(); iterk != opkUselist.end(); iterk++){
      vector<Instruction*> eachuse = *iterk;
      Instruction *Ik = eachuse.back();
      if(Ik != instk){
        tmp.push_back(eachuse);
      }  
  }
  // We compare opkUselist and opfUselist
  if(tmp.size()!=opfUselist.size())
    return "N";
  for(int i = 0; i< opfUselist.size();i++){
    vector<Instruction*> eachfuse = opfUselist[i];
    
    vector<Instruction*> eachkuse =  tmp[i];

    if(eachfuse.size() != eachkuse.size())
      return "N";
    
    for(int j = 0; j < eachfuse.size(); j++){
      Instruction *IF =  eachfuse[i];
      Instruction *IK =  eachkuse[i]; 
      double InstSimilarity = CompareInst(IK, IF);
      if(InstSimilarity < 0.7){
       
        return "N";
      }
    }    
  }
  return "Y";
}


std::vector<std::set<BasicBlock*>> GetBound(Instruction *deletedInst, Instruction *instk, int type, Mapbbl *KBasicBlockInfo){
  std::vector<std::set<BasicBlock*>> Bound;
  if(deletedInst != NULL){
   
    string content = "\ndeletedInst: " + getInstContent(deletedInst) + " +" + getIntContent(GetLocation(deletedInst)) + " type: " + getIntContent(type);
    content = content + "\ninstk: " + getInstContent(instk) + " +" + getIntContent(GetLocation(instk));
    if((type == 0) && (isa<BranchInst>(deletedInst) || isa<SwitchInst>(deletedInst) || isa<SelectInst>(deletedInst))){
        BranchInst *BI = dyn_cast<BranchInst>(deletedInst);
        SwitchInst *SI = NULL;
        SelectInst *SEI = NULL;
        if (BI) {
          if (BI->getNumSuccessors() < 2)
            return Bound;
        } 
        else {
          SI = dyn_cast<SwitchInst>(deletedInst);
          if(SI){
            if (SI->getNumSuccessors() < 2)
              return Bound;
          }
          else{
            SEI = dyn_cast<SelectInst>(deletedInst);
            if(SEI){
              OP<<"\nSEI: "<< *SEI;
             
            }
          }
        }
        BasicBlock *BB = deletedInst->getParent();
        int StartID = ObtainBBID(BB, KBasicBlockInfo);
        int EndID  = -1;
        Function *F = BB->getParent();
        int N = F->size();
        int Matrix[N][N];
        for(int i = 0 ; i < N; i++){
          for(int j = 0; j < N; j++ ){
              if(i == j)
                Matrix[i][j] = 1;
              else
                Matrix[i][j] = 0;
          }
        }

        std::set<int> L, R, left, right, VisitedElem;

        BasicBlock *leftbb = deletedInst->getSuccessor(0);
        int leftID = ObtainBBID(leftbb, KBasicBlockInfo);
        BasicBlock *rightbb = deletedInst->getSuccessor(1);
        int rightID =  ObtainBBID(rightbb, KBasicBlockInfo);
        L.insert(leftID);
        R.insert(rightID);
        left.insert(leftID);
        right.insert(rightID);
        Matrix[StartID][leftID] = 1;
        Matrix[StartID][rightID] = 1;
        
        //dump_buffer1(content, "bound1.txt"); 
        while(true){
          content = "";
          if(L.size() == 0 && R.size() == 0){
            OP<<"\n not found";
            break;
          }
          
          content = content + "\n*********************";
        
          
          std::set<int>  Lchildrennodes;
          std::set<int> Rchildrennodes;
          for (auto l : L){
              bbl_info bbInfo = ObtainBBInfo(l, KBasicBlockInfo);
              if(bbInfo == NULL)
                continue;
              int BBID  = bbInfo->BBLID;
              std::vector<int> Lchildrennodes_tmp = ObtainChildrenList(bbInfo);
              DeleteItem(&Lchildrennodes_tmp, BBID);

              std::set<int> tmp(Lchildrennodes_tmp.begin(), Lchildrennodes_tmp.end());
              Lchildrennodes = tmp;
              for(auto c : Lchildrennodes){
                  for(auto i :  left){
                      if(Matrix[i][l])
                          Matrix[i][c] = 1;              
                  }
              }     
          }
          
          for(auto r : R){
              bbl_info bbInfo = ObtainBBInfo(r, KBasicBlockInfo);
              if(bbInfo == NULL)
                continue;
              int BBID  = bbInfo->BBLID;
              std::vector<int> Rchildrennodes_tmp = ObtainChildrenList(bbInfo);
              DeleteItem(&Rchildrennodes_tmp, BBID);
              std::set<int> tmp(Rchildrennodes_tmp.begin(), Rchildrennodes_tmp.end());
              Rchildrennodes = tmp;
              for(auto c: Rchildrennodes){
                  for(auto i: right){
                    if(Matrix[i][r])
                        Matrix[i][c] = 1;
                  }
              }      
          }

          std::set<int>  New_L;
          for (auto l : L){
              bbl_info bbInfo = ObtainBBInfo(l, KBasicBlockInfo);
              if(bbInfo == NULL)
                continue;
              int BBID  = bbInfo->BBLID;
              std::vector<int> Lchildrennodes_tmp = ObtainChildrenList(bbInfo);
              DeleteItem(&Lchildrennodes_tmp, BBID);
              std::set<int> tmp(Lchildrennodes_tmp.begin(), Lchildrennodes_tmp.end());
              Lchildrennodes = tmp;
              New_L = MergeNode(New_L, Lchildrennodes);   
          }
          
          L = New_L;



          std::set<int>  New_R;
          for(auto r : R){
              bbl_info bbInfo = ObtainBBInfo(r, KBasicBlockInfo);
              if(bbInfo == NULL)
                continue;
              int BBID  = bbInfo->BBLID;
              std::vector<int> Rchildrennodes_tmp = ObtainChildrenList(bbInfo);
              DeleteItem(&Rchildrennodes_tmp, BBID);
              std::set<int> tmp(Rchildrennodes_tmp.begin(), Rchildrennodes_tmp.end());
              Rchildrennodes = tmp;
              New_R = MergeNode(New_R, Rchildrennodes);
          }
          R = New_R;
          
          VisitedElem = MergeNode(L, R, left, right); 
          
          std::vector<int> JoinNode;

          for(auto d : VisitedElem){

              bool Is_merged = true;

              for(auto s: VisitedElem){
                  
                  if(Matrix[s][d] == 0){
                      Is_merged = false;
                      content = content + "\nflag";
                      break;
                  }    
              }
              if(Is_merged){
                    JoinNode.push_back(d);
                   
              }
          }
          
          left = MergeNode(left, L);
          right = MergeNode(right, R);

         
          if(JoinNode.size() == 1){
            EndID = JoinNode[0];
            break;
          }
         
        }
        content = "\nEndID: " + getIntContent(EndID);

        std::set<BasicBlock*> Leftbound = ObtainBBs(left, KBasicBlockInfo);
        std::set<BasicBlock*> Rightbound = ObtainBBs(right, KBasicBlockInfo);
        Bound.push_back(Leftbound);
        Bound.push_back(Rightbound);

       
    }
    
    if(type == 1){
      std::set<BasicBlock*> bound;
      int Line = GetLocation(instk);
      content = content + "\nLine: " + getIntContent(Line);
      for(auto U : instk->users()){
       
        Instruction *use = dyn_cast<Instruction>(U);
        if(use == NULL)
          continue;
       
        if( GetLocation(U) <= Line){
          continue;
        }
        if(isa<StoreInst>(use)){
          break;
        }
        else
          {
            content = content + "\nadduse: " + getInstContent(use) + " +" + getIntContent(GetLocation(use));
            BasicBlock *BB = use->getParent();
            if(BB)
              bound.insert(BB);
          }
        OP<<"\nU is:\t"<<*U;
      }
      Bound.push_back(bound);
    }
    if(type == 4 ){
      std::set<BasicBlock*> bound;
      int Line = GetLocation(deletedInst);
      for(auto U : deletedInst->users()){
        if(GetLocation(U) <= Line)
          continue;
        Instruction *use = dyn_cast<Instruction>(U);
        BasicBlock *BB = use->getParent();
        if(BB)
          bound.insert(BB);  
        OP<<"\nU is:\t"<<*U;
      }
      Bound.push_back(bound);
    }
    if(type == 3){
      std::set<BasicBlock*> bound;
      int Line = GetLocation(deletedInst);
      for(auto U : deletedInst->users()){
        if(GetLocation(U) <= Line)
          continue;
        Instruction *use = dyn_cast<Instruction>(U);
        BasicBlock *BB = use->getParent();
        if(BB)
          bound.insert(BB);      
        OP<<"\nU is:\t"<<*U;
      }
      Bound.push_back(bound);
    }
  } 
  return Bound;
}

std::pair<string, bool> CompareBoundedUse(std::vector<std::set<BasicBlock*>> Kbound, int type, std::vector<std::vector<Instruction*>> opkUses, std::vector<std::vector<Instruction*>> opfUses){
  string contend = "";
  bool identical = false;
  contend = contend + "\n\"Bounded Uses\" :\"" + ObtainBU(Kbound) + "\",";
  if(type == 0){
    std::set<BasicBlock*> Leftbound = Kbound[0];
    std::set<BasicBlock*> Rightbound = Kbound[1];
    // if only one branch or both two branched matched, return true
    vector<Instruction*> LeftBranchUse;
    vector<Instruction*> RightBranchUse;
    vector<Instruction*> ALLUse;
    for(auto eachuse:  opkUses){
        Instruction *opkuse = eachuse[0];
        BasicBlock *BB = opkuse->getParent();
        if(Leftbound.find(BB) != Leftbound.end()){
          LeftBranchUse.push_back(opkuse);
          ALLUse.push_back(opkuse);
        }
        else if(Rightbound.find(BB) != Rightbound.end()){
          RightBranchUse.push_back(opkuse);
          ALLUse.push_back(opkuse);
        }
    }
    contend = contend + "\n\"LeftBranchUse\" :\"";
    for( vector<Instruction*>::iterator ii= LeftBranchUse.begin(); ii!= LeftBranchUse.end(); ii++){
            if((getInstContent(*ii).find("asm")!=string::npos) || (getInstContent(*ii).find("call")!=string::npos))
              contend = contend + "\\n"+ " +" + getIntContent(GetLocation(*ii));
            else
              contend = contend + "\\n" + " +" + getIntContent(GetLocation(*ii));
      }
    contend = contend + "\","; 
    // Dump right branch
    contend = contend + "\n\"RightBranchUse\" :\"";
    for( vector<Instruction*>::iterator ii= RightBranchUse.begin(); ii!= RightBranchUse.end(); ii++){
            if((getInstContent(*ii).find("asm")!=string::npos) || (getInstContent(*ii).find("call")!=string::npos))
              contend = contend + "\\n"+ " +" + getIntContent(GetLocation(*ii));
            else
              contend = contend + "\\n" + " +" + getIntContent(GetLocation(*ii));
      }
    contend = contend + "\","; 
    //only exist left branch
    bool matchres;
    if((LeftBranchUse.size() > 0) && (RightBranchUse.size() == 0) ){
      for(auto eachuse: LeftBranchUse){
          matchres = IsExist(eachuse, opfUses);
          if(matchres){
            identical = true;
            continue;
          }
          else
            identical = false;
      }
    }
    //only exist right branch
    else if((RightBranchUse.size() > 0) && (LeftBranchUse.size() == 0) ){
      for(auto eachuse: RightBranchUse){
          matchres = IsExist(eachuse, opfUses);
          if(matchres){
            identical = true;
            continue;
          }
          else
            identical = false;
      }
    }
    //exist two branches
    else if ( ALLUse.size() > 0){
      for(auto eachuse: ALLUse){
          matchres = IsExist(eachuse, opfUses);
          if(matchres){
            identical = true;
            continue;
          }
          else
            identical = false;
      }
    }
    contend = contend + "\n\"CU_identical\" :\"" + getBoolContent(identical) + "\",";
  }
  else if((type == 1) || (type == 3) || (type ==4)){
    std::set<BasicBlock*> bound = Kbound[0];
    vector<Instruction*> BranchUse;
    bool matchres;
    for(auto opkUse:  opkUses){
        Instruction *opkuse = opkUse[0];
        BasicBlock *BB = opkuse->getParent();
        if(bound.find(BB) != bound.end()){
          BranchUse.push_back(opkuse);
        }
    }
    // Dump BranchUse
    contend = contend + "\n\"InitUse\" :\"";
    for( vector<Instruction*>::iterator ii= BranchUse.begin(); ii!= BranchUse.end(); ii++){
            if((getInstContent(*ii).find("asm")!=string::npos) || (getInstContent(*ii).find("call")!=string::npos))
              contend = contend + "\\n"+ " +" + getIntContent(GetLocation(*ii));
            else
              contend = contend + "\\n" + " +" + getIntContent(GetLocation(*ii));
      }
    contend = contend + "\","; 

    for(auto eachuse: BranchUse){
          matchres = IsExist(eachuse, opfUses);
          if(matchres){
            identical = true;
            continue;
          }
          else
            identical = false;
      }
    contend = contend + "\n\"CU_identical\" :\"" + getBoolContent(identical) + "\",";
  }

  return std::make_pair(contend, identical);       
}

std::pair<string, bool> CompareBoundedUse(std::vector<std::set<BasicBlock*>> Kbound, int type, vector<Instruction*> opkUses, vector<Instruction*> opfUses){
  string contend = "";
  //bool identical = true;
  bool identical = false;
  contend = contend + "\n\"Bounded Uses\" :\"" + ObtainBU(Kbound) + "\",";
  if(type == 0){
    std::set<BasicBlock*> Leftbound = Kbound[0];
    std::set<BasicBlock*> Rightbound = Kbound[1];
    // if only one branch or both two branched matched, return true
    vector<Instruction*> LeftBranchUse;
    vector<Instruction*> RightBranchUse;
    vector<Instruction*> ALLUse;
    for(auto opkuse:  opkUses){
        BasicBlock *BB = opkuse->getParent();
        if(Leftbound.find(BB) != Leftbound.end()){
          LeftBranchUse.push_back(opkuse);
          ALLUse.push_back(opkuse);
        }
        else if(Rightbound.find(BB) != Rightbound.end()){
          RightBranchUse.push_back(opkuse);
          ALLUse.push_back(opkuse);
        }
    }

    // Dump left branch
    contend = contend + "\n\"LeftBranchUse\" :\"";
    for( vector<Instruction*>::iterator ii= LeftBranchUse.begin(); ii!= LeftBranchUse.end(); ii++){
            if((getInstContent(*ii).find("asm")!=string::npos) || (getInstContent(*ii).find("call")!=string::npos))
              contend = contend + "\\n"+ " +" + getIntContent(GetLocation(*ii));
            else
              contend = contend + "\\n" + " +" + getIntContent(GetLocation(*ii));
      }
    contend = contend + "\","; 
        
        
    // Dump right branch
    contend = contend + "\n\"RightBranchUse\" :\"";
    for( vector<Instruction*>::iterator ii= RightBranchUse.begin(); ii!= RightBranchUse.end(); ii++){
            if((getInstContent(*ii).find("asm")!=string::npos) || (getInstContent(*ii).find("call")!=string::npos))
              contend = contend + "\\n"+ " +" + getIntContent(GetLocation(*ii));
            else
              contend = contend + "\\n" + " +" + getIntContent(GetLocation(*ii));
      }
    contend = contend + "\","; 
    //only exist left branch
    bool matchres;
    if((LeftBranchUse.size() > 0) && (RightBranchUse.size() == 0) ){
      for(auto eachuse: LeftBranchUse){
          matchres = IsExist(eachuse, opfUses);
          if(matchres){
            identical = true;
            continue;
          }
          else
            identical = false;
      }
    }
    //only exist right branch
    else if((RightBranchUse.size() > 0) && (LeftBranchUse.size() == 0) ){
      for(auto eachuse: RightBranchUse){
          matchres = IsExist(eachuse, opfUses);
          if(matchres){
            identical = true;
            continue;
          }
          else
            identical = false;
      }
    }
    //exist two branches
    else if ( ALLUse.size() > 0){
      for(auto eachuse: ALLUse){
          matchres = IsExist(eachuse, opfUses);
          if(matchres){
            identical = true;
            continue;
          }
          else
            identical = false;
      }
    }
    contend = contend + "\n\"CU_identical\" :\"" + getBoolContent(identical) + "\",";
  }
  else if((type == 1) || (type == 3) || (type ==4)){
    std::set<BasicBlock*> bound = Kbound[0];
    vector<Instruction*> BranchUse;
    bool matchres;
    for(auto opkuse:  opkUses){
        BasicBlock *BB = opkuse->getParent();
        if(bound.find(BB) != bound.end()){
          BranchUse.push_back(opkuse);
        }
    }
    // Dump BranchUse
    contend = contend + "\n\"InitUse\" :\"";
    for( vector<Instruction*>::iterator ii= BranchUse.begin(); ii!= BranchUse.end(); ii++){
            if((getInstContent(*ii).find("asm")!=string::npos) || (getInstContent(*ii).find("call")!=string::npos))
              contend = contend + "\\n"+ " +" + getIntContent(GetLocation(*ii));
            else
              contend = contend + "\\n" + " +" + getIntContent(GetLocation(*ii));
      }
    contend = contend + "\","; 

    for(auto eachuse: BranchUse){
          matchres = IsExist(eachuse, opfUses);
          if(matchres){
            identical = true;
            continue;
          }
          else
            identical = false;
      }
    contend = contend + "\n\"CU_identical\" :\"" + getBoolContent(identical) + "\",";
  }
  return std::make_pair(contend, identical);
}
/*
  instk is the operand of deletedInst, i.e. the critical variable;

*/
string CompareUseList(Instruction *deletedInst, Instruction *instk, int type, USESEQ useSeqk, std::vector<CVRecord> CV_Use, Mapbbl *KBasicBlockInfo, Mapbbl *FBasicBlockInfo){
  string contend = "";
  bool identical = false;
  Value *opf = NULL;
  Instruction *instf = NULL;
  if(deletedInst != NULL)
    contend = contend + "\n\"CU_deletedInst\": \"" + getInstContent(deletedInst) + " +" + getIntContent(GetLocation(deletedInst))+  "\"," ;
  if(instk != NULL)
    contend = contend + "\n\"CU_instk\": \"" + getInstContent(instk) + " +" + getIntContent(GetLocation(instk)) +  "\"," ;
  // Fail to find the corresponding variables in Iot firmware.
  if(instk != NULL){
    // compare the uses of instk itself
    std::vector<std::set<BasicBlock*>> Kbound, Fbound;

    for(std::vector<CVRecord>::iterator iter = CV_Use.begin(); iter != CV_Use.end(); iter++){
      CVRecord cv = *iter;
      Value *opk = get<0>(cv);
      
      if(getValueContent(opk) == getInstContent(instk)){
        vector<Instruction*> opkUses = get<1>(cv);
        Value *opf = get<2>(cv);
        vector<Instruction*> opfUses = get<3>(cv);  
        // Record use
        contend = contend + "\n\"CU_opk\" : \""+getValueContent(opk) + " +" + getIntContent(GetLocation(opk)) + "\",\n\"CU_Kuse\" :\"";
        for( vector<Instruction*>::iterator ii= opkUses.begin(); ii!= opkUses.end(); ii++){
                if((getInstContent(*ii).find("asm")!=string::npos) || (getInstContent(*ii).find("call")!=string::npos))
                  contend = contend + "\\n"+ " +" + getIntContent(GetLocation(*ii));
                else
                  contend = contend + "\\n"+getInstContent(*ii) + " +" + getIntContent(GetLocation(*ii));
          }
        contend = contend + "\","; 
        // Record use Lines
        contend = contend + "\n\"CU_Kuse_Lines\" :\"";
        for( vector<Instruction*>::iterator ii= opkUses.begin(); ii!= opkUses.end(); ii++){
                if((getInstContent(*ii).find("asm")!=string::npos) || (getInstContent(*ii).find("call")!=string::npos))
                  contend = contend + "\\n"+ " +" + getIntContent(GetLocation(*ii));
                else
                  contend = contend + "\\n" + " +" + getIntContent(GetLocation(*ii));
          }
        contend = contend + "\","; 
        // Record use
        contend = contend + "\n\"CU_opf\" : \""+getValueContent(opf) + " +" + getIntContent(GetLocation(opf)) + "\",\n\"CU_Fuse\" :\"";
        for( vector<Instruction*>::iterator ii= opfUses.begin(); ii!= opfUses.end(); ii++){
                if((getInstContent(*ii).find("asm")!=string::npos) || (getInstContent(*ii).find("call")!=string::npos))
                  contend = contend + "\\n"+ " +" + getIntContent(GetLocation(*ii));
                else
                  contend = contend + "\\n"+getInstContent(*ii) + " +" + getIntContent(GetLocation(*ii));
          }
        contend = contend + "\","; 
        // Record use Lines
        contend = contend +  "\n\"CU_Fuse_Lines\" :\"";
        for( vector<Instruction*>::iterator ii= opfUses.begin(); ii!= opfUses.end(); ii++){
                if((getInstContent(*ii).find("asm")!=string::npos) || (getInstContent(*ii).find("call")!=string::npos))
                  contend = contend + "\\n"+ " +" + getIntContent(GetLocation(*ii));
                else
                  contend = contend + "\\n" + " +" + getIntContent(GetLocation(*ii));
          }
        contend = contend + "\","; 

        // Get the bound of uses
        Kbound = GetBound(deletedInst, instk, type, KBasicBlockInfo);
        if(Kbound.size() > 0){
          std::pair<string, bool> Res = CompareBoundedUse(Kbound, type, opkUses, opfUses);
          contend = contend + Res.first;
          identical = Res.second;
        }
        else
          contend = contend + "\n\"Kbound\" : \"Empty\",";
        break;
        
      }
    }
  }  
  return contend;
}


string CompareUseList(Instruction *deletedInst, Instruction *instk, int type, mul_USESEQ useSeqk, 
         std::vector<m_CVRecord> CV_Use, Mapbbl *KBasicBlockInfo, Mapbbl *FBasicBlockInfo){
      string contend = "";
      bool identical = false;
      Value *opf = NULL;
      Instruction *instf = NULL;
      if(deletedInst != NULL)
        contend = contend + "\n\"CU_deletedInst\": \"" + getInstContent(deletedInst) + " +" + getIntContent(GetLocation(deletedInst))+  "\"," ;
      if(instk != NULL)
        contend = contend + "\n\"CU_instk\": \"" + getInstContent(instk) + " +" + getIntContent(GetLocation(instk)) +  "\"," ;
      if(instk != NULL){
        std::vector<std::set<BasicBlock*>> Kbound, Fbound;
        for(std::vector<m_CVRecord>::iterator iter = CV_Use.begin(); iter != CV_Use.end(); iter++){
          m_CVRecord cv = *iter;
          mul_key opk = get<0>(cv);
          if(getInstContent(opk.first) == getInstContent(instk)){
            vector<vector<Instruction*>> opkUses = get<1>(cv);
            mul_key opf = get<2>(cv);
            vector<vector<Instruction*>> opfUses = get<3>(cv);  
            Kbound = GetBound(deletedInst, instk, type, KBasicBlockInfo);
            if(Kbound.size() > 0){
              std::pair<string, bool> Res = CompareBoundedUse(Kbound, type, opkUses, opfUses);
              contend = contend + Res.first;
              identical = Res.second;
            }
            else
              contend = contend + "\n\"Kbound\" : \"Empty\",";
            break;
          }
        }
      }
      identical = true;
      contend = contend + "\n\"CU_identical\" :\"" + getBoolContent(identical) + "\",";
      return contend;
}

string CheckSuccessor(Instruction *instk, Instruction *instf, Mapbbl *KBasicBlockInfo, Mapbbl *FBasicBlockInfo){
    if(instk == NULL || instf == NULL){
      OP<<"\nInvalidate Instruction.";
      return "";
    }
    BasicBlock *KBB = instk->getParent();
    BasicBlock *FBB = instf->getParent();
    if(KBB == NULL || FBB == NULL){
      OP<<"\nInvalidate Basicblock.";
      return "";
    }
    std::vector<size_t> KBBhash, FBBhash, intersection;
    int ksucc_no=0, fsucc_no=0;
    bbl_info kbbl, fbbl;
    for (succ_iterator kbiter = succ_begin(KBB), keiter = succ_end(KBB); kbiter != keiter; ++kbiter) {
      BasicBlock *KSuccBB = *kbiter;
      kbbl = ObtainBBInfo(KSuccBB, KBasicBlockInfo);
      KBBhash.push_back(kbbl->BBhash);
      ksucc_no++;
    }
    for (succ_iterator fbiter = succ_begin(FBB), feiter = succ_end(FBB); fbiter != feiter; ++fbiter) {
      BasicBlock *FSuccBB = *fbiter;
      fbbl = ObtainBBInfo(FSuccBB, FBasicBlockInfo);
      FBBhash.push_back(fbbl->BBhash);
      fsucc_no++;
    }
    std::set_intersection(KBBhash.begin(),KBBhash.end(),
                          FBBhash.begin(),FBBhash.end(),
                          back_inserter(intersection));
    if(intersection.size()>0)
      return "FP";
    else
      return "Continue analyze.";
}

bbl_info FindSimilarBB(bbl_info kbbl, Mapbbl *FBasicBlockInfo, std::vector<int> *remain_graph2, std::map<int,int> *MCSMap){
  bbl_info fbbl = NULL;
  int kbblID = kbbl->BBLID;
  int fbblID = -1;
  // Check if kbbl is in MCS
  for(std::map<int,int>::iterator iter = MCSMap->begin(); iter != MCSMap->end(); iter++){
    if(iter->first == kbblID){
      fbblID = iter->second;
      fbbl = ObtainBBInfo(fbblID, FBasicBlockInfo);
      break;
    }
  }
  // If kbbl is not in MCS, match it in remain_graph
  if(fbbl == NULL){
    for(std::vector<int>::iterator iter = remain_graph2->begin(); iter != remain_graph2->end(); iter++){
      bbl_info bbl = ObtainBBInfo(*iter, FBasicBlockInfo);
      SigMatchResult smr = SigMatch(kbbl,bbl,MCSMap);
      int Similarity = get<0>(smr); 
      if(Similarity < Threshhod)
        continue;
      else 
        fbbl = bbl;
    }
  }
  return fbbl;
}

// if KBB and FBB have high similarity, we find instf in FBB
Instruction* LocateInst(BasicBlock *KBB, Mapbbl *KBasicBlockInfo, BasicBlock *FBB, Mapbbl *FBasicBlockInfo, Instruction *instk, std::map<int,int> *MCSMap){
  SigMatchResult smr = SigMatch(ObtainBBInfo(KBB, KBasicBlockInfo), ObtainBBInfo(FBB, FBasicBlockInfo), MCSMap);
  Instruction *instf;
  std::vector<Instruction*> candidateInst;
  int Similarity = get<0>(smr); 
  if(Similarity < Threshhod)
    instf = NULL;
  else {
    for(BasicBlock::iterator iter = FBB->begin();iter != FBB->end(); ++iter){
      Instruction *inst = &*iter;
      if(Filter(getInstContent(instk)) == Filter(getInstContent(inst)))
        candidateInst.push_back(inst);     
    }
    instf = FilterCandidate(candidateInst, instk, FBB); 
  } 
  return instf;
}

/*
  Since we cannot match the basic block(BB)  which instk is in, we furtherly check the successor and processor of BB.
*/
string CheckFP(Instruction *instk, string filename,  Mapbbl *KBasicBlockInfo, Mapbbl *FBasicBlockInfo,std::vector<int> *remain_graph2, std::map<int,int> *MCSMap){
    if(instk == NULL){
      OP<<"\nInvalidate Instruction.";
      return "Invalidate Instruction";
    }
    BasicBlock *KBB = instk->getParent();
    if(KBB == NULL){
      OP<<"\nInvalidate Basicblock.";
      return "Invalidate Basicblock.";
    }
    Instruction *instf = NULL;
    int ksucc_no=0, fsucc_no=0;
    bbl_info kbblInfo, fbblInfo;
    // Search successors of instk
    for (succ_iterator kbiter = succ_begin(KBB), keiter = succ_end(KBB); kbiter != keiter; ++kbiter) {
      BasicBlock *KSuccBB = *kbiter;
      if(KSuccBB == NULL)
        continue;
      kbblInfo = ObtainBBInfo(KSuccBB, KBasicBlockInfo);
      if(kbblInfo == NULL)
        continue;
      fbblInfo = FindSimilarBB(kbblInfo, FBasicBlockInfo, remain_graph2, MCSMap);
      if(fbblInfo == NULL)
        continue;
      BasicBlock *FSuccBB = fbblInfo->bbl;
      if(FSuccBB == NULL)
        continue;
      for (auto it = pred_begin(FSuccBB), et = pred_end(FSuccBB); it != et; ++it){
        BasicBlock* FBB = *it;
        if(FBB != NULL)
          instf = LocateInst(KBB, KBasicBlockInfo, FBB, FBasicBlockInfo, instk, MCSMap);
      }
    }
    // If we cannot find instf in the successors of instk, Seatch Processor of instk.
    if(instf == NULL){
      for (auto kbiter = pred_begin(KBB), keiter = pred_end(KBB); kbiter != keiter; ++kbiter) {
        BasicBlock *KPressorBB = *kbiter;
        if(KPressorBB == NULL)
          continue;
        kbblInfo = ObtainBBInfo(KPressorBB, KBasicBlockInfo);
        if(kbblInfo == NULL)
          continue;
        fbblInfo = FindSimilarBB(kbblInfo, FBasicBlockInfo, remain_graph2, MCSMap);
        if(fbblInfo == NULL)
          continue;
        BasicBlock *FPressorBB = fbblInfo->bbl;
        if(FPressorBB == NULL)
          continue;
        for (succ_iterator fbiter = succ_begin(FPressorBB), feiter = succ_end(FPressorBB); fbiter != feiter; ++fbiter){
          BasicBlock* FBB = *fbiter;
          if(FBB != NULL)
            instf = LocateInst(KBB, KBasicBlockInfo, FBB, FBasicBlockInfo, instk, MCSMap);
        }
      }
    }
    if(instf != NULL)
      return "FP";
    else
      return "Unknown";
}


std::vector<Value*> Getargs(Function *F){
  std::vector<Value*> fargs;
  for (Function::arg_iterator iters = F->arg_begin(), itere = F->arg_end();
                             iters != itere; ++iters){
            //Instruction *Inst =  &*iters;
            OP<<"\nFunction name:"<<F->getName();
            OP<<"\narg:"<< *iters;
            fargs.push_back(&*iters);
   }
  for (Function::iterator FB_iter = F->begin(); FB_iter != F->end(); ++FB_iter){
      BasicBlock *FcurBB = &*FB_iter;
      for(BasicBlock::iterator iter = FcurBB->begin(); iter!= FcurBB->end(); iter++){
            Instruction *instr = &*iter;
            if(isa<AllocaInst>(instr) && (find(fargs.begin(), fargs.end(),  instr) == fargs.end()))
                fargs.push_back(instr);
            if(isa<GlobalVariable>(instr) && (find(fargs.begin(), fargs.end(),  instr) == fargs.end()))
                fargs.push_back(instr);
      }
  }
  return fargs;
}

/*
Find the real critical variable.
instk: %tobool301 = icmp ne %struct.usb_endpoint_descriptor* %155, null, !dbg !4506",
       %cmp270 = icmp ne i32 %conv269, 3, !dbg !4448";
       %conv269 = zext i8 %137 to i32, !dbg !4443"
       %call290 = call i32 @usb_endpoint_is_bulk_in(%struct.usb_endpoint_descriptor* %150) #7, !dbg !4490"
       %153 = load %struct.usb_endpoint_descriptor*, %struct.usb_endpoint_descriptor** %epctrl, align 4, !dbg !4501" : %epctrl
       %cmp767 = icmp eq %struct.urb* %367, null, !dbg !5008"	> if (snd->urb == NULL) : urb, NULL
       %367 = load %struct.urb*, %struct.urb** %urb766, align 4, !dbg !5007"
*/


std::tuple<bool, string, string> FurtherCheckUseSequence(Instruction *deletedInst, Instruction *instk, string filename, Mapbbl *KbasicBlockInfo, Mapbbl *FbasicBlockInfo,
                 std::vector<int> *remain_graph2, std::map<int,int> *MCSMap, int type){
      string content;
      std::queue<Value*> OperandQue;
      std::vector<Value*> VisitedElem;
      std::tuple<bool, string, string>  CheckRes;
      bool  ExistKUseSeq;
      string UseSeqmatch;

      if(CallInst *call_inst = dyn_cast<CallInst>(instk)){
          // Check if the CallInst has return value, Obtain the real critical variable
          OP<<"\nCallInst:"<<*call_inst<<", lineno: " << GetLocation(call_inst);
          Value *operand = NULL;        
          for(auto U : call_inst->users()){
            Instruction *use = dyn_cast<Instruction>(U);
            OP<<"\nCallInst use:"<<*use<<", lineno: " << GetLocation(use);
            if(use == NULL)
              continue;
            if((isa<StoreInst>(use)) && (dyn_cast<Instruction>(use->getOperand(0)) == call_inst)){
                OP<<"\nCallInst use Store:"<<*use<<", lineno: " << GetLocation(use);
              operand = (use->getOperand(1));
              OP<<"\nCallInst use Store operand:"<<*operand<<", lineno: " << GetLocation(operand);
              if(!IsValideOperand(operand) || operand == NULL )
                continue;
              OperandQue.push(operand);  
            }
          }
          // if there is no return inst for this callinst
          if( operand == NULL){
              OP<<"\nCall Inst parameter:";
              Function* fn = call_inst->getCalledFunction();
              if(fn != NULL){
                int i = 0;
                for(auto arg = fn->arg_begin(); arg != fn->arg_end(); ++arg) {
                    //operand = &*arg;
                    operand = call_inst->getArgOperand(i);
                    i++;
                    if(!IsValideOperand(operand) || operand == NULL)
                      continue;                   
                    OperandQue.push(operand);
                    OP<<"\noperand:"<<*operand;
                }
              }
          }
      }
      else{               
          for(int i = 0; i < instk->getNumOperands(); i++){    
              Value *operand = instk->getOperand(i); 
              if(!IsValideOperand(operand) || operand == NULL )
                continue;
              OperandQue.push(operand);                                        
          }
      }

      int jsoncount = 0;
      while(!OperandQue.empty()){
        Value *operand = OperandQue.front();
        OperandQue.pop();
        VisitedElem.push_back(operand);
        
        Instruction *inst_op = dyn_cast<Instruction>(operand);
        if(inst_op == NULL)
          continue;
        jsoncount ++;
        CheckRes = CheckUseSequence(deletedInst, inst_op, filename, KbasicBlockInfo, FbasicBlockInfo, 
                                          remain_graph2, MCSMap,  type);
        ExistKUseSeq = get<0>(CheckRes);
        UseSeqmatch = get<1>(CheckRes);
        OP<<"\n*operand: "<<*operand;
        OP<<"\nExistKUseSeq: "<<ExistKUseSeq;
        if(jsoncount != 1)
          content = content + ",";
        content = content + get<2>(CheckRes); 
        
        if(ExistKUseSeq == false){
          if(CallInst *call_inst = dyn_cast<CallInst>(inst_op)){
              OP<<"\n*getCalledFunction: ";
              Function* fn = call_inst->getCalledFunction();
              if(fn != NULL){
                
                int i = 0;
                for(auto arg = fn->arg_begin(); arg != fn->arg_end(); ++arg) {
                   
                    Value *op = call_inst->getArgOperand(i);
                    i++;
                    OP<<"\n*op: "<<*op;
                    if(!IsValideOperand(op) || op == NULL)
                      continue;                   
                    if(!Searchqueue(OperandQue, VisitedElem, op))
                      OperandQue.push(op);     
                }
              }
          }
        else{               
            for(int i = 0; i < inst_op->getNumOperands(); i++){    
                Value *op = inst_op->getOperand(i); 
                if(!IsValideOperand(op) || op == NULL)
                  continue;
                if(!Searchqueue(OperandQue, VisitedElem, op))
                  OperandQue.push(op);                                                        
            }
          }
        }
      }

  return make_tuple(ExistKUseSeq, UseSeqmatch, content);
}


// instk is the operand of the deletedInst
std::tuple<bool, string, string> CheckUseSequence(Instruction *deletedInst, Instruction *instk,  string filename, Mapbbl *KbasicBlockInfo, Mapbbl *FbasicBlockInfo,
                 std::vector<int> *remain_graph2, std::map<int,int> *MCSMap, int type){                 
     
    Function *K = instk->getParent()->getParent();
    std::vector<Value*> Kfargs = Getargs(K);
    StringRef funcName = K->getName();
    string LineInfo = ObtainSourceCodeInfoInst(deletedInst); 
    int lineno = GetLocation(instk);
    bool Ismatch = false;  // The match of instruction
    bool ExistTwoUseSeq = false; // The match of use sequences
    bool ExistKUseSeq = false;  // opk contains use or not
    string UseSeqmatch = "N";
    string content; // record log
    
    content = "\n{\"AItem" + getIntContent(type) + "\" : { ";
    content = content +"\n\"FucName\": \"" + funcName.str() + "\",  \n\"Sensitive Inst\": \"" + getInstContent(instk)+ "\",  \n\"type\": \"" + getIntContent(type) + "\",\n\"LineInfo\": \""+ LineInfo+"\"," ;

    

    if(isa<GetElementPtrInst>(instk))
    {
        
        int countuse = 0;
        std::pair<mul_USESEQ, Value*> KRes = ObtainUseSeq(instk, &Kfargs);
        mul_USESEQ useSeqk = KRes.first;
        content = content +"\n\"UseSize\": \"" + getIntContent(useSeqk.size()) + "\", ";
        content = content +"\n\"Use\": [" + DumpUseSeq(useSeqk) + "], ";
        
        Instruction *instf = NULL;
        int basicblockIDf = -1;

        std::map<mul_key, mul_key> CriticalValue;
        std::vector<std::tuple<mul_key, vector<vector<Instruction*>> , mul_key, vector<vector<Instruction*>>>> CV_Use;

        
        if(GetUseNo(useSeqk) < 2){
     
              ExistKUseSeq = false;
              goto MInext;
        }
        ExistKUseSeq = true;
        content = content + "  \n\"MIMCSUseCmp\":" + "[";
        for(mul_USESEQ::iterator iterk = useSeqk.begin(), itere = useSeqk.end(); iterk != itere; ++iterk){        
          
          std::pair<Instruction*, stack<string>> op = iterk->first;  // key
          
          if( CriticalValue.find(op) != CriticalValue.end() )
              continue;

          vector<Instruction*> opkUse = iterk->second; // use
          
          stack<string> pattern = op.second;  

          Instruction *I = opkUse.back(); // the last inst of opkUse: I is always a getelement instruction.
          
          OP<<"\nInstruction *I"<<*I;
          BasicBlock *BB = I->getParent();
          if(BB == NULL)
            continue;
          int basicblockIDk = ObtainBBID(BB,KbasicBlockInfo); 
          if(basicblockIDk == -1)
            continue;
          countuse++;
          std::pair<Instruction*, int>  matchResult = IsInMCS(MCSMap, basicblockIDk, I, FbasicBlockInfo);
          
          Instruction *instf = matchResult.first; 
          int basicblockIDf = matchResult.second;
          // a valide instf should follow the pattern.
          if(instf == NULL || !IsValideOperand(instf)){
            #ifdef RECORD
              vector<vector<Instruction*>> opkUselist = FindUseList(useSeqk, op);
                // Record in logs. Output opk and all the use of it.
              if(countuse != 1)
                  content = content + ",";
                
              content = content + "\n{\"opk\" : \""+getInstContent(op.first) + " +"+getIntContent(GetLocation(op.first))+ "\",\n\"Pattern\":\"" + Dumpstack(op.second) + "\",\n\"Kuse\" :\"";
          
              for( vector<vector<Instruction*>>::iterator ii= opkUselist.begin(); ii!= opkUselist.end(); ii++){
                  vector<Instruction*> eachuse = *ii;
                  Instruction *lastInst = eachuse.back();
                  if((getInstContent(lastInst).find("asm")!=string::npos) || (getInstContent(lastInst).find("call")!=string::npos))
                    content = content + "\\n"+ " +" + getIntContent(GetLocation(lastInst));
                  else
                    content = content + "\\n"+getInstContent(lastInst) + " +" + getIntContent(GetLocation(lastInst));
              }
              content = content + "\",";
              content = content + "\n\"KI\": \""+ getInstContent(I)+ " +" + getIntContent(GetLocation(I))+"\",";
              content = content + "\n\"FI\":  \"NULL\"} ";
            #endif
            continue;
          }

          Ismatch = true;
          #ifdef RECORD
            // Record in logs. Output opk and all the use of it.
            vector<vector<Instruction*>> opkUselist = FindUseList(useSeqk,op);
            if(countuse != 1)//{
              content = content + ",";
            content = content + "\n{\"opk\" : \""+getInstContent(op.first) + " +"+getIntContent(GetLocation(op.first))+ "\",\n\"Pattern\":\"" + Dumpstack(op.second) + "\",\n\"Kuse\" :\"";
          
            for( vector<vector<Instruction*>>::iterator ii= opkUselist.begin(); ii!= opkUselist.end(); ii++){
                  vector<Instruction*> eachuse = *ii;
                  Instruction *lastInst = eachuse.back();
                  if((getInstContent(lastInst).find("asm")!=string::npos) || (getInstContent(lastInst).find("call")!=string::npos))
                    content = content + "\\n"+ " +" + getIntContent(GetLocation(lastInst));
                  else
                    content = content + "\\n"+getInstContent(lastInst) + " +" + getIntContent(GetLocation(lastInst));  
            }
            content = content + "\",";
            content = content + "\n\"KI\": \""+ getInstContent(I)+ " +" + getIntContent(GetLocation(I)) + "\",";
            content = content + "\n\"FI\": \""+ getInstContent(instf)+ " +" + getIntContent(GetLocation(instf)) + "\",";
          #endif

          #ifdef RECORD
            content = content +  "\n\"basicblockIDk\" : \""+getIntContent(basicblockIDk)+"\",\n\"basicblockIDf\" : \""
            +getIntContent(basicblockIDf)+ "\", \n\"opk(ninstk)\" : \""+getInstContent(op.first) + " +"+getIntContent(GetLocation(op.first))+ "\",\n\"Chooseduse\" : \""+getInstContent(I)+
            " +"+getIntContent(GetLocation(I))+ "\",\n\"instf\" : \""+getInstContent(instf) + " +"+getIntContent(GetLocation(instf)) + "\",\n\"operandF\": \""+getInstContent(instf)+
            " +"+getIntContent(GetLocation(instf))+"\",";
          #endif
          Function *F = instf->getParent()->getParent();
          OP<<"\nFunction F1 name:";
          std::vector<Value*> Ffargs = Getargs(F);
    
          std::pair<mul_USESEQ, Value*> FRes = ObtainUseSeq(instf, &Ffargs); 
          mul_USESEQ useSeqf = FRes.first;

          if(useSeqf.size() == 0)
            continue;
          mul_key operandf = make_pair(instf, pattern);

          vector<vector<Instruction*>> opfUselist = FindUseList(useSeqf, operandf);

          CriticalValue.insert(make_pair(make_pair(I, pattern), operandf));
          CV_Use.push_back(make_tuple(make_pair(I, pattern), opkUselist, operandf, opfUselist));

          content = content + "\n\"opf\" : \""+getInstContent(instf)+"\",\n\"Fuse\" :\"";
          for( vector<vector<Instruction*>>::iterator ii= opfUselist.begin(); ii!= opfUselist.end(); ii++){
                  vector<Instruction*> eachuse = *ii;
                  Instruction *lastInst = eachuse.back();
                  content = content + "\\n"+getInstContent(lastInst) + " +" + getIntContent(GetLocation(lastInst));
                  //OP<<"\n"+getInstContent(*ii) + " +" + getIntContent(GetLocation(*ii));
            }
              
          content = content + "\",";
          UseSeqmatch = CompareUseList(opkUselist, opfUselist, instk);
          content = content + "\n\"Match results\": \""+ UseSeqmatch+"\"}";
          if(UseSeqmatch == "FP1" || UseSeqmatch == "Y1"){
          //if(UseSeqmatch == "FP" || UseSeqmatch == "Y"){
            if(UseSeqmatch == "FP"){
              string bcfile = splitStr(filename,"/")+".bc";
              string FPRecord =  (string)DATA_DIR+ "../result/"+RecordDate+"/FPRecord-"+kernel_eddition+".txt";
              dump_buffer1(bcfile+" +" + getIntContent(lineno) +": "+ funcName.str()+": FP (trace use)\n",FPRecord);
            }
            ExistTwoUseSeq = true;
            content = content + "]";
            goto MInext; 
          }  
        }        
        
        content = content + "],";
        content = content + "  \n\"NonMCSUseCmp\":" + "[";
        if(useSeqk.size()!=0){
          int jsoncount =0;
            for(mul_USESEQ::iterator iterk = useSeqk.begin(), itere = useSeqk.end(); iterk != itere; ++iterk){ 
              
              std::pair<Instruction*, stack<string>> op = iterk->first;  // key

              if( CriticalValue.find(op) != CriticalValue.end() )
                  continue;

              vector<Instruction*> opkUse = iterk->second; // use
              
              stack<string> pattern = op.second;  
              Instruction *IK = opkUse.back(); // 

              BasicBlock *bk = IK->getParent();
              bbl_info bblk = ObtainBBInfo(bk, KbasicBlockInfo);
              if(bblk==NULL)
                  continue;
              int basicblockIDk = bblk->BBLID;
              if(basicblockIDk == -1)
                continue;

              for(std::vector<int>::iterator it = remain_graph2->begin(); it!=remain_graph2->end();it++){
                bbl_info bblf = ObtainBBInfo(*it, FbasicBlockInfo);
                int basicblockIDf = bblf->BBLID;
                if(bblf==NULL)
                  continue;

                // The instruction field of bblk and bblf should be initialized.
                InitializeBBLInfo(bblk);
                InitializeBBLInfo(bblf);
                SigMatchResult smr = SigMatch(bblk,bblf,MCSMap);
                int Similarity = get<0>(smr); 
                AddCMPItem(bblk, basicblockIDf, Similarity, smr);
                AddCMPItem(bblf, basicblockIDk, Similarity, smr);
                if(Similarity < Threshhod_process_1)
                  continue;
                // If we can match bk with bf, we furtherly check the existance of the use (an instruction)
                BasicBlock *bf = bblf->bbl;
                Instruction *instf = FindInstInBBL(bf,IK);
                jsoncount ++;
                if(instf ==NULL || !IsValideOperand(instf)){
                  #ifdef RECORD
                  vector<vector<Instruction*>> opkUselist = FindUseList(useSeqk, op);
                    if((jsoncount != 1))//{
                      content = content +",";
                      
                  content = content + "\n{\"opk\" : \""+getInstContent(op.first) + " +"+getIntContent(GetLocation(op.first))+ "\",\n\"Pattern\":\"" + Dumpstack(op.second) + "\",\n\"Kuse\" :\"";
          
                  for( vector<vector<Instruction*>>::iterator ii= opkUselist.begin(); ii!= opkUselist.end(); ii++){
                  vector<Instruction*> eachuse = *ii;
                  Instruction *lastInst = eachuse.back();
                  if((getInstContent(lastInst).find("asm")!=string::npos) || (getInstContent(lastInst).find("call")!=string::npos))
                    content = content + "\\n"+ " +" + getIntContent(GetLocation(lastInst));
                  else
                    content = content + "\\n"+getInstContent(lastInst) + " +" + getIntContent(GetLocation(lastInst));
                 
                  }
                  content = content + "\",";
                  content = content + "\n\"KI\": \""+ getInstContent(IK)+ " +" + getIntContent(GetLocation(IK))+"\",";
                  content = content + "\n\"FI\":  \"NULL\"} ";
                  #endif
                  continue; 
                }
                #ifdef RECORD
                  Ismatch = true; // Ismatch indicates we find the corresponding instf.
                  if(jsoncount != 1)
                    content = content +",";
                  vector<vector<Instruction*>> opkUselist = FindUseList(useSeqk, op);

                  content = content + "\n{\"opk\" : \""+getInstContent(op.first) + " +"+getIntContent(GetLocation(op.first))+ "\",\n\"Pattern\":\"" + Dumpstack(op.second) + "\",\n\"Kuse\" :\"";
          
                  for( vector<vector<Instruction*>>::iterator ii= opkUselist.begin(); ii!= opkUselist.end(); ii++){
                        vector<Instruction*> eachuse = *ii;
                        Instruction *lastInst = eachuse.back();
                        if((getInstContent(lastInst).find("asm")!=string::npos) || (getInstContent(lastInst).find("call")!=string::npos))
                          content = content + "\\n"+ " +" + getIntContent(GetLocation(lastInst));
                        else
                          content = content + "\\n"+getInstContent(lastInst) + " +" + getIntContent(GetLocation(lastInst));
                        
                  }
                  content = content + "\","; 
                  content = content + "\n\"KI\": \""+ getInstContent(IK)+ " +" + getIntContent(GetLocation(IK)) + "\",";
                  content = content + "\n\"FI\": \""+ getInstContent(instf)+ " +" + getIntContent(GetLocation(instf)) + "\",";     
                #endif

                
                #ifdef RECORD
                  content = content +  "\n\"basicblockIDk\" : \""+getIntContent(basicblockIDk)+"\",\n\"basicblockIDf\" : \""
                  +getIntContent(basicblockIDf)+ "\", \n\"opk(ninstk)\" : \""+getInstContent(op.first) + " +"+getIntContent(GetLocation(op.first))+ "\",\n\"Chooseduse\" : \""+getInstContent(IK)+
                  " +"+getIntContent(GetLocation(IK)) + "\",\n\"instf\" : \""+getInstContent(instf) + " +"+getIntContent(GetLocation(instf)) + "\",\n\"operandF\": \""+getInstContent(instf) + 
                  " +"+getIntContent(GetLocation(instf)) + "\",";
                #endif
                Function *F = instf->getParent()->getParent();
                OP<<"\nFunction F2 name:";
                std::vector<Value*> Ffargs = Getargs(F);
          
                std::pair<mul_USESEQ, Value*> FRes = ObtainUseSeq(instf, &Ffargs); 
                mul_USESEQ useSeqf = FRes.first;

                if(useSeqf.size() == 0)
                  continue;

                mul_key operandf = make_pair(instf, pattern);
                vector<vector<Instruction*>> opfUselist = FindUseList(useSeqf, operandf);

                CriticalValue.insert(make_pair(make_pair(IK, pattern), operandf));
                CV_Use.push_back(make_tuple(make_pair(IK, pattern), opkUselist, operandf, opfUselist));

                content = content + "\n\"opf\" : \""+getInstContent(instf)+"\",\n\"Fuse\" :\"";
                for( vector<vector<Instruction*>>::iterator ii= opfUselist.begin(); ii!= opfUselist.end(); ii++){
                        vector<Instruction*> eachuse = *ii;
                        Instruction *lastInst = eachuse.back();
                        content = content + "\\n"+getInstContent(lastInst) + " +" + getIntContent(GetLocation(lastInst));
                        
                }

                content = content + "\",\n"; 
                // When we compare the use list of opk and opf, we need to furtherly confirm that if the sensitive operation is deleted, e.g. decrease the false positive
                UseSeqmatch = CompareUseList(opkUselist, opfUselist, instk);
                // We need to record opkUselist and opfUselist

                
                content = content + "\n\"Match result\": \""+ UseSeqmatch+"\"}";
                // If we find the corresponding instf, break the loop.
                if(UseSeqmatch == "FP1" || UseSeqmatch == "Y1"){
                  if(UseSeqmatch == "FP"){
                    string bcfile = splitStr(filename,"/")+".bc";
                    string FPRecord =  (string)DATA_DIR+ "../result/"+RecordDate+"/FPRecord-"+kernel_eddition+".txt";
                    dump_buffer1(bcfile+" +" + getIntContent(lineno) +": "+ funcName.str()+": FP (trace use)\n",FPRecord);
                  }
                  ExistKUseSeq = true;
                  ExistTwoUseSeq = true;
                  content = content + "]";
                  goto MInext; 
                }   
              }              
            } 
        }
        content = content + "],";
         

      MInext: 
          content = content + "\n\"CV\": \"" + Dumpmap(CriticalValue) + "\"," ;

          // Compare the source of instk
          std::tuple<Instruction*, Instruction*, bool>  res = CompareSource(instk, CriticalValue);
          Instruction *opk = get<0>(res);
          Instruction *opf = get<1>(res);
          bool IdenticalSource  = get<2>(res);
          content = content + "\n\"cvk\": \"" + getInstContent(opk) +  "\"," ;
          content = content + "\n\"getelementInst\": \"" + "Y" +  "\"," ;
          if(opf != NULL)
            content = content + "\n\"cvf\": \"" + getValueContent(opf) +  "\"," ;
          else
            content = content + "\n\"cvf\": \" NULL\"," ;
          content = content + "\n\"sourceIdentical\": \"" + getBoolContent(IdenticalSource) +  "\"," ;


          // compare the use seq of instk
          if(IdenticalSource){
            string IdenticalUseList = CompareUseList(deletedInst, instk, type, useSeqk, CV_Use, KbasicBlockInfo, FbasicBlockInfo );
            content = content + IdenticalUseList;
          }
          
          // compare the use seq of the propogation of instk
          if(ExistTwoUseSeq == false && ExistKUseSeq == true){
            content = content + "\n\"ExistKUseSeq\": \"" + getBoolContent(ExistKUseSeq) + "\"" ;
             }
          if(ExistKUseSeq == false){
            content = content + "\n\"ExistKUseSeq\": \"" + getBoolContent(ExistKUseSeq)+ "\"" ;
             }
          content = content + "}}";      
    }
    else{        
        int countuse = 0;
       
        USESEQ useSeqk = ObtainUseSeq(instk);

        std::map<Value*, Value*> CriticalValue;
        std::vector<CVRecord> CV_Use;

        content = content +"\n\"UseSize\": \"" + getIntContent(useSeqk.size()) + "\", ";
        content = content +"\n\"Use\": [" + DumpUseSeq(useSeqk) + "], ";
        if(GetUseNo(useSeqk) < 2){
        
            ExistKUseSeq = false;
            goto next;
        }

        
        OP<< "  \n\"useSeqk.size\":\"" << getIntContent(useSeqk.size()) ;
        ExistKUseSeq = true;   
        content = content + "  \n\"MCSUseCmp\":" + "[";
        for (USESEQ::iterator iterk = useSeqk.begin(), itere = useSeqk.end(); iterk != itere; ++iterk) {
              Value *op = iterk->first;  // variable
              if( CriticalValue.find(op) != CriticalValue.end() )
                  continue;
              Instruction *I = iterk->second; // the use of a variable
              int pos = FindPos(op, I); // output that op is the ith operand of I, which is use to locate operand in instf

              if(op == NULL || I == NULL)
                continue;
              BasicBlock *BB = I->getParent();
              if(BB == NULL)
                continue;
              int basicblockIDk = ObtainBBID(BB,KbasicBlockInfo); 
              if(basicblockIDk == -1)
                continue;
              #ifdef CheckDSS
                OP<<"\nIn CheckUseSeq, basicblockIDk is : "<<basicblockIDk<<"\n";
                PrintMCS(MCSMap);
              #endif

              countuse++;

              // if the use is in MCS, we find the corresponding instf
              std::pair<Instruction*, int>  matchResult = IsInMCS(MCSMap, basicblockIDk, I, FbasicBlockInfo);

              Instruction *instf = matchResult.first;
              int basicblockIDf = matchResult.second;

              // We are not able to find the corresponding instruction in basic block in firmware, we also record it in log
              if(instf == NULL){
                #ifdef RECORD
                  // Record in logs. Output opk and all the use of it.
                  if(countuse != 1)//{
                    content = content + ",";
                    vector<Instruction*> opkUselist = FindUseList(useSeqk,op);
                    content = content + "\n{\"opk\" : \""+getValueContent(op) + " +"+getIntContent(GetLocation(op))+"\",\n\"Kuse\" :\"";
                   
                   
                    for( vector<Instruction*>::iterator ii= opkUselist.begin(); ii!= opkUselist.end(); ii++){
                        if((getInstContent(*ii).find("asm")!=string::npos) || (getInstContent(*ii).find("call")!=string::npos))
                          content = content + "\\n"+ " +" + getIntContent(GetLocation(*ii));
                        else
                          content = content + "\\n"+getInstContent(*ii) + " +" + getIntContent(GetLocation(*ii));
                       
                    }
                    content = content + "\",";
                    content = content + "\n\"KI\": \""+ getInstContent(I)+ " +" + getIntContent(GetLocation(I))+"\",";
                    content = content + "\n\"FI\":  \"NULL\"} ";
                #endif
                continue;
              }
              // If we find instf , we can match a instruction in firmware.
              Ismatch = true;
              #ifdef RECORD
                // Record in logs. Output opk and all the use of it.
                vector<Instruction*> opkUselist = FindUseList(useSeqk,op);
                if(countuse != 1)//{
                  content = content + ",";
                  content = content + "\n{\"opk\" : \""+getValueContent(op) + " +"+getIntContent(GetLocation(op))+"\",\n\"Kuse\" :\"";
                 
                  for( vector<Instruction*>::iterator ii= opkUselist.begin(); ii!= opkUselist.end(); ii++){
                      if((getInstContent(*ii).find("asm")!=string::npos) || (getInstContent(*ii).find("call")!=string::npos))
                          content = content + "\\n"+ " +" + getIntContent(GetLocation(*ii));
                      else
                          content = content + "\\n"+getInstContent(*ii) + " +" + getIntContent(GetLocation(*ii));

                     
                  }
                  content = content + "\",";
                  content = content + "\n\"KI\": \""+ getInstContent(I)+ " +" + getIntContent(GetLocation(I)) + "\",";
                  content = content + "\n\"FI\": \""+ getInstContent(instf)+ " +" + getIntContent(GetLocation(instf)) + "\",";
                
              #endif

              // We obtain the corresponding variable in instf
              Value *operandf = instf->getOperand(pos);
              if(operandf == NULL)
                continue;
              if(!IsValideOperand(operandf))
                continue;
              
              

              #ifdef RECORD
                  content = content +  "\n\"basicblockIDk\" : \""+getIntContent(basicblockIDk)+"\",\n\"basicblockIDf\" : \""
                +getIntContent(basicblockIDf)+ "\", \n\"opk(ninstk)\" : \""+getValueContent(op) + " +"+getIntContent(GetLocation(op))+ "\",\n\"Chooseduse\" : \""+getInstContent(I)+
                " +"+getIntContent(GetLocation(I))+ "\",\n\"instf\" : \""+getInstContent(instf)+  " +"+getIntContent(GetLocation(instf))+"\",\n\"operandF\": \""+getValueContent(operandf)+
                " +"+getIntContent(GetLocation(operandf))+"\",";

              #endif
             
              USESEQ useSeqf = ObtainUseSeq(operandf);
              
              if(useSeqf.size() == 0)
                continue;
              
              vector<Instruction*> opfUselist = FindUseList(useSeqf,operandf);

              CriticalValue.insert(make_pair(op, operandf));
              CV_Use.push_back(make_tuple(op, opkUselist, operandf, opfUselist));

              content = content + "\n\"opf\" : \""+getValueContent(operandf)+ " +" + getIntContent(GetLocation(operandf)) + "\",\n\"Fuse\" :\"";
              for( vector<Instruction*>::iterator ii= opfUselist.begin(); ii!= opfUselist.end(); ii++){
                content = content + "\\n"+getInstContent(*ii) + " +" + getIntContent(GetLocation(*ii));
              }
              content = content + "\",";
              UseSeqmatch = CompareUseList(opkUselist, opfUselist, instk);
              content = content + "\n\"Match results\": \""+ UseSeqmatch+"\"}";
              
        }        
        
        content = content + "],";


        //After we tranverse the use sequence of all the operands and find that all the uses are not in MCS.
        content = content + "  \n\"NonMCSUseCmp\":" + "[";
       
        {
          int jsoncount =0;
          
            for(USESEQ::iterator inst = useSeqk.begin(); inst != useSeqk.end(); inst++){
              Value *operand = inst->first; // the variable 
              if( CriticalValue.find(operand) != CriticalValue.end() )
                  continue;
              Instruction *IK = inst->second;  // the use of the corresponding variable
              int pos = FindPos(operand, IK);
              
              // We need to match bk (the basic block of the use)
              BasicBlock *bk = IK->getParent();
              bbl_info bblk = ObtainBBInfo(bk, KbasicBlockInfo);
              if(bblk==NULL)
                  continue;
              int basicblockIDk = bblk->BBLID;
             
              for(std::vector<int>::iterator it = remain_graph2->begin(); it!=remain_graph2->end();it++){
                bbl_info bblf = ObtainBBInfo(*it, FbasicBlockInfo);
                int basicblockIDf = bblf->BBLID;
                if(bblf==NULL)
                  continue;

                // The instruction field of bblk and bblf should be initialized.
                InitializeBBLInfo(bblk);
                InitializeBBLInfo(bblf);
                SigMatchResult smr = SigMatch(bblk,bblf,MCSMap);
                int Similarity = get<0>(smr); 
                AddCMPItem(bblk, basicblockIDf, Similarity, smr);
                AddCMPItem(bblf, basicblockIDk, Similarity, smr);
                if(Similarity < Threshhod_process_1)
                  continue;
                // If we can match bk with bf, we furtherly check the existance of the use (an instruction)
                BasicBlock *bf = bblf->bbl;
                Instruction *instf = FindInstInBBL(bf,IK);
                jsoncount ++;
                if(instf ==NULL){
                  #ifdef RECORD
                    
                    if((jsoncount != 1))//{
                      content = content +",";
                    vector<Instruction*> opkUselist = FindUseList(useSeqk,operand);
                    content = content + "\n{\"opk\" : \""+getValueContent(operand)+"\",\n\"Kuse\" :\"";
                    for( vector<Instruction*>::iterator ii= opkUselist.begin(); ii!= opkUselist.end(); ii++){
                        if((getInstContent(*ii).find("asm")!=string::npos) || (getInstContent(*ii).find("call")!=string::npos))
                          content = content + "\\n"+ " +" + getIntContent(GetLocation(*ii));
                        else
                          content = content + "\\n"+getInstContent(*ii) + " +" + getIntContent(GetLocation(*ii));

                      
                    }
                    content = content + "\",";
                    content = content + "\n\"KI\": \""+ getInstContent(IK)+" +"+getIntContent(GetLocation(IK))+"\",";
                    content = content + "\n\"FI\":  \"NULL\"} ";
                  #endif
                  continue; 
                }
                #ifdef RECORD
                  Ismatch = true; // Ismatch indicates we find the corresponding instf.
                  if(jsoncount != 1)
                    content = content +",";
                  vector<Instruction*> opkUselist = FindUseList(useSeqk,operand);
                  content = content + "\n{\"opk\" : \""+getValueContent(operand)+"\",\n\"Kuse\" :\"";
                  for( vector<Instruction*>::iterator ii= opkUselist.begin(); ii!= opkUselist.end(); ii++){
                        if((getInstContent(*ii).find("asm")!=string::npos) || (getInstContent(*ii).find("call")!=string::npos))
                          content = content + "\\n"+ " +" + getIntContent(GetLocation(*ii));
                        else
                          content = content + "\\n"+getInstContent(*ii) + " +" + getIntContent(GetLocation(*ii));
                    
                  }
                  content = content + "\","; 
                  content = content + "\n\"KI\": \""+ getInstContent(IK)+" +"+getIntContent(GetLocation(IK))+"\",";
                  content = content + "\n\"FI\": \""+ getInstContent(instf)+" +"+getIntContent(GetLocation(instf))+"\",";         
                #endif

                Value *operandf = instf->getOperand(pos);
                if(operandf == NULL)
                  continue;
                if(!IsValideOperand(operandf))
                  continue;
                #ifdef RECORD
                  content = content +  "\n\"basicblockIDk\" : \""+getIntContent(basicblockIDk)+"\",\n\"basicblockIDf\" : \""
                    +getIntContent(basicblockIDf)+ "\", \n\"opk(ninstk)\" : \""+getValueContent(operand) + " +" + getIntContent(GetLocation(operand)) + "\",\n\"Chooseduse\" : \""+getInstContent(IK)+
                    +" +"+getIntContent(GetLocation(IK))+ "\",\n\"instf\" : \""+getInstContent(instf)+ + " +"+getIntContent(GetLocation(instf))+ "\",\n\"operandF\": \""+getValueContent(operandf)+
                    " +"+getIntContent(GetLocation(operandf)) + "\",";
                #endif
                OP<< "\nLog 1-25-3";
                USESEQ useSeqf = ObtainUseSeq(operandf);
                if(useSeqf.size() == 0)
                  continue;
                vector<Instruction*> opfUselist = FindUseList(useSeqf,operandf);

                CriticalValue.insert(make_pair(operand, operandf));
                CV_Use.push_back(make_tuple(operand, opkUselist, operandf, opfUselist));

                content = content + "\n\"opf\" : \""+getValueContent(operandf) + " +"+getIntContent(GetLocation(operandf)) + "\",\n\"Fuse\" :\"";
                for( vector<Instruction*>::iterator ii= opfUselist.begin(); ii!= opfUselist.end(); ii++){
                  content = content + "\\n"+getInstContent(*ii) + " +" + getIntContent(GetLocation(*ii));
                }
                content = content + "\",\n"; 
                // When we compare the use list of opk and opf, we need to furtherly confirm that if the sensitive operation is deleted, e.g. decrease the false positive
                UseSeqmatch = CompareUseList(opkUselist, opfUselist, instk);
                // We need to record opkUselist and opfUselist

                
                content = content + "\n\"Match result\": \""+ UseSeqmatch+"\"}";
               
              }
            } 
        }
        content = content + "],";
    
      next: 
          content = content + "\n\"CV\": \"" + Dumpmap(CriticalValue) + "\"," ;
          // Compare the source of instk
          OP<<"\n Instk is: "<<*instk;
          std::tuple<Instruction*, Instruction*, bool>  res = CompareSource(instk, CriticalValue);
          Instruction *opk = get<0>(res);
          Instruction *opf = get<1>(res);
          bool IdenticalSource  = get<2>(res);
          content = content + "\n\"cvk\": \"" + getInstContent(opk) +  "\"," ;
          if(opf != NULL)
            content = content + "\n\"cvf\": \"" + getValueContent(opf) +  "\"," ;
          else
            content = content + "\n\"cvf\": \" NULL\"," ;
          content = content + "\n\"sourceIdentical\": \"" + getBoolContent(IdenticalSource) +  "\"," ;
          
          if(IdenticalSource){
            string IdenticalUseList = CompareUseList(deletedInst, instk, type, useSeqk, CV_Use, KbasicBlockInfo, FbasicBlockInfo );
            content = content + IdenticalUseList;
          }
          // compare the use seq of the propogation of instk
          if(ExistTwoUseSeq == false && ExistKUseSeq == true){
          content = content + "\n\"ExistKUseSeq\": \"" + getBoolContent(ExistKUseSeq) + "\"" ;
          
        }
        if(ExistKUseSeq == false){
          content = content + "\n\"ExistKUseSeq\": \"" + getBoolContent(ExistKUseSeq)+ "\"" ;
         
        }
        content = content + "}}";      
    }
    //}
    return  make_tuple(ExistKUseSeq, UseSeqmatch, content);
}


/*
Analyzes the deleted security operation
*/
void AnalyzeDeleteSS(std::map<llvm::Instruction*, int> *deletedSSlistr,  std::map<int,int> *MCSMap,std::vector<int> *remain_graph2,
Mapbbl *KbasicBlockInfo, Mapbbl *FbasicBlockInfo,  string filename){
  #ifdef analyzeDeleteSS
    OP<<"IN analyzedeletess.\n";
  #endif
  if (FILE *file = fopen(Convertstr2char(filename), "r")){
    if(remove(Convertstr2char(filename))==0)
        OP<<"delete sucessfully.";
  }

  int DeleteSSNo = 0;
  // if we can find the uses of critical variables
  int KUseSeqCount = 0;
  // matchResult
  int YCount = 0;
  int FPCount = 0;
  int NCount = 0;
  int LockCount = 0;
  StringRef funcName;

  string staticsDir = (string)DATA_DIR+ "../result/TimeRecord/DSOStatics-"+ RecordDate + "-" +kernel_eddition+".txt";
  string content = "{";
  content = content +"\n\"BCName\" : \"" + filename;
  content = content + "\",";
  content = content +"\n\"MCS\" : "+ DumpMCSMap(MCSMap)+",";  
  content = content + "\n\"DeletedSo\" : " +DumpDeletedSSO(deletedSSlistr, KbasicBlockInfo)+",";
  //OP<<"IN analyzedeletess, before dump_buffer.\n";
  content = content +"\n\"DeletionAnalysis\" : [";
  
  int count = 0;
  #ifdef analyzeDeleteSS
    OP<<"\nLog1, count:"<<count;
  #endif
  for(std::map<llvm::Instruction*, int>::iterator it = deletedSSlistr->begin(); it != deletedSSlistr->end(); it++){
      
      // Inst is the deleted instruction; type is the type of sensitive operaion.
      Instruction *Inst = it->first;
      int type = it->second;
      OP<<"type is: "<<type<<"\n";
      if(Inst == NULL)
        continue;
      int lineno = GetLocation(Inst);  

      if(isa<SwitchInst>(Inst)){
        StringRef funcName = Inst->getParent()->getParent()->getName();
	      string bcfile = splitStr(filename,"/")+".bc";
        string FPRecord =  (string)DATA_DIR+ "../result/"+RecordDate+"/FPRecord-"+kernel_eddition+".txt";
        dump_buffer1(bcfile+" +" + getIntContent(lineno) +": "+ funcName.str()+": SwitchInst\n",FPRecord);
        continue;
      }

      Instruction *instk = Inst; 
      count ++;
      if(count != 1)
        content = content + "\n,{\"Analysis\" : [";
      else
        content =  content + "\n{\"Analysis\" : [";

     
      funcName = Inst->getParent()->getParent()->getName();
      // we need to exclude FP.
      string  checkResult = CheckFP(instk,  filename, KbasicBlockInfo, FbasicBlockInfo, remain_graph2, MCSMap);
      if(checkResult == "")
        OP<<"   No successor. ";
      else if(checkResult =="FP"){
        string bcfile = splitStr(filename,"/")+".bc";
        string FPRecord =  (string)DATA_DIR+ "../result/"+RecordDate+"/FPRecord-"+kernel_eddition+".txt";
        dump_buffer1(bcfile+" +" + getIntContent(lineno) +": "+ funcName.str()+": Modification\n",FPRecord);
      }
      else if(checkResult =="Unknown")
        OP<<"  need further analysis. ";
      string SSInfoDir =  (string)DATA_DIR+ "../result/"+RecordDate+"/SSINFO-"+kernel_eddition+".txt";
      #ifdef RECORD
        dump_buffer1(filename+"/"+funcName.str()+"\n",SSInfoDir);    
      #endif

      //If the deleted SO is a security check
      DeleteSSNo ++;
      std::tuple<bool, string, string>  CheckRes;
      bool  ExistKUseSeq;
      string UseSeqmatch;

      if(type == 0) {
          
          Tpye_Security_check++;
          
          Instruction *Cond = ObtainConds(instk); 
          
          if(Cond == NULL){
           
            content = content + "]}" ;
            continue;        
          }

          CheckRes =  FurtherCheckUseSequence(instk, Cond, filename,  KbasicBlockInfo, FbasicBlockInfo, 
                                            remain_graph2, MCSMap,  0);
          ExistKUseSeq = get<0>(CheckRes);
          UseSeqmatch = get<1>(CheckRes);
          content = content + get<2>(CheckRes);
          //}
          if(ExistKUseSeq)
            KUseSeqCount ++;
          
          if(UseSeqmatch == "Y")
            YCount++;
          else if(UseSeqmatch == "N")
            NCount++;
          else if(UseSeqmatch == "FP")
            FPCount++;
      }
      else if(type==1 ){
        Tpye_missing_init++;
        CheckRes = FurtherCheckUseSequence(instk, instk, filename, KbasicBlockInfo, FbasicBlockInfo, 
                                          remain_graph2, MCSMap,  1);
        ExistKUseSeq = get<0>(CheckRes);
        UseSeqmatch = get<1>(CheckRes);
        content = content + get<2>(CheckRes);

        if(ExistKUseSeq)
          KUseSeqCount ++;
        
        if(UseSeqmatch == "Y")
          YCount++;
        else if(UseSeqmatch == "N")
          NCount++;
        else if(UseSeqmatch == "FP")
          FPCount++;
      }
      else if(type == 4){
        Tpye_missing_RR++;

       
        CheckRes = FurtherCheckUseSequence(instk, instk, filename, KbasicBlockInfo, FbasicBlockInfo, 
                                          remain_graph2, MCSMap,  4);
        ExistKUseSeq = get<0>(CheckRes);
        UseSeqmatch = get<1>(CheckRes);
        content = content + get<2>(CheckRes);
        // }
        if(ExistKUseSeq)
          KUseSeqCount ++;
        
        if(UseSeqmatch == "Y")
          YCount++;
        else if(UseSeqmatch == "N")
          NCount++;
        else if(UseSeqmatch == "FP")
          FPCount++;
      }
      
      content = content + "]}" ;
  }
  content = content + "]}" ;
  
  string statics ="\nBCName: " + filename+ "\nFunctionName: " + funcName.str() + "; DeleteSSNo: " + getIntContent(DeleteSSNo) +"; KUseSeqCount: " + getIntContent(KUseSeqCount) + "; YCount: " + getIntContent(YCount)
  +  "; FPCount: " + getIntContent(FPCount)+ "; NCount: " + getIntContent(NCount) +  "; LockCount: " + getIntContent(LockCount)+ "\n";

  dump_buffer(content, filename, 1);
  dump_buffer1(statics, staticsDir);
  
}


void UpdatedeletedSSlist(map<llvm::Instruction*, int> *deletedSSlist, map<llvm::Instruction*, int> *DeletedSSlists){
  for(map<llvm::Instruction*, int>::iterator iter=deletedSSlist->begin();iter!=deletedSSlist->end();iter++){
      DeletedSSlists->insert(make_pair(iter->first,iter->second));
  }
}

void UpdateVisitedElem(vector<int> *VisitedElem, vector<int> L, vector<int> R, vector<int> left, vector<int> right){

}

std::map<int,int>  ObtainRelatedVetex(bbl_info b, std::vector<int> common_node ){
    vector<int> RelatedVetex={};
    // basicblockID, basicblock type
    std::map<int,int> Relatemap;
  
    vector<int> p = ObtainParentList(b);     

    vector<int> c = ObtainChildrenList(b);
  
    vector<int> s = ObtainSilbingList(b);
    
    std::sort(p.begin(),p.end());   
    std::sort(c.begin(),c.end());  
    std::sort(s.begin(),s.end());
    for (auto vetex: p){

      int v = vetex;
      if(Is_element_in_vector(RelatedVetex, v) || Is_element_in_vector(common_node, v))
      continue;
      else{
          RelatedVetex.push_back(vetex);
          Relatemap[vetex]=0; 
      }
    }

    for (auto vetex: c){

      int v = vetex;
      if(Is_element_in_vector(RelatedVetex, v) || Is_element_in_vector(common_node, v))
      continue;
      else{
          RelatedVetex.push_back(vetex);
          Relatemap[vetex]=1; 
      }
    }

    for (auto vetex: s){

      int v = vetex;
      if(Is_element_in_vector(RelatedVetex, v) || Is_element_in_vector(common_node, v))
      continue;
      else{
          RelatedVetex.push_back(vetex);
          Relatemap[vetex]=2; 
      }
    }
    return Relatemap;
}


std::map<int,int>  ObtainCFGRelatedVetex(int common_vetex, std::map<int,int> *MCSMap, Mapbbl basicBlockInfo, int pos){
  std::map<int,int>  relatedvetex;
  bbl_info b = basicBlockInfo[common_vetex];

  vector<int> MSCnode = FindMCSNode(MCSMap, pos);
  // the nodes that connect to a MCS node through CFG
  relatedvetex = ObtainRelatedVetex(b,MSCnode);
  return relatedvetex;
}


std::vector<USESEQ> ObtainDFGFlow(Instruction *Inst){
  std::vector<USESEQ> UseSEQ;
  Value *v = dyn_cast<Value>(Inst);
  if(IsValideOperand(v))
    UseSEQ.push_back(ObtainUseSeq(v));
  for(int i=0; i<Inst->getNumOperands(); i++){    
        Value *operand = Inst->getOperand(i); 
        if(IsValideOperand(operand))
          UseSEQ.push_back(ObtainUseSeq(operand));
  }
  return UseSEQ;
}

// basicblockIDk and basicblockIDf are paired in MCS. We match each instruction in bk with the corresponding instruction.
// <basicblockIDk,Instk, UseSeqK> : the ID of basic block,  instruction, and all the uses of the data of the instruction, and the basic block ID of the use.
std::vector<InstMatchItem>  MatchVariable(BasicBlock *bk, BasicBlock *bf){
  std::vector<InstMatchItem> MatchResult;
  for(BasicBlock::iterator iterk = bk->begin(); iterk != bk->end(); iterk++){
    vector<Instruction*> candidateInst;
    Instruction *Instk = &*iterk;
    Instruction *Instf;
    for(BasicBlock::iterator iterf = bf->begin(); iterf != bf->end(); iterf++){
        Instruction *instf = &*iterf;
        if(Filter(getInstContent(Instk)) == Filter(getInstContent(instf)))
          candidateInst.push_back(instf);     
    }
    Instf = FilterCandidate(candidateInst, Instk, bf);  
    if(Instf != NULL){  
      std::vector<USESEQ> UseSeqK = ObtainDFGFlow(Instf);
      std::vector<USESEQ> UseSeqF = ObtainDFGFlow(Instk);
      MatchResult.push_back(make_tuple(Instk, UseSeqK, Instf, UseSeqF));
    }
  }
  return  MatchResult;
}

vector<int> ObtainNodes(USESEQ *useseq, Mapbbl *BasicBlockInfo, std::map<int,int> *MCSMap, int pos){
  vector<int> RelatedVetex;
  vector<int> common_node = FindMCSNode(MCSMap, pos);
  for(USESEQ::iterator iter=useseq->begin(); iter!=useseq->end();iter++){
    int BBLID = ObtainBBID((iter->second)->getParent(), BasicBlockInfo);
    if(Is_element_in_vector(RelatedVetex, BBLID) || Is_element_in_vector(common_node, BBLID))
      continue;
    RelatedVetex.push_back(BBLID);
  }
  return RelatedVetex;
}

std::map<pair<int, int>, std::vector<InstMatchItem>> MCSDFGAnalyze(std::map<int,int> *MCSMap,  Mapbbl *KbasicBlockInfo,  Mapbbl *FbasicBlockInfo){
  std::map<pair<int, int>, std::vector<InstMatchItem>> DFGUseInfo;
  for(std::map<int,int>::iterator iter=MCSMap->begin(); iter != MCSMap->end(); iter++){
    int basicblockIDk = iter->first;
    int basicblockIDf = iter->second;
    bbl_info bk = ObtainBBInfo(basicblockIDk, KbasicBlockInfo);
    bbl_info bf = ObtainBBInfo(basicblockIDf, FbasicBlockInfo);
    if( bk && bf){
      std::vector<InstMatchItem> MatchResult = MatchVariable(bk->bbl, bf->bbl); 
      DFGUseInfo.insert(make_pair(make_pair(basicblockIDk,basicblockIDf),MatchResult));
    }
  }
  return DFGUseInfo;
}


std::vector<InstMatchItem>  ObtainDFGRelatedVetex(pair<int, int> key,  std::map<pair<int, int>, std::vector<InstMatchItem>> *DFGUseeInfo){
  std::vector<InstMatchItem> MatchResult;
  auto iter = DFGUseeInfo->find(key);
  if( iter!= DFGUseeInfo->end())
    MatchResult = iter->second;
  return MatchResult;
}


int IsSensitive(llvm::BasicBlock *bbl,  GlobalContext *GlobalCtx){
    bool sensitive = false;
    string macro, word, FnName;

    vector<llvm::Instruction*> sensitive_ins_Set;
    for (llvm::BasicBlock::iterator bbl_iter = bbl->begin(); bbl_iter != bbl->end(); ++bbl_iter) 
        {
          OP <<"Instruction is :";
          OP<<*bbl_iter<<"\n";
          Instruction *Inst = &*bbl_iter;
          Value *Cond = NULL;
          BasicBlock *BB = Inst->getParent();
          Function *F = BB->getParent();

          if(isa<BranchInst>(Inst) || isa<SwitchInst>(Inst) || isa<SelectInst>(Inst)) {
              SensitiveChecksPass KSCPass(GlobalCtx, "SecurityCheck");

              sensitive = KSCPass.IsSecurityCheck(F,Inst);  
              if(sensitive) {
                sensitive_ins_Set.push_back(Inst);
                OP<<"Sensitive Instruction in condition branch: "<< *Inst<<"\n";
              }
            }

          else if(isa<AllocaInst>(Inst)) {
              SensitiveChecksPass KSCPass(GlobalCtx, "SecurityCheck");
        
              sensitive = KSCPass.IsSecurityCheck(F,Inst);  
              if(sensitive){
                sensitive_ins_Set.push_back(Inst); 
                OP<<"Sensitive Instruction in Selection branch: "<< *Inst<<"\n";
              }  
          }
       
          else if(isa<CallInst>(Inst)){
              CallInst *CI = dyn_cast<CallInst>(Inst);
              FnName = getCalledFuncName(CI);
              OP<<"FnName is :"<<FnName<<"\n";
             
              sensitive = Is_element_in_stingvector((GlobalCtx->LockFuncs), FnName);
              if(sensitive) {
                sensitive_ins_Set.push_back(Inst);
                OP<<"Sensitive lock function: "<< *Inst<<" "<<FnName<<"\n";
              }
             
              else{
                sensitive = Is_element_in_stingvector((GlobalCtx->PairFuncs), FnName);
                if(sensitive) {
                sensitive_ins_Set.push_back(Inst);
                OP<<"Sensitive pair function: "<< *Inst<<" "<<FnName<<"\n";
                }
              }   
          }
          else{
            ;
          }
        }
    return sensitive;
}

void searchQueue(std::queue<int>  q){
  while(!q.empty()){
  int value=q.front();
  std::cout<<value<<" ";
  q.pop();
  }
  std::cout<<"\n";
}




void DeleteItem(std::vector<int> *V, int Ele){
  for(vector<int>::iterator iter=V->begin(); iter!=V->end(); ){
    if( *iter == Ele)
      iter = V->erase(iter);
    else
      iter ++ ;
  }
}

void DeleteItem(std::map<int,int> *V, int Ele){
  std::map<int,int>::iterator key = V->find(Ele);
  if(key!=V->end())
	  V->erase(key);
}



std::string CalculateMatchResult(double **a,int m, int n){
	string content_mat = "\n";
  std::vector<int> MatchRow, MatchCol;

  for(int i=0; i<m; i++){
    if(a[i][0] != -1000)
      MatchRow.push_back(i); 
  }
  for(int j=0; j<n; j++){
      MatchCol.push_back(j); 
  }
  while(MatchRow.size()){

    int max_i = 0, max_j = 0;
    double max= -1000;
    for(int i=0; i<m; i++){
        for (int j=0; j<n; j++){
            if((find(MatchRow.begin(), MatchRow.end(), i) != MatchRow.end())&& (find(MatchCol.begin(), MatchCol.end(), j) != MatchCol.end()))
            if(a[i][j]>max){
                max=a[i][j];
                max_i=i;
                max_j=j;
            }     
        }
      } 
      content_mat = content_mat + "\nbblK: "+getIntContent(max_i) + "; bblF: "+  getIntContent(max_j) + "; similarity: " + getDoubleContent(max);   
      DeleteItem(&MatchRow, max_i);
      DeleteItem(&MatchCol, max_j);

  }  
	return  content_mat;
}

// Find the corresponding node in firmware by MCS
int FindNode(std::map<int,int> *MCSMap, int kcommon_vetex){
  std::map<int,int>::const_iterator pos = MCSMap->find(kcommon_vetex);
  if (pos != MCSMap->end()) 
      return pos->second;
  else
      return -1;
}

vector<int> FindMCSNode(std::map<int,int> *MCSMap, int pos){
  vector<int> MCSnode;
  for(std::map<int,int>::iterator it= MCSMap->begin(); it!=MCSMap->end();it++){
    // obtain nodes in kernel
    if(pos == 0)
      MCSnode.push_back(it->first);
    // obtain nodes in firmware
    if(pos == 1)
      MCSnode.push_back(it->second);
  }
  return MCSnode;
}


void AddCMPItem(bbl_info bbl, int basicblockID, double Similarity, SigMatchResult smr){
  std::map<int, pair<double, SigMatchResult>> MatchRecords = bbl->MatchRecords;
  if(MatchRecords.find(basicblockID) != MatchRecords.end()){
      (bbl->MatchRecords[basicblockID]).first = Similarity;
      (bbl->MatchRecords[basicblockID]).second = smr;
  }
  else
      bbl->MatchRecords.insert(make_pair(basicblockID, make_pair(Similarity, smr)));
}


int findkeyByvalue(std::map<int,int> aMap, int value){
  int key = -1;
  for(std::map<int,int>::iterator it = aMap.begin();it!=aMap.end();it++) {
    
		if(it->second==value)
			key = it->first;
	} 
  return key;
}

bool IsChecked(bbl_info bbl, int basicblockID){
  std::map<int, pair<double, SigMatchResult>> MatchRecords = bbl->MatchRecords;
  if(MatchRecords.find(basicblockID) != MatchRecords.end())
    return true;
  else  
    return false;
}


void ClusterCMP(int kcommon_vetex, int fcommon_vetex,vector<int> *kDFGrelatedvetex, vector<int> *fDFGrelatedvetex, set<int> *SScfgk,std::queue<int> *kcommon_subgraph,std::vector<int> *kcommon_node,
                Mapbbl KbasicBlockInfo,std::vector<int> *remain_graph1,std::map<int, int> *MatchResult,
                set<int> *SScfgf,std::queue<int> *fcommon_subgraph,std::vector<int> *fcommon_node, Mapbbl FbasicBlockInfo , std::vector<int> *remain_graph2,
                std::map<int,int> *MCSMap, std::vector<int> *DeletedBBlist, std::map<llvm::Instruction*, int> *DeletedSSlists, char*  local_msg, string filename) {
  string content = "";
  for (std::vector<int> ::iterator iter=kDFGrelatedvetex->begin(); iter!=kDFGrelatedvetex->end(); iter++)
      {
          if(SScfgk->find(*iter) == SScfgk->end())
              continue;
          bbl_info rk = KbasicBlockInfo[*iter];
          int sensitive = (rk->Sensitive_Info).size();

          if(!sensitive)
              continue;
        
          content = content + "\npoped fcommon_vetex is : "+getIntContent(fcommon_vetex) + "; Related Vetex of  fcommon_vetex: "+DumpVectorI(*fDFGrelatedvetex);         

          map<llvm::Instruction*, int>  deletedSSlist;
          map<llvm::Instruction*, int> sensitive_Infok = rk->Sensitive_Info;
          llvm::BasicBlock *bblk = rk->bbl;
          bool Matched = false;

          
          int basicblockIDk = *iter;

          int basicblockIDf;
          bbl_info rf;
          SigMatchResult smr;
          double Similarity;
          vector<IdenticalInst> identicalInsts;
          float InstRaio = 0;
          // end
  
          #ifdef Debug_SO
            OP<<"\033[32mbasicblockIDk ("<<basicblockIDk<<"): not in MCS and contain SSOP \033[0m \n";
          #endif
          content = content + "\nbasicblockIDk (" +getIntContent(basicblockIDk) + "): not in MCS and contain SSOP";
          

          for(std::vector<int> ::iterator iter1=fDFGrelatedvetex->begin();iter1!=fDFGrelatedvetex->end();iter1++){
              basicblockIDf = *iter1;

              if(SScfgf->find(basicblockIDf) == SScfgf->end())
                  continue;
              #ifdef Debug_SO
                OP<<"\033[32mbasicblockIDf  ("<<basicblockIDf<<") is not in MCS and in frelatedvetex and contain SSOP. \033[0m\n";
              #endif
              content = content + "\nbasicblockIDf (" +getIntContent(basicblockIDf) + "): not in MCS, in frelatedvetex, contain SSOP.";
              

              rf = FbasicBlockInfo[basicblockIDf];

              if(rf==NULL || rk==NULL) continue;
              smr = SigMatch(rk, rf, MCSMap );
              Similarity = get<0>(smr); 
              AddCMPItem(rk, basicblockIDf, Similarity, smr);
              AddCMPItem(rf, basicblockIDk, Similarity, smr);
              #ifdef Debug_SO
                OP<<"\033[32mthe Similarity of "<< basicblockIDk <<" and "<<basicblockIDf <<" is: "<<Similarity<<"\033[0m\n";
              #endif
              content = content + get<4>(smr);
              
              identicalInsts = get<1>(smr); 
              if(Similarity > Threshhod_process_1){
                  #ifdef Debug_SO
                    OP<<"\033[35m"<< basicblockIDk <<" is matched  with "<< basicblockIDf<<"\033[0m\n";
                  #endif
                  content = content +"\n"+ getIntContent(basicblockIDk) + " is matched  with " + getIntContent(basicblockIDf) +"\n";
                  MatchResult->insert(make_pair(basicblockIDk,basicblockIDf));
                  if(fcommon_node->size())
                      DeleElem(fcommon_node,fcommon_vetex); 
                  Matched = true;
                  deletedSSlist = get<2>(smr); 
                  InstRaio = get<3>(smr); 
                  if(InstRaio < InstCMPThreshhod){ 
                    if(deletedSSlist.size()>0) 
                        UpdatedeletedSSlist(&deletedSSlist, DeletedSSlists);
                    UpdateVetex(basicblockIDk,kcommon_subgraph,kcommon_node,remain_graph1,SScfgk,
                    basicblockIDf,fcommon_subgraph,fcommon_node,remain_graph2,SScfgf,MCSMap);   
                  }
                  break; 
              }
          }

          if(!Matched){
              for(std::vector<int>::iterator iter2=fDFGrelatedvetex->begin();iter2!=fDFGrelatedvetex->end();iter2++){
                  basicblockIDf = *iter2;

                  if(SScfgf->find(basicblockIDf) != SScfgf->end())
                      continue;
                  #ifdef Debug_SO
                    OP<<"\033[32mbasicblockIDf ("<<basicblockIDf<<") is not in MCS and in frelatedvetex and does not contain SSOP. \033[0m\n";
                  #endif
                  
                  content = content + "\nbasicblockIDf (" +getIntContent(basicblockIDf) + "): not in MCS, in frelatedvetex, not contain SSOP.";
          
                  rf = FbasicBlockInfo[basicblockIDf];
                  
                  if(rf==NULL||rk==NULL)
                    continue;
                  ContainCheck(rf);
                  smr = SigMatch(rk, rf, MCSMap );
                  
                  Similarity = get<0>(smr); 
                  AddCMPItem(rk, basicblockIDf, Similarity, smr);
                  AddCMPItem(rf, basicblockIDk, Similarity, smr);
                
                  content = content + get<4>(smr);
                  #ifdef Debug_SO
                  OP<<"\033[32mthe Similarity of "<< basicblockIDk <<" and "<<basicblockIDf <<" is: "<<Similarity<<"\033[0m\n";
                  #endif
                  identicalInsts = get<1>(smr); 
                  if(Similarity > Threshhod_process_1){
                      #ifdef Debug_SO
                      OP<<"\033[35m"<< basicblockIDk <<" is matched  with "<< basicblockIDf<<"\033[0m\n";
                      #endif
                      content = content + getIntContent(basicblockIDk) + " is matched  with " + getIntContent(basicblockIDf) +"\n";
                      MatchResult->insert(make_pair(basicblockIDk,basicblockIDf));
                      if(fcommon_node->size())
                      DeleElem(fcommon_node,fcommon_vetex); 
                      Matched = true;
                      deletedSSlist = get<2>(smr); 
                      InstRaio = get<3>(smr); 
                      if((InstRaio < InstCMPThreshhod)){
                        if(deletedSSlist.size()>0)
                          UpdatedeletedSSlist(&deletedSSlist, DeletedSSlists);
                        UpdateVetex(basicblockIDk,kcommon_subgraph,kcommon_node,remain_graph1, SScfgk,
                        basicblockIDf,fcommon_subgraph,fcommon_node,remain_graph2, SScfgf,MCSMap);
                      }
                      break;
                  }
              }
          }
      }
}


std::pair<int, std::pair<double, SigMatchResult>> RankMatchResult(bbl_info bk, std::map<int,int> *MCSMap, Mapbbl FbasicBlockInfo ){
  
  std::vector<int> fcommon_vetex;
  for(std::map<int,int>::iterator pos =  MCSMap->begin(); pos != MCSMap->end(); pos++){
    fcommon_vetex.push_back(pos->second);
  }
  double MatchRes = -10;
  double MaxmimSim = -10;
  int ID = -1;
  SigMatchResult SMR;
  std::map<int, pair<double, SigMatchResult>> MatchResult = bk->MatchRecords;

  for(std::map<int, pair<double, SigMatchResult>>::iterator iter = MatchResult.begin(); iter != MatchResult.end(); iter++){
      // Obtain the basic block ID of firmware
      int BBLID = iter->first; 
      
      vector<int>::iterator it = find(fcommon_vetex.begin(), fcommon_vetex.end(), BBLID);
      if (it != fcommon_vetex.end())
          continue;
     
      // double Similarity = (iter->second).first;
      // SigMatchResult smr = (iter->second).second;
      bbl_info bf = FbasicBlockInfo[BBLID];
      
      SigMatchResult smr = SigMatch(bk, bf, MCSMap);
      double Similarity = get<0>(smr);
      double InstRaio = get<3>(smr); 
      double tmp = Similarity*(1-InstRaio);

      if( tmp > MatchRes){
        MatchRes = tmp;
        MaxmimSim = Similarity;
        ID = BBLID;
        SMR = smr;
      }
  }
  return make_pair(ID, make_pair(MaxmimSim,SMR));
}

/*
In this function we tranverse
input :SScfgk
output: 
*/
NToOneResult ObtainMatchCandidate(std::set<int> *SScfgk, std::set<int> *SScfgf, Mapbbl *KbasicBlockInfo, Mapbbl *FbasicBlockInfo, std::map<int,int> *MCSMap,
std::queue<int> *kcommon_subgraph,std::vector<int> *kcommon_node, std::vector<int> *remain_graph1,
std::queue<int> *fcommon_subgraph,std::vector<int> *fcommon_node, std::vector<int> *remain_graph2, std::map<llvm::Instruction*, int> *DeletedSSlists){
  // content records logs.
  string content = "";
  vector<int> deletedSScfgk;
  std::map<int, std::vector<int>> MatchResult;
  for(set<int>::iterator iter=SScfgk->begin(); iter != SScfgk->end(); ){
    std::vector<int> matchList;
    int BBLIDk = *iter;
    // obtain the bbl_info of BBLIDk
    bbl_info bblk =  ObtainBBInfo(BBLIDk, KbasicBlockInfo);
    // tranverse the MatchRecords of each bblk in SScfgk.
    OP<<"\n The size of MatchRec:"<< (bblk->MatchRecords).size();
    int count  = 0;
    for(std::map<int, pair<double, SigMatchResult>>::iterator iter1 = (bblk->MatchRecords).begin(); iter1 !=(bblk->MatchRecords).end(); iter1++){
      count++;
      int BBLIDf = iter1->first;
      OP<<"\nBBLIDf:"<<BBLIDf;
      OP<<"\ncount:"<<count;
      double Similarity = (iter1->second).first;
      SigMatchResult smr = (iter1->second).second;
      double InstRaio = get<3>(smr); 
      content = content + "\nBBLIDk: "+ getIntContent(BBLIDk) + ", BBLIDf: "+ getIntContent(BBLIDf) + ". Similarity: " +getDoubleContent(Similarity);
      // if BBLIDf is a matched node in MCSMap, we will not include it to the matchList
      if(findkeyByvalue(*MCSMap, BBLIDf) != -1)
        continue;
      
      bbl_info bblf =  ObtainBBInfo(BBLIDf, FbasicBlockInfo);
      if((Similarity > Threshhod_process_1_2) && (InstRaio < InstRaioThreshhod ) && (std::abs(int((bblk->bbl)->size()-(bblf->bbl)->size()))<DiffNum )){  
        content = content + "\n"+getIntContent(BBLIDk) + " is matched  with " + getIntContent(BBLIDf) +"\n"; 
        map<llvm::Instruction*, int> deletedSSlist = get<2>(smr);
        if(deletedSSlist.size()>0)
          UpdatedeletedSSlist(&deletedSSlist, DeletedSSlists);
        UpdateVetex(BBLIDk,kcommon_subgraph,kcommon_node,remain_graph1,
              BBLIDf,fcommon_subgraph,fcommon_node,remain_graph2,MCSMap);  
        SScfgk->erase(iter++);  
        break;
      }
      if((Similarity > Threshhod_process_3))
        matchList.push_back(BBLIDf);
    }
    // for some bblk, the similarity of the matched bblf is larger thatn Threshhod_process_3
    if(MCSMap->find(BBLIDk) == MCSMap->end()){
      iter++;
      if(matchList.size()!= 0){
        MatchResult.insert(make_pair(BBLIDk, matchList));
        content = content + "\nBBLIDk: "+ getIntContent(BBLIDk)+"; BBLIDf: {"+ getvectorContent(matchList)+"}\n";
      }
      else{
        deletedSScfgk.push_back(BBLIDk);
      }
    }
  }
  return make_tuple(MatchResult, content, deletedSScfgk);
}



/*
 basicblockIDk is the deleted basic block
 the similarity score if the deleted basicblock: basicblockIDk and basicblockIDf is high. if basicblockIDk
 is not in remappedNode, we remap basicblockIDk with basicblockIDf and find the real deleted basic block in MCS.
*/
int remap(int basicblockIDf, std::map<int,int> *MCSMap, std::vector<int> *DeletedBBlist, int basicblockIDk,vector<int> remappedNode,Mapbbl *KBasicBlockInfo, Mapbbl *FBasicBlockInfo){

  string contend = "";
  int BBlID = -1;
  bbl_info bblk = ObtainBBInfo(basicblockIDk, KBasicBlockInfo);
  bbl_info bblf = ObtainBBInfo(basicblockIDf, FBasicBlockInfo);
  std::map<int, pair<double, SigMatchResult>> MatchRecords = bblk->MatchRecords;
  
  if(find(remappedNode.begin(), remappedNode.end(), basicblockIDk) == remappedNode.end()){
    // BBlID is the node that is previously  mapped with basicblockIDf.
    BBlID = findkeyByvalue(*MCSMap, basicblockIDf);
    bbl_info bblpk = ObtainBBInfo(BBlID, KBasicBlockInfo);
    contend = contend +"\nbasicblockIDk: "+ getIntContent(basicblockIDk);
    contend = contend +"\nBBlID: "+ getIntContent(BBlID);
    contend = contend +"\nbasicblockIDf: "+ getIntContent(basicblockIDf);
    if(BBlID != -1){
      SigMatchResult pre = SigMatch(bblpk, bblf, MCSMap);
      SigMatchResult post = SigMatch(bblk, bblf, MCSMap);
      double PreSimilarity = get<0>(pre);
      double PosSimilarity = get<0>(post);
      contend = contend +"\nPreSimilarity: "+ getDoubleContent(PreSimilarity);
      contend = contend +"\nPosSimilarity: "+ getDoubleContent(PosSimilarity);
      
      // we find that the similarity score of the new matched node is higher than the previous matched node.
      if(PreSimilarity < PosSimilarity){
          MCSMap->erase(MCSMap->find(BBlID));
          MCSMap->insert(make_pair(basicblockIDk, basicblockIDf));
          std::vector<int>::iterator  iter = find(DeletedBBlist->begin(), DeletedBBlist->end(), basicblockIDk);
          if(iter != DeletedBBlist->end())
            DeletedBBlist->erase(iter);
          DeletedBBlist->push_back(BBlID);
          contend = contend +"\nEarse: "+ getIntContent(BBlID);
      }
      else 
        BBlID =  -1;
    }
  }
  return BBlID;
}


void MergeNode(std::map<int,int>  *relatedvetexInMCS, std::map<int,int>  relatedvetex){
  for(std::map<int,int>::iterator iter = relatedvetex.begin(); iter != relatedvetex.end(); iter++){
    if(relatedvetexInMCS->find(iter->first) == relatedvetexInMCS->end())
      relatedvetexInMCS->insert(make_pair(iter->first, iter->second));
  }
}

std::set<int> MergeNode(set<int> left, set<int> right, set<int> L, set<int> R){
  std::set<int> tmp1, tmp2, Union;
  set_union(left.begin(), left.end(), right.begin(), right.end(), inserter(tmp1,tmp1.begin()));
  set_union(L.begin(), L.end(), R.begin(), R.end(), inserter(tmp2, tmp2.begin())); 
  set_union(tmp1.begin(), tmp1.end(), tmp2.begin(), tmp2.end(), inserter(Union, Union.begin())); 
  return Union;
}

std::set<int> MergeNode(set<int> left, set<int> right){
  set<int> Union;
  set_union(left.begin(), left.end(), right.begin(), right.end(), inserter(Union, Union.begin()));
  return Union;
}


std::map<int,int> ObtainRelatedVetexInMCS(std::map<int,int>  *relatedvetex,  Mapbbl *FbasicBlockInfo, std::map<int,int> *MCSMap){
  std::map<int,int>  FrelatedvetexInMCS;
  std::vector<int> common_node;
  // Obtain FrelatedvetexInMCS
  for(std::map<int,int>::iterator iter = relatedvetex->begin(); iter != relatedvetex->end(); iter++){
    int relatedBBLID = iter->second;
    int relatedBBLType = iter->first;
    // if the node is in MCSMap
    std::map<int,int>::iterator item = MCSMap->find(relatedBBLID);
    if(item != MCSMap->end()){
      int basicblockIDf = item->second;
      bbl_info relatedBBLf = ObtainBBInfo(basicblockIDf, FbasicBlockInfo);
      MergeNode(&FrelatedvetexInMCS, ObtainRelatedVetex(relatedBBLf, common_node)); 
    }
  }
  return FrelatedvetexInMCS;
}

std::pair<int, string> ReConfirmMCSNode(std::vector<int> *DeletedBBlist, std::map<int,int> *MCSMap, bbl_info deletedbbl, 
                                        Mapbbl *KBasicBlockInfo, Mapbbl *FBasicBlockInfo, vector<int> remappedNode){
  // bblk is the deleted basic block
  string content ="DumpMCSMap\n";
  int newDeletedBB = -1;
  int DeletedbasicblockID = deletedbbl->BBLID;
  content = content +" MCSMap  is: "+ DumpMCSMap(MCSMap);
  content = content + " MCSMap size is: " +getIntContent(MCSMap->size());
  for(std::map<int,int>::iterator iter = MCSMap->begin(); iter != MCSMap->end(); iter++){
    int basicblockIDk = iter->first;
    int basicblockIDf = iter->second;
    bbl_info bblk = ObtainBBInfo(basicblockIDk, KBasicBlockInfo);
    bbl_info bblf = ObtainBBInfo(basicblockIDf, FBasicBlockInfo);
    if(!bblk ||!bblf)
      continue;
    std::vector<int> common_node;
    SigMatchResult smr;
    double Similarity;
    vector<IdenticalInst> identicalInsts;
    map<llvm::Instruction*, int>  deletedSSlist;
    float InstRaio = 0;
    smr = SigMatch(deletedbbl, bblf, MCSMap);
    
    Similarity = get<0>(smr);
    content = "\nCompare BB" + getIntContent(DeletedbasicblockID) +" with BB "+getIntContent(basicblockIDf)
        + " Similarity is:" + getDoubleContent(Similarity); 
    InstRaio = get<3>(smr);
   
    AddCMPItem(bblk, basicblockIDf, Similarity, smr);
    AddCMPItem(bblf, basicblockIDk, Similarity, smr);
    if((Similarity > Threshhod_process_1) &&(InstRaio < InstCMPThreshhod) ){
        content = "\nBB" + getIntContent(DeletedbasicblockID) +" may be matched with BB"+getIntContent(basicblockIDf)
        + " Similarity is:" + getDoubleContent(Similarity);
        /*
         we match the related vetex of the deleted bblk and the corresponding bblf
        */
        std::map<int,int>  relatedvetexInkernel = ObtainRelatedVetex(deletedbbl, common_node);
        std::map<int,int>  relatedvetexInfirmware = ObtainRelatedVetex(bblf, common_node);
        content = content +"\nrelatedvetex of the deleted BB: "+ DumpmapII(relatedvetexInkernel);
        content = content +"\nrelatedvetex of the bblf: "+ DumpmapII(relatedvetexInfirmware);
        int MatchedRelatedVetex = 0;
        for(std::map<int,int>::iterator iterk = relatedvetexInkernel.begin();
          iterk != relatedvetexInkernel.end(); iterk++){
            SigMatchResult smrR;
            double SimilarityR;
            vector<IdenticalInst> identicalInstsR;
            map<llvm::Instruction*, int>  deletedSSlistR;
            float InstRaioR = 0;
            for(std::map<int,int>::iterator iterf = relatedvetexInfirmware.begin();
              iterf != relatedvetexInfirmware.end(); iterf++){
                bbl_info bblkR = ObtainBBInfo(iterk->first, KBasicBlockInfo); 
                bbl_info bblfR = ObtainBBInfo(iterf->first, FBasicBlockInfo);
                smr = SigMatch(bblkR, bblfR, MCSMap);
                SimilarityR = get<0>(smr); 
                InstRaioR = get<3>(smr);
                if((SimilarityR > Threshhod_process_1) &&(InstRaioR < InstCMPThreshhod) ){
                    content = content + "\nCompare BB"+getIntContent(iterk->first)+" with BB"+getIntContent(iterf->first)+ 
                    " similarity is: "+ getDoubleContent(SimilarityR);
                    MatchedRelatedVetex++;
                }
            }
        }
        content = content + "\nMatchedRelatedVetex: "+ getIntContent(MatchedRelatedVetex);
        double RelatedRatio = ((double)MatchedRelatedVetex/relatedvetexInkernel.size());
        content = content + "\nRelatedRatio"+getDoubleContent(RelatedRatio);
        if(RelatedRatio >= RelatedVetexRaioThreshhod){
          content = content + "\nbasicblockIDf:" +getIntContent(basicblockIDf)+" DeletedbasicblockID:"+ getIntContent(DeletedbasicblockID);
          newDeletedBB = remap(basicblockIDf, MCSMap, DeletedBBlist, DeletedbasicblockID, remappedNode, KBasicBlockInfo, FBasicBlockInfo);
          content = content + "\nnewDeletedBB: "+ getIntContent(newDeletedBB);
          break;
        }

    }

  }
  return make_pair(newDeletedBB,content);

}

string ReConfirmDeletedBB(std::vector<int> *DeletedBBlist, std::map<llvm::Instruction*, int> *DeletedSSlists,std::map<int,int> *MCSMap,
 Mapbbl *FbasicBlockInfo, Mapbbl *KbasicBlockInfo, std::set<int> *SScfgk, std::map<int, int> *MatchResult){
   
   OP<<"\nReConfirmDeletedBB\n";
   string content="\nReConfirmDeletedBB";
   // We push each element in DeletedBBlist to a queue
   std::queue<int> DeletedBB;
   for(std::vector<int>::iterator iter = DeletedBBlist->begin(); iter != DeletedBBlist->end(); iter++){
     DeletedBB.push(*iter);
   }
   // record the vetexes that have been remapped.
   vector<int> remappedNode;
   
   while(!DeletedBB.empty()){
      
      std::vector<int> common_node;
      SigMatchResult smr;
      double Similarity;
      vector<IdenticalInst> identicalInsts;
      map<llvm::Instruction*, int>  deletedSSlist;
      float InstRaio = 0;

      int basicblockIDk = DeletedBB.front();
      DeletedBB.pop();
      // We obtain the basic block info of the deleted basic block
      bbl_info bblk = ObtainBBInfo(basicblockIDk, KbasicBlockInfo);
      
      // We obtain the related vetexes of the deleted basic block
      if(bblk == NULL)
        continue;

      bool remapStatus = false;

      std::map<int,int>  relatedvetex =  ObtainRelatedVetex(bblk, common_node );
      content = content + "\nThe deleted BB: "+ getIntContent(basicblockIDk);
      content = content +"\nrelatedvetex of the deleted BB: "+ DumpmapII(relatedvetex);
      content = content + "MCSmap:\n" + DumpMCSMap(MCSMap);

      std::map<int,int>  Frelatedvetex;
      for(std::map<int,int>::iterator iter0 = relatedvetex.begin(); iter0 != relatedvetex.end(); iter0++){
        int relatedBBLID = iter0->first;
        content = content + "\nrelated vetex:"+ getIntContent(relatedBBLID)+"\n";
        int relatedBBLType = iter0->second;
        // if the node is in MCSMap
        std::map<int,int>::iterator item = MCSMap->find(relatedBBLID);
        if(item != MCSMap->end()){
          int basicblockIDf = item->second;
          content = content + "In MCS "+ getIntContent(relatedBBLID) +" "+ getIntContent(basicblockIDf) +"\n";
          bbl_info relatedBBLf = ObtainBBInfo(basicblockIDf, FbasicBlockInfo);
          if(!relatedBBLf)
            continue;
          std::map<int,int>  relatedvetexInfirmware = ObtainRelatedVetex(relatedBBLf, common_node);
          MergeNode(&Frelatedvetex, relatedvetexInfirmware); 
        }
      }

      // if the related vetexes of the deleted basic block are in MCS, we get the corresponding 
      // vetex in firmware and furtherly obtain the the related vetexes in firmware.
      //std::map<int,int>  Frelatedvetex =  ObtainRelatedVetexInMCS(&relatedvetex, FbasicBlockInfo, MCSMap);
      content = content +"\nFrelatedvetex: "+ DumpmapII(Frelatedvetex);
      if(Frelatedvetex.size()>0){
        for(std::map<int,int>::iterator iter1 = Frelatedvetex.begin(); 
          iter1!= Frelatedvetex.end(); iter1++){
          int basicblockIDf = iter1->first;
          bbl_info bblf = ObtainBBInfo(basicblockIDf, FbasicBlockInfo);
          if(!bblf)
            continue;
          std::map<int, pair<double, SigMatchResult>> MatchRecords = bblk->MatchRecords;
          if(MatchRecords.find(basicblockIDf) != MatchRecords.end())
              Similarity = MatchRecords[basicblockIDf].first ;
          else{
            smr = SigMatch(bblk, bblf, MCSMap );
            Similarity = get<0>(smr); 
            AddCMPItem(bblk, basicblockIDf, Similarity, smr);
            AddCMPItem(bblf, basicblockIDk, Similarity, smr);
            identicalInsts = get<1>(smr); 
            deletedSSlist = get<2>(smr); 
            InstRaio = get<3>(smr); 
            content = content + "\nCompare BB"+getIntContent(basicblockIDk)+" with BB"+getIntContent(basicblockIDf)+ " similarity is: "+ getDoubleContent(Similarity)+ " InstRaio is: "+ getDoubleContent(InstRaio);
          }

          content = content + "\n Test MCSmap:\n" + DumpMCSMap(MCSMap);


          if(Similarity > Threshhod_process_0){
            #ifdef Debug_SO
              OP<<"\033[35m"<< basicblockIDk <<" is matched  with "<< basicblockIDf<<"\033[0m\n";
              OP<<"\033[35mInstRaio is: "<< InstRaio <<"\033[0m\n";
            #endif
            int newDeletedBB = remap(basicblockIDf, MCSMap, DeletedBBlist,basicblockIDk, remappedNode, KbasicBlockInfo, FbasicBlockInfo);
            

            
            if((newDeletedBB != -1)){
            content = content +"\nRemap. The previoud deleted basic block: "+ getIntContent(basicblockIDk) + " is matched  with " + getIntContent(basicblockIDf) 
            +". The new deleted basic block is:"+ getIntContent(newDeletedBB)+  " \n";

            
            map<int,int>::iterator delPos = MatchResult->find(newDeletedBB);
            if( delPos != MatchResult->end())
            MatchResult->erase(delPos);
            MatchResult->insert(make_pair(basicblockIDk, basicblockIDf));

            if(SScfgk->find(basicblockIDk) != SScfgk->end())
              SScfgk->erase(basicblockIDk);
            if(SScfgk->find(newDeletedBB) == SScfgk->end())
              SScfgk->insert(newDeletedBB);
              DeletedBB.push(newDeletedBB);
              remappedNode.push_back(newDeletedBB);
              remappedNode.push_back(basicblockIDk);
              remapStatus = true;
            }
            if(deletedSSlist.size()>0) 
                UpdatedeletedSSlist(&deletedSSlist, DeletedSSlists);       
            break;          
          } 
        }
      }
      if(remapStatus == false){
        content = content + "\nMCSmap:\n" + DumpMCSMap(MCSMap);
        content = content +"\nBegin ReConfirmMCSNode: ";
        std::pair<int, string> res =ReConfirmMCSNode(DeletedBBlist, MCSMap, bblk, KbasicBlockInfo, FbasicBlockInfo, remappedNode);
        int newDeletedBB = res.first;
        content = content +"\nReConfirmMCSNode: "+ res.second;
        if((newDeletedBB != -1)){
          DeletedBB.push(newDeletedBB);
          remappedNode.push_back(newDeletedBB);
          remappedNode.push_back(basicblockIDk);
        }
      }
   }
return content;
}

/*
  MatchK1FN match N basic block in firmware to one basic block in kernel.
  DeletedSSlists records the deleted sensitive operations.
  DeletedBBlist records the deleted basick blocks.
  return the log of processing MatchK1FN.
*/
string MatchK1FN( std::map<int, std::vector<int>> *K1FN, Mapbbl *KbasicBlockInfo, Mapbbl *FbasicBlockInfo, std::map<llvm::Instruction*, int> *DeletedSSlists, 
std::vector<int> *remain_graph1, std::vector<int> *remain_graph2,std::queue<int> *kcommon_subgraph,std::vector<int> *kcommon_node, std::set<int> *SScfgk,
std::queue<int> *fcommon_subgraph,std::vector<int> *fcommon_node, std::set<int> *SScfgf, std::vector<int> *DeletedBBlist, std::map<int,int> *MCSMap){
  string contend ="\nPerform MatchK1FN\n";
  for(std::map<int, std::vector<int>>::iterator iter = K1FN->begin(); iter !=K1FN->end(); iter++){
    int KID = iter->first;
    bbl_info bblk = ObtainBBInfo(KID, KbasicBlockInfo);
    if(!bblk)
      continue;
    vector<int> FIDs = iter->second;
    std::vector<int> common_node;
    if(FIDs.size()==1){
        UpdateDeletedBBlistN(KID, remain_graph1, DeletedBBlist);
        contend = contend + "\nThe size of Fset is 1. The deleted BB is: "+getIntContent(KID);
     }
    // determine that if there is parent-child relation between these two nodes.
    if(FIDs.size()==2){
      bbl_info blf0 = ObtainBBInfo(FIDs[0], FbasicBlockInfo);
      bbl_info blf1 = ObtainBBInfo(FIDs[1], FbasicBlockInfo);
      int BBlIDf0 = blf0->BBLID;
      int BBlIDf1 = blf1->BBLID;
      SigMatchResult smr0 = SigMatch_Mul2One(bblk, blf0, MCSMap);
      SigMatchResult smr1 = SigMatch_Mul2One(bblk, blf1, MCSMap);
      SigMatchResult  smr_res;
  
      double sim0 = get<0>(smr0);
      double sim1 = get<0>(smr1);
      double instsequencesimilarity0 =get<5>(smr0);
      double instsequencesimilarity1 =get<5>(smr1);

      double simmax = sim0 > sim1 ? sim0 : sim1;
      double instsequencesimilarity_max = instsequencesimilarity0 > instsequencesimilarity1 ? instsequencesimilarity0: instsequencesimilarity1;
      // the concentrated Similarity
      double concentratedsim = 0.0;
      double concentrated_InSeqSim = 0.0;
      
      // construct a New basic block by connected blk0, blk1
      bbl_info newbbl0_1 = ConstructNewBasicBlock(blf0, blf1) ;
      bbl_info newbbl1_0 = ConstructNewBasicBlock(blf1, blf0) ;
      SigMatchResult smr0_1, smr1_0;
      double sim0_1 = 0.0, sim1_0 = 0.0;
      double instsequencesimilarity0_1 = 0.0, instsequencesimilarity1_0 = 0.0;

      if(newbbl0_1){
        smr0_1 = SigMatch_Mul2One(bblk, newbbl0_1, MCSMap);
        sim0_1 = get<0>(smr0_1);
        instsequencesimilarity0_1 = get<5>(smr0_1);
      }  
      if(newbbl1_0){   
        smr1_0 = SigMatch_Mul2One(bblk, newbbl1_0, MCSMap);
        sim1_0 = get<0>(smr1_0);
        instsequencesimilarity1_0 = get<5>(smr1_0);
      }
     if(sim0_1 > sim1_0){
        smr_res = smr0_1;
        concentratedsim = sim0_1;
        contend = contend + get<4>(smr_res);
      }
      else{
        smr_res = smr1_0;
        concentratedsim = sim1_0;
        contend = contend + get<4>(smr_res);
      }

      concentrated_InSeqSim = instsequencesimilarity0_1 > instsequencesimilarity1_0 ? instsequencesimilarity0_1 : instsequencesimilarity1_0;
      contend = contend + "\nbblf0:" + getIntContent(BBlIDf0)+ " bblf1:" + getIntContent(BBlIDf1)+ "; bblk:" + getIntContent(KID)+
       " concentrated Similarity is: "+ getDoubleContent(concentratedsim)+"; BBlIDf0 Similarity is: "+ getDoubleContent(sim0)+ "; BBlIDf1 Similarity is: "+ getDoubleContent(sim1) +
       "\nconcentrated InstSeq Similarity is: "+ getDoubleContent(concentrated_InSeqSim)+  "; instsequencesimilarity_max is: "+ getDoubleContent(instsequencesimilarity_max)+
       "; BBlIDf0 Similarity is: "+ getDoubleContent(instsequencesimilarity0_1)+ "; BBlIDf1 Similarity is: "+ getDoubleContent(instsequencesimilarity1_0)+"\n";
        
      // if one node should be mapped with two node.
      if((concentratedsim > simmax) && (concentrated_InSeqSim > instsequencesimilarity_max )){
        UpdateVetex(KID,kcommon_subgraph,kcommon_node,remain_graph1,
                    BBlIDf0, fcommon_subgraph,fcommon_node,remain_graph2,MCSMap);

        UpdateVetex(BBlIDf1, fcommon_subgraph,fcommon_node,remain_graph2);
        contend = contend + "\nBBlIDf0: " +getIntContent(BBlIDf0) + " together with BBlIDf1: " +getIntContent(BBlIDf1)+ " should be matched with BBlIDk: "+ getIntContent(KID);
        map<llvm::Instruction*, int>  deletedSSlist = get<2>(smr_res);
        contend = contend + "\nDumpDeletedSSO of concentrated BB:"+ DumpDeletedSSO(&deletedSSlist,KbasicBlockInfo);
	      if(deletedSSlist.size()>0) 
          UpdatedeletedSSlist(&deletedSSlist, DeletedSSlists);

        if(SScfgf->find(BBlIDf0) != SScfgf->end())
          SScfgf->erase(BBlIDf0);
        if(SScfgf->find(BBlIDf1) != SScfgf->end())
          SScfgf->erase(BBlIDf1);
        if(SScfgk->find(KID) != SScfgk->end())
          SScfgk->erase(KID);
      }
      
    }

  }
  return contend;
}



string MatchF1KN( std::map<int, std::vector<int>> *F1KN, Mapbbl *KbasicBlockInfo, Mapbbl *FbasicBlockInfo, std::map<llvm::Instruction*, int> *DeletedSSlists, 
std::vector<int> *remain_graph1, std::vector<int> *remain_graph2,std::queue<int> *kcommon_subgraph,std::vector<int> *kcommon_node, std::set<int> *SScfgk,
std::queue<int> *fcommon_subgraph,std::vector<int> *fcommon_node, std::set<int> *SScfgf,std::vector<int> *DeletedBBlist, std::map<int,int> *MCSMap){
  string contend ="\nPerform MatchF1KN\n";
  for(std::map<int, std::vector<int>>::iterator iter = F1KN->begin(); iter !=F1KN->end(); iter++){
    int FID = iter->first;
    bbl_info bblf = ObtainBBInfo(FID, FbasicBlockInfo);
    if(!bblf)
      continue;
    vector<int> KIDs = iter->second;
    std::vector<int> common_node;

    if(KIDs.size()==1){

        continue;
     }
    if(KIDs.size()==2){
      bbl_info blk0 = ObtainBBInfo(KIDs[0], KbasicBlockInfo);
      bbl_info blk1 = ObtainBBInfo(KIDs[1], KbasicBlockInfo);


      SigMatchResult smr0 = SigMatch_Mul2One(blk0, bblf, MCSMap);
      contend = contend + "\nTest";
      contend = contend +get<4>(smr0);
      SigMatchResult smr1 = SigMatch_Mul2One(blk1, bblf, MCSMap);
      contend = contend +get<4>(smr1);
      double sim0 = get<0>(smr0);
      double sim1 = get<0>(smr1);
      double instsequencesimilarity0 =get<5>(smr0);
      double instsequencesimilarity1 =get<5>(smr1);
      double simmax = sim0 > sim1 ? sim0 : sim1;
      double instsequencesimilarity_max = instsequencesimilarity0 > instsequencesimilarity1 ? instsequencesimilarity0: instsequencesimilarity1;
      int BBlIDk0 = blk0->BBLID;
      int BBlIDk1 = blk1->BBLID;

      double concentratedsim = 0.0;
      double concentrated_InSeqSim = 0.0;

      bbl_info newbbl0_1 = ConstructNewBasicBlock(blk0, blk1) ;
      bbl_info newbbl1_0 = ConstructNewBasicBlock(blk1, blk0) ;
      SigMatchResult smr0_1, smr1_0, smr_res;
      double sim0_1 = 0.0, sim1_0 = 0.0;
      double instsequencesimilarity0_1 = 0.0, instsequencesimilarity1_0 = 0.0;

      if(newbbl0_1){
        smr0_1 = SigMatch_Mul2One(newbbl0_1, bblf, MCSMap);
      	sim0_1 = get<0>(smr0_1);
	instsequencesimilarity0_1 = get<5>(smr0_1);
      }  
      if(newbbl1_0){   
        smr1_0 = SigMatch_Mul2One(newbbl1_0, bblf, MCSMap);
        sim1_0 = get<0>(smr1_0);
	instsequencesimilarity1_0 = get<5>(smr1_0);
      }

      if(sim0_1 > sim1_0){
        smr_res = smr0_1;
        concentratedsim = sim0_1;
        contend = contend + get<4>(smr_res);
      }
      else{
        smr_res = smr1_0;
        concentratedsim = sim1_0;
        contend = contend + get<4>(smr_res);
      }
      contend = contend + "\nsim0_1: "+ getDoubleContent(sim0_1) +"\nsim1_0: "+ getDoubleContent(sim1_0) ;
      concentratedsim = sim0_1 > sim1_0 ? sim0_1 : sim1_0;
      concentrated_InSeqSim = instsequencesimilarity0_1 > instsequencesimilarity1_0 ? instsequencesimilarity0_1 : instsequencesimilarity1_0;

      contend = contend + "\nbblk0:" + getIntContent(BBlIDk0)+ " bblk1:" + getIntContent(BBlIDk1)+ "\nbblk:" + getIntContent(FID)+
       " concentrated Similarity is: "+ getDoubleContent(concentratedsim)+"; BBlIDf0 Similarity is: "+ getDoubleContent(sim0)+ "; BBlIDf1 Similarity is: "+ getDoubleContent(sim1)+"\n" +
       "\nconcentrated InstSeq Similarity is: "+ getDoubleContent(concentrated_InSeqSim)+ "; instsequencesimilarity_max is: "+ getDoubleContent(instsequencesimilarity_max)+
       "; BBlIDk0 Similarity is: "+ getDoubleContent(instsequencesimilarity0_1)+ "; BBlIDk1 Similarity is: "+ getDoubleContent(instsequencesimilarity1_0)+"\n";
          
      // if one node should be mapped with two node.
      if((concentratedsim > simmax) && (concentrated_InSeqSim > instsequencesimilarity_max )){

        contend = contend + "\nBBlIDk0: " +getIntContent(BBlIDk0) + " together with BBlIDk1: " +getIntContent(BBlIDk1)+ " should be matched with BBlIDf: "+ getIntContent(FID);

        UpdateVetex(BBlIDk0,kcommon_subgraph,kcommon_node,remain_graph1,SScfgk,
                    FID, fcommon_subgraph,fcommon_node,remain_graph2, SScfgf,MCSMap);
        UpdateVetex(BBlIDk1,kcommon_subgraph,kcommon_node,remain_graph1,SScfgk,
                    FID, fcommon_subgraph,fcommon_node,remain_graph2,SScfgf,MCSMap);
        map<llvm::Instruction*, int>  deletedSSlist = get<2>(smr_res);  
        if(deletedSSlist.size()>0){ 
          UpdatedeletedSSlist(&deletedSSlist, DeletedSSlists);
          contend = contend + "\nDumpDeletedSSO:"+ DumpDeletedSSO(&deletedSSlist,KbasicBlockInfo);

        }
        
        if(SScfgf->find(FID) != SScfgf->end())
          SScfgf->erase(FID);
        if(SScfgk->find(BBlIDk0) != SScfgk->end())
          SScfgk->erase(BBlIDk0);
        if(SScfgk->find(BBlIDk1) != SScfgk->end())
          SScfgk->erase(BBlIDk1);
      }
    }
  }
  return contend;
}


bbl_info  ConstructNewBasicBlock(bbl_info bbl0, bbl_info bbl1){
    string contend = "NewBB:\n";
    bbl_info newbbl = new(bbl);
    (newbbl)->BBLID = NewBasicBlockID;

    vector<llvm::Instruction*> NewInstructions;
    NewInstructions.insert( NewInstructions.end(), bbl0->Instructions.begin(), bbl0->Instructions.end()-1 );
    NewInstructions.insert( NewInstructions.end(), bbl1->Instructions.begin(), bbl1->Instructions.end() );

    (newbbl)->Instructions = NewInstructions;
    Feature bblfeature = bblFeature((newbbl)->Instructions);
    (newbbl)-> Inbbfeature = bblfeature;
    contend = contend +"\nBBlIDk0: "+getIntContent(bbl0->BBLID);
    contend = contend +"\nBBlIDk1: "+getIntContent(bbl1->BBLID);

    contend = contend + "\n Merage instuction:\n";
    for(vector<llvm::Instruction*>::iterator iter = NewInstructions.begin(); iter != NewInstructions.end();iter++){
      Instruction *Inst = *iter;
      contend = contend +getInstContent(Inst)+"\n";
    }

    ParentNode Newparentnode = bbl0->parentnode;

    ChildrenNode Newchildrennode = bbl1->childrennode;
    SilbingNode Newsilibingnode = bbl1-> silibingnode;
    
    (newbbl)->parentnode = Newparentnode;
    (newbbl)->childrennode = Newchildrennode;
    (newbbl)->silibingnode = Newsilibingnode;
    map<llvm::Instruction*, int> NewSensitive_Info; 
    contend = contend +"\n Merage sensitive_Info:\n";

    NewSensitive_Info.insert(bbl0->Sensitive_Info.begin(), bbl0->Sensitive_Info.end());
    NewSensitive_Info.insert(bbl1->Sensitive_Info.begin(), bbl1->Sensitive_Info.end());

    for(map<llvm::Instruction*, int>::iterator iter1 = NewSensitive_Info.begin(); iter1 != NewSensitive_Info.end();iter1++){
      Instruction *Inst = iter1->first;
      contend = contend +getInstContent(Inst)+"\n";
    }
    (newbbl)->Sensitive_Info = NewSensitive_Info;
    return newbbl;
}

/*
The input MatchCandidates is a map that key is basic block k  and value is the list basic block f  
MatchCandidates: {bblk:1 bblf:2,3,4
                  bblk:5 bblf:5,7
                  bblk:10 bblf:12,13
                 } 
The output are K1FN, KNF1, and One2One 
              K1FN: is a map that key is basic block k  and value is the list basic block f   {bblk:1 bblf:2,3,4}
              KNF1: is a map that key is basic block f  and value is the list basic block k   {bblf:1 bblk:2,3,4} 
              One2One records one to one mapping {bblf:1 bblk:1}        
*/
SplitResult SplitCandidates( std::map<int, std::vector<int>> *MatchCandidates){
  std::map<int, std::vector<int>> KNF1, K1FN;
  vector<int> deletedSScfgk;
  std::map<int,int> Tmp;
  std::map<int,int> One2One;
  vector<int> bblfs;
  for(std::map<int, std::vector<int>>::iterator iter = MatchCandidates->begin(); iter != MatchCandidates->end(); iter++){
      // one basic block of  kernel  match to several basic blocks of firmware.
      if((iter->second).size() > 1)
        K1FN.insert(*iter);
      else if((iter->second).size() == 1){
        Tmp.insert(make_pair(iter->first, (iter->second)[0]));
        // bblfs records all the bblf ID that may match to mutiple bblks.
        bblfs.push_back((iter->second)[0]);
      }     
  }
  for( vector<int>::iterator iter1 = bblfs.begin(); iter1!=bblfs.end();iter1++){
          int BBLIDf =  *iter1;
          if(count(bblfs.begin(),bblfs.end(), BBLIDf)>1){
            std::vector<int> matchList;
            for(std::map<int,int>::iterator iter2 = Tmp.begin(); iter2 != Tmp.end(); iter2++){
              if(iter2->second == BBLIDf)
                matchList.push_back(iter2->first); 
            }
            KNF1.insert(make_pair(BBLIDf, matchList));
          }
          else{
            //deletedSScfgk.push_back(findkeyByvalue(Tmp, BBLIDf));
            One2One.insert(make_pair(findkeyByvalue(Tmp, BBLIDf), BBLIDf));
          }
      }
  // we find  the cases that one basic block of  firmware  match to several basic blocks of kernel.
  return make_tuple(K1FN, KNF1, deletedSScfgk, One2One);
}



void GenerateDeletedSoNew(set<int> SScfgk,std::queue<int> *kcommon_subgraph,std::vector<int> *kcommon_node,Mapbbl KbasicBlockInfo,std::vector<int> *remain_graph1,
        set<int> SScfgf,std::queue<int> *fcommon_subgraph,std::vector<int> *fcommon_node,Mapbbl FbasicBlockInfo , std::vector<int> *remain_graph2,
        std::map<int,int> *MCSMap, std::vector<int> *DeletedBBlist, std::map<llvm::Instruction*, int> *DeletedSSlists,char*  local_msg, string filename)
        {
          string content ="";
          std::map<int, int> MatchResult;
          #ifdef Debug_SO
              OP<<"\ncurrent SScfgk :  ";
              PrintSet(SScfgk);
              OP<<"current SScfgf :  ";
              PrintSet(SScfgf);
          #endif
          content = content + "\ncurrent SScfgk :  "+ DumpSet(SScfgk) + "current SScfgf :  "+ DumpSet(SScfgf);
     

CalDDSO:  while(!kcommon_subgraph->empty()){
            #ifdef Debug_SO
              OP<<"Print MCS: \n";
              PrintVectorI(*kcommon_node); 
              PrintVectorI(*fcommon_node);
              OP<<"\ncurrent SScfgk :  ";
              PrintSet(SScfgk);
              OP<<"current SScfgf :  ";
              PrintSet(SScfgf);
            #endif
            content = content + "\nKMCSQueue:"+DumpVectorI(*kcommon_node) +"\nFMCSQueue:"+ DumpVectorI(*fcommon_node);

            int kcommon_vetex = kcommon_subgraph->front();
            kcommon_subgraph->pop();
            if(kcommon_node->size())
              DeleElem(kcommon_node,kcommon_vetex); 
            int fcommon_vetex = FindNode(MCSMap, kcommon_vetex);

            // The related vetexes that connected by CFG.
            std::map<int,int>  krelatedvetex, frelatedvetex;
            // The related vetexes that connected by DFG.
            std::vector<int>  kDFGrelatedvetex, fDFGrelatedvetex;

            krelatedvetex = ObtainCFGRelatedVetex(kcommon_vetex, MCSMap, KbasicBlockInfo, 0);                
            #ifdef Debug_SO
              OP<<"The poped kcommon_vetex is : "<<kcommon_vetex<<" ";
              OP<<"The Related Vetex of  kcommon_vetex: ";
              PrintmapII(krelatedvetex); 
            #endif
            content = content + "\npoped kcommon_vetex is : "+getIntContent(kcommon_vetex)+ "; Related Vetex of  kcommon_vetex: "+ DumpmapII(krelatedvetex);
            

         
            if (krelatedvetex.size() != 0){
              for (std::map<int,int>::iterator iter=krelatedvetex.begin(); iter!=krelatedvetex.end(); iter++)
              {
                 
                  bbl_info rk = KbasicBlockInfo[iter->first];
                
                  frelatedvetex = ObtainCFGRelatedVetex(fcommon_vetex, MCSMap, FbasicBlockInfo, 1);
                  
                  #ifdef Debug_SO
                    OP<<"The poped fcommon_vetex is : "<<fcommon_vetex<<" ";
                    OP<<"The Related Vetex of  fcommon_vetex : ";
                    PrintmapII(frelatedvetex); 
                  #endif

                  content = content + "\npoped fcommon_vetex is : "+getIntContent(fcommon_vetex) + "; Related Vetex of  kcommon_vetex: "+DumpmapII(frelatedvetex);

                  if(frelatedvetex.size()==0)
                    continue; 

                              
                  
                  map<llvm::Instruction*, int>  deletedSSlist;
                  map<llvm::Instruction*, int> sensitive_Infok = rk->Sensitive_Info;
                  llvm::BasicBlock *bblk = rk->bbl;
                  bool Matched = false;
                
                  int type = iter->second; 
                  int basicblockIDk = iter->first;
                  
               
                  int basicblockIDf;
                  bbl_info rf;
                  SigMatchResult smr;
                  double Similarity;
                  vector<IdenticalInst> identicalInsts;
                  float InstRaio = 0;
                  content = content + "\nbasicblockIDk (" +getIntContent(basicblockIDk) + "): not in MCS and contain SSOP";
                  
                  
                  // 1. In frelatedvetex, we only compare the basic block node that conatain sensitive operation.
                  for(std::map<int,int>::iterator iter1=frelatedvetex.begin();iter1!=frelatedvetex.end();iter1++){
                      basicblockIDf = iter1->first;
                      if(IsChecked(rk, basicblockIDf))
                        continue;
                     
                      #ifdef Debug_SO
                        OP<<"\033[32mbasicblockIDf  ("<<basicblockIDf<<") is not in MCS and in frelatedvetex and contain SSOP. \033[0m\n";
                      #endif
                      content = content + "\nbasicblockIDf (" +getIntContent(basicblockIDf) + "): not in MCS, in frelatedvetex, contain SSOP.";
                      
                      
                      rf = FbasicBlockInfo[basicblockIDf];
                      if(rf==NULL || rk==NULL) continue;
                      if(rk->MatchRecords.find(basicblockIDf) != rk->MatchRecords.end()) continue;
                      
                      

                      smr = SigMatch(rk, rf,MCSMap );
                      Similarity = get<0>(smr); 

                      AddCMPItem(rk, basicblockIDf, Similarity, smr);
                      AddCMPItem(rf, basicblockIDk, Similarity, smr);
                     
                      content = content + get<4>(smr);
                      
                      identicalInsts = get<1>(smr); 
                      if(Similarity > Threshhod_process_1){
                          
                         
                          content = content +"\n"+ getIntContent(basicblockIDk) + " is matched  with " + getIntContent(basicblockIDf) +"\n";
                         
                          if(fcommon_node->size())
                              DeleElem(fcommon_node,fcommon_vetex); 
                          
                          deletedSSlist = get<2>(smr); 
                          InstRaio = get<3>(smr); 
                         
                          if((InstRaio < InstCMPThreshhod) && (std::abs(int((rk->bbl)->size()-(rf->bbl)->size()))<DiffNum )){ //指令总数相差不多,说明是1对1) 
                            if(deletedSSlist.size()>0) 
                                UpdatedeletedSSlist(&deletedSSlist, DeletedSSlists);
                            UpdateVetex(basicblockIDk,kcommon_subgraph,kcommon_node,remain_graph1,&SScfgk,
                            basicblockIDf,fcommon_subgraph,fcommon_node,remain_graph2,&SScfgf,MCSMap);   
                            Matched = true;
                            MatchResult.insert(make_pair(basicblockIDk,basicblockIDf));
                            DeleteItem(&frelatedvetex, basicblockIDf);
                          }
                          break; 
                      }
                  }
                
              }
            }
      }
      
      content = content +  "\nMCS is empty"+ "\n";
      content = content + DumpMCSMap(MCSMap);
      content = content + "\ncurrent SScfgk :  "+ DumpSet(SScfgk) + "current SScfgf :  "+ DumpSet(SScfgf);
      {
          // Since the largest common subgraph is empty, we can check SScfgk one by one.
          for(set<int>::iterator itk = SScfgk.begin(); itk != SScfgk.end(); ){
             
              bool Matched = false;
              int basicblockIDk = *itk;
              int basicblockIDf;
              double Similarity;
              vector<IdenticalInst> identicalInsts;
             
              bbl_info bk = KbasicBlockInfo[basicblockIDk];
              int sensitive = (bk->Sensitive_Info).size();
              if(!sensitive){
                  itk++;
                  continue;
              }

              bbl_info bf;
              SigMatchResult smr;
              float InstRaio = 0; 
              
              // 1.Compare basic block basicblockIDk in SScfgk with each node in SScfgf.
              for(set<int>::iterator itf = SScfgf.begin(); itf != SScfgf.end(); ){
                  content = content +  "Directly match SScfgk with SScfgf. "+ "\n";
                  basicblockIDf = *itf;
                  if(IsChecked(bk, basicblockIDf)){
                    itf++;
                    continue;
                  }
                 
                  bf = FbasicBlockInfo[basicblockIDf];
                  if(bf==NULL || bk==NULL){
                    itf++;
                    continue;
                  }
                   
                 
                  if(bk->MatchRecords.find(basicblockIDf) != bk->MatchRecords.end()){
                    itf++;
                    continue;
                  }
                 
                  smr = SigMatch(bk, bf,MCSMap);
                  Similarity = get<0>(smr); 
                  AddCMPItem(bk, basicblockIDf, Similarity, smr);
                  AddCMPItem(bf, basicblockIDk, Similarity, smr);
                  
                  content = content + get<4>(smr);
                  identicalInsts = get<1>(smr); 
                  InstRaio = get<3>(smr); 
                 
                  if((Similarity > Threshhod_process_1) && (InstRaio < InstCMPThreshhod) && (std::abs(int((bk->bbl)->size()-(bf->bbl)->size()))<DiffNum )){ 
                  
                      content = content + getIntContent(basicblockIDk) + " is matched  with " + getIntContent(basicblockIDf) +"\n";
                      
                      
                      map<llvm::Instruction*, int>  deletedSSlist = get<2>(smr); 
                      if(deletedSSlist.size()>0)
                              UpdatedeletedSSlist(&deletedSSlist, DeletedSSlists);
                      UpdateVetex(basicblockIDk,kcommon_subgraph,kcommon_node,remain_graph1,
                          basicblockIDf,fcommon_subgraph,fcommon_node,remain_graph2,MCSMap);
                      Matched = true;
                      MatchResult.insert(make_pair(basicblockIDk,basicblockIDf));
                      SScfgk.erase(itk++);
                      SScfgf.erase(itf++); 
                      OP<<"\nTest point\n";
                      goto CalDDSO;
                  }
                  else
                      itf++;
              }
              
              // 2. If there is no any node in SScfgf that can be matched with basicblockIDk, we furtherly match basicblockIDk with the nodes that are not in SScfgf and MCS
              if(!Matched){
                 
                  content = content +  "\nDirectly match SScfgk with remain vetexes in firmware. "+ "\n";
                  
                  PrintVectorI(*remain_graph2);
                  for(std::vector<int>::iterator iterr= remain_graph2->begin(); iterr!=remain_graph2->end(); iterr++){
                      basicblockIDf = *iterr;
                      if(IsChecked(bk, basicblockIDf) || (SScfgf.find(basicblockIDf) != SScfgf.end() ))
                        continue;
                      else{
                          bf = FbasicBlockInfo[basicblockIDf];
                          ContainCheck(bf);
                          #ifdef Debug_SO
                            OP<<"\033[32mbasicblockIDf (not in sscf) is : "<<basicblockIDf<<"\033[0m\n";
                          #endif
                          if(bf==NULL || bk==NULL) 
                            continue;
                          if(bk->MatchRecords.find(basicblockIDf) != bk->MatchRecords.end()) 
                            continue;
                          smr = SigMatch(bk, bf,MCSMap);
                          
                          Similarity = get<0>(smr); 
                          AddCMPItem(bk, basicblockIDf, Similarity, smr);
                          AddCMPItem(bf, basicblockIDk, Similarity, smr);
                          identicalInsts = get<1>(smr); 
                          content = content + get<4>(smr);
                          InstRaio = get<3>(smr); 
                          
                          
                  	  if((Similarity > Threshhod_process_1) && (InstRaio < InstCMPThreshhod) && (std::abs(int((bk->bbl)->size()-(bf->bbl)->size()))<DiffNum )){ //指令总数相差不多,说明是1对1) 
                              
                              content = content + getIntContent(basicblockIDk) + " is matched  with " + getIntContent(basicblockIDf) +"\n"; 
                              map<llvm::Instruction*, int> deletedSSlist = get<2>(smr); 
                              
                             
                              if(deletedSSlist.size()>0)
                                    UpdatedeletedSSlist(&deletedSSlist, DeletedSSlists);
                              UpdateVetex(basicblockIDk,kcommon_subgraph,kcommon_node,remain_graph1,
                                        basicblockIDf,fcommon_subgraph,fcommon_node,remain_graph2,MCSMap);
                              Matched = true;
                              MatchResult.insert(make_pair(basicblockIDk,basicblockIDf));
                              SScfgk.erase(itk++);
                              goto CalDDSO;
                              
                          }
                        }
                  }
              }

              if(!Matched)
                itk++;       
          }   
      } 
    


      // we perform multiple to one
      content = content +"\nBegin, "+  "\ncurrent SScfgk :  "+ DumpSet(SScfgk) + "current SScfgf :  "+ DumpSet(SScfgf) +"MCS is:\n"+DumpMCSMap(MCSMap);
      if(SScfgk.size() != 0){
       
        std::map<int, std::vector<int>> K1FN;
        std::map<int, std::vector<int>> F1KN;
        content = content + "Match multiple basic blocks to one basic block. SScfgk: " +DumpSet(SScfgk);
        
        NToOneResult Res = ObtainMatchCandidate(&SScfgk, &SScfgf, &KbasicBlockInfo,&FbasicBlockInfo,  MCSMap,
        kcommon_subgraph, kcommon_node, remain_graph1, 
        fcommon_subgraph, fcommon_node, remain_graph2, DeletedSSlists );
        
        content = content +"\nLo1, DeletedBBlist:\n" + DumpDeletedSSO(DeletedSSlists, &KbasicBlockInfo);
        std::map<int, std::vector<int>> MatchCandidates = get<0>(Res);
        content = content + get<1>(Res);
        std::vector<int> deletedSScfgk = get<2>(Res);
        if(deletedSScfgk.size()!=0){
            for(std::vector<int>::iterator iter=deletedSScfgk.begin(); iter!= deletedSScfgk.end();iter++ ){
              int basicblockIDk = *iter;
              bbl_info bk = ObtainBBInfo(basicblockIDk, &KbasicBlockInfo);
              content = content + "\n" +getIntContent(basicblockIDk) + " is deleted";
              UpdateDeletedBBlistN(basicblockIDk, remain_graph1, DeletedBBlist);
             
            }
        }  

        if(MatchCandidates.size()!=0){
          
          SplitResult split = SplitCandidates(&MatchCandidates);
          K1FN = get<0>(split);
          F1KN =  get<1>(split);
          std::vector<int> deletedSScfgk1 = get<2>(split);
          std::map<int, int> One2One = get<3>(split);
          
          content = content + "\nThe deleted sscfgk: "+ DumpVectorI(deletedSScfgk)+"\nK1FN: " + Dumpmap(K1FN) + +"\nF1KN: "+Dumpmap(F1KN);
          
          content = content +"\nLo2, DeletedBBlist:\n" + DumpDeletedSSO(DeletedSSlists, &KbasicBlockInfo);
          if(One2One.size()!=0){
            for(std::map<int,int>::iterator iter = One2One.begin(); iter!= One2One.end(); iter++){
              int basicblockIDk = iter->first;
              int basicblockIDf = iter->second;
              // if basicblockIDf is not in MCS
              if(findkeyByvalue(*MCSMap, basicblockIDf) == -1){
                bbl_info blk = ObtainBBInfo(basicblockIDk, &KbasicBlockInfo);
                // We obtain the deleted sensitive operations according to the match results between bblk and blf1
                std::map<int, pair<double, SigMatchResult>> MatchRecords = blk->MatchRecords;
                if(MatchRecords.find(basicblockIDf) != MatchRecords.end()){
                    UpdateVetex(basicblockIDk, kcommon_subgraph,kcommon_node,remain_graph1, &SScfgk,
                            basicblockIDf,fcommon_subgraph,fcommon_node,remain_graph2, &SScfgf,MCSMap);
                    SigMatchResult smr = (blk->MatchRecords[basicblockIDf]).second;
                    map<llvm::Instruction*, int>  deletedSSlist = get<2>(smr);  
                    if(deletedSSlist.size()>0) 
                      UpdatedeletedSSlist(&deletedSSlist, DeletedSSlists);
                }
              }
              else{
                    content = content + getIntContent(basicblockIDk) + " is deleted"+"\n" ;
                    UpdateDeletedBBlistN(basicblockIDk, remain_graph1, DeletedBBlist);
              }

            }
          }
          content = content +"\nLo3, DeletedBBlist:\n" + DumpDeletedSSO(DeletedSSlists, &KbasicBlockInfo);
        }
        
        content = content + "\nAfter One2One Mapping, MCSMap is:\n" + DumpMCSMap(MCSMap);


        content = content + "\nMatchF1KN: " + MatchF1KN(&F1KN, &KbasicBlockInfo, &FbasicBlockInfo, DeletedSSlists, remain_graph1, remain_graph2, 
        kcommon_subgraph ,kcommon_node, &SScfgk, fcommon_subgraph, fcommon_node,  &SScfgf ,DeletedBBlist, MCSMap);
        
        content = content + "\nMatchK1FN: "+ MatchK1FN(&K1FN, &KbasicBlockInfo, &FbasicBlockInfo, DeletedSSlists, remain_graph1, remain_graph2, 
        kcommon_subgraph, kcommon_node , &SScfgk, fcommon_subgraph, fcommon_node,  &SScfgf , DeletedBBlist, MCSMap);
      }
      content = content + "\nMCSMap:\n" + DumpMCSMap(MCSMap);

      content = content + "\nDeleted BB list:\n" + DumpVectorI(*DeletedBBlist);
      
     

        // Rank the similarity of nodes
      for(set<int>::iterator itk = SScfgk.begin(); itk != SScfgk.end(); ){
        //  basicblockIDk is unmatched
        bool Matched = false;
        int basicblockIDk = *itk;
        int basicblockIDf;
        double Similarity;
        SigMatchResult smr;
        float InstRaio = 0; 
        bbl_info bk = KbasicBlockInfo[basicblockIDk];
        
        if(!Matched){
          OP<<"Rank the similarity of nodes. \n";
          content = content +  "\nRank similarity."+ "\nMCS is:\n"+DumpMCSMap(MCSMap);
          content = content + "\ncurrent SScfgk :  "+ DumpSet(SScfgk) + "current SScfgf :  "+ DumpSet(SScfgf);
          // Ranking
          std::pair<int, std::pair<double, SigMatchResult>> Res = RankMatchResult(bk,MCSMap,FbasicBlockInfo);
          basicblockIDf = Res.first;
          bbl_info bf = FbasicBlockInfo[basicblockIDf];
          Similarity = Res.second.first;
          smr = Res.second.second;
          InstRaio = get<3>(smr); 
          if(!bk || !bf){
            itk++; 
            continue;
          }
          smr = SigMatch(bk, bf, MCSMap);
          double NewSimilarity = get<0>(smr);
          if((Similarity> Threshhod_process_2)){
            if(  InstRaio < InstCMPThreshhod_2){
              
              content = content + getIntContent(basicblockIDk) + " is matched  with " + getIntContent(basicblockIDf) +". Similarity is:"+ getDoubleContent(Similarity) +". NewSimilarity is:"+ getDoubleContent(NewSimilarity) + ". InstRaio is: "+ getDoubleContent(InstRaio)+"\n";  
              map<llvm::Instruction*, int> deletedSSlist = get<2>(smr); 
             
              if(deletedSSlist.size()>0)
                    UpdatedeletedSSlist(&deletedSSlist, DeletedSSlists);
              UpdateVetex(basicblockIDk,kcommon_subgraph,kcommon_node,remain_graph1,
                        basicblockIDf,fcommon_subgraph,fcommon_node,remain_graph2,MCSMap);
              Matched = true;
              MatchResult.insert(make_pair(basicblockIDk,basicblockIDf));
              SScfgk.erase(itk++);
              goto CalDDSO;
            }
          }
        }
        if(!Matched)
                itk++;   
      }
      

      // if we want to match BB with large difference
      if( (SScfgk.size() != 0) && (!finegrain)){
        //  Rank the similarity of nodes again
        content = content + "\nRank the similarity of nodes again\n";
       for(set<int>::iterator itk = SScfgk.begin(); itk != SScfgk.end(); ){
        
        bool Matched = false;
        int basicblockIDk = *itk;
        int basicblockIDf;
        double Similarity;
        SigMatchResult smr;
        float InstRaio = 0; 
        bbl_info bk = KbasicBlockInfo[basicblockIDk];
        
        if(!Matched){
          content = content +  "MCS is:"+ "\n";
          content = content + DumpMCSMap(MCSMap);
          content = content + "\ncurrent SScfgk :  "+ DumpSet(SScfgk) + "current SScfgf :  "+ DumpSet(SScfgf);
         
          std::pair<int, std::pair<double, SigMatchResult>> Res = RankMatchResult(bk,MCSMap,FbasicBlockInfo);
          basicblockIDf = Res.first;
          Similarity = Res.second.first;
          smr = Res.second.second;
          InstRaio = get<3>(smr); 
          
          content = content+ "\nbasicblockIDk is :  "+getIntContent(basicblockIDk) + ",  basicblockIDf is :  "+getIntContent(basicblockIDf) + " Similarity is:"+ getDoubleContent(Similarity);
          if((Similarity > Threshhod_process_4) && (SScfgf.find(basicblockIDf) != SScfgf.end())){    
              
              content = content + "\n"+getIntContent(basicblockIDk) + " is matched  with " + getIntContent(basicblockIDf) +". Similarity is:"+ getDoubleContent(Similarity)+ ". InstRaio is: "+ getDoubleContent(InstRaio)+"\n";  
              map<llvm::Instruction*, int> deletedSSlist = get<2>(smr); 
              if(deletedSSlist.size()>0)
                    UpdatedeletedSSlist(&deletedSSlist, DeletedSSlists);
              UpdateVetex(basicblockIDk,kcommon_subgraph,kcommon_node,remain_graph1,
                        basicblockIDf,fcommon_subgraph,fcommon_node,remain_graph2,MCSMap);
              
              std::vector<int>::iterator it=find(DeletedBBlist->begin(),DeletedBBlist->end(),basicblockIDk);
              if (it!=DeletedBBlist->end())
                DeletedBBlist->erase(it);
              Matched = true;
              MatchResult.insert(make_pair(basicblockIDk,basicblockIDf));
              SScfgk.erase(itk++);
              if(SScfgf.find(basicblockIDf) != SScfgf.end())
                SScfgf.erase(basicblockIDf);
              
          }
        }
        if(!Matched)
                itk++;   
        }
      }

      
      for(set<int>::iterator itk = SScfgk.begin(); itk != SScfgk.end(); itk++){
          int basicblockIDk = *itk;
          if(find(DeletedBBlist->begin(),DeletedBBlist->end(),basicblockIDk) == DeletedBBlist->end())
            DeletedBBlist->push_back(basicblockIDk);
      }

      content = content + ReConfirmDeletedBB(DeletedBBlist, DeletedSSlists,MCSMap, &FbasicBlockInfo,&KbasicBlockInfo,&SScfgk, &MatchResult);
     

      if(DeletedBBlist->size() > 0){
        for(std::vector<int>::iterator iter= DeletedBBlist->begin();
          iter != DeletedBBlist->end(); iter++ ){
            int DeletedBB = *iter;
            if(IsInMCS(MCSMap, DeletedBB))
              continue;
            bbl_info Deletedbbl =  ObtainBBInfo(DeletedBB, &KbasicBlockInfo);
            
            map<llvm::Instruction*, int>  deletedSSlist = Deletedbbl->Sensitive_Info;
            if(deletedSSlist.size()>0){
                UpdatedeletedSSlist(&deletedSSlist, DeletedSSlists);   
          }
        }
      }
    }
  

