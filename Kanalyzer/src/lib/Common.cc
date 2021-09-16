#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/InstIterator.h>
#include <fstream>
#include <regex>
#include "Common.h"
#include <algorithm>
#include <string>
#include <fstream>
#include <iostream>
#include <dirent.h>
#include <string.h>
#include <stdlib.h>
#include <vector>
#include <bits/stdc++.h> 
#include <sys/types.h>
#include <sys/stat.h>
using namespace std;


#define LINUX_SOURCE "/your-path-of-the-linux-source/linux-5.3.0"

bool IsPathExist(const std::string &s)
{
  struct stat buffer;
  return (stat (s.c_str(), &buffer) == 0);
}

bool trimPathSlash(string &path, int slash) {
	while (slash > 0) {
		path = path.substr(path.find('/') + 1);
		--slash;
	}

	return true;
}

string getFileName(DILocation *Loc, DISubprogram *SP) {
	string FN;
	if (Loc)
		FN = Loc->getFilename().str();
	else if (SP)
		FN = SP->getFilename().str();
	else
		return "";

	// TODO: require config
	int slashToTrim = 2;
	trimPathSlash(FN, slashToTrim);
	FN = string(LINUX_SOURCE) + "/" + FN;
	return FN;
}

void Replace(std::string& str, const std::string& from, const std::string& to) {
    size_t start_pos = 0;
    while((start_pos = str.find(from, start_pos)) != std::string::npos) {
        str.replace(start_pos, from.length(), to);
        start_pos += to.length(); // In case 'to' contains 'from', like replacing 'x' with 'yx'
    }
}

std::string getValueContent(Value *V){
	std::string Str;
	raw_string_ostream OS(Str);
	V->print(OS);
	if(Str.find("\"")!=string::npos)
		Replace(Str, "\"", "\\\"");

	if(Str.find("define") != string::npos)
		return "Function definition";
	else if(Str.find("declare")!= string::npos)
		return "declare";
		
	else
		return OS.str();
}

std::string getInstContent(Instruction *I){
	if(!I)
		return "";
	if(isa<SwitchInst>(I))
		return "SwitchInst";
	else{
		//OP<<"\nInst is:"<<*I;
		string Str("");
        raw_string_ostream rso(Str);

		// std::string Str;
		// raw_string_ostream OS(Str);
		rso<<*I; 
		if(Str.find("\"")!=string::npos)
			Replace(Str, "\"", "\\\"");
		//I->llvm::Value::print(OS);
		
		if(Str.find("asm")!=string::npos)
			return "asm";
		
		else
			return rso.str();
	}
}


std::string getvectorContent(std::vector<int> v){
	std::string content;
	for(vector<int>::iterator iter= v.begin(); iter != v.end(); iter++){
		content = content + getIntContent(*iter)+" ";
	}
	return content;
}



std::string getvectorContent(std::vector<string> v){
	std::string content;
	for(vector<string>::iterator iter= v.begin(); iter != v.end(); iter++){
		content = content + *iter+"\n";
	}
	return content;
}

std::string getBoolContent(bool b){
	if(b)
		return "Y";
	else
		return "N";
}

std::string getIntContent(int i){
	return std::to_string(i);
}

std::string getDoubleContent(double i){
	return std::to_string(i);
}

std::string getMatrixContent(double **a,int m, int n){
	string content_mat = "";
	for(int i=0; i<m; i++){
        for (int j=0; j<n; j++){
            content_mat = content_mat + getDoubleContent(a[i][j])+ "  ";     
        }
		 content_mat = content_mat+ "\n ";
    }   
	return  content_mat;
}

/// Check if the value is a constant.
bool isConstant(Value *V) {
  // Invalid input.
  if (!V) 
    return false;

  // The value is a constant.
  Constant *Ct = dyn_cast<Constant>(V);
  if (Ct) 
    return true;

  return false;
}

/// Get the source code line
string getSourceLine(string fn_str, unsigned lineno) {
	std::ifstream sourcefile(fn_str);
	string line;
	sourcefile.seekg(ios::beg);
	
	for(int n = 0; n < lineno - 1; ++n){
		sourcefile.ignore(std::numeric_limits<streamsize>::max(), '\n');
	}
	getline(sourcefile, line);

	return line;
}

string getSourceFuncName(Instruction *I) {

	DILocation *Loc = getSourceLocation(I);
	if (!Loc)
		return "";
	unsigned lineno = Loc->getLine();
	std::string fn_str = getFileName(Loc);
	string line = getSourceLine(fn_str, lineno);
	
	while(line[0] == ' ' || line[0] == '\t')
		line.erase(line.begin());
	line = line.substr(0, line.find('('));
	return line;
}

string extractMacro(string line, Instruction *I) {
	string macro, word, FnName;
	std::regex caps("[^\\(][_A-Z][_A-Z0-9]+[\\);,]+");
	smatch match;
	
	// detect function macros
	if (CallInst *CI = dyn_cast<CallInst>(I)) {
		FnName = getCalledFuncName(CI);
		caps = "[_A-Z][_A-Z0-9]{2,}";
		std::regex keywords("(\\s*)(for|if|while)(\\s*)(\\()");

		if (regex_search(line, match, keywords))
		  line = line.substr(match[0].length());
		
		if (line.find(FnName) != std::string::npos) {
			if (regex_search(FnName, match, caps))
				return FnName;

		} else {
			//identify non matching functions as macros
			//std::count(line.begin(), line.end(), '"') > 0
			std::size_t eq_pos = line.find_last_of("=");
			if (eq_pos == std::string::npos)
				eq_pos = 0;
			else
				++eq_pos;

			std::size_t paren = line.find('(', eq_pos);
			return line.substr(eq_pos, paren-eq_pos);
		}

	} else {
		// detect macro constant variables
		std::size_t lhs = -1;
		stringstream iss(line.substr(lhs+1));

		while (iss >> word) {
			if (regex_search(word, match, caps)) {
				macro = word;
				return macro;
			}
		}
	}

	return "";
}

/// Get called function name of V.
StringRef getCalledFuncName(Instruction *I) {

  Value *V;
	if (CallInst *CI = dyn_cast<CallInst>(I))
		V = CI->getCalledValue();
	else if (InvokeInst *II = dyn_cast<InvokeInst>(I))
		V = II->getCalledValue();
	assert(V);

  InlineAsm *IA = dyn_cast<InlineAsm>(V);
  if (IA)
    return StringRef(IA->getAsmString());

  User *UV = dyn_cast<User>(V);
  if (UV) {
    if (UV->getNumOperands() > 0) {
			Value *VUV = UV->getOperand(0);
			return VUV->getName();
		}
  }

	return V->getName();
}

DILocation *getSourceLocation(Instruction *I) {
  if (!I)
	  return NULL;


  MDNode *N = I->getMetadata("dbg");
  if (!N)
  {
	//printf("n ");
    return NULL;
  }

  DILocation *Loc = dyn_cast<DILocation>(N);
  if (!Loc || Loc->getLine() < 1)
  {
	  //printf("l ");
	  return NULL;
  }

	return Loc;
}


int GetLocation(Value *V){
	Instruction *I = dyn_cast<Instruction>(V);
	if (!I)
		return -1;
	DILocation *Loc = getSourceLocation(I);
	if (!Loc)
		return -1;
	unsigned LineNo = Loc->getLine();
	return LineNo;
}

int GetLocation(Instruction *I){
	if (!I)
		return -1;
	DILocation *Loc = getSourceLocation(I);
	if (!Loc)
		return -1;
	unsigned LineNo = Loc->getLine();
	return LineNo;
}


/// Print out source code information to facilitate manual analyses.
void printSourceCodeInfo(Value *V) {
	Instruction *I = dyn_cast<Instruction>(V);
	if (!I)
		return;

	DILocation *Loc = getSourceLocation(I);
	if (!Loc)
	{
		//printf(". ");
		return;
	}
	unsigned LineNo = Loc->getLine();
	std::string FN = getFileName(Loc);
	string line = getSourceLine(FN, LineNo);
	FN = Loc->getFilename().str();
	FN = FN.substr(FN.find('/') + 1);
	FN = FN.substr(FN.find('/') + 1);

	while(line[0] == ' ' || line[0] == '\t')
		line.erase(line.begin());
	OP << " ["
		<< "\033[34m" << "Code" << "\033[0m" << "] "
		<< FN
		<< " +" << LineNo << ": "
		<< "\033[35m" << line << "\033[0m" <<'\n';
}

void printSourceCodeInfoInst(Instruction *I) {
	if (!I)
		return;

	DILocation *Loc = getSourceLocation(I);
	if (!Loc)
	{
		//printf(". ");
		return;
	}
	unsigned LineNo = Loc->getLine();
	std::string FN = getFileName(Loc);
	string line = getSourceLine(FN, LineNo);
	FN = Loc->getFilename().str();
	FN = FN.substr(FN.find('/') + 1);
	FN = FN.substr(FN.find('/') + 1);

	while(line[0] == ' ' || line[0] == '\t')
		line.erase(line.begin());
	OP << " ["
		<< "\033[34m" << "Code" << "\033[0m" << "] "
		<< FN
		<< " +" << LineNo << ": "
		<< "\033[35m" << line << "\033[0m" <<'\n';
}

string ObtainSourceCodeInfoInst(Instruction *I) {
	string LineInfo ="";
	if (!I)
		return LineInfo;

	DILocation *Loc = getSourceLocation(I);
	if (!Loc)
	{
		//printf(". ");
		return LineInfo;
	}
	unsigned LineNo = Loc->getLine();
	std::string FN = getFileName(Loc);
	string line = getSourceLine(FN, LineNo);
	FN = Loc->getFilename().str();
	
	FN = FN.substr(FN.find('/') + 1);
	FN = FN.substr(FN.find('/') + 1);

	while(line[0] == ' ' || line[0] == '\t')
		line.erase(line.begin());
	OP << " ["
		<< "\033[34m" << "Code" << "\033[0m" << "] "
		<< FN
		<< " +" << LineNo << ": "
		<< "\033[35m" << line << "\033[0m" <<'\n';
	
	LineInfo = "[Code]"+ FN+ " +" + getIntContent(LineNo) + ": "+ line;
	return LineInfo;
}

void printSourceCodeInfo(Function *F) {

	DISubprogram *SP = F->getSubprogram();

	if (SP) {
		string FN = getFileName(NULL, SP);
		string line = getSourceLine(FN, SP->getLine());
		while(line[0] == ' ' || line[0] == '\t')
			line.erase(line.begin());

		FN = SP->getFilename().str();
		FN = FN.substr(FN.find('/') + 1);
		FN = FN.substr(FN.find('/') + 1);

		OP << " ["
			<< "\033[34m" << "Code" << "\033[0m" << "] "
			<< FN
			<< " +" << SP->getLine() << ": "
			<< "\033[35m" << line << "\033[0m" <<'\n';
	}
}

string getMacroInfo(Value *V) {

	Instruction *I = dyn_cast<Instruction>(V);
	if (!I) return "";

	DILocation *Loc = getSourceLocation(I);
	if (!Loc) return "";

	unsigned LineNo = Loc->getLine();
	std::string FN = getFileName(Loc);
	string line = getSourceLine(FN, LineNo);
	FN = Loc->getFilename().str();
	const char *filename = FN.c_str();
	filename = strchr(filename, '/') + 1;
	filename = strchr(filename, '/') + 1;
	int idx = filename - FN.c_str();

	while(line[0] == ' ' || line[0] == '\t')
		line.erase(line.begin());

	string macro = extractMacro(line, I);

	//clean up the ending and whitespaces
	macro.erase(std::remove (macro.begin(), macro.end(),' '), macro.end());
	unsigned length = 0;
	for (auto it = macro.begin(), e = macro.end(); it != e; ++it)
		if (*it == ')' || *it == ';' || *it == ',') {
			macro = macro.substr(0, length);
			break;
		} else {
			++length;
		}

	return macro;
}

/// Get source code information of this value
void getSourceCodeInfo(Value *V, string &file,
                               unsigned &line) {
  file = "";
  line = 0;

  auto I = dyn_cast<Instruction>(V);
  if (!I)
    return;

  MDNode *N = I->getMetadata("dbg");
  if (!N)
    return;

  DILocation *Loc = dyn_cast<DILocation>(N);
  if (!Loc || Loc->getLine() < 1)
    return;

  file = Loc->getFilename().str();
  line = Loc->getLine();
}

Argument *getArgByNo(Function *F, int8_t ArgNo) {

  if (ArgNo >= F->arg_size())
    return NULL;

  int8_t idx = 0;
  Function::arg_iterator ai = F->arg_begin();
  while (idx != ArgNo) {
    ++ai;
    ++idx;
  }
  return ai;
}

//#define HASH_SOURCE_INFO
size_t funcHash(Function *F, bool withName) {

	hash<string> str_hash;
	string output;

#ifdef HASH_SOURCE_INFO
	DISubprogram *SP = F->getSubprogram();

	if (SP) {
		output = SP->getFilename();
		output = output + to_string(uint_hash(SP->getLine()));
	}
	else {
#endif
		string sig;
		raw_string_ostream rso(sig);
		Type *FTy = F->getFunctionType();
		FTy->print(rso);
		output = rso.str();

		if (withName)
			output += F->getName();
#ifdef HASH_SOURCE_INFO
	}
#endif
	string::iterator end_pos = remove(output.begin(), 
			output.end(), ' ');
	output.erase(end_pos, output.end());

	return str_hash(output);
}

size_t callHash(CallInst *CI) {

	CallSite CS(CI);
	Function *CF = CI->getCalledFunction();

	if (CF)
		return funcHash(CF);
	else {
		hash<string> str_hash;
		string sig;
		raw_string_ostream rso(sig);
		Type *FTy = CS.getFunctionType();
		FTy->print(rso);

		string strip_str = rso.str();
		string::iterator end_pos = remove(strip_str.begin(), 
				strip_str.end(), ' ');
		strip_str.erase(end_pos, strip_str.end());
		return str_hash(strip_str);
	}
}

size_t typeHash(Type *Ty) {
	hash<string> str_hash;
	string sig;

	raw_string_ostream rso(sig);
	Ty->print(rso);
	string ty_str = rso.str();
	string::iterator end_pos = remove(ty_str.begin(), ty_str.end(), ' ');
	ty_str.erase(end_pos, ty_str.end());

	return str_hash(ty_str);
}

size_t hashIdxHash(size_t Hs, int Idx) {
	hash<string> str_hash;
	return Hs + str_hash(to_string(Idx));
}

size_t typeIdxHash(Type *Ty, int Idx) {
	return hashIdxHash(typeHash(Ty), Idx);
}

void getSourceCodeLine(Value *V, string &line) {

	line = "";
	Instruction *I = dyn_cast<Instruction>(V);
	if (!I)
		return;

	DILocation *Loc = getSourceLocation(I);
	if (!Loc)
		return;

	unsigned LineNo = Loc->getLine();
	std::string FN = getFileName(Loc);
	line = getSourceLine(FN, LineNo);
	FN = Loc->getFilename().str();
	FN = FN.substr(FN.find('/') + 1);
	FN = FN.substr(FN.find('/') + 1);

	while(line[0] == ' ' || line[0] == '\t')
		line.erase(line.begin());

	return;
}

int min(int x, int y, int z) 
{ 
    return min(min(x, y), z); 
} 

// Find minimum number of edits (operations) required to convert ‘str1’ into ‘str2’.
int editDistDP(string str1, string str2, int m, int n) 
{ 
    // Create a table to store results of subproblems 
    int dp[m + 1][n + 1]; 
  
    // Fill d[][] in bottom up manner 
    for (int i = 0; i <= m; i++) { 
        for (int j = 0; j <= n; j++) { 
            // If first string is empty, only option is to 
            // insert all characters of second string 
            if (i == 0) 
                dp[i][j] = j; // Min. operations = j 
  
            // If second string is empty, only option is to 
            // remove all characters of second string 
            else if (j == 0) 
                dp[i][j] = i; // Min. operations = i 
  
            // If last characters are same, ignore last char 
            // and recur for remaining string 
            else if (str1[i - 1] == str2[j - 1]) 
                dp[i][j] = dp[i - 1][j - 1]; 
  
            // If the last character is different, consider all 
            // possibilities and find the minimum 
            else
                dp[i][j] = 1 + min(dp[i][j - 1], // Insert 
                                   dp[i - 1][j], // Remove 
                                   dp[i - 1][j - 1]); // Replace 
        } 
	} 
    return dp[m][n];
} 
double mindistance(double a,double b,double c)  
{  
    double tmp=a<b?a:b;  
    return tmp<c?tmp:c;  
}  
// Find minimum number of edits (operations) required to convert longerSeq into shorterSeq.
double editInstDistDPInst(vector<string> longerSeq, vector<string> shorterSeq) 
{ 
    // Create a table to store results of subproblems 
	int m = longerSeq.size();
	int n = shorterSeq.size();
	double remove_cost = 0 ;
    double dp[m + 1][n + 1]; 
	double colValue = 0;
	double rowValue = 0;
	if(shorterSeq.size()<4) 
		remove_cost = 2.0/longerSeq.size();
	else
		remove_cost = 1.0/longerSeq.size();
	std::cout<<"remove_cost : "<<remove_cost<<"\n";
    // Fill d[][] in bottom up manner 
    for (int i = 0; i <= m; i++) { 
        for (int j = 0; j <= n; j++) { 
            // If first string is empty, only option is to 
            // insert all characters of second string 
            if (i == 0) {
				colValue = 2*remove_cost*j;
                dp[i][j] = colValue; // Min. operations = j 
			}
  
            // If second string is empty, only option is to 
            // remove all characters of second string 
            else if (j == 0){
				rowValue = 2*remove_cost*i;
                dp[i][j] = rowValue; // Min. operations = i 
			}
            // If last characters are same, ignore last char 
            // and recur for remaining string 
            else if (longerSeq[i - 1] == shorterSeq[j - 1]) 
                dp[i][j] = dp[i - 1][j - 1]; 
  
            // If the last character is different, consider all 
            // possibilities and find the minimum 
            else
                dp[i][j] = mindistance(dp[i][j - 1]+1, // Insert 
                                   dp[i - 1][j]+remove_cost, // Remove 
                                   dp[i - 1][j - 1]+1); // Replace 
        } 
	} 
	// for (int i = 0; i <= m; i++) { 
    //     for (int j = 0; j <= n; j++) { 
	// 		std::cout<<dp[i][j]<<"  ";
	// 	}
	// 	std::cout<<"\n";
	// }
    return dp[m][n];
} 


double editInstDistDPInst2(vector<string> longerSeq, vector<string> shorterSeq) 
{ 
    // Create a table to store results of subproblems 
	double remove_cost = 1.0/longerSeq.size();
    std::vector<string> intersec, different;
	std::set_intersection(longerSeq.begin(), longerSeq.end(),
        shorterSeq.begin(), shorterSeq.end(),
        std::back_inserter(intersec));
	std::set_difference(longerSeq.begin(), longerSeq.end(),
        shorterSeq.begin(), shorterSeq.end(),
        std::back_inserter(different));
	cout<<"remove cost: "<<remove_cost<<" different size "<<different.size();
	return different.size()*remove_cost;
} 

double editInstDistDPInst1(vector<string> longerSeq, vector<string> shorterSeq) 
{ 
    // Create a table to store results of subproblems 
	int m = longerSeq.size();
	int n = shorterSeq.size();
	double remove_cost = 0 ;
    double dp[m + 1][n + 1]; 
	remove_cost = 1.0/longerSeq.size();
	std::cout<<"remove_cost : "<<remove_cost<<"\n";
    // Fill d[][] in bottom up manner 
    for (int i = 0; i <= m; i++) { 
        for (int j = 0; j <= n; j++) { 
            // If first string is empty, only option is to 
            // insert all characters of second string 
            if (i == 0) 
                dp[i][j] = j; // Min. operations = j 
  
            // If second string is empty, only option is to 
            // remove all characters of second string 
            else if (j == 0) 
                dp[i][j] = i; // Min. operations = i 
  
            // If last characters are same, ignore last char 
            // and recur for remaining string 
            else if (longerSeq[i - 1] == shorterSeq[j - 1]) 
                dp[i][j] = dp[i - 1][j - 1]; 
  
            // If the last character is different, consider all 
            // possibilities and find the minimum 
            else
                dp[i][j] = mindistance(dp[i][j - 1]+1, // Insert 
                                   dp[i - 1][j]+remove_cost, // Remove 
                                   dp[i - 1][j - 1]+1); // Replace 
        } 
	} 
	// for (int i = 0; i <= m; i++) { 
    //     for (int j = 0; j <= n; j++) { 
	// 		std::cout<<dp[i][j]<<"  ";
	// 	}
	// 	std::cout<<"\n";
	// }
    return dp[m][n];
} 


std::pair<double, int> mindistanceNew(double a,double b,double c)  
{  
    int position;
    double tmp=a<b?a:b; 
    tmp = tmp<c?tmp:c;

    if(tmp == a)
        position = 0;
    else if(tmp == b)
        position = 1;
    else
        position = 2;
    return make_pair(tmp, position);  

}  

// turn the longerSeq to the shorterSeq.
double editInstDistDPInstNew(vector<string> longerSeq, vector<string> shorterSeq) 
{ 
    // Create a table to store results of subproblems 
	int m = longerSeq.size();
	int n = shorterSeq.size();
    int count = 0;
	double remove_cost = 0 ;
    double dp[m + 1][n + 1]; 
    double dp_1[m + 1][n + 1]; 
	double colValue = 0;
	double rowValue = 0;
	if(shorterSeq.size()<4) 
		remove_cost = min(2.0/longerSeq.size(),1.0);
	else
		remove_cost = 1.0/longerSeq.size();
	// std::cout<<"remove_cost : "<<remove_cost<<"\n";
    // Fill d[][] in bottom up manner 
    for (int i = 0; i <= m; i++) { 
        for (int j = 0; j <= n; j++) { 
            // If first string is empty, only option is to 
            // insert all characters of second string 
            if (i == 0) {
				colValue = 2*remove_cost*j;
                dp[i][j] = j; // Min. operations = j 
                // dp_1[i][j] = colValue; 
                dp_1[i][j] = j;
			}
  
            // If second string is empty, only option is to 
            // remove all characters of second string 
            else if (j == 0){
				rowValue = 2*remove_cost*i;
                dp[i][j] = i; // Min. operations = i 
                //dp_1[i][j] = rowValue;
                //dp_1[i][j] = i;
				// dp_1[i][j] = rowValue;
				dp_1[i][j] = min(rowValue,1.0);
			}
            // If last characters are same, ignore last char 
            // and recur for remaining string 
            else if (longerSeq[i - 1] == shorterSeq[j - 1]) {
                dp[i][j] = dp[i - 1][j - 1]; 
                dp_1[i][j] = dp_1[i - 1][j - 1];
            }
            // If the last character is different, consider all 
            // possibilities and find the minimum 
            else{
                pair<double, int> res = mindistanceNew(dp[i][j - 1], // Insert 
                                        dp[i - 1][j], // Remove 
                                        dp[i - 1][j - 1]); // Replace
                dp[i][j] = 1 + res.first;
                if(res.second==0)
                    dp_1[i][j] = dp_1[i][j - 1] + 1;
                else if(res.second==1)
                    dp_1[i][j] = dp_1[i - 1][j] + remove_cost;
                else
                    dp_1[i][j] = dp_1[i - 1][j - 1] + 1;
            } 
        } 
	} 
    // cout<<"count: "<<count<<"\n";
    
	// for (int i = 0; i <= m; i++) { 
    //     for (int j = 0; j <= n; j++) { 
	// 		std::cout<<dp[i][j]<<"  ";
	// 	}
	// 	std::cout<<"\n";
	// }
    // std::cout<<"\n";
    // for (int i = 0; i <= m; i++) { 
    //     for (int j = 0; j <= n; j++) { 
	// 		std::cout<<dp_1[i][j]<<"  ";
	// 	}
	// 	std::cout<<"\n";
	// }

    //return dp[m][n]-(1-remove_cost)*count;
    return dp_1[m][n];
} 


int StrminDistance(string word1, string word2) {
        int m = word1.length();
        int n = word2.length();
        
        vector<vector<int>> cost(m+1, vector<int>(n+1));
        
        for (int i = 0; i <= m; ++i) {
            cost[i][0] = i;
        }
        for (int j = 0; j <= n; ++j) {
            cost[0][j] = j;
        }
        for (int i = 1; i <= m; ++i) {
            for (int j = 1; j <= n; ++j) {
                if (word1[i-1] == word2[j-1]) {
                    cost[i][j] = cost[i-1][j-1];
                } else {
                    cost[i][j] = 1 + min(cost[i-1][j-1], min(cost[i][j-1], cost[i-1][j]));
                }             
            }
        }
        return cost[m][n];
    }
