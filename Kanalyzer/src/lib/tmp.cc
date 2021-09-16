// Find same-origin variables from the given variable
void PairAnalysisPass::findSameVariablesFrom(Function *F,
        CriticalVar &criticalvar,
        std::set<Value *>pathvalueset) {

 //Value* VSource = V;
 std::set<Value *> PV; //Global value set to avoid loop
 std::list<Value *> EV; //BFS record list

 PV.clear();
 EV.clear();
 EV.push_back(criticalvar.inst);

    /* if(getValueName(criticalvar.inst)=="%215"){
        OP << "pathvalueset\n";
        for(auto i = pathvalueset.begin(); i != pathvalueset.end();i++){
            OP << "Value: "<<getValueName(*i)<<"\n";
        }
        OP << "\n";
    } */

 while (!EV.empty()) {

  Value *TV = EV.front(); //Current checking value
  EV.pop_front();

  if (PV.find(TV) != PV.end())
   continue;
  PV.insert(TV);

        //This inst does not appear in current path
        //Then stop loop and collect current value
        if(0 == pathvalueset.count(TV)){
            criticalvar.sourceset.insert(TV);
            continue;
        }
    
        Instruction *I = dyn_cast<Instruction>(TV);
        if(!I)
            continue;

        ///////////////////////////////////////////////
        // The value (%TV) is a load: %TV = load i32, i32* %LPO
        ///////////////////////////////////////////////
        LoadInst* LI = dyn_cast<LoadInst>(TV);
        if(LI){
            //Get value %LPO
            //OP << "Inst: "<< *V <<"\n";
            //OP << "The value is a load\n";
            Value *LPO = LI->getPointerOperand();

            //OP << "load: "<<*LPO<<"\n";

            EV.push_back(LPO);
            continue;
        }

        ///////////////////////////////////////////////
        // The value is a store instruction. store i32 vop, i32* pop
        ///////////////////////////////////////////////
        StoreInst *STI = dyn_cast<StoreInst>(TV);
        if(STI){
            //OP << "Inst: "<< *V <<"\n";
            //OP << "The value is a store\n";
            Value* vop = STI->getValueOperand();
            //OP << "Stored var: "<<getValueName(op)<<"\n";
            Value* pop = STI->getPointerOperand();
            //OP << "pop: "<<getValueName(pop)<<"\n";

            EV.push_back(pop);
            continue;
        }

        ///////////////////////////////////////////////
        // The value is a getelementptr instruction.
        ///////////////////////////////////////////////
  GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(TV);
        if(GEP){
            //OP << "Inst: "<< *TV <<"\n";
            //OP << "The value is a getelementptr\n";

            //The struct ptr
            Value *PO = GEP->getPointerOperand();
            //OP << "PO: "<<*PO<<"\n";
            auto numindices = GEP->getNumIndices();
            //OP << "numindices: "<<numindices<<"\n";

            vector<Value*> GEPInfo;
            GEPInfo.clear();

            for(int i = 0;i<numindices;i++){
                Value* indice = GEP->getOperand(i+1);
                //OP << "indice: "<<*indice<< "\n";
                GEPInfo.push_back(indice);
                //Constant *k = dyn_cast<Constant>(indice);
                //int indice_test = k->getUniqueInteger();
        
            }
            pair<Value*, vector<Value*>> value(TV,GEPInfo);
            criticalvar.getelementptrInfo.insert(value);

            EV.push_back(PO);
            continue;
        }

        ///////////////////////////////////////////////
        // The value is a call instruction.
        // Function could be a void func (no return or assign) 
        ///////////////////////////////////////////////
  CallInst *CAI = dyn_cast<CallInst>(TV);
  if(CAI){
            //OP << "Inst: "<< *V <<"\n";
            //OP << "The value is a call instruction\n";
            Function *CF = CAI->getCalledFunction();
   if (!CF) 
    continue;

            StringRef FName = getCalledFuncName(CAI);

            //Ignore llvm debug funcs
            if(1 == Ctx->DebugFuncs.count(FName)){
                //OP << "Found a debug funcs: "<<FName<<"\n";
                continue;
            }

            unsigned argnum = CAI->getNumArgOperands();
            for(unsigned j=0;j<argnum;j++){
                Value* arg = CAI->getArgOperand(j);
                if(isConstant(arg)){
                    continue;
                }
                        
                EV.push_back(arg);
            }

            //Consider the function
            criticalvar.sourcefuncs.insert(CF);
            
            continue;
        }
        
        ///////////////////////////////////////////////
        // The value is a return instruction.
        ///////////////////////////////////////////////
        ReturnInst *RI = dyn_cast<ReturnInst>(TV);
        if(RI){
            //OP << "Inst: "<< *V <<"\n";
            //OP << "The value is a return\n";

            continue;
        }

        ///////////////////////////////////////////////
        // The value is a branch instruction. (br)
        ///////////////////////////////////////////////
        BranchInst *BI = dyn_cast<BranchInst>(TV);
        if(BI){
            //OP << "Inst: "<< *V <<"\n";
            //OP << "The value is a branch\n";
            if (BI->getNumSuccessors() < 2)
    continue;

            auto CD = BI->getCondition(); //test can be icmp
            //OP << "test: "<<getValueName(test)<<"\n";

            EV.push_back(CD);
            continue;
        }

        ///////////////////////////////////////////////
        // The value is a switch instruction.
        ///////////////////////////////////////////////
        SwitchInst *SWI = dyn_cast<SwitchInst>(TV);
        if(SWI){
            //OP << "Inst: "<< *V <<"\n";
            //OP << "The value is a switch\n";
            if (SWI->getNumSuccessors() < 2)
     continue;

            auto CD = SWI->getCondition();
            // /OP << "test: "<<getValueName(test);

            EV.push_back(CD);

            continue;
        }

        ///////////////////////////////////////////////
        // The value is a icmp instruction.
        ///////////////////////////////////////////////
  ICmpInst *ICI = dyn_cast<ICmpInst>(TV);
  if (ICI){
            //OP << "Inst: "<< *TV <<"\n";
            //OP << "The value is a icmp\n";
            
            //null is also a const
            auto oprand0 = I->getOperand(0);
            //OP << "op0: "<<*oprand0<<"\n";
            //OP << "Isconst op0: "<<isConstant(oprand0)<<"\n";
            auto oprand1 = I->getOperand(1);
            //OP << "op1: "<<*oprand1<<"\n";
            //OP << "Isconst op1: "<<isConstant(oprand1)<<"\n";

            if(isConstant(oprand0) && !isConstant(oprand1)){
                EV.push_back(oprand1);
            }
            else if(isConstant(oprand1) && !isConstant(oprand0)){
                EV.push_back(oprand0);
            }
            
   continue;
        }

        /*------------------------Just pick the pre value (begin)------------------------*/
        ///////////////////////////////////////////////
        // The value is a bitcast instruction.
        ///////////////////////////////////////////////
        BitCastInst *BCI = dyn_cast<BitCastInst>(TV);
        if(BCI){
            //OP << "Inst: "<< *V <<"\n";
            //OP << "The value is a bitcast\n";

            //Get the operated var as the source
            //Only have op0
            Value *op = BCI->getOperand(0);

            EV.push_back(op);
   continue;
        }

        ///////////////////////////////////////////////
        // The value is a trunc instruction.
        ///////////////////////////////////////////////
        TruncInst *TCI = dyn_cast<TruncInst>(TV);
        if(TCI){
            //OP << "Inst: "<< *V <<"\n";
            //OP << "The value is a trunc\n";

            //Get the operated var as the source
            //Only have op0
            Value *op = TCI->getOperand(0);

            EV.push_back(op);
   continue;
        }

        ///////////////////////////////////////////////
        // The value is a sext instruction.
        ///////////////////////////////////////////////
  SExtInst *SEI = dyn_cast<SExtInst>(TV);
  if (SEI){
            //OP << "Inst: "<< *V <<"\n";
            //OP << "---The value is a sext\n";

            //Get the operated var as the source
            //Only have op0
            Value *op = SEI->getOperand(0);
            //OP << "op: "<< getValueName(op)<<"\n";

            EV.push_back(op);
   continue;
        }

        ///////////////////////////////////////////////
        // The value is a zext instruction.
        ///////////////////////////////////////////////
  ZExtInst *ZEI = dyn_cast<ZExtInst>(TV);
  if (ZEI){
            //OP << "Inst: "<< *V <<"\n";
            //OP << "---The value is a zsext\n";

            //Get the operated var as the source
            //Only have op0
            Value *op = ZEI->getOperand(0);
            //OP << "op: "<< getValueName(op)<<"\n";

            EV.push_back(op);
   continue;
        }

        ///////////////////////////////////////////////
        // The value is a inttoptr instruction.
        ///////////////////////////////////////////////
  IntToPtrInst *ITPI = dyn_cast<IntToPtrInst>(TV);
  if (ITPI){
            //OP << "Inst: "<< *V <<"\n";
            //OP << "---The value is a inttoptr\n";

            //Get the operated var as the source
            //Only have op0
            Value *op = ITPI->getOperand(0);
            //auto ops = ZEI->getOpcodeName();
            //OP << "op: "<< getValueName(op)<<"\n";
            //OP << "OPcode: "<< ops<<"\n";

            EV.push_back(op);
   continue;
        }

        ///////////////////////////////////////////////
        // The value is a ptrtoint instruction.
        ///////////////////////////////////////////////
  PtrToIntInst *PTI = dyn_cast<PtrToIntInst>(TV);
  if (PTI){
            //OP << "Inst: "<< *V <<"\n";
            //OP << "---The value is a ptrtoint\n";

            //Get the operated var as the source
            //Only have op0
            Value *op = PTI->getOperand(0);
            //auto ops = ZEI->getOpcodeName();
            //OP << "op: "<< getValueName(op)<<"\n";
            //OP << "OPcode: "<< ops<<"\n";

            EV.push_back(op);
   continue;
        }

        ///////////////////////////////////////////////
        // The value is a extractvalue instruction.
        ///////////////////////////////////////////////
  ExtractValueInst  *EVI = dyn_cast<ExtractValueInst>(TV);
  if (EVI){
            //OP << "Inst: "<< *TV <<"\n";
            //OP << "---The value is a extractvalue\n";

            //Get the operated var as the source
            //Only have op0
            Value *op = EVI->getOperand(0);
            //auto ops = ZEI->getOpcodeName();
            //OP << "op: "<< getValueName(op)<<"\n";
            //OP << "OPcode: "<< ops<<"\n";

            EV.push_back(op);
   continue;
        }

        ///////////////////////////////////////////////
        // The value is a extractelement instruction.
        ///////////////////////////////////////////////
        ExtractElementInst *EEI = dyn_cast<ExtractElementInst>(TV);
        if(EEI){
            //OP << "Inst: "<< *TV <<"\n";
            //OP << "---The value is a extractelement\n";

            //Get the operated var as the source
            //Only have op0
            Value *op = EEI->getOperand(0);
            //auto ops = ZEI->getOpcodeName();
            //OP << "op: "<< getValueName(op)<<"\n";
            //OP << "OPcode: "<< ops<<"\n";

            EV.push_back(op);
   continue;
        }
        /*------------------------Just pick the pre value (end)------------------------*/



        /*------------------------Multiple sources inst (begin)------------------------*/
        ///////////////////////////////////////////////
        // The value is a phinode. 
        // %40 = phi i8* [ %21, %28 ], [ %21, %35 ], ..
        ///////////////////////////////////////////////
  PHINode *PN = dyn_cast<PHINode>(TV);
        if(PN){
            //OP << "Inst: "<< *V <<"\n";
            //OP << "---The value is a phi\n";

            // Check each incoming value.
   for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i){
                
                //PHI sets this value according to inBB
                Value *IV = PN->getIncomingValue(i); // %21 %21
                BasicBlock *inBB = PN->getIncomingBlock(i); // %28 %35

                //All of the above values/blocks are out of current block
                //But not sure if they are out of current path

                if(!isConstant(IV)){
                    EV.push_back(IV);
                }

            }

            continue;
        }

        ///////////////////////////////////////////////
        // The value is a select instruction.  
        // %27 = select i1 %26, i32 %20, i32 %22
        ///////////////////////////////////////////////
        SelectInst *SI = dyn_cast<SelectInst>(TV);
        if(SI){
            //OP << "Inst: "<< *V <<"\n";
            //OP << "The value is a select\n";

            Value *Cond = SI->getCondition(); //%26
            Value* Truevalue = SI->getTrueValue(); //%20
            Value* Falsevalue = SI->getFalseValue(); //%22

            //OP << "Cond: "<<*Cond<<"\n";
            //OP << "True value: "<<*Truevalue<<"\n";
            //OP << "False value: "<<*Falsevalue<<"\n";

            if(!isConstant(Truevalue)){
                EV.push_back(Truevalue);
            }

            if(!isConstant(Falsevalue)){
                EV.push_back(Falsevalue);
            }

            continue;
        }

        ///////////////////////////////////////////////
        // The value is a shufflevector instruction.
        //  %174 = shufflevector <2 x i8*> %173, <2 x i8*> undef, <2 x i32> zeroinitializer
        ///////////////////////////////////////////////
        /* ShuffleVectorInst *SVI = dyn_cast<ShuffleVectorInst>(TV);
        if(SVI){
            OP << "Inst: "<< *TV <<"\n";
            OP << "The value is a shufflevector\n";

            auto oprand0 = I->getOperand(0);
            OP << "op0: "<<*oprand0<<"\n";
            auto oprand1 = I->getOperand(1);
            OP << "op1: "<<*oprand1<<"\n";
            
            continue;
        } */
        /*------------------------Multiple sources inst (end)------------------------*/


  /* for (User *U : TV->users()) {

   StoreInst *SI = dyn_cast<StoreInst>(U);
   if (SI && TV == SI->getValueOperand()) {

    for (User *SU : SI->getPointerOperand()->users()) {
     LoadInst *LI = dyn_cast<LoadInst>(SU);
     if (LI) {
      VSet.insert(LI);
      EV.push_back(LI);
     }
    }
   }
  } */

        //Resolve binary operation
        //更改策略：目前对存在1个常数操作数的binary operation，对非常量进行回溯
        auto opcodeName = I->getOpcodeName();
        if(1 == Ctx->BinaryOperandInsts.count(opcodeName)){
            //continue;
            //OP << "Inst: "<< *TV <<"\n";
            Value* op0 = I->getOperand(0);
            Value* op1 = I->getOperand(1);
            //OP << "op0: "<<*op0<<"\n";
            //OP << "op1: "<<*op1<<"\n";

            if(!isConstant(op0) && isConstant(op1)){
                EV.push_back(op0);
                continue;
            }
            else if(!isConstant(op1) && isConstant(op0)){
                EV.push_back(op1);
                continue;
            }

        }

        //TODO: support more LLVM IR types.
        //printf("\033[31m== Warning: unsupported LLVM IR:\033[0m\n");
        //OP << "IR: " << *TV << '\n';
        //OP << "opcode: "<<opcode<<"\n";
        //auto oprand0 = I->getOperand(0);
        //OP << "oprand0: "<<*oprand0<<"\n";
 }
}