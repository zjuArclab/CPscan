


void ObtainFuncPairOfBCfile(map<string, string> PairOfBCfile)
{
    SMDiagnostic Err;
    map<string, string>::iterator iter;
    int MapFucByName = 0;
    int curBC = 0;
    int curFuc = 0;
    int unfinished_CMP = 0;
    clock_t totalstartTime,totalendTime;
    totalstartTime = clock();
    for(iter = PairOfBCfile.begin(); iter != PairOfBCfile.end(); iter++){
        // Obtain PairOfFunctions
        curBC ++;
        std::cout<<"curBC is :"<<curBC<<"\n";
        LLVMContext *LLVMCtxFirmware = new LLVMContext();
        LLVMContext *LLVMCtxKernel = new LLVMContext();
        // Parse IR for the first .bc file.
        unique_ptr<Module> MFirmware = parseIRFile(iter->first, Err, *LLVMCtxFirmware);
        StringRef MFName = StringRef(strdup(iter->first.data())); //MName  /home/yjq/Fulirong/Data/bitcode/linux-5.3.0/mm/backing-dev.bc 
        //push_back(make_pair(MFirmware, MFName))
        OP<<"Firmware File name: "<< MFName<<"\n"; 

        // Parse IR for the seconf .bc file.
        unique_ptr<Module> MKernel = parseIRFile(iter->second, Err, *LLVMCtxKernel);
        StringRef MKName = StringRef(strdup(iter->second.data())); //MName  /home/yjq/Fulirong/Data/bitcode/linux-5.3.0/mm/backing-dev.bc 
        //push_back(make_pair(MKernel, MKName))
        OP<<"Kernel File name: "<< MKName<<"\n"; 
        ofstream ofile;
        ofile.open("test-filter.txt", ios::app);
        if(!ofile){
            cerr<<"Open File Fail."<<endl;
            exit(1);
            }
        ofile<<"Kernel File name:  ";
        string filename = MKName;
        ofile<< filename;
        ofile<<"\n";
        ofile.close();
        // if(curBC >3)
        //     break ;
        
        //获得MFirmware
        if (MFirmware == NULL) {
                OP <<  " llvm-diff, error loading file: "
                    << iter->first << "'\n";
                continue;
            }

        Module *ModuleFirmware = MFirmware.release();
        //获得MKernel
        if (MKernel == NULL) {
                OP <<  " llvm-diff, error loading file: "
                    << iter->second << "'\n";
                continue;
            }
        
        Module *ModuleKernel = MKernel.release();  
        // 遍历Module，获得Module中的每一个函数
        string BCContend = "";
        // string BCpath = "/home/yjq/Fulirong/Tools/cheq/deadline-arm/code/FilterSC/Firm-BC//usbnet.bc";
        // if(MFName == BCpath)
        for (Module::iterator f = ModuleFirmware->begin(), fe = ModuleFirmware->end(); 
                f != fe; ++f) {
                //curFuc++;
                Function *F = &*f;
                if (F->empty())
			        continue;
		        if (F->size() > MAX_BLOCKS_SUPPORT)
			        continue;
                unrollLoops_l(F);
                // obtain func name of .bc file in Firmware
                for (Module::iterator k = ModuleKernel->begin(), ke = ModuleKernel->end(); 
                k != ke; ++k) {
                    Function *K = &*k;
                    if (K->empty())
                    continue;
		            if (K->size() > MAX_BLOCKS_SUPPORT)
			        continue;
                    unrollLoops_l(K);
                   
                    // Perform Function Match
                    //if(MFName=="/home/yjq/Fulirong/Data/bitcode/firmware-bit-code/Asuswrt-src-rt-7.14.114.x-linux-2.6.36/drivers/net/usb/usbnet.bc")
                    if (F->getName() == K->getName()){
                        
                        MapFucByName ++;
                        
                        OP<<"Firmware File name: "<< MFName<<"\n"; 
                        OP << "Function name is:" << F->getName() <<"\n";
                        // Obtain the conditional states of functions.
                        //vector<Value*> FConds = ObtainConds(F);
                        //vector<Value*> KConds = ObtainConds(K);
                        // Graph cfgF;
                        // Graph cfgK;
                        //if(F->getName() == "load_aout_binary")
                        //if(F->getName() == "usbnet_change_mtu")
                       
                        // Compare the conditional states
                        //cfgF = 
                        //ObtainCFG(F);
                        //cfgK = ObtainCFG(K);
                        //CompareConds(F, FConds, K, KConds);

                        //obtain all malloc instructions within a function 
                        // test
                        std::chrono::system_clock::time_point seconds_passed
                        = std::chrono::system_clock::now() + std::chrono::seconds(10);
                        std::promise<int> p2;
                        std::future<int> f_times_out = p2.get_future();
                        std::thread([F,K,MKName](std::promise<int> p2)
                                    { 
                                        std::this_thread::sleep_for(std::chrono::seconds(5)); 
                                        clock_t startTime,endTime;
                                        startTime =clock();
                                        //CompareCFG(F,K,MKName);
                                        //CompareCFG(F, K, MKName, KGlobalCtx, FGlobalCtx);
                                        endTime = clock();
                                        std::cout << "The run time is:" <<(double)(endTime - startTime) / CLOCKS_PER_SEC << "s." << "\n";
                                        //std::cout <<(double)(endTime - startTime) / CLOCKS_PER_SEC <<  "\n";
                                        CompareTime += (double)(endTime - startTime) / CLOCKS_PER_SEC;
                                        p2.set_value_at_thread_exit(8); 
                                    }, 
                                    std::move(p2)
                        ).detach();
                        if(std::future_status::ready == f_times_out.wait_until(seconds_passed))
                            { OP << "CMP finished: " << f_times_out.get() << "\n"; }
                        else
                            { std::cout << "f_times_out did not complete!\n"; 
                              OP << "f_times_out did not complete!\n"; 
                              unfinished_CMP++;
                            }
                        //
                        //CompareCFG(F,K);
                        break;    
                    }
                }
            }
    }    
    totalendTime=clock();
    OP << "MapFucByName: " << MapFucByName<< "\n";
    OP<< "NotIdenticalFunc: " << NotIdenticalFunc <<"\n";
    OP<< "unfinished_CMP: " << unfinished_CMP <<"\n";
    OP << "Compare time is:" <<CompareTime << "s" << "\n";
    OP << "The Total run time is:" <<(double)(totalendTime - totalstartTime) / CLOCKS_PER_SEC << "s" << "\n";

    std::cout << "MapFucByName: " << MapFucByName<< "\n";
    std::cout<< "NotIdenticalFunc: " << NotIdenticalFunc <<"\n";
    std::cout<< "unfinished_CMP: " << unfinished_CMP <<"\n";
    std::cout << "Compare time is:" <<CompareTime << "s" << "\n";
    std::cout << "The Total run time is:" <<(double)(totalendTime - totalstartTime) / CLOCKS_PER_SEC << "s" << "\n"; 

}