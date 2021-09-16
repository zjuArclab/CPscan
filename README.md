# CPscan: Detecting Bugs Causedby Code Pruning in IoT Kernels

Code pruning is prevalent in IoT kernels. we present CPscan, a system 
for automatically detecting bugs caused by code pruning in IoT kernels. 
First, using a new graph-based approach that iteratively conducts a 
structure-aware basic block matching, CPscan can precisely and efficiently 
identify the deleted security operations in IoT kernels. 
Then, CPscan infers the security impact of a  deleted security operation
by comparing the bounded use chain. The tool, CPscan, can help automatically 
identify bugs caused by the deletions of security operations in OS kernels.  



## How to use CPscan


### prerequisites 
```sh
- boost_1_72_0
- openmpi
- llvm

```
### Build LLVM 
```sh 
	$ cd llvm 
	$ ./build-llvm.sh 
	# The installed LLVM is of version 10.0.0 
```

### Build the CPscan analyzer 
```sh 
	# Build the analysis pass of CPscan 
	$ cd ../analyzer 
	$ make 
	# Now, you can find the executable, `kanalyzer`, in `build/lib/`
```
 
### Prepare LLVM bitcode files of OS kernels


* The code should be compiled with the built LLVM
* Compile the code with options: -O0 or -O2, -g, -fno-inline


### Run the CPscan analyzer
```sh
	# To analyze a single bitcode file, say "test.bc", run:
	$ ./build/lib/kanalyzer -sc test.bc
	# To analyze a list of bitcode files, put the absolute paths of the bitcode files in a file, say "bc.list", then run:
	$ ./build/lib/kalalyzer -sc @bc.list
```


