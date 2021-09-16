#!/bin/bash -e
  

# LLVM version: 10.0.0 (as of 09/12/2019)

ROOT=$(git rev-parse --show-toplevel)
cd $ROOT/llvm/llvm-project

if [ ! -d "buildMips" ]; then
  mkdir buildMips
fi

cd buildMips
cmake -DLLVM_TARGET_ARCH="Mips" -DLLVM_TARGETS_TO_BUILD="Mips" -DCMAKE_BUILD_TYPE=Release \
                        -DLLVM_ENABLE_PROJECTS="clang" -G "Unix Makefiles" ../llvm
make -j8

if [ ! -d "$ROOT/llvm/llvm-project/prefixMips" ]; then
  mkdir $ROOT/llvm/llvm-project/prefixMips
fi

cmake -DCMAKE_INSTALL_PREFIX=$ROOT/llvm/llvm-project/prefixMips -P cmake_install.cmake

