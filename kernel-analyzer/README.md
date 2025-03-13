# Linux Kernel Analyzer

This is a static kernel analyzer forked from [KINT](https://github.com/CRYPTOlab/kint).

## generate bitcode for Linux kernel
build LLVM with [this patch](https://github.com/Markakd/LLVM-O0-BitcodeWriter), then build kernel with the compiled clang.

## build the analyzer
set the LLVM_BUILD in the Makefile.inc to your local LLVM BUILD directory before running make.

## run the analyzer
Before dumping the execution path from the syscall to certain functions, you need to give the names of these functions, which should be assigned to the global variable funcDumpPath in GlobalCtx.h.

Specify the struct name and field index by initializing the variable pageStructField in PageAnalyzer.h.

```bash
./analyzer `find your_bitcode_folder -name "*.c.bc"` 
```
