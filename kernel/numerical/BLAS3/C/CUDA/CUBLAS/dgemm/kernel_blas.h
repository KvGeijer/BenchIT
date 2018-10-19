#include <stdio.h>
#include <stdlib.h>
#include <cuda_runtime.h>
#include <cublas_v2.h>

#define CUBLAS_CHECK(cmd) {cudaError_t error = cmd; if(error!=CUBLAS_STATUS_SUCCESS){printf("<%s>:%i error = %i\n",__FILE__,__LINE__, error); bi_abort(1);return 1;}}
#define CUBLAS_STAT_CHECK(cmd) {cublasStatus_t stat = cmd; if(stat!=cudaSuccess){printf("<%s>:%i error = %i\n",__FILE__,__LINE__, stat); return 1;}}
#define CHECK_NULL(op) {if (NULL == op){printf("<%s>:%i operand was NULL\n",__FILE__,__LINE__); bi_abort(1); return 1;}}
