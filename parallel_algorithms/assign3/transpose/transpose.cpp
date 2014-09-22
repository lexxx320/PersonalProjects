#include <stdio.h>
#include <stdlib.h>
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#include <time.h>
#include <sys/time.h>
#include <string.h>

int n = 10; 
int m = 10;

#define IND(mat, i, j) mat[j + i * m]
#define IND2(mat, i, j, numCols) mat[j + i * numCols]

void printMat(float * mat, int n, int m){
	for(int i = 0; i < n; i++){
		for(int j = 0; j < m; j++){
			printf("%.0f, ", IND(mat, i , j));
		}
		printf("\n");
	}
	printf("\n\n");
}

static inline unsigned long long cilk_getticks()
{
     struct timeval t;
     gettimeofday(&t, 0);
     return t.tv_sec * 1000000ULL + t.tv_usec;
}

static inline double cilk_ticks_to_seconds(unsigned long long ticks)
{
     return ticks * 1.0e-6;
}

float * genMat(){
	float * mat = (float*)malloc(sizeof(float) * n * m);
	for(int i = 0; i < n; i++){
		for(int j = 0; j < m; j++)
			IND(mat, i, j) = j + i * m;
	}
	return mat;
}

float * transpose(float * mat){
	float * res = (float*)malloc(sizeof(float) * n * m);

	cilk_for(int i = 0; i < n; i++){
		for(int j = 0; j < m; j++){
			IND2(res, j, i, n) = IND(mat, i, j);
		}
	}
	
	return res;
}	

float * transpose_in_place(float * mat){
	if(n != m){
		printf("in place transposition currently only works with square matrices\n");
		return NULL;
	}
	cilk_for(int i = 0; i < n; i++){
		for(int j = i+1; j < n; j++){
			IND(mat, j, i) = IND(mat, i, j);
		}
	}
	return mat;
}	

int main(int argc, char *argv[])
{
    // number of elements to be sorted
    if(argc == 2){
		if (atoi(argv[1]) < 1){
            printf("Usage: transpose [n] (square matrices)\n");
            exit(1);
        }
        n = atoi(argv[1]); m = atoi(argv[1]);
    }
    if (argc > 2){
        if (atoi(argv[1]) < 1 || atoi(argv[2]) < 1){
            printf("Usage: fib [problem size]\n");
            exit(1);
        }
        n = atoi(argv[1]); m = atoi(argv[2]);
        if(argc > 3){
			__cilkrts_set_param("nworkers", argv[3]);
        }
    }

    // Time how long it takes to calculate the nth Fibonacci number
    float * mat = genMat();
	//printMat(mat, n, m);
    unsigned long long start = cilk_getticks();
    float * res = transpose(mat);
    unsigned long long end = cilk_getticks();

    // Display our results
    double duration = cilk_ticks_to_seconds(end - start);
    printf("Calculated in %.3f seconds using %d workers.\n",
           duration, __cilkrts_get_nworkers());

	free(res);
	
	start = cilk_getticks();
	res = transpose_in_place(mat);
	end = cilk_getticks();
	
	if(res != NULL){
		duration = cilk_ticks_to_seconds(end - start);
		 printf("Calculated in %.3f seconds using %d workers (in place).\n",
           duration, __cilkrts_get_nworkers());
	}

	free(mat);



    return 0;
}












