#include <stdio.h>
#include <stdlib.h>
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#include <time.h>
#include <sys/time.h>
#include <string.h>

#define INTENTIONAL_RACE

void printArr(float * arr, int n){
	for(int i = 0; i < n; i++){
		printf("%.4f, ", arr[i]);
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

void merge(float * arr1, float * arr2, int n1, int n2){
	float * temp = (float*)malloc(sizeof(float) * (n1 + n2));
	int i1 = 0;
	int i2 = 0;
	int i = 0;
	while(i1 < n1 &&i2 < n2){
		if(arr1[i1] < arr2[i2]){
			temp[i] = arr1[i1];
			i++; i1++;
		}else{
			temp[i] = arr2[i2];
			i++; i2++;
		}
	}

	if(i1 == n1){
		while(i2 < n2){
			temp[i] = arr2[i2];
			i++; i2++;
		}
	}else{
		while(i1 < n1){
			temp[i] = arr1[i1];
			i++; i1++;
		}
	}

	memcpy(arr1, temp, sizeof(float) * (n1+n2));
	free(temp);
	
}

float * msort(float * arr, int n){
	if(n > 1){
		int pivot = n/2;
		cilk_spawn msort(arr, pivot);
		msort(arr+pivot, n - pivot);
		cilk_sync;
		merge(arr, arr+pivot, pivot, n-pivot);
	}
	return arr;
}

bool chk(float * arr, int n){
	bool res = true;
	for(int i = 1; i < n; i++){
		if(arr[i] < arr[i-1]){
			printf("Result is incorrect at position %d\n", i);
			printArr(arr, n);
			res = false; 
			break;
		}	
	}	
	return res;
}

float * genArray(int n){
	srand(time(NULL));
	float * arr = (float*)malloc(sizeof(float) * n);
	for(int i = 0; i < n; i++){
		arr[i] = (float)rand() / (float)RAND_MAX;
	}
	return arr;
}

int main(int argc, char *argv[])
{
    // number of elements to be sorted
    int n = 40;

    if (argc > 1){
        if (atoi(argv[1]) < 1){
            printf("Usage: fib [problem size]\n");
            exit(1);
        }
        n = atoi(argv[1]);
        if(argc > 2){
			__cilkrts_set_param("nworkers", argv[2]);
        }
    }

    // Time how long it takes to calculate the nth Fibonacci number
    float * arr = genArray(n);

    unsigned long long start = cilk_getticks();
    msort(arr, n);
    unsigned long long end = cilk_getticks();
    
	chk(arr, n);

    // Display our results
    double duration = cilk_ticks_to_seconds(end - start);
    printf("Calculated in %.3f seconds using %d workers.\n",
           duration, __cilkrts_get_nworkers());

    return 0;
}
