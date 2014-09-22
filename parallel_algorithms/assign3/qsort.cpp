

#include <stdio.h>
#include <stdlib.h>
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#include <time.h>
#include <sys/time.h>

void printArr(float * arr, int n){
	for(int i = 0; i < n; i++){
		printf("%.2f, ", arr[i]);
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

int fib(int n)
{
    if (n < 2)
        return n;
    int x = cilk_spawn fib(n-1);
    int y = fib(n-2);
    cilk_sync;
    return x + y;
}

int partition(float * arr, int n){
	int ind = n/2;
	float pivot = arr[ind]; 
	int count = 0;
	float temp = arr[ind];
	arr[ind] = arr[n-1];
	arr[n-1] = temp;
	
	for(int i = 0; i < n-1; i++){
		if(arr[i] < pivot){
			temp = arr[i];
			arr[i] = arr[count];
			arr[count] = temp;
			count++;
		}	
	}

	temp = arr[count];
	arr[count] = arr[n-1];
	arr[n-1] = temp;
	
	return count;
}

float * qsort(float * arr, int n){
	if(n > 1){
		int pivot = partition(arr, n);
		cilk_spawn qsort(arr, pivot);
		qsort(arr + pivot, n - pivot);
		cilk_sync;
	}
	return arr;
}

bool chk(float * arr, int n){
	bool res = true;
	for(int i = 1; i < n; i++){
		res = res && (arr[i] > arr[i-1]);
	}	
	if(res){
		printf("Result is correct\n");
	}else{
		printf("Result is incorrect\n");
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

    // If we've got a parameter, assume it's the number of workers to be used
    if (argc > 1)
    {
        // Values less than 1, or parameters that aren't numbers aren't allowed
        if (atoi(argv[1]) < 1)
        {
            printf("Usage: fib [problem size]\n");
            return 1;
        }

        n = atoi(argv[1]);
    }

    // Time how long it takes to calculate the nth Fibonacci number
    float * arr = genArray(n);
    unsigned long long start = cilk_getticks();
    qsort(arr, n);
    unsigned long long end = cilk_getticks();
    
	chk(arr, n);

    // Display our results
    double duration = cilk_ticks_to_seconds(end - start);
    printf("Calculated in %.3f seconds using %d workers.\n",
           duration, __cilkrts_get_nworkers());

    return 0;
}
