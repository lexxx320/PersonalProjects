#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

void* reader(void *args){
  int threadId = 12;
  threadId = *(int*)args;
  printf("reader id = %d\n", threadId);

  return args; 
}

void* writer(void *args){
  int threadId = *(int*)args;
  printf("writer id = %d\n", threadId);
  return args;
}

int main(int argc, char **argv){
  if(argc != 3){
    printf("usage: \"%s [numReaders] [numWriters]\"\n", argv[0]);
    exit(1);
  }
  int numReaders = atoi(argv[1]); 
  int numWriters = atoi(argv[2]);

  pthread_t readers[numReaders];
  pthread_t writers[numWriters];

  int i;
  //Dispatch reader threads
  for(i = 0; i < numReaders; i++){
    pthread_create(readers + i, NULL, reader, (void*)&i);
  }
  //Dispatch writer threads
  for(i = 0; i < numWriters; i++){
    pthread_create(writers + i, NULL, writer, (void*)&i);
  }

  void *returnStatus;
  for(i = 0; i < numWriters; i++){
    pthread_join(readers[i], &returnStatus);
  }
  for(i = 0; i < numReaders; i++){
    pthread_join(writers[i], &returnStatus);
  }
  
  return 0;
}



