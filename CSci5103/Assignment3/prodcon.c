#include <stdio.h>
#include <stdlib.h>
#include <semaphore.h>
#include "buffer.h"
#include <unistd.h>
#include <sys/ipc.h>
#include <sys/types.h>
#include <sys/shm.h>

#define True 1
#define False 0
#define iterations 100
sem_t mutex;
sem_t empty;
sem_t full;
sem_t alternate;
Buffer *buf;

char *widgetArray[2] = {"red", "white"};
int bufferSize;

void consumer(sharedMem_t *sharedMem){
  int i = 0;
  while(i < iterations){
    sem_wait(&full);
    sem_wait(&mutex);
    Color c = removeFromBuffer(buf);
    printf("consumed %s widget.\n", widgetArray[c]);
    sem_post(&mutex);
    sem_post(&empty);
    i++;
  } 
}

void whiteProducer(sharedMem_t *sharedMem){
  int i = 0;
  while(i < iterations){
    sem_wait(&empty);
    sem_wait(&alternate);
    sem_wait(&mutex);
    printf("Adding red widget.\n");
    addToBuffer(white, buf);
    sem_post(&mutex);
    sem_post(&alternate);
    sem_post(&full);
    i++;
  }
}

void redProducer(sharedMem_t *sharedMem){
  int i = 0;
  while(i < iterations){
    sem_wait(&empty);
    sem_wait(&alternate);
    sem_wait(&mutex);
    printf("Adding white widget.\n");
    addToBuffer(red, buf);
    sem_post(&mutex);
    sem_post(&alternate);
    sem_post(&full);
    i++;
  }
}

int main(int argc, char**argv){ 
  if(argc != 2){
    printf("User must input only the size of the buffer.\n");
    exit(1);
  }
  bufferSize = atoi(argv[1]);
  buf = (Buffer*)malloc(sizeof(Buffer));
  buf->head = (Node*)malloc(sizeof(Node));
  sem_init(&mutex, 1, 1); 
  sem_init(&empty, 1, bufferSize);
  sem_init(&full, 1, 0);
  sem_init(&alternate, 1, 1);
  
  key_t key = 4455;
  int size = 2048;
  int flag = 0;
  flag = flag | IPC_CREAT;
  flag = flag| 00400 |00200 |00040 | 00020| 00004 | 00002 ;
  int shmem_id;
  char* shmem_ptr;
  
  if((shmem_id = shmget(key, size, flag)) == -1){
    perror("shmget failed data memory\n");
    exit(1);
  } 
  
  if((shmem_ptr = shmat(shmem_id, (void*)NULL, flag)) == (void*) -1){
    perror("shmat failed for data memory\n");
    exit(1);
  }
  sharedMem_t *sharedMem = (sharedMem_t*)malloc(sizeof(sharedMem_t));
  sharedMem->head = (int*)shmem_ptr;
  sharedMem->tail = (int*)shmem_ptr+4;
  sharedMem->size = (int*)shmem_ptr+8;
  sharedMem->maxSize = (int*)shmem_ptr+12;
  sharedMem->buf = (Color *)shmem_ptr+16;
  
  
  
  pid_t childPID = fork();
  if(childPID == 0){ //child process
    redProducer(sharedMem);
  }
  else if(childPID > 0){//parent process
    pid_t childPID2 = fork();
    if(childPID2 == 0){ //second child process
      whiteProducer(sharedMem);
    }
    else if(childPID2 > 0){ //parent process
      consumer(sharedMem);
    }
    else{
      perror("Fork Error\n");
      exit(1);
    }
  }
  else{
    perror("Fork Error\n");
    exit(1);
  }
  return 0;
}




