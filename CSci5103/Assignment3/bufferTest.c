#include <stdio.h>
#include <stdlib.h>
#include <semaphore.h>
#include "buffer.h"
#include <unistd.h>
#include <sys/ipc.h>
#include <sys/types.h>
#include <sys/shm.h>

int  main(int argc, char **argv){
  key_t key = 4455;
  int size = 1024;
  int flag = 0;
  flag = flag | IPC_CREAT;
  flag = flag| 00400 |00200 |00040 | 00020| 00004 | 00002 ;
  int shmem_id;
  char* shmem_ptr;
  
  if((shmem_id = shmget(key, size, flag)) == -1){
    perror("shmget failed\n");
    exit(1);
  } 
  
  if((shmem_ptr = shmat(shmem_id, (void*)NULL, flag)) == (void*) -1){
    perror("shmat failed\n");
    exit(1);
  }

  sharedMem_t *sharedMem = (sharedMem_t*)malloc(sizeof(sharedMem_t));
  sharedMem->head = (int*)shmem_ptr;
  sharedMem->tail = (int*)shmem_ptr+4;
  sharedMem->size = (int*)shmem_ptr+8;
  sharedMem->maxSize = (int*)shmem_ptr + 12;
  sharedMem->buf = (Color*)shmem_ptr + 16;
  
  *sharedMem->head = 0;
  *sharedMem->tail = 0;
  *sharedMem->size = 0;
  *sharedMem->maxSize = 4;
  
  addToBuffer(red, sharedMem);
  printBuffer(sharedMem);
  addToBuffer(white, sharedMem);
  printBuffer(sharedMem);
  addToBuffer(red, sharedMem);
  printBuffer(sharedMem);
  addToBuffer(white, sharedMem);
  
  printBuffer(sharedMem);
  
  removeFromBuffer(sharedMem);
  printBuffer(sharedMem);
  removeFromBuffer(sharedMem);
  printBuffer(sharedMem);
  addToBuffer(white, sharedMem);
  printBuffer(sharedMem);
  
  
  shmdt((void*)shmem_ptr);
  shmctl(shmem_id, IPC_RMID, NULL);
  return 0;
}

 
