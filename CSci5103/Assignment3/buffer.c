#include "buffer.h"

int addToBuffer(Color c, sharedMem_t *sharedMem){
  char *array[3] = {"dummy", "red", "white"};
  printf("adding %s to buffer\n", array[c]);
  if(*sharedMem->size == *sharedMem->maxSize){
    printf("buffer is at max capacity.\n");
    return -1;
  }
  if(*sharedMem->tail == (*sharedMem->maxSize)){
    sharedMem->buf[0] = c;
    *sharedMem->size = *sharedMem->size+1;
    *sharedMem->tail = 0;
    return *sharedMem->size;
  }
  printf("size = %d\n", *sharedMem->size);
  sharedMem->buf[*sharedMem->tail] = c;
  *sharedMem->size = *sharedMem->size+1;
  *sharedMem->tail = *sharedMem->tail + 1;
  return *sharedMem->size;
} 

Color removeFromBuffer(sharedMem_t *sharedMem){
  char *array[3] = {"dummy", "red", "white"};
  if(*sharedMem->head == *sharedMem->tail){
    printf("Buffer is empty.\n");
    return -1;
  }
  
  Color temp = sharedMem->buf[*sharedMem->head];
  sharedMem->buf[*sharedMem->head] = 0;
  
  printf("removing %s from buffer\n", array[temp]);
  if(*sharedMem->head == (*sharedMem->maxSize)-1){
    *sharedMem->head = 0;
    *sharedMem->size = *sharedMem->size - 1;
    return temp;
  }
  *sharedMem->head = *sharedMem->head + 1;
  *sharedMem->size = *sharedMem->size - 1;
  return temp;
}

void printBuffer(sharedMem_t *sharedMem){
  int i, n, j;
  j = 0;
  char *array[3] = {"dummy", "red", "white"};
  n = *sharedMem->size;
  i = *sharedMem->head;
  while(i != (*sharedMem->tail)){
    printf("buffer[%d] = %s\n", i, array[sharedMem->buf[i]]);
    if(i == *sharedMem->maxSize - 1){
      i = 0;
    }
    else{
      i = i + 1;
    }
    j++;
  }
  
}
