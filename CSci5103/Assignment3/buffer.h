#include <stdio.h>
#include <stdlib.h>

typedef enum e_color{
  dummy,
  red,
  white
}Color;

typedef struct Node_t{
  Color color;
  struct Node_t * next;
}Node;

typedef struct Buffer_t{
  Node *head;
  int size;
}Buffer;

typedef struct sharedMem_t{
  Color * buf;
  int *head;
  int *tail;
  int *size;
  int *maxSize;
}sharedMem_t;

int addToBuffer(Color c, sharedMem_t *);
Color removeFromBuffer(sharedMem_t*);
void printBuffer(sharedMem_t*);




