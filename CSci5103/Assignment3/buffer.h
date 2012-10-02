#include <stdio.h>
#include <stdlib.h>

typedef enum e_color{
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

int addToBuffer(Color c, Buffer *buf);
Color removeFromBuffer(Buffer *buf);
void printBuffer(Buffer *buf);




