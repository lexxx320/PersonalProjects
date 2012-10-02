#include "buffer.h"

int addToBuffer(Color c, Buffer *buf){
  Node *ptr = buf->head->next;
  Node *trailer = buf->head;
  Node *item = (Node*)malloc(sizeof(Node));
  item->color = c;
  item->next = NULL;
  
  if(ptr == NULL){
    trailer->next = item;
    
    buf->size = 1;
    
    return buf->size;
  }
  
  while(ptr != NULL){
    ptr = ptr->next;
    trailer = trailer->next;
  }

  trailer->next = item;
  buf->size = buf->size+1;
  return buf->size;  
}

Color removeFromBuffer(Buffer *buf){
  if(buf->size == 0){
    return (Color)NULL;
  }
  Node *temp = buf->head->next;
  Color tempColor = temp->color;
  buf->head->next = temp->next;
  free(temp);
  buf->size = buf->size - 1;
  return tempColor;
} 

void printBuffer(Buffer *buf){
  char *colorArray[2] = {"red", "white"};
  Node *ptr;
  ptr = buf->head->next;
  printf("buffer size = %d\n", buf->size);
  while(ptr != NULL){
    printf("color = %s\n", colorArray[ptr->color]);
    ptr = ptr->next;
  }
}










