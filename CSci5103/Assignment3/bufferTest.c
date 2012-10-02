#include "buffer.h"

int  main(int argc, char **argv){
  Buffer *buf = (Buffer*)malloc(sizeof(Buffer));
  buf->head = (Node*)malloc(sizeof(Node));
  addToBuffer(red, buf);
  addToBuffer(white, buf);
  addToBuffer(red, buf);
  printBuffer(buf);
  removeFromBuffer(buf);
  printBuffer(buf);
  return 0;
}

 
