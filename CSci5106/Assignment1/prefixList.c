#include <stdlib.h>
#include <stdio.h>

int listPrefix(int listA[], int sizeA, int listB[], int sizeB){
  int i;
  for(i = 0; i < sizeA; i++){
    if(listA[i] != listB[i]){
      return 0;
    }
  }
  return 1;
}

main(int argc, char **argv){
  int listA[500];
  int listB[500];
  printf("please enter a list element by element that is terminated by a negative number\n");
  int num;
  char tempChar[256];
  int i = 0;
  do{
    if(i > 500){
      printf("exceeded list size\n");
      break;
    }
    fgets(tempChar, 256, stdin);
    num = atoi(tempChar);
    if(num > 0)
      listA[i] = num;
    i++;
  }while(num >= 0);
  int sizeA = i-1;
  printf("please enter another list element by element that is terminated by a negative number\n");
  i = 0;
  do{
    if(i > 500){
      printf("exceeded list size\n");
      break;
    }
    fgets(tempChar, 256, stdin);
    num = atoi(tempChar);
    if(num > 0)
      listB[i] = num;
    i++;
  }while(num >= 0);
  int sizeB = i-1;
  int retVal = listPrefix(listA, sizeA, listB, sizeB);
  if(retVal == 0){
    printf("The first list is not the prefix of the second.\n");
  }
  else if(retVal == 1){
    printf("The first list is the prefix of the second list.\n");
  }
  else{
    perror("return value error from listPrefix function, exiting...\n");
    exit(1);
  }
}






