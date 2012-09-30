/*****************************************************
Matthew Le
3975089
lexxx320

Progam Description:
This program reads in two lists of funbers, using the 
getList function, which enters the numbers into the list
as they are read from the terminal, returning the number
of elements entered by the user.  The listPrefix function
then checks to see if all of the elements of the first list
make up the first n elements of the second list, where n is 
the number of elements of the first list.
*****************************************************/

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
 //This function fills out the list provided, and returns
 //the size of the list.
int getList(int *list){
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
      list[i] = num;
    i++;
  }while(num >= 0);
  int sizeA = i-1;
  return sizeA;
}

main(int argc, char **argv){
  int listA[500];
  int listB[500];
  printf("please enter a list element by element that is terminated by a negative number\n");
  int sizeA = getList(listA);
  
  printf("please enter another list element by element that is terminated by a negative number\n");
  int sizeB = getList(listB);
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






