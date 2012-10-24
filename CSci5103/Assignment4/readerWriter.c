#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <semaphore.h>
#include <string.h>

sem_t okToWrite;
sem_t okToRead;
sem_t mutex;
FILE *writersFile;
int activeReaders, waitingReaders, activeWriters, waitingWriters, totalLines;
long int writerOffset;

int read(FILE *outputFile, FILE *writersFile, int numLines, long int *offset){
  
  int itemsRead;
  char line[16];
  int i;
   
  for(i = 0; i < 5; i++){
    //--------------------------Get Line--------------------------------
    sem_wait(&mutex);
    fseek(writersFile, *offset, SEEK_SET);       //find correct offset
    char *temp = fgets(line, 16, writersFile);   //read from file
    *offset = ftell(writersFile);                //update offset
    sem_post(&mutex);
    //-----------------------------------------------------------------
    if(temp == NULL){
      printf("Did not read all 5 chars.\n");
      return numLines;
    }
    //printf("just read line%d\n", numLines);
    fprintf(outputFile, "%s", line);
    numLines++;
  }
  return numLines;
}

void startRead(int id, int readLines){
  sem_wait(&mutex);
  if(activeWriters + waitingWriters == 0){          //no one writing or waiting to write
    sem_post(&okToRead);
  }
  else{
    printf("reader%d waiting to read.\n", id);
    printf("activeWriters = %d, waitingWriters = %d\n", activeWriters, waitingWriters);
  } 
  waitingReaders++;
  sem_post(&mutex);
  sem_wait(&okToRead);
  waitingReaders--;
  activeReaders++;
  printf("reader%d currently reading.\n", id);
}

void endRead(int id){
  sem_wait(&mutex);
  activeReaders--;
  //printf("reader%d done reading.\n", id);
  if(activeReaders == 0 && waitingWriters > 0){
    activeWriters++;
    waitingWriters--;
    sem_post(&okToWrite);
  }
  sem_post(&mutex);
}

void* reader(void *args){
  int id = *((int*)args);
  char fileName[100];
  char idString[10];
  sprintf(idString, "%d", id);
  strcpy(fileName, "reader");
  strcat(fileName, idString);
  strcat(fileName, "_output_file");
  FILE *readerFile = fopen(fileName, "w");
  int linesRead = 0;
  int previousLinesRead = 0;
  long int fileOffset = 0;
  int readLines = 1;
  
  while(linesRead < totalLines){
    startRead(id, readLines);
    linesRead = read(readerFile, writersFile, linesRead, &fileOffset);
    printf("reader%d finished reading line %d\n", id, linesRead);
    endRead(id);
    if(previousLinesRead == linesRead){
      readLines = 0;
    } 
    else{
      readLines = 1;
    }
    previousLinesRead = linesRead;
  }
  printf("reader%d exiting...\n", id);
  return args; 
}

int write(int id, int currentNum, FILE *writerFile){
  int i;
  fseek(writerFile, writerOffset, SEEK_SET);
  for(i = currentNum; i < currentNum+5; i++){
    fprintf(writerFile, "<W%d, %d>\n", id, i);
  }
  currentNum = currentNum+5;
  writerOffset = ftell(writerFile);
  printf("writer%d finished writing element %d\n", id, currentNum);
  return (currentNum);
}

void startWrite(int id){
  sem_wait(&mutex);
  if(activeWriters + activeReaders + waitingWriters == 0){
    sem_post(&okToWrite);
    activeWriters++;
  }
  else{
    printf("writer%d waiting to write.\n", id);
    waitingWriters++;
  }
  sem_post(&mutex);
  sem_wait(&okToWrite);
  printf("writer%d currently writing.\n", id);
}

void endWrite(int id){
  sem_wait(&mutex);
  activeWriters--;
  printf("writer%d done writing.\n", id);
  if(waitingWriters > 0){
    printf("%d writers are currently waiting.\n", waitingWriters);
    sem_post(&okToWrite);
    activeWriters++;
    waitingWriters--;
  }
  else{
    int i;
    for(i = 0; i < waitingReaders; i++){
      sem_post(&okToRead);
    }
  }
  sem_post(&mutex);
}

void* writer(void *args){
  int id = *((int*)args);
  int currentNum = 1;
  
  while(currentNum < 100){
    startWrite(id);
    currentNum = write(id, currentNum, writersFile);
    endWrite(id); 
  }  
  printf("writer%d exiting...\n", id);
  return args;
}


int main(int argc, char **argv){
  if(argc != 3){
    printf("usage: \"%s [numReaders] [numWriters]\"\n", argv[0]);
    exit(1);
  }
  int numReaders = atoi(argv[1]); 
  int numWriters = atoi(argv[2]);

  writersFile = fopen("writer_output_file", "w+r");

  //pthread_t *readers = (pthread_t*)malloc(sizeof(pthread_t) * numReaders);
  //pthread_t *writers = (pthread_t*)malloc(sizeof(pthread_t) * numWriters);
  
  pthread_t readers[numReaders];
  pthread_t writers[numWriters];
  
  sem_init(&okToRead, 0, 0);
  sem_init(&okToWrite, 0, 0);
  sem_init(&mutex, 0, 1);
  writerOffset = 0;
  int i;
  totalLines = 100*numWriters;
  int idsReaders[numReaders];  
  //Dispatch reader threads
  for(i = 0; i < numReaders; i++){
    idsReaders[i] = i;
    pthread_create(readers + i, NULL, reader, (void*)&idsReaders[i]);
  }
  
  int idsWriters[numWriters];
  //Dispatch writer threads
  for(i = 0; i < numWriters; i++){
    idsWriters[i] = i;
    pthread_create(writers + i, NULL, writer, (void*)&idsWriters[i]);
  }
  
  
  for(i = 0; i < numWriters; i++){
    if((pthread_join(writers[i], NULL)) != 0){
      perror("pthread_join writers.\n");
      exit(1);
    }
  }
  for(i = 0; i < numReaders; i++){
    if((pthread_join(readers[i], NULL)) != 0){
      perror("pthread_join readers.\n");
      exit(1);
    }
  }
  //free(readers);
  //free(writers);
  fclose(writersFile);
  //*/
  
  return 0;
}



