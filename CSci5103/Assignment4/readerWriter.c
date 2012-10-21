#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <semaphore.h>
#include <string.h>

sem_t okToWrite;
sem_t okToRead;
sem_t mutex;
int activeReaders, waitingReaders, activeWriters, waitingWriters;

typedef struct threadInfo_t{
  int id;
  int totalLines;
  FILE *writerFile;
}ThreadInfo;

int read(FILE *outputFile, FILE *writersFile, int numLines){
  
  int itemsRead;
  char line[16];
  int i;
  for(i = 0; i < 5; i++){
    if(fgets(line, 16, writersFile) == NULL){
      printf("No chars read.\n");
      sleep(1);
      return numLines;
    }
    fprintf(outputFile, "%s", line);
    numLines++;
  }
  return numLines;
}

void startRead(int id){
  sem_wait(&mutex);
  if(activeWriters + waitingWriters == 0){
    sem_post(&okToRead);
    activeReaders++;
  }
  else{
    printf("reader%d waiting to read.\n", id);
  } 
  waitingReaders++;
  sem_post(&mutex);
  sem_wait(&okToRead);
  waitingReaders--;
  printf("reader%d currently reading.\n", id);
}

void endRead(int id){
  sem_wait(&mutex);
  activeReaders--;
  printf("reader%d done reading.\n", id);
  if(activeReaders == 0 && waitingWriters > 0){
    sem_post(&okToWrite);
    activeWriters++;
    waitingWriters--;
  }
  sem_post(&mutex);
}

void* reader(void *args){
  ThreadInfo info = *((ThreadInfo*)args);
  char fileName[100];
  char idString[10];
  sprintf(idString, "%d", info.id);
  strcpy(fileName, "reader");
  strcat(fileName, idString);
  strcat(fileName, "_output_file");
  FILE *readerFile = fopen(fileName, "w");
  int linesRead = 0;

  while(linesRead < info.totalLines){
    startRead(info.id);
    linesRead = read(readerFile, info.writerFile, linesRead);
    endRead(info.id);
  }
  return args; 
}

int write(int id, int currentNum, FILE *writerFile){
  int i;
  for(i = currentNum; i < currentNum+5; i++){
    fprintf(writerFile, "<W%d, %d>\n", id, i);
  }
  currentNum = currentNum+5;
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
    sem_post(&okToWrite);
    activeWriters++;
    waitingWriters--;
  }
  else{
    int i;
    for(i = 0; i < waitingReaders; i++){
      sem_post(&okToRead);
      activeReaders++;
      waitingReaders--;
    }
  }
  sem_post(&mutex);
}

void* writer(void *args){
  ThreadInfo info = *((ThreadInfo*)args);
  int currentNum = 1;
  
  while(currentNum < 100){
    startWrite(info.id);
    currentNum = write(info.id, currentNum, info.writerFile);
    endWrite(info.id); 
  }  
  return args;
}


int main(int argc, char **argv){
  if(argc != 3){
    printf("usage: \"%s [numReaders] [numWriters]\"\n", argv[0]);
    exit(1);
  }
  int numReaders = atoi(argv[1]); 
  int numWriters = atoi(argv[2]);

  FILE *writerFile = fopen("writer_output_file", "w");

  pthread_t readers[numReaders];
  pthread_t writers[numWriters];
  
  sem_init(&okToRead, 0, 0);
  sem_init(&okToWrite, 0, 0);
  sem_init(&mutex, 0, 1);
  
  int i;
  ThreadInfo idsReaders[numReaders];  
  //Dispatch reader threads
  for(i = 0; i < numReaders; i++){
    idsReaders[i].writerFile = writerFile;
    idsReaders[i].id = i;
    idsReaders[i].totalLines = numWriters * 100;
    pthread_create(readers + i, NULL, reader, (void*)&idsReaders[i]);
  }
  
  ThreadInfo idsWriters[numReaders];
  //Dispatch writer threads
  for(i = 0; i < numWriters; i++){
    idsWriters[i].writerFile = writerFile;
    idsWriters[i].id = i;
    idsWriters[i].totalLines = numWriters * 100;
    pthread_create(writers + i, NULL, writer, (void*)&idsWriters[i]);
  }

  void *returnStatus;
  for(i = 0; i < numWriters; i++){
    pthread_join(writers[i], &returnStatus);
  }
  for(i = 0; i < numReaders; i++){
    pthread_join(readers[i], &returnStatus);
  }
  fclose(writerFile);
  //*/
  return 0;
}



