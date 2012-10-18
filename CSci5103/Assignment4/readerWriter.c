#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <semaphore.h>
#include <string.h>

sem_t readersMutex;
sem_t writersMutex;
sem_t mutex;
int numReading;
int waitingToRead;
int waitingToWrite;
int numWriting;

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
      return numLines;
    }
    fprintf(outputFile, "%s", line);
    numLines++;
  }
  return itemsRead;
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
    sem_wait(&mutex);
    if(numWriting > 0){               //someone is writing, so wait
      printf("reader%d waiting to read.\n", info.id);
      sem_post(&mutex);                
      sem_wait(&readersMutex);
      sem_wait(&mutex);                
      printf("reader%d starting to read.\n", info.id);
      numReading++;
      sem_post(&mutex);
      linesRead = read(readerFile, info.writerFile, linesRead);
    }  
    else if(numReading > 0){          //ok to read
      numReading++;
      sem_post(&mutex);
      printf("reader%d starting to read.\n", info.id);
      linesRead = read(readerFile, info.writerFile, linesRead);
    }
    else{                              //ok to read   
      numReading++;
      sem_post(&mutex);
      printf("reader%d starting to read.\n", info.id);
      linesRead = read(readerFile, info.writerFile, linesRead);
    }
    printf("reader%d done reading.\n", info.id);
    sem_wait(&mutex);
    if(numReading == 0 && waitingToWrite > 0){
      sem_post(&writersMutex);
    }
    sem_post(&mutex);
  }
  return args; 
}

int write(int id, int currentNum){
  FILE *writerFile = fopen("writer_output_file", "w+");
  int i;
  for(i = currentNum; i < currentNum+5; i++){
    fprintf(writerFile, "<W%d, %d>\n", id, i);
    currentNum++;
  }
  return currentNum;
}

void* writer(void *args){
  ThreadInfo info = *((ThreadInfo*)args);
  int currentNum = 1;
  
  while(currentNum < 100){
    sem_wait(&mutex);
    if(numWriting > 0){  //Someone else is writing
      sem_post(&mutex);
      printf("writer%d waiting to write.\n", info.id);
      sem_wait(&writersMutex);
      sem_wait(&mutex);
      numWriting++;
      sem_post(&mutex);
      printf("writer%d starting to write.\n", info.id);
      currentNum = write(info.id, currentNum);
    }
    else if(numReading > 0){
      sem_post(&mutex);
      printf("writer%d waiting to write.\n", info.id);
      sem_wait(&writersMutex);
      sem_wait(&mutex);
      numWriting++;
      sem_post(&mutex);
      printf("writer%d starting to write.\n", info.id);
      currentNum = write(info.id, currentNum);
    }
    else{
      numWriting++;
      printf("writer%d starting to write.\n", info.id);
      currentNum = write(info.id, currentNum);
    }
    printf("writer%d done writing.\n", info.id);
    numWriting--;
    if(waitingToWrite > 0){
      sem_post(&writersMutex);
    }
    else if(waitingToRead > 0){
      int i;
      for(i = 0; i < waitingToRead; i++){
        sem_post(&readersMutex);
      }
    }
  }
  return args;
}

void test(void *args){
  int x = *((int*)args);
  printf("x = %d\n", x);
}

int main(int argc, char **argv){
  if(argc != 3){
    printf("usage: \"%s [numReaders] [numWriters]\"\n", argv[0]);
    exit(1);
  }
  int numReaders = atoi(argv[1]); 
  int numWriters = atoi(argv[2]);

  FILE *writerFile = fopen("writer_output_file", "w");
  fclose(writerFile);

  pthread_t readers[numReaders];
  pthread_t writers[numWriters];
  
  sem_init(&readersMutex, 0, 1);
  sem_init(&writersMutex, 0, 0);
  sem_init(&mutex, 1, 0);
  
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
  //*/
  return 0;
}



