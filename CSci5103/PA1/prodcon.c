#include "prodcon.h"

#define SHMKEY 2041
#define SHMKEY2 2042
struct sharedMemStruct{
  char * data;
  int * numChars;
};

void sigHandler(int n){
  
}

void producerWriteText(char * filePath, pid_t childPID){
  //open the file and check that it exists
  FILE *inputFile = fopen(filePath, "r");
  if(inputFile == NULL){
    printf("input file, \"%s\" does not exist, exiting...\n", filePath);
    exit(1);
  }
  
  int sharedMemId, charsReadId;
  sharedMemId = shmget(SHMKEY, 1024, 0666 | IPC_CREAT);
  charsReadId = shmget(SHMKEY2, 4, 0666 | IPC_CREAT);
  if(sharedMemId == -1 || charsReadId == -1){
    perror("Error creating shared memory.\n");
    exit(1);
  }
  struct sharedMemStruct sharedMem;
  sharedMem.numChars = shmat(charsReadId, 0, 0);
  sharedMem.data = shmat(sharedMemId, 0, 0);
  if(sharedMem.data == (char*) -1 || sharedMem.numChars == (int*) -1){
    perror("Error attaching shared memory.\n");
    exit(1);
  }
  
  char *currentBlock = (char*)malloc(sizeof(char) * 1024);
  int charsRead = fread(currentBlock, 1, 1024, inputFile);
  int j = 0;
  while(charsRead > 0){
    int i;
    
    for(i = 0; i < charsRead; i++){
      sharedMem.data[i] = currentBlock[i];
    }
    *(sharedMem.numChars) = (int)charsRead;
    printf("sending signal SIGUSR1\n");
    
    sleep(1);
    
    kill(childPID, SIGUSR1);
    printf("waiting on signal SIGUSR2\n");
    sigpause(SIGUSR2);
    j = j+1;
    charsRead = fread(currentBlock, 1, 1024, inputFile);
  }
  
  *(sharedMem.numChars) = -1;
  kill(childPID, SIGUSR1);
  shmdt((void*) sharedMem.data);
  free(currentBlock);
}

void consumerReadText(){
  FILE *outputFile = fopen("output", "w");
  int sharedMemId, charsReadId;
  sharedMemId = shmget(SHMKEY, 1024, 0666);
  charsReadId = shmget(SHMKEY2, 4, 0666);
  if(sharedMemId == -1 || charsReadId == -1){
    perror("Error getting shared memory to consumer.\n");
    exit(0);
  }
  
  struct sharedMemStruct sharedMem;
  sharedMem.data = shmat(sharedMemId, 0, 0);
  sharedMem.numChars = shmat(charsReadId, 0, 0);
  if(sharedMem.data == (char*) -1 || sharedMem.numChars == (int*) -1){
    perror("Error attaching shared memory to consumer.\n");
    exit(1);
  }

  while(*sharedMem.numChars != -1){
    printf("waiting on signal SIGUSR1\n");
    sigpause(SIGUSR1);
    
    //printf("consumer recieved = \"%s\"\n", sharedMem.data);
    printf("consumer recieved numChars = \"%d\"\n", *sharedMem.numChars);
    
    //fprintf(outputFile, "%s", sharedMem.data);
    fwrite(sharedMem.data, sizeof(char) * 1, sizeof(char) * (*sharedMem.numChars), outputFile);
    
    printf("sending signal SIGUSR2\n");
    sleep(1);
    kill(getppid(), SIGUSR2);
  }
  fclose(outputFile);
  shmdt((void*) sharedMem.data);
  shmctl(sharedMemId, IPC_RMID, NULL);
  printf("exiting...\n");
  exit(0);
  
}

int main(int argc, char ** argv){
  if(argc != 2){
    printf("user must input only the filename to be transfered.\n");
    exit(1);
  }
  
  char* filePath = argv[1];
  int status;
  signal(SIGUSR1, sigHandler);
  signal(SIGUSR2, sigHandler);
  pid_t childPid = fork(); //fork a child process
  
  if(childPid == 0){ //child process goes to read function
    consumerReadText();
  }
  else if(childPid > 0){ //parent process
    producerWriteText(filePath, childPid);
    wait(&status);
  }
  else{
    printf("fork error, exiting...\n");
    exit(1);
  }
 return 1;
}
