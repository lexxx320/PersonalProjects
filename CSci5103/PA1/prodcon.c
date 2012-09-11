#include "prodcon.h"

#define SHMKEY 2041
struct sharedMemStruct{
  char * data;
  int * numChars;
};

void sigHandler(int sigNum){
  switch(sigNum){
    case SIGUSR1:
      printf("handling SIGUSR1\n");
      break;
    case SIGUSR2:
      printf("handling SIGUSR2\n");
      break;
    default:
      printf("could not recognize signal\n");
  }
  
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
  charsReadId = shmget(SHMKEY, 4, 0666 | IPC_CREAT);
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
  //printf("chars read = %d\n", charsRead);
  
  while(charsRead > 0){
    int i;
    
    printf("waiting on signal SIGUSR2\n");
    
    for(i = 0; i < charsRead; i++){
      sharedMem.data[i] = currentBlock[i];
    }
    *(sharedMem.numChars) = charsRead;
    printf("sending signal SIGUSR1\n");
    kill(childPID, SIGUSR1);
    sigpause(SIGUSR2);
    
    charsRead = fread(currentBlock, 1, 1024, inputFile); 
   
  }
  
  free(currentBlock);
}

void consumerReadText(){

  printf("waiting on signal SIGUSR1\n");
  sigpause(SIGUSR1);
  printf("sending signal SIGUSR2\n");
  kill(getppid(), SIGUSR2);
  printf("exiting...\n");
  exit(0);
  
}

int main(int argc, char ** argv){
  if(argc != 2){
    printf("user must input only the filename to be transfered.\n");
    exit(1);
  } 

  signal(SIGUSR1, sigHandler);
  signal(SIGUSR2, sigHandler);
  char* filePath = argv[1];
  
  pid_t childPid = fork();  //fork a child process
  
  if(childPid == 0){  //child process goes to read function
    consumerReadText();
  }
  else if(childPid > 0){ //parent process
    producerWriteText(filePath, childPid);
  }
  else{
    printf("fork error, exiting...\n");
    exit(1);
  }
 return 1;
}



