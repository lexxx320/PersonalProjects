#include "prodcon.h"

#define SHMKEY 2041
#define SHMKEY2 2042
struct sharedMemStruct{
  char * data;
  int * numChars;
};

void parentHandler(int sig){
  printf("Parent caught signal\n");
}
void childHandler(int sig){
  printf("Child caught signal\n");
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
  //printf("chars read = %d\n", charsRead);
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
    //sigpause(SIGUSR2);
    pause();
    j = j+1;
    charsRead = fread(currentBlock, 1, 1024, inputFile);
  }
  
  *(sharedMem.numChars) = -1;
  kill(childPID, SIGUSR1);
  
  free(currentBlock);
  free(sharedMem.data);
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
  int i = 0;
  while(*sharedMem.numChars != -1){
    printf("waiting on signal SIGUSR1\n");
    
    
    //sigpause(SIGUSR1);
    pause();
    
    printf("consumer recieved = \"%s\"\n", sharedMem.data);
    printf("consumer recieved numChars = \"%d\"\n", *sharedMem.numChars);
    
    printf("sending signal SIGUSR2\n");
    sleep(1);
    kill(getppid(), SIGUSR2);
    ++i;
    if(i >= 500){
      exit(0);
    }
  }
  printf("exiting...\n");
  exit(0);
  
}

int main(int argc, char ** argv){
  if(argc != 2){
    printf("user must input only the filename to be transfered.\n");
    exit(1);
  }
  
  static struct sigaction pAction, cAction;
  pAction.sa_handler = parentHandler;
  sigaction(SIGUSR1, &pAction, NULL);
  char* filePath = argv[1];
  int status;
  
  pid_t childPid = fork(); //fork a child process
  
  if(childPid == 0){ //child process goes to read function
    cAction.sa_handler = childHandler;
    sigaction(SIGUSR1, &cAction, NULL);
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
