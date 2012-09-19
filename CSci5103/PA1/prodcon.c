#include "prodcon.h"

struct sharedMemStruct{
  char * data;
  int * numChars;
};

void sigHandler(int n){
  signal(n, sigHandler);
}
void producerWriteText(char * filePath, pid_t childPID, char* data, int* numCharsPointer){
  
  //open the file and check that it exists
  FILE *inputFile = fopen(filePath, "r");
  if(inputFile == NULL){
    printf("input file, \"%s\" does not exist, exiting...\n", filePath);
    exit(1);
  }
  
  struct sharedMemStruct sharedMem;
  sharedMem.numChars = numCharsPointer;
  sharedMem.data = data;
  
  char *currentBlock = (char*)malloc(sizeof(char) * 1024);
  int charsRead = fread(currentBlock, 1, 1024, inputFile);
  int j = 0;
  //-----Read in chars and write to Shared memory------
  while(charsRead > 0){
    int i;

    //Write to shared memory
    for(i = 0; i < charsRead; i++){
      sharedMem.data[i] = currentBlock[i];
    }
    *(sharedMem.numChars) = (int)charsRead;
    printf("writing %d chars to shared memory\n", charsRead);
    
    kill(childPID, SIGUSR1); //send SIGUSR1
    sigpause(SIGUSR2); //Wait for SIGUSR2

    j = j+1;
    charsRead = fread(currentBlock, 1, 1024, inputFile);
  }
  
  *(sharedMem.numChars) = -1;
  kill(childPID, SIGUSR1);
  shmdt((void*) sharedMem.data);
  free(currentBlock);
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
  
  key_t key = 4455;
  key_t key2 = 4457;
  int size = 1024;
  int flag = 0;
  flag = flag | IPC_CREAT;
  flag = flag| 00400 |00200 |00040 | 00020| 00004 | 00002 ;
  int shmem_id;
  char* shmem_ptr;
  
  shmem_id = shmget(key, size, flag);
  if(shmem_id == -1){
    perror("shmget failed data memory\n");
    exit(1);
  } 
  shmem_ptr = shmat(shmem_id, (void*) NULL, flag);
  if(shmem_ptr == (void*) -1){
    perror("shmat failed for data memory\n");
    exit(1);
  }
  
  int shmem_id2 = shmget(key2, 4, flag);
  if(shmem_id2 == -1){
    perror("shmget failed for numChars memory\n");
    exit(1);
  } 
  int *shmem_ptr2 = shmat(shmem_id2, (void*) NULL, flag);
  if(shmem_ptr2 == (void*) -1){
    perror("shmat failed for numChars memory\n");
    exit(1);
  }
  
  sigset_t sigs;
  sigemptyset(&sigs);
  sigaddset(&sigs, SIGUSR1);
  
  
  pid_t childPid = fork(); //fork a child process
  
  if(childPid == 0){ //child process goes to read function
    char keystr1[10];
    char keystr2[10];
    char pidstr[10];
    
    sprintf(pidstr, "%d", getppid());
    sprintf(keystr1, "%d", key);
    sprintf(keystr2, "%d", key2);
    
    execl("./child", "child", keystr1, keystr2, pidstr, NULL);
    
    //consumerReadText(key, key2);
  }
  else if(childPid > 0){ //parent process
    sigpause(SIGUSR2);
    producerWriteText(filePath, childPid, shmem_ptr, shmem_ptr2);
    wait(&status);
  }
  else{
    printf("fork error, exiting...\n");
    exit(1);
  }
 return 1;
}
