#include <stdio.h>
#include <stdlib.h>
#include <signal.h>

void sigHandler(int n){
  switch(n){
    case SIGUSR1:
      printf("handling SIGUSR1\n");
    case SIGUSR2:
      printf("handling SIGUSR2\n");
    default:
      printf("signal not recognized\n");
  }
}

void parent(pid_t pid, sigset_t sigs){
  //sleep(1);
  int signalNum;
  printf("sending signal SIGUSR1\n");
  kill(pid, SIGUSR1);

  sigwait(&sigs, &signalNum);
  printf("caught signal from child\n");
  sleep(1);
  kill(pid, SIGUSR1);
  
}

void child(sigset_t sigs){
  sleep(1);
  int signalNum;
  sigwait(&sigs, &signalNum);
  sigaddset(&sigs, SIGUSR1);
  printf("caught signal SIGUSR1 from parent\n");
  sleep(1);
  kill(getppid(), SIGUSR2);
  sigwait(&sigs, &signalNum);
  printf("caught signal SIGUSR1 from parent\n");
}



main(int argc, char **argv){
  sigset_t sigs;
  sigemptyset(&sigs);
  sigaddset(&sigs, SIGUSR1);
  sigaddset(&sigs, SIGUSR2);
  
  pid_t pid = fork();
  if(pid == 0){
    child(sigs);
  }
  else if(pid > 0){
    parent(pid, sigs);
  }
  else{
    perror("fork error\n");
    exit(1);
  }
}






