#include <stdio.h>
#include <stdlib.h>
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#include <time.h>
#include <sys/time.h>
#include <string.h>

int nParticles;

typedef struct particle_t{
  float xPos;
  float yPos;
  float mass;
  float xVel;
  float yVel;
} particle;

typedef struct coords_t{
  float x1; float x2; float y1; float y2;
} coords;

particle * readData(const char * filename){
  FILE * fp = fopen(filename, "r");
  fscanf(fp, "%d", &nParticles);

  particle * data = (particle*)malloc(sizeof(particle) * nParticles);
  
  float i1, i2, i3, i4, i5;
  int iter = 0;
  while(fscanf(fp, "%f %f %f %f %f", &i1, &i2, &i3, &i4, &i5) == 5){
    data[iter].xPos = i1;
    data[iter].yPos = i2;
    data[iter].mass = i3;
    data[iter].xVel = i4;
    data[iter].yVel = i5;
    iter++;
  } 
  
  return data;
} 


coords mkInitBox(particle * data){
  coords current;
  current.x1 = 0; current.x2 = 0; current.y1 = 0; current.y2 = 0;
  cilk_for(int i = 0; i < nParticles; i++){
    current.x1 = data[i].x1 < current.x1 ? data[i].x1 : current.x1;
    current.y1 = data[i].y1 < current.y1 ? data[i].y1 : current.y1;
    current.x2 = data[i].x2 < current.x2 ? data[i].x2 : current.x2;
    current.y2 = data[i].y2 < current.y2 ? data[i].y2 : current.y2;
  }

  return current;
}

int main(){
  particle * data = readData("bodies.txt");
  
  
}











