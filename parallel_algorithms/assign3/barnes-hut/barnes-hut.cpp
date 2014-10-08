#include <stdio.h>
#include <stdlib.h>
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#include <time.h>
#include <sys/time.h>
#include <string.h>

#define THETA 0.5

int nParticles;

typedef struct particle_t{
  float xPos;
  float yPos;
  float mass;
  float xVel;
  float yVel;
} particle;

typedef struct quadTree_t{
  float mass;                                 //total mass of the cube
  float x; float y;                           //coordinates of the center
  float mx; float my;                         //center of mass
  int n;                                      //number of particles
  struct quadTree_t * c1;                     //4 subcubes
  struct quadTree_t * c2;
  struct quadTree_t * c3;
  struct quadTree_t * c4; 
} * quadTree;

quadTree mkEmptyNode(){
  quadTree q = (quadTree) malloc(sizeof(struct quadTree_t));
  q->mass = 0; q-> x = 0; q -> y = 0;
  q->mx = 0; q->my = 0; q-> n = 0; q->c1 = NULL;
  q->c2 = NULL; q->c3 = NULL; q->c4 = NULL;
  return q;
}

particle * readData(const char * filename){
  FILE * fp = fopen(filename, "r");
  fscanf(fp, "%d", &nParticles);

  particle * data = (particle*)malloc(sizeof(struct quadTree_t));
  
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

quadTree insert(quadTree t, particle p, float x1, float x2, float y1, float y2){
  if(t==NULL){
    quadTree q = mkEmptyNode();
    q->mass = p.mass;
    q->x = p.xPos;
    q->y = p.yPos;
    q->n = 1;
    return q;
  }
  float xMid = (x2-x1)/2; float yMid = (y2-y1)/2;
  if(p.xPos <= x1+xMid){
    if(p.yPos <= y1+yMid){    //Q1
      t->c1 = insert(t->c1, p, x1, x1+xMid, y1, y1+yMid);
      t->n++;
      return t;
    }else{                    //Q2
      t->c2 = insert(t->c2, p, x1+xMid, x2, y1, y1+yMid);
      t->n++;
      return t;
    }
  }else{
    if(p.yPos <= y1+yMid){    //Q3
      t->c3 = insert(t->c3, p, x1, x1+xMid, y1+yMid, y2);
      t->n++;
      return t;
    }else{                    //Q4
      t->c4 = insert(t->c4, p, x1+xMid, x2, y1+yMid, y2);
      t->n++;
      return t;
    }
  }
}

typedef struct coords_t{
  float x1; float x2; float y1; float y2;
} coords;

coords mkInitBox(particle * data){
  coords current;
  current.x1 = 0; current.x2 = 0; current.y1 = 0; current.y2 = 0;
  cilk_for(int i = 0; i < nParticles; i++){
    current.x1 = data[i].xPos < current.x1 ? data[i].xPos : current.x1;
    current.y1 = data[i].yPos < current.y1 ? data[i].yPos : current.y1;
    current.x2 = data[i].xPos < current.x2 ? data[i].xPos : current.x2;
    current.y2 = data[i].yPos < current.y2 ? data[i].yPos : current.y2;
  }
  return current;
}

quadTree barnes_hut(particle * data, coords c){
  quadTree t = NULL;
  for(int i = 0; i < nParticles; i++){
    t = insert(t, data[i], c.x1, c.x2, c.y1, c.y2);
  }
  
  return t;
}

void printTree(quadTree t){
  if(t==NULL){
    return;
  }
  printf("(%f, %f, %f)\n", t->x, t->y, t->mass);
  printTree(t->c1);
  printTree(t->c2);
  printTree(t->c3);
  printTree(t->c4);
}

int main(){
  particle * data = readData("small_data.txt");
  coords c = mkInitBox(data);
  quadTree t = barnes_hut(data, c);
  printTree(t);
}











