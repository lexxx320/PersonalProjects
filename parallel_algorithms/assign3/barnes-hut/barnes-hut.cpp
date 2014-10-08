#include <stdio.h>
#include <stdlib.h>
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#include <time.h>
#include <sys/time.h>
#include <string.h>
#include <math.h>

#define THETA 0.5
#define G 6.67384e10-11

int nParticles;

typedef struct particle_t{
  float xPos;
  float yPos;
  float mass;
} particle;

typedef struct quadTree_t{
  float mass;                                 //total mass of the cube
  float x; float y;                           //coordinates of the center
  int n;                                      //number of particles                         
  struct quadTree_t * c1;                     //4 subcubes
  struct quadTree_t * c2;
  struct quadTree_t * c3;
  struct quadTree_t * c4; 
} * quadTree;

quadTree mkEmptyNode(){
  quadTree q = (quadTree) malloc(sizeof(struct quadTree_t));
  q->mass = 0; q-> x = 0; q -> y = 0;
  q-> n = 0; q->c1 = NULL;
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
    iter++;
  }
  return data;
} 

quadTree insert(quadTree t, particle p, float x1, float x2, float y1, float y2){
  if(t==NULL){
    quadTree q = mkEmptyNode();
    q->mass = p.mass;
    q->x = p.xPos * p.mass;
    q->y = p.yPos * p.mass;
    q->n = 1;
    return q;
  }
  float xMid = (x2-x1)/2; float yMid = (y2-y1)/2;
  if(p.xPos <= x1+xMid){
    if(p.yPos <= y1+yMid){    //Q1
      t->c1 = insert(t->c1, p, x1, x1+xMid, y1, y1+yMid);
      t->x += p.xPos * p.mass;
      t->y += p.yPos * p.mass;
      t->mass += p.mass;
      t->n++;
      return t;
    }else{                    //Q2
      t->c2 = insert(t->c2, p, x1+xMid, x2, y1, y1+yMid);
      t->n++;
      t->x += p.xPos * p.mass;
      t->y += p.yPos * p.mass;
      t->mass += p.mass;
      return t;
    }
  }else{
    if(p.yPos <= y1+yMid){    //Q3
      t->c3 = insert(t->c3, p, x1, x1+xMid, y1+yMid, y2);
      t->n++;
      t->x += p.xPos * p.mass;
      t->y += p.yPos * p.mass;
      t->mass += p.mass;
      return t;
    }else{                    //Q4
      t->c4 = insert(t->c4, p, x1+xMid, x2, y1+yMid, y2);
      t->n++;
      t->x += p.xPos * p.mass;
      t->y += p.yPos * p.mass;
      t->mass += p.mass;
      return t;
    }
  }
}

//F = GMm/R2
float computeForce(particle p1, particle p2){
  float Rsquared = sqrt(pow(p1.xPos - p2.xPos, 2) + pow(p1.yPos - p2.yPos, 2));
  return G * p1.mass * p2.mass * Rsquared; 
} 

//Compute force exerted on p
float computeMass(quadTree t, particle p, float x1, float x2, float y1, float y2){
  if(t == NULL){
    return 0;
  }
  if(t->n == 1){
    float x = t->x / t->mass;
    float y = t->y / t->mass;
    particle p2 = {x, y, t->mass}; 
    return computeForce(p, p2);
  }
  float s = x2 - x1;//width of the region
  float xcm = t->x / t->mass; 
  float ycm = t->y / t->mass;
  float d = sqrt(pow(p.xPos - xcm, 2) + pow(p.yPos - ycm, 2));
  if((s/d) > THETA){//recurse
    float f1 = computeMass(t->c1, p, x1, x1+s, y1, y1+s);
    float f2 = computeMass(t->c2, p, x1+s, x2, y1, y1+s); 
    float f3 = computeMass(t->c3, p, x1, x1+s, y1+s, y2);
    float f4 = computeMass(t->c4, p, x1+s, x2, y1+s, y2); 
    return f1+f2+f3+f4;
  }else{
    float x = t->x / t->mass;
    float y = t->y / t->mass;
    particle p2 = {x, y, t->mass}; 
    return computeForce(p, p2);
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
    current.x2 = data[i].xPos > current.x2 ? data[i].xPos : current.x2;
    current.y2 = data[i].yPos > current.y2 ? data[i].yPos : current.y2;
  }
  if(current.x2-current.x1 > current.y2-current.y1){//make the box square
    float diff = (current.x2-current.x1) - (current.y2-current.y1);
    current.y2 += diff;
  }else{
    float diff = (current.y2-current.y1) - (current.x2-current.x1);
    current.x2 += diff;
  }
  return current;
}

void printTree(quadTree t){
  if(t == NULL){
    return;
  }
  printf("(%f, %f, %f, nparticles = %d)\n", t->x / t->mass, t->y / t->mass, t->mass, t->n);
  printTree(t->c1);
  printTree(t->c2);
  printTree(t->c3);
  printTree(t->c4);
}

float * barnes_hut(particle * data, coords c){
  quadTree t = NULL;
  for(int i = 0; i < nParticles; i++){
    t = insert(t, data[i], c.x1, c.x2, c.y1, c.y2);
  }
  //printTree(t);
  float * res = (float *)malloc(sizeof(float) * nParticles);
  for(int i = 0; i < nParticles; i++){
    res[i] = computeMass(t, data[i], c.x1, c.x2, c.y1, c.y2);
  } 
  return res;
}

int main(){
  particle * data = readData("small_data.txt");
  coords c = mkInitBox(data);
  float * res = barnes_hut(data, c);
  for(int i = 0; i < nParticles; i++){
    printf("Force exerted on particle %d is %f\n", i, res[i]);
  }
}











