#include <stdio.h>
#include <stdlib.h>
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#include <time.h>
#include <sys/time.h>
#include <string.h>
#include <math.h>

#define THETA 0.5

#define PAR false

#if PAR == true
#define CSPAWN cilk_spawn
#define CSYNC cilk_sync;
#else 
#define CSPAWN 
#define CSYNC
#endif

int nParticles;

float epsilon = 0.0;
float eClose = 0.01;

typedef struct particle_t{
  float xPos;
  float yPos;
  float mass;
} particle;

typedef struct quadTree_t{
  float mass;                                 //total mass of the cube
  float x; float y;                           //coordinates of the center
  int n;                                      //number of particles                        
  struct quadTree_t * q1;                     //4 subcubes
  struct quadTree_t * q2;
  struct quadTree_t * q3;
  struct quadTree_t * q4; 
} * quadTree;

typedef struct force_t{
  float vx; float vy;
} force; 

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
    iter++;
  }
  return data;
} 

quadTree mkEmptyNode(){
  quadTree q = (quadTree) malloc(sizeof(struct quadTree_t));
  q->mass = 0; q-> x = 0; q -> y = 0;
  q-> n = 0; q->q1 = NULL; 
  q->q2 = NULL; q->q3 = NULL; q->q4 = NULL;
  return q;
}

bool inQ(particle p, float x1, float x2, float y1, float y2){
  return p.xPos > x1 && p.xPos <= x2 && p.yPos > y1 && p.yPos <= y2;
}

particle * getParts(particle * ps, float x1, float x2, float y1, float y2, int n, int * finalSize){
  int size = 0;
  for(int i = 0; i < n; i++){
    if(inQ(ps[i], x1, x2, y1, y2))
      size++;
  }
  *finalSize = size;
  particle * res = (particle*)malloc(sizeof(particle) * size);
  int count = 0;
  for(int i = 0; i < n; i++){
    if(inQ(ps[i], x1, x2, y1, y2)){
      res[count] = ps[i];
      count++;
    }
  }
  return res;
}

void computeCenter(quadTree t, particle * ps, int n){
  float mx = 0; float my = 0; float m = 0;
  for(int i = 0; i < n; i++){
    m += ps[i].mass;
    mx += ps[i].mass * ps[i].xPos;
    my += ps[i].mass * ps[i].yPos;
  }
  t->mass = m;
  t->x = mx / m;
  t->y = my / m;
}

quadTree buildTree(particle * ps, float x1, float x2, float y1, float y2, int n){
  if(n <= 1){
    quadTree t = mkEmptyNode();
    computeCenter(t, ps, n);
    return t;
  }
  int n1, n2, n3, n4;
  float xMid = (x2-x1)/2; float yMid = (y2-y1)/2;
  particle * p1 = CSPAWN getParts(ps, x1, x1+xMid, y1, y1+yMid, n, &n1);
  particle * p2 = CSPAWN getParts(ps, x1+xMid, x2, y1, y1+yMid, n, &n2);
  particle * p3 = CSPAWN getParts(ps, x1, x1+xMid, y1+yMid, y2, n, &n3);
  particle * p4 = CSPAWN getParts(ps, x1+xMid, x2, y1+yMid, y2, n, &n4);

  CSYNC
  
  quadTree q1 = CSPAWN buildTree(p1, x1, x1+xMid, y1, y1+yMid, n1);
  quadTree q2 = CSPAWN buildTree(p2, x1+xMid, x2, y1, y1+yMid, n2);
  quadTree q3 = CSPAWN buildTree(p3, x1, x1+xMid, y1+yMid, y2, n3);
  quadTree q4 = CSPAWN buildTree(p4, x1+xMid, x2, y1+yMid, y2, n4);

  CSYNC
  
  quadTree result = mkEmptyNode();
  result->q1 = q1; 
  result->q2 = q2; 
  result->q3 = q3; 
  result->q4 = q4;
  computeCenter(result, ps, n);
  return result;
}

force computeForce(particle p1, particle p2){
  float dx = p1.xPos - p2.xPos;
  float dy = p1.yPos - p2.yPos;
  float rsqr = dx * dx + dy * dy;
  float r = sqrt(rsqr);
  float aabs = p2.mass / rsqr;
  force f = {aabs * dx / r, aabs * dy / r};
  return f;
}

force addForces(force f1, force f2){
  force f = {f1.vx + f2.vx, f1.vy + f2.vy};
  return f;
}

/*
fun is_close (x1, y1, m) (x2, y2) =  
  sq (x1 - x2) + sq (y1 - y2) < eClose
*/
bool isClose(particle p1, particle p2){
  float xd = p1.xPos - p2.xPos;
  float yd = p1.yPos - p2.yPos;
  return (xd*xd + yd*yd) < eClose;
}

//Compute force exerted on p
force computeMass(quadTree t, particle p, float x1, float x2, float y1, float y2){
  if(t == NULL){//empty leaf
    force f = {0,0};
    return f;
  }
  if(t->n == 1){//region only contains a single body
    if(t->x == p.xPos && t->y == p.yPos){//don't compute force against the same particles
      force f = {0,0};
      return f;
    }
    particle p2 = {t->x, t->y, t->mass};
    return computeForce(p, p2);
  }
  float s = x2 - x1;//width of the region
  float xcm = t->x / t->mass; 
  float ycm = t->y / t->mass;
  float d = sqrt(pow(p.xPos - xcm, 2) + pow(p.yPos - ycm, 2));
  particle p2 = {t->x, t->y, t->mass};
  bool ic = !isClose(p, p2);
  bool temp = (s/d) > THETA;
  if((s/d) > THETA){//recurse
    force f1 = CSPAWN computeMass(t->q1, p, x1, x1+s, y1, y1+s);
    force f2 = CSPAWN computeMass(t->q2, p, x1+s, x2, y1, y1+s); 
    force f3 = CSPAWN computeMass(t->q3, p, x1, x1+s, y1+s, y2);
    force f4 = CSPAWN computeMass(t->q4, p, x1+s, x2, y1+s, y2); 
    CSYNC
    return addForces(f1, addForces(f2, addForces(f3, f4)));
  }else{//treat group as a single body
    float x = t->x / t->mass;
    float y = t->y / t->mass;
    particle p2 = {t->x, t->y, t->mass}; 
    return computeForce(p, p2);
  }
}
typedef struct coords_t{
  float x1; float x2; float y1; float y2;
} coords;

//Determine the dimensions of the original box
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
  printf("--------------Q1--------------\n");
  printTree(t->q1);
  printf("--------------Q2--------------\n");
  printTree(t->q2);
  printf("--------------Q3--------------\n");
  printTree(t->q3);
  printf("--------------Q4--------------\n");
  printTree(t->q4);
  printf("------------------------------\n");
}

force * barnes_hut(particle * data, coords c){
  quadTree t = buildTree(data, c.x1, c.x2, c.y1, c.y2, nParticles);
  //printTree(t2);
  
  force * res = (force *)malloc(sizeof(force) * nParticles);
  for(int i = 0; i < nParticles; i++){
    res[i] = computeMass(t, data[i], c.x1, c.x2, c.y1, c.y2);
  }
  return res;
}

int main(int argc, char ** argv){
  particle * data;
  if(argc > 1){
    data = readData(argv[1]);
  }else{
    data = readData("small_data.txt");
  }
  coords c = mkInitBox(data);
  force * res = barnes_hut(data, c);
  if(nParticles <= 10){
    for(int i = 0; i < nParticles; i++){
      printf("Force exerted on particle %d is (%.15f, %.15f)\n", i, res[i].vx, res[i].vy);
    }
  }
}











