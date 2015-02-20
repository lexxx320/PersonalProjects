//
//  Rasterizer.cpp
//
//
//  Created by Joe Geigel on 11/30/11.
//  Copyright 2011 Rochester Institute of Technology. All rights reserved.
//



#include "Rasterizer.h"
#include "simpleCanvas.h"
#include <list>

using namespace std;

typedef struct{
    int y;
    int x;
    int dx;
    int dy;
    int sum;
} bucket;

/**
 *
 * Simple class that performs rasterization algorithms
 *
 */


/**
 * Constructor
 *
 * @param n - number of scanlines
 *
 */
Rasterizer::Rasterizer (int n) : n_scanlines (n)
{
}


list<bucket*> filter(list <bucket*> ael, int y){
    for (list<bucket *>::iterator it = ael.begin(); it != ael.end(); it++){
        bucket * b = *it;
        if(b-> y == y){
            ael.erase(it);
        }
    }
    return ael;
}

void updateXs(list <bucket*>ael){
    for (list<bucket *>::iterator it = ael.begin(); it != ael.end(); it++){
        bucket * b = *it;
        int xInc = (b->dx + b->sum) / b->dy;
        b->sum = (b->dx + b->sum) % b->dy;
        b->x += xInc;
    }
}

bool lineLT(bucket * b1, bucket * b2){
    if(b1->x < b2->x){
        return true;
    }else if (b1->x == b2->x){
        double s1 = (double)b1->dx / (double) b1->dy;
        double s2 = (double)b2->dx / (double) b2->dy;
        return s1 < s2;
    }else{
        return false;
    }
}

list<bucket*> insert(list<bucket*> yBucket, list<bucket*> ael){
    for(list<bucket *>::iterator it = yBucket.begin(); it != yBucket.end(); it++){
        bucket * yb = *it;
        if(yb->dy == 0)
            continue;
        bool inserted = false;
        for(list<bucket *>::iterator it2 = ael.begin(); it2 != ael.end(); it2++){
            if(lineLT(yb, *it2)){
                ael.insert(it2, yb);
                inserted = true;
                break;
            }
        }
        if(!inserted){
            ael.push_back(yb);
        }
    }
    return ael;
}


/**
 * Draw a filled polygon in the simpleCanvas C.
 *
 * The polygon has n distinct vertices.  The coordinates of the vertices
 * making up the polygon are stored in the x and y arrays.  The ith
 * vertex will have coordinate (x[i],y[i]).
 *
 * You are to add the implementation here using only calls
 * to C.setPixel()
 */
void Rasterizer::drawPolygon(int n, int x[], int y[], simpleCanvas &C){
    list <bucket *> * el = new list<bucket *>[n_scanlines]; //edge table
    int j;

    //Build edge table
    for(int i = 0; i < n; i++){
        j = (i + 1) % n;
        bucket * b = (bucket*)malloc(sizeof(bucket));
        if(y[i] < y[j]){
            b->y = y[j];
            b->x = x[i];
            el[y[i]].push_front(b);
        }else{
            b->y = y[i];
            b->x = x[j];
            el[y[j]].push_front(b);
        }
        b->dx = x[j] - x[i];
        b->dy = y[j] - y[i];
        b->sum = 0;
    }
    
    list<bucket *> ael;
    
    for(int y = 0; y < n_scanlines; y++){
        ael = filter(ael, y);
        updateXs(ael);
        list <bucket*> yBucket = el[y];
        //printf("before: ael size is %lu, yBucket size is %lu\n", ael.size(), yBucket.size());
        ael = insert(yBucket, ael);
        //printf("after: ael size is %lu\n", ael.size());
        for(list<bucket *>::iterator it = ael.begin(); it != ael.end(); it++){
            bucket * e1 = *it;
            it++;
            if(it == ael.end()){
                it = ael.begin();
                bucket * e2 = *it;
                int start = e1->sum == 0 ? e1->x : e1->x+1;
                int end = e2->sum == 0 ? e2->x-1 : e2->x;
                for(int x = start; x <= end; x++){
                    C.setPixel(x, y);
                }
            }else{
                bucket * e2 = *it;
                int start = e1->sum == 0 ? e1->x : e1->x+1;
                int end = e2->sum == 0 ? e2->x-1 : e2->x;
                for(int x = start; x <= end; x++){
                    C.setPixel(x, y);
                }
            }
        }
    }
}






















