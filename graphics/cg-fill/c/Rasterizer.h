//
//  Rasterizer.h
//  
//
//  Created by Warren R. Carithers on 01/28/14.
//  Based on a C++ version created by Joe Geigel on 11/30/11.
//  Copyright 2014 Rochester Institute of Technology. All rights reserved.
//

#ifndef _RASTERIZER_H_
#define _RASTERIZER_H_

#include "simpleCanvas.h"

/**
 *
 * Simple structure that performs rasterization algorithms
 *
 */

typedef struct st_Rasterizer {

    /**
     * number of scanlines
     */
    int n_scanlines;

} Rasterizer;

/**
 * Constructor
 *
 * @param n - number of scanlines
 *
 */
Rasterizer *Rasterizer_create( int n );

/**
 * Destructor
 *
 * @param R Rasterizer to destroy
 */
void Rasterizer_destroy( Rasterizer *R );

/**
 * Draw a filled polygon in the the simpleCanvas C.
 *
 * The polygon has n distinct vertices.  The coordinates of the vertices
 * making up the polygon are stored in the x and y arrays.  The ith
 * vertex will have coordinate (x[i],y[i]).
 *
 * You are to add the implementation here using only calls
 * to simpleCanvas_setPixel()
 *
 * @param n - number of vertices
 * @param x - x coordinates
 * @param y - y coordinates
 * @param C - The canvas on which to apply the draw command.
 * @param R - The relevant rasterizer (not currently used)
 */
void drawPolygon( int n, int x[], int y[],
    simpleCanvas *C, Rasterizer *R );

#endif
