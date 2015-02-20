//
//  Rasterizer.c
//  
//
//  Created by Warren R. Carithers on 01/28/14.
//  Based on a C++ version created by Joe Geigel on 11/30/11.
//  Copyright 2014 Rochester Institute of Technology. All rights reserved.
//

#include <stdlib.h>
#include "Rasterizer.h"
#include "simpleCanvas.h"

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
Rasterizer *Rasterizer_create (int n)
{
    Rasterizer *new = calloc( 1, sizeof(Rasterizer) );
    if( new != NULL ) {
        new->n_scanlines = n;
    }
    return( new );
}

/**
 * Destructor
 *
 * @param R Rasterizer to destroy
 */
void Rasterizer_destroy( Rasterizer *R )
{
    if( R )
        free( R );
}

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
    simpleCanvas *C, Rasterizer *R )
{
    // YOUR IMPLEMENTATION GOES HERE
}
