//
//  simpleCanvas.h
//  
//
//  Created by Warren R. Carithers on 01/15/14.
//  Based on a C++ version created by Joe Geigel on 11/30/11.
//  Copyright 2014 Rochester Institute of Technology. All rights reserved.
//

#ifndef _SIMPLECANVAS_H
#define _SIMPLECANVAS_H

#include <SFML/Graphics.h>

/**
 * Simple canvas structure that allows for pixel-by-pixel rendering.
 *
 */
typedef struct st_simpleCanvas {

    /**
     * height and width of the canvas
     */
    int width;
    int height;

    sfImage *myImage;
    sfColor myColor;

} simpleCanvas;

/**
 * Constructor
 *
 * @param w width of canvas
 * @param h height of canvas
 */
simpleCanvas *simpleCanvas_create( int w, int h );

/**
 * Destructor
 *
 * @param C canvas to destroy
 */
void simpleCanvas_destroy( simpleCanvas *C );

/**
 * clears the canvas using the current color
 */
void simpleCanvas_clear( simpleCanvas *C );

/**
 * draw yourself into a given renderWindow
 *
 * @param R the window in which to draw.
 */
void simpleCanvas_draw (sfRenderWindow *R, simpleCanvas *C);

/**
 * Sets the current color
 *
 * @param r The red component of the new color (between 0-1)
 * @param g The green component of the new color (between 0-1)
 * @param b The blue component of the new color (between 0-1);
 */
void simpleCanvas_setColor (float r, float g, float b, simpleCanvas *C);

/**
 * writes a pixel using the passed in color.  Does not modify the 
 * current color
 *
 * @param x The x coord of the pixel to be set
 * @param y The y coord of the pixel to be set
 * @param r The red component of the new color (between 0-1)
 * @param g The green component of the new color (between 0-1)
 * @param b The blue component of the new color (between 0-1)
 */
void simpleCanvas_setPixelColor (int x, int y, float r, float g, float b,
    simpleCanvas *C);

/**
 * writes a pixel using the current color
 *
 * @param x The x coord of the pixel to be set
 * @param y The y coord of the pixel to be set
 */
void simpleCanvas_setPixel (int x, int y, simpleCanvas *C);

#endif
