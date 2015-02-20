//
//  simpleCanvas.c
//  
//  Created by Warren R. Carithers on 01/15/14.
//  Based on a C++ version created by Joe Geigel on 11/30/11.
//  Copyright 2014 Rochester Institute of Technology.  All rights reserved.
//

#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <SFML/Config.h>
#include "simpleCanvas.h"

/**
 * Simple canvas class that allows for pixel-by-pixel rendering.
 *
 */

/**
 * Constructor
 *
 * @param w width of canvas
 * @param h height of canvas
 */
simpleCanvas *simpleCanvas_create( int w, int h )
{
    simpleCanvas *new = calloc( 1, sizeof(simpleCanvas) );
    if( new != NULL ) {
        new->width = w;
        new->height = h;
        new->myColor.r = 0;
        new->myColor.g = 0;
        new->myColor.b = 0;
        new->myColor.a = 255;
        new->myImage = sfImage_createFromColor( w, h, new->myColor );
    }
    return( new );
}


/**
 * Destructor
 *
 * @param C canvas to destroy
 */
void simpleCanvas_destroy( simpleCanvas *C )
{
    if( !C )
        return;
    if( C->myImage )
        sfImage_destroy( C->myImage );
    free( C );
}


/**
 * clears the canvas using the current color
 */
void simpleCanvas_clear( simpleCanvas *C )
{
    for (int i=0; i < C->width; i++)
        for (int j=0; j < C->height; j++)
            sfImage_setPixel( C->myImage, i, j, C->myColor );
}


/**
 * draw yourself into a given renderWindow
 *
 * @param R the window in which to draw.
 */
void simpleCanvas_draw (sfRenderWindow *R, simpleCanvas *C )
{
    sfSprite *sprite;
    sfTexture *texture;

    texture = sfTexture_createFromImage( C->myImage, NULL );
    sfTexture_setSmooth( texture, sfFalse );

    // Add your image as a sprite
    sprite = sfSprite_create();
    sfSprite_setTexture( sprite, texture, sfFalse );

    // draw it
    sfRenderWindow_drawSprite( R, sprite, 0 );

    // release the sprite and texture
    sfSprite_destroy( sprite );
    sfTexture_destroy( texture );
}


/**
 * Sets the current color
 *
 * @param r The red component of the new color (between 0-1)
 * @param g The green component of the new color (between 0-1)
 * @param b The blue component of the new color (between 0-1);
 */
void simpleCanvas_setColor (float r, float g, float b, simpleCanvas *C )
{
    C->myColor.r = (unsigned char)(r * 255);
    C->myColor.g = (unsigned char)(g * 255);
    C->myColor.b = (unsigned char)(b * 255);
}


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
    simpleCanvas *C )
{
    unsigned char R = (unsigned char)(r * 255);
    unsigned char G = (unsigned char)(g * 255);
    unsigned char B = (unsigned char)(b * 255);
    sfColor color = { R, G, B };
    sfImage_setPixel( C->myImage, x, y, color );
}


/**
 * writes a pixel using the current color
 *
 * @param x The x coord of the pixel to be set
 * @param y The y coord of the pixel to be set
 */
void simpleCanvas_setPixel (int x, int y, simpleCanvas *C )
{
    sfImage_setPixel( C->myImage, x, C->height - y - 1, C->myColor );
}
