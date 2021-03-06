/*********************************************************************
Use the image magic library to paint a picture from a file of lines
and fill colors.
CFLAGS = -I/usr/include/ImageMagick-6 -DMAGICKCORE_QUANTUM_DEPTH=16 -DMAGICKCORE_HDRI_ENABLE=0
LDLIBS = /lib/libMagickWand-6.Q16.so /lib/libMagickCore-6.Q16.so
*********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <ImageMagick-6/wand/magick_wand.h>
#include <ImageMagick-6/magick/MagickCore.h>


static MagickWand *m_wand;
// background and foreground.
static PixelWand *bc_wand;
static PixelWand *fc_wand;
static DrawingWand *dw;
static ChannelType channel;

static int lineno; /* line number */

/* This routine mostly converts integers to decimal, as DrawLine expects. */
static void drawSegment(int x1, int y1, int x2, int y2)
{
DrawLine(dw, (double)x1, (double)y1, (double)x2, (double)y2);
#if 0
// for debugging
printf("draw %d %d - %d %d\n", x1, y1, x2, y2);
#endif
}

int main(int argc, char **argv)
{
FILE *f;
int w_pixel, h_pixel;
int x, y, last_x, last_y;
char action;
char dodraw = 0;
char line[60];
const char *color;
int radius, rad2;
char *q;

if(argc != 3) {
fprintf(stderr, "usage:  drawit inputfile outputfile\n");
exit(1);
}

f = fopen(argv[1], "r");
if(!f) {
fprintf(stderr, "drawit cannot open %s\n", argv[1]);
exit(1);
}

lineno = 0;
while(fgets(line, sizeof(line), f)) {
++lineno;
sscanf(line, "%c%d,%d", &action, &x, &y);
switch(action) {
case 'f':
// set the frame, should be first line of the input file
MagickWandGenesis();
m_wand = NewMagickWand();
bc_wand = NewPixelWand();
	PixelSetColor(bc_wand, "white");
MagickNewImage(m_wand, x, y, bc_wand);
fc_wand = NewPixelWand();
	PixelSetColor(fc_wand, "black");
	channel = ParseChannelOption("rgba");
dw = NewDrawingWand();
DrawSetStrokeColor(dw, fc_wand);
DrawSetStrokeWidth(dw, 2.0);
DrawSetStrokeOpacity(dw, 1.0);
break;

case 'd': // draw
drawSegment(last_x, last_y, x, y);

case 's': // set
last_x = x, last_y = y;
break;

case 'c': // circle
last_x = last_y = 0;
radius = atoi(strchr(line, 'r') + 1);
q = strchr(line, 's');
if(!q) { // circle
DrawCircle(dw, x, y, x, x+radius);
} else { // ellipse
++q;
rad2 = atoi(q);
DrawEllipse(dw, x, y, radius, rad2, 0, 0);
}
break;

// everything else is flood fill
case 'b': color = "blue"; goto fill;
case 'r': color = "red"; goto fill;
case 'g': color = "green"; goto fill;
case 'y': color = "yellow"; goto fill;
case 'p': color = "pink"; goto fill;
case 'o': color = "orange"; goto fill;
default:
fprintf(stderr, "line %d: invalid action %c\n", lineno, action);
exit(1);
fill:
if(!dodraw) {
MagickDrawImage(m_wand, dw);
dodraw = 1;
}
	PixelSetColor(fc_wand, color);
	//      The bordercolor=bc_wand (with fuzz of 20 applied) is replaced 
	// by the fill colour=fc_wand starting at the given coordinate.
	// Normally the last argument is MagickFalse so that the colours are matched but
	// if it is MagickTrue then it floodfills any pixel that does *not* match 
	// the target color
	MagickFloodfillPaintImage(m_wand, channel, fc_wand, 20, bc_wand, x, y,
				  MagickFalse);
#if 0
// for debugging
printf("fill %s %d,%d\n", color, x, y);
#endif

}
}

// and write the file.
if (MagickWriteImage(m_wand, argv[2]) == MagickFalse) {
ExceptionType severity;
const char *msg;
msg = MagickGetException(m_wand, &severity);
printf("%d %s\n", severity, msg);
fprintf(stderr,"drawit cannot create the output file %s\n", argv[2]);
exit(1);
}

/* and we're done so destroy the magick wand etc. */
DestroyDrawingWand(dw);
DestroyPixelWand(fc_wand);
DestroyPixelWand(bc_wand);
DestroyMagickWand(m_wand);
MagickWandTerminus();
exit(0);
} /* main */
