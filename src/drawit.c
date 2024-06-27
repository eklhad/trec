/*********************************************************************
Use the image magic library to paint a picture from a file of lines
and fill colors.
CFLAGS = -I/usr/include/ImageMagick-6 -DMAGICKCORE_QUANTUM_DEPTH=16 -DMAGICKCORE_HDRI_ENABLE=0
LDLIBS = /lib/libMagickWand-6.Q16.so /lib/libMagickCore-6.Q16.so
You may need to use png48:outfile.png
_GNU_SOURCE is needed to prototype asprintf.
Coordinates don't match the conventions of mathematics, x and y,
nor do they match matrix convention.
A pixel at 71,5 is 71 over and 5 down.  Ugh!
*********************************************************************/

#define _GNU_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#include <ImageMagick-6/wand/magick_wand.h>
#include <ImageMagick-6/magick/MagickCore.h>

// color codes and words
static const char ccodes[] = "brgypokwe";
static const char *cwords[] = {
"blue","red","green","yellow","pink","orange","black","white","purple"
};
static const char *colorWord(char c)
{
const char *s = strchr(ccodes, c);
if(!s) return 0; // bad code
return cwords[s - ccodes];
}

static MagickWand *m_wand;
// background and foreground.
static PixelWand *bc_wand;
static PixelWand *fc_wand;
static DrawingWand *dw;
static ChannelType channel;

static void setColor(const char *color, int hollow)
{
	PixelSetColor(fc_wand, color);
DrawSetStrokeColor(dw, fc_wand);
if(hollow) 	PixelSetColor(fc_wand, "white");
DrawSetFillColor(dw, fc_wand);
// less that 4 and FloodFill doesn't work properly
DrawSetStrokeWidth(dw, 4.0);
DrawSetStrokeOpacity(dw, 1.0);
}

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
char *out2;
int w_pixel, h_pixel;
int x, y, last_x, last_y;
char action;
char dodraw = 0;
char line[400];
const char *color;
int radius, rad2;
char *q;

if(argc > 3 || argc < 2) {
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
// skip blank lines and comments
if(line[0] == '\n' || line[0] == '\r' || line[0] == '#') continue;

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
	channel = ParseChannelOption("rgba");
dw = NewDrawingWand();
setColor("black", 0);
break;

case 'd': // draw
drawSegment(last_x, last_y, x, y);

case 's': // set
last_x = x, last_y = y;
break;

case 'c': // circle
last_x = last_y = 0;
q = strchr(line, 'r');
radius = strtol(q + 1, &q, 10);
if(*q != 's' && *q != 'u' && *q != 'l') { // circle
color = 0;
if(*q && !isspace(*q)) {
color = colorWord(*q);
if(!color) {
fprintf(stderr, "line %d: bad circle color %c\n", lineno, *q);
exit(1);
}
}
if(color) setColor(color, 0);
DrawCircle(dw, x, y, x, y+radius);
// and put it "back in black"
if(color) setColor("black", 0);
} else { // ellipse
char portion = 0;
if(*q == 'u') portion = 1;
if(*q == 'l') portion = 2;
rad2 = strtol(q + 1, &q, 10);
color = 0;
if(*q && !isspace(*q)) {
color = colorWord(*q);
if(!color) {
fprintf(stderr, "line %d: bad ellipse color %c\n", lineno, *q);
exit(1);
}
}
if(color) setColor(color, 0);
if(portion == 0)
DrawEllipse(dw, x, y, radius, rad2, 0, 360);
if(portion == 1)
DrawEllipse(dw, x, y, radius, rad2, 180, 360);
if(portion == 2)
DrawEllipse(dw, x, y, radius, rad2, 0, 180);
// and put it "back in black"
if(color) setColor("black", 0);
}
break;

// everything else is flood fill
default:
color = colorWord(action);
if(color) goto fill;
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
if(!dodraw) MagickDrawImage(m_wand, dw);
if(argc == 3) out2 = argv[2];
else asprintf(&out2, "png48:%s.png", argv[1]);
if (MagickWriteImage(m_wand, out2) == MagickFalse) {
ExceptionType severity;
const char *msg;
msg = MagickGetException(m_wand, &severity);
printf("%d %s\n", severity, msg);
fprintf(stderr,"drawit cannot create the output file %s\n", out2);
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
