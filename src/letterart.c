/*********************************************************************
Use the image magic library to paint a polyomino tiling from its letter matrix.
CFLAGS = -I/usr/include/ImageMagick-6 -DMAGICKCORE_QUANTUM_DEPTH=16 -DMAGICKCORE_HDRI_ENABLE=0
LDLIBS = /lib/libMagickWand-6.Q16.so /lib/libMagickCore-6.Q16.so
You may need to use png48:outfile.png
_GNU_SOURCE is needed to prototype asprintf.
*********************************************************************/

#define _GNU_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <ImageMagick-6/wand/magick_wand.h>
#include <ImageMagick-6/magick/MagickCore.h>

#define BOARDWIDTH 250

static MagickWand *m_wand;
// background and foreground.
static PixelWand *bc_wand;
static PixelWand *fc_wand;
static DrawingWand *dw;

static const int _x0 = 20;
static int _x1;
static const int _y0 = 20;
static int _y1;
static int dpl; /* dots per letter */
static int w_pixel, h_pixel; // pixels across and down
static int width; /* in letters */
static int lineno; /* line number */
#define xloc(n) ((n)*dpl + _x0)

static char thisline[BOARDWIDTH+6], lastline[BOARDWIDTH+6];

static char debugdraw;

static void setScale(void)
{
dpl = 20;
while(dpl*width > 760) --dpl;
if(dpl < 7) {
fprintf(stderr, "dpl %d too small\n", dpl);
exit(1);
}
_x1 = xloc(width);
} /* setScale */

/* This routine mostly converts integers to decimal, as DrawLine expects. */
static void drawSegment(int x1, int y1, int x2, int y2)
{
DrawLine(dw, (double)x1, (double)y1, (double)x2, (double)y2);
if(debugdraw)
printf("draw %d %d - %d %d\n", x1, y1, x2, y2);
}

static void printRow(void)
{
int agree, i, _y2;

if(!lineno) {
/* top line of the rectangle */
_y1 = _y0;
memset(lastline, ' ', width);
}
/* borders with previous row */
agree = -1;
for(i=0; i<width; ++i) {
if(thisline[i] != lastline[i])
continue;
if(agree+1 < i) {
/* region of disagreeing letters, draw line */
drawSegment(xloc(agree+1), _y1, xloc(i), _y1);
}
agree = i;
}
if(agree+1 < i) {
drawSegment(xloc(agree+1), _y1, xloc(i), _y1);
}

_y2 = _y1 + dpl;
/* left and right border */
if(thisline[0] != ' ')
drawSegment(_x0, _y1, _x0, _y2);
if(thisline[width-1] != ' ')
drawSegment(_x1, _y1, _x1, _y2);

for(i=1; i<width; ++i) {
if(thisline[i] == thisline[i-1])
continue;
drawSegment(xloc(i), _y1, xloc(i), _y2);
}

_y1 = _y2;
++lineno;
} /* printRow */

int main(int argc, char **argv)
{
FILE *f;
char *out2;
int w;
char *s;

if(argc == 4 && !strcmp(argv[1], "-d")) {
debugdraw = 1;
--argc, ++argv;
}

if(argc > 3 || argc < 2) {
fprintf(stderr, "usage:  letterart [-d] inputfile outputfile\n");
exit(1);
}

f = fopen(argv[1], "r");
if(!f) {
fprintf(stderr, "letterart cannot open %s\n", argv[1]);
exit(1);
}

// count lines and set dimensions.
lineno = 0;
while(fgets(thisline, sizeof(thisline), f)) {
s = strpbrk(thisline, "\r\n");
if(s) *s = 0;
w = strlen(thisline);
if(!lineno) {
width = w;
setScale();
} else if(width != w) {
fprintf(stderr, "width mismatch %d versus %d\n", width, w);
exit(1);
}
++lineno;
}
w_pixel = 20*2 + dpl*width;
h_pixel = 20*2 + dpl*lineno;

MagickWandGenesis();
m_wand = NewMagickWand();
bc_wand = NewPixelWand();
	PixelSetColor(bc_wand, "white");
MagickNewImage(m_wand, w_pixel, h_pixel, bc_wand);
fc_wand = NewPixelWand();
	PixelSetColor(fc_wand, "black");
dw = NewDrawingWand();
DrawSetStrokeColor(dw, fc_wand);
DrawSetStrokeWidth(dw, 2.0);
DrawSetStrokeOpacity(dw, 1.0);

lineno = 0;
rewind(f);
while(fgets(thisline, sizeof(thisline), f)) {
s = strpbrk(thisline, "\r\n");
if(s) *s = 0;
printRow();
strcpy(lastline, thisline);
}

/* bottom line */
memset(thisline, ' ', width);
printRow();

// and write the file.
MagickDrawImage(m_wand, dw);
if(argc == 3) out2 = argv[2];
else asprintf(&out2, "png48:%s.png", argv[1]);
if (MagickWriteImage(m_wand, out2) == MagickFalse) {
ExceptionType severity;
const char *msg;
msg = MagickGetException(m_wand, &severity);
printf("%d %s\n", severity, msg);
fprintf(stderr,"letterart cannot create the output file %s\n", out2);
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
