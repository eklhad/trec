/*********************************************************************
3dbox.c: fill a box with 3d polyominoes.
Use the -O option, or a lot of my coding tricks won't speed things up,
and could even slow things down.
*********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <malloc.h>
#include <ctype.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>

#ifndef O_BINARY
#define O_BINARY 0
#endif

#define DEBUG 0
#define NODEHOLES 0
#define CORNERHOLES 1
#define NEAR 1
#define SWING 1

typedef unsigned char uchar;
typedef signed char schar;
typedef ushort shapebits;

// short highbit macros
#define HIGHBIT 0x8000
#define isHighbit(word) ((short)(word) < 0)
#define isNotHighbit(word) ((short)(word) >= 0)

// command line parameters
static int showdiag;
static uchar doNodes; // look by using nodes instead of filling the entire box
static uchar robin = 1; // round robin on the colors
static uchar countFlag; // count or generate solutions
static uchar tubes = 0;
static uchar hascorner = 0;
static uchar flat3 = 0;
static int countSol = 0;
static int oc_2, oc_3, oc_4, oc_6; // overcounts
static int megaNodes = 80; // millions of nodes that can be cached
static long maxNodes; // megaNodes times a million
static long slopNodes; // maxNodes plus some slop for the randomness of the hash
static int dim_x, dim_y, dim_z; // box being filled
static int boxOrder, boxArea, boxVolume;

#define NSQ 100 // number of squares in largest polyomino
static int nsq; // number of squares in the polyomino
static int nsqMix; // different square counts among the pieces
static int curDepth; // when climbing through layers
static int maxDepth, minDepth;
static int reachup; /* greatest reach of node so far */
static int setMaxDimension, setMinDimension;
static int stopgap, forgetgap;
static uchar r_shorts; // nodes must use shorts, rather than bytes
static int restart = -1; // depth when resuming the analysis
static int restartParent;
static int cbflag; // checkerboard flag
static int csflag; // checkerstripe flag
static int cpflag; // checkerplane flag
static int ordFactor = 1;

// see the comments at the top of trec.c
#define stopsearch (2*curDepth + stopgap > maxDepth)
#define stopstore(x) (2*curDepth + stopgap == maxDepth || curDepth + x.depth + x.gap > maxDepth)

#define REPDIAMETER 16 // represent pieces this large
#define SETSIZE 30 // number of pieces in the set
static int setSize; // for sets of polyominoes
static int qty[SETSIZE]; // limit on number of pieces used
static int qtyc[SETSIZE]; // limit on chiral pieces used
static int qtySpec; // some quantity was specified
static int qtyOne = 1; // just one of each piece
static int qtyTotal, qtyOrder;
static int qu[SETSIZE], quc[SETSIZE]; // quantity used
#define MAXORDER 1000
#define BOXWIDTH 32

// orientation boards
static uchar orib1[REPDIAMETER][REPDIAMETER][REPDIAMETER];
static uchar orib2[REPDIAMETER][REPDIAMETER][REPDIAMETER];
static struct SLICE { short xy; shapebits bits; } orib3[NSQ];
static shapebits orib4[REPDIAMETER][REPDIAMETER];

// Rotate and reflect a polyominoe in position.
static void counterclockwise(void)
{
int x, y, z;
for(x=0; x<REPDIAMETER; ++x)
for(y=0; y<REPDIAMETER; ++y)
for(z=0; z<REPDIAMETER; ++z)
orib2[REPDIAMETER-1-y][x][z] = orib1[x][y][z];
}

static void y_mirror(void)
{
int x, y, z;
for(x=0; x<REPDIAMETER; ++x)
for(y=0; y<REPDIAMETER; ++y)
for(z=0; z<REPDIAMETER; ++z)
orib2[x][REPDIAMETER-1-y][z] = orib1[x][y][z];
}

static void point_mirror(void)
{
int x, y, z;
for(x=0; x<REPDIAMETER; ++x)
for(y=0; y<REPDIAMETER; ++y)
for(z=0; z<REPDIAMETER; ++z)
orib2[REPDIAMETER-1-x][REPDIAMETER-1-y][REPDIAMETER-1-z] = orib1[x][y][z];
}

static void xyz_spin(void)
{
int x, y, z;
for(x=0; x<REPDIAMETER; ++x)
for(y=0; y<REPDIAMETER; ++y)
for(z=0; z<REPDIAMETER; ++z)
orib2[y][z][x] = orib1[x][y][z];
}

static void bailout(const char *msg, int n)
{
fprintf(stderr, msg, n);
fprintf(stderr, "\n");
exit(1);
}

static void bailouts(const char *msg, const char *n)
{
fprintf(stderr, msg, n);
fprintf(stderr, "\n");
exit(1);
}

static void *emalloc(unsigned int n)
{
void *s = malloc(n);
if(!s) bailout("failure to allocate %d bytes", n);
return s;
}

static void *erealloc(void *p, unsigned int n)
{
void *s = realloc(p, n);
if(!s) bailout("failure to reallocate %d bytes", n);
return s;
}

static void eread(int fd, void *buf, unsigned n)
{
if((unsigned)read(fd, buf, n) != n)
bailout("disk read error, errno %d", errno);
}

static void ewrite(int fd, const void *buf, unsigned n)
{
const char *s = buf;
int rc;
char hold[24];
top:
rc = write(fd, s, n);
if(rc == (signed)n) return; // good write
// Disk failure, disk is probably full,
// you could save the situation by clearing space.
if(rc > 0) n -= rc, s += rc;
printf("\nDisk failure, errno %d.\n\
If I stop now, all your work at this depth could be lost.\n\
See if you can fix the problem, then hit return, and I will try again.\n\
Or type x and I will exit, and it's game over.\n", errno);
// Don't worry about other threads, all disk access is inside a mutex,
// so the other threads will queue up behind this one, and not write,
// and wait for you to hit return.
if(!fgets(hold, sizeof(hold), stdin) ||
hold[0] == 'x') exit(2);
// Is the file offset still at the end of the file? Sure hope so.
// lseek(fd, 0, SEEK_END);
goto top;
}

static void elseek(int fd, long offset)
{
if(lseek(fd, offset, SEEK_SET) < 0)
bailout("disk seek error, errno %d", errno);
}

struct ORIENT { // describe an orientation
uchar pno; // piece number in the set
uchar ono; // orientation number
uchar x, y; // offset of lowest square
uchar rng_x, rng_y, rng_z; // range of this piece in this orientation
uchar slices;
schar breakLine; // the row with more than half the piece below it
uchar ambig; // ambiguous indicator
uchar inspace; // nonchiral orientation
uchar zflip;
int near;
// the swing orientations, when one corner swings around to the other.
short hr, vr; // horizontal vertical reflections
short dxy, dxz, dyz; // diagonal reflections
short r1, r2, r3; // rotations
short dr2; // rotate 180 then xy reflect
short spin1, spin2;
uchar zero_spin, zero_dxy, zero_dxz, zero_dyz, zero_hr, zero_vr, zero_zr, farbits;
struct SLICE pattern[NSQ];
uchar slant[NSQ];
};

#define O_MAX 1000
static int o_max; /* number of orientations */
static int o_max2;
static struct ORIENT o_list[O_MAX];

static void print_o(const struct ORIENT *o)
{
int x, y, n = 0;
// assumes slices are in a raster order
for(y=0; y<o->rng_y; ++y) {
if(y) printf("!");
for(x=0; x<o->rng_x; ++x) {
int xy = y * BOXWIDTH + x;
if(n == o->slices || o->pattern[n].xy != xy) {
printf("00");
} else {
shapebits mask = o->pattern[n++].bits;
printf("%02x", (mask>>8));
mask &= 0xff;
if(mask == 0x80) printf("+");
else if(mask) printf("{%02x}", mask);
}
}
}
printf("\n");
}

// translate back to the origin
static void pulldown(int r1, int r2, int r3)
{
int x, y, z, j, n;
int rng_x, rng_y, rng_z; // range of the piece
int start_x, start_y, near;
struct ORIENT *o;
int chiral = r2 ^ r3;

for(x=0; x<REPDIAMETER; ++x)
for(y=0; y<REPDIAMETER; ++y)
for(z=0; z<REPDIAMETER; ++z)
if(orib2[x][y][z]) goto floor_x;
floor_x:
if(x == REPDIAMETER) bailout("pulldown empty space", 0);
j = x;
if(j) {
for(x=0; x<REPDIAMETER; ++x)
for(y=0; y<REPDIAMETER; ++y)
for(z=0; z<REPDIAMETER; ++z)
orib2[x][y][z] =
(x+j < REPDIAMETER ? orib2[x+j][y][z] : 0);
}

for(y=0; y<REPDIAMETER; ++y)
for(x=0; x<REPDIAMETER; ++x)
for(z=0; z<REPDIAMETER; ++z)
if(orib2[x][y][z]) goto floor_y;
floor_y:
if(y == REPDIAMETER) bailout("pulldown empty space", 0);
j = y;
if(j) {
for(x=0; x<REPDIAMETER; ++x)
for(y=0; y<REPDIAMETER; ++y)
for(z=0; z<REPDIAMETER; ++z)
orib2[x][y][z] =
(y+j < REPDIAMETER ? orib2[x][y+j][z] : 0);
}

for(z=0; z<REPDIAMETER; ++z)
for(x=0; x<REPDIAMETER; ++x)
for(y=0; y<REPDIAMETER; ++y)
if(orib2[x][y][z]) goto floor_z;
floor_z:
if(z == REPDIAMETER) bailout("pulldown empty space", 0);
j = z;
if(j) {
for(x=0; x<REPDIAMETER; ++x)
for(y=0; y<REPDIAMETER; ++y)
for(z=0; z<REPDIAMETER; ++z)
orib2[x][y][z] =
(z+j < REPDIAMETER ? orib2[x][y][z+j] : 0);
}

if(orib2[0][0][0]) hascorner = 1;

rng_x = rng_y = rng_z = 0;
for(x=0; x<REPDIAMETER; ++x)
for(y=0; y<REPDIAMETER; ++y)
for(z=0; z<REPDIAMETER; ++z)
if(orib2[x][y][z]) {
if(x > rng_x) rng_x = x;
if(y > rng_y) rng_y = y;
if(z > rng_z) rng_z = z;
}

// Scan in a diagonal pattern, rather than raster, it increases speed
// a few percent. Assumes dim_x >= dim_y.
x = y = 0;
while(!orib2[x][y][0]) {
++y, --x;
if(y == dim_y) {
x += dim_y, y = 0;
++x; // next diagonal
while(x >= dim_x) ++y, --x;
if(y == dim_y) bailout("orientation %d has nothing on the floor", o_max);
continue;
}
if(x < 0) x += y+1, y = 0;
}
start_y = y, start_x = x;

n = 0;
for(y=0; y<REPDIAMETER; ++y)
for(x=0; x<REPDIAMETER; ++x) {
shapebits mask = 0;
for(z=0; z<REPDIAMETER; ++z)
if(orib2[x][y][z])
mask |= (HIGHBIT>>z);
if(mask) orib3[n].xy = y*BOXWIDTH + x, orib3[n].bits = mask, ++n;
}

// Have we seen this one before?
o = o_list;
for(j=0; j<o_max; ++j, ++o)
if( n == o->slices && !memcmp(orib3, o->pattern, sizeof(struct SLICE)*n)) {
if(j < o_max2) bailout("a piece is duplicated in the set", 0);
o->inspace |= !chiral;
if((o->zflip&3) == r1 &&
(o->zflip&4) != (r2<<2))
o->zflip |= 8;
return;
}

if(o_max == O_MAX)
bailout("too many orientations, limit %d", O_MAX);
memcpy(o->pattern, orib3, sizeof(struct SLICE)*n);
o->slices = n;
o->ono = o_max;
o->pno = setSize;
o->x = start_x, o->y = start_y;
o->rng_x = rng_x + 1, o->rng_y = rng_y + 1, o->rng_z = rng_z + 1;
if(o->rng_z > setMaxDimension) setMaxDimension = o->rng_z;
if(setMaxDimension > 9) r_shorts = 1;
if(o->rng_z < setMinDimension) setMinDimension = o->rng_z;
if(o->rng_z == 1 && o->rng_x >= 3 && o->rng_y >= 3) flat3 = 1;
o->ambig = 0;
o->zflip = r1; // remember the spin
o->zflip |= (r2<<2); // remember point reflection
o->inspace = !chiral;
o->zero_spin = o->zero_dxy = o->zero_dxz = o->zero_dyz = o->zero_hr = o->zero_vr = o->zero_zr = o->farbits = 0;

for(x=0; x<=rng_x; ++x)
for(y=0; y<=rng_y; ++y)
for(z=0; z<=rng_z-1; ++z) {
if(!orib2[x][y][z] || !orib2[x][y][z+1]) continue;
if(z < rng_z-1 && orib2[x][y][z+2]) continue;
if(x && orib2[x-1][y][z]) continue;
if(x < rng_x && orib2[x+1][y][z]) continue;
if(y && orib2[x][y-1][z]) continue;
if(y < rng_y && orib2[x][y+1][z]) continue;
if(x && orib2[x-1][y][z+1]) continue;
if(x < rng_x && orib2[x+1][y][z+1]) continue;
if(y && orib2[x][y-1][z+1]) continue;
if(y < rng_y && orib2[x][y+1][z+1]) continue;
tubes = 1;
}

// compute the break level. Include this piece if we have
// tiled up through breakLine.
o->breakLine = (o->rng_z-1)/2;
if(!(o->rng_z&1)) { // even, requires further refinement
// See which half is "heavier".
// This is a center of mass calculation.
// But simple moment makes horizontal e0b0 ambiguous, so give extra weight
// to the squares near the outside of the piece.
int bottom = 0, top = 0;
for(x=0; x<o->rng_x; ++x)
for(y=0; y<o->rng_y; ++y)
for(z=0; z<o->rng_z; ++z)
if(orib2[x][y][z]) {
int subtotal, v, w;
int k = z - o->breakLine;
if(k <= 0) --k;
// REPDIAMETER 16, k at most 8, k^2 at most 64
// 100 squares: 100*64 = 6400
subtotal = (k*k << 18);
v = o->rng_y/2 - y;
if(v <= 0 && !(o->rng_y&1)) --v;
// extra credit for connectivity toward the middle
if(v < 0 && orib2[x][y-1][z]) --v;
if(v > 0 && orib2[x][y+1][z]) ++v;
w = o->rng_x/2 - x;
if(w <= 0 && !(o->rng_x&1)) --w;
if(w < 0 && orib2[x-1][y][z]) --w;
if(w > 0 && orib2[x+1][y][z]) ++w;
if(v < 0) v = -v;
if(w < 0) w = -w;
subtotal += v + w + v*w;
if(k < 0) bottom += subtotal; else top += subtotal;
}
if(bottom == top) o->ambig = 1;
if(bottom < top) ++o->breakLine;
}

// near calculation
x = start_x, y = start_y; // shorthand
near = 0;
if(y < o->rng_y-1) {
if(orib2[x][y+1][0]) near |= 1;
if(x && orib2[x-1][y+1][0]) near |= 2;
if(o->rng_z >= 2) {
if(orib2[x][y+1][1]) near |= 4;
if(x && orib2[x-1][y+1][1]) near |= 8;
}
}
if(o->rng_z >= 2) {
if(y && orib2[x][y-1][1]) near |= 0x10;
if(x && y && orib2[x-1][y-1][1]) near |= 0x20;
if(x && orib2[x-1][y][1]) near |= 0x40;
if(orib2[x][y][1]) near |= 0x80;
}
if(x < o->rng_x-1) {
if(orib2[x+1][y][0]) near |= 0x100;
if(y < o->rng_y-1 && orib2[x+1][y+1][0]) near |= 0x200;
}
o->near = near;

if(orib2[0][0][0]) {
// Look for spin and various reflections.
// These only become meaningful if the dimensions are compatible.
// Further calculations in main(), once we know the dimensions.
if(o->rng_x == o->rng_y) {
for(x=0; x<o->rng_x; ++x)
for(y=0; y<o->rng_y; ++y)
for(z=0; z<o->rng_z; ++z)
if(orib2[x][y][z] != orib2[y][x][z]) goto past_dxy;
o->zero_dxy = 1;
past_dxy: ;
if(o->rng_x == o->rng_z) {
for(x=0; x<o->rng_x; ++x)
for(y=0; y<o->rng_y; ++y)
for(z=0; z<o->rng_z; ++z)
if(orib2[x][y][z] != orib2[y][z][x]) goto past_spin;
o->zero_spin = 1;
past_spin: ;
}
}
if(o->rng_x == o->rng_z) {
for(x=0; x<o->rng_x; ++x)
for(y=0; y<o->rng_y; ++y)
for(z=0; z<o->rng_z; ++z)
if(orib2[x][y][z] != orib2[z][y][x]) goto past_dxz;
o->zero_dxz = 1;
past_dxz: ;
}
if(o->rng_y == o->rng_z) {
for(x=0; x<o->rng_x; ++x)
for(y=0; y<o->rng_y; ++y)
for(z=0; z<o->rng_z; ++z)
if(orib2[x][y][z] != orib2[x][z][y]) goto past_dyz;
o->zero_dyz = 1;
past_dyz: ;
}
for(x=0; x<o->rng_x; ++x)
for(y=0; y<o->rng_y; ++y)
for(z=0; z<o->rng_z; ++z)
if(orib2[x][y][z] != orib2[o->rng_x-1-x][y][z]) goto past_hr;
o->zero_hr = 1;
past_hr: ;
for(x=0; x<o->rng_x; ++x)
for(y=0; y<o->rng_y; ++y)
for(z=0; z<o->rng_z; ++z)
if(orib2[x][y][z] != orib2[x][o->rng_y-1-y][z]) goto past_vr;
o->zero_vr = 1;
past_vr: ;
for(x=0; x<o->rng_x; ++x)
for(y=0; y<o->rng_y; ++y)
for(z=0; z<o->rng_z; ++z)
if(orib2[x][y][z] != orib2[x][y][o->rng_z-1-z]) goto past_zr;
o->zero_zr = 1;
past_zr: ;
}
if(orib2[0][0][o->rng_z-1]) o->farbits |= 1;
// since no corner on the ceiling swings to the floor, we can generate
// a z reflected solution even if this pieces isn't symmetric.
// The piece reflects, and all other corners are larger pieces, and que sera sera.
// Just touching the ceiling is all we need. Good news - it almost never happens.
// the box is deeper than the longest piece.
if(o->farbits&1) o->zero_zr = 1;
if(orib2[o->rng_x-1][0][o->rng_z-1]) o->farbits |= 2;
if(orib2[o->rng_x-1][o->rng_y-1][o->rng_z-1]) o->farbits |= 4;
if(orib2[0][o->rng_y-1][o->rng_z-1]) o->farbits |= 8;
if(orib2[o->rng_x-1][o->rng_y-1][0]) o->farbits |= 0x10;

#if DEBUG
printf("range %d,%d,%d near %x", o->rng_x, o->rng_y, o->rng_z, o->near);
printf("_%d%s ", o->breakLine, (o->ambig ? "*" : ""));
print_o(o);
#endif
++o_max;
}

static int sortSlices(int n)
{
int change = 1;
int i, j, diff;
const struct ORIENT *o;

while(change) {
change = 0;
for(i=0; i<n-1; ++i)
if(orib3[i].xy > orib3[i+1].xy) {
struct SLICE swap = orib3[i];
orib3[i] = orib3[i+1];
orib3[i+1] = swap;
change = 1;
}
}

o = o_list;
for(i=0; i<o_max; ++i, ++o) {
if(o->slices != n) continue;
diff = orib3[0].xy - o->pattern[0].xy;
for(j=0; j<n; ++j) {
if(orib3[j].xy - o->pattern[j].xy != diff) break;
if(orib3[j].bits != o->pattern[j].bits) break;
}
if(j == n) return i;
}
bailout("swing orientation not found", 0);
return -1;
}

static void swingSet(void)
{
int i, j, n;
const int r = REPDIAMETER;
int x, y, z;
struct ORIENT *o;
const struct SLICE *s;
int v, k, m;

o = o_list;
for(i=0; i<o_max2; ++i, ++o)
o->r1 = o->r2 = o->r3 = o->hr = o->vr = o->dxy = o->dxz = o->dyz = o->dr2 = o->spin1 = o->spin2 = -1;

o = o_list;
for(i=0; i<o_max; ++i, ++o) {
// has to fill the lower left corner
if(o->pattern[0].xy) continue;
if(isNotHighbit(o->pattern[0].bits)) continue;
n = o->slices;

s = o->pattern;
for(j=0; j<n; ++j, ++s) {
y = s->xy / BOXWIDTH, x = s->xy % BOXWIDTH;
orib3[j].bits = s->bits;
orib3[j].xy = y * BOXWIDTH + r-1-x;
}
o_list[sortSlices(n)].hr = i;

s = o->pattern;
for(j=0; j<n; ++j, ++s) {
y = s->xy / BOXWIDTH, x = s->xy % BOXWIDTH;
orib3[j].bits = s->bits;
orib3[j].xy = (r-1-y) * BOXWIDTH + x;
}
o_list[sortSlices(n)].vr = i;

s = o->pattern;
for(j=0; j<n; ++j, ++s) {
y = s->xy / BOXWIDTH, x = s->xy % BOXWIDTH;
orib3[j].bits = s->bits;
orib3[j].xy = (r-1-y) * BOXWIDTH + r-1-x;
}
o_list[sortSlices(n)].r2 = i;

if(dim_x == dim_y) {
// these only make sense on a square base.

s = o->pattern;
for(j=0; j<n; ++j, ++s) {
y = s->xy / BOXWIDTH, x = s->xy % BOXWIDTH;
orib3[j].bits = s->bits;
orib3[j].xy = x * BOXWIDTH + r-1-y;
}
o_list[sortSlices(n)].r1 = i;

s = o->pattern;
for(j=0; j<n; ++j, ++s) {
y = s->xy / BOXWIDTH, x = s->xy % BOXWIDTH;
orib3[j].bits = s->bits;
orib3[j].xy = (r-1-x) * BOXWIDTH + y;
}
o_list[sortSlices(n)].r3 = i;

s = o->pattern;
for(j=0; j<n; ++j, ++s) {
y = s->xy / BOXWIDTH, x = s->xy % BOXWIDTH;
orib3[j].bits = s->bits;
orib3[j].xy = x * BOXWIDTH + y;
}
o_list[sortSlices(n)].dxy = i;

s = o->pattern;
for(j=0; j<n; ++j, ++s) {
y = s->xy / BOXWIDTH, x = s->xy % BOXWIDTH;
orib3[j].bits = s->bits;
orib3[j].xy = (r-1-x) * BOXWIDTH + (r-1-y);
}
o_list[sortSlices(n)].dr2 = i;
}

if(doNodes) continue;

// now dim_z is meaningful; we are filling a specific box.
// This is rather an add-on, that I didn't think of before,
// that's why it doesn't really fit the design as above.

if(dim_x == dim_z) {
s = o->pattern;
m = 0;
for(j=0; j<n; ++j, ++s)
for(z=0; z<r; ++z)
if(s->bits & (HIGHBIT>>z)) {
y = s->xy / BOXWIDTH, x = s->xy % BOXWIDTH;
v = x, x = z;
for(k=0; k<m; ++k)
if(orib3[k].xy == y*BOXWIDTH+x) break;
if(k == m) orib3[k].xy = y*BOXWIDTH + x, orib3[k].bits = 0, ++m;
orib3[k].bits |= (HIGHBIT>>v);
}
o_list[sortSlices(m)].dxz = i;
}

if(dim_y == dim_z) {
s = o->pattern;
m = 0;
for(j=0; j<n; ++j, ++s)
for(z=0; z<r; ++z)
if(s->bits & (HIGHBIT>>z)) {
y = s->xy / BOXWIDTH, x = s->xy % BOXWIDTH;
v = y, y = z;
for(k=0; k<m; ++k)
if(orib3[k].xy == y*BOXWIDTH+x) break;
if(k == m) orib3[k].xy = y*BOXWIDTH + x, orib3[k].bits = 0, ++m;
orib3[k].bits |= (HIGHBIT>>v);
}
o_list[sortSlices(m)].dyz = i;
}

if(dim_x == dim_y && dim_y == dim_z) {
s = o->pattern;
m = 0;
for(j=0; j<n; ++j, ++s)
for(z=0; z<r; ++z)
if(s->bits & (HIGHBIT>>z)) {
y = s->xy / BOXWIDTH, x = s->xy % BOXWIDTH;
v = x, x = y, y = z;
for(k=0; k<m; ++k)
if(orib3[k].xy == y*BOXWIDTH+x) break;
if(k == m) orib3[k].xy = y*BOXWIDTH + x, orib3[k].bits = 0, ++m;
orib3[k].bits |= (HIGHBIT>>v);
}
o_list[sortSlices(m)].spin1 = i;
s = o->pattern;
m = 0;
for(j=0; j<n; ++j, ++s)
for(z=0; z<r; ++z)
if(s->bits & (HIGHBIT>>z)) {
y = s->xy / BOXWIDTH, x = s->xy % BOXWIDTH;
v = y, y = x, x = z;
for(k=0; k<m; ++k)
if(orib3[k].xy == y*BOXWIDTH+x) break;
if(k == m) orib3[k].xy = y*BOXWIDTH + x, orib3[k].bits = 0, ++m;
orib3[k].bits |= (HIGHBIT>>v);
}
o_list[sortSlices(m)].spin2 = i;
}

}

#if DEBUG
o = o_list;
for(i=0; i<o_max; ++i, ++o) {
if(o->hr >= 0) printf("%d:", o->hr), print_o(o_list+o->hr), printf("hr from %d:", i), print_o(o);
if(o->vr >= 0) printf("%d:", o->vr), print_o(o_list+o->vr), printf("vr from %d:", i), print_o(o);
if(o->dxy >= 0) printf("%d:", o->dxy), print_o(o_list+o->dxy), printf("dxy from %d:", i), print_o(o);
if(o->dxz >= 0) printf("%d:", o->dxz), print_o(o_list+o->dxz), printf("dxz from %d:", i), print_o(o);
if(o->dyz >= 0) printf("%d:", o->dyz), print_o(o_list+o->dyz), printf("dyz from %d:", i), print_o(o);
if(o->dr2 >= 0) printf("%d:", o->dr2), print_o(o_list+o->dr2), printf("dr2 from %d:", i), print_o(o);
if(o->r1 >= 0) printf("%d:", o->r1), print_o(o_list+o->r1), printf("r1 from %d:", i), print_o(o);
if(o->r2 >= 0) printf("%d:", o->r2), print_o(o_list+o->r2), printf("r2 from %d:", i), print_o(o);
if(o->r3 >= 0) printf("%d:", o->r3), print_o(o_list+o->r3), printf("r3 from %d:", i), print_o(o);
if(o->spin1 >= 0) printf("%d:", o->spin1), print_o(o_list+o->spin1), printf("spin1 from %d:", i), print_o(o);
if(o->spin2 >= 0) printf("%d:", o->spin2), print_o(o_list+o->spin2), printf("spin2 from %d:", i), print_o(o);
}
#endif
}

static void moreOrientations(void)
{
const struct ORIENT *o;
struct ORIENT *q;
const struct SLICE *s;
int i, k, x, y;

o = o_list;
q = o_list + o_max;
for(i=0; i<o_max; ++i, ++o) {
x = o->x, y = o->y;
while(x && y < o->rng_y-1) {
--x, ++y;
s = o->pattern;
for(k=0; k<o->slices; ++k, ++s) {
if(s->xy != y*BOXWIDTH + x) continue;
if(isNotHighbit(s->bits)) continue;
// anchor this orientation on this cube
if(o_max2 == O_MAX)
bailout("too many extra orientations, limit %d", O_MAX);
*q = *o;
q->x = x, q->y = y;
q->near = 0;
++o_max2, ++q;
break;
}
}
}
#if DEBUG
printf("%d extra orientations\n", o_max2 - o_max);
#endif
}

static shapebits fromHex(char c)
{
c = tolower(c);
if(c >= 'a') c -= ('a'-'9'-1);
return c-'0';
}

static const uchar nibbleCount[] = {0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4};
// assumes the base piece is in orib1
static void compileRotations(void)
{
int r1, r2, r3, r4;
const struct ORIENT *o;
memcpy(orib2, orib1, sizeof(orib1));
for(r1=0; r1<3; ++r1) {
for(r2=0; r2<2; ++r2) {
for(r3=0; r3<2; ++r3) {
for(r4=0; r4<4; ++r4) {

// checkerboad can be run once for all rotations,
// not so for checkerstripe.
if(!nsqMix && !(nsq&1)) {
int x, y, z, i = 0;
for(x=0; x<REPDIAMETER; ++x)
for(y=0; y<REPDIAMETER; ++y)
for(z=0; z<REPDIAMETER; ++z)
if(orib1[x][y][z])
if((x+y)&1) ++i; else --i;
if(i < 0) i = -i;
i &= 2;
if(!o_max) csflag = i;
else if(i != csflag) csflag = 0;
i = 0;
for(x=0; x<REPDIAMETER; ++x)
for(y=0; y<REPDIAMETER; ++y)
for(z=0; z<REPDIAMETER; ++z)
if(orib1[x][y][z])
if(x&1) ++i; else --i;
if(i < 0) i = -i;
i &= 2;
if(!o_max) cpflag = i;
else if(i != cpflag) cpflag = 0;
}

pulldown(r1, r2, r3);
counterclockwise();
memcpy(orib1, orib2, sizeof(orib2));
}
y_mirror();
memcpy(orib1, orib2, sizeof(orib2));
}
point_mirror();
memcpy(orib1, orib2, sizeof(orib2));
}
xyz_spin();
memcpy(orib1, orib2, sizeof(orib2));
}

o = o_list;
for(r1=0; r1<o_max; ++r1, ++o)
if(o->ambig && !(o->zflip&8)) {
printf("orientation %d is unexpectedly ambiguous ", o->ono);
print_o(o);
}

#if DEBUG
r2 = 0;
o = o_list;
for(r1=0; r1<o_max; ++r1, ++o)
r2 += !o->inspace;
printf("%d orientations", o_max);
if(r2) printf(" %d chiral", r2);
printf("\n");
#endif
}

// Convert a hex-format representation of a polyomino into its bitmap,
// and derive all its rotations.
static const char *piecename;
static void stringPiece(const char *hexrep)
{
int i, x, y, z;
shapebits mask;
const char *s = hexrep;
char c;
int nsqFirst = -1;
// for the connection test
int nsq1, nsq2;
uchar qx[NSQ], qy[NSQ], qz[NSQ];

piecename = hexrep;
setMaxDimension = 0, setMinDimension = NSQ;

while(*s) {
if(setSize >= SETSIZE) bailout("too many pieces in the set, limit %d", SETSIZE);
memset(orib4, 0, sizeof(orib4));
nsq = 0;
i = y = 0;

while((c = *s) != 0 && c != '_' && c != '=') {
if(c == '!') { ++s; ++y; i=0;
if(y >= REPDIAMETER) bailout("polyomino is too wide, limit %d rows", REPDIAMETER);
continue;
}
if(!isxdigit(c)) bailout("character %c unrecognized, hex digit expected", c);
if(!isxdigit(s[1])) bailout("character %c unrecognized, hex digit expected", s[1]);
if(i >= REPDIAMETER) bailout("polyomino is too wide, limit %d rows", REPDIAMETER);
mask = (fromHex(c)<<4) | fromHex(s[1]);
mask <<= 8;
s += 2;
if(*s == '+') ++s, mask |= 0x80;
else if(*s == '{') {
++s;
if(!isxdigit(s[0]) || !isxdigit(s[1]) || s[2] != '}')
bailout("improper {xx} sequence for the second 8 bits", 0);
mask |= fromHex(s[0])<<4;
mask |= fromHex(s[1]);
s += 3;
}
/* this line was fine in 2d, but not in 3d
if(!mask) bailout("zero row in polyomino", 0);
*/
nsq += nibbleCount[mask>>12];
nsq += nibbleCount[(mask>>8)&0xf];
nsq += nibbleCount[(mask>>4)&0xf];
nsq += nibbleCount[(mask)&0xf];
orib4[i][y] = mask;
++i;
} /* loop gathering the rows in this piece */

if(!nsq) bailout("empty piece", 0);
if(nsq > NSQ)
bailout("too many squares in the given polyomino, limit %d", NSQ);
if(nsqFirst < 0) nsqFirst = nsq;
else if(nsq != nsqFirst) nsqMix = 1;

// unpack into orib1
memset(orib1, 0, sizeof(orib1));
nsq1 = nsq2 = 0;
for(x=0; x<REPDIAMETER; ++x)
for(y=0; y<REPDIAMETER; ++y) {
mask = orib4[x][y];
for(z=0; z<REPDIAMETER; ++z) {
if((orib1[x][y][z] = isHighbit(mask)) && !nsq2)
nsq2 = 1, qx[0] = x, qy[0] = y, qz[0] = z;
mask <<= 1;
}
}

// connection test, which is more important here in 3 dimensions,
// where it is easier to make a mistake.
while(nsq1 < nsq2) {
x = qx[nsq1], y = qy[nsq1], z = qz[nsq1];
++nsq1;
if(x > 0 && orib1[x-1][y][z]) {
for(i=0; i<nsq2; ++i)
if(qx[i] == x-1 && qy[i] == y && qz[i] == z) break;
if(i == nsq2)
qx[i] = x-1, qy[i] = y, qz[i] = z, ++nsq2;
}
if(y > 0 && orib1[x][y-1][z]) {
for(i=0; i<nsq2; ++i)
if(qx[i] == x && qy[i] == y-1 && qz[i] == z) break;
if(i == nsq2)
qx[i] = x, qy[i] = y-1, qz[i] = z, ++nsq2;
}
if(z > 0 && orib1[x][y][z-1]) {
for(i=0; i<nsq2; ++i)
if(qx[i] == x && qy[i] == y && qz[i] == z-1) break;
if(i == nsq2)
qx[i] = x, qy[i] = y, qz[i] = z-1, ++nsq2;
}
if(x < REPDIAMETER-1 && orib1[x+1][y][z]) {
for(i=0; i<nsq2; ++i)
if(qx[i] == x+1 && qy[i] == y && qz[i] == z) break;
if(i == nsq2)
qx[i] = x+1, qy[i] = y, qz[i] = z, ++nsq2;
}
if(y < REPDIAMETER-1 && orib1[x][y+1][z]) {
for(i=0; i<nsq2; ++i)
if(qx[i] == x && qy[i] == y+1 && qz[i] == z) break;
if(i == nsq2)
qx[i] = x, qy[i] = y+1, qz[i] = z, ++nsq2;
}
if(z < REPDIAMETER-1 && orib1[x][y][z+1]) {
for(i=0; i<nsq2; ++i)
if(qx[i] == x && qy[i] == y && qz[i] == z+1) break;
if(i == nsq2)
qx[i] = x, qy[i] = y, qz[i] = z+1, ++nsq2;
}
}
if(nsq2 != nsq) bailout("piece is not connected, %d squares", nsq2);

// see if the checkerboard argument applies
if(!nsqMix && !(nsq&1)) {
i = 0;
for(x=0; x<REPDIAMETER; ++x)
for(y=0; y<REPDIAMETER; ++y)
for(z=0; z<REPDIAMETER; ++z)
if(orib1[x][y][z])
if((x+y+z)&1) ++i; else --i;
if(i < 0) i = -i;
i &= 2;
if(!o_max) cbflag = i;
else if(i != cbflag) cbflag = 0;
} /* even squares */

compileRotations();
if(nsqMix) cbflag = csflag = cpflag = 0;

if(*s == '=') {
int j = strtol(s+1, (char**)&s, 10);
if(j <= 0 || j > MAXORDER) bailout("quantity out of range, limit 1 to %d", MAXORDER);
qty[setSize] = j, qtyc[setSize] = -1, qtySpec = 1, qtyTotal += nsq * j, qtyOrder += j;
if(j > 1) qtyOne = 0;
if(*s == '=') {
j = strtol(s+1, (char**)&s, 10);
if(j < 0 || j > MAXORDER) bailout("quantity out of range, limit 0 to %d", MAXORDER);
qtyc[setSize] = j, qtyTotal += nsq * j, qtyOrder += j;
if(j > 1) qtyOne = 0;
}
if(*s && *s != '_') bailout("unexpected character %c after quantity specifier", *s);
}

if(*s) ++s;
++setSize;
o_max2 = o_max;
} /* loop over pieces in the set */

if(cbflag) {
puts("checkerboard upgrade");
ordFactor = 2;
}
if(csflag) {
puts("checkerstripe upgrade");
ordFactor = 2;
}
if(cpflag) {
puts("checkerplane upgrade");
ordFactor = 2;
}

if(!qtySpec) qtyOne = 0;
if(qtySpec) {
for(i=0; i<setSize; ++i)
if(!qty[i]) bailout("each piece in the set should have a quantity specifier", 0);
}

stopgap = (setMinDimension&1) ? setMinDimension : setMinDimension - 1;
forgetgap = stopgap/2 - setMaxDimension/2 - 1;
if(forgetgap >= 0) bailout("forget gap should be negative, not %d", forgetgap);

/* I don't think we need this.
moreOrientations();
*/
}

// find the highest empty bit in a short
// This is the opposite order of the routine in trec.c
static char lowEmpty[65536];
static void lowEmptySet(void)
{
ushort mask;
int j, k;
for(j=0; j<65536; ++j) {
mask = j;
for(k=0; isHighbit(mask); ++k, mask<<=1)  ;
lowEmpty[j] = k;
}
}

static const shapebits revNibble[] = {0,8,4,12,2,10,6,14,1,9,5,13,3,11,7,15};
static shapebits reverseShort(shapebits v)
{
return revNibble[v>>12] |
(revNibble[(v>>8)&0xf]<<4) |
(revNibble[(v>>4)&0xf]<<8) |
(revNibble[v&0xf]<<12);
}
static uchar reverseByte(uchar v)
{
return revNibble[v>>4] |
(revNibble[v&0xf]<<4);
}

// Here is the structure for the node.
struct NODE {
long parent; // where this node came from
long hash; // hash value of this pattern
short depth; // the depth of this node
uchar gap; // the gap of this pattern
uchar dead;
union {
uchar b[BOXWIDTH*BOXWIDTH]; // bytes
ushort s[BOXWIDTH*BOXWIDTH]; // shorts
} pattern;
};
static long nodesPending; // nodes yet to process
static long nodesCache; // nodes stored in cache
static int hwm; // high water mark on the cache

static void setBestZ(void)
{
int denom = nsq * ordFactor;
maxDepth = boxOrder*nsq/boxArea;
do {
if(((long)maxDepth*boxArea) % denom) continue;
break;
} while(--maxDepth);

// We have already covered rows below 2*curDepth + stopgap.
minDepth = 2*curDepth + stopgap;
// We already checked skinnier rectangles.
if(dim_x > minDepth) minDepth = dim_x;
do {
if(((long)minDepth*boxArea) % denom) continue;
break;
} while(++minDepth);
}

static struct NODE floor;
static void initFiles(void);
static int solve(void);
static void expandNode(long this_idx, const uchar *base_b);
static void expandNodes(void);
static void markOldNodes(void);
static void inCorner(void);

int main(int argc, const char **argv)
{
char *u;

++argv, --argc;
while(argc && argv[0][0] == '-') {
// -l is least colors, within reason
if(argc && !strcmp(*argv, "-l"))
++argv, --argc, robin = 0;
if(argc && !strcmp(*argv, "-c"))
++argv, --argc, countFlag = 1;
if(argc && !strcmp(*argv, "-a"))
++argv, --argc, countFlag = 2;
if(argc && argv[0][0] == '-' && argv[0][1] == 'm' && isdigit(argv[0][2]))
megaNodes = atoi(argv[0]+2), doNodes = 1, ++argv, --argc;
if(argc && argv[0][0] == '-' && argv[0][1] == 'd' && isdigit(argv[0][2]))
showdiag = atoi(argv[0]+2), ++argv, --argc;
}

if(argc != 2 && argc != 4)
bailout("usage: 3dbox [-l] [-dnn] [-c] [-a] [-mnnn] piece_set width depth height[@restart] | 3dbox piece_set order", 0);

lowEmptySet();
stringPiece(argv[0]);

if(!hascorner) bailout("piece has no corner, cannot fill a box", 0);

if(nsqMix && (doNodes || argc == 2)) bailout("all polyominoes in the set must have the same number of squares", 0);

if(countFlag) {
char opt = (countFlag == 1 ? 'c' : 'a');
if(doNodes || argc == 2)
bailout("-%c option can only be used when filling a specific box", opt);
if(!(qtySpec&qtyOne))
bailout("-%c option requires exactly one of each piece", opt);
}

if(argc == 4) {
dim_x = atoi(argv[1]);
dim_y = atoi(argv[2]);
dim_z = atoi(argv[3]);
boxArea = dim_x * dim_y;
boxVolume = boxArea * dim_z;
if(!nsqMix) {
if(boxVolume % nsq) bailout("volume %d does not admit a whole number of pieces", boxVolume);
boxOrder = boxVolume / nsq;
} else if(qtySpec) {
if(boxVolume != qtyTotal) bailout("box volume is not consistent with the volume of the pieces %d", qtyTotal);
boxOrder = qtyOrder;
} else bailout("all polyominoes in the set must have the same number of squares", 0);
if(boxOrder > MAXORDER) bailout("order to large, limit %d", MAXORDER);
if(dim_y > dim_x || dim_x > dim_z)
bailout("dimensions must be y x z increasing", 0);
if(dim_x > BOXWIDTH)
bailout("x dimension too large, limit %d", BOXWIDTH);
swingSet();

if(!doNodes) {

if(countFlag) {
char opt = (countFlag == 1 ? 'c' : 'a');
int j;
struct ORIENT *o;
if(countFlag == 1) printf("%d orientations\n", o_max);
for(j=0; j<o_max; ++j) {
o = o_list + j;
if(dim_x < o->rng_x || dim_y < o->rng_y || dim_z < o->rng_z) // doesn't fit
o->zero_spin = o->zero_dxy = o->zero_dxz = o->zero_dyz = o->zero_hr = o->zero_vr = o->zero_zr = 0;
if(dim_x != dim_y) o->zero_dxy = 0;
if(dim_x != dim_z) o->zero_dxz = 0;
if(dim_y != dim_z) o->zero_dyz = 0;
if(dim_x != dim_y || dim_x != dim_z) o->zero_spin = 0;
if(dim_x != o->rng_x) o->zero_hr = 0;
if(dim_y != o->rng_y) o->zero_vr = 0;
if(dim_z != o->rng_z) o->zero_zr = 0;
}
if(opt == 'a') {
#if DEBUG
for(j=0; j<o_max; ++j) {
o = o_list + j;
if(o->zero_dxy | o->zero_dxz | o->zero_dyz) {
printf("warning: equivalent solutions will be generated by diagonal reflection if piece %d is at the origin: ", o->pno);
print_o(o);
}
if(o->zero_spin) {
printf("warning: equivalent solutions will be generated by spin if piece %d is at the origin: ", o->pno);
print_o(o);
}
if(o->zero_hr) {
printf("warning: equivalent solutions will be generated by horizontal reflection if piece %d is at the origin: ", o->pno);
print_o(o);
}
if(o->zero_vr) {
printf("warning: equivalent solutions will be generated by vertical reflection if piece %d is at the origin: ", o->pno);
print_o(o);
}
if(o->zero_zr) {
printf("warning: equivalent solutions will be generated by z reflection if piece %d is at the origin: ", o->pno);
print_o(o);
}
}
#endif
}
}

printf("order %d\n", boxOrder);
printf("box %d by %d by %d\n", dim_x, dim_y, dim_z);
solve();
if(countFlag) {
if(oc_2%2) bailout("why isn't oc_2 %d divisible by 2?", oc_2);
if(oc_3%3) bailout("why isn't oc_3 %d divisible by 3?", oc_3);
if(oc_4%4) bailout("why isn't oc_4 %d divisible by 4?", oc_4);
if(oc_6%6) bailout("why isn't oc_6 %d divisible by 6?", oc_6);
countSol -= oc_2/2;
countSol -= oc_3/3 * 2;
countSol -= oc_4/4 * 3;
countSol -= oc_6/6 * 5;
if(countFlag == 2) puts("");
printf("%d solutions\n", countSol);
}
return 0;
}

if(qtySpec) bailout("cannot combine node search with quantity specifiers", 0);

u = strchr(argv[3], '@');
if(u && isdigit(u[1])) restart = atoi(u+1);

// At this point dim_z doesn't mean anything - until we find a solution.
// Search up through the levels, with dim_x and dim_y as footprint,
// up to boxOrder.
curDepth = 0;
setBestZ();
if(maxDepth < dim_x) return 0;
setbuf(stdout, 0);
initFiles();
printf("?%dx%d", dim_x, dim_y);
expandNode(0, floor.pattern.b);
while(nodesPending) {
int j;
printf(" @");
if(restart < 0) markOldNodes();
printf("%d", curDepth);
j = nodesCache / (maxNodes/10);
if(j != hwm) { hwm = j; printf(" %%%d0", j); }
expandNodes();
restart = -1;
restartParent = 0;
++curDepth;
setBestZ(); /* also resets minDepth */
if(stopsearch) break;
if(maxDepth < dim_x) break;
}
printf(" :%ld\n", nodesCache);
return 0;
}

if(doNodes) bailout("order search using nodes is not yet implemented", 0);
if(qtySpec) bailout("order search cannot be combined with quantity specifiers", 0);

boxOrder = atoi(argv[1]);
// order 0 is a special case
if(!boxOrder) inCorner();
while(1) {
while(boxOrder % ordFactor) ++boxOrder;
if(boxOrder > MAXORDER) bailout("order to large, limit %d", MAXORDER);
printf("order %d\n", boxOrder);
boxVolume = boxOrder * nsq;
// We're not considering flat boxes here, even if the piece is flat.
// Nor any box narrower than the piece itself.
for(dim_y = setMinDimension > 2 ? setMinDimension : 2; dim_y*dim_y*dim_y <= boxVolume; ++dim_y) {
if(dim_y == 2 && flat3) continue;
if(boxVolume % dim_y) continue;
for(dim_x = dim_y; dim_y*dim_x*dim_x <= boxVolume; ++dim_x) {
if((boxVolume/dim_y) % dim_x) continue;
if(dim_x > BOXWIDTH) bailout("box too wide, limit %d", BOXWIDTH);
dim_z = boxVolume / dim_y / dim_x;
printf("box %d by %d by %d\n", dim_x, dim_y, dim_z);
swingSet();
solve();
}
}
++boxOrder;
}

return 0;
}

static struct SF { // like a stack frame
schar x, y, z; // where piece is placed
schar increase;
short onum;
short xy; // y*BOXWIDTH + x
short breakLine;
short mzc;
int near;
} stack[MAXORDER];

static shapebits ws[BOXWIDTH*BOXWIDTH]; // workspace for specific box solve

// This only prints bytes, not shorts
static void print_ws(void)
{
int x, y;
for(y=0; y<dim_y; ++y) {
for(x=0; x<dim_x; ++x)
printf("%02x", ws[y*BOXWIDTH+x]>>8);
printf("|");
}
printf("\n");
}

static void print_node(const struct NODE *n)
{
int x, y;
shapebits mask;
for(y=0; y<dim_y; ++y) {
for(x=0; x<dim_x; ++x) {
// I believe c upgrades unsigned char to int, as in c << 8, but let's cast to be sure.
mask = r_shorts ? n->pattern.s[y*dim_x+x] : ((int)n->pattern.b[y*dim_x+x]<<8);
// only print the first byte.
printf("%02x", (mask>>8));
}
printf("|");
}
printf("\n");
}

#define COLORS 26
static uchar used[COLORS];
static int last_ci; // last color index
static char assignColor(void)
{
int k;
char c = '*';
if(robin) {
k = last_ci;
do { ++k;
if(k == COLORS) k = 0;
if(!used[k]) { c = k+'a'; last_ci = k; break; }
} while(k != last_ci);
} else {
for(k=0; k<COLORS; ++k) if(!used[k]) break;
if(k < COLORS) c = 'a'+k;
}
return c;
}

#define B_LOC(x,y,z) b[dim_x*dim_y*(z0+z) + dim_x*(y0+y) + (x0+x)]
static void print_solution(void)
{
char *b = malloc(boxVolume);
const struct ORIENT *o;
const struct SF *p;
int lev, x, y, z, k;
int x0, y0, z0;
char c;
uchar badchar = 0;

memset(b, '?', boxVolume);
// all the question marks should disappear
last_ci = COLORS - 1;

for(lev=0; lev<boxOrder; ++lev) {
p = stack + lev;
o = o_list + p->onum;
x0 = p->xy % BOXWIDTH, y0 = p->xy / BOXWIDTH, z0 = p->z;

// check for neighboring colors
memset(used, 0, sizeof(used));
for(k=0; k<o->slices; ++k) {
const struct SLICE *s = o->pattern + k;
y = s->xy/BOXWIDTH, x = s->xy%BOXWIDTH;
for(z=0; z<o->rng_z; ++z)
if(s->bits & (HIGHBIT >> z)) {
if(x0+x > 0 && (c = B_LOC(x-1,y,z)) != '?' && c != '*')
used[c-'a'] = 1;
if(y0+y > 0 && (c = B_LOC(x,y-1,z)) != '?' && c != '*')
used[c-'a'] = 1;
if(z0+z > 0 && (c = B_LOC(x,y,z-1)) != '?' && c != '*')
used[c-'a'] = 1;
if(x0+x < dim_x-1 && (c = B_LOC(x+1,y,z)) != '?' && c != '*')
used[c-'a'] = 1;
if(y0+y < dim_y-1 && (c = B_LOC(x,y+1,z)) != '?' && c != '*')
used[c-'a'] = 1;
if(z0+z < dim_z-1 && (c = B_LOC(x,y,z+1)) != '?' && c != '*')
used[c-'a'] = 1;
}
}

c = assignColor();

for(k=0; k<o->slices; ++k) {
const struct SLICE *s = o->pattern + k;
y = s->xy/BOXWIDTH, x = s->xy%BOXWIDTH;
for(z=0; z<o->rng_z; ++z)
if(s->bits & (HIGHBIT >> z))
B_LOC(x,y,z) = c;
}
}

x0 = y0 = z0 = 0;
// not sure the best way to present this.
// I'm going to go for the fewest layers.
for(y=0; y<dim_y; ++y) {
if(y) {
for(z=0; z<dim_z; ++z)
printf("-");
printf("\n");
}
for(x=0; x<dim_x; ++x) {
for(z=0; z<dim_z; ++z) {
c = B_LOC(x,y,z);
printf("%c", c);
if(c == '*' || c == '?') badchar = 1;
}
printf("\n");
}
}
if(badchar) puts("bad characters in the box");
free(b);
}
#undef B_LOC

static void found_solution(const struct SF *p)
{
int corner_ono, corner_piece, thispiece;
int oc; // overcount
int j;
int x0, y0;
const struct ORIENT *q;
const struct SF *w;

if(!countFlag) {
puts("solution!");
print_solution();
exit(0);
}

corner_ono = stack[0].onum;
q = o_list + corner_ono;
corner_piece = q->pno;
if(dim_x == q->rng_x && dim_y == q->rng_y && q->farbits&0x10 ||
dim_x == q->rng_x && dim_z == q->rng_z && q->farbits&2 ||
dim_x == q->rng_x && dim_y == q->rng_y && dim_z == q->rng_z && q->farbits&4 ||
dim_y == q->rng_y && dim_z == q->rng_z && q->farbits&8) {
printf("Piece connects the origin with a nonadjacent corner, I am not programmed to respond in this area.\n");
print_o(q);
print_solution();
exit(1);
}

// look for lesser pieces on the ceiling
for(w = stack+1; w < p; ++w) {
const struct ORIENT *r = o_list + w->onum;
if(w->z + r->rng_z < dim_z) continue; // not on the ceiling
thispiece = r->pno;
if(thispiece > corner_piece) continue; // lesser, that's good
// same piece, could reach up to the ceiling from the origin, or,
// one could be spacial and the other chiral.
x0 = w->x - r->x;
y0 = w->y - r->y;
if(x0 == 0 && y0 == 0 && r->farbits&1) {
if(thispiece < corner_piece) return;
}
if(x0 + r->rng_x == dim_x && y0 == 0 && r->farbits&2) {
if(thispiece < corner_piece) return;
}
if(x0 + r->rng_x == dim_x && y0 + r->rng_y == dim_y && r->farbits&4) {
if(thispiece < corner_piece) return;
}
if(x0 == 0 && y0 + r->rng_y == dim_y && r->farbits&8) {
if(thispiece < corner_piece) return;
}
}

if(countFlag == 2) puts("");

if(qtyc[corner_piece] > 0) {
printf("chiral piece at the origin, I can't handle this situation, please put your chiral pieces last in the set.\n");
print_o(q);
print_solution();
exit(1);
}

// ok, none of the pieces in the corners of the ceiling are lesser.
// See if the piece at the origin is too weird.
// If it's reasonable, establish the reflection overcount.
oc = 1;
if(q->zero_spin) {
if(q->zero_hr | q->zero_vr | q->zero_zr) {
printf("spin cannot combine with a lateral reflection\n");
print_o(q);
exit(1);
}
j = q->zero_dxy + q->zero_dxz + q->zero_dyz;
if(j && j != 3) {
printf("spin cannot combine with 1 or 2 diagonal reflections\n");
print_o(q);
exit(1);
}
if(j) {
if(countFlag == 2) { printf("duplicate 6 spin + reflect "); print_o(q); }
oc = 6;
} else {
if(countFlag == 2) { printf("duplicate 3 spin "); print_o(q); }
oc = 3;
}
} else {
j = q->zero_hr + q->zero_vr + q->zero_zr;
if(j > 1) {
printf("multiple lateral reflections\n");
print_o(q);
exit(1);
}
j = q->zero_dxy + q->zero_dxz + q->zero_dyz;
if(j > 1) {
printf("multiple diagonal reflections\n");
print_o(q);
exit(1);
}
if(q->zero_zr && q->zero_dxz|q->zero_dyz ||
q->zero_hr && q->zero_dxz|q->zero_dxy ||
q->zero_vr && q->zero_dyz|q->zero_dxy) {
printf("incompatible lateral and diagonal reflections\n");
print_o(q);
exit(1);
}
if(q->zero_zr) {
if(q->zero_dxy) {
if(countFlag == 2) { printf("duplicate 4 z + xy "); print_o(q); }
oc = 4;
} else {
if(countFlag == 2) { printf("duplicate 2 z "); print_o(q); }
oc = 2;
}
} else if(q->zero_dxy) {
if(countFlag == 2) { printf("duplicate 2 xy "); print_o(q); }
oc = 2;
}
if(q->zero_hr) {
if(q->zero_dyz) {
if(countFlag == 2) { printf("duplicate 4 x + yz "); print_o(q); }
oc = 4;
} else {
if(countFlag == 2) { printf("duplicate 2 x "); print_o(q); }
oc = 2;
}
} else if(q->zero_dyz) {
if(countFlag == 2) { printf("duplicate 2 yz "); print_o(q); }
oc = 2;
}
if(q->zero_vr) {
if(q->zero_dxz) {
if(countFlag == 2) { printf("duplicate 4 y + xz "); print_o(q); }
oc = 4;
} else {
if(countFlag == 2) { printf("duplicate 2 y "); print_o(q); }
oc = 2;
}
} else if(q->zero_dxz) {
if(countFlag == 2) { printf("duplicate 2 xz "); print_o(q); }
oc = 2;
}
}

++countSol;
if(oc == 2) ++oc_2;
if(oc == 3) ++oc_3;
if(oc == 4) ++oc_4;
if(oc == 6) ++oc_6;
if(countFlag == 2) print_solution();
}

static int solve(void)
{
int lev = -1;
struct SF *p = stack - 1;
const struct ORIENT *o;
const struct SLICE *s;
int x, y, z, j, k, near = 0;
int x0, y0;

memset(ws, 0, sizeof(ws));

advance:
if(++lev == boxOrder) {
found_solution(++p);
goto backup;
}
if(lev == MAXORDER) bailout("placement stack overflow %d", lev);

// find location to place the piece
if(!lev) x = y = z = 0;
else {
x = p->x, y = p->y, z = p->z;

relocate:
// Assumes dim_x >= dim_y.
while(isHighbit(ws[y*BOXWIDTH+x])) {
++y, --x;
if(y == dim_y) {
x += dim_y, y = 0;
++x; // next diagonal
while(x >= dim_x) ++y, --x;
if(y == dim_y) break;
continue;
}
if(x < 0) x += y+1, y = 0;
}

if(y == dim_y) { // have to push workspace down
int r_x, r_y;
j = REPDIAMETER;
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x) {
k = lowEmpty[ws[y*BOXWIDTH+x]];
if(k < j) j = k, r_x = x, r_y = y;
}
if(!j || j == REPDIAMETER) bailout("increase level is %d", j);
p->increase = j;
z += j;
#if DEBUG
printf("push %d\n", j);
#endif
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
ws[y*BOXWIDTH+x] <<= j;
x = y = 0;
goto relocate;
}
}
++p;
p->x = x, p->y = y, p->z = z;
p->increase = 0;

#if NEAR
// Improves efficiency by 30%
near = 0;
if(y < dim_y-1) {
if(ws[x+BOXWIDTH*(y+1)]&(HIGHBIT>>0)) near |= 1;
if(!x || ws[x-1+BOXWIDTH*(y+1)]&(HIGHBIT>>0)) near |= 2;
if(ws[x+BOXWIDTH*(y+1)]&(HIGHBIT>>1)) near |= 4;
if(!x || ws[x-1+BOXWIDTH*(y+1)]&(HIGHBIT>>1)) near |= 8;
} else near |= 15;
if(!y || ws[x+BOXWIDTH*(y-1)]&(HIGHBIT>>1)) near |= 0x10;
if(!x || !y || ws[x-1+BOXWIDTH*(y-1)]&(HIGHBIT>>1)) near |= 0x20;
if(!x || ws[x-1+BOXWIDTH*(y)]&(HIGHBIT>>1)) near |= 0x40;
if(ws[x+BOXWIDTH*(y)]&(HIGHBIT>>1)) near |= 0x80;
if(x < dim_x-1) {
if(ws[x+1+BOXWIDTH*(y)]&(HIGHBIT>>0)) near |= 0x100;
if(y == dim_y-1 || ws[x+1+BOXWIDTH*(y+1)]&(HIGHBIT>>0)) near |= 0x200;
} else near |= 0x300;
p->near = near;
#endif

#if DEBUG
printf("locate %d,%d,%d near %x\n", x, y, z, near);
#endif

p->onum = -1;
o = o_list - 1;

next:
if(++p->onum == o_max) goto backup;
++o;
#if NEAR
if(p->near & o->near) goto next;
#endif
if(qtySpec) {
int piece = o->pno;
if(qtyc[piece] >= 0) { // chirality specified
if(o->inspace && qu[piece] == qty[piece]) goto next;
if(!o->inspace && quc[piece] == qtyc[piece]) goto next;
} else {
if(qu[piece] == qty[piece]) goto next;
}
}
x0 = p->x - o->x;
if(x0 < 0) goto next;
if(x0 + o->rng_x > dim_x) goto next;
y0 = p->y - o->y;
if(y0 < 0) goto next;
if(y0 + o->rng_y > dim_y) goto next;
if(p->z + o->rng_z > dim_z) goto next;
// the piece fits in the box.

// Look for collision.
p->xy = y0 * BOXWIDTH + x0;
s = o->pattern; k = o->slices; while(1) {
if(ws[p->xy+s->xy] & s->bits) goto next;
if(!--k) break;
++s;
}

#if SWING
if(!p->z) {
int swing;
int corner = stack[0].onum;
// I think this works even if p == stack, the first piece touches two corners.
// Note that we can't reflect if you specified 0 reflections of a piece.
// we need no quantity specifiers, or qtyOne
if((swing = o->hr) >= 0 && y0 == 0 && x0 + o->rng_x == dim_x && swing < corner && (!qtySpec || qtyOne)) goto next;
if((swing = o->vr) >= 0 && x0 == 0 && y0 + o->rng_y == dim_y && swing < corner && (!qtySpec || qtyOne)) goto next;
if((swing = o->r2) >= 0 && x0 + o->rng_x == dim_x && y0 + o->rng_y == dim_y && swing < corner) goto next;
if(dim_x == dim_y) {
if((swing = o->dr2) >= 0 && x0 + o->rng_x == dim_x && y0 + o->rng_y == dim_y && swing < corner && (!qtySpec || qtyOne)) goto next;
if((swing = o->dxy) >= 0 && x0 == 0 && y0 == 0 && swing < corner && (!qtySpec || qtyOne)) goto next;
if((swing = o->r1) >= 0 && y0 == 0 && x0 + o->rng_x == dim_x && swing < corner) goto next;
if((swing = o->r3) >= 0 && x0 == 0 && y0 + o->rng_y == dim_y && swing < corner) goto next;
}
if(x0 == 0 && y0 == 0) {
if(dim_x == dim_z && (swing = o->dxz) >= 0 &&  swing < corner && (!qtySpec || qtyOne)) goto next;
if(dim_y == dim_z) {
if((swing = o->dyz) >= 0 &&  swing < corner && (!qtySpec || qtyOne)) goto next;
// with y <= x <= z, x = y = z
if((swing = o->spin1) >= 0 &&  swing < corner) goto next;
if((swing = o->spin2) >= 0 &&  swing < corner) goto next;
}
}
}
#endif

#if DEBUG
printf("place{%d,%d,%d ", p->x, p->y, p->z);
print_o(o);
sleep(1);
#endif
if(p == stack && countFlag == 1) { printf("origin %d ", p->onum); print_o(o); }
s = o->pattern; k = o->slices; while(1) {
ws[p->xy+s->xy] |= s->bits;
if(!--k) break;
++s;
}
if(qtySpec) {
int piece = o->pno;
if(qtyc[piece] >= 0 && !o->inspace) ++quc[piece]; else ++qu[piece];
}
goto advance;

backup:
if(--lev < 0) {
if(!countFlag) puts("no solution");
return 0;
}
--p;
o = o_list + p->onum;
if(j = p->increase) {
shapebits m = ((short)HIGHBIT >> (j-1));
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
ws[y*BOXWIDTH+x] = ( ws[y*BOXWIDTH+x] >> j) | m;
p->increase = 0;
#if DEBUG
printf("pop %d\n", j);
#endif
}
// unplace piece
#if DEBUG
puts("}");
#endif
s = o->pattern; k = o->slices; while(1) {
ws[p->xy+s->xy] ^= s->bits;
if(!--k) break;
++s;
}
if(qtySpec) {
int piece = o->pno;
if(qtyc[piece] >= 0 && !o->inspace) --quc[piece]; else --qu[piece];
}
goto next;
}

static int nodeSize; // adjusted for dim_x and dim_y
static int curNodeWidth;

/*********************************************************************
I store nodes on disk, and a cache in memory.
I support up to 60 data files, each 2 gig - that's 120 gig of data.
This can hold as many as a billion nodes.
*********************************************************************/

static int fd[60] = // the file descriptors
{-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,};
static char filename[200];
static long nodesInFile;
static long nodesDisk; // nodes stored on disk
static long *hashIdx; // array of hashed indexes
static long lastDisk;
static long mon_idx; // for markOldNodes()
static long nodeStep;
static int workStep;
static long *workList; // the list of discovered nodes to expand
static int workEnd, workAlloc;

// Recache all the active nodes - as part of resumption.
static void readNode(long idx, struct NODE *buf);
static void recache(void)
{
static struct NODE rebuf, redest; /* for recaching */
int cutoff = curDepth + forgetgap;
int j;
long n, hash, idx;
long *hb;

hashIdx = emalloc(slopNodes * sizeof(long));
memset(hashIdx, 0, slopNodes*sizeof(long));
nodesCache = 0;
hwm = 0;

for(j=mon_idx; j<nodesDisk; ++j) {
if(j % 100000 == 0) printf(".");
readNode(j, &rebuf);
if(rebuf.dead) continue;
if(rebuf.depth <= cutoff) continue;

hash = rebuf.hash;
n = hash % slopNodes;

hb = hashIdx + n;
while(1) {
idx = *hb;
if(!idx) break;
idx &= 0x7fffffff;
readNode(idx, &redest);
if(redest.hash != hash) goto nextnode;
if(memcmp(redest.pattern.b, rebuf.pattern.b, curNodeWidth)) goto nextnode;
if(rebuf.depth < redest.depth) *hb = j;
goto nextDisk;
nextnode:
++n, ++hb;
if(n == slopNodes) n = 0, hb = hashIdx;
}

*hb = j;

if(++nodesCache >= maxNodes)
bailout("cannot recache at level %d", megaNodes);

nextDisk: ;
} /* loop recaching nodes on disk */
}

static void initFiles(void)
{
int flags;
int i;
static char *xptr;

if(!xptr) {
if(strlen(piecename) > sizeof(filename) - 24)
bailout("piecename string is too long", 0);
sprintf(filename, "dotile/%s", piecename);
mkdir(filename, 0777);
sprintf(filename, "dotile/%s/data-x", piecename);
xptr = strchr(filename, 'x');
}

if(workList) free(workList);
workAlloc = 60;
workList = emalloc(4*workAlloc);
workEnd = 0;

// assumes dim_x and dim_y are set
curNodeWidth = dim_x * dim_y * (1+r_shorts);
nodeSize = sizeof(struct NODE) - BOXWIDTH*BOXWIDTH*2 + curNodeWidth;
nodeSize = (nodeSize + 3) & ~3;
#if DEBUG
printf("node size %d\n", nodeSize);
#endif
nodesInFile = 0x7fff0000 / nodeSize;
maxNodes = megaNodes * 0x100000;
slopNodes = maxNodes / 8 * 9;
reachup = 0;

if(restart >= 0) { /* resume program */
long l;
struct NODE buf;
int cutoff = restart + forgetgap;

nodesDisk = 0;
for(i=0; i<60; ++i) {
flags = O_RDWR|O_BINARY;
*xptr = 'A' + i;
fd[i] = open(filename, flags, 0666);
if(fd[i] < 0) bailout("cannot reopen data file, errno %d", errno);
l = lseek(fd[i], 0, SEEK_END);
if(l%nodeSize) bailout("data file has bad length %ld", l);
nodesDisk += l/nodeSize;
} /* loop over files */

readNode(nodesDisk-1, &buf);
restartParent = buf.parent;
if(!restartParent) bailout("restartParent is 0", 0);
readNode(restartParent, &buf);
if(buf.depth != restart)
bailout("last depth was %d", buf.depth);

mon_idx = 0;
nodesPending = 0;
for(i=1; i<nodesDisk; ++i) {
readNode(i, &buf);
if(buf.dead) continue;
if(buf.depth == restart && i >= restartParent) ++nodesPending;
if(buf.depth > restart) ++nodesPending;
if(buf.depth > cutoff && !mon_idx) mon_idx = i;
if(buf.depth + buf.gap > reachup) reachup = buf.depth + buf.gap;
}

printf("Restart with %d nodes, %d pending\n", nodesDisk, nodesPending);

curDepth = restart;
recache();
return;
} /* resume program */

if(!hashIdx) hashIdx = emalloc(slopNodes * sizeof(long));
memset(hashIdx, 0, slopNodes*sizeof(long));
nodesCache = 0;
hwm = 0;
nodesDisk = 1; /* the initial node of all zeros is at location 0 */
mon_idx = 1;
nodesPending = 1;
curDepth = 0;

for(i=0; i<60; ++i) {
if(fd[i] > 0) close(fd[i]);
flags = O_CREAT|O_TRUNC|O_RDWR|O_BINARY;
*xptr = 'A' + i;
fd[i] = open(filename, flags, 0666);
if(fd[i] < 0) bailout("cannot create data file, errno %d", errno);
} /* loop over files */
}

static void appendWorkList(long idx)
{
if(workEnd == workAlloc) {
workAlloc = workAlloc/2 * 3;
workList = erealloc(workList, sizeof(long)*workAlloc);
}
workList[workEnd++] = idx;
printf("<");
// This node was pending before and is still pending so nodesPending doesn't change.
}

static void readNode(long idx, struct NODE *buf)
{
int i = idx / nodesInFile;
long offset = (idx%nodesInFile) * nodeSize;
elseek(fd[i], offset);
eread(fd[i], buf, nodeSize);
}

static void writeNode(long idx, const struct NODE *buf)
{
int i = idx / nodesInFile;
long offset = (idx%nodesInFile) * nodeSize;
elseek(fd[i], offset);
ewrite(fd[i], buf, nodeSize);
}

// I'm sure there are more efficient wayst to do this, but...
// I just wanted to get er done.
static const ulong hashprime = 2147483629;
static const ulong m_factor = (ulong)0x80000000 - hashprime;
// hash work areas
static ushort hw1[BOXWIDTH*BOXWIDTH], hw2[BOXWIDTH*BOXWIDTH];
static long computeHashShorts(ushort *p)
{
int x, y, r1, r2;
ulong hash = 0;
memcpy(hw1, p, curNodeWidth);
for(r1=0; r1<2; ++r1) {
if(dim_x == dim_y) {
for(r2=0; r2<4; ++r2) {
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
hw2[x*dim_x + (dim_y-1-y)] = hw1[y*dim_x + x];
memcpy(hw1, hw2, curNodeWidth);
if(r1 == 0 && r2 == 3) break;
if(memcmp(p, hw1, curNodeWidth) < 0)
memcpy(p, hw1, curNodeWidth);
}
} else {
for(r2=0; r2<2; ++r2) {
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
hw2[(dim_y-1-y)*dim_x + dim_x-1-x] = hw1[y*dim_x + x];
memcpy(hw1, hw2, curNodeWidth);
if(r1 == 0 && r2 == 1) break;
if(memcmp(p, hw1, curNodeWidth) < 0)
memcpy(p, hw1, curNodeWidth);
}
}
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
hw2[(dim_y-1-y)*dim_x + x] = hw1[y*dim_x + x];
memcpy(hw1, hw2, curNodeWidth);
}

for(x=0; x<dim_x*dim_y; ++x) {
// hash = (hash * 65536 + p[x]) mod hashprime
hash = ((hash&0x7fff)<<16) + ((hash>>15)*m_factor);
hash += p[x];
if(hash >= hashprime) hash -= hashprime;
}

if(hash >= hashprime) bailout("hash value too large", 0);
// 0 hash value is not allowed
if(!hash) hash = 1;
return (long)hash;
}

static long computeHashBytes(uchar *p)
{
int x, y, r1, r2;
ulong hash = 0;
uchar *hb1 = (uchar*)hw1;
uchar *hb2 = (uchar*)hw2;
memcpy(hb1, p, curNodeWidth);
for(r1=0; r1<2; ++r1) {
if(dim_x == dim_y) {
for(r2=0; r2<4; ++r2) {
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
hb2[x*dim_x + (dim_y-1-y)] = hb1[y*dim_x + x];
memcpy(hb1, hb2, curNodeWidth);
if(r1 == 0 && r2 == 3) break;
if(memcmp(p, hb1, curNodeWidth) < 0)
memcpy(p, hb1, curNodeWidth);
}
} else {
for(r2=0; r2<2; ++r2) {
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
hb2[(dim_y-1-y)*dim_x + dim_x-1-x] = hb1[y*dim_x + x];
memcpy(hb1, hb2, curNodeWidth);
if(r1 == 0 && r2 == 1) break;
if(memcmp(p, hb1, curNodeWidth) < 0)
memcpy(p, hb1, curNodeWidth);
}
}
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
hb2[(dim_y-1-y)*dim_x + x] = hb1[y*dim_x + x];
memcpy(hb1, hb2, curNodeWidth);
}

for(x=0; x<dim_x*dim_y; ++x) {
// hash = (hash * 65536 + p[x]) mod hashprime
hash = ((hash&0x7fff)<<16) + ((hash>>15)*m_factor);
hash += p[x];
if(hash >= hashprime) hash -= hashprime;
}

if(hash >= hashprime) bailout("hash value too large", 0);
// 0 hash value is not allowed
if(!hash) hash = 1;
return (long)hash;
}

static void markOldNode(long jdx, long hash)
{
long *hb;
long n, idx;

n = hash % slopNodes;
hb = hashIdx + n;
while(1) {
idx = *hb;
if(!idx) break;
if((idx&0x7fffffff) == jdx) {
if(idx == jdx) {
*hb |= 0x80000000;
--nodesCache;
}
return; /* found it */
}
++n, ++hb;
if(n == slopNodes) n = 0, hb = hashIdx;
}

/* Apparently it was already removed from the cache. */
}

static void markOldNodes(void)
{
long idx;
static struct NODE buf;
int cutoff = curDepth + forgetgap;
uchar firstBigger = 1;
if(cutoff < 0) return;
for(idx=mon_idx; idx<nodesDisk; ++idx) {
readNode(idx, &buf);
if(buf.dead) continue;
if(buf.depth > cutoff && firstBigger) { firstBigger = 0; mon_idx = idx; }
// This is == in trec.c. Not sure which is right.
if(buf.depth <= cutoff) markOldNode(idx, buf.hash);
} /* loop scanning all nodes on disk */
}

// Look for a node, vectoring through the cache.
// If generated is false, this is a complementary node in search of a solution.
// Return true if the node was found.
static int findNode( struct NODE *look, int generated, struct NODE *dest)
{
long *hb;
long n, hash, idx;
long empty = -1;
int j;

if(r_shorts)
hash = computeHashShorts(look->pattern.s);
else
hash = computeHashBytes(look->pattern.b);
n = hash % slopNodes;

hb = hashIdx + n;
while(1) {
idx = *hb;
if(!idx) break;
if(idx < 0) {
if(empty < 0) empty = n;
if(!generated) goto nextnode;
idx &= 0x7fffffff;
}

readNode(idx, dest);
if(dest->hash != hash) goto nextnode;
if(memcmp(dest->pattern.b, look->pattern.b, curNodeWidth)) goto nextnode;
if(generated && look->depth < dest->depth) {
dest->depth = look->depth;
dest->parent = look->parent;
writeNode(idx, dest);
if(look->depth == curDepth && idx < look->parent)
appendWorkList(idx);
} /* downgrading the depth */
return 1;
nextnode:
++n, ++hb;
if(n == slopNodes) n = 0, hb = hashIdx;
}

if(!generated) return 0;

j = look->depth + look->gap;
if(j > reachup) reachup = j;

if(nodesDisk >= 2140000000) bailout("too many nodes, limit 2 billion", 0);
if(nodesDisk/60 >= nodesInFile)
bailout("too many nodes for 60 data files on disk", 0);
look->hash = hash;
writeNode(nodesDisk, look);

if(empty >= 0) n = empty;
hb = hashIdx + n;
*hb = nodesDisk;
++nodesDisk;
++nodesPending;
if(++nodesCache >= maxNodes) {
printf("\nCache overflow; you will have to restart with a higher cache.\n%dx%d@%d^%d\n",
dim_x, dim_y, curDepth, megaNodes);
//inTerm = 1;
exit(1);
}

j = nodesCache / (maxNodes/10);
if(j == 10) j = 9;
if(j > hwm) { hwm = j; printf(" %%%d0", j); }

return 0;
}

#define MAXLAYER 200
static struct SF betweenstack[MAXLAYER];

/* place pieces between two nodes */
static int betweenNodes(const struct NODE *nb, const struct NODE *nt)
{
int lev = -1; // placement level
struct SF *p = betweenstack - 1;
const struct ORIENT *o;
const struct SLICE *s;
int x, y, z;
shapebits mask;
int diff = nt->depth - nb->depth;
int j, k, x0, y0;
shapebits b[BOXWIDTH*BOXWIDTH];

for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
if(r_shorts) {
mask = nt->pattern.s[y*dim_x + x];
mask ^= 0xffff;
mask >>= diff;
if(mask & nb->pattern.s[y*dim_x + x]) return 0;
mask |= nb->pattern.s[y*dim_x + x];
b[y*BOXWIDTH + x] = mask;
} else {
mask = ((int)nt->pattern.b[y*dim_x + x] << 8);
mask ^= 0xffff;
mask >>= diff;
if(mask & ((int)nb->pattern.b[y*dim_x + x] << 8)) return 0;
mask |= ((int)nb->pattern.b[y*dim_x + x] << 8);
b[y*BOXWIDTH + x] = mask;
}

advance:
if(++lev >= MAXLAYER)
bailout("placement stack overflow %d", MAXLAYER);

// find location to place the piece
x = y = 0;
if(!lev) z = 0; else z = p->z;

relocate:
while(isHighbit(b[y*BOXWIDTH + x])) {
++y, --x;
if(y == dim_y) {
x += dim_y, y = 0;
++x; // next diagonal
while(x >= dim_x) ++y, --x;
if(y == dim_y) break;
continue;
}
if(x < 0) x += y+1, y = 0;
}
if(y == dim_y) { // have to push workspace down
int r_x, r_y;
j = REPDIAMETER;
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x) {
k = lowEmpty[b[y*BOXWIDTH + x]];
if(k < j) j = k, r_x = x, r_y = y;
}
if(!j) bailout("between increase level is %d", j);
if(j == REPDIAMETER) return lev;
p->increase = j;
z += j;
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x) {
b[y*BOXWIDTH + x] <<= j;
b[y*BOXWIDTH + x] |= ((1<<j)-1);
}
x = y = 0;
goto relocate;
}

++p;
p->x = x, p->y = y, p->z = z;
p->increase = 0;
p->onum = -1;
o = o_list - 1;

next:
if(++p->onum == o_max) goto backup;
++o;
x0 = p->x - o->x;
if(x0 < 0) goto next;
if(x0 + o->rng_x > dim_x) goto next;
y0 = p->y - o->y;
if(y0 < 0) goto next;
if(y0 + o->rng_y > dim_y) goto next;
// the piece fits in the box.
// Look for collision.
p->xy = y0 * BOXWIDTH + x0;
s = o->pattern;
for(k=0; k<o->slices; ++k, ++s)
if(b[p->xy+s->xy] & s->bits) goto next;
s = o->pattern;
for(k=0; k<o->slices; ++k, ++s)
b[p->xy+s->xy] |= s->bits;
goto advance;

backup:
if(--lev < 0) return 0;
--p;
o = o_list + p->onum;
if(j = p->increase) {
shapebits m = ((short)HIGHBIT >> (j-1));
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
b[y*BOXWIDTH+x] = ( b[y*BOXWIDTH+x] >> j) | m;
z -= j;
p->increase = 0;
}
s = o->pattern;
for(k=0; k<o->slices; ++k, ++s)
b[p->xy+s->xy] ^= s->bits;
goto next;
}

#define B_LOC(x,y,z) board[dim_x*dim_y*(z0+z) + dim_x*(y0+y) + (x0+x)]
static void downToFloor(char *board, const struct NODE *top)
{
long parent;
int x, y, z, x0, y0, z0;
int k;
int added;
int r1, r2; // rotations in the D4 group
shapebits mask;
char c;
const struct SF *p;
const struct ORIENT *o;
const struct SLICE *s;
struct NODE n1, n2;
struct NODE n3; // just a work area

n2 = *top; // structure copy

do {
parent = n2.parent;
if(parent)
readNode(parent, &n1);
else
n1 = floor;

for(r1=0; r1<2; ++r1) {
if(dim_x == dim_y) {
for(r2=0; r2<4; ++r2) {
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
if(r_shorts)
n3.pattern.s[x*dim_x + (dim_y-1-y)] = n1.pattern.s[y*dim_x + x];
else
n3.pattern.b[x*dim_x + (dim_y-1-y)] = n1.pattern.b[y*dim_x + x];
memcpy(n1.pattern.s, n3.pattern.s, curNodeWidth);
if((added = betweenNodes(&n1, &n2))) goto found;
}
} else {
for(r2=0; r2<2; ++r2) {
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
if(r_shorts)
n3.pattern.s[(dim_y-1-y)*dim_x + dim_x-1-x] = n1.pattern.s[y*dim_x + x];
else
n3.pattern.b[(dim_y-1-y)*dim_x + dim_x-1-x] = n1.pattern.b[y*dim_x + x];
memcpy(n1.pattern.s, n3.pattern.s, curNodeWidth);
if((added = betweenNodes(&n1, &n2))) goto found;
}
}
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
if(r_shorts)
n3.pattern.s[(dim_y-1-y)*dim_x + x] = n1.pattern.s[y*dim_x + x];
else
n3.pattern.b[(dim_y-1-y)*dim_x + x] = n1.pattern.b[y*dim_x + x];
memcpy(n1.pattern.s, n3.pattern.s, curNodeWidth);
}
found:

if(!added) {
printf("\nunfillable %d.%d:\n", n1.depth, n2.depth);
print_node(&n1);
print_node(&n2);
bailout("cannot fill the space between two successive nodes.", 0);
}

for(p=betweenstack; added; --added, ++p) {
z0 = n1.depth + p->z;
x0 = p->xy % BOXWIDTH, y0 = p->xy / BOXWIDTH;
o = p->onum + o_list;
// find the colors that touch this piece.
memset(used, 0, sizeof(used));
s = o->pattern;
for(k=0; k<o->slices; ++k, ++s) {
y = s->xy / BOXWIDTH;
x = s->xy % BOXWIDTH;
z = 0;
for(mask = s->bits; mask; mask<<=1, ++z) {
if(isNotHighbit(mask)) continue;
if(x0+x > 0 && (c = B_LOC(x-1,y,z)) != '?' && c != '*')
used[c-'a'] = 1;
if(y0+y > 0 && (c = B_LOC(x,y-1,z)) != '?' && c != '*')
used[c-'a'] = 1;
if(z0+z > 0 && (c = B_LOC(x,y,z-1)) != '?' && c != '*')
used[c-'a'] = 1;
if(x0+x < dim_x-1 && (c = B_LOC(x+1,y,z)) != '?' && c != '*')
used[c-'a'] = 1;
if(y0+y < dim_y-1 && (c = B_LOC(x,y+1,z)) != '?' && c != '*')
used[c-'a'] = 1;
if((c = B_LOC(x,y,z+1)) != '?' && c != '*')
used[c-'a'] = 1;
}
} /* loop over slices in the piece */

c = assignColor();

s = o->pattern;
for(k=0; k<o->slices; ++k, ++s) {
y = s->xy / BOXWIDTH;
x = s->xy % BOXWIDTH;
z = 0;
for(mask = s->bits; mask; mask<<=1, ++z) {
if(isNotHighbit(mask)) continue;
B_LOC(x, y, z) = c;
}
} /* loop over slices in the piece */
} /* loop over pieces between the two nodes */

n2 = n1;
} while(parent); /* loop down through the depths */
}
#undef B_LOC

static char *leftBoard, *rightBoard, *workBoard;

#define B_LOC(a, x, y, z) a[(z)*dim_x*dim_y + (y)*dim_x + (x)]
static void mergeBoards(void)
{
int x, y, z;
char c, d;

// where the half boards meet, colors may collide.
// Look for pieces in the left board that are on the border.
for(x=0; x<dim_x; ++x)
for(y=0; y<dim_y; ++y)
for(z=0; z<dim_z; ++z) {
int nsq1, nsq2, j;
uchar qx[NSQ], qy[NSQ], qz[NSQ];
c = B_LOC(leftBoard, x, y, z);
if(c == '?') continue;
// it's a real piece.
// This doesn't have to be efficient; it's the solution.
nsq1 = 0, nsq2 = 1;
qx[0] = x, qy[0] = y, qz[0] = z;
memset(used, 0, sizeof(used));
while(nsq1 < nsq2) {
int x0 = qx[nsq1], y0 = qy[nsq1], z0 = qz[nsq1];
d = B_LOC(leftBoard, x0, y0, z0);
++nsq1;
if(d != c) continue;
// this is part of the same piece; look at the 6 neighbors
if(x0 > 0) {
d = B_LOC(leftBoard, x0-1, y0, z0);
if(d == c) { // part of the same piece
// have we seen it before?
for(j=0; j<nsq2; ++j)
if(qx[j] == x0-1 && qy[j] == y0 && qz[j] == z0) break;
if(j == nsq2)
qx[j] = x0-1, qy[j] = y0, qz[j] = z0, ++nsq2;
} else {
if(d == '?') // grab color from the other board
d = B_LOC(rightBoard, x0-1, y0, dim_z-1-(z0));
if(d != '?' && d != '*')
used[d-'a'] = 1;
}
}
if(y0 > 0) {
d = B_LOC(leftBoard, x0, y0-1, z0);
if(d == c) { // part of the same piece
for(j=0; j<nsq2; ++j)
if(qx[j] == x0 && qy[j] == y0-1 && qz[j] == z0) break;
if(j == nsq2)
qx[j] = x0, qy[j] = y0-1, qz[j] = z0, ++nsq2;
} else {
if(d == '?') // grab color from the other board
d = B_LOC(rightBoard, x0, y0-1, dim_z-1-(z0));
if(d != '?' && d != '*')
used[d-'a'] = 1;
}
}
if(z0 > 0) {
d = B_LOC(leftBoard, x0, y0, z0-1);
if(d == c) { // part of the same piece
for(j=0; j<nsq2; ++j)
if(qx[j] == x0 && qy[j] == y0 && qz[j] == z0-1) break;
if(j == nsq2)
qx[j] = x0, qy[j] = y0, qz[j] = z0-1, ++nsq2;
} else {
if(d == '?') // grab color from the other board
d = B_LOC(rightBoard, x0, y0, dim_z-1-(z0-1));
if(d != '?' && d != '*')
used[d-'a'] = 1;
}
}
if(x0 < dim_x-1) {
d = B_LOC(leftBoard, x0+1, y0, z0);
if(d == c) { // part of the same piece
for(j=0; j<nsq2; ++j)
if(qx[j] == x0+1 && qy[j] == y0 && qz[j] == z0) break;
if(j == nsq2)
qx[j] = x0+1, qy[j] = y0, qz[j] = z0, ++nsq2;
} else {
if(d == '?') // grab color from the other board
d = B_LOC(rightBoard, x0+1, y0, dim_z-1-(z0));
if(d != '?' && d != '*')
used[d-'a'] = 1;
}
}
if(y0 < dim_y-1) {
d = B_LOC(leftBoard, x0, y0+1, z0);
if(d == c) { // part of the same piece
for(j=0; j<nsq2; ++j)
if(qx[j] == x0 && qy[j] == y0+1 && qz[j] == z0) break;
if(j == nsq2)
qx[j] = x0, qy[j] = y0+1, qz[j] = z0, ++nsq2;
} else {
if(d == '?') // grab color from the other board
d = B_LOC(rightBoard, x0, y0+1, dim_z-1-(z0));
if(d != '?' && d != '*')
used[d-'a'] = 1;
}
}
if(z0 < dim_z-1) {
d = B_LOC(leftBoard, x0, y0, z0+1);
if(d == c) { // part of the same piece
for(j=0; j<nsq2; ++j)
if(qx[j] == x0 && qy[j] == y0 && qz[j] == z0+1) break;
if(j == nsq2)
qx[j] = x0, qy[j] = y0, qz[j] = z0+1, ++nsq2;
} else {
if(d == '?') // grab color from the other board
d = B_LOC(rightBoard, x0, y0, dim_z-1-(z0+1));
if(d != '?' && d != '*')
used[d-'a'] = 1;
}
}
}

if(nsq2 != nsq) // should never happen
printf("mergeBoard piece at %d,%d,%d color %c has size %d\n", x, y, z, c, nsq2);

// if c is still good then leave it alone
if(!used[c-'a']) continue;

// Oops, need a new color
last_ci = c - 'a';
d = assignColor();
for(j=0; j<nsq2; ++j)
B_LOC(leftBoard, qx[j], qy[j], qz[j]) = d;
#if DEBUG
// 3dbox -m1 e04040 10 3 10
// recolor 2,1,4 from g to l
// recolor 3,0,3 from h to j
// recolor 6,1,4 from e to g
// recolor 9,0,5 from f to h
printf("recolor %d,%d,%d from %c to %c\n", x, y, z, c, d);
#endif
}

// colors do not collied; let's merge

for(x=0; x<dim_x; ++x)
for(y=0; y<dim_y; ++y)
for(z=0; z<dim_z; ++z) {
c = B_LOC(leftBoard, x, y, z);
if(c != '?') continue;
c = B_LOC(rightBoard, x, y, dim_z-1-z);
if(c == '?') bailout("double ? at %d", x);
B_LOC(leftBoard, x, y, z) = c;
}
}

static int boardsOverlap(void)
{
int x, y, z;
char c;
for(x=0; x<dim_x; ++x)
for(y=0; y<dim_y; ++y)
for(z=0; z<dim_z; ++z)
if(B_LOC(leftBoard, x, y, z) != '?' &&
B_LOC(rightBoard, x, y, dim_z-1-z) != '?')
return 1;
return 0;
}

static void matchFound(const struct NODE *left, const struct NODE *right)
{
int newOrder;
int r1, r2; // rotations in the D4 group
char solname[120];
int x, y, z;
FILE *sol;

dim_z = left->depth + right->depth + left->gap;
boxVolume = boxArea * dim_z;
if(boxVolume % ordFactor)
bailout("impossible dimensions, height %d", dim_z);
newOrder = boxVolume/nsq;
if(newOrder > boxOrder) return;

// found something boxOrder or better!
printf(" *%d[%dx%dx%d", newOrder, dim_x, dim_y, dim_z);

leftBoard = emalloc(boxVolume);
rightBoard = emalloc(boxVolume);
workBoard = emalloc(boxVolume);
memset(leftBoard, '?', boxVolume);
memset(rightBoard, '?', boxVolume);
last_ci = COLORS - 1;
downToFloor(leftBoard, left);
downToFloor(rightBoard, right);
printf("]");

for(r1=0; r1<2; ++r1) {
if(dim_x == dim_y) {
for(r2=0; r2<4; ++r2) {
for(x=0; x<dim_x; ++x)
for(y=0; y<dim_y; ++y)
for(z=0; z<dim_z; ++z)
B_LOC(workBoard, dim_y-1-y, x, z) = B_LOC(rightBoard, x, y, z);
memcpy(rightBoard, workBoard, boxVolume);
if(!boardsOverlap()) goto found;
}
} else {
for(r2=0; r2<2; ++r2) {
for(x=0; x<dim_x; ++x)
for(y=0; y<dim_y; ++y)
for(z=0; z<dim_z; ++z)
B_LOC(workBoard, dim_x-1-x, dim_y-1-y, z) = B_LOC(rightBoard, x, y, z);
memcpy(rightBoard, workBoard, boxVolume);
if(!boardsOverlap()) goto found;
}
}
for(x=0; x<dim_x; ++x)
for(y=0; y<dim_y; ++y)
for(z=0; z<dim_z; ++z)
B_LOC(workBoard, x, dim_y-1-y, z) = B_LOC(rightBoard, x, y, z);
memcpy(rightBoard, workBoard, boxVolume);
}

bailout("cannot put the two halves of the solution together", 0);

found:
mergeBoards();

sprintf(solname, "dotile/%s/sol%dx%dx%d",
piecename, dim_x, dim_y, dim_z);
sol = fopen(solname, "w");
if(!sol) bailouts("cannot create solution file %s", solname);

for(y=0; y<dim_y; ++y) {
if(y) {
for(z=0; z<dim_z; ++z)
fprintf(sol, "-");
fprintf(sol, "\n");
}
for(x=0; x<dim_x; ++x) {
for(z=0; z<dim_z; ++z)
fprintf(sol, "%c", B_LOC(leftBoard, x,y,z));
fprintf(sol, "\n");
}
}
fclose(sol);

free(leftBoard);
free(rightBoard);
free(workBoard);

boxOrder = newOrder - 1;
setBestZ();
}
#undef B_LOC

static void expandNode(long this_idx, const uchar *base_b)
{
ushort *base_s = (ushort*)base_b;
int lev; /* placement level */
struct SF *p;
const struct SF *q;
const struct ORIENT *o;
const struct SLICE *s;
int min_z, min_z_count;
shapebits min_z_bit, mask;
int reset = -1, near = 0;
int breakLine = REPDIAMETER; // the first piece will ratchet it down
int x, y, j, k;
int x0, y0, diag2;
uchar ambinclude, ambnode;
uchar children = 0;
struct NODE newnode, compnode, looknode;
shapebits b0[BOXWIDTH*BOXWIDTH];
shapebits b1[BOXWIDTH*BOXWIDTH];

min_z = 0;
min_z_bit = HIGHBIT;
min_z_count = 0;
// copy the board to the board on-stack for manipulation
if(r_shorts) {
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x) {
b0[y*BOXWIDTH + x] = base_s[y*dim_x + x];
if(!(b0[y*BOXWIDTH+x]&min_z_bit)) ++min_z_count;
}
} else {
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x) {
b0[y*BOXWIDTH + x] = ((int)base_b[y*dim_x + x]<<8);
if(!(b0[y*BOXWIDTH+x]&min_z_bit)) ++min_z_count;
}
}

p = stack - 1, lev = -1;

advance:
if(++lev >= MAXORDER)
bailout("placement stack overflow %d", MAXORDER);
// trec.c had a lookahead parameter, to tile past breakLine, but it didn't
// seem to help much, so just tile up through breakLine.
if(min_z > breakLine) goto complete;

// find location to place the piece
if(lev && min_z == p->z)
x = p->x, y = p->y;
else x = y = 0;

while(b0[y*BOXWIDTH+x] & min_z_bit) {
++y, --x;
if(y == dim_y) {
x += dim_y, y = 0;
++x; // next diagonal
while(x >= dim_x) ++y, --x;
if(y == dim_y) break;
continue;
}
if(x < 0) x += y+1, y = 0;
}

if(y == dim_y)
bailout("no empty square found at level %d", min_z);

++p;
p->x = x, p->y = y;
// in in solve() above, x y and z are absolute;
// here x and y are absolute, but z is relative to the node.
p->z = min_z;
p->mzc = min_z_count;

// look for holes
#if NODEHOLES
// This is complicated, and the speed is exactly the same, so leave it off.
diag2 = x + y;
if(diag2 > 1 && diag2 < dim_x + dim_y-4 && min_z < 10) {
int x2, y2;
shapebits zb0 = min_z_bit;
shapebits zb1 = zb0 >> 1;
shapebits zb2 = zb1 >> 1;
for(x2 = x, y2 = y; x2 && y2 < dim_y; --x2, ++y2) {
if(b0[x2+BOXWIDTH*y2]&zb0) continue;
// we're on the current diag, everything on the previous diag is filled,
// so we don't need these 3 lines.
#if 0
if(x2 && !(b0[x2-1+BOXWIDTH*y2]&zb0)) continue;
if(y2 && !(b0[x2+BOXWIDTH*(y2-1)]&zb0)) continue;
#endif
if(x2 < dim_x-1 && !(b0[x2+1+BOXWIDTH*y2]&zb0)) {
// ok, perhaps a hole of size 2
if((y2 == dim_y-1 || b0[x2+BOXWIDTH*(y2+1)]&zb0) &&
b0[x2+BOXWIDTH*y2]&zb1 &&
(y2 == dim_y-1 || b0[x2+1+BOXWIDTH*(y2+1)]&zb0) &&
b0[x2+1+BOXWIDTH*y2]&zb1 &&
(!y2 || b0[x2+1+BOXWIDTH*(y2-1)]&zb0)) {
if(x2 == dim_x-2 || b0[x2+2+BOXWIDTH*y2]&zb0) {
#if DEBUG
puts("hole2x");
#endif
goto backup;
}
if(!tubes) {
#if DEBUG
puts("tube2x");
#endif
goto backup;
}
}
continue;
}
if(y2 < dim_y-1 && !(b0[x2+BOXWIDTH*(y2+1)]&zb0)) {
// ok, perhaps a hole of size 2
if(b0[x2+BOXWIDTH*y2]&zb1 &&
(x2 == dim_x-1 || b0[x2+1+BOXWIDTH*(y2+1)]&zb0) &&
b0[x2+BOXWIDTH*(y2+1)]&zb1) {
if(!x2 || b0[x2-1+BOXWIDTH*(y2+1)]&zb0) {
if(y2 == dim_y-2 || b0[x2+BOXWIDTH*(y2+2)]&zb0) {
#if DEBUG
puts("hole2y");
#endif
goto backup;
}
if(!tubes) {
#if DEBUG
puts("tube2y");
#endif
goto backup;
}
continue;
}
if((y2 == dim_y-2 || b0[x2+BOXWIDTH*(y2+2)]&zb0) &&
b0[x2-1+BOXWIDTH*(y2+1)]&zb1 &&
(y2 == dim_y-2 || b0[x2-1+BOXWIDTH*(y2+2)]&zb0)) {
#if DEBUG
puts("hole3xy");
#endif
goto backup;
}
}
continue;
}
if(!(b0[x2+BOXWIDTH*y2]&zb1)) {
// ok, perhaps a hole of size 2
if((x2 == dim_x-1 || b0[x2+1+BOXWIDTH*y2]&zb1) &&
(y2 == dim_y-1 || b0[x2+BOXWIDTH*(y2+1)]&zb1)) {
if((!x2 || b0[x2-1+BOXWIDTH*y2]&zb1) &&
(!y2 || b0[x2+BOXWIDTH*(y2-1)]&zb1)) {
if(b0[x2+BOXWIDTH*y2]&zb2) {
#if DEBUG
puts("hole2z");
#endif
goto backup;
}
if(!tubes) {
#if DEBUG
puts("tube2z");
#endif
goto backup;
}
}
if(b0[x2+BOXWIDTH*y2]&zb2) {
if((!x2 || b0[x2-1+BOXWIDTH*y2]&zb1) &&
y2 && !(b0[x2+BOXWIDTH*(y2-1)]&zb1) &&
b0[x2+BOXWIDTH*(y2-1)]&zb2 &&
(x2 == dim_x-1 || b0[x2+1+BOXWIDTH*(y2-1)]&zb1) &&
(!x2 || b0[x2-1+BOXWIDTH*(y2-1)]&zb1) &&
(y2 == 1 || b0[x2+BOXWIDTH*(y2-2)]&zb1)) {
#if DEBUG
puts("hole3yz");
#endif
goto backup;
}
if((!y2 || b0[x2+BOXWIDTH*(y2-1)]&zb1) &&
x2 && !(b0[x2-1+BOXWIDTH*y2]&zb1) &&
b0[x2-1+BOXWIDTH*y2]&zb2 &&
(y2 == dim_y-1 || b0[x2-1+BOXWIDTH*(y2+1)]&zb1) &&
(!y2 || b0[x2-1+BOXWIDTH*(y2-1)]&zb1) &&
(x2 == 1 || b0[x2-2+BOXWIDTH*y2]&zb1)) {
#if DEBUG
puts("hole3xz");
#endif
goto backup;
}
}
}
continue;
}
#if DEBUG
puts("hole");
#endif
goto backup;
}

++diag2;

for(x2 = diag2, y2 = 0; x2 && y2 <dim_y; --x2, ++y2) {
if(x2 >= dim_x) continue;
if(b0[x2+BOXWIDTH*y2]&zb0) continue;
if(x2 && !(b0[x2-1+BOXWIDTH*y2]&zb0)) continue;
if(y2 && !(b0[x2+BOXWIDTH*(y2-1)]&zb0)) continue;
if(x2 < dim_x-1 && !(b0[x2+1+BOXWIDTH*y2]&zb0)) {
// ok, perhaps a hole of size 2
if((y2 == dim_y-1 || b0[x2+BOXWIDTH*(y2+1)]&zb0) &&
b0[x2+BOXWIDTH*y2]&zb1 &&
(y2 == dim_y-1 || b0[x2+1+BOXWIDTH*(y2+1)]&zb0) &&
b0[x2+1+BOXWIDTH*y2]&zb1 &&
(!y2 || b0[x2+1+BOXWIDTH*(y2-1)]&zb0)) {
if(x2 == dim_x-2 || b0[x2+2+BOXWIDTH*y2]&zb0) {
#if DEBUG
puts("hole+2x");
#endif
goto backup;
}
if(!tubes) {
#if DEBUG
puts("tube+2x");
#endif
goto backup;
}
}
continue;
}
if(y2 < dim_y-1 && !(b0[x2+BOXWIDTH*(y2+1)]&zb0)) {
// ok, perhaps a hole of size 2
if(b0[x2+BOXWIDTH*y2]&zb1 &&
(x2 == dim_x-1 || b0[x2+1+BOXWIDTH*(y2+1)]&zb0) &&
b0[x2+BOXWIDTH*(y2+1)]&zb1) {
if(!x2 || b0[x2-1+BOXWIDTH*(y2+1)]&zb0) {
if(y2 == dim_y-2 || b0[x2+BOXWIDTH*(y2+2)]&zb0) {
#if DEBUG
puts("hole+2y");
#endif
goto backup;
}
if(!tubes) {
#if DEBUG
puts("tube+2y");
#endif
goto backup;
}
continue;
}
if((y2 == dim_y-2 || b0[x2+BOXWIDTH*(y2+2)]&zb0) &&
b0[x2-1+BOXWIDTH*(y2+1)]&zb1 &&
(y2 == dim_y-2 || b0[x2-1+BOXWIDTH*(y2+2)]&zb0) &&
(x2 == 1 || b0[x2-2+BOXWIDTH*(y2+1)]&zb0)) {
#if DEBUG
puts("hole+3xy");
#endif
goto backup;
}
}
continue;
}
if(!(b0[x2+BOXWIDTH*y2]&zb1)) {
// ok, perhaps a hole of size 2
if((x2 == dim_x-1 || b0[x2+1+BOXWIDTH*y2]&zb1) &&
(y2 == dim_y-1 || b0[x2+BOXWIDTH*(y2+1)]&zb1)) {
if((!x2 || b0[x2-1+BOXWIDTH*y2]&zb1) &&
(!y2 || b0[x2+BOXWIDTH*(y2-1)]&zb1)) {
if(b0[x2+BOXWIDTH*y2]&zb2) {
#if DEBUG
puts("hole+2z");
#endif
goto backup;
}
if(!tubes) {
#if DEBUG
puts("tube+2z");
#endif
goto backup;
}
}
if(b0[x2+BOXWIDTH*y2]&zb2) {
if((!x2 || b0[x2-1+BOXWIDTH*y2]&zb1) &&
y2 && !(b0[x2+BOXWIDTH*(y2-1)]&zb1) &&
b0[x2+BOXWIDTH*(y2-1)]&zb2 &&
(x2 == dim_x-1 || b0[x2+1+BOXWIDTH*(y2-1)]&zb1) &&
(!x2 || b0[x2-1+BOXWIDTH*(y2-1)]&zb1) &&
(y2 == 1 || b0[x2+BOXWIDTH*(y2-2)]&zb1)) {
#if DEBUG
puts("hole+3yz");
#endif
goto backup;
}
if((!y2 || b0[x2+BOXWIDTH*(y2-1)]&zb1) &&
x2 && !(b0[x2-1+BOXWIDTH*y2]&zb1) &&
b0[x2-1+BOXWIDTH*y2]&zb2 &&
(y2 == dim_y-1 || b0[x2-1+BOXWIDTH*(y2+1)]&zb1) &&
(!y2 || b0[x2-1+BOXWIDTH*(y2-1)]&zb1) &&
(x2 == 1 || b0[x2-2+BOXWIDTH*y2]&zb1)) {
#if DEBUG
puts("hole+3xz");
#endif
goto backup;
}
}
}
continue;
}
#if DEBUG
puts("hole+");
#endif
goto backup;
}
}
#endif

#if NEAR
near = 0;
if(y < dim_y-1) {
if(b0[x+BOXWIDTH*(y+1)]&(HIGHBIT>>min_z)) near |= 1;
if(!x || b0[x-1+BOXWIDTH*(y+1)]&(HIGHBIT>>min_z)) near |= 2;
if(b0[x+BOXWIDTH*(y+1)]&(HIGHBIT>>(min_z+1))) near |= 4;
if(!x || b0[x-1+BOXWIDTH*(y+1)]&(HIGHBIT>>(min_z+1))) near |= 8;
} else near |= 15;
if(!y || b0[x+BOXWIDTH*(y-1)]&(HIGHBIT>>(min_z+1))) near |= 0x10;
if(!x || !y || b0[x-1+BOXWIDTH*(y-1)]&(HIGHBIT>>(min_z+1))) near |= 0x20;
if(!x || b0[x-1+BOXWIDTH*(y)]&(HIGHBIT>>(min_z+1))) near |= 0x40;
if(b0[x+BOXWIDTH*(y)]&(HIGHBIT>>(min_z+1))) near |= 0x80;
if(x < dim_x-1) {
if(b0[x+1+BOXWIDTH*(y)]&(HIGHBIT>>min_z)) near |= 0x100;
if(y == dim_y-1 || b0[x+1+BOXWIDTH*(y+1)]&(HIGHBIT>>min_z)) near |= 0x200;
} else near |= 0x300;
p->near = near;
#endif

#if DEBUG
printf("locate %d,%d,%d near %x\n", x, y, min_z, near);
#endif

p->breakLine = breakLine;
p->onum = -1;
o = o_list - 1;

next:
if(++p->onum == o_max) goto backup;
++o;
#if NEAR
if(p->near & o->near) goto next;
#endif
x0 = p->x - o->x;
if(x0 < 0) goto next;
if(x0 + o->rng_x > dim_x) goto next;
y0 = p->y - o->y;
if(y0 < 0) goto next;
if(y0 + o->rng_y > dim_y) goto next;
// the piece fits in the box.

// Look for collision.
p->xy = y0 * BOXWIDTH + x0;
s = o->pattern; k = o->slices; while(1) {
if(b0[p->xy+s->xy] & (s->bits>>min_z)) goto next;
if(!--k) break;
++s;
}

#if SWING
if(!this_idx && !min_z) {
// Sinced nodes are normalized through the dihedral group, the same nodes are
// produced; this just gets us off the floor faster.
int swing;
int corner = stack[0].onum;
// I think this works even if p == stack, the first piece touches two corners.
if((swing = o->hr) >= 0 && y0 == 0 && x0 + o->rng_x == dim_x && swing < corner) goto next;
if((swing = o->vr) >= 0 && x0 == 0 && y0 + o->rng_y == dim_y && swing < corner) goto next;
if((swing = o->r2) >= 0 && x0 + o->rng_x == dim_x && y0 + o->rng_y == dim_y && swing < corner) goto next;
if(dim_x == dim_y) {
if((swing = o->dr2) >= 0 && x0 + o->rng_x == dim_x && y0 + o->rng_y == dim_y && swing < corner) goto next;
if((swing = o->dxy) >= 0 && x0 == 0 && y0 == 0 && swing < corner) goto next;
if((swing = o->r1) >= 0 && y0 == 0 && x0 + o->rng_x == dim_x && swing < corner) goto next;
if((swing = o->r3) >= 0 && x0 == 0 && y0 + o->rng_y == dim_y && swing < corner) goto next;
}
}
#endif

#if DEBUG
printf("place{%d,%d,%d ", p->x, p->y, min_z);
print_o(o);
sleep(1);
#endif
s = o->pattern; k = o->slices; while(1) {
shapebits t = (s->bits>>min_z);
b0[p->xy+s->xy] |= t;
if(t&min_z_bit) --min_z_count;
if(!--k) break;
++s;
}

// downgrade breakLine
j = o->breakLine + min_z;
if(j < breakLine) breakLine = j;

if(min_z_count) goto advance;
// find lowest level
mask = 0xffff;
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
mask &= b0[y*BOXWIDTH + x];
min_z = lowEmpty[mask];
min_z_bit = (HIGHBIT >> min_z);
min_z_count = 0;
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
if(!(b0[y*BOXWIDTH + x] & min_z_bit)) ++min_z_count;
#if DEBUG
printf("min_z now %d count %d\n", min_z, min_z_count);
#endif
goto advance;

backup:
#if DEBUG
puts("}");
#endif
--lev, --p;
if(lev < 0) {
// If this node has no descendants, there's no strong reason to keep it
// around in cache. This hardly ever happens.
if(!children && this_idx) {
readNode(this_idx, &compnode);
compnode.dead = 1;
writeNode(this_idx, &compnode);
markOldNode(this_idx, compnode.hash);
}
--nodesPending; // this node has been processed
return;
}

// restore
breakLine = p->breakLine;
#if DEBUG
if(min_z != p->z)
printf("min_z back %d count %d\n", p->z, p->mzc);
#endif
min_z = p->z;
min_z_bit = (HIGHBIT >> min_z);
min_z_count = p->mzc;
o = o_list + p->onum;
// unplace piece
s = o->pattern; k = o->slices; while(1) {
b0[p->xy+s->xy] ^= (s->bits>>min_z);
if(!--k) break;
++s;
}
if(reset >= 0) {
if(min_z > reset) goto backup;
reset = -1;
}
goto next;

complete:
children = 1;
ambinclude = ambnode = 0;
reset = breakLine - (setMinDimension-1)/2;

recomplete:
// build a new instance of the board, with only those pieces
// that would be included on the lower side of the breakLine.
if(r_shorts)
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
b1[y*BOXWIDTH + x] = base_s[y*dim_x + x];
else
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
b1[y*BOXWIDTH + x] = ((int)base_b[y*dim_x + x]<<8);

for(q=stack; q<=p; ++q) {
o = q->onum + o_list;
j = o->breakLine + q->z - breakLine;
if(j > 0) continue;
if(j == 0 && o->ambig && !ambinclude) {
ambnode = 1;
continue;
}

// place piece
j = q->z;
s = o->pattern; k = o->slices; while(1) {
b1[q->xy+s->xy] |= (s->bits>>j);
if(!--k) break;
++s;
}
}

// compute depth and shift the patttern back down to the floor
mask = 0xffff;
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
mask &= b1[y*BOXWIDTH + x];
j = lowEmpty[mask];
newnode.depth = curDepth + j;
if(j) {
if(j > 8*(1+r_shorts)) bailout("depth difference %d is too high", j);
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
b1[y*BOXWIDTH + x] <<= j;
} else if(ambnode) {
// did we make the same node again?
if(r_shorts)
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
if(b1[y*BOXWIDTH + x] != base_s[y*dim_x + x]) goto notsame;
else
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x)
if(b1[y*BOXWIDTH + x] != ((int)base_b[y*dim_x + x] << 8)) goto notsame;
// same node, skip ahead
goto ambtest;
}
notsame:

// build new node and compute gap
mask = 0;
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x) {
j = y*BOXWIDTH + x;
mask |= b1[j];
if(r_shorts)
newnode.pattern.s[y*dim_x + x] = b1[j];
else
newnode.pattern.b[y*dim_x + x] = (b1[j] >> 8);
}
for(j=0; mask; ++j, mask<<=1)  ;
newnode.gap = j;
if(j > 8*(1+r_shorts)) bailout("gap %d is too high", j);
if(j == 0) bailout("zero gap at depth %d", newnode.depth);
newnode.dead = 0;
newnode.parent = this_idx;

#if DEBUG
printf("new node depth %d gap %d ", newnode.depth, newnode.gap);
print_node(&newnode);
#endif

if(!stopstore(newnode)) {
int rc = findNode(&newnode, 1, &looknode);
if(rc) goto ambtest;
}

if(newnode.depth + reachup >= minDepth) {
// by inserting first, this complement check now tests whether
// the node matches itself.
if(r_shorts) {
// need a signed right shift here.
mask = ((short)HIGHBIT >> (newnode.gap-1));
for(j=0; j<boxArea; ++j)
compnode.pattern.s[j] = (reverseShort((newnode.pattern.s[j]^mask)) << (16-newnode.gap));
} else {
mask = ((schar)0x80 >> (newnode.gap-1));
for(j=0; j<boxArea; ++j)
compnode.pattern.b[j] = (reverseByte((uchar)(newnode.pattern.b[j]^mask)) << (8-newnode.gap));
}
#if DEBUG
printf("complement ");
print_node(&compnode);
#endif
if(findNode(&compnode, 0, &looknode))
matchFound(&newnode, &looknode);
}

ambtest:
if(ambnode && !ambinclude) { ambnode = 0; ambinclude = 1; goto recomplete; }
++p;
goto backup;
}

// Get the next node to expand
static long getNode(struct NODE *buf)
{
int n;
while(nodeStep < nodesDisk || workStep < workEnd) {
if(workStep < workEnd) {
n = workList[workStep++];
printf(">");
} else n = nodeStep++;
readNode(n, buf);
if(buf->dead) continue;
if(buf->depth != curDepth) continue;
// Sanity check, but these things should never happen.
if(nodesPending < 0)
bailout("pending negative %d", nodesDisk - nodeStep);
if(nodesCache < 0)
bailout("nodesCache negative %d", nodesCache);
if(!nodesCache && curDepth)
bailout("nothing in cache, %d pending", nodesPending);
return n;
}
return 0;
}

// One of these workers per worker thread,
// except we don't have threads here; only in trec.c.
static void *expandWorker(void *notused)
{
long n; /* index of node being expanded */
struct NODE buf; /* node buffer */
while(n = getNode(&buf)) {
#if DEBUG
printf("get node %ld depth %d ", n, buf.depth);
print_node(&buf);
#endif
expandNode(n, buf.pattern.b);
// Wait a minute - we might have found a better solution.
// Can we stop searching?
if(stopsearch) break;
if(maxDepth < dim_x) break;
}
return NULL;
}

// Expand all the nodes in the pending list at the current depth.
static void expandNodes(void)
{
workEnd = workStep = 0;
nodeStep = mon_idx;
if(restartParent && restartParent >= nodeStep) nodeStep = restartParent;
expandWorker(NULL);
}

/*********************************************************************
The following is practically a separate program from the above,
but I want to reuse the machinery to grab a piece or set of pieces
from the command line and compute orientations etc, so it's here.
inCorner() tries to fill the corner of a box of unspecified dimensions.
It is here to prove certain shapes have order 0, and never tile a box.
It is only useful for a few shapes.
This is not very efficient.
*********************************************************************/

#define CDIM 32 // corner dimension
#define CSTACKSIZE 2000

static struct CSF { // corner stack frame
schar x, y, z; // where piece is placed
short onum; // orientation number
short snum; // slice number
} cstack[CSTACKSIZE];

static void slantSet(void)
{
struct ORIENT *o;
const struct SLICE *s, *t;
int diag1, diag2;
shapebits mask;
int x1, y1, z1, x2, y2, z2;
int i, k, l;

o = o_list;
for(i=0; i<o_max; ++i, ++o) {
s = o->pattern;
for(k=0; k<o->slices; ++k, ++s) {
mask = s->bits;
z1 = 0;
while(isNotHighbit(mask)) ++z1, mask <<= 1;
x1 = s->xy % BOXWIDTH, y1 = s->xy / BOXWIDTH;
diag1 = x1 + y1 + z1;

t = o->pattern;
for(l=0; l<o->slices; ++l, ++t) {
if(t == s) continue;
mask = t->bits;
z2 = 0;
while(isNotHighbit(mask)) ++z2, mask <<= 1;
x2 = t->xy % BOXWIDTH, y2 = t->xy / BOXWIDTH;
diag2 = x2 + y2 + z2;
if(diag2 < diag1) { o->slant[k] = 1; break; }
if(diag2 > diag1) continue;
if(z2 > z1 || z2 == z1 && y2 >= y1) continue;
o->slant[k] = 1;
break;
}
}
}
}

static void inCorner(void)
{
int x,y, z;
int x1, y1, z1, x0, y0, z0;
shapebits mask;
int diag = 0, diag2;
int j, k, lev = -1;
struct CSF *p = cstack - 1;
const struct ORIENT *o;
const struct SLICE *s, *t;
// can the stack handle this chunk of board?
// If I packed it myself it would be 1/6 the size, but who cares?
uchar b[CDIM][CDIM][CDIM];

memset(b, 0, sizeof(b));
// I'm only setting dimensions so swingSet() will run properly.
dim_x = dim_y = dim_z = NSQ + 1;
swingSet();
slantSet();
if(tubes) puts("tubes");
puts("diag 0");

advance:
if(++lev == CSTACKSIZE) bailout("corner stack overflow %d", lev);

// find location to place the piece
if(!lev) x = y = z = 0;
else {
x = p->x, y = p->y, z = p->z;
while(b[x][y][z]) {
++y, --x;
if(x >= 0) continue;
x += y-1, y = 0, ++z;
if(x >= 0) continue;
++x; // next layer
if(z == CDIM) { puts("success"); exit(0); }
x = z, z = 0;
if(x > diag)
printf("diag %d\n", (diag = x));
}
}
++p;
p->x = x, p->y = y, p->z = z;
#if DEBUG
printf("locate %d,%d,%d\n", x, y, z);
#endif

// look for holes
#if CORNERHOLES
// This speeds things up quite a bit.
diag2 = x + y + z;
if(diag2 > 1 && diag2 < CDIM-3) {
int x2, y2, z2;
for(z2=z; z2<=diag2; ++z2)
for(x2=0; x2<=diag2-z2; ++x2) {
y2 = diag2 - z2 - x2;
if(b[x2][y2][z2]) continue;
// we're on the current diag, everything on the previous diag is filled,
// so we don't need these 3 lines.
#if 0
if(x2 && !b[x2-1][y2][z2]) continue;
if(y2 && !b[x2][y2-1][z2]) continue;
if(z2 && !b[x2][y2][z2-1]) continue;
#endif
if(!b[x2+1][y2][z2]) {
// ok, perhaps a hole of size 2
if(b[x2][y2+1][z2] &&
b[x2][y2][z2+1] &&
b[x2+1][y2+1][z2] &&
b[x2+1][y2][z2+1] &&
(!y2 || b[x2+1][y2-1][z2]) &&
(!z2 || b[x2+1][y2][z2-1])) {
if(b[x2+2][y2][z2]) {
#if DEBUG
puts("hole2x");
#endif
goto backup;
}
if(!tubes) {
#if DEBUG
puts("tube2x");
#endif
goto backup;
}
}
continue;
}
if(!b[x2][y2+1][z2]) {
// ok, perhaps a hole of size 2
if(b[x2][y2][z2+1] &&
b[x2+1][y2+1][z2] &&
b[x2][y2+1][z2+1] &&
(!z2 || b[x2][y2+1][z2-1])) {
if(!x2 || b[x2-1][y2+1][z2]) {
if(b[x2][y2+2][z2]) {
#if DEBUG
puts("hole2y");
#endif
goto backup;
}
if(!tubes) {
#if DEBUG
puts("tube2y");
#endif
goto backup;
}
continue;
}
if(b[x2][y2+2][z2] &&
b[x2-1][y2+1][z2+1] &&
b[x2-1][y2+2][z2]) {
#if DEBUG
puts("hole3xy");
#endif
goto backup;
}
}
continue;
}
if(!b[x2][y2][z2+1]) {
// ok, perhaps a hole of size 2
if(b[x2+1][y2][z2+1] &&
b[x2][y2+1][z2+1]) {
if((!x2 || b[x2-1][y2][z2+1]) &&
(!y2 || b[x2][y2-1][z2+1])) {
if(b[x2][y2][z2+2]) {
#if DEBUG
puts("hole2z");
#endif
goto backup;
}
if(!tubes) {
#if DEBUG
puts("tube2z");
#endif
goto backup;
}
}
if(b[x2][y2][z2+2]) {
if((!x2 || b[x2-1][y2][z2+1]) &&
y2 && !b[x2][y2-1][z2+1] &&
b[x2][y2-1][z2+2] &&
b[x2+1][y2-1][z2+1]) {
#if DEBUG
puts("hole3yz");
#endif
goto backup;
}
if((!y2 || b[x2][y2-1][z2+1]) &&
x2 && !b[x2-1][y2][z2+1] &&
b[x2-1][y2][z2+2] &&
b[x2-1][y2+1][z2+1]) {
#if DEBUG
puts("hole3xz");
#endif
goto backup;
}
}
}
continue;
}
#if DEBUG
puts("hole");
#endif
goto backup;
}

++diag2;

for(z2=0; z2<=diag2; ++z2)
for(x2=0; x2<=diag2-z2; ++x2) {
y2 = diag2 - z2 - x2;
if(b[x2][y2][z2]) continue;
if(x2 && !b[x2-1][y2][z2]) continue;
if(y2 && !b[x2][y2-1][z2]) continue;
if(z2 && !b[x2][y2][z2-1]) continue;
if(!b[x2+1][y2][z2]) {
// ok, perhaps a hole of size 2
if(b[x2][y2+1][z2] &&
b[x2][y2][z2+1] &&
b[x2+1][y2+1][z2] &&
b[x2+1][y2][z2+1] &&
(!y2 || b[x2+1][y2-1][z2]) &&
(!z2 || b[x2+1][y2][z2-1])) {
if(b[x2+2][y2][z2]) {
#if DEBUG
puts("hole+2x");
#endif
goto backup;
}
if(!tubes) {
#if DEBUG
puts("tube+2x");
#endif
goto backup;
}
}
continue;
}
if(!b[x2][y2+1][z2]) {
// ok, perhaps a hole of size 2
if(b[x2][y2][z2+1] &&
b[x2+1][y2+1][z2] &&
b[x2][y2+1][z2+1] &&
(!z2 || b[x2][y2+1][z2-1])) {
if(!x2 || b[x2-1][y2+1][z2]) {
if(b[x2][y2+2][z2]) {
#if DEBUG
puts("hole+2y");
#endif
goto backup;
}
if(!tubes) {
#if DEBUG
puts("tube+2y");
#endif
goto backup;
}
continue;
}
if(b[x2][y2+2][z2] &&
b[x2-1][y2+1][z2+1] &&
b[x2-1][y2+2][z2] &&
(!z2 || b[x2-1][y2+1][z2-1]) &&
(x2 == 1 || b[x2-2][y2+1][z2])) {
#if DEBUG
puts("hole+3xy");
#endif
goto backup;
}
}
continue;
}
if(!b[x2][y2][z2+1]) {
// ok, perhaps a hole of size 2
if(b[x2+1][y2][z2+1] &&
b[x2][y2+1][z2+1]) {
if((!x2 || b[x2-1][y2][z2+1]) &&
(!y2 || b[x2][y2-1][z2+1])) {
if(b[x2][y2][z2+2]) {
#if DEBUG
puts("hole+2z");
#endif
goto backup;
}
if(!tubes) {
#if DEBUG
puts("tube+2z");
#endif
goto backup;
}
}
if(b[x2][y2][z2+2]) {
if((!x2 || b[x2-1][y2][z2+1]) &&
y2 && !b[x2][y2-1][z2+1] &&
b[x2][y2-1][z2+2] &&
b[x2+1][y2-1][z2+1] &&
(!x2 || b[x2-1][y2-1][z2+1]) &&
(y2 == 1 || b[x2][y2-2][z2+1])) {
#if DEBUG
puts("hole+3yz");
#endif
goto backup;
}
if((!y2 || b[x2][y2-1][z2+1]) &&
x2 && !b[x2-1][y2][z2+1] &&
b[x2-1][y2][z2+2] &&
b[x2-1][y2+1][z2+1] &&
(!y2 || b[x2-1][y2-1][z2+1]) &&
(x2 == 1 || b[x2-2][y2][z2+1])) {
#if DEBUG
puts("hole+3xz");
#endif
goto backup;
}
}
}
continue;
}
#if DEBUG
printf("hole+@%d,%d,%d\n", x2, y2, z2);
#endif
goto backup;
}
}
#endif

p->onum = -1;
o = o_list - 1;

next_o:
if(++p->onum == o_max) goto backup;
++o;
s = o->pattern - 1;
p->snum = -1;
next_s:
if(++p->snum == o->slices) goto next_o;
++s;
if(o->slant[p->snum]) goto next_s;
mask = s->bits;
z1 = 0;
while(isNotHighbit(mask)) ++z1, mask <<= 1;
x1 = s->xy % BOXWIDTH, y1 = s->xy / BOXWIDTH;
x0 = x - x1, y0 = y - y1, z0 = z - z1;
if(x0 < 0 || y0< 0 || z0 < 0) goto next_s;
// look for collisions
for(k=0, t = o->pattern; k < o->slices; ++k, ++t) {
int x2 = t->xy % BOXWIDTH, y2 = t->xy / BOXWIDTH;
mask = t->bits;
for(j=0;mask; ++j, mask<<=1)
if(isHighbit(mask) && x0+x2 < CDIM && y0+y2 < CDIM && z0+j < CDIM && b[x0+x2][y0+y2][z0+j]) goto next_s;
}

#if SWING
if(p == cstack) {
int swing;
int corner = p->onum;
if((swing = o->dxy) >= 0 && swing < corner) goto next_o;
if((swing = o->dxz) >= 0 && swing < corner) goto next_o;
if((swing = o->dyz) >= 0 && swing < corner) goto next_o;
if((swing = o->spin1) >= 0 && swing < corner) goto next_o;
if((swing = o->spin2) >= 0 && swing < corner) goto next_o;
}
#endif

if(p == cstack) { printf("origin %d ", p->onum); print_o(o); }
else if(x + y + z <= showdiag) { printf("%d,%d,%d %d ", x, y, z, p->onum); print_o(o); }

#if DEBUG
printf("place{%d,%d,%d@%d,%d ", x, y, z, x1, y1);
print_o(o);
sleep(1);
#endif
for(k=0, t = o->pattern; k < o->slices; ++k, ++t) {
int x2 = t->xy % BOXWIDTH, y2 = t->xy / BOXWIDTH;
mask = t->bits;
for(j=0;mask; ++j, mask<<=1)
if(isHighbit(mask) && x0+x2 < CDIM && y0+y2 < CDIM && z0+j < CDIM) b[x0+x2][y0+y2][z0+j] = 1;
}
goto advance;

backup:
if(--lev < 0) {
puts("no solution");
exit(0);
}
#if DEBUG
puts("}");
#endif
--p;
o = o_list + p->onum;
s = o->pattern + p->snum;
mask = s->bits;
z1 = 0;
while(isNotHighbit(mask)) ++z1, mask <<= 1;
x = p->x, y = p->y, z = p->z;
x1 = s->xy % BOXWIDTH, y1 = s->xy / BOXWIDTH;
x0 = x - x1, y0 = y - y1, z0 = z - z1;
for(k=0, t = o->pattern; k < o->slices; ++k, ++t) {
int x2 = t->xy % BOXWIDTH, y2 = t->xy / BOXWIDTH;
mask = t->bits;
for(j=0;mask; ++j, mask<<=1)
if(isHighbit(mask) && x0+x2 < CDIM && y0+y2 < CDIM && z0+j < CDIM) b[x0+x2][y0+y2][z0+j] = 0;
}
goto next_s;
}
