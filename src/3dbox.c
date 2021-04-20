/*********************************************************************
3dbox.c: fill a box with 3d polyominoes.
*********************************************************************/

#define NSQ 80 // number of squares in largest polyomino
static int nsq; // number of squares in the polyomino
static int dim_x, dim_y, dim_z; // box being filled
static int curDepth; // when climbing through layers
static int maxDepth, minDepth;
static int reachup; /* greatest reach of node so far */
static int setMaxDimension, setMinDimension;
static int stopgap, forgetgap;
static char r_shorts; // nodes must use shorts, rather than bytes
static int boxOrder, boxArea, boxVolume;
static int cbflag; // checkerboard flag
static int ordFactor = 1;

// see the comments at the top of trec.c
#define stopsearch (2*curDepth + stopgap > maxDepth)
#define stopstore(x) (2*curDepth + stopgap == maxDepth || curDepth + x.depth + x.gap > maxDepth)

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
#define DIAG 1

#define REPDIAMETER 16 // represent pieces this large
#define SETSIZE 10 // number of pieces in the set
static int setSize; // for sets of polyominoes
#define MAXORDER 1000
#define BOXWIDTH 32

typedef unsigned char uchar;
typedef signed char schar;
typedef ushort shapebits;

// short highbit macros
#define HIGHBIT 0x8000
#define isHighbit(word) ((short)(word) < 0)
#define isNotHighbit(word) ((short)(word) >= 0)

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
struct SLICE pattern[NSQ];
};

#define O_MAX 500
static int o_max; /* number of orientations */
static struct ORIENT o_list[O_MAX];

static void print_o(const struct ORIENT *o)
{
int x, y, n = 0;
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
int start_x, start_y; // start_z will be 0 once adjusted
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

rng_x = rng_y = rng_z = 0;
for(x=0; x<REPDIAMETER; ++x)
for(y=0; y<REPDIAMETER; ++y)
for(z=0; z<REPDIAMETER; ++z)
if(orib2[x][y][z]) {
if(x > rng_x) rng_x = x;
if(y > rng_y) rng_y = y;
if(z > rng_z) rng_z = z;
}

#if DIAG
// Scan in a diagonal pattern, rather than raster,
// but this only increases speed a few percent,
// so it might be more confusing than it's worth.
// Assumes dim_x >= dim_y.
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
#else

for(y=0; y<REPDIAMETER; ++y)
for(x=0; x<REPDIAMETER; ++x)
if(orib2[x][y][0]) {
start_y = y, start_x = x;
goto pack;
}
bailout("orientation %d has nothing on the floor", o_max);
pack:
#endif

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
o->ambig = 0;
o->zflip = r1; // remember the spin
o->zflip |= (r2<<2); // remember point reflection
o->inspace = !chiral;

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
int subtotal, side;
int k = z - o->breakLine;
if(k <= 0) --k;
// REPDIAMETER 16, k at most 8, k^2 at most 64
// 80 squares: 80*64 = 4800
subtotal = (k*k << 18);
side = o->rng_y/2 - y;
if(side <= 0 && !(o->rng_y&1)) --side;
side = side * side;
if(o->rng_y > o->rng_x)
subtotal += (side << 9);
else subtotal += side;
side = o->rng_x/2 - x;
if(side <= 0 && !(o->rng_x&1)) --side;
side = side * side;
if(o->rng_x > o->rng_y)
subtotal += (side << 9);
else subtotal += side;
if(k < 0) bottom += subtotal; else top += subtotal;
}
if(bottom == top) o->ambig = 1;
if(bottom < top) ++o->breakLine;
}

#if DEBUG
printf("range %d,%d,%d", o->rng_x, o->rng_y, o->rng_z);
printf("_%d%s ", o->breakLine, (o->ambig ? "*" : ""));
print_o(o);
#endif
++o_max;
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

piecename = hexrep;
setMaxDimension = 0, setMinDimension = NSQ;

while(*s) {
if(setSize >= SETSIZE) bailout("too many pieces in the set, limit %d", SETSIZE);
memset(orib4, 0, sizeof(orib4));
nsq = 0;
i = y = 0;

while((c = *s) != 0 && c != '_') {
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

if(nsqFirst >= 0 && nsq != nsqFirst)
bailout("all polyominoes in the set must have the same number of squares", 0);
if(nsq > NSQ)
bailout("too many squares in the given polyomino, limit %d", NSQ);
nsqFirst = nsq;

// unpack into orib1
memset(orib1, 0, sizeof(orib1));
for(x=0; x<REPDIAMETER; ++x)
for(y=0; y<REPDIAMETER; ++y) {
mask = orib4[x][y];
for(z=0; z<REPDIAMETER; ++z) {
orib1[x][y][z] = isHighbit(mask);
mask <<= 1;
}
}

// see if the checkerboard argument applies
if(!(nsq&1)) {
i = 0;
for(x=0; x<REPDIAMETER; ++x)
for(y=0; y<REPDIAMETER; ++y)
for(z=0; z<REPDIAMETER; ++z)
if(orib1[x][y][z])
if((x+y+z)&1) ++i; else --i;
if(i < 0) i = -i;
if(!setSize) cbflag = i;
else if(i != cbflag) cbflag = 0;
} /* even squares */

compileRotations();

if(*s) ++s;
++setSize;
} /* loop over pieces in the set */

if(cbflag) {
puts("checkerboard upgrade");
ordFactor = 2;
}

stopgap = (setMinDimension&1) ? setMinDimension : setMinDimension - 1;
forgetgap = stopgap/2 - setMaxDimension/2 - 1;
if(forgetgap >= 0) bailout("forget gap should be negative, not %d", forgetgap);
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

static int solve(void);
#define COLORS 26
static uchar robin; // round robin on the colors
static uchar doNodes; // look by using nodes instead of filling the entire box
static int megaNodes = 80; // millions of nodes that can be cached

int main(int argc, const char **argv)
{
++argv, --argc;
while(argc && argv[0][0] == '-') {
if(argc && !strcmp(*argv, "-r"))
++argv, --argc, robin = 1;
if(argc && !strcmp(*argv, "-n"))
++argv, --argc, doNodes = 1;
if(argc && argv[0][0] == '-' && argv[0][1] == 'm' && isdigit(argv[0][2]))
megaNodes = atoi(argv[0]+2), ++argv, --argc;
}

if(argc != 2 && argc != 4)
bailout("usage: 3dbox [-r] [-n] [-mnnn] piece_set width depth height | 3dbox piece_set order", 0);

lowEmptySet();
stringPiece(argv[0]);

if(argc == 4) {
dim_x = atoi(argv[1]);
dim_y = atoi(argv[2]);
dim_z = atoi(argv[3]);
boxVolume = dim_x * dim_y * dim_z;
if(boxVolume % nsq) bailout("volume %d does not admit a whole number of pieces", boxVolume);
boxOrder = boxVolume / nsq;
if(boxOrder > MAXORDER) bailout("order to large, limit %d", MAXORDER);
if(dim_y > dim_x || dim_x > dim_z)
bailout("dimensions must be y x z increasing", 0);
if(dim_x > BOXWIDTH)
bailout("x dimension too large, limit %d", BOXWIDTH);
printf("order %d\n", boxOrder);
printf("box %d by %d by %d\n", dim_x, dim_y, dim_z);
solve();
return 0;
}

boxOrder = atoi(argv[1]);
while(1) {
while(boxOrder % ordFactor) ++boxOrder;
if(boxOrder > MAXORDER) bailout("order to large, limit %d", MAXORDER);
printf("order %d\n", boxOrder);
boxVolume = boxOrder * nsq;
for(dim_y = 2; dim_y*dim_y*dim_y <= boxVolume; ++dim_y) {
if(boxVolume % dim_y) continue;
for(dim_x = dim_y; dim_y*dim_x*dim_x <= boxVolume; ++dim_x) {
if((boxVolume/dim_y) % dim_x) continue;
if(dim_x > BOXWIDTH) bailout("box too wide, limit %d", BOXWIDTH);
dim_z = boxVolume / dim_y / dim_x;
printf("box %d by %d by %d\n", dim_x, dim_y, dim_z);
solve();
}
}
++boxOrder;
}

return 0;
}

static struct SF { // like a stack frame
schar x, y, z; // where piece is placed
schar x0, y0; // adjusted location of piece
schar increase;
short onum;
short xy; // y*BOXWIDTH + x
short breakLine;
short mzc;
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
int last_k = COLORS - 1;
uchar used[COLORS];

memset(b, '?', boxVolume);
// all the question marks should disappear

for(lev=0; lev<boxOrder; ++lev) {
p = stack + lev;
o = o_list + p->onum;
x0 = p->x0, y0 = p->y0, z0 = p->z;

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

if(robin) {
k = last_k;
c = '*';
do { ++k;
if(k == COLORS) k = 0;
if(!used[k]) { c = k+'a'; last_k = k; break; }
} while(k != last_k);
} else {
for(k=0; k<COLORS; ++k) if(!used[k]) break;
c = k < COLORS ? 'a'+k : '*';
}

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

static int solve(void)
{
int lev = -1;
struct SF *p = stack - 1;
const struct ORIENT *o;
const struct SLICE *s;
int x, y, z, j, k;

memset(ws, 0, sizeof(ws));

advance:
if(++lev == boxOrder) {
puts("solution!");
print_solution();
exit(0);
}
if(lev == MAXORDER) bailout("placement stack overflow %d", lev);
// find location to place the piece
if(!lev) x = y = z = 0;
else {
x = p->x, y = p->y, z = p->z;

#if DIAG
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
#else

while(isHighbit(ws[y*BOXWIDTH+x])) {
if(++x < dim_x) continue;
x = 0;
if(++y == dim_y) break;
}
#endif

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
#if DIAG
x = y = 0;
goto relocate;
#else
x = r_x, y = r_y;
#endif
}
}
++p;
p->x = x, p->y = y, p->z = z;
#if DEBUG
printf("locate %d,%d,%d\n", x, y, z);
#endif
p->increase = 0;
p->onum = -1;
o = o_list - 1;

next:
if(++p->onum == o_max) goto backup;
++o;
p->x0 = p->x - o->x;
if(p->x0 < 0) goto next;
p->y0 = p->y - o->y;
if(p->y0 < 0) goto next;
if(p->x0 + o->rng_x > dim_x) goto next;
if(p->y0 + o->rng_y > dim_y) goto next;
if(p->z + o->rng_z > dim_z) goto next;
// the piece fits in the box.
// Look for collision.
p->xy = (short)p->y0 * BOXWIDTH + p->x0;
s = o->pattern;
for(k=0; k<o->slices; ++k, ++s)
if(ws[p->xy+s->xy] & s->bits) goto next;
#if DEBUG
printf("place{%d,%d,%d ", p->x, p->y, p->z);
print_o(o);
sleep(3);
#endif
s = o->pattern;
for(k=0; k<o->slices; ++k, ++s)
ws[p->xy+s->xy] |= s->bits;
goto advance;

backup:
#if DEBUG
puts("}");
#endif
if(--lev < 0) {
puts("no solution");
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
s = o->pattern;
for(k=0; k<o->slices; ++k, ++s)
ws[p->xy+s->xy] ^= s->bits;
goto next;
}

// Here begins the node approach to finding solutions.
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
static long nodesCache; // nodes stored in cache
static long *hashIdx; // array of hashed indexes
static int megaNodes; // millions of nodes that can be cached
static long maxNodes; // megaNodes times a million
static long slopNodes; // maxNodes plus some slop for the randomness of the hash
static int hwm; // high water mark on the cache
static long nodesPending; // nodes yet to process
static long lastDisk;
static long mon_idx; // for markOldNodes()
static long nodeStep;
static int workStep;
static long *workList; // the list of discovered nodes to expand
static int workEnd, workAlloc;

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

for(i=0; i<60; ++i) {
if(fd[i] > 0) close(fd[i]);
flags = O_CREAT|O_TRUNC|O_RDWR|O_BINARY;
*xptr = 'A' + i;
fd[i] = open(filename, flags, 0666);
if(fd[i] < 0) bailout("cannot create data file, errno %d", errno);
} /* loop over files */

if(workList) free(workList);
workAlloc = 60;
workList = emalloc(4*workAlloc);
workEnd = 0;

// assumes dim_x and dim_y are set
curNodeWidth = BOXWIDTH * BOXWIDTH * (1+r_shorts);
nodeSize = sizeof(struct NODE) - BOXWIDTH*BOXWIDTH*2 + curNodeWidth;
nodeSize = (nodeSize + 3) & ~3;
nodesInFile = 0x7fff0000 / nodeSize;
maxNodes = megaNodes * 0x100000;
slopNodes = maxNodes / 8 * 9;
reachup = 0;

if(!hashIdx) hashIdx = emalloc(slopNodes * sizeof(long));
memset(hashIdx, 0, slopNodes*sizeof(long));
nodesCache = 0;
hwm = 0;
nodesDisk = 1; /* the initial node of all zeros is at location 0 */
mon_idx = 1;
nodesPending = 1;
curDepth = 0;
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
*hb |= 0x80000000;
--nodesCache;
return; /* found it */
}
++n, ++hb;
if(n == slopNodes) n = 0, hb = hashIdx;
}

/* Apparently it was already removed from the cache. */
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
int j, k;
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
mask = (nt->pattern.b[y*dim_x + x] << 8);
mask ^= 0xffff;
mask >>= diff;
if(mask & (nb->pattern.b[y*dim_x + x] << 8)) return 0;
mask |= (nb->pattern.b[y*dim_x + x] << 8);
b[y*BOXWIDTH + x] = mask;
}

advance:
if(++lev >= MAXLAYER)
bailout("placement stack overflow %d", MAXLAYER);
++p;

// find location to place the piece
if(!lev) x = y = z = 0;
else {
x = p->x, y = p->y, z = p->z;
#if DIAG
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
#else
while(isHighbit(b[y*BOXWIDTH + x])) {
if(++x < dim_x) continue;
x = 0;
if(++y == dim_y) break;
}
#endif
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
#if DIAG
x = y = 0;
goto relocate;
#else
x = r_x, y = r_y;
#endif
}
}

++p;
p->x = x, p->y = y, p->z = z;
p->onum = -1;
o = o_list - 1;

next:
if(++p->onum == o_max) goto backup;
++o;
p->x0 = p->x - o->x;
if(p->x0 < 0) goto next;
p->y0 = p->y - o->y;
if(p->y0 < 0) goto next;
if(p->x0 + o->rng_x > dim_x) goto next;
if(p->y0 + o->rng_y > dim_y) goto next;
// the piece fits in the box.
// Look for collision.
p->xy = (short)p->y0 * BOXWIDTH + p->x0;
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
int k, last_k = COLORS - 1;
int added;
int r1, r2; // rotations in the D4 group
shapebits mask;
char c;
const struct SF *p;
const struct ORIENT *o;
const struct SLICE *s;
struct NODE n1, n2;
struct NODE n3; // just a work area
static struct NODE floor;
uchar used[COLORS];

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
bailout("cannot fill the space between two successive nodes.", 0);
}

for(p=betweenstack; added; --added, ++p) {
z0 = n1.depth + p->z;
x0 = p->x0, y0 = p->y0;
o = p->onum + o_list;
// find the colors that touch this piece.
memset(used, 0, sizeof(used));
s = o->pattern;
for(k=0; k<o->slices; ++k, ++s) {
x = s->xy / BOXWIDTH;
y = s->xy % BOXWIDTH;
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

if(robin) {
k = last_k;
c = '*';
do { ++k;
if(k == COLORS) k = 0;
if(!used[k]) { c = k+'a'; last_k = k; break; }
} while(k != last_k);
} else {
for(k=0; k<COLORS; ++k) if(!used[k]) break;
c = k < COLORS ? 'a'+k : '*';
}

s = o->pattern;
for(k=0; k<o->slices; ++k, ++s) {
x = s->xy / BOXWIDTH;
y = s->xy % BOXWIDTH;
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
char c;
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
downToFloor(leftBoard, left);
memset(rightBoard, '?', boxVolume);
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
if(!sol) bailout("cannot create solution file %s", (int)solname);

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
int reset = -1;
int breakLine = REPDIAMETER; // the first piece will ratchet it down
int x, y, j, k;
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
b0[y*BOXWIDTH + x] = (base_b[y*dim_x + x]<<8);
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
if(!lev) x = y = 0;
else {
x = p->x, y = p->y;

#if DIAG
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
#else

while(b0[y*BOXWIDTH+x] & min_z_bit) {
if(++x < dim_x) continue;
x = 0;
if(++y == dim_y) break;
}
#endif

if(y == dim_y)
bailout("no empty square found at level %d", min_z);
}

++p;
p->x = x, p->y = y;
// in in solve() above, x y and z are absolute;
// here x and y are absolute, but z is relative to the node.
p->z = min_z;
p->mzc = min_z_count;
#if DEBUG
printf("locate %d,%d,%d\n", x, y, min_z);
#endif
p->breakLine = breakLine;
p->onum = -1;
o = o_list - 1;

next:
if(++p->onum == o_max) goto backup;
++o;
p->x0 = p->x - o->x;
if(p->x0 < 0) goto next;
p->y0 = p->y - o->y;
if(p->y0 < 0) goto next;
if(p->x0 + o->rng_x > dim_x) goto next;
if(p->y0 + o->rng_y > dim_y) goto next;
// the piece fits in the box.
// Look for collision.
p->xy = (short)p->y0 * BOXWIDTH + p->x0;
s = o->pattern;
for(k=0; k<o->slices; ++k, ++s)
if(b0[p->xy+s->xy] & (s->bits>>min_z)) goto next;
#if DEBUG
printf("place{%d,%d,%d ", p->x, p->y, min_z);
print_o(o);
sleep(3);
#endif
s = o->pattern;
for(k=0; k<o->slices; ++k, ++s) {
shapebits t = (s->bits>>min_z);
b0[p->xy+s->xy] |= t;
if(t&min_z_bit) --min_z_count;
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
min_z = p->z;
min_z_bit = (HIGHBIT >> min_z);
min_z_count = p->mzc;
o = o_list + p->onum;
// unplace piece
s = o->pattern;
for(k=0; k<o->slices; ++k, ++s)
b0[p->xy+s->xy] ^= (s->bits>>min_z);
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
b1[y*BOXWIDTH + x] = (base_b[y*dim_x + x]<<8);

for(q=stack; q<p; ++q) {
o = q->onum + o_list;
j = o->breakLine + q->z - breakLine;
if(j > 0) continue;
if(j == 0 && o->ambig && !ambinclude) {
ambnode = 1;
continue;
}

// place piece
j = q->z;
s = o->pattern;
for(k=0; k<o->slices; ++k, ++s)
b1[q->xy+s->xy] |= (s->bits>>j);
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
if(b1[y*BOXWIDTH + x] != (base_b[y*dim_x + x] << 8)) goto notsame;
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

if(!stopstore(newnode)) {
int rc = findNode(&newnode, 1, &looknode);
if(rc) goto ambtest;
}

if(newnode.depth + reachup >= minDepth) {
// by inserting first, this complement check now tests whether
// the node matches itself.
// need a signed right shift here.
mask = ((short)HIGHBIT >> (newnode.gap-1));
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x) {
j = y*dim_x + x;
if(r_shorts)
compnode.pattern.s[j] = (reverseShort((newnode.pattern.s[j]^mask)) << (16-newnode.gap));
else
compnode.pattern.b[j] = (reverseByte((uchar)(newnode.pattern.b[j]^mask)) << (8-newnode.gap));
}
if(findNode(&compnode, 0, &looknode))
matchFound(&newnode, &looknode);
}

ambtest:
if(ambnode && !ambinclude) { ambnode = 0; ambinclude = 1; goto recomplete; }
goto backup;
}
