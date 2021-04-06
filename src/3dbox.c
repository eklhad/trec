/*********************************************************************
3dbox.c: fill a box with 3d polyominoes.
This is brute force and not terribly efficient,
or optimized the way trec.c is.
*********************************************************************/

static int nsq; // number of squares in the polyomino
static int dim_x, dim_y, dim_z; // box being filled
static int boxOrder, boxVolume;
static int ordFactor; // order must be a multiple of this
static int dimFactor; // each dimension must be a multiple of this
static int cbflag; // checkerboard flag

#include <stdio.h>
#include <stdlib.h>
#include <malloc.h>
#include <ctype.h>
#include <string.h>
#include <unistd.h>

#define DEBUG 0

#define REPDIAMETER 16 // represent pieces this large
#define NSQ 80 // number of squares in largest polyomino
#define SETSIZE 10 // number of pieces in the set
#define MAXORDER 1000

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
static shapebits orib3[REPDIAMETER][REPDIAMETER];

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

struct ORIENT { // describe an orientation
uchar pno; // piece number in the set
uchar ono; // orientation number
uchar x, y; // offset of lowest square
uchar rng_x, rng_y, rng_z; // rnage of this piece in this orientation
uchar filler;
shapebits pattern[REPDIAMETER][REPDIAMETER];
};

#define O_MAX 100
static struct ORIENT o_list[O_MAX];
static int o_max; /* number of orientations */
static int setSize; // for sets of polyominoes

static void print_o(const struct ORIENT *o)
{
int x, y;
for(y=0; y<o->rng_y; ++y) {
if(y) printf("!");
for(x=0; x<o->rng_x; ++x) {
shapebits mask = o->pattern[x][y];
printf("%02x", (mask>>8));
mask &= 0xff;
if(mask == 0x80) printf("+");
else if(mask) printf("{%02x}", mask);
}
}
/*
printf(" range %d,%d,%d start %d,%d", o->rng_x, o->rng_y, o->rng_z, o->x, o->y);
*/
printf("\n");
}

// translate back to the origin
static void pulldown(void)
{
int x, y, z, j;
int rng_x, rng_y, rng_z; // range of the piece
int start_x, start_y; // start_z will be 0 once adjusted
struct ORIENT *o;

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

for(y=0; y<REPDIAMETER; ++y)
for(x=0; x<REPDIAMETER; ++x)
if(orib2[x][y][0]) {
start_y = y, start_x = x;
goto pack;
}

pack:
for(x=0; x<REPDIAMETER; ++x)
for(y=0; y<REPDIAMETER; ++y) {
orib3[x][y] = 0;
for(z=0; z<REPDIAMETER; ++z)
if(orib2[x][y][z])
orib3[x][y] |= (0x8000>>z);
}

// Have we seen this one before?
o = o_list;
for(j=0; j<o_max; ++j, ++o)
if(!memcmp(orib3, o->pattern, sizeof(orib3)))
return;

if(o_max == O_MAX)
bailout("too many orientations, limit %d", O_MAX);
memcpy(o->pattern, orib3, sizeof(orib3));
o->ono = o_max;
o->pno = setSize;
o->x = start_x, o->y = start_y;
o->rng_x = rng_x + 1, o->rng_y = rng_y + 1, o->rng_z = rng_z + 1;
#if DEBUG
printf("range %d,%d,%d ", o->rng_x, o->rng_y, o->rng_z);
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
memcpy(orib2, orib1, sizeof(orib1));
for(r1=0; r1<3; ++r1) {
for(r2=0; r2<2; ++r2) {
for(r3=0; r3<2; ++r3) {
for(r4=0; r4<4; ++r4) {
pulldown();
memcpy(orib1, orib2, sizeof(orib2));
counterclockwise();
}
y_mirror();
}
point_mirror();
}
xyz_spin();
}
#if DEBUG
printf("%d orientations\n", o_max);
#endif
}

// Convert a hex-format representation of a polyomino into its bitmap,
// and derive all its rotations.
static void stringPiece(const char *hexrep)
{
int i, x, y, z;
shapebits mask;
const char *s = hexrep;
char c;
int nsqFirst = -1;

while(*s) {
if(setSize >= SETSIZE) bailout("too many pieces in the set, limit %d", SETSIZE);
memset(orib3, 0, sizeof(orib3));
nsq = 0;
i = y = 0;

while((c = *s) != 0 && c != '_') {
if(c == '!') { ++s; ++y; i=0;
if(y >= REPDIAMETER) bailout("polyomino is too wide, limit %d rows", REPDIAMETER);
continue; }
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
orib3[i][y] = mask;
++i;
} /* loop gathering the rows in this piece */

if(nsqFirst >= 0 && nsq != nsqFirst)
bailout("all polyominoes in the set must have the same number of squares", 0);
if(nsq > NSQ)
bailout("too many squares in the given polyomino, limit %d", NSQ);
nsqFirst = nsq;

// unpack into orib1
for(x=0; x<REPDIAMETER; ++x)
for(y=0; y<REPDIAMETER; ++y) {
mask = orib3[x][y];
for(z=0; z<REPDIAMETER; ++z) {
orib1[x][y][z] = isHighbit(mask);
mask <<= 1;
}
}

/* see if the checkerboard argument applies */
if(!(nsq&1)) {
i = 0;
for(x=0; x<REPDIAMETER; ++x)
for(y=0; y<REPDIAMETER; ++y)
for(z=0; z<REPDIAMETER; ++z)
if((x+y+z)&1) ++i; else --i;
if(i < 0) i = -i;
if(!setSize) cbflag = i;
else if(i != cbflag) cbflag = 0;
} /* even squares */

compileRotations();

if(*s) ++s;
++setSize;
} /* loop over pieces in the set */

if(cbflag) puts("checkerboard upgrade");
}

// find the highest empty bit in a short
// This is the opposite of the routine in trec.c
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

static int solve(void);

int main(int argc, const char **argv)
{
stringPiece(argv[1]);
dim_x = atoi(argv[2]);
dim_y = atoi(argv[3]);
dim_z = atoi(argv[4]);
boxVolume = dim_x * dim_y * dim_z;
if(boxVolume % nsq) bailout("volume %d does not admit a whole number of pieces", boxVolume);
boxOrder = boxVolume / nsq;
lowEmptySet();
solve();
return 0;
}

static struct SF { // like a stack frame
schar x, y, z; // where piece is placed
schar x0, y0; // adjusted location of piece
schar increase;
short onum;
} stack[MAXORDER];

static shapebits ws[REPDIAMETER][REPDIAMETER]; // our workspace

static void print_ws(void)
{
int x, y;
for(y=0; y<dim_y; ++y) {
for(x=0; x<dim_x; ++x)
printf("%02x", ws[x][y]>>8);
printf("|");
}
printf("\n");
}

static int solve(void)
{
int lev = -1;
struct SF *p = stack - 1;
struct ORIENT *o;
int x, y, z, j, k;

memset(ws, 0, sizeof(ws));

advance:
if(++lev == boxOrder) {
puts("solution!");
exit(0);
}
if(lev == MAXORDER) bailout("placement stack overflow %d", lev);
// find location to place the piece
if(!lev) x = y = z = 0;
else {
x = p->x, y = p->y, z = p->z;
while(isHighbit(ws[x][y])) {
if(++x < dim_x) continue;
x = 0;
if(++y == dim_y) break;
}
if(y == dim_y) { // have to push workspace down
int r_x, r_y;
j = REPDIAMETER;
for(y=0; y<dim_y; ++y)
for(x=0; x<dim_x; ++x) {
k = lowEmpty[ws[x][y]];
if(k < j) j = k, r_x = x, r_y = y;
}
if(!j) bailout("increase level is 0", 0);
p->increase = j;
z += j;
#if DEBUG
printf("push %d\n", j);
#endif
for(x=0; x<dim_x; ++x)
for(y=0; y<dim_y; ++y)
ws[x][y] <<= j;
x = r_x, y = r_y;
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
for(x=0; x<o->rng_x; ++x)
for(y=0; y<o->rng_y; ++y)
if(ws[p->x0+x][p->y0+y] & o->pattern[x][y]) goto next;
#if DEBUG
printf("place{%d,%d,%d ", p->x, p->y, p->z);
print_o(o);
#endif
for(x=0; x<o->rng_x; ++x)
for(y=0; y<o->rng_y; ++y)
ws[p->x0+x][p->y0+y] |= o->pattern[x][y];
goto advance;

backup:
#if DEBUG
puts("}");
#endif
if(--lev < 0) {
puts("no solution");
exit(0);
}
--p;
o = o_list + p->onum;
if(j = p->increase) {
shapebits m = ((short)HIGHBIT >> (j-1));
for(x=0; x<dim_x; ++x)
for(y=0; y<dim_y; ++y)
ws[x][y] = ( ws[x][y] >> j) | m;
p->increase = 0;
#if DEBUG
printf("pop %d\n", j);
//  print_ws();
#endif
}
for(x=0; x<o->rng_x; ++x)
for(y=0; y<o->rng_y; ++y)
ws[p->x0+x][p->y0+y] &= ~o->pattern[x][y];
goto next;

return 0;
}
