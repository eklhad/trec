/* hexsol.c: find all solutions to the hex puzzle (pentomino packings */

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>

int w, l; /* width and lefgth */
int w1, l1;
int w2, l2;
char wcenter, lcenter, ocenter;
int btype = 3; /* board type, 3 is standard */
// board holds the transpose of what you see with the -d option
char board[5*22];

char shapes[][5] = {
{1, 7,8,9,16},
{2, 1,2,3,4},
{2, 8,16,24,32},
{3, 1,2,8,16},
{3, 1,2,10,18},
{3, 8,14,15,16},
{3, 8,16,17,18},
{4, 1,2,9,17},
{4, 6,7,8,16},
{4, 8,15,16,17},
{4, 8,9,10,16},
{5, 1,2,8,10},
{5, 1,9,16,17},
{5, 2,8,9,10},
{5, 1,8,16,17},
{6, 1,7,8,15},
{6, 1,9,10,18},
{6, 7,8,14,15},
{6, 8,9,17,18},
{7, 1,8,15,16},
{7, 8,9,10,18},
{7, 1,9,17,18},
{7, 6,7,8,14},
{8, 1,2,3,8},
{8, 1,9,17,25},
{8, 5,6,7,8},
{8, 8,16,24,25},
{8, 8,9,10,11},
{8, 1,8,16,24},
{8, 1,2,3,11},
{8, 8,16,23,24},
{9, 1,2,8,9},
{9, 1,8,9,17},
{9, 1,7,8,9},
{9, 8,9,16,17},
{9, 1,8,9,10},
{9, 1,8,9,16},
{9, 1,2,9,10},
{9, 7,8,15,16},
{10, 1,2,3,9},
{10, 7,8,16,24},
{10, 6,7,8,9},
{10, 8,16,17,24},
{10, 1,2,3,10},
{10, 8,15,16,24},
{10, 7,8,9,10},
{10, 8,9,16,24},
{11, 1,9,10,11},
{11, 7,8,15,23},
{11, 1,2,10,11},
{11, 8,15,16,23},
{11, 1,2,7,8},
{11, 8,9,17,25},
{11, 1,6,7,8},
{11, 8,16,17,25},
{12, 1,9,10,17},
{12, 6,7,8,15},
{12, 7,8,16,17},
{12, 7,8,9,15},
{12, 1,7,8,16},
{12, 7,8,9,17},
{12, 8,9,15,16},
{12, 8,9,10,17},
{0, 0,0,0,0},
};

static void rebuildShapes(void)
{
int i, j, k, r, c;
for(i=0; shapes[i][0]; ++i) {
for(j=1; j<5; ++j) {
k = shapes[i][j];
k += 3;
r = k/8;
c = k%8;
c -= 3;
k = w2*r + c;
shapes[i][j] = k;
}
}
}

/* valid positions for the cross */
/* prevents reflections and rotations */
/* But extra code is needed if the width or height is odd */
int cross_all[6][10] = {
{12, 37, 0},
{14, 20, 26, 32, 38, 44, 0},
{10, 16, 17, 23, 24, 30, 31, 37, 38, 0},
{11, 18, 19, 26, 27, 34, 35 , 0},
{0},
{13,14,23,0}
};
int *cross_pos;

/* flipp through width and look for asymmetry */
static int wflip(void)
{
int i, j;
for(i=1; i<l2; ++i) {
for(j=1; j<=2; ++j) {
int d = board[i*w2+j] - board[i*w2+w1-j];
if(!d) continue;
return (d > 0);
}
}
}

static int lflip(void)
{
int i, j;
for(i=1; i<w2; ++i) {
for(j=1; j<=7; ++j) {
int d = board[j*w2+i] - board[(l1-j)*w2+i];
if(!d) continue;
return (d > 0);
}
}
}

/*********************************************************************
Horizontal split, only applicable on the standard board.
The count comes out 16, but the top piece, having the cross on its left,
can be reflected vertically,
while the bottom can be reflected or rotated, thus 8 combinations.
There are really only 2 split solutions as follows.

	EEEIIBJJJJ
	EAEIIBGJHH
	AAALIBGGGH
	CALLLBDFGH
	CKKKLBDFFH
	CCCKKDDDFF

	EEEIIBJJJJ
	EAEIIBGJHH
	AAAKIBGGGH
	CALKKBDFGH
	CLLLKBDFFH
	CCCLKDDDFF

*********************************************************************/

static int hsplit(void)
{
int i;
for(i=1; i<w1; ++i)
if(board[5*w2+i] == board[6*w2+i])
return 0;
return 1;
}

char used[13];
int level;
int nsols;
int nhs; /* number of horizontal splits */
char countflag, dispflag;


static void cross(int top) ;
static void place(void) ;
static int findloc(void) ;
static int test(int loc, int pattern) ;


void main(int argc, char **argv)
{
int i;

if(argc > 1) {
if(argv[1][0] == '-') {
if(argv[1][1] == 'c') countflag = 1;
if(argv[1][1] == 'd') dispflag = 1;
++argv, --argc;
}
}

/* specify the width of the board as an argument */
if(argc > 1) {
if(isdigit(argv[1][0]) && argv[1][1] == 0)
btype = argv[1][0] - '3';
else btype = -1;
}
if(argc > 2 || btype < 0 || btype > 5 || btype == 4) {
fprintf(stderr, "usage: hexsol [-c|-d] width\n");
exit(1);
}

w = btype + 3;
l = 60 / w;
if(w == 8) l = 8;
l1 = l + 1, w1 = w + 1;
l2 = l + 2, w2 = w + 2;
for(i=0; i<w2; ++i) {
board[i] = -1;
board[w2*l1+i] = -1;
}
for(i=0; i<l2; ++i) {
board[w2*i] = -1;
board[w2*i+w1] = -1;
}
if(w == 8) {
board[10*5+5] = 26;
board[10*4+5] = 26;
board[10*4+4] = 26;
board[10*5+4] = 26;
}

rebuildShapes();

level = 1;
nsols = 0;
for(i=1; i<13; ++i) used[i] = 0;

cross_pos = cross_all[btype];
for(i=0; cross_pos[i]; ++i) {
/* w = 3 handled in place() */
lcenter = wcenter = ocenter = 0;
if(w == 4 && i == 5) lcenter = 1;
if(w == 5 && !(i&1)) wcenter = 1;
if(w == 8 && i == 2) ocenter = 1;
cross(cross_pos[i]);
}

if(countflag) printf("%d solutions\n", nsols);
exit(0);
} /* main */

/* position the cross, and go */
static void cross(int top)
{
int i;
int piece;

piece = shapes[0][0];
used[piece] = 1;
for(i=1; i<5; ++i)
board[top + shapes[0][i]] = piece;
board[top] = piece;

place();

for(i=1; i<5; ++i)
board[top + shapes[0][i]] = 0;
board[top] = 0;
used[piece] = 0;
} /* cross */

/* place a piece in the board; recursive */
static void place(void)
{
short i, loc;
char piece;

/* find best location */
loc = findloc();
if(!loc) return; /* square that no piece fits into */
++level;

for(i=1; shapes[i][0]; ++i) {
if(!test(loc, i)) continue;

// When width is 3, we know what the solutions are.
// Keep Utah on the right and that fixes symmetry.
if(loc == 21 && w == 3 && shapes[i][0] == 9) continue;

/* place the piece */
piece = shapes[i][0];
#ifdef DEBUG
printf("placing piece %d[%d] at square %d, level %d\n", piece, i, loc, level);
#endif
used[piece] = 1;
board[loc] = piece;
board[loc + shapes[i][1]] = piece;
board[loc + shapes[i][2]] = piece;
board[loc + shapes[i][3]] = piece;
board[loc + shapes[i][4]] = piece;

if(level == 12) {
if(wcenter && wflip() || lcenter && lflip() ||
ocenter && board[13] > board[31]) {
; /* skip this one */
} else {
int row, col;

++nsols;
if(w == 6 && hsplit()) ++ nhs;
/* print solution */
if(!countflag) {
for(col=1; col<w1; ++col) {
for(row=1; row<l1; ++row)
putchar('A'-1 + board[w2*row + col]);
if(dispflag) putchar('\n');
}
putchar('\n');
}
}
} else place();

/* remove piece */
used[piece] = 0;
board[loc] = 0;
board[loc + shapes[i][1]] = 0;
board[loc + shapes[i][2]] = 0;
board[loc + shapes[i][3]] = 0;
board[loc + shapes[i][4]] = 0;
}

--level;
} /* place */

static int findloc(void)
{
int i;
for(i=w2+1; i<w2*l1-1; ++i)
if(!board[i]) return i;
return 0; /* should never happen */
} /* findloc */

static int test(int loc, int pattern)
{
char *s, *b;
char piece;

s = shapes[pattern];
piece = *s++;
if(used[piece]) return 0;

b = board + loc;
if(b[*s++]) return 0;
if(b[*s++]) return 0;
if(b[*s++]) return 0;
if(b[*s]) return 0;
return 1;
} /* test */

