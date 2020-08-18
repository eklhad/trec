/* chiral.c: count pieces by orientation */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <memory.h>

#define NROWS 300
#define NCOLS 300
#define NP 120
#define NSQ 80

char board[NROWS][NCOLS];
short nrows, ncols;
short pieces[NP][NSQ];
short pcnt[NP];
short np, nsq, order;

static void eval(int, int, char);

static void
bailout(const char *msg, int arg)
{
fprintf(stderr, msg, arg);
fprintf(stderr, "\n");
exit(1);
} /* bailout */

int main(int argc, char **argv)
{
FILE *f;
short i, j, l;

if(argc != 2) bailout("usage:  chiral solution-file", 0);

f = fopen(argv[1], "r");
if(!f) bailout("cannot open %s", (int)argv[1]);

while(fgets(board[nrows], NCOLS, f)) {
l = strlen(board[nrows]);
--l; /* forget newline */
if(!ncols) { /* first row */
ncols = l;
if(ncols > NCOLS)
bailout("too many columnss, limit %d", NCOLS);
} else {
if(l != ncols)
bailout("file is not an ascii matrix, row %d", nrows);
}
++nrows;
if(nrows == NROWS)
bailout("too many rows, limit %d", NROWS);
}
fclose(f);

for(i=0; i<nrows; ++i) {
for(j=0; j<ncols; ++j) {
char c = board[i][j];
if(c) eval(i, j, c);
}
}

/* print out the stats */
printf("Order %d, orientations %d\n", order, np);
for(i=0; i<np; ++i) {
printf("%d:", pcnt[i]);
for(j=1; j<nsq; ++j) {
if(j > 1) printf(".");
printf("%d", pieces[i][j]);
}
printf("\n");
}

return 0;
} /* main */

static void eval(int x, int y, char base)
{
short this[NSQ];
short i, j, n;
char change = 1;

n = 1;
this[0] = x*NCOLS + y;
board[x][y] |= 0x80;

while(change) {
change = 0;
for(i=x; i<nrows; ++i) {
for(j=0; j<ncols; ++j) {
if(board[i][j] != base) continue; /* different letter */
if(i && board[i-1][j]&0x80) goto adjacent;
if(j && board[i][j-1]&0x80) goto adjacent;
if(i < nrows-1 && board[i+1][j]&0x80) goto adjacent;
if(j < ncols-1 && board[i][j+1]&0x80) goto adjacent;
continue;

adjacent:
board[i][j] |= 0x80;
if(n == NSQ)
bailout("piece at %d has too many squares, limit 50", 100*(x+1) + (y+1));
this[n] = i * NCOLS + j;
++n;
change = 1;
}
}
}

for(i=0; i<nrows; ++i)
for(j=0; j<ncols; ++j)
if(board[i][j]&0x80)
board[i][j] = 0;

if(nsq && n != nsq)
bailout("piece at %d has improper size", 100*(x+1) + (y+1));
nsq = n;

for(i=0; i<nsq; ++i)
this[i] -= NCOLS*x + y;

for(n=0; n<np; ++n)
if(!memcmp(pieces[n], this, nsq*2)) break;
if(n == np) { /* new piece */
if(n == NP)
bailout("too many orientations, limit %d", NP);
memcpy(pieces[n], this, nsq*2);
++np;
}
++pcnt[n];
++order;
} /* eval */

