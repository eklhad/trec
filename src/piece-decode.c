/* Print binary notation for a polyomino. */
#include <ctype.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void nputchar(const int c, const unsigned int n)
{
for (unsigned int i = 0; i < n; i++) {
putchar(c);
}
}

int main(int argc, char *argv[])
{
int return_value = EXIT_SUCCESS;
if (argc == 1) {
printf("%s: print binary notation for a polyomino.\n", argv[0]);
puts("Use an argument in hexadecimal notation for each polyomino.");
puts("Each row of the polyomino must use a minimum of two hexadecimal digits.");
puts("These two digits can show up to eight columns of a row of the polyomino.");
puts("For wider rows, use more pairs of hexadecimal digits in braces.");
puts("Use + to show that a polyomino that is nine columns wide uses the ninth column.");
puts("This is equivalent to {80}.");
puts("In a three-dimensional polyomino,");
puts("use ! to separate the layers.");
puts("Use -q as an argument to not show the size or the dimensions of the polyomino.");
} else {
const char *hexadecimal = "0123456789ABCDEFabcdef";
bool stop = false;
bool quiet = false;
for (int i = 1; i < argc; i++) {
if (strcmp(argv[i], "-q") == 0) {
quiet = true;
} else if (argv[i][0] == '\0') {
fprintf(stderr, "argument %d is blank\n", i);
return_value = EXIT_FAILURE;
stop = true;
} else {
char *s = argv[i];
while (*s != '\0') {
bool invalid = false;
bool hex = false;
unsigned int braces = 0;
while (*s != '\0' && *s != '_') {
const size_t len = strspn(s, hexadecimal);
s += len;
if ((len % 2) != 0) {
s--;
invalid = true;
break;
} else if (len != 0) {
hex = true;
if (braces == 2) {
braces = 0;
}
} else {
if (*s == '!' && hex == true && (braces % 2) == 0 && isxdigit(s[1])) {
hex = false;
braces = 0;
} else if (*s == '}' && hex == true && braces == 1) {
braces = 2;
} else if (*s == '{' && hex == true && braces == 0 && isxdigit(s[1])) {
hex = false;
braces = 1;
} else if (*s == '+' && hex == true && braces == 0) {
braces = 2;
} else {
invalid = true;
break;
}
s++;
}
}
if (*s == '_') {
if (hex == true && (braces % 2) == 0 && isxdigit(s[1])) {
hex = false;
braces = 0;
s++;
} else {
invalid = true;
}
}
if (invalid == true) {
fprintf(stderr, "argument %d: character %u is invalid: %s\n", i, s - argv[i] + 1, argv[i]);
if (isxdigit(*s)) {
fputs("Hexadecimal digits must occur in pairs.\n", stderr);
} else if (braces == 1) {
fputs("Only hexadecimal characters can occur between braces.\n", stderr);
} else if (*s == '+') {
fputs("Hexadecimal characters must come before +.\n", stderr);
} else if (*s == '{') {
fputs("Hexadecimal characters must come before and after {.\n", stderr);
} else if (*s == '}') {
fputs("{ and hexadecimal characters must come before }.\n", stderr);
} else if (*s == '!' || *s == '_') {
fprintf(stderr, "Valid rows must come before and after %c.\n", *s);
}
return_value = EXIT_FAILURE;
stop = true;
break;
} else if (braces == 1) {
fprintf(stderr, "argument %d has a { without a }\n", i);
return_value = EXIT_FAILURE;
stop = true;
break;
}
}
}
}
if (stop == false) {
bool first = true;
for (int i = 1; i < argc; i++) {
if (strcmp(argv[i], "-q") == 0) {
} else {
char *s = argv[i];
while (*s != '\0') {
char *t = s;
unsigned int braces = 0;
if (first == false) {
putchar('\n');
} else {
first = false;
}
if (quiet == false) {
printf("piece: ");
}
unsigned int size = 0;
unsigned int column = 0;
unsigned int columns = 0;
unsigned int nibble = 0;
unsigned int row = 1;
unsigned int rows = 0;
unsigned int layer = 1;
unsigned int layers = 0;
while (*s != '\0' && *s != '_') {
if (quiet == false) {
putchar(*s);
}
char *const match = strchr(hexadecimal, *s);
if (match != NULL) {
size_t j = match - hexadecimal;
if (j > 15) {
j -= 6;
}
unsigned int len = 0;;
unsigned int k = 8;
unsigned int bit = 0;
while (k != 0) {
bit++;
if (j & k) {
size++;
len = bit;
}
k /= 2;
}
if ((braces == 0 && nibble == 2) || braces == 2) {
braces = 0;
nibble = 0;
row++;
}
if (len != 0) {
column = 4 * nibble + len;
if (columns < column) {
columns = column;
}
}
if (rows < row) {
rows = row;
}
if (layers < layer) {
layers = layer;
}
nibble++;
} else if (*s == '!') {
nibble = 0;
column = 0;
braces = 0;
layer++;
row = 1;
} else if (*s == '}') {
braces = 2;
} else if (*s == '{') {
braces = 1;
} else if (*s == '+') {
size++;
if (columns < 9) {
columns = 9;
}
braces = 2;
}
s++;
}
putchar('\n');
if (quiet == false) {
printf("size: %u\n", size);
printf("layers: %u\n", layers);
printf("rows: %u\n", rows);
printf("columns: %u\n", columns);
}
if (columns != 0) {
braces = 0;
column = 0;
nibble = 0;
row = 1;
layer = 1;
s = t;
while (*s != '\0' && *s != '_') {
char *const match = strchr(hexadecimal, *s);
if (match != NULL) {
size_t j = match - hexadecimal;
if (j > 15) {
j -= 6;
}
if ((braces == 0 && nibble == 2) || braces == 2) {
nputchar('0', columns - column);
putchar('\n');
braces = 0;
row++;
nibble = 0;
column = 0;
}
unsigned int k = 8;
while (k != 0 && column < columns) {
if (j & k) {
putchar('1');
} else {
putchar('0');
}
k /= 2;
column++;
}
nibble++;
} else if (*s == '!') {
nputchar('0', columns - column);
putchar('\n');
braces = 0;
nibble = 0;
column = 0;
while (row < rows) {
nputchar('0', columns);
putchar('\n');
row++;
}
nputchar('-', columns);
putchar('\n');
row = 1;
layer++;
} else if (*s == '}') {
braces = 2;
} else if (*s == '{') {
braces = 1;
} else if (*s == '+') {
putchar('1');
column = 9;
braces = 2;
}
s++;
}
nputchar('0', columns - column);
putchar('\n');
braces = 0;
nibble = 0;
column = 0;
while (row < rows) {
nputchar('0', columns);
putchar('\n');
row++;
}
}
if (*s == '_') {
s++;
}
}
}
}
}
}
return return_value;
}
