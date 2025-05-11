/* Print hexadecimal notation for a polyomino. */
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char *argv[])
{
int return_value = EXIT_SUCCESS;
if (argc == 1) {
printf("%s: print hexadecimal notation for a polyomino.\n", argv[0]);
puts("Use an argument for each row of the polyomino.");
puts("In such an argument, use 0 for a gap and 1 for a part of the polyomino.");
puts("Any trailing 0 is optional.");
puts("In a three-dimensional polyomino,");
puts("use one or more - as an argument to separate the layers.");
puts("Use -q as an argument to not show the size of the polyomino.");
} else {
bool invalid = false;
bool quiet = false;
for (int i = 1; i < argc; i++) {
if (argv[i][0] == '-' && strspn(argv[i], "-") == strlen(argv[i])) {
} else if (strcmp(argv[i], "-q") == 0) {
quiet = true;
} else {
const size_t len = strspn(argv[i], "01");
if (argv[i][len] != '\0') {
invalid = true;
fprintf(stderr, "argument %d: character %zu is invalid: %s\n", i, len + 1, argv[i]);
return_value = EXIT_FAILURE;
}
}
}
if (invalid == false) {
unsigned int rows = 0;
unsigned int size = 0;
for (int i = 1; i < argc; i++) {
if (argv[i][0] == '-' && strspn(argv[i], "-") == strlen(argv[i])) {
if (rows == 0) {
printf("00");
} else {
rows = 0;
}
putchar('!');
} else if (strcmp(argv[i], "-q") == 0) {
} else {
size_t len = 0;
const char *last = strrchr(argv[i], '1');
if (last != NULL) {
len = last - argv[i] + 1;
}
rows++;
if(len == 0) {
printf("00");
continue;
}
unsigned int value = 0;
unsigned int factor = 128;
size_t j = 0;
while (j < len) {
const char c = argv[i][j++];
if (c == '1') {
size++;
value += factor;
}
if (j == len || (j % 8) == 0) {
if (j == 9 && c == '1') {
putchar('+');
} else {
printf("%02x", value);
if (len > 9) {
if (j == 8) {
putchar('{');
} else if (j == len) {
putchar('}');
}
}
factor = 128;
value = 0;
}
} else {
factor /= 2;
}
}
}
}
if (rows == 0) {
printf("00");
}
putchar('\n');
if (quiet == false) {
printf("size: %u\n", size);
}
}
}
return return_value;
}
