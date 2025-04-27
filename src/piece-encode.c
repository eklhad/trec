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
puts("use an argument of \"-\" to separate the layers.");
} else {
bool valid = true;
bool quiet = false;
for (int i = 1; i < argc; i++) {
if (strcmp(argv[i], "-") == 0) {
} else if (strcmp(argv[i], "-q") == 0) {
quiet = true;
} else {
const size_t len = strspn(argv[i], "01");
if (argv[i][len] != '\0') {
valid = false;
fprintf(stderr, "argument %d: character %zu is invalid: %s\n", i, len + 1, argv[i]);
return_value = EXIT_FAILURE;
}
}
}
if (valid) {
size_t parts = 0;
for (int i = 1; i < argc; i++) {
if (strcmp(argv[i], "-") == 0) {
if (i == 1) {
printf("00");
}
putchar('!');
} else if (strcmp(argv[i], "-q") == 0) {
} else {
size_t len = 0;
const char *last = strrchr(argv[i], '1');
if (last != NULL) {
len = last - argv[i] + 1;
}
if(!len) {
printf("00");
continue;
}
size_t value = 0;
size_t factor = 128;
size_t j = 0;
while (j < len) {
const char c = argv[i][j++];
if (c == '1') {
parts++;
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
putchar('\n');
if (quiet == false) {
printf("Total: %zu\n", parts);
}
}
}
return return_value;
}
