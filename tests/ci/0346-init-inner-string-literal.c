#include <stdio.h>

// STD §6.7.9#14: a string literal may initialise an array of character type
// that is *not* the whole declared object -- a member, or a row of a
// multidimensional array.

struct S { char s[4]; int n; };
struct S x = { "abc", 7 };

// truncated (no terminating null) and zero-padded rows
char c[3][4] = { "ab", "cdef" };

struct T { char tag[2]; char name[5]; };
struct T t = { "hi", "abc" };

// a string literal reached by a designator
struct S d = { .n = 3, .s = "xy" };

int main(void)
{
  printf("x= {\"%s\", %d}\n", x.s, x.n);
  printf("c= {\"%s\", %c%c%c%c, \"%s\"}\n",
    c[0], c[1][0], c[1][1], c[1][2], c[1][3], c[2]);
  printf("t= {%c%c, \"%s\"}\n", t.tag[0], t.tag[1], t.name);
  printf("d= {\"%s\", %d} (s[2]=%d s[3]=%d)\n", d.s, d.n, d.s[2], d.s[3]);
}
