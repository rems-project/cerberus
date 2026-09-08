#include <stdio.h>

// STD §6.7.9#20: brace elision. The initialisers below have fewer braces
// than there are levels of aggregate, and the "current object" has to walk
// down into the sub-aggregates on its own.

struct T { int a; int b; };

// an array of structs, initialised with a flat list
struct T ts[2] = {1, 2, 3, 4};

// a multidimensional array, initialised with a flat list
int m[2][3] = {1, 2, 3, 4, 5, 6};

// a multidimensional array, partially braced (the remainder is zeroed)
int p[2][3] = {{1}, {4, 5}};

// a struct containing an array, initialised with a flat list
struct U { int x; int ys[3]; int z; };
struct U u = {1, 2, 3, 4, 5};

int main(void)
{
  printf("ts= {{%d, %d}, {%d, %d}}\n", ts[0].a, ts[0].b, ts[1].a, ts[1].b);
  printf("m= {{%d, %d, %d}, {%d, %d, %d}}\n",
    m[0][0], m[0][1], m[0][2], m[1][0], m[1][1], m[1][2]);
  printf("p= {{%d, %d, %d}, {%d, %d, %d}}\n",
    p[0][0], p[0][1], p[0][2], p[1][0], p[1][1], p[1][2]);
  printf("u= {%d, {%d, %d, %d}, %d}\n", u.x, u.ys[0], u.ys[1], u.ys[2], u.z);
}
