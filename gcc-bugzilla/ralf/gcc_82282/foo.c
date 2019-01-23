#include <stdio.h>
#include <stdint.h>

int* glb;
int* tmp[10];

int main(int argc, char** argv) {
  int x[1] = { 555 }, y[1] = { 777 };
  uintptr_t u = (uintptr_t) (x + 1);
  uintptr_t v = (uintptr_t) y;
  uintptr_t w;

  int b1 = u != v;
  int b2 = u+1 != v+1;

  int* z;

  if (b1) {
    printf("b1 TRUE.\n");
    v = u;
  }
  glb = (int*) v;

  for (int i=0; i < 10; i++)
    tmp[i] = (int*) v;

  if (b2) {
    printf("b2 TRUE.\n");
    glb = x;
  }

  w = u;
  for (int i = 0; i < 100; ++i) {
    if (w < v) {
      w += 1;
    }
  }

  if (v == w) {
    z = x;
  } else {
    printf("IMPOSSIBLE!\n");
    z = y;
  }
  *z = 555;

  *glb = 1;

  printf("x=%d y=%d\n", x[0], y[0]);
}