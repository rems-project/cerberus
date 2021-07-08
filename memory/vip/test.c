#include <stdint.h>

int main(void)
{
  int x = 1012;
  int *p = &x;

  uintptr_t i = (uintptr_t) p;

  //int* q = (int*) (i + 0); fails correctly.
  int* q = (int*) i;

  int y = *q;

  return x + 10;
}
