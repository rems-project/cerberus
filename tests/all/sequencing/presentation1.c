#include "stdio.h"

int x = 0;

int main (void) {
  int result = (x += 0) + (x += 1);
  printf ("%d\n", result);
  return 0;
}
