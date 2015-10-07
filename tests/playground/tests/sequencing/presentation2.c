#include "stdio.h"

int x = 0;

int f(int i) {return x += i;}

int main (void) {
  int result = f (0) + f (1);
  printf ("%d\n", result);
  return 0;
}
