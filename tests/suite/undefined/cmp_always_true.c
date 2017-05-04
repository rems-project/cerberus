#include "stdio.h"

int test(void) {
  int x;
  return (x+1) > x;
}

int main(void) {
  printf("%d\n", test());
  return 0;
}
