#include <stdio.h>

int main () {
  int i = (i = 1, i++);
  printf("%d\n", i);
  return 0;
}
