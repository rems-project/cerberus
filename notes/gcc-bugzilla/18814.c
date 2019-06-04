#include <stdio.h>

int main() {
  int i = 0;
  int* p;
top:
  p = &((int) {1});
  printf("%p %d\n", p, *p);
  *p = 77;
  if (i++ == 0) goto top;
  return 0;
}
