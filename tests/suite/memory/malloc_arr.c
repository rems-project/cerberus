#include <stdlib.h>


int f2(void) {
  unsigned char *p_base = malloc(5 * sizeof(int));
  int *p_int = (int *) (p_base + (3 * sizeof(int)));
  
  return *p_int = 1;
}

int main(void) {
  f1();
  f2();
  return 0;
}
