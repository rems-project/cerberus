#include <stdlib.h>

int f1(void) {
  void *p_base = malloc(5 * sizeof(long));
  int (*p_arr)[5] = p_base;
  long *p_long    = p_base;
  
  *p_long = 1;
  return *p_arr[2] = 2;
}

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
