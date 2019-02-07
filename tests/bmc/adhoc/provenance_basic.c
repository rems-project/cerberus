#include <stdint.h>
int x=1, y=2;
int main() {
  int *p = &x + 1;
  int *q = &y;
  __BMC_ASSUME((intptr_t)p==(intptr_t)q);
  if ((intptr_t)p == (intptr_t)q)
    *p = 11; // does this have UB?
 }
