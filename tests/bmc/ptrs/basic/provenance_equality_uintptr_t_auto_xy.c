#include <inttypes.h> 
int main() {
  int x=1, y=2;
  uintptr_t p = (uintptr_t)(&x + 1);
  uintptr_t q = (uintptr_t)&y;
  //printf("Addresses: p=%" PRIxPTR " q=%" PRIxPTR "\n",
   //      p,q);
  _Bool b = (p==q);

  assert (b == 1);
  return b;
}
