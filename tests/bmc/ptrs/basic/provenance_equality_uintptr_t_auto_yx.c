#include <inttypes.h> 
int main() {
  int y=2, x=1;
  uintptr_t p = (uintptr_t)(&x + 1);
  uintptr_t q = (uintptr_t)&y;
  _Bool b = (p==q);
  // can this be false even with identical addresses?
  
  return 0;
}
