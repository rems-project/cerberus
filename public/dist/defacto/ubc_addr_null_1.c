#include <stddef.h>
#include <inttypes.h>
#include <stdio.h>
struct s { uint8_t a; uint8_t b; };
int main () {
  struct s *f = NULL;
  uint8_t *p = &(f->b); // free of undefined behaviour?
  // and equal to the offsetof result? 
  printf("p=%p  offsetof(struct s,b)=0x%zx\n",
         (void*)p,offsetof(struct s, b));
}

