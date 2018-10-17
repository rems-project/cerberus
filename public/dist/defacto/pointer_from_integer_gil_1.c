#include <stdint.h>
#include <stdio.h>
intptr_t foo(intptr_t a, intptr_t b) {
  return (a==b)?b:a;
  //return a;
}

int main(void) {
  //  int y=0, x=0;
  int x=0, y=0;
  intptr_t a = (intptr_t)(&x+1);
  intptr_t b = (intptr_t)&y;
  if (a==b) {
    intptr_t c=foo(a,b);       //  b
    int *r = (int*)c;
    *r = 42;
    printf("y=%d\n",y);
  }
}


// In our model (and in Cerberus with concrete model, in which the allocations are adjacent) this is a well-defined program, printing 42 
// 
// In GCC -O2 (as Gil says) there is a miscompilation:
//   
// ~km569/usr/bin/gcc-8.1 -std=c11 -Wall -Wno-unused-variable -pedantic pointer_from_integer_gil_1.c -O2 && ./a.out
// y=0
// 
// because (presumably) the (a==b)?b:a is being optimised to a before alias analysis is done.
// 
// This is just like our provenance_lost_escape_1.c - we could ask the compiler to preserve the dependencies lost in the optimisation.



     
     
