#include <stdio.h>
#include <stdint.h>
void foo(void) {
  int z=0;
  printf("ADDRESSES &z=%p\n",(void*)&z);

  // clang 6.0
  //intptr_t offset = 0x4; 
  //int *p = (int*)(((intptr_t)&z) - offset);

  // gcc 8.1
  intptr_t offset = 0x20;
  int *p = (int*)(((intptr_t)&z) + offset);

  printf("ADDRESSES  p=%p\n",(void*)p);
  *p=32;
  return;
}

void gee(int *c) {
  *c=1;
  return;
}

int main(void) {
  int a=0;
  int *c = &a;
  foo();
  int b=a;
  gee(c);
  printf("ADDRESSES  c=%p\n",(void*)c);
  printf("b=%d\n",b);
}

// if you make all casts from integer to pointer allowed to access any live object, then this would be well-defined and should print 32.

// But GCC misoptimises (wrt that semantics):
// 
// limbus:de_facto_memory_model$ ~km569/usr/bin/gcc-8.1 -std=c11 -Wall -Wno-unused-variable -pedantic pointer_from_integer_gil_2.c -O2 && ./a.out
// ADDRESSES &z=0x7ffc6c15eaec
// ADDRESSES  p=0x7ffc6c15eb0c
// ADDRESSES  c=0x7ffc6c15eb0c
// b=0
// 
// while Clang is more conservative:
//
// limbus:de_facto_memory_model$ ~km569/Applications/clang+llvm-6.0.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang-6.0 -std=c11 -Wall -Wno-unused-variable -pedantic pointer_from_integer_gil_2.c -O2 && ./a.out
// ADDRESSES &z=0x7ffd125c67ec
// ADDRESSES  p=0x7ffd125c67e8
// ADDRESSES  c=0x7ffd125c67e8
// b=32
// 
//  Gil: LLVM wouldn't optimise b to 0, because a has escaped.  GCC does some flow-sensitive analysis so it knows a hasn't escaped at the foo() point. 

// Gil guesses that if we didn't take the address of c, LLVM would do constant propagation (but then we can't print the address of c)
