#include <stdlib.h>
#include <stdio.h>
extern void bar(void*);
extern int foo(void){ 
  void* a = malloc(1);
  //printf("a=%p  ",a);
  bar(a);
  void* b = malloc(1);
  //printf("b=%p  ",b);
  return (a == b) ? 1 : 0;
}
