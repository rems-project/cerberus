#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
typedef struct { char c1; } st1;
typedef struct { float f2; } st2;
typedef union { st1 s1; st2 s2; } un;
int main() {
  // check that st2 is bigger than st1 
  // (otherwise the test is uninteresting)
  assert(sizeof(st2) > sizeof(st1));
  // is this free of undefined behaviour?
  unsigned char* p = malloc(sizeof(st1)+sizeof(int));
  un* pu = (un*)p;
  char *pc = (char*)(p + sizeof(st1));
  *pc='B';
  pu->s1.c1 = 'A';
  // is this guaranteed to read 'B'?
  unsigned char c = *pc;
  printf("c=0x%x\n",(int)c);
}

