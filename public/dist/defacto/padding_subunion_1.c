#include <stdio.h>
#include <stdlib.h>
typedef struct { char c1; } st1;
typedef struct { float f2; } st2;
typedef union { st1 s1; st2 s2; } un;
int main() {
  // is this free of undefined behaviour?
  un* u = (un*)malloc(sizeof(st1));
  u->s1.c1 = 'a';
  printf("u->s1.c1=0x%x\n",(int)u->s1.c1);
}

