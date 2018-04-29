#include <stdio.h>
#include <stddef.h>
#include <string.h>
typedef struct { char c; float f; } st;
int main() {
  st s1 = {.c = 'A', .f = 1.0 };
  st s2;
  memcpy(&(s2.c), &(s1.c), sizeof(char)); 
  memset(&(s2.c)+sizeof(char),'X',
    offsetof(st,f)-offsetof(st,c)-sizeof(char));
  memcpy(&(s2.f), &(s1.f), sizeof(float)); 
  //memset(&(s2.f)+sizeof(float),'Y',
  //  sizeof(st)-offsetof(st,f)-sizeof(float));
  // is s2 now a copy of s1?
  printf("s2.c=%c s2.f=%f\n",s2.c,s2.f);
}

