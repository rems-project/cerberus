#include <stdio.h>
#include <stddef.h>
typedef struct { float f; int i; } st;
int main() {
  st s = {.f=1.0, .i=1};
  int *pi = &(s.i);
  unsigned char *pci = ((unsigned char *)pi);
  unsigned char *pcf = (pci - offsetof(st,i)) 
    + offsetof(st,f);
  float *pf = (float *)pcf;
  *pf = 2.0;  // is this free of undefined behaviour?
  printf("s.f=%f *pf=%f  s.i=%i\n",s.f,*pf,s.i);
}

