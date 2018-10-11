#include <stdio.h>
#include <stddef.h>
typedef struct { float f; int i; } st;
int main() {
  st s = {.f=1.0, .i=1};
  st *ps = &s;
  unsigned char *pcs = ((unsigned char*)ps);
  unsigned char *pci = (pcs + offsetof(st,i));
  unsigned char *pcf = (pci - offsetof(st,i)) 
    + offsetof(st,f);
  float *pf = (float *)pcf;
  *pf = 2.0;  // is this free of undefined behaviour?
  printf("s.f=%f *pf=%f  s.i=%i\n",s.f,*pf,s.i);
}

