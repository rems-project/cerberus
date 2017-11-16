#include <stdio.h>
#include <stddef.h>
typedef struct { int i; float f; int j; } st;
int main() {
  st s = {.i=1, .f=2.0, .j=3};
  int *pj = &(s.j);
  char *pcj = ((char *)pj);
  char *pcst = (pcj - (offsetof(st,j)-offsetof(st,i)));
  //are these two lines free of undefined behaviour?
  st *ps = (st *)pcst;
  ps->f = 22.0;
  printf("s.i=%i s.f=%f s.j=%i ps->f=%f\n",s.i,s.f,s.j,
         ps->f);
}
