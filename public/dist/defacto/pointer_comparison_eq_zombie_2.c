#include <stdio.h>
#include <stdlib.h>
int main() {
  int i=0;
  int *pj;
  {
    int j=1;
    pj = &j;
    printf("(&i==pj)=%s\n",(&i==pj)?"true":"false"); 
  }
  printf("(&i==pj)=%s\n",(&i==pj)?"true":"false");
  // is the == comparison above defined behaviour?
  return 0;
}
