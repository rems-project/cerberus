#include <stdio.h>
int main() {
  unsigned int i; 
  unsigned int *p = &i;
  unsigned int j = (i-i);    // is this an unspecified value?
  _Bool b = (j==j); // can this be false?
  printf("b=%s\n",b?"true":"false"); 
}
