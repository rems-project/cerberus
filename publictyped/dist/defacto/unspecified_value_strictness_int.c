#include <stdio.h>
int main() {
  int i; 
  int *p = &i;
  int j = (i-i);    // is this an unspecified value?
  _Bool b = (j==j); // can this be false?
  printf("b=%s\n",b?"true":"false"); 
}
