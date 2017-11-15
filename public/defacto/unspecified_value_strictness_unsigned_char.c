#include <stdio.h>
int main() {
  unsigned char c; 
  unsigned char *p=&c;
  int j = (c-c);    // is this an unspecified value?
  _Bool b = (j==j); // can this be false?
  printf("b=%s\n",b?"true":"false"); 
}
