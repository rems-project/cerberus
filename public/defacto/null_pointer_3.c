#include <stdio.h> 
#include <stddef.h> 
#include <string.h>
#include <stdlib.h>
int y=0;
int main() {
  int *p = NULL;
  int **q = (int **) calloc(1,sizeof(int*));
  // is this guaranteed to be true?
  _Bool b = (memcmp(&p, q, sizeof(p))==0);
  printf("%s\n",b?"zero":"nonzero");
}
