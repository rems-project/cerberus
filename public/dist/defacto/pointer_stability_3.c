#include <stdio.h>
#include <string.h>
#include <inttypes.h>
int main() {
  int x=1;
  int *p = &x;
  int *q = &x;
  // is this guaranteed to be true?
  _Bool b = (0==memcmp(&p,&q,sizeof(p)));
  printf("(p==q)=%s\n",b?"true":"false");
  return 0;
}
