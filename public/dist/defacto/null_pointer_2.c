#include <stdio.h> 
#include <stddef.h> 
#include <string.h>
#include <assert.h> 
int y=0;
int main() {
  assert(sizeof(int*)==sizeof(char*));
  int *p = NULL;
  char *q = NULL;
  // are two null pointers guaranteed to have the
  //  same representation?
  _Bool b = (memcmp(&p, &q, sizeof(p))==0);
  printf("p=%p q=%p\n",(void*)p,(void*)q);
  printf("%s\n",b?"equal":"unequal");
}
