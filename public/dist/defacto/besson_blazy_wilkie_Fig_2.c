#include <inttypes.h>
#include <stdlib.h>
char hash(void *ptr);
// The besson et al. example doesn't include a concrete definition
// of a hash function; here we use a very crude one
char hash(void *ptr) {
  char h=0;
  unsigned int i;
  for (i=0;i<sizeof(ptr);i++) 
    h = h ^ *((char *)ptr+i);
  return h; }
int main(){
  int *p = (int *) malloc(sizeof(int));
  *p = 0;
  int *q = (int *) ((uintptr_t) p | (hash(p) & 0xF));
  int *r = (int *) (((uintptr_t) q >> 4) << 4);
  return *r; }
