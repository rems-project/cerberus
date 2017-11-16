#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>
int x=1;
int main() {
  int *p = &x;
  FILE *f = fopen(
    "provenance_via_io_percentp_global.tmp","w+b");
  printf("Addresses: p=%p\n",(void*)p);
  // print pointer address to a file
  fprintf(f,"%p\n",(void*)p);
  rewind(f);
  void *rv;
  int n = fscanf(f,"%p\n",&rv);
  int *r = (int *)rv;
  if (n != 1) exit(EXIT_FAILURE);
  printf("Addresses: r=%p\n",(void*)r);
  // are r and p now equivalent?  
  *r=12; // is this free of undefined behaviour?                                                           
  _Bool b1 = (r==p); // do they compare equal?                      
  _Bool b2 = (0==memcmp(&r,&p,sizeof(r)));//same reps?
  printf("x=%i *r=%i b1=%s b2=%s\n",x,*r,
         b1?"true":"false",b2?"true":"false");
}
