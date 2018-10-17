#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>
int main() {
  int x=1;  
  int *p = &x;
  uintptr_t i = (uintptr_t) p;
  FILE *f = fopen("provenance_via_io_auto.tmp","w+b");
  printf("Addresses: i=%"PRIuPTR"\n",i);
  // print pointer address to a file
  fprintf(f,"%"PRIuPTR"\n",i);
  rewind(f);
  uintptr_t k;
  // read a pointer address from the file
  int n = fscanf(f,"%"SCNuPTR"\n",&k);
  if (n != 1) exit(EXIT_FAILURE);
  printf("Addresses: k=%"PRIuPTR"\n",k);
  int *r = (int *)k;
  // are r and p now equivalent?  
  *r=12; // is this free of undefined behaviour?                                                           
  _Bool b1 = (r==p); // do they compare equal?                      
  _Bool b2 = (0==memcmp(&r,&p,sizeof(r)));//same reps?
  printf("x=%i *r=%i b1=%s b2=%s\n",x,*r,
         b1?"true":"false",b2?"true":"false");
}
