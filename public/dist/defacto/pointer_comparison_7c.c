#include <stdio.h>
#include <stdlib.h>
int main() {
  int *pj;
  {
    int j=1;
    pj = &j;
    printf("pj=%p  &pj=%p\n",(void*)pj,(void*)&pj); 
  }
  int *pk;
  {
    int k=2;
    pk = &k;
    //printf("pk=%p  \n",(void*)pk);
    printf("pk=%p  &pk=%p\n",(void*)pk,(void*)&pk);
    *pj=3;
    printf("k=%i\n",k);
  }
  printf("pj=%p  &pj=%p\n",(void*)pj,(void*)&pj);
  return 0;
}
