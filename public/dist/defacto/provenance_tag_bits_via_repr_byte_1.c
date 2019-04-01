#include <assert.h>
#include <stdio.h>
#include <stdint.h>
int x=1;
int main() {
  int *p=&x, *q=&x;
  // read low-order (little endian) representation byte of p 
  unsigned char i = *(unsigned char*)&p;
  // check the bottom two bits of an int* are not used
  assert(_Alignof(int) >= 4);
  assert((i & 3u) == 0u);
  // set the low-order bit of the byte
  i = i | 1u;  
  // write the representation byte back
  *(unsigned char*)&p = i; 
  // [p might be passed around or copied here]
  // clear the low-order bits again
  *(unsigned char*)&p = (*(unsigned char*)&p) & ~((unsigned char)3u);
  // are p and q now equivalent?  
  *p = 11;          // does this have defined behaviour? 
  _Bool b = (p==q); // is this true?
  printf("x=%i *p=%i (p==q)=%s\n",x,*p,b?"true":"false");  
}
