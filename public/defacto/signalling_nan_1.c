#include <stdio.h>

// if long double is implemented here with 80-bit Intel Extended Precision, which is unclear right now, then this:
//https://en.wikipedia.org/wiki/Extended_precision#x86_Extended_Precision_Format
// suggests the following is a signalling NaN representation.
unsigned char snan[10] =  {0xFF, 0xFF, 0b10111111, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF};
// but the code doesn't signal. 

union a_union {
  long double ld;
  unsigned char cs[10];
};

int main() {
  printf("sizeof(long double)=%ld\n",sizeof(long double));
  union a_union u;
  int i;
  for (i=0; i < 10; i++) 
    u.cs[i] = snan[9-i];
  for (i=0; i < 10; i++) 
    printf("0x%x ",u.cs[9-i]);
  printf("\n");
  long double ld = u.ld; // is this defined behaviour?
  ld = ld + 1.0;         // is this defined behaviour?
  printf("ld=%Lf\n",ld);
}


//0x7F, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01
