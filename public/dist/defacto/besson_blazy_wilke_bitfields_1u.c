#include <stdio.h>
struct f {
  unsigned int a0 : 1; unsigned int a1 : 1;
} bf ;
int main() {
  unsigned int a;
  bf.a1 = 1; 
  a = bf.a1; 
  printf("a=%u\n",a);
}
