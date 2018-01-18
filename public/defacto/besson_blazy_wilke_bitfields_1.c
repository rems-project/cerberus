#include <stdio.h>
struct f {
  int a0 : 1; int a1 : 1;
} bf ;
int main() {
  int a;
  bf.a1 = 1; 
  a = bf.a1;  // is this a well-defined value?
  printf("a=%i\n",a);
}
