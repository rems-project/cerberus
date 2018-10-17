#include <stdio.h>
int main() {
  int a[2][2] = {{0,0},{0,0}};
  a[0][2] = 1;   // undefined behaviour?
  int x = a[1][0];
  printf("x=%d\n",x);
}
  
