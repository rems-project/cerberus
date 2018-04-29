#include <stdio.h>
int main() {
  int x=3;
  *((int *) (float *)&x) = 4;
  printf("x=%i\n",x);
}
