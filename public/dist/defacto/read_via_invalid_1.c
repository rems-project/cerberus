#include <stdio.h>
int main() {
  int x;
  // is this free of undefined behaviour?
  x = *(int*)0x654321;
  printf("x=%i\n",x);
}
