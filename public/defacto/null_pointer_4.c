#include <stdio.h>
int main() {
  int x;
  // is this guaranteed to trap (rather than be
  // undefined behaviour)?
  x = *(int*)NULL;
  printf("x=%i\n",x);
}
