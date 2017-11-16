// adapted from GCC docs
#include <stdio.h>
union a_union {
  int i;
  double d;
};
int main() {
  union a_union t;
  t.d = 3.1415;
  int j = t.i; // is this defined behaviour?
  printf("j=%d\n",j);
}

