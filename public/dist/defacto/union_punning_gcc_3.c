// adapted from GCC docs
#include <stdio.h>
union a_union {
  int i;
  double d;
};
int main() {
  double d = 3.1415;
  int j = ((union a_union * ) &d)->i;
  printf("j=%d\n",j);
}

