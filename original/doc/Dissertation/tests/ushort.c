#include <stdio.h>

int main(void) {
  unsigned short s = 0;
  unsigned short t = s;
  while(t <= s) {
    printf("%d, %d\n", s, (s % 1));
    t = s;
    s++;
  }
  return 0;
}
