#include <stdio.h>
int main() {
  FILE  * f = fopen("foo.txt", "w+");
  if (!f) return 1;
  putc('h', f);
  rewind(f);
  char c = getc(f);
  assert(c == 'h');
  return 0;
}
