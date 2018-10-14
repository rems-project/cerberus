#include <string.h> 
int x=1, y=2;
int main() {
  int *p = &x;
  int *q = &y;
  p = p + 1;
  if (memcmp(&p, &q, sizeof(p)) == 0) {
    *p = 11;  // undefined behaviour?
  }
  return 0;
}
