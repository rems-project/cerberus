#include <stdlib.h>
int main() { 
  void *p = malloc(sizeof(int));
  _Bool b = (p == (void*)-1); // defined behaviour?
}
