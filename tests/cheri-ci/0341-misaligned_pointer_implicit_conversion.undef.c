#include <stdlib.h>

void func(void *p0)
{
    int **p1 = p0; // undef
}

int main(void)
{
  char *p = malloc(sizeof(int*)+1);
  void *p0 = (void*)(p+1);

  func(p0);
}