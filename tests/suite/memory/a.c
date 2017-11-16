#include<stdio.h>

int main(void)
{
  int b[2], a;
  int *p = (int *)b, *q = &b[0], *r = &b[1];
  
  if (p==q) { // Should always be TRUE.
    printf("p == q\n");
  };
  if (q==r) {// Should always be FALSE.
    printf("q == r\n");
  };
  if (p==r) {// Should always be FALSE.
    printf("p == r\n");
  };
  
  if (&a+1 == (int*)&b) { // Can be either TRUE or FALSE.
    printf("&a+1 == &b\n");
  };
  if (&a+1 == (int*)&b) { // Should always have the same result has the previous.
    printf("&a+1 == &b\n");
  };
}
