#include "stdio.h"

int main(void) {
  int size = sizeof (unsigned int);
  int align = __alignof__ (unsigned int);
  printf ("size of unsigned int: %d\n", size);
  printf ("alignment of unsigned int : %d\n", align);
  unsigned long a = 0L;
  unsigned int *p = (unsigned int *) &a;
  for (; p < ((unsigned int *) &a) + (sizeof a); p++)
    printf ("%d\n", *p);
  return 0;
}
