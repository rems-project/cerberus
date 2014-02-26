#include "stdio.h"

int main(void) {
  long a = 0L;
  char *p = (char *) &a;
  for (; p <= (char *) &a + (sizeof a); p++)
    printf ("%d\n", *p);
  return 0;
}
