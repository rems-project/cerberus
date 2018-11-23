#include <string.h>
#include <stdio.h>
unsigned i = 0;

int main (void)
{
  {
    char d [3];
    memcpy (d + i, "abcdef", 5);
    printf ("%.0s", d);
  }
}
