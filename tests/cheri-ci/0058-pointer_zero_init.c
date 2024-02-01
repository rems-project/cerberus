#include <stdlib.h> // NULL

//int *glob1;
int glob1;
int *glob2 = &glob1;
int *glob3 = NULL;

int main(void)
{
  glob1; glob2; glob3;
  //  int *p = 0;
}
