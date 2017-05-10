int const **glob1;  // declare glob1 as pointer to pointer to {const} int
int * const *glob2; // declare glob2 as pointer to {const} pointer to int
int ** const glob3; // declare glob3 as {const} pointer to pointer to int

int main(void)
{
  // All of these should typecheck
  *glob1 = 0; glob1 = 0;
  **glob2 = 0; glob2 = 0;
  **glob3 = 0; *glob3 = 0;
  
  int const **p;
  int * const *q;
  int ** const r;
  *p = 0; p = 0;
  **q = 0; q = 0;
  **r = 0; *r = 0;
}
