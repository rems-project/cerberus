// declare glob1 as {const} pointer to {} int
int * const glob1;
// declare glob2 as {} pointer to {const} int
int const * glob2;

// declare foo as function (void) returning {const} pointer to {} int
int * const foo(void)
{
//  return glob1;
}

// declare bar as function (void) returning {} pointer to {const} int
int const * bar(void)
{
//  return glob2;
}

void baz(int * const p, int const * q) {
/*
  int * const r = 0;
  int const * s = 0;
  
  *p = 0;
  q = 0;
  *r = 0;
  s = 0;
  
  *glob1 = 0;
  glob2 = 0;
  
*/
  *foo() = 0;

  // All of these should typecheck
}
