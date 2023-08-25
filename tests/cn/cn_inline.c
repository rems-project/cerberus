

enum size {
  big,
  medium,
  small,
};

/*@ function (integer) lookup_size_shift (integer sz) @*/

static inline int
lookup_size_shift (enum size sz)
/*@ cn_function lookup_size_shift @*/
/*@ ensures return == lookup_size_shift(sz) @*/
{
  switch (sz) {
    case big:
      return 12;
    case medium:
      return 8;
    case small:
      return 2;
    default:
      /* shouldn't happen */
      return 0;
  }
}

/* The original plan was to inline the above into the below, but when possible
   it is much simpler to use its functional representation, as done here. */

int
f (void)
/*@ ensures return < power(10, 6) @*/
{
  int x;
  x = 1 << lookup_size_shift(medium);
  x += 1 << lookup_size_shift(small);
  return x;
}

