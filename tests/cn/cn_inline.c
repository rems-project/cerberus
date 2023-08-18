

enum size {
  big,
  medium,
  small,
};

static inline int
lookup_size_shift (enum size sz)
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

int
f (void)
/*@ ensures return < power(10, 6) @*/
{
  int x;
  /*@ inline; @*/
  x = 1 << lookup_size_shift(medium);
  /*@ inline; @*/
  x += 1 << lookup_size_shift(small);
  return x;
}

