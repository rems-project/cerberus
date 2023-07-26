

int
f (unsigned int x) {
  unsigned int y;

  y = __builtin_ctz(x);

  if (y < 10) {
    return 1;
  }
  else {
    return 3;
  }
}

