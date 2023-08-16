

int
f (unsigned int x) {
  unsigned int y;

  y = __builtin_ctz(x);
  y = __builtin_ffs(x);

  if (y < 10) {
    return 1;
  }
  else {
    return 3;
  }
}

