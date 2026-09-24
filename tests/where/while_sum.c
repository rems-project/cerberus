int f(int i, int limit) {
  int sum = 0;
  while (i < limit) {
    sum = sum + i;
    i = i + 1;
  }
  return sum;
}
