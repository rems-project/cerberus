int main(void) {
  int x = 0;
  if (x) {
    return 1;
  } else {
    return 2;
  }
  1/0;
  return 1;
}
