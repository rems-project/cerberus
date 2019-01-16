int main(void) {
  int x = 1;
  if (x) {
    return 1;
  } else {
    5/0;
  }
  1/0;
  return 2;
}
