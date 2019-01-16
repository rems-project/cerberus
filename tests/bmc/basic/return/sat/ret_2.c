int main(void) {
  int x = 0;
  if (x) {
    return 2;
  } else {
    1/0;
  }
  return 3;
}
