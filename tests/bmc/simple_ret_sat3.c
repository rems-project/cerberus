int main(void) {
  int x = 0;
  if (x) {
    return 1;
  } else {
    1/0;
  }
  return 1;
}
