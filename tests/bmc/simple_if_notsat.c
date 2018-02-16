int main(void) {
  int x = 1;
  if (x == 1) {
    x = x+1;
  } else {
    x = 3;
  }
  assert (x == 2);
}
