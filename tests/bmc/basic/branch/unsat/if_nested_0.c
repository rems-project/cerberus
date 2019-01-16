int main(void) {
  int x = 1;
  if (x == 1) {
    int y = 2;
    x = y + 1;
    if (x == 3) {
      x = 4;
    } else {
      assert (0);
    }
  } else {
    assert (0);
  }
  assert (x == 4);

}
