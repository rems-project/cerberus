int main(void) {
  int x = 1;
  assert (x == 1);
  int y = 5;
  assert (y == 5);
  
  if (x == 1) {
    assert (x == 1);
    y = x;
    assert (y == 1);
    x = 2;
    assert (x == 2);
  } else {
    assert (1 == 2);
    x = 4;
  }
  assert (y == 1);
  assert (x == 2);
}
