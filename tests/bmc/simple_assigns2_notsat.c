int main(void) {
  int x = 1;
  assert (x == 1);
  int y = 5;
  assert (y == 5);
  
  if (x != 1) {
    y = 10;
    assert (1 == 2);
  } else {
    int z = 6;
    y = x;
    x = z;
  }
  assert (y == 1);
  assert (x == 6);
}
