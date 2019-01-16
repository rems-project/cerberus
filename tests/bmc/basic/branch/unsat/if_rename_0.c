int main(void) {
  int x = 1;
  if (1) {
    int z = 1;
    assert (z == 1);
    x = z + 1;
  } else {
    int z = 2;
    assert (z == 2);
  }
  assert ( x == 2);
}
