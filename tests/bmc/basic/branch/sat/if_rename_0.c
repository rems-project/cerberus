int main(void) {
  int x = 1;
  if (x) {
    int z = 1;
    x = z+1;
  } else {
    int z = 2;
    x = z + 1;
  }
  assert (x == 3);
}
