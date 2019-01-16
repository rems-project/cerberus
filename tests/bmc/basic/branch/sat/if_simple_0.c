int main(void) {
  int x = 1;
  if (x == 1) {
    int z = 10;
    x = z + 1;
  }
  assert ( x == 1);
}
