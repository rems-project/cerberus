int main() {
  int x = 2;
  int y = 0;
  y = (x == (x=3));
  assert (y == 0);
  return 0;
}
