// Jump down into an outer block
int main(void) {
  int x = 0;
  {
    int y = 3;
    goto l; // [x, y, x]
  }
  int z = 4;
 l: // [x, z]
  return 0;
}
