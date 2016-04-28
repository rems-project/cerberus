// Jump up into an inner block
int main(void) {
  int x;
  {
    int y = 3;
  l: // [x, y]
    x = y;
  }
  int z = 4;
  goto l; // [x, z]
  
  return 0;
}
