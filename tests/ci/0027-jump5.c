int main(void) {
  int x = 0;
  {
    int y = 3;
  l: // [x, y]
    x = y;
    
    if (x > 0)
      goto l2;
  }
  int z = 4;
  goto l; // [x, z]
  
 l2:
  return x;
}
