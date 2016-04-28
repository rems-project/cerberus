// Jump down into an inner block
int main(void) {
  int x;
  goto l;
  {
    int y = 3;
  l:
    x = y;
  }
  
  return 0;
}
