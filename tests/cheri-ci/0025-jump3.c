// Jump up into an outer block
int main(void) {
  int x = 0;
 l: // [x]
  {
    int y = 3;
    goto l; // [x, y]
  }
  return 0;
}
