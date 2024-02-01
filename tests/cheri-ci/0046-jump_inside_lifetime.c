// the object x get allocated, but is NOT initialized
int main(void) {
  goto l;
  int x = 10;
 l:
  return x;
}
