int main(void) {
  int x = 1;
  int *p = &x; 
  x = 2;
  int y = *p;
  assert ( x != y);
}
