int main(void) {
  unsigned int indet;
  unsigned int x = indet;
  assert ((x + !x) == x?x:1);
}
