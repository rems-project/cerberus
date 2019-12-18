// #include<stdlib.h>

int main(void) {
  int *p = 0; // NULL;
  { int x = 0; p = &x; };
  *p; // undefined
  return 0;
}
