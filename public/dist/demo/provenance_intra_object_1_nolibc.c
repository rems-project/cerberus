typedef struct { int x; int y; } st;
int main() {
  st s = { .x=1, .y=2 };
  int *p = &s.x + 1;
  int *q = &s.y;
  *p = 11;  // is this free of undefined behaviour?
}
