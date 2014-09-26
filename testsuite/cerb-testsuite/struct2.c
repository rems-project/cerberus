struct T1 {
  int x, y;
  int z;
};


int main(void) {
  struct T1 {int x; } s;
  return s.x;
}
