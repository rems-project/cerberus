struct T1 {
  int x;
};

struct T2 {
  int x;
};

struct {
  int x;
} s;

int main(void) {
  s.x = 0;
  return 0;
}
