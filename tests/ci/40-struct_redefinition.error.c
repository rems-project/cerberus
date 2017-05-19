struct T;

struct T {
  int x;
};

// error: redeclaration of T
struct T {
  int x;
};

int main(void) {
  return 0;
}
