typedef struct {char c; int i; } st;
void f(char* cp) {
  *cp='B';
}
int main() {
  st s = { .c='A', .i=1 };
  f(&s.c);
}
