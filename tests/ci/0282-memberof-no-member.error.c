struct s  { int x; } a;
struct s bar () { return a; }
void foo() {
  (bar()).y;
}
