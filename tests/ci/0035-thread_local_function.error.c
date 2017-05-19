// OK
extern int f1() {
  return 0;
}

// OK
static int f2() {
  return 0;
}

// Error
_Thread_local int f3() {
  return 0;
}

int main() {
}
