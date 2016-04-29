int x;

int f(void) {
  return x;
}


int main(void) {
  int x = 20;
  return f(); // returns: 10
}

int x = 10;
