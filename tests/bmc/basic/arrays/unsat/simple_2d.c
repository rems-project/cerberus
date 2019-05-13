
int x[2][2] = {{1,2},{3,4}};

int main() {
  assert(x[0][0] == 1);
  assert(x[0][1] == 2);
  assert(x[1][0] == 3);
  assert(x[1][1] == 4);
  x[0][0] = 0;
  assert(x[0][0] == 0);
}
