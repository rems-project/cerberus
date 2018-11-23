int ww, vv;
int x(int y)
{
  int z = y / 16;
  int w = z / 3;
  int v = z % 3;
  ww = w;
  return v;
}

int main() {
  return x(42);
}
