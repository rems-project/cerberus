int a, b, c[1][25];

void f ()
{ 
  for (a = 0; a < 5; a++)
    for (b = 0; b < 5; b++)
      c[3970000000000000000][a * 5 + b] = 1;
}

int main() {
  f();
}
