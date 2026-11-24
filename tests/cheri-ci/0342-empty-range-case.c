int main(void)
{
  int x = 1, r = 0;
  switch (x) {
    case 1:       r += 1;
    case 5 ... 3: r += 10; /* this is executed */
    case 2:       r += 100;
  }
  return r;
}
