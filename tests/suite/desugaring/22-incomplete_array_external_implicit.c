// EXAMPLE 2 (§6.9.2#5)
int i[]; // this should have type int[1]

int main(void)
{
  return i[0]; // EXPECTED: 0
}
