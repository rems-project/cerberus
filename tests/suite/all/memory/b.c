int main(void)
{
//  int ret = 0;
  int x, y;
  int z = &x+1 == &y?100:200;
  return ((&x+1 == &y?10:20) + z);
}
