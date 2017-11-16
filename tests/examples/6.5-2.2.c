/* UB: 6.5#2 */
int main()
{
  int i = 0;
  int a[10];
  a[i++] = i;
  return i;
}

