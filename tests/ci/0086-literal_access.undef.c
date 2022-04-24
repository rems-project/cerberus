int main(void)
{
  char arr[] = "modifiable";
  char *p = "not modifiable";
  
  arr[0] = 'M'; // OK
  p[0] = 'N'; // Undefined behaviour (§#6.4.5#7), see also comment in §6.7.9#32)
}
