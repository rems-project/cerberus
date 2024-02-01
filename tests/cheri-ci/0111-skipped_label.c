int main(void)
{
  goto p;
 l:
  return 0;
 p:
  if (0) {

  } else {
    if (1)
      goto l;
  }
}
