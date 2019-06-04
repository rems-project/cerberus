extern void abort (void);
static void bar ();

int
main (void)
{
  bar (1);
  return 0;
}

static void
bar (double i)
{
  if (i)
    abort ();
}
