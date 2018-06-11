#include "cerberus.h"
int v;

char *
g (void)
{
  return "";
}

char *
f (void)
{
  return (v == 0 ? g () : "abc");
}

int 
main (void)
{
  v = 1;
  if (!strcmp (f (), "abc"))
    exit (0);
  abort();
}
