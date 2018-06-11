#include "cerberus.h"
static unsigned int expr_hash_table_size = 1;

int 
main (void)
{
  int del = 1;
  unsigned int i = 0;

  if (i < expr_hash_table_size && del)
    exit (0);
  abort ();
}
