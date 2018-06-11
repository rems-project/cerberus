#include "cerberus.h"
typedef struct SEntry
{
  unsigned char num;
} TEntry;

typedef struct STable
{
  TEntry data[2];
} TTable;

TTable *
init (void)
{
  return malloc(sizeof(TTable));
}

void
expect_func (int a, unsigned char *b) ;

static void
inlined_wrong (TEntry *entry_p, int flag);

static void
inlined_wrong (TEntry *entry_p, int flag)
{
  unsigned char index;
  entry_p->num = 0;

  if (flag == 0)
    abort();

  for (index = 0; index < 1; index++)
    entry_p->num++;

  if (!entry_p->num)
    {
      abort();
    }
}

void
expect_func (int a, unsigned char *b)
{
  if (abs ((a == 0)))
    abort ();
  if (abs ((b == 0)))
    abort ();
}

int 
main (void)
{
  unsigned char index = 0;
  TTable *table_p = init();
  TEntry work;

  inlined_wrong (&(table_p->data[1]), 1);
  expect_func (1, &index);
  inlined_wrong (&work, 1);

  free (table_p);

  return 0;
}

