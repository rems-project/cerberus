#include "cerberus.h"
enum foo { e0, e1 };
typedef enum foo E;

struct {
  E eval;
} s;

int 
p (void)
{
  abort();
}

void
f (void)
{
  switch (s.eval)
    {
    case e0:
      p();
    }
}

int 
main (void)
{
  s.eval = e1;
  f();
  exit(0);
}
