#include "cerberus.h"
typedef enum foo E;
enum foo { e0, e1 };

struct {
  E eval;
} s;

int 
p (void)
{
  abort();
}

int 
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
