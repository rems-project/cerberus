#include "cerberus.h"
/* From PR target/16176 */
struct  s { struct s *next; };

struct s * 
maybe_next (struct s *s, int t)
{
  if (t)
    s = s->next;
  return s;
}

int 
main (void)
{
  struct s s1, s2;

  s1.next = &s2;
  if (maybe_next (&s1, 1) != &s2)
    abort ();
  exit (0);
}
