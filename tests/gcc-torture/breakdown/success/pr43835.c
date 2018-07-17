#include "cerberus.h"
struct PMC {
    unsigned flags;
};

typedef struct Pcc_cell
{
    struct PMC *p;
    long bla;
    long type;
} Pcc_cell;

extern void Parrot_gc_mark_PMC_alive_fun(int * interp, struct PMC *pmc)
     ;

void Parrot_gc_mark_PMC_alive_fun (int * interp, struct PMC *pmc)
{
  abort ();
}

static void mark_cell(int * interp, Pcc_cell *c)
        
        
        ;

static void
mark_cell(int * interp, Pcc_cell *c)
{
            if (c->type == 4 && c->p
		&& !(c->p->flags & (1<<18)))
	      Parrot_gc_mark_PMC_alive_fun(interp, c->p);
}

void foo(int * interp, Pcc_cell *c);

void
foo(int * interp, Pcc_cell *c)
{
  mark_cell(interp, c);
}

int 
main (void)
{
  int i;
  Pcc_cell c;
  c.p = 0;
  c.bla = 42;
  c.type = 4;
  foo (&i, &c);
  return 0;
}
