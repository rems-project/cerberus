#include "cerberus.h"
struct fd
{
	unsigned char a;
	unsigned char b;
} f = { 5 };

struct fd *
g (void) { return &f; }
int 
h (void) { return -1; }

int 
main (void)
{
	struct fd *f = g();
	f->b = h();
	if (((f->a & 0x7f) & ~0x10) <= 2)
		abort ();
	exit (0);
}
