
int global_x;
void *global_void_ptr;

extern int extern_f (void);

int
g (int x)
{
  return 0;
}

/*@
function ({u32 x1, u32 x2}) get_globals ()
  { {x1: (u32) (&g), x2: (u32) (&extern_f)} }
@*/

int
f (int x)
/*@ accesses global_x; @*/
{
  /* resolution of the 'g' & 'extern_f' addrs triggered a bug at one point */
  /*@ assert (((u32) (&x)) == ((u32) (&x))); @*/;
  /*@ assert (((u32) (&global_x)) == ((u32) (&global_x))); @*/;
  /*@ assert (get_globals () == get_globals ()); @*/;
  /*@ assert (((u32) (&g)) == ((u32) (&g))); @*/;

  return x == global_x;
}
