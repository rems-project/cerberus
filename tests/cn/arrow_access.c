struct s {
  int x;
  int y;
};

void arrow_access_1() 
{
  struct s origin = { .x = 0, .y = 0 };
  /*@ assert (origin.x == 0i32); @*/ // -- member
  struct s *p = &origin;
  struct s *q = &origin;

  /*@ assert (p->x == 0i32); @*/   // Arrow access 
  /*@ assert ((*p).x == 0i32); @*/ // ... desugared as this 
  (*p).y = 7; 
  /*@ assert (q->y == 7i32); @*/
}

void arrow_access_2 (struct s *origin) 
/*@ 
requires 
  take Or = Owned<struct s>(origin); 
  origin->y == 0i32; 
ensures 
  take Or_ = Owned<struct s>(origin); 
  origin->y == 7i32; 
  (*origin).y == 7i32; 
@*/
{
  origin->y = 7; 
}