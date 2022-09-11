struct T1 { int x; int y; };
struct T2 { struct T1 *a; };
struct T3 { struct T1 *u; struct T2 * v; };

struct T3 glob = {
  &(struct T1) { 1000, 200 },
  &(struct T2) { &(struct T1) { 30, 4 } }
};

int main(void)
{
  return glob.u->x + glob.u->y + glob.v->a->x + glob.v->a->y;
}
