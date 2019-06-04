#define INTTYPE_SIGNED(t) (! ((t) 0 < (t) -1))
#define INTTYPE_MINIMUM(t) ((t) (INTTYPE_SIGNED (t) \
                             ? ~ (t) 0 << (sizeof (t) * 8 - 1) : (t) 0))
#define INTTYPE_MAXIMUM(t) ((t) (~ (t) 0 - INTTYPE_MINIMUM (t)))
typedef long int int64_t;
int64_t
to_int ()
{
 int64_t sign;
 return sign * INTTYPE_MAXIMUM (int64_t);
}

int main() {
  return to_int();
}
