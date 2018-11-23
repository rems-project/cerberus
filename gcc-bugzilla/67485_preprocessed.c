

typedef long int int64_t;
int64_t
to_int ()
{
 int64_t sign;
 return sign * ((int64_t) (~ (int64_t) 0 - ((int64_t) ((! ((int64_t) 0 < (int64_t) -1)) ? ~ (int64_t) 0 << (sizeof (int64_t) * 8 - 1) : (int64_t) 0))));
}

int main() {
  return to_int();
}
