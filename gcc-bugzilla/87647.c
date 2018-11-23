struct a { char c; };
struct a *const b = &(struct a){'c'};
int main() {
  struct {
    char *s;
    struct a *t;
  } a[] = {"", b,  "", b,  "", b,  "", b,  "", b,  "", b,  "", b,  "", b,  "",
           b,  "", b,  "", b,  "", b,  "", b,  "", b,  "", b,  "", b,  "", b};
}
