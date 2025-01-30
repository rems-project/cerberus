typedef struct a {
    int b;
    int c;
} a;
_Static_assert(offsetof(a, c) == sizeof(int), "no gap");
