/* Negative test: an effectful RHS with tail_sym = None (the RHS ends in
   an action result, not pure(sym)) must not be touched by copy_prop. */
int g = 0;
int main(void) {
    int x = 10;
    g = x;
    return g;
}
