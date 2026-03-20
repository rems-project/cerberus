/* Negative test: a binding with a pure but non-sym RHS (a literal value)
   must not be eliminated by copy_prop. */
int main(void) {
    int x = 42;
    return x;
}
