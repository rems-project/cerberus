/* Tests that a simple local variable load through a pure(sym) alias
   is eliminated by the copy_prop pass. */
int main(void) {
    int x = 42;
    return x;
}
