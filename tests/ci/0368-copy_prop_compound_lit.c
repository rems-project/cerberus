/* Tests the extended case: a compound literal produces an effectful RHS
   ending in pure(ptr_sym). The binding is kept (for the store side effect)
   but the alias is replaced with the canonical pointer. */
int main(void) {
    int x = (int){ 42 };
    return x;
}
