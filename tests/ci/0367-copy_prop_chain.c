/* Tests that chained pure(sym) aliases are eliminated in a single pass.
   let a = pure(x) in let b = pure(a) in use b --> use x */
int main(void) {
    int x = 42;
    int y = x;
    return y;
}
