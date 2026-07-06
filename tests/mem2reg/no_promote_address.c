int foo(int *p) { return *p; }
int main(void) {
    int x = 55;
    return foo(&x);
}
