int fn(int *p) { return *p; }
int main() {
    int x = 0;
    do { fn(&x); } while (0);
    return x;
}
