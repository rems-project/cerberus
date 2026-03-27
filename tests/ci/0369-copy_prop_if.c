/* Tests copy_prop with an alias used in both branches of an if. */
int main(void) {
    int x = 1;
    int y = 2;
    int z;
    if (x) {
        z = x;
    } else {
        z = y;
    }
    return z;
}
