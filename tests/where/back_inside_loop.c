int main() {
    int x = 3;
    int y = 2;

    while (x > 0) {
        x--;
l:
        x;
    }

    int z = 1;

    if (z < y) {
        y = 0;
        x = -1;
        goto l;
    }

    return 0;
}
