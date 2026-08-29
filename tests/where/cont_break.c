int main() {
    int x = 10;

    while (1) {
        if (x < 0) {
            break;
        } else if (x % 2 == 0) {
            --x;
            continue;
        }
        --x;
    }
}
