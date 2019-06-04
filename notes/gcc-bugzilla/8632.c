static void a1(void *p) { }

int main(int argc, char **argv) {
    int i;
    a1(&i);
    return 0;
}
