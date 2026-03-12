int sink(int *p) { return *p; }
int main(void) {
    int promotable = 11;   /* no address taken */
    int escaped = 22;      /* address passed to sink */
    return promotable + sink(&escaped);
}
