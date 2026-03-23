/* Tests tuple copy_prop: in an Eunseq, pure constant arms are propagated
   into the continuation, eliminating the binding from the tuple pattern. */
int main() {
    int x = 42;
    return x == 42 ? 0 : 1;
}
