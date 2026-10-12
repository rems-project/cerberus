/* This is the only test in this directory whose observable behaviour differs
   under the strict_reads switch: the read of the uninitialised x is UB011
   (use of an indeterminate value) under strict_reads, and an unspecified
   value otherwise. Every other test here is either UB under both, or fine
   under both. */
int main() {
    int x;
    return x;
}
