/* Tests that a local variable initialised via a compound literal is
   promotable.  The Core IR for (int){ 42 } contains:
       Ewseq(_, Store0(Paction Pos, ptr_tmp, 42), Load0(ptr_tmp))
   This tests the "strong write in weak sequence" test case. */
int main(void) {
    int x = (int){ 42 };
    return x;
}
