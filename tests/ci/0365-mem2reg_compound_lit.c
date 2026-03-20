/* Tests that a local variable initialised via a compound literal is
   promotable.  The Core IR for (int){ 42 } contains:
       Ewseq(_, Store0(Paction Pos, ptr_tmp, 42), Load0(ptr_tmp))
   Under the old bool-based analysis, Load0 in the Ewseq e2 saw
   `already_init = false` (init in e1 was not forwarded) -> NOT promotable.
   Under the new Write_kind analysis, Strong from e1 propagates to e2 -> IS
   promotable.  This is the "strong write in weak sequence" test case. */
int main(void) {
    int x = (int){ 42 };
    return x;
}
