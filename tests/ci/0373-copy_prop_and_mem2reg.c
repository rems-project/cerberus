/* Integration test: copy_prop before mem2reg makes the compound literal
   pointer directly visible to mem2reg's check_definitely_init analysis,
   allowing it to promote the variable. */
int main(void) {
    int x = (int){ 42 };
    return x;
}
