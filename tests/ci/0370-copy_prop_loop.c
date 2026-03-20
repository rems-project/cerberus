/* Tests copy_prop with a loop. Aliases before and inside the loop
   should be eliminated where safe. */
int main(void) {
    int sum = 0;
    int i;
    for (i = 0; i < 5; i++) {
        sum = sum + i;
    }
    return sum;
}
