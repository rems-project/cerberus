/* The goto resumes a label whose save is inside a Core case arm.
 * Both visits increment n; execution must return 2.
 */
int main(void)
{
    int n = 0;
    switch (n) {
    case 0:
    label:
        n++;
        break;
    }
    if (n < 2)
        goto label;
    return n;
}
