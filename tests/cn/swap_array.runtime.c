void swap_array (int *p, int n, int i, int j)
/* --BEGIN-- */
/*@ requires take a1 = each(i32 k; 0i32 <= k && k < n) { Owned<int>(array_shift<int>(p,k)) };
             0i32 <= i && i < n;
             0i32 <= j && j < n;
             j != i;
    ensures take a2 = each(i32 k; 0i32 <= k && k < n) { Owned<int>(array_shift<int>(p,k)) };
            a2 == a1[i: a1[j], j: a1[i]];
@*/
/* --END-- */
{
/* --BEGIN-- */
  /*@ extract Owned<int>, i; @*/
/* --END-- */
  int tmp = p[i];
/* --BEGIN-- */
  /*@ extract Owned<int>, j; @*/
/* --END-- */
  p[i] = p[j];
  p[j] = tmp;
}

int main()
/*@ trusted; @*/
{
    int a[3] = { 0, 1, 2 };

    swap_array(a, 3, 0, 2);
    int *first = a;
    int *third = a + 2;
    /*@ assert (*third == 0i32); @*/
    /*@ assert (*first == 2i32); @*/

    // uncomment for failure
    // swap_array(a, 3, 1, 1);
}
