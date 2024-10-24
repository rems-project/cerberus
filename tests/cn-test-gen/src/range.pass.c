int range(int* arr, int len)
/*@ trusted;
    requires
        take A = each (u64 i; 0u64 <= i && i < (u64)len) {
            Owned(array_shift<int>(arr, i))
        };
        each (u64 i; 0u64 <= i && i < (u64)len) {
            A[i] == (i32)i
        };
    ensures
        take A2 = each (u64 i; 0u64 <= i && i < (u64)len) {
            Owned(array_shift<int>(arr, i))
        };
        A == A2;
        return == 1i32;
@*/
{
    int i = 0;
    while (i < len) {
        if (arr[i] != i) {
            return 0;
        }

        i++;
    }

    return 1;
}