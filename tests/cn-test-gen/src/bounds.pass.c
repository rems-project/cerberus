void bounds1(int size, int* p)
/*@
requires
  take a1 = each(u64 i; 0u64 <= i && i < (u64)size) { Owned<int>(array_shift<int>(p,i)) };
ensures
  take a2 = each(u64 i; 0u64 <= i && i < (u64)size) { Owned<int>(array_shift<int>(p,i)) };
@*/
{}

void bounds2(int size, int* p)
/*@
requires
  take a1 = each(u64 i; i < (u64)size) { Owned<int>(array_shift<int>(p,i)) };
ensures
  take a2 = each(u64 i; i < (u64)size) { Owned<int>(array_shift<int>(p,i)) };
@*/
{}

void bounds3(int size, int* p)
/*@
requires
  take a1 = each(i32 i; -1i32 < i && i < size) { Owned<int>(array_shift<int>(p,i)) };
ensures
  take a2 = each(i32 i; -1i32 < i && i < size) { Owned<int>(array_shift<int>(p,i)) };
@*/
{}

void bounds4(int* p)
/*@
requires
  take a1 = each(i32 i; i == 1i32 || i == 2i32 || i == 5i32) { Owned<int>(array_shift<int>(p,i)) };
ensures
  take a2 = each(i32 i; i == 1i32 || i == 2i32 || i == 5i32) { Owned<int>(array_shift<int>(p,i)) };
@*/
{}
