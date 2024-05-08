void check_cn_max_min_consts()
{
    /*@ assert(255u8 == MAXu8()); @*/
    /*@ assert(127i8 == MAXi8()); @*/

    /*@ assert(0u8 == MINu8()); @*/
    /*@ assert((0i8 - 127i8 - 1i8) == MINi8()); @*/

    /*@ assert(65535u16 == MAXu16()); @*/
    /*@ assert(32767i16 == MAXi16()); @*/

    /*@ assert(0u16 == MINu16()); @*/
    /*@ assert((0i16 - 32767i16 - 1i16) == MINi16()); @*/

    /*@ assert(4294967295u32 == MAXu32()); @*/
    /*@ assert(2147483647i32 == MAXi32()); @*/

    /*@ assert(0u32 == MINu32()); @*/
    /*@ assert((0i32 - 2147483647i32 - 1i32) == MINi32()); @*/

    /*@ assert(18446744073709551615u64 == MAXu64()); @*/
    /*@ assert(9223372036854775807i64 == MAXi64()); @*/

    /*@ assert(0u64 == MINu64()); @*/
    /*@ assert((0i64 - 9223372036854775807i64 - 1i64) == MINi64()); @*/
}

