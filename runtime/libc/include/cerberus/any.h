#include <limits.h>

// builtins
char __any_bounded_char (char, char);
short __any_bounded_short (short, short);
int __any_bounded_int (int, int);
long __any_bounded_long (long, long);
long long __any_bounded_long_long (long long, long long);

unsigned char __any_bounded_uchar (unsigned char, unsigned char);
unsigned short __any_bounded_ushort (unsigned short, unsigned short);
unsigned int __any_bounded_uint (unsigned int, unsigned int);
unsigned long __any_bounded_ulong (unsigned long, unsigned long);
unsigned long long __any_bounded_ulong_long (unsigned long long,unsigned long long);

#define any_int()                 __any_bounded_int (INT_MIN, INT_MAX)
#define any_bounded_int(min, max) __any_bounded_int(min, max)
 

