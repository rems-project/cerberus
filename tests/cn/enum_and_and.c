
typedef unsigned long long u64;
typedef unsigned int u32;

enum flags {
  flag_1 = 1,
  flag_4 = 4,
};

#include <stdbool.h>

void foo(enum flags flag, u32 level)
{
        bool table = (1 == 1);

        if (table && (flag & flag_1)) {
		return;
	}
}

int main(void)
/*@ trusted; @*/
{
  foo(flag_1, 1);
}
