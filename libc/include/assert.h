// 7.2 Diagnostics<assert.h>

// 7.2.1 assert must be redefined each time
#undef assert

#ifdef NDEBUG
#define assert(ignore) ((void)0)
#endif

#ifndef _ASSERT_H_
#define _ASSERT_H_

#define static_assert _Static_assert

#endif
