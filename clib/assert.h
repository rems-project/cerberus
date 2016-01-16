#ifndef	_ASSERT_H_
#define	_ASSERT_H_

// 7.2 Diagnostics<assert.h>

#ifdef NDEBUG
#define assert(ignore) ((void)0)
#elseif
// void assert(scalar expression); // TODO the "polymorphic" type implies we need a specific construct in Cabs/Ail...
#endif // NDEBUG

#define static_assert _Static_assert

#else
#endif
