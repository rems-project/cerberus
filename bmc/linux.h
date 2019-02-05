#ifndef	_LINUX_H_
#define	_LINUX_H_

// TODO: should be built in and not part of header
typedef enum linux_memory_order {
  linux_memory_order_once,
  linux_memory_order_acquire,
  linux_memory_order_release,
  linux_memory_order_rmb,
  linux_memory_order_wmb,
  linux_memory_order_mb,
  linux_memory_order_rbdep,
  linux_memory_order_rculock,
  linux_memory_order_rcuunlock,
  linux_memory_order_syncrcu,
} linux_memory_order;


#define smp_rmb() __cerbvar_linux_fence(linux_memory_order_rmb)
#define smp_wmb() __cerbvar_linux_fence(linux_memory_order_wmb)
#define smp_mb()  __cerbvar_linux_fence(linux_memory_order_mb)
#define smp_read_barrier_depends() __cerbvar_linux_fence(linux_memory_order_rbdep)
#define smp_load_acquire(object) __cerbvar_linux_read(&(object),linux_memory_order_acquire)
#define smp_store_release(object,desired) __cerbvar_linux_write(&(object),(desired),linux_memory_order_release)

// TODO: not the best api
//#define xchg_relaxed(ptr,desired) __cerbvar_linux_rmw((ptr),(desired),linux_memory_order_once)
//#define xchg_acquire(ptr,desired) __cerbvar_linux_rmw((ptr),(desired),linux_memory_order_acquire)
//#define xchg_release(ptr,desired) __cerbvar_linux_rmw((ptr),(desired),linux_memory_order_release)
//#define xchg(ptr,desired) __cerbvar_linux_rmw((ptr),(desired),linux_memory_order_mb)

#define READ_ONCE(object) __cerbvar_linux_read(&(object),linux_memory_order_once)
#define WRITE_ONCE(object,desired) __cerbvar_linux_write(&(object),(desired),linux_memory_order_once)

#define rcu_read_lock() __cerbvar_linux_fence(linux_memory_order_rculock)
#define rcu_read_unlock() __cerbvar_linux_fence(linux_memory_order_rcuunlock)
#define synchronize_rcu() __cerbvar_linux_fence(linux_memory_order_syncrcu)


#endif
