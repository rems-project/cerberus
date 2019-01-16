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


#define smb_rmb() __cerbvar_linux_fence(linux_memory_order_rmb)
#define smb_wmb() __cerbvar_linux_fence(linux_memory_order_wmb)
#define smb_mb()  __cerbvar_linux_fence(linux_memory_order_mb)
#define smb_read_barrier_depends() __cerbvar_linux_fence(linux_memory_order_rbdep)
#define smb_load_acquire(object) __cerbvar_linux_read(&(object),linux_memory_order_acquire)
#define smb_store_release(object,desired) __cerbvar_linux_write(&(object),(desired),linux_memory_order_release)

// TODO: not the best api
#define xchg_relaxed(ptr,desired) __cerbvar_linux_rmw((ptr),(desired),linux_memory_order_once)
#define xchg_acquire(ptr,desired) __cerbvar_linux_rmw((ptr),(desired),linux_memory_order_acquire)
#define xchg_release(ptr,desired) __cerbvar_linux_rmw((ptr),(desired),linux_memory_order_release)
#define xchg(ptr,desired) __cerbvar_linux_rmw((ptr),(desired),linux_memory_order_mb)

#define READ_ONCE(object) __cerbvar_linux_read(&(object),linux_memory_order_once)
#define WRITE_ONCE(object,desired) __cerbvar_linux_write(&(object),(desired),linux_memory_order_once)


#endif
