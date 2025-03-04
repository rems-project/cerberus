typedef unsigned char uint8_t;
typedef struct s {
    uint8_t a;
} s;
/*@
predicate (map<u64,u8>) Array_u8 (pointer p, u64 l)
{
  take pv = each(u64 i; i >= 0u64 && i < l) {RW<uint8_t>(array_shift<uint8_t>(p,i))};
  return pv;
}
@*/

#if 0
static void transmute_to_blob(void *p)
/*@
  requires take xsi = Array_u8(p, sizeof<s>);
  ensures take xso = RW<s>p);
  @*/
{
  /*@ from_bytes RW<s>(p); @*/
}
#else

static void untransmute_to_blob(void *p)
/*@
  requires take xsi = RW<s>(p);
  ensures take xso = Array_u8(p, sizeof<s>);
  @*/
{
  /*@ to_bytes RW<s>(p); @*/
}
#endif
