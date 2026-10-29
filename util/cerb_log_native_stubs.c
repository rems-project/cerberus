/* Native OCaml 5 static strings have the out-of-heap header defined by the
   runtime. Such blocks are never moved or reclaimed by the GC. Do not admit
   ordinary heap strings to an address-keyed table, even after promotion.
   This uses the runtime's header macros; it does not scan binary data or
   depend on linker symbols, a data-segment layout, or string contents.

   The caller supplies a well-typed OCaml string. Both functions are noalloc:
   no callback, allocation, or release of the runtime lock is permitted. */
#include <stdint.h>
#include <caml/mlvalues.h>
#include <caml/version.h>

#if OCAML_VERSION_MAJOR != 5
#error Review the static-string admission check before using a new OCaml major version
#endif

CAMLprim value cerb_log_is_static(value name)
{
  header_t hd = Hd_val(name);
  return Val_bool(Tag_hd(hd) == String_tag &&
    Color_hd(hd) == Color_hd(Caml_out_of_heap_header(0, String_tag)));
}

CAMLprim value cerb_log_pointer_hash(value name)
{
  /* Drop alignment bits, then mix nearby literal addresses into low bits.
     Unsigned arithmetic avoids signed overflow; Val_long supplies tagging.
     Equality still compares the complete pointer, so collisions are harmless. */
  uint64_t x = (uintnat)name >> 3;
  x ^= x >> 16;
  x = (x * UINT64_C(0x9e3779b97f4a7c15)) & (UINT64_MAX >> 1);
  x ^= x >> 31;
  return Val_long((uintnat)x);
}
