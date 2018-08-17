#include <stdint.h>

#include <sys/ioctl.h>
#include <unistd.h>

#include "caml/alloc.h"
#include "caml/memory.h"
#include "caml/mlvalues.h"


// Rounding an ocaml float (which on a 64bits
// machine is a C double into a C float
// NOTE: this follows Pascal Cuoq's comment here
// https://stackoverflow.com/questions/45362323/ieee-64-and-32-bit-float-validation-in-ocaml?rq=1#comment77712839_45362890
value round_double_to_float32(value d)
{
  CAMLparam1(d);
  float f = Double_val(d);
  CAMLreturn(caml_copy_double(f));
}


value bits_of_float32(value d)
{
  CAMLparam1(d);
  union {
    float f;
    int32_t i32;
  } un = { .f = (float)Double_val(d) };
  CAMLreturn(caml_copy_int64((int64_t)un.i32));
}


value terminal_size(value unit)
{
  CAMLparam1(unit);
  CAMLlocal2(pair, ret);
  struct winsize wsz;
  if ( -1 == ioctl(STDOUT_FILENO, TIOCGWINSZ, &wsz) )
    // returns: None
    CAMLreturn(Val_int(0));
  
  // returns: Some (row,col)
  pair = caml_alloc_tuple(2);
  Field(pair, 0) = Val_int(wsz.ws_row);
  Field(pair, 1) = Val_int(wsz.ws_col);
  ret = caml_alloc(1, 0);
  Store_field(ret, 0, pair);
  CAMLreturn(ret);
}
