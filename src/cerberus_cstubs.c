#include <stdint.h>

#include <sys/ioctl.h>
#include <unistd.h>

#include "caml/alloc.h"
#include "caml/mlvalues.h"

// Rounding an ocaml float (which on a 64bits
// machine is a C double into a C float
// NOTE: this follows Pascal Cuoq's comment here
// https://stackoverflow.com/questions/45362323/ieee-64-and-32-bit-float-validation-in-ocaml?rq=1#comment77712839_45362890
value round_double_to_float32(value d)
{
  float f = Double_val(d);
  return caml_copy_double(f);
}


value bits_of_float32(value d)
{
  union {
    float f;
    int32_t i32;
  } un = { .f = (float)Double_val(d) };
  return caml_copy_int64((int64_t)un.i32);
}


value terminal_size(value unit)
{
  struct winsize wsz;
  ioctl(STDOUT_FILENO, TIOCGWINSZ, &wsz);
  
  value ret = caml_alloc_tuple(2);
  Field(ret, 0) = Val_int(wsz.ws_row);
  Field(ret, 1) = Val_int(wsz.ws_col);
  return ret;
}
