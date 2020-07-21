/************************************************************************************/
/*  BSD 2-Clause License                                                            */
/*                                                                                  */
/*  Cerberus                                                                        */
/*                                                                                  */
/*  Copyright (c) 2011-2020                                                         */
/*    Kayvan Memarian                                                               */
/*                                                                                  */
/*  All rights reserved.                                                            */
/*                                                                                  */
/*  Redistribution and use in source and binary forms, with or without              */
/*  modification, are permitted provided that the following conditions are met:     */
/*                                                                                  */
/*  1. Redistributions of source code must retain the above copyright notice, this  */
/*     list of conditions and the following disclaimer.                             */
/*                                                                                  */
/*  2. Redistributions in binary form must reproduce the above copyright notice,    */
/*     this list of conditions and the following disclaimer in the documentation    */
/*     and/or other materials provided with the distribution.                       */
/*                                                                                  */
/*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"     */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE       */
/*  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE  */
/*  DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE    */
/*  FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL      */
/*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR      */
/*  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER      */
/*  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,   */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE   */
/*  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.            */
/************************************************************************************/

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
