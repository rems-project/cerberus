#include <stdlib.h>

/*@
// copying from list_cn_types.h
datatype seq {
  Seq_Nil {},
  Seq_Cons {i32 head, datatype seq tail}
}
@*/

/*@
function (i32) hd (datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      0i32
    }
    Seq_Cons {head : h, tail : _} => {
      h
    }
  }
}

function (datatype seq) tl (datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      Seq_Nil {}
    }
    Seq_Cons {head : _, tail : tail} => {
      tail
    }
  }
}
@*/
/*@
function [rec] (datatype seq) snoc(datatype seq xs, i32 y) {
  match xs {
    Seq_Nil {} => {
      Seq_Cons {head: y, tail: Seq_Nil{}}
    }
    Seq_Cons {head: x, tail: zs}  => {
      Seq_Cons{head: x, tail: snoc (zs, y)}
    }
  }
}
@*/

/*@
// copying from list_length.c
function [rec] (i32) length(datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      0i32
    }
    Seq_Cons {head : h, tail : zs}  => {
      1i32 + length(zs)
    }
  }
}

function (i32) queue_size (i32 inp, i32 outp, i32 bufsize)
{
  ((inp - outp) + bufsize) % bufsize
}


function [rec] (datatype seq) seq_of_buf (map<i32,i32> buf, i32 inp, i32 outp, i32 bufsize) {
  if (queue_size (inp, outp, bufsize) > 0i32) {
    Seq_Cons {
      head: buf[outp],
      tail: seq_of_buf(buf, inp, (outp + 1i32) % bufsize, bufsize)
    }
  }
  else {
    Seq_Nil {}
  }
}

@*/


struct queue
{
  int inp;
  int outp;
  int size;
  int* buf;
};

/*@
function (boolean) queue_wf (i32 inp, i32 outp, i32 bufsize)
{
  bufsize > 0i32
  && (i64) bufsize + (i64) bufsize <= 2147483647i64
  && (0i32 <= inp && inp < bufsize)
  && (0i32 <= outp && outp < bufsize)
}


type_synonym state = {
  datatype seq content,
  i32 size  // max size
}

predicate state QueueAbs(pointer p)
{
  take q = Owned<struct queue>(p);
  take buf = each (i32 i; 0i32 <= i && i < q.size) { Owned<int>(q.buf + i) };
  assert (queue_wf (q.inp, q.outp, q.size));
  let content = seq_of_buf(buf, q.inp, q.outp, q.size);
  return {content: content, size: q.size - 1i32};
}

@*/

void* cn_malloc(unsigned long size);

int* malloc_buf(int size)
/*@
  trusted;
  requires size < 8192i32;
  ensures take rv = each (i32 i; 0i32 <= i && i < size) { Owned<int>(return + i) };
@*/
{
  return cn_malloc(size * sizeof(int));
}

struct queue* malloc_queue()
  /*@
    trusted;
    requires true;
    ensures take rv = Owned<struct queue>(return);
  @*/
{
  return cn_malloc(sizeof(struct queue));
}


struct queue* new(int n)
  /*@ requires 0i32 < n;
               (i64) n + (i64) n + 2i64 < 8192i64;
      ensures take queue_out = QueueAbs(return);
              queue_out.size == n;
              queue_out.content == Seq_Nil {};
  @*/
{
  int bufsize = n + 1;
  int* buff = malloc_buf(bufsize);
  struct queue q = {0, 0, bufsize, buff};
  struct queue* qptr = malloc_queue();
  *qptr = q;
  return qptr;
}

void put(struct queue* q, int n)
/*@ requires take queue = QueueAbs(q);
             let expected_content = snoc(queue.content, n);  // Why not inline below?
    ensures take queue_out = QueueAbs(q);
            queue_out.content == expected_content;
            queue_out.size == queue.size;
@*/
{
  /*@ extract Owned<int>, q->inp; @*/
  q->buf[q->inp] = n;
  q->inp = (q->inp + 1) % q->size;
}

int get(struct queue* q)
/*@ requires take queue = QueueAbs(q);
             length(queue.content) > 1i32;
    ensures take queue_out = QueueAbs(q);
            return == hd(queue.content);
            queue_out.content == tl(queue.content);
            queue_out.size == queue.size;
@*/
{
  /*@ extract Owned<int>, q->outp; @*/
  int ans = q->buf[q->outp];
  q->outp = (q->outp + 1) % q->size;
  return ans;
}

int queueSize(struct queue* q)
/*@ requires take queue = QueueAbs(q);
    ensures take queue_out = QueueAbs(q);
            queue == queue_out;
            return == length(queue.content);
@*/
{
  return (q->inp - q->outp + q->size) % q->size;
}
