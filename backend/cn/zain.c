
/* 
1. malloc() for generated heap
2. initialise heap with generated values
3. call CN-annotated function with concrete heap values
*/


/*
Steps for translation:

Mathematical context + heap
->
Ail program (nodes from ailSyntax.ml/ailSyntax.lem)
->
Pretty-print into doc, then string (ocaml_frontend/pprinters/pp_ail.ml)
->
Augment input file with this string
*/

struct int_list { 
  int head;
  struct int_list* tail;
};

struct int_list* IntList_append(struct int_list* xs, struct int_list* ys) 
/*@ requires take L1 = IntList(xs) @*/
/*@ requires take L2 = IntList(ys) @*/
/*@ ensures take L3 = IntList(return) @*/
/*@ ensures L3 == append(L1, L2) @*/
{ 
  if (xs == 0) { 
    /*@ unfold append(L1, L2); @*/
    return ys;
  } else { 
    /*@ unfold append(L1, L2); @*/
    struct int_list *new_tail = IntList_append(xs->tail, ys);
    xs->tail = new_tail;
    return xs;
  }
}

