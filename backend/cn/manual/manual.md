---
title: CN Manual (draft, to be expanded)
fontsize: 20px
mainfont: sans-serif
linestretch: 1.4
maxwidth: 45em
---


<!-- section 'Annotation syntax' copied and adjusted from 2021-10-cn-report -->

## CN language

CN includes several different kinds of annotations for different purposes. Primarily, users write type specifications for functions and loops. In order to phrase these specifications, users may define (mutually) inductive datatypes, specification functions, and resource predicates. Finally, where verification requires reasoning steps outside the fragment handled by CN's proof automation, users assist in the proof, by inserting CN ghost statements, or by manually stating and applying lemmata required for the verification. The following gives an overview of each of these CN sub-languages. The full grammar is given in section "Grammar".


### Type specifications

Function and loop types are specified as "magic comments" of the form `/*@ ... @*/` in the C code. 

#### Function types

In the case of function definitions the magic comment is placed after the argument list, before the function body block:
```c
int f(...args...)
/*@ <function_spec> @*/
{
    ...body of f...
}
```

Here `<function_spec>` is the CN specification of `f`, a list of items of the following kind (and in that order):

- `trusted`

  To indicate that the function type should be trusted, not verified by CN.

- `accesses [<cn_variable> (SEMICOLON <cn_variable>)*]`

  (`accesses` followed by a semicolon-separated list of one or more variables) The list must only contain C global variables. The specification `accesses VARS`, for some list of global variables `VARS`, specifies that the functions takes (read and write) ownership of `VARS` on entry, and returns ownership of `VARS` at the end of its execution. 
  
  
  **Note:** On function return, `VARS` are permitted to have been assigned values different from their original values; if the values are required to be unchanged, this can be specified using additional `ensures` clauses. 
  
The `accesses` keyword provides a short-hand for specifications that can also be expressed using `requires` and `ensures` together with `Owned` (all of which are described below).


- `requires [<condition> (SEMICOLON <condition>)*]`

  (`requires` followed by a semicolon-separated list of one or more CN conditions) 
  
  `requires CONDS`, for a list `CONDS` of CN conditions (explained below), specifies that `CONDS` have to hold whenever the function is called.


- `ensures [<condition> (SEMICOLON <condition>)*]`

  (`ensures` followed by a semicolon-separated list of one or more CN conditions) 
  
  `ensures CONDS`, for a list of CN conditions `CONDS` (explained below), specifies that `CONDS` have to hold whenever the function returns.


- `function <cn_variable>`

(`function` followed by a variable name) 

This instructs CN to automatically derive a CN specification function, with the same name, from the annotated C function. Currently this only works for relatively simple C functions.


#### Loop types

In the case of loops, the CN type is given after the loop condition, before the loop body block (currently only for and while loops are supported):
```c
while( ...loop condition... )
/*@ <loop_spec> @*/
{
    ...loop body...
}
```

Here `<loop_spec>` is the CN loop invariant specification, which must be of the form:

```
inv [<condition> (SEMICOLON <condition>)*]
```

(`inv` followed by a semicolon-separated list of one or more CN conditions) 

`inv CONDS`, for a list of CN conditions `CONDS` (explained below), specifies that `CONDS` hold on loop entry (before the loop condition has been executed); hence `CONDS` can be assumed to hold when the loop condition and loop body are executed, and it has to be shown that their execution re-establishes `CONDS`.

**Note:** any global variables listed under `accesses` in the surrounding function's specification are also considered "accessed" as part of the loop specification: CN implicitly adds the corresponding ownership requirement into the loop invariant.


#### Conditions

CN conditions, as used in function and loop type specifications, include 

- logical conditions, 
- ownership conditions, and 
- (for convenience) let bindings.

These are defined in the following.
  
##### Logical conditions

There are two forms of logical conditions:
  
  - `<expr>` 
  
    (a boolean typed expression) 
    
    This simply asserts that the expression is required to evaluate to `true`.

  - `each LPAREN <base_type> <cn_variable> SEMICOLON <expr>
                  RPAREN LBRACE <expr> RBRACE`

    Condition `each (BT V; C) { E }` introduces a new variable `V`, of CN basetype `BT` (explained below) and asserts that whenever `C` holds (for `V`), `E` must also hold (for `V`). 
    
    For instance, `each (i32 i; 0i32 <= i && i < 10i32) { E }` requires `E` to hold for all instances of `i`, of basetype `i32`, when `i` is between `0` and `10`.




##### Ownership conditions

Users can specify ownership of memory using resources and ownership conditions. A resource is a permission to manipulate an area of memory. Similar to pointer ownership in Rust, this permission cannot be duplicated; unlike Rust, in CN ownership also cannot be dropped. In CN, resource predicates have *inputs* and *outputs*. Informally, inputs are used to specify *what is owned*, while the outputs are information that can be derived from the ownership, such as the pointee value in the case of an owned pointer.

**Resource predicates.** CN has three kinds of resource predicates, the built-in predicates `Owned` and `Block`, as well as user-defined predicates:

- `Owned<T>`, for any C-type `T`.

  `Owned<T>` takes as input a pointer-expression. For a given pointer expression `P`, `Owned<T>(P)` asserts full (read and write) ownership of memory at address `P`, at C-type `T`. Its output is the memory value at address `P`. `Owned<T>(P)` allows reading and writing `P`, or any of its parts.

- `Block<T>` for any C-type `T`.

  `Block<T>` takes as input a pointer-expression. For a given pointer expression `P`, `Block<T>(P)` asserts ownership of memory at address `P`, at C-type `T`; unlike `Owned`, `Block` represents "uninitialised" memory, which can be written but not read. The output of `Block` is `void`.

(Reading memory requires an `Owned` resource; writing requires only a `Block` resource and returns an `Owned` resource with updated value.) When the C-type `T` of Owned and Block can be inferred by CN, the C-type annotation `<T>` can be omitted.

- Aside from built-in resource predicates, users can also define new resource predicates, as explained later. A resource definition includes the definition of its inputs and outputs. The first input of a user-defined resource predicate must always be the pointer the ownership is associated with (just as in the case of `Owned` and `Block`). 

**Ownership conditions.** Ownership conditions are used to specify resource ownership in function and loop type specifications. They take the form

```take <cn_variable> = <resource>```

The condition `take V = RES` specifies that ownership of resource `RES` is required; it also introduces a new variable `V` and binds the outputs of resource `RES` to `V`. 

For instance `take x = Owned<int>(p)` specifies that ownership of
`int`-pointer `p` is required, and binds the name `x` to the output
of `Owned<int>(p)`, so the pointee value of `p`.

The resource is one of two kinds:

- `<pred> LPAREN [<expr> (COMMA <expr>)*] RPAREN`

  `Pred(ARGS)` asserts ownership of a resource predicate `Pred` (one of the three possible kinds defined above) applied to a list `ARGS` of one or more input expressions. The output of this resource is as defined by the resource predicate `Pred` (see above).

- `each LPAREN <base_type> <cn_variable> SEMICOLON <expr> RPAREN LBRACE <pred> LPAREN [<expr> (COMMA <expr>)*] RPAREN RBRACE`

  This is an iterated resource. Resource `each (BT V; C) { Pred(ARGS) }` introduces a new (quantified) variable `V` of basetype `BT` (explained below), and asserts ownership of multiple instances of resource predicate `Pred`: `Pred`, applied to arguments `ARGS`, is owned for all instances of variable `V` that satisfy condition `C`; typically both `C` and `ARGS` will mention `V`. 
  
  For instance, `each (i32 i; 0i32 <= i && i < 10i32) { Owned<int>(array_shift<int>(p,i)) }`, for an `int`-pointer `p`, requires ownership of an `int`-array starting at `p`, for all indices up to `10`. Here `array_shift<T>(P,I)`, for a C-type `T`, pointer `P` (of arbitrary pointer type), and index `I`, computes the pointer to the `I`-th element of an array starting from `P`, at type `T` (in the above example an `int`-array). 
  
  The first input of an iterated resource, the pointer, must be an expression of the shape `array_shift<T>(P,V)`, where `T` is a C-type, `P` some pointer and `V` the quantified variable. If `V` has basetype `BT` and the output of the resource predicate `P` is of basetype `OBT`, the iterated resource has an output of type `map<BT,OBT>`, a map from indices into the array (of quantifier basetype) to their output value (of basetype `OBT`).


##### Let-bindings

Finally, conditions also include let-bindings of the form

```let <cn_variable> EQ <expr>```

`let V = E` defines variable `V` to be the value of expression `E`.


##### Scoping

By default, in function specifications, global variables and the function arguments are in scope. In `inv` loop invariant specifications additionally the function's local variables are in scope. In `ensures` specifications the special `return` variable is in scope, to refer to the functions return value.

Conditions can bring new variables into scope (i.e. ownership conditions using `take`, and let-bindings). Within the body of `requires`, `ensures`, or `inv` their scoping follows the lexical structure. Moreover, variables bound in the `requires` pre-condition are in scope for `inv` loop invariants and for the `ensures` post-condition. (While variables bound in `ensures` and `inv` are not visible outside these.)

To make writing specifications more convenient, CN offers a short-hand for referring to the pointee of an owned pointer. Where the user has asserted `take V = Owned<...>(P)` for some pointer expression `P` and variable `V`, they can subsequently use the CN expression `*P` to refer to `V`. This is a shallow surface-level feature -- `*P` can only be used if `Owned` has been asserted for a term *syntactically* matching `P`, not merely one that is provably the same as `P`. (Hence, following condition `take V = Owned<...>(Q)`, CN will not allow the user to specify `*P` in a subsequent condition, even if `P==Q` is known.)

Since the user may include ownership of a pointer `P` both in the `requires` and the `ensures` specification, in principle the use of `*P` is ambiguous. CN uses the following rules:

- A condition `take V = Owned<...>(P)` within a `requires`/`ensures`/`inv` specification brings `*P` only into scope for subsequent conditions in the same `requires`/`ensures`/`inv` specification.  For instance 

  ```c
  void f(int *p)
  /*@ requires take x = Owned(p)
      ensures *p == 0i32 
  @*/
  {
      ...
  }
  ```
  will lead to an error, because `*p` is not in scope in the `ensures` specification.
  
- Users can moreover use special syntax to "evaluate" expressions using old pointee values, from the start of function execution: `{E}@start` instructs CN to evaluate pointer-dereference expressions (such as `*p`) using the initial pointee values from the `requires` specification. For instance the marked line in the example below asserts that the new value of `*p` is the old value incremented by 1. (The expression `E` in `{E}@start`, however, can freely combine pointer-dereferencing with other terms into complex expressions.)

  ```c
  void f(int *p)
  /*@ requires take x = Owned(p)
      ensures take y = Owned(p); 
              *p == {*p}@start + 1i32            // <---
  @*/
  {
      ...
  }
  ```

- A related short-hand is `{E} unchanged`, for the common assertion that the value of expressions `E`, typically involving pointer-dereferencing, is unchanged compare to the initial state (e.g. the value is the same before and after execution of the function, or is the same during the execution of the loop as in the initial state).


#### Basetypes

CN's base types include:

- `void` (or `unit`)
- `bool`
- bounded integer types, such as `i32` and `u8`
- unbounded mathematical integers, `integer` (hardly used)
- pointers, `pointer` (untyped in the pointee type)
- pointer allocation IDs, `alloc_id` (for the in-progress VIP memory model)
- C structs, `struct T`, for struct tags `T`
- user-defined inductive datatypes, `datatype T`, for a tag `T`
- records/anonymous structs `{ bt1 member1, ..., bt2 member2 }` 
- maps, `map<bt1,bt2>`, for map domain `bt1` and range `bt2`
- lists `list<bt>`, for a list element type `bt`
- sets, `set<bt>`, for a set element type `bt` (untested)



#### Expressions (EXPR)

CN has a C-like expression syntax. Expressions include

- C variables, 
- CN variables (such as let-bound variables and variables from `take` ownership conditions)
- pointer-dereferencing
- `{...}@start`
- `{...}@unchanged`
- integer arithmetic and comparison
- bit-wise arithmetic
- pointer operations
- boolean expressions
- struct-value and struct-update expressions
- map access and update operations



### Auxiliary definitions
#### Datatype definitions
#### Specification function definitions
#### Resource predicate definitions
### Proof assistance
#### CN statements
#### Lemma statements
