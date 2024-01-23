
## Note on Resources and CN logic

CN is a correctness checker for C programs. It is designed as an enhanced type
system (specifically, a refinement type system), based on separation logic.
In addition to well-typed arguments, C functions are annotated to
*require* various resources and preconditions. In addition to returning a
well-typed return value, C functions are annotated to *ensure* various
resources are returned to their caller, and various postconditions hold.

For instance, the function `deref_on_2` here takes a pointer argument `int *p`, and
additionally requires that it can take ownership (exclusive use) of the memory
that `p` points to via the `take .. Owned(p)` clause. It returns the same
resource to its parent via the `ensures` counterpart, `ensures take .. Owned(p)`.

```
int deref_on_2 (int *p, int x)
/*@ requires take p_v = Owned(p) @*/
/*@ requires x >= 0i32 @*/
/*@ ensures take p_v2 = Owned(p) @*/
{
  int y;
  if (x == 2) {
    y = *p;
  }
  else {
    y = 0;
  }
  return y;
}
```

### Process of type checking

CN type checks a program forward through its syntax. It begins at the
entry point, and assuming that all logical `requires` conditions hold, and
assuming that the required resources can be taken from the calling environment.
Type-checking then proceeds, statement by statement, from start to end. At
`return` points, CN must be able to prove the `ensures` postconditions, and all
the resources in the "ensures" clauses must be present. Furthermore, no other
(nonempty) resources may remain in the context once the named resources are
returned. CN has a linear type system for resources, and does not permit
resources to be discarded silently, instead they must be explicitly returned
or disposed of via a a call to `free` or similar.

Type-checking proceeds forwards through straight-line blocks, but forks at
conditionals such as `if (x == 2)` above. Here type-checking will split into
two cases, one assuming `x == 2`, the other assuming the opposite. Statements
after the conditional, such as `return y` above, might be type-checked in both
branches. This exploration is roughly a depth-first walk of the control-flow
graph. Impossible branch combinations will be detected, so some arcs of the
control-flow graph may be skipped.

Loops need to be annotated by the user with `inv` annotations, which, like the
`requires` annotations of the function, specify the preconditions and resources
required to execute the loop. For example, the invariant that `i` and `j` add to
seven is sufficient to verify this function:

```
int
count_to_seven(void)
/*@ ensures return == 7i32 @*/
{
  int i = 0, j = 7;
  while (j > 0)
  /*@ inv 0i32 <= j @*/
  /*@ inv 0i32 <= i @*/
  /*@ inv i + j == 7i32 @*/
  {
    j -= 1;
    i += 1;
  }
  return i;
}
```

These annotations specify what must be true and available prior to the loop.
Type-checking proceeds with the loop as an additional entry point, where the
`inv` conditions rather than the initial `requires` conditions are used to set
up the initial context. The loop entry point is the point where the loop
condition is tested, e.g. before the `j > 0` test in the example above.

When type checking a loop, if a `continue` statement returns to the loop entry
point, the `inv` conditions must all be established, much like how the
`ensures` conditions must hold at a `return` statement. Like a `return`
statement, all the resources must be claimed by the `inv` conditions, and none
can be left unusued. This must also be true at the implicit continue at the end
of the loop body, and at the point at which the loop is entered for the first
time from the main function body.

### Context of type checking

CN maintains a context as it is type checking. This context is split into a
logical context and a resource context.

The logical context contains a collection of known facts, which are used by CN
(supported by an SMT solver) to decide the provability of other facts. The
logical context also stores the types of variables, needed to check the type
correctness (in the simple sense) of expressions.

The logical context does not mutate, it is only extended. Variables do not
change type. Known logical facts are not removed from the context, so a
provable statement never becomes unprovable. It was mentioned above that the
type checking process forks at conditionals, with two future type checking
contexts that disagree on the truth of the conditional, each of which is then
extended but not changed by further type checking.

The resource context handles the mutable state of C. It consists of a list of
available resources. The default resource type is the `Owned<type>(pointer)`
builtin resource which provides full access to the memory pointed to by a
pointer. The `Block<type>(pointer)` resource is analogous, for possibly
uninitialised memory that may be written but not read. As an aside, CN does not
permit reads of possibly uninitialised memory, a conservative approach to a
complex aspect of the C standard. For both `Owned` and `Block`, the type argument
(a C type) may be omitted if it is clear from the context. For instance, if `p`
is a pointer whose type is known to be `int *p`, then `Owned(p)`,
`Owned<int>(p)` and `Owned<signed int>(p)` are all equivalent. Users may add
additional kinds of resources by defining compound resource predicates, as
documented (FIXME, add ref) elsewhere. Future CN versions may contain more
variations on the basic memory type, for instance a read-only resource.

All resources take some input arguments and return an output argument. The
first input argument must be a pointer (FIXME: thoughts about that constraint).
Resources also return some value, though this may be the `void` type. Return
values of resources are the bridge between the logical context and the mutable
resource context. Values returned from the process of taking resources appear
in the logical context. Operations that mutate a resource will consume the
relevant resource from the context and return a duplicate with a new current
value.

For instance, the function `adjust_on_2` below takes an integer pointer and may
adjust the cell it points to. The `Owned<int>(p)` requirement takes ownership
of the memory pointed to by `p`. The returned value, `p_v`, is a logical 32-bit
integer that is the current contents of this memory. The expression `*p < 1`
requires such a resource to be found in the context. If this were not claimed
for this function by the `requires` clause, this would result in a "missing
resource" type error. The resource is at this point unmodified, so the value
read is equal to `p_v`.  The fact that `*p` results in `p_v`, and the
additional logical requirement `p_v < 300i32`, are needed to prove the absence
of undefined behaviour in the expression `*p + 1` (C does not permit overflow
in signed arithmetic).

At the statement `*p = y;`, if it is reached, the type checking process
requires either `Owned(p)` or `Block(p)` to be consumed from the resource
context, and replaced with a new `Owned(p)` which returns the newly stored
value. Finally, the `ensures take p_v2 = Owned(p)` clause itself consumes this
resource from the context, binding its return value to the logical name `p_v2`.
The final logical postcondition, that the cell is either unmodified or set to a
value at least `2`, can then be proven from the available logical facts.

```
void adjust_on_2 (int *p, int x)
/*@ requires take p_v = Owned<int>(p) @*/
/*@ requires x >= 0i32 @*/
/*@ requires p_v < 300i32 @*/
/*@ ensures take p_v2 = Owned(p) @*/
/*@ ensures p_v2 == p_v || p_v2 >= 2i32 @*/
{
  int y;
  if (*p > 1) {
    y = *p + 1;
  }
  else {
    y = 2;
  }
  if (x == 2) {
    *p = y;
  }
}
```

The C language permits local variables (such as `y` above) and parameters (such
as `x` above) to have their addresses taken via the `&y` syntax. The Cerberus
toolchain, on which CN builds, handles this mechanism and the mutability of
local variables by placing them in memory. The simple function `adjust_on_2`
above is elaborated into a function that first allocates memory for its mutable
variables with addresses `&p`, `&x`, and `&y`. Reads and writes of `y`
elaborate to loads and stores at `&y`, roughly `*(&y)` in C syntax. During
their lifetimes these local allocations live in the resource context like any
other resource. The return values of these resources give the current values of
the mutable variables.

Resource predicates are used to claim larger quantities of memory and regions
of memory of variable shape. For instance, it is simple to define a recursive
resource predicate that claims all the nodes of a singly-linked list or a
binary tree. The return value of these predicates determine what specifications
can be written. A predicate that claims a binary tree and returns `void` can be
used to verify the spatial safety of a function that manipulates a binary tree.
To prove something about the contents of the returned tree, however, the
resource predicate would have to return some representation of that contents,
for instance as an algebraic datatype. (FIXME: refs)

