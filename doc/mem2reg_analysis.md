Let's replace `check_definitely_init` and `no_mixed_unseq_uses` (and
`expr_writes_sym`) with one function `sequentialisable`. Make a plan for this
as per CLAUDE.md and make sure the first step is to write that plan to
doc/history/. Make sure to also include a note to add an addendum to the same
plan after implementing and testing with any changes updates learned during
that process.

The function will have a similar shape to `check_definitely_init`, but instead
of `strongly_init` it will have a `env` which will be either `Uninit | Init
of pexpr | Killed`, and instead of `Write_kind.t` we'll have a `Mem_event.t
list`, where a `Mem_event.t` will either be a `Pos_store of pexpr | Neg_store
of pexpr | Load | Kill`. It will also be able to throw an exception
`Not_sequentialisable`. Its return values will all be wrapped in an option,
because the Erun case will always return None, and all other cases some.
All recursion on subterms will thus happen inside an option monad (define 
and use let* to write such code).

The basic idea is that it's an abstract interpretation. After recursing on a
subexpression, it will update the environment appropriately or throw an
exception if it can't, and then recurse on other subexpressions. For branching
ones like if and case, the env passed in will be the same, and the constructed
value will be a pure if and case respectively. The non-load events need to be
combinable: all kills, or all stores, where one `Neg_store` means the whole
expression is treated as a `Neg_store` of the constructed value.

The strong sequencing is easy enough, and the weak-sequencing needs to make
sure that negative store from e1 is unsequenced with events from e2, with the
resulting env and events combined or an exception thrown. Unseq will be
similar, except branches need to be either all reads, or at most one write.

Esaves and is treated similar to now, but there's no need to memoize 
anything, it will recurse in the body with respect to the corresponding
aliased parameter if there is one (and skipped otherwise). Eruns will
just return a None.

---

We will need a helper function `update_env env1 events1`, which will return
an `abs_env option`.

That function will filter out all the Load events from the set (call it events')
and then check the cardinality of what's left:
- If it's empty, then `env1` will be returned as is.
- If it's a singleton, and it has a `Kill` then the returned value will be
  `Some (Killed, events')`.
- If it's a singleton, and it has a `Pos_store pexpr | Neg_store pexpr`, the
  returned value will be `Some (Init pexpr, events')`.
- If it's got more than one element, the function will return `None`.

Back to `sequentialisable`. For the sseq case, the `sequentialisable` will
recurse on e1, and will have a `(env1, events1)`. It will then call
`update_abs_env env1 events1` to get an `env_opt`. If it's None, the
function will throw the `Not_sequentialisable` exception. Otherwise, it'll
unwrap the `Some (env2, _)` and pass it into recursing on the second expression.

For weak-sequencing, the function will recurse on `e1` similarly. But it will
call a `weak_update_env` helper function, which will be like `update_env` but
which returns an extra boolean flag inside the `Some` case signaling whether
the update was strong or weak. Similarly to sseq, the None case will raise an
exception, but the `Some (env2, events1')` will be used as follows.
`env2' = if is_weak_store events1' then env1 else env2`, and that will be
used to recurse on `e2`. We'll now have `(env1, events1)` and `(env2,
events2)`.

