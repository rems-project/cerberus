Let's iterate on a plan (strictly as per CLAUDE.md) to implement the transform
step for mem2reg.

Inputs:
- sym => loaded t (unspec/spec pexpr) env
- set of syms written so far
- expression

Outputs:
- transformed expressions
- sym set to be bound


[load(p)] =>
    (env(p), None, so_far)

[store(p, v)] =>
    (v, Some { p }, so_far u { p } )

[kill(p)] => (Unit, None, so_far)

[let* x = create() in e] =>
    e

[pure(pe)] =>
  (pure((pe, env(x1), ..) ), Some so_far, 
  where x1 .. in so_far

[let* pat = e1 in e2] =>
  let (e1', set_opt, so_far) = rec e1 in
  match set_opt with
  | None -> let (e2', set_opt, so_far) = rec e2 in (let* pat = e1 in e2, set_opt, so_far)
  | Some vars ->
      let splatted = splat set_opt in
      let update_env = update env set_opt splatted in
      let pat1 = Option.fold set_opt ~none:pat ~some:(fun set -> splat set, pat) in
      let (e2', set_opt, so_far) = rec e2 update_env so_far in
      ([let* pat1 = e1' in e2', set_opt, so_far)

pure(pe) ==>
    pure((pe,pe1,..,pen))
    where env(x1) = Some pe1, .., env(xn) = Some pen
    x1, .., xn in set of written variables
    (sorted to ensure a consistent order)

Ememop, Eccall, Eproc, need to be handled similarly

Eexcluded can be skipped/assert false - it's a runtime only construct

let* pat = e1 in e2 ==>
    let* (pat, y1 : storable, .., yn : storable) = e1' in e2'
    where y1, .., yn are fresh variables
    where recursing on e1 first gives e1' and..
    - the set of variable written (x1, .., xn)
    - the updated environment env
    env is udpated extended/modified so that
    env(x1) = Some (y1), .., env(xn) = Some (yn)
    (sorted to ensure consistent order)
    all of which is used to recurse on e2'
    the resulting env and written var set is passed up as a whole

if pe then e1 else e2 ==>
    if pe then
        let (y1 : st, .., yk : st) = e1' in
        pure(pet1, y1, .., petm, yk)
    else
        (let z1 : str, .., zm : st) = e2' in
        pure(z1, pef1, .., zm, pefk)
    - where y1, .., yk bind all the variables written by e1
            (x1, .., xk)
      and   z1, .., zm bind all the variables written by e2
            (w1, .., wm)
    - pet1, .., petm are env(w1) = pet1, .. env(wm) = petm
    - pef1, .., pefk are env(x1) = pef1, .. env(xk) = pefk
    - the set of written variables is the union
    - the big tuple is ordered correspondingly
    - env1 is updated so that env1(x1) = Some y1, .., env1(xk) = Some yk
    - env2 is updated so that env2(w1) = Some z1, .., env2(wm) = Some zm 
    - env1 and env2 are combined (if they modify the same value, then None
      is fine, since it will be overwritten later, when the if expression is
      bound by a let)

Similarly for case-expressions

unseq(e1, .., en) ==>
    let ((a1, y1, ..), .., (an, z1, ..)) =
        unseq(e1', .., en') in
    - pure((a1, .., an), y1, .., z1, ..)
    - where e1', .., en' are all recursed
    - the environments are combined (should be no overlap)
    - and updated so that env(x1) = Some y1, .. env(w1) = Some z1
    - where x1, .. w1, .. and from the written var sets of each expression
    - the written var sets are all unioned

par is handled similarly

nd can be skipped entirely (it's always got pure values true and false inside)

bound(e) ==> bound(e')
    env and written vars unchanged

same with Eannot, Elet

---

Let's iterate on a plan (strictly as per CLAUDE.md) to implement the transform
step for mem2reg.  The transform for Esaves will always occur within the context
of a let strong _: unit = save (..) in E, into let strong (v1, v2, ..) :
(storable, storable, ..)  = save (..) in E, where v1, v2 are variables
representing the values in the promoted variables. Every control-flow path
within an Esave will end either in a unit or in a run, and the body of the save
will need to change each to supply the values of the promoted variables. After
the Esave's been tranformed, the environment for each promoted variable which
was passed in as a default argument will need to be updated to point to hold v1
v2 etc. respectively. The transform will return for each expression a set of
variables which have been modified; these will be sorted and used for
pattern-matching the new values and the new bound variables will be used to
update the environment. At the base case for any pure expression,
