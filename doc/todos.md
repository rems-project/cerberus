# Todos

- Started on mem2reg transform, but got stuck with save!
- Started fixing save mem2reg analysis, but realised it needs simultaneous sym
  analysis avoid locally bound symbols escaping in the env.

```c
int main()
{
    void *p;
    int houdini;
escape:
    p = &houdini;
    return 0;
}
```

```ocaml
proc main (): eff loaded integer :=
  let strong p: pointer = create(Ivalignof('void*'), 'void*') in
  let strong houdini: pointer = create(Ivalignof('signed int'), 'signed int') in
  store('void*', p, Unspecified('void*')) ;
  store('signed int', houdini, Unspecified('signed int')) ;
  save escape: unit (p: pointer:= p, houdini: pointer:= houdini) in
    let strong _: loaded pointer =
      bound(
        let weak a_509: pointer = pure(p) in
        let weak a_511: loaded pointer =
          let weak _: pointer = pure(houdini) in
          pure(Specified(houdini)) in
        let weak _: unit = neg(store('void*', a_509, a_511)) in
        pure(a_511)
      ) in
    pure(Unit) ;
  let strong a_512: loaded integer = bound(pure(Specified(0))) in
  kill('void*', p) ;
  kill('signed int', houdini) ;
  run ret_508(conv_loaded_int('signed int', a_512)) ;
  kill('void*', p) ;
  kill('signed int', houdini) ;
  pure(Unit) ;
  save ret_508: loaded integer (a_513: loaded integer:= Specified(0)) in
    pure(a_513)
```

Support createReadOnly?

Think about the mem2reg transform? At least as a sanity check.

Parallelise sequentialisable e.g. analyses collection of syms simultaneously?

Check that mem2reg works equally well with both calling conventions.

Check whether the invariant of Esave being closed is true if the inner-arg
calling convention is used?
