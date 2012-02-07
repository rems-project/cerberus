val map_type : (CpAil.ctype -> CpAil.ctype) -> CpAil.ctype -> CpAil.ctype
val for_all_type : (CpAil.ctype -> bool) -> CpAil.ctype -> bool

val map_exp :
  ('e1 -> 'e2)
  -> ('id1 -> 'id2)
  -> ('id1, 'e1) CpAil.expression
  -> ('id2, 'e2) CpAil.expression

val map_stmt :
  ('s1 -> 's2)
  -> ('e1 -> 'e2)
  -> ('id1 -> 'id2)
  -> ('id1, 'e1, 's1) CpAil.statement
  -> ('id2, 'e2, 's2) CpAil.statement

val fold_exp_left :
  ('a -> 'e -> 'a)
  -> 'a
  -> ('id, 'e) CpAil.expression
  -> 'a

val fold_stmt_left :
  ('a -> 's -> 'a)
  -> ('a -> 'e -> 'a)
  -> 'a -> ('id, 'e, 's) CpAil.statement
  -> 'a
