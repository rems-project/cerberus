import qualified Data.Map as M

type Sym = String

data Expr
  = Eskip
  | Econst Integer
  | Esym Sym
  | Eif Expr Expr Expr
  | Eeq Expr Expr
  | Eadd Expr Expr
  | Esub Expr Expr
  | Ereturn Expr -- the expression must be pure
  | Eseq Sym Expr Expr
  | Eunseq [Expr]
  | Erun Sym
  | Esave Sym Expr
  | Ecall Sym [Expr]
  deriving Show


data Cont
  = Khole
  | Kskip
  | Kconst Integer
  | Ksym Sym
  | Kif Cont Cont Cont
  | Keq Cont Cont
  | Kadd Cont Cont
  | Ksub Cont Cont
  | Kreturn Cont
  | Kseq Sym Cont Cont
  | Kunseq [Cont]
  | Krun Sym
  | Ksave Sym Cont
  | Kcall Sym [Cont]
  deriving Show




data Fun
  = Fun Sym [Sym] Expr
  deriving Show

data Prog
  = Prog [Fun] Expr
  deriving Show

data Env = Env {
  symMap :: M.Map Sym Expr,  -- value bound by symbolic names (in seq)
  funMap :: M.Map Sym Fun,   -- env for functions

  currentFunction :: [Expr]
--  labMap :: M.Map Sym Expr   -- env for labels
} deriving Show


isValue :: Env -> Expr -> Bool
isValue _ (Econst _)    = True
isValue _ (Esym _)      = True
isValue _ (Eadd _ _)    = True
isValue _ (Esub _ _)    = True
isValue _ (Eeq _ _)     = True

-- isValue _ (Eif _ e1 e2) = isValue e1 && isValue e2

-- isValue env (Kadd e1 e2)   = isValue env e1 && isValue env e2
{-
isValue env (Ecall f args) =
  let Fun _ _ body = (funMap env) M.! f in
  isValue env body
-}
isValue _ _ = False

{-
eval :: Env -> Expr -> Expr
eval _ (Econst n)     = Econst n
eval env (Ereturn e)  = eval env e
eval env (Eadd e1 e2) = let Econst n1 = eval env e1
                            Econst n2 = eval env e2 in
                        Econst $ n1 + n2
eval env (Esub e1 e2) = let Econst n1 = eval env e1
                            Econst n2 = eval env e2 in
                        Econst $ n1 - n2
eval env (Eeq e1 e2) = let Econst n1 = eval env e1
                           Econst n2 = eval env e2 in
                       Econst $ if n1 == n2 then 1 else 0
-- eval env (Eif e1 e2 e3) = 
eval env (Esym a) = eval env $ (symMap env) M.! a

eval _ e = error $ "EVAL>> " ++ show e
-}


-- [subst e a e'] substitute [a] with [e'] in [e]
subst :: Expr -> Sym -> Expr -> Expr
subst Eskip           _ _  = Eskip
subst (Econst n   )   _ _  = Econst n
subst (Esym a')       a e' = if a == a' then e' else Esym a
subst (Eadd e1 e2)    a e' = Eadd (subst e1 a e') (subst e2 a e')
subst (Esub e1 e2)    a e' = Esub (subst e1 a e') (subst e2 a e')
subst (Eeq e1 e2)     a e' = Eeq (subst e1 a e') (subst e2 a e')
subst (Eif e1 e2 e3)  a e' = Eif (subst e1 a e') (subst e2 a e') (subst e3 a e')
subst (Ereturn e)     a e' = Ereturn (subst e a e')
subst (Eseq _a e1 e2) a e' = Eseq _a (subst e1 a e') (if a == _a then e2 else subst e2 a e')
subst (Eunseq es)     a e' = Eunseq $ map (\e -> subst e a e') es
subst (Erun d)        _ _  = Erun d
subst (Esave d e)     a e' = Esave d (subst e a e')
subst (Ecall f args)  a e' = Ecall f $ map (\e -> subst e a e') args





get_cont :: Env -> Sym -> Expr
get_cont env d =
  let e:_ = currentFunction env in
  case f e of
    Just e' -> e'
    Nothing -> error " BOOM in get_cont"
  where
    f Eskip          = Nothing
    f (Econst _)     = Nothing
    f (Esym _)       = Nothing
    f (Eeq e1 e2)    = case f e1 of
                         Just e  -> Just e
                         Nothing -> f e2
    f (Eadd e1 e2)   = case f e1 of
                         Just e  -> Just e
                         Nothing -> f e2
    f (Esub e1 e2)   = case f e1 of
                         Just e  -> Just e
                         Nothing -> f e2
    f (Eif _ e2 e3)  = case f e2 of
                         Just e  -> Just e
                         Nothing -> f e3
    f (Ereturn _)    = Nothing
    f (Eseq _ e1 e2) = case f e1 of
                         Just e  -> Just e
                         Nothing -> f e2
--    f (Eunseq es)
    f (Erun _)     = Nothing
    f (Esave d' e) = if d == d' then Just e else f e
    f (Ecall _ _)  = Nothing -- TODO: assuming I forbid labels in pure expressions ?



-- TODO: here we assume a unique hole
applyCont :: Cont -> Expr -> Expr
applyCont Khole e          = e
applyCont Kskip _          = Eskip
applyCont (Kconst n) _     = Econst n
applyCont (Ksym a) _       = Esym a
applyCont (Kif k1 k2 k3) e  = Eif (applyCont k1 e) (applyCont k2 e) (applyCont k3 e)
applyCont (Keq k1 k2) e    = Eeq (applyCont k1 e) (applyCont k2 e)
applyCont (Kadd k1 k2) e   = Eadd (applyCont k1 e) (applyCont k2 e)
applyCont (Ksub k1 k2) e   = Esub (applyCont k1 e) (applyCont k2 e)
applyCont (Kreturn k) e    = Ereturn (applyCont k e)
applyCont (Kseq a k1 k2) e = Eseq a (applyCont k1 e) (applyCont k2 e)
-- applyCont Kunseq [Cont]
applyCont (Krun d) _       = Erun d
applyCont (Ksave d k) e    = Esave d (applyCont k e)
applyCont (Kcall f ks) e = Ecall f $ map (\k -> applyCont k e) ks


composeCont :: Cont -> Cont -> Cont
composeCont k Khole          = k
composeCont k Kskip          = Kskip
composeCont k (Kconst n)     = Kconst n
composeCont k (Ksym a)       = Ksym a
composeCont k (Kif k1 k2 k3) = Kif (composeCont k k1) (composeCont k k2) (composeCont k k3)
composeCont k (Keq k1 k2)    = Keq (composeCont k k1) (composeCont k k2)
composeCont k (Kadd k1 k2)   = Kadd (composeCont k k1) (composeCont k k2)
composeCont k (Ksub k1 k2)   = Ksub (composeCont k k1) (composeCont k k2)
composeCont k (Kreturn k')   = Kreturn (composeCont k k')
composeCont k (Kseq a k1 k2) = Kseq a (composeCont k k1) (composeCont k k2)
-- composeCont Kunseq [Cont]
composeCont k (Krun d)       = Krun d
composeCont k (Ksave d k')    = Ksave d (composeCont k k')
composeCont k (Kcall f ks)   = Kcall f $ map (\x -> composeCont k x) ks


toCont :: Expr -> Cont
toCont Eskip          = Kskip
toCont (Econst n)     = Kconst n
toCont (Esym a)       = Ksym a
toCont (Eif e1 e2 e3) = Kif (toCont e1) (toCont e2) (toCont e3)
toCont (Eeq e1 e2)    = Keq (toCont e1) (toCont e2)
toCont (Eadd e1 e2)   = Kadd (toCont e1) (toCont e2)
toCont (Esub e1 e2)   = Ksub (toCont e1) (toCont e2)
toCont (Ereturn e)    = Kreturn (toCont e)
toCont (Eseq a e1 e2) = Kseq a (toCont e1) (toCont e2)
-- toCont (Eunseq es) = 
toCont (Erun d)       = Krun d
toCont (Esave d e)    = Ksave d (toCont e)
toCont (Ecall f args) = Kcall f $ map toCont args



red :: (Expr, Env, [Cont]) -> (Expr, Env, [Cont])
{-
red (e, env, _E : _ES)
  | isValue env e        = (applyCont _E (eval env e), env, _ES)

-}

red (Econst n, _, []) = error $ "DONE: " ++ show n

red (Econst n, env, _E : _ES) = (applyCont _E (Econst n), env, _ES)

red (Esym a, env, _ES) = ((symMap env) M.! a, env, _ES)

red (Eeq (Econst n1) (Econst n2), env, _ES) = (Econst $ if n1 == n2 then 1 else 0, env, _ES)
red (Eeq (Econst n1) e2, env, _E : _ES) = (e2, env, composeCont (Keq (Kconst n1) Khole) _E : _ES)
red (Eeq e1 e2, env, _E : _ES) = (e1, env, composeCont (Keq Khole (toCont e2)) _E : _ES)

red (Eadd (Econst n1) (Econst n2), env, _ES) = (Econst $ n1 + n2, env, _ES)
red (Eadd (Econst n1) e2, env, _E : _ES) = (e2, env, composeCont (Kadd (Kconst n1) Khole) _E : _ES)
red (Eadd e1 e2, env, _E : _ES) = (e1, env, composeCont (Kadd Khole (toCont e2)) _E : _ES)

red (Esub (Econst n1) (Econst n2), env, _ES) = (Econst $ n1 - n2, env, _ES)
red (Esub (Econst n1) e2, env, _E : _ES) = (e2, env, composeCont (Ksub (Kconst n1) Khole) _E : _ES)
red (Esub e1 e2, env, _E : _ES) = (e1, env, composeCont (Ksub Khole (toCont e2)) _E : _ES)

red (Eif (Econst n) e2 e3, env, _ES) =
  if n /= 0 then (e2, env, _ES)
            else (e3, env, _ES)

red (Eif e1 e2 e3, env, _E : _ES) = (e1, env, composeCont (Kif Khole (toCont e2) (toCont e3)) _E : _ES)


red (Ereturn (Econst n), env, _E : _ES) = (Econst n, env, _ES)

red (Eseq a e1 e2, env, _E : _ES) = (e1, env, composeCont (Kseq a Khole (toCont e2)) _E : _ES)

-- red (Eunseq es, env, _ES) = (e1, env, (\x -> Eseq a x e2) : _ES)

red (Erun d, env, _E : _ES) = (get_cont env d, env, _ES)

-- TODO: maybe a should keep track of the Esave
red (Esave d e, env, _ES) = (e, env, _ES)


red (Ecall f args, env, _ES) =
  let Fun _ params fbody = (funMap env) M.! f in
  (foldl (\acc (a,e) -> subst acc a e) fbody (zip params args), env {currentFunction= fbody : currentFunction env}, Khole : _ES)





foo n = if n == 1 then 1 else (foo $ n-1) + n

-- sum n := if n = 1 then 1 else sum(n-1) + n
_sum :: Fun
_sum = Fun "sum" ["n"] $ Eif (Eeq (Esym "n") (Econst 1))
                            (Econst 1)
                            (Eadd (Ecall "sum" [Esub (Esym "n") (Econst 1)]) (Esym "n"))



{-
f1 x :=
  x + if 1 then (run d; 42) else (save d. 24)


-}
f1 :: Fun
f1 = Fun "f1" ["x"] $ Eadd (Esym "x")
                           (Eif (Econst 1)
                                (Eseq "a" (Erun "d") (Econst 42))
                                (Esave "d" (Econst 24)))


-- test program
prog :: Prog
prog = Prog [_sum] $ Ecall "sum" [Econst 5]


emptyEnv :: Env
emptyEnv = Env M.empty M.empty [Eskip]

_init = Env M.empty (M.fromList [("sum", _sum)]) [Eskip]




run = loop (Ecall "sum" [Econst 5], _init, [])
  where
    loop x@(e, _, _) = do print e; putStrLn "\n\n"; loop (red x)



run2 = loop (Ecall "f1" [Econst 10], Env M.empty (M.fromList [("f1", f1)]) [Eskip], [])
  where
    loop x@(e, env, cont) = do  putStrLn $ "E = " ++ show e
                                putStrLn $ "F = " ++  (show $ currentFunction env)
                                putStrLn $ "K = " ++ show cont
                                putStrLn "\n\n"
                                loop (red x)


{-
  | Eunseq [Expr]
-}