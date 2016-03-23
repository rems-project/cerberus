import qualified Data.Map as M

type Sym     = String
type MemAddr = Integer

data Ctype = Ctype


data BinOp
  = OpAdd
  | OpSub
  | OpMul
  | OpDiv
  | OpMod
  | OpEq
  | OpLt
  | OpAnd
  | OpOr
  deriving Show

data Polarity
  = Pos | Neg

data Expr
  = Eskip
  | Econst Integer
  | Eaddr MemAddr
  | Esym Sym
  | Eop BinOp Expr Expr
  | Etrue
  | Efalse
  | Enot Expr
--  | Ectype Ctype
  | Elet Sym Expr Expr
  | Eif Expr Expr Expr
  | Ecall Sym [Expr]
--  | Esame Expr Expr
  | Eundef
--  | Eerror

  | Eaction Paction
  
  | Eunseq [Expr]
  | Ewseq [Maybe Sym] Expr Expr
--  | Esseq [Maybe Sym] Expr Expr
--  | Easeq (Maybe Sym) Action Paction

--  | Eindet Integer Expr
--  | Ebound Integer Expr

  | Esave Sym Expr -- save d. e
  | Erun Sym       -- run d
  
--  | End [Expr]

--  | Eshift Sym Expr

  | Ereturn Expr
  deriving Show

type Paction = Char

{-
data Action
  = Kcreate Expr
  | Kalloc Expr
  | Kkill Expr
  | Kstore Expr Expr Expr
  | Kload Expr Expr

data Paction = (Polarity, Action)
-}



data Cont
  = Khole
  | Kskip

  | Kpure Expr -- EXPERIMENT
--  | Kconst Integer
--  | Kaddr MemAddr
--  | Ksym Sym
--  | Kop BinOp Expr Expr
--  | Ktrue
--  | Kfalse
--  | Knot Expr
  | Klet Sym Expr Cont -- EXPERIMENT
  | Kif Expr Cont Cont -- EXPERIMENT
  | Kcall Sym [Expr]   -- EXPERIMENT
  | Kundef
  | Kaction Paction
  | Kunseq [Cont]
  | Kwseq [Maybe Sym] Cont Cont
  | Ksave Sym Cont
  | Krun Sym
--  | Knd [Cont] <--- I don't need that (?)

--  | Eshift Sym Expr

  | Kreturn Expr
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


isValue :: Expr -> Bool
isValue Eskip         = True
isValue (Econst _)    = True
isValue (Esym _)      = True
isValue (Eop _ _ _)   = True

-- isValue _ (Eif _ e1 e2) = isValue e1 && isValue e2

-- isValue env (Kadd e1 e2)   = isValue env e1 && isValue env e2
{-
isValue env (Ecall f args) =
  let Fun _ _ body = (funMap env) M.! f in
  isValue env body
-}
isValue _ = False

eval :: Env -> Expr -> Expr
eval _   Eskip          = Eskip
eval _   (Econst n)     = Econst n
eval _   (Eaddr x)      = Eaddr x
eval env (Esym a)       = eval env $ (symMap env) M.! a
eval env (Eop op e1 e2) =
  case (op, eval env e1, eval env e2) of
    (OpAdd, Econst n1, Econst n2) -> Econst $ n1 + n2
    (OpSub, Econst n1, Econst n2) -> Econst $ n1 - n2
    (OpMul, Econst n1, Econst n2) -> Econst $ n1 * n2
    (OpDiv, Econst n1, Econst n2) -> Econst $ div n1 n2
    (OpMod, Econst n1, Econst n2) -> Econst $ mod n1 n2
    (OpEq,  Econst n1, Econst n2) -> if n1 == n2 then Etrue else Efalse
    (OpLt,  Econst n1, Econst n2) -> if n1 < n2  then Etrue else Efalse
    (OpAnd, Etrue,     Etrue    ) -> Etrue
    (OpAnd, Etrue,     Efalse   ) -> Efalse
    (OpAnd, Efalse,    Etrue    ) -> Efalse
    (OpAnd, Efalse,    Efalse   ) -> Efalse
    (OpOr,  Etrue,     Etrue    ) -> Etrue
    (OpOr,  Etrue,     Efalse   ) -> Etrue
    (OpOr,  Efalse,    Etrue    ) -> Etrue
    (OpOr,  Efalse,    Efalse   ) -> Efalse
    _                             -> error "TYPE-ERROR in [eval] on a `Eop'"

eval _   (Etrue)        = Etrue
eval _   (Efalse)       = Efalse
eval env (Enot e)       = case eval env e of
                            Etrue  -> Efalse
                            Efalse -> Etrue
                            _      -> error "TYPE-ERROR in [eval] on a `Enot'"
eval env (Elet a e1 e2) =
  eval env{symMap= M.insert a (eval env e1) $ symMap env} e2


eval env (Eif e1 e2 e3) =
  case eval env e1 of
    Etrue  -> eval env e2
    Efalse -> eval env e3


eval env (Ecall f args) =
  let Fun _ params fbody = (funMap env) M.! f in
  eval env $ foldl (\acc (a,e) -> subst acc a e) fbody (zip params args)



eval _   e           = error $ "[eval] found a " ++ show e





-- [subst e a e'] substitute [a] with [e'] in [e]
subst :: Expr -> Sym -> Expr -> Expr
subst Eskip           _ _  = Eskip
subst (Econst n   )   _ _  = Econst n
subst (Esym a')       a e' = if a == a' then e' else Esym a
subst (Eop op e1 e2)  a e' = Eop op (subst e1 a e') (subst e2 a e')
subst (Eif e1 e2 e3)  a e' = Eif (subst e1 a e') (subst e2 a e') (subst e3 a e')
subst (Ereturn e)     a e' = Ereturn (subst e a e')
subst (Ewseq _a e1 e2) a e' = Ewseq _a (subst e1 a e') (if elem (Just a) _a then e2 else subst e2 a e')
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
    f (Eop _ _ _)    = Nothing
    f (Eif _ e2 e3)  = case f e2 of
                         Just e  -> Just e
                         Nothing -> f e3
    f (Ereturn _)    = Nothing
    f (Ewseq _as e1 e2) = case f e1 of
                            Just e  -> Just $ Ewseq _as e e2
                            Nothing -> f e2
--    f (Eunseq es)
    f (Erun _)     = Nothing
    f (Esave d' e) = if d == d' then Just e else f e
    f (Ecall _ _)  = Nothing -- TODO: assuming I forbid labels in pure expressions ?
    
    f (Eaction _) = Nothing
    
    f e = error $ "[get_conf f] found a " ++ show e


-- TODO: here we assume a unique hole
applyCont :: Cont -> Expr -> Expr
applyCont Khole e          = e
applyCont Kskip _          = Eskip
applyCont (Kpure e) _      = e
-- applyCont (Kconst n) _     = Econst n
-- applyCont (Ksym a) _       = Esym a
applyCont (Kif e1 k2 k3) e  = Eif e1 (applyCont k2 e) (applyCont k3 e)
applyCont (Kreturn e1) _    = Ereturn e1
applyCont (Kwseq a k1 k2) e = Ewseq a (applyCont k1 e) (applyCont k2 e)
-- applyCont Kunseq [Cont]
applyCont (Krun d) _       = Erun d
applyCont (Ksave d k) e    = Esave d (applyCont k e)
applyCont (Kcall f es) _ = Ecall f es

applyCont (Kaction act) _ = Eaction act


composeCont :: Cont -> Cont -> Cont
composeCont k Khole          = k
composeCont k Kskip          = Kskip
-- composeCont k (Kconst n)     = Kconst n
-- composeCont k (Ksym a)       = Ksym a
composeCont k (Kif e1 k2 k3) = Kif e1 (composeCont k k2) (composeCont k k3)
composeCont _ (Kreturn e)   = Kreturn e
composeCont k (Kwseq a k1 k2) = Kwseq a (composeCont k k1) (composeCont k k2)
-- composeCont Kunseq [Cont]
composeCont k (Krun d)       = Krun d
composeCont k (Ksave d k')    = Ksave d (composeCont k k')
composeCont _ (Kcall f es)   = Kcall f es

composeCont _ (Kaction act) = Kaction act


composeCont _ e = error $ "[composeCont] found a " ++ show e





toCont :: Expr -> Cont
toCont Eskip          = Kskip

toCont e
  | isValue e = Kpure e



toCont (Eif e1 e2 e3) = Kif e1 (toCont e2) (toCont e3)
toCont (Ereturn e)    = Kreturn e
toCont (Ewseq a e1 e2) = Kwseq a (toCont e1) (toCont e2)
-- toCont (Eunseq es) = 
toCont (Erun d)       = Krun d
toCont (Esave d e)    = Ksave d (toCont e)
toCont (Ecall f args) = Kcall f args

toCont (Eaction act) = Kaction act

toCont e = error $ "[toCont] found a " ++ show e


----------------------------------------------------------------------------------------------------



red :: (Expr, Env, [Cont], [Paction]) -> (Expr, Env, [Cont], [Paction])

red (e, env, [], tr)
  | isValue e        = error $ show (eval env e, tr)

red (e, env, Khole : _ES, tr)
  | isValue e        = (eval env e, env, _ES, tr)

red (e, env, _E : _ES, tr)
  | isValue e        = (applyCont _E (eval env e), env, Khole : _ES, tr)


-- red (Econst n, _, []) = error $ "DONE: " ++ show n

-- red (Econst n, env, _E : _ES) = (applyCont _E (Econst n), env, _ES)

-- red (Esym a, env, _ES) = ((symMap env) M.! a, env, _ES)

-- red (Eeq (Econst n1) (Econst n2), env, _ES) = (Econst $ if n1 == n2 then 1 else 0, env, _ES)
-- red (Eeq (Econst n1) e2, env, _E : _ES) = (e2, env, composeCont (Keq (Kconst n1) Khole) _E : _ES)
-- red (Eeq e1 e2, env, _E : _ES) = (e1, env, composeCont (Keq Khole (toCont e2)) _E : _ES)

-- red (Eadd (Econst n1) (Econst n2), env, _ES) = (Econst $ n1 + n2, env, _ES)
-- red (Eadd (Econst n1) e2, env, _E : _ES) = (e2, env, composeCont (Kadd (Kconst n1) Khole) _E : _ES)
-- red (Eadd e1 e2, env, _E : _ES) = (e1, env, composeCont (Kadd Khole (toCont e2)) _E : _ES)

-- red (Esub (Econst n1) (Econst n2), env, _ES) = (Econst $ n1 - n2, env, _ES)
-- red (Esub (Econst n1) e2, env, _E : _ES) = (e2, env, composeCont (Ksub (Kconst n1) Khole) _E : _ES)
-- red (Esub e1 e2, env, _E : _ES) = (e1, env, composeCont (Ksub Khole (toCont e2)) _E : _ES)

red (Eif p e2 e3, env, _ES, tr) =
  case n of
    Etrue  -> (e2, env, _ES, tr)
    Efalse -> (e3, env, _ES, tr)
  where
    n = eval env p


-- red (Eif e1 e2 e3, env, _E : _ES) = (e1, env, composeCont (Kif Khole (toCont e2) (toCont e3)) _E : _ES)


red (Ereturn (Econst n), env, _E : _ES, tr) = (Econst n, env, _ES, tr)

red (Ewseq a Eskip e2, env, _ES, tr) = (e2, env, _ES, tr)


red (Ewseq a e1 e2, env, _E : _ES, tr) = (e1, env, composeCont (Kwseq a Khole (toCont e2)) _E : _ES, tr)

-- red (Eunseq es, env, _ES) = (e1, env, (\x -> Ewseq a x e2) : _ES)

red (Erun d, env, _E : _ES, tr) = (get_cont env d, env, Khole : _ES, tr)

-- TODO: maybe a should keep track of the Esave
red (Esave d e, env, _ES, tr) = (e, env, _ES, tr)


red (Ecall f args, env, _ES, tr) =
  let Fun _ params fbody = (funMap env) M.! f in
  (foldl (\acc (a,e) -> subst acc a e) fbody (zip params args), env {currentFunction= fbody : currentFunction env}, Khole : _ES, tr)


red (Eaction act, env , _ES, tr) = (Eskip, env, _ES, tr ++ [act])



red x = error $ "[red] unmatched pattern: " ++ show x







----------------------------------------------------------------------------------------------------



foo n = if n == 1 then 1 else (foo $ n-1) + n

-- sum n := if n = 1 then 1 else sum(n-1) + n
_sum :: Fun
_sum = Fun "sum" ["n"] $ Eif (Eop OpEq (Esym "n") (Econst 1))
                            (Econst 1)
                            (Eop OpAdd (Ecall "sum" [Eop OpSub (Esym "n") (Econst 1)]) (Esym "n"))



{-
if true then
  run l1 >>
  save l2. A
else
  save l1. B >> run l2

>> C

-}
f1 :: Fun
f1 = Fun "f1" [] $
  Ewseq [Nothing] (Eif Etrue (Ewseq [Nothing] (Erun "l1") (Esave "l2" (Eaction 'A')))
                             (Esave "l1" (Ewseq [Nothing] (Eaction 'B') (Erun "l2"))))
                  (Eaction 'C')


-- test program
prog :: Prog
prog = Prog [_sum] $ Ecall "sum" [Econst 5]


emptyEnv :: Env
emptyEnv = Env M.empty M.empty [Eskip]

_init = Env M.empty (M.fromList [("sum", _sum)]) [Eskip]




run = loop (Ecall "sum" [Econst 5], _init, [], [])
  where
    loop x@(e, _, _, _) = do print e; putStrLn "\n\n"; loop (red x)



run2 = loop (Ecall "f1" [], Env M.empty (M.fromList [("f1", f1)]) [Eskip], [], [])
  where
    loop x@(e, env, cont, tr) = do putStrLn $ "E = " ++ show e
                                   putStrLn $ "F = " ++  (show $ currentFunction env)
                                   putStrLn $ "K = " ++ show cont
                                   putStrLn $ "T = " ++ show tr
                                   putStrLn "\n\n"
                                   loop (red x)


{-
  | Eunseq [Expr]
-}