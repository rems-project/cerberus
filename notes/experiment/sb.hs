data CoreSyn
  = Atom String
  | Seq CoreSyn CoreSyn
  | Par CoreSyn CoreSyn
  | Call String
  deriving Show

data G = G {
  graph :: ([String], [(String, String)]),
  calls   :: [String]
} deriving Show

g :: [String] -> [(String, String)] -> G
g v e = G (v,e) []

(|||) :: CoreSyn -> CoreSyn -> CoreSyn
a ||| b = Par a b

(|>) :: CoreSyn -> CoreSyn -> CoreSyn
a |> b = Seq a b






ups :: String -> G -> [String]
ups v (G (vs, es) cs)
  | elem v vs = [ v' | v' <- vs, elem (v',v) es ]
  | otherwise = error "[ups] v is not inside vs"


-- [downs v g] the list of vertices sequenced after [v] in [g]
downs :: String -> G -> [String]
downs v (G (vs, es) cs)
  | elem v vs = [ v' | v' <- vs, elem (v,v') es ]
  | otherwise = error "[downs] v is not inside vs"
  


{-
  Graph semantics for function calls
    
    f      a call
    (V,E)  a graph (f \notin V)
    
    1: X <- V
    2: for each v IN X do
    3:   choose (f,v) or (v,f) and add to E
    4:   E <- transitive closure of E
    5:   X <- subset of X not connected to f
    6: done
  
-}
-- returns True iff 
accessible x y r =
  


transitiveClosure (vs,es) =
  es ++ [ (x,y) | x <- vs, y <- vs, accessible (x,y), not(elem (x,y) es) ]
  where
    accessible (x,y) = elem (x,y) es || elem 

callsem c (vs,es) =
  f vs es
  where
    f x es = do
               v <- x
               e <- [(f,v), (v,f)]
               f x (transitiveClosure es)
               


sem :: CoreSyn -> [G]
sem (Atom a)  = return (g [a] [])
sem (Seq a b) = do
  G (va, ea) ca <- sem a
  G (vb, eb) cb <- sem b
  return $ g (va ++ vb ++ ca ++ cb)
                          -- events of [a] are sequenced before those of [b].
             (ea ++ eb ++ [ (x,y) | x <- va++ca, y <- vb++cb ])
sem (Par a b) = do
  G (va, ea) ca <- sem a
  G (vb, eb) cb <- sem b
  let v' = va ++ vb
      e' = ea ++ eb
      c' = ca ++ cb
  return $ G (v',e')
             c'
sem (Call a) = return $ G ([],[]) [a]



-- graph :: CoreSyn -> G
-- graph (Atom a)  = ([a],[])
-- graph (Seq a b) = let (va,ea) = graph a
--                       (vb,eb) = graph b in
--                   (va++vb, ea ++ eb ++ [(x,y) | x <- va, y <- vb])
-- graph (Par a b) = let (va,ea) = graph a
--                       (vb,eb) = graph b in
--                   (va++vb, ea ++ eb)



toDot :: G -> String
toDot (G (vs,es) _) = "digraph G {\n" ++ printV vs ++ printE es ++ "}"
  where
    printV vs = foldl (\s v -> s ++ v ++ ";\n") "" vs
    printE es = foldl (\s (x,y) -> s ++ x ++ " -> " ++ y ++ ";\n") "" es



test1 = (Atom "A" ||| Atom "B") |> (Atom "C" ||| Atom "D")

test2 = Atom "A" |> (Atom "B" ||| Atom "C") |> Atom "D"


-- main = do
--   putStrLn (toDot $ graph test2)