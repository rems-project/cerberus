{-#  LANGUAGE ScopedTypeVariables #-}
import Data.Maybe
import Data.List
import Data.Either
import Control.Monad


data Expr
  = Katom String
  | Kindet
  | Kseq Expr Expr
  | Kunseq [Expr]
  | Kbefore Expr
  | Kafter Expr
  deriving Eq

instance Show Expr where
  show (Katom a)    = a
  show (Kindet)     = "[f]"
  show (Kseq e1 e2) = "(" ++ show e1 ++ "; " ++ show e2 ++ ")"
  show (Kunseq [e])  = "\x1b[31m[\x1b[0m" ++ show e ++ "\x1b[31m]\x1b[0m"
  show (Kunseq es)  = "<" ++ intercalate " || " (map show es) ++ ">"
  show (Kbefore e)  = "^{" ++ show e ++ "}"
  show (Kafter e)   = "v{" ++ show e ++ "}"


data Dir
  = B | A
  deriving (Show, Eq)




pickOne :: [a] -> [([a], a, [a])]
pickOne l = msum $ map return (f [] l)
  where
    f acc []     = []
    f acc (x:xs) = (reverse acc, x, xs) : f (x:acc) xs



-- one :: Expr -> [(Dir, Expr)]
one (Katom a) = return (B, Kbefore (Katom a)) `mplus` return (A, Kafter (Katom a))

one (Kseq Kindet e2) = return (A, Kseq Kindet (Kafter e2)) -- CHECK returned Dir
one (Kseq e1 Kindet) = return (B, Kseq (Kbefore e1) Kindet) -- CHECK returned Dir

one (Kseq e1 e2) = do
  (d, e1') <- one e1
  case d of
    B -> one e2 >>= \(d', e2') -> return (d', Kseq e1' e2') -- TODO: not sure about the returned dir
    A -> return (d, Kseq e1' (Kafter e2))

one (Kunseq es) = do
  (ds, es') <- mapM one es >>= return . unzip
  return (if all (==B) ds then B else A, Kunseq es')


data M a
  = Modified a
  | Unmodified a
  deriving Show

isUnseq (Kunseq _) = True
isUnseq _          = False

isSingleton [_] = True
isSingleton _   = False

two :: Expr -> Expr
two (Kunseq [e]) = error "SINGLETON UNSEQ"

-- TMP ?
two (Kseq e1 Kindet) = Kunseq [e1, Kindet]

two (Kseq (Kbefore e1) (Kbefore e2)) = Kbefore (Kseq e1 e2)
two (Kseq (Kafter e1) (Kafter e2))   = Kafter (Kseq e1 e2)
two (Kseq (Kbefore e1) (Kafter e2))  = Kunseq [Kbefore e1, Kafter e2]
two (Kseq e1 (Kunseq es))            = let (as, _es) = partition (\e -> case e of Kafter _ -> True; _ -> False) es in
                                       if null as then Kseq (two e1) (two $ Kunseq es)
                                                  else Kunseq $ [Kseq e1 (case _es of [_e] -> _e; _ -> Kunseq _es),
                                                                 Kafter (case map (\(Kafter e) -> e) as of [x] -> x; xs -> Kunseq xs)]
two (Kseq e1 e2)                     = Kseq (two e1) (two e2)
two (Kunseq es)
  | any isUnseq es' = case (foldl (\acc e -> case e of Kunseq es -> acc ++ es
                                                       _         -> acc ++ [e]) [] es') of
                        [x] -> x -- TODO: should not be possible ?
                        xs  -> Kunseq xs
  | otherwise       = let (bs, as, xs) = f es' ([],[],[]) in
                      case (case bs of
                              []  -> []
                              [b] -> [Kbefore b]
                              _   -> [Kbefore $ Kunseq bs]) ++
                           (case as of
                              []  -> []
                              [a] -> [Kafter a]
                              _   -> [Kafter $ Kunseq as]) ++ xs of
                        [] -> error "BOOM ?"
                        [x] -> x
                        xs -> Kunseq xs
  where
    es' = map two es
    f []       acc           = acc
    f (x : xs) (bs, as, xs') = case x of
--                                 Kunseq es            -> f xs (bs,         as,        xs' ++ es  )
                                 Kbefore e            -> f xs (bs ++ [e],  as,        xs'        ) -- YUCK
                                 Kafter e             -> f xs (bs,         as ++ [e], xs'        ) -- YUCK
--                                 Kseq (Kbefore e1) e2 -> f xs (bs ++ [e1], as,        xs' ++ [e2]) -- YUCK
                                 e                    -> f xs (bs,         as,        xs' ++ [e] ) -- YUCK



two (Kbefore e) = Kbefore e
two (Kafter e)  = Kafter e
two (Kindet)    = Kindet

two e = error (show e)
-- two e = e

fp e = let e' = two e in if e == e' then e else fp e'


three e = let e' = two e in if e == e' then final e else three e'

final Kindet  = Kindet
final (Kunseq [Kindet, Kbefore bs])  = Kseq bs Kindet
final (Kunseq [Kbefore bs, Kindet])  = Kseq bs Kindet
final (Kunseq [Kafter as, Kindet])  = Kseq Kindet as
final (Kunseq [Kindet, Kafter as])  = Kseq Kindet as


final (Kunseq [Kindet,     Kbefore bs, Kafter as])  = Kseq bs (Kseq Kindet as)
final (Kunseq [Kindet,     Kafter as,  Kbefore bs]) = Kseq bs (Kseq Kindet as)
final (Kunseq [Kbefore bs, Kindet,     Kafter as])  = Kseq bs (Kseq Kindet as)
final (Kunseq [Kafter as,  Kindet,     Kbefore bs]) = Kseq bs (Kseq Kindet as)
final (Kunseq [Kbefore bs, Kafter as,  Kindet])     = Kseq bs (Kseq Kindet as)
final (Kunseq [Kafter as,  Kbefore bs, Kindet])     = Kseq bs (Kseq Kindet as)

final e = error $ show e



xs = fromJust $ zero testC


{-
  if any (\e' -> case e' of Modified _ -> True; Unmodified (Kunseq _) -> True; _ -> False) es'
    then case two (Kunseq $ let (bs, as, xs) = f es' ([],[],[]) in
                            (if null bs then [] else [Kbefore (Kunseq bs)]) ++
                            xs ++
                            (if null as then [] else [Kafter (Kunseq as)])) of
           Modified e'   -> two e'   
           Unmodified e' -> Modified e'
    else Unmodified (Kunseq es)
  where
    es' = map two es
    f []       acc           = acc
    f (x : xs) (bs, as, xs') = case (case x of Modified x -> x; Unmodified x -> x) of
                                 Kunseq es -> f xs (bs, as, xs' ++ es)
                                 Kbefore e -> f xs (bs ++ [e], as, xs') -- YUCK
                                 Kafter e  -> f xs (bs, as ++ [e], xs') -- YUCK
                                 Kseq (Kbefore e1) e2 -> f xs (bs ++ [e1], as, xs' ++ [e2]) -- YUCK
                                 e         -> f xs (bs, as, xs' ++ [e]) -- YUCK

two e = Unmodified e
-}

{-
two :: Expr -> M Expr
-- two e = msum [twoSeqB e, twoSeqA e]

two (Kseq (Kbefore e1) (Kbefore e2)) = Modified $ Kbefore (Kseq e1 e2)
two (Kseq (Kafter e1) (Kafter e2))   = Modified $ Kafter (Kseq e1 e2)
two (Kseq (Kbefore e1) (Kafter e2))  = Modified $ Kunseq [Kbefore e1, Kafter e2]
two (Kseq e1 e2)                     = let e1' = two e1
                                           e2' = two e2 in
                                       case (e1', e2') of
                                         -- YUCK
                                         (Unmodified _, Unmodified _) -> Unmodified (Kseq e1 e2)
                                         (Modified e1', Unmodified _) -> case two (Kseq e1' e2) of
                                                                           Modified e'   -> two e'
                                                                           Unmodified e' -> Modified e'
                                         (Unmodified _, Modified e2') -> case two (Kseq e1 e2') of
                                                                           Modified e'   -> two e'
                                                                           Unmodified e' -> Modified e'
                                         (Modified e1', Modified e2') -> case two (Kseq e1' e2') of
                                                                           Modified e'   -> two e'
                                                                           Unmodified e' -> Modified e'

-- TODO: this is silly, or not
two (Kunseq es) =
  if any (\e' -> case e' of Modified _            -> True;
                            Unmodified (Kunseq _) -> True;
--                            Unmodified (Kbefore _) -> True;
--                            Unmodified (Kafter _) -> True;                            
                            _ -> False) es'
    then case two (Kunseq $ let (bs, as, xs) = f es' ([],[],[]) in
                            (if null bs then [] else [Kbefore (Kunseq bs)]) ++
                            xs ++
                            (if null as then [] else [Kafter (Kunseq as)])) of
           Modified e'   -> two e'   
           Unmodified e' -> Modified e'
    else Unmodified (Kunseq es)
  where
    es' = map two es
    f []       acc           = acc
    f (x : xs) (bs, as, xs') = case (case x of Modified x -> x; Unmodified x -> x) of
                                 Kunseq es -> f xs (bs, as, xs' ++ es)
                                 Kbefore e -> f xs (bs ++ [e], as, xs') -- YUCK
                                 Kafter e  -> f xs (bs, as ++ [e], xs') -- YUCK
                                 Kseq (Kbefore e1) e2 -> f xs (bs ++ [e1], as, xs' ++ [e2]) -- YUCK
                                 e         -> f xs (bs, as, xs' ++ [e]) -- YUCK

two e = Unmodified e
-}




{-
twoSeq (Kseq (Kbefore e1) (Kbefore e2)) = return $ Kbefore (Kseq e1 e2)
twoSeqB _ = mzero
twoSeqA (Kseq (Kafter e1) (Kafter e2))   = return $ Kafter (Kseq e1 e2)
twoSeqA _ = mzero

twoSeq
-}


{-
^{A;    B;    C} || (((^{X}; ^{Y}); ([f]; v{Z})))  
^{A;    B;    C} || (((^{X}; v{Y}); v{([f]; Z)}))  BAD
^{A;    B;    C} || (((v{X}; v{Y}); v{([f]; Z)}))  BAD
^{A;    B}; v{C} || (((^{X}; ^{Y}); ([f]; v{Z})))  
^{A;    B}; v{C} || (((^{X}; v{Y}); v{([f]; Z)}))  BAD
^{A;    B}; v{C} || (((v{X}; v{Y}); v{([f]; Z)}))  BAD
^{A}; v{B;    C} || (((^{X}; ^{Y}); ([f]; v{Z})))  
^{A}; v{B;    C} || (((^{X}; v{Y}); v{([f]; Z)}))  BAD
^{A}; v{B;    C} || (((v{X}; v{Y}); v{([f]; Z)}))  BAD
v{A;    B;    C} || (((^{X}; ^{Y}); ([f]; v{Z})))  
v{A;    B;    C} || (((^{X}; v{Y}); v{([f]; Z)}))  BAD
v{A;    B;    C} || (((v{X}; v{Y}); v{([f]; Z)}))  BAD
-}

{-
zero :: Expr -> Maybe Expr
zero (Katom a) = Nothing
zero (Kindet)  = Just Kindet

zero (Kseq Kindet e2) = Just $ Kseq Kindet (Kafter e2)
zero (Kseq e1 Kindet) = Just $ Kseq (Kbefore e1) Kindet
zero (Kseq e1 e2)     = case zero e1 of
                          Nothing  -> case zero e2 of
                                        Nothing  -> Nothing
                                        Just e2' -> Just $ Kseq (Kbefore e1) e2'
                                      -- no need to look inside [zero e2] because we can only have 1 indet
                          Just e1' -> Just $ Kseq e1' (Kafter e2)

zero (Kunseq es) = sequence (map zero es) >>= return . Kunseq
-- Just $ Kunseq (map (\e -> maybe e id (zero e)) es)
-}



zero :: Expr -> Maybe [Expr]
-- zero :: MonadPlus m => Expr -> Maybe (m a)
zero (Katom a) = Nothing
zero (Kindet)  = Just (return Kindet)
-- zero (Kseq Kindet e2) = Just (return $ Kseq Kindet (Kafter e2))
zero (Kseq Kindet e2) = Just (return $ Kunseq [Kindet, Kafter e2])
-- zero (Kseq e1 Kindet) = Just (return $ Kseq (Kbefore e1) Kindet)
zero (Kseq e1 Kindet) = Just (return $ Kunseq [Kbefore e1, Kindet])
zero (Kseq e1 e2)     = case zero e1 of
                          Nothing   -> case zero e2 of
                                         Nothing   -> Nothing
                                         Just e2s' -> Just $ e2s' >>= \e2' -> return $ Kseq (Kbefore e1) e2'
                          Just e1s' -> Just $ e1s' >>= \e1' -> return $ Kseq e1' (Kafter e2)

zero (Kunseq es) =
  let _es' :: [Either Expr [Expr]] = map (\e -> case zero e of Just es' -> Right es'; Nothing -> Left e) es in
  if all isLeft _es' then Nothing
  else Just $ (sequence $ map (either (\e -> one e >>= return.snd) id) _es') >>= return . Kunseq
  where
    isLeft (Left _) = True
    isLeft _        = False




determinate :: Expr -> [Expr]
determinate e =
  case zero e of
    Nothing -> error "no indeterminate subexpression"
    Just es -> map three es


toGraph (Katom a)    = ([a],[])
toGraph Kindet       = (["f"],[])
toGraph (Kseq e1 e2) = let (as1,es1) = toGraph e1
                           (as2,es2) = toGraph e2 in
                       (as1 ++ as2, es1 ++ es2 ++ [ (x,y) | x <- as1, y <- as2 ])
toGraph (Kunseq es)  = foldl (\(as',es') (as,es) -> (as ++ as', es ++ es')) ([],[]) $ map toGraph es
toGraph (Kbefore e)  = toGraph e
toGraph (Kafter e)   = toGraph e

toDot n (as,es) = "digraph G" ++ (show n) ++ "{" ++ nodes ++ "; " ++ edges ++ "};\n"
  where
    nodes = intercalate "; " as
    edges = intercalate "; " $ map (\(x,y) -> x ++ " -> " ++ y) es

-- writeG n e = writeFile ("dots/" ++ show n ++ ".dot") $ toDot (toGraph e) n

writeG e fname = writeFile ("dots/" ++ fname ++ ".dot") $ concat $ map (uncurry toDot) $ zip [1..] (map (simpl . toGraph) $ determinate e)

-- mapM_ (uncurry writeG) $ zip [1..] (determinate e)






-- img :: Eq a => a -> [(a,] -> [a]
img _ []         = []
img z ((x, y) : es)
  | z == x       = y : img z es
  | otherwise    = img z es

-- isAccessible :: Eq a => [Edge a] -> a -> a -> Bool
isAccessible es x y = or $ f x y es []
  where
    f x y es acc = do
                    z  <- img x es
                    if elem z acc then
                      return False
                    else if z == y then
                      return True
                    else
                      f z y es (z:acc)


simpl (as,es) = (as,filter f es)
  where
    f e@((x, y)) = not $ isAccessible (delete e es) x y




{-

^{A}; ^{B}; ^{C} || ^{X; Y}; [f]; v{Z} --> ^{A; B; C || X; Y} || [f] || v{Z}
^{A}; ^{B}; v{C} || ^{X; Y}; [f]; v{Z}
^{A}; v{B}; v{C} || ^{X; Y}; [f]; v{Z}
v{A}; v{B;    C} || ^{X; Y}; [f]; v{Z}
-}


testX = Kseq (Kunseq [Katom "A", Katom "B"]) (Kindet)


-- X; [f]; Y
testA = Kseq (Katom "X") (Kseq Kindet (Katom "Y"))

-- (A || B); [f]; C
testB = Kseq (Kunseq [Katom "A", Katom "B"]) (Kseq Kindet (Katom "C"))



-- A; B; C || X; Y; [f]; Z
testC = Kunseq [test1, Kseq (Kseq (Katom "X") (Katom "Y")) (Kseq Kindet (Katom "Z"))]



test1 = Kseq (Katom "A") (Kseq (Katom "B") (Katom "C"))

test2 = Kseq (Kseq (Katom "A") (Katom "B")) (Katom "C")


test3 = Kseq (Katom "A") (Kseq (Kunseq [Katom "B", Katom "C"]) (Katom "D"))

-- A; (B || C; D) || [f]; G; (H || I)
test4 = Kunseq [Kseq (Katom "A") (Kunseq [Katom "B", Kseq (Katom "C") (Katom "D")]), Kseq Kindet (Kseq (Katom "G") (Kunseq [Katom "H", Katom "I"]))]




