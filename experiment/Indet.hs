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


instance Show Expr where
  show (Katom a)    = a
  show (Kindet)     = "[f]"
  show (Kseq e1 e2) = "(" ++ show e1 ++ "; " ++ show e2 ++ ")"
  show (Kunseq es)  = "(" ++ intercalate " || " (map show es) ++ ")"
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
  (ds, es') <- mapM one es >>= return.unzip
  return (if all (==B) ds then B else A, Kunseq es')


data M a
  = Modified a
  | Unmodified a
  deriving Show





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
                                                                           Modified e'   -> Modified e'
                                                                           Unmodified e' -> Modified e'
                                         (Unmodified _, Modified e2') -> case two (Kseq e1 e2') of
                                                                           Modified e'   -> Modified e'
                                                                           Unmodified e' -> Modified e'
                                         (Modified e1', Modified e2') -> case two (Kseq e1' e2') of
                                                                           Modified e'   -> Modified e'
                                                                           Unmodified e' -> Modified e'

-- TODO: this is silly
two (Kunseq es) =
  if any (\e' -> case e' of Modified _ -> True; Unmodified (Kunseq _) -> True; _ -> False) es'
    then case two (Kunseq $ let (bs, as, xs) = f es' ([],[],[]) in
                            (if null bs then [] else [Kbefore (Kunseq bs)]) ++
                            xs ++
                            (if null as then [] else [Kafter (Kunseq as)])) of
           Modified e'   -> Modified e'
           Unmodified e' -> Modified e'
    else Unmodified (Kunseq es)
  where
    es' = map two es
    f []       acc           = acc
    f (x : xs) (bs, as, xs') = case (case x of Modified x -> x; Unmodified x -> x) of
                                 Kunseq es -> f xs (bs, as, xs' ++ es)
                                 Kbefore e -> f xs (bs ++ [e], as, xs') -- YUCK
                                 Kafter e  -> f xs (bs, as ++ [e], xs') -- YUCK
                                 e         -> f xs (bs, as, xs' ++ [e]) -- YUCK

two e = Unmodified e


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

zero (Kseq Kindet e2) = Just (return $ Kseq Kindet (Kafter e2))
zero (Kseq e1 Kindet) = Just (return $ Kseq (Kbefore e1) Kindet)
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



{-

^{A}; ^{B}; ^{C} || ^{X; Y}; [f]; v{Z}
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

test4 = Kseq (Kunseq [Katom "A", Katom "B"]) (Kseq (Katom "C") (Katom "D"))


xs = map snd $ one test1
