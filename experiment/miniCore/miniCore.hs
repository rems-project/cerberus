import Prelude hiding ((||))
import Control.Monad
import Control.Applicative hiding ((<|>))
import Data.List
import Data.Char

import System.Console.Haskeline
import System.Console.Haskeline.IO -- TODO: find how to get rid of that
import Control.Exception

import System.Environment
import System.Process

import Text.Parsec
import qualified Text.Parsec.Token as T
import Text.Parsec.Language
import Text.Parsec.Expr

-- don't know how to rename just one function of a module
(\/) a b = if a then True else b



{- Directed graphs with "environments" ----------------------------------------}

-- (UI hack) uses to remember from where an edge come from
data Kind
  = Syntax      -- from the sequenced composition
  | SyntaxTrans -- by transitivity as a result of sequenced composition alone
  | Indet       -- from an indeterminate choice
  | IndetTrans  -- by transitivity after addition of the indeterminate choices
  deriving (Eq, Show)

data Edge a = Edge a a Kind

instance Eq a => Eq (Edge a) where
  (Edge a b _) == (Edge a' b' _) = a==a' && b==b'

instance Show a => Show (Edge a) where
  show (Edge a b _) = show (a,b)


data G a = G {
  vertices :: [a],
  edges    :: [Edge a],
  calls    :: [a]       -- function calls accountered so far
} deriving (Eq, Show)




-- [collectVertices es] retrieve the list of vertices associated to
--                      the edge-map [es]
collectVertices :: [Edge a] -> [a]
collectVertices es = f [] es
  where
    f acc []                = acc
    f acc (Edge a b _ : es) = f (a:b:acc) es


-- [fromEdges es] builds the graph (collectVertices es, e)
fromEdges :: Eq a => [Edge a] -> G a
fromEdges es = G (nub $ collectVertices es) es [] -- nub removes duplicates

-- [lookups x r] = { y | (x,y,_) IN r }
img :: Eq a => a -> [Edge a] -> [a]
img _ []         = []
img x (Edge a b _:rs)
  | x == a       = b : img x rs
  | otherwise    = img x rs


-- [isAccessible r x y] = True iff there is a path from x to y in r (irreflexive).
isAccessible :: Eq a => [Edge a] -> a -> a -> Bool
isAccessible r x y = or $ f x y r []
  where
    f x y r acc = do
                    z  <- img x r       -- for any z such that (x,z) IN r:
                    if elem z acc then  -- if z has already been visited,
                      return False      -- then abort the currrent branch.
                    else if z == y then -- Otherwise, if z = y,
                      return True       -- then we are done.
                    else                -- Otherwise, remember z and look for
                      f z y r (z:acc)   -- a path from z to y.

-- note that this one is reflexive
connected :: Eq a => [Edge a] -> a -> a -> Bool
connected r x y = (x == y) \/ isAccessible r x y \/ isAccessible r y x

unreachablesFrom :: Eq a => a -> [a] -> [Edge a] -> [a]
unreachablesFrom x vs es = filter (not . connected es x) vs

-- close by transitivity the edge relation of a graph.
transitiveClosure :: Eq a => Kind -> G a -> G a
transitiveClosure k (G vs es cvs) =
  let es' = es ++ [ Edge x y k | x <- vs, y <- vs,
                                 x/=y, isAccessible es x y, not(elem (Edge x y undefined) es) ] in
  G vs es' cvs

close :: Eq a => [Edge a] -> [Edge a]
close = edges . transitiveClosure IndetTrans . fromEdges


-- remove syntax edges implied by transitivity
-- HIGHLY non-efficient algorithm
simpl :: Eq a => [Edge a] -> [Edge a]
simpl es = filter f es
  where
    f e@(Edge x y Syntax) = not $ isAccessible (delete e es) x y
    f _                   = True

-- generate a graphviz representation of a given graph.
-- REMARK: doesn't take a graph of type G as input.
toDot n es =
  "subgraph cluster_" ++ (show n) ++ "{style=filled;color=" ++ boxColour ++
  ";label=\"order n°" ++ (show n) ++ "\";" ++ printV vs ++ printE (simpl es) ++ "}"
  where
    vs = collectVertices (simpl es)
    -- print a vertex (salmond if it is a function call, white otherwise)
    printV vs = foldl (\s v -> s ++ show (v ++ (show n)) ++ "[label=" ++ (show v) ++
                (if all (not.isUpper) v then "color=salmon" else "") ++ "];") "" vs
    -- print a edge with the colour corresponding to its "kind"
    printE es = foldl (\s (Edge x y k) -> s ++ show (x ++ (show n)) ++ " -> " ++
                show (y ++ (show n)) ++ (style k) ++ ";") "" es
    style Syntax      = ""
    style SyntaxTrans = "[style=dashed]"
    style Indet       = "[color=red]"
    style IndetTrans  = "[color=salmon,style=dashed]"
    -- paint the background of the order yellow if there is a cycle
    boxColour = if any (\v -> isAccessible es v v) vs then "yellow" else "lightgrey"



{- MiniCore -------------------------------------------------------------------}
data CoreSyn
  = Atom String         -- base action
  | Seq CoreSyn CoreSyn -- sequenced composition
  | Par CoreSyn CoreSyn -- unsequenced composition
  | Call String         -- function call (indeterminately sequenced
  deriving Show

(||) :: CoreSyn -> CoreSyn -> CoreSyn
a || b = Par a b

(|>) :: CoreSyn -> CoreSyn -> CoreSyn
a |> b = Seq a b


-- PARSING ---------------------------------------------------------------------
miniCoreParser = whiteSpace >> expr <* eof

expr = buildExpressionParser opTable term
term = parens expr <|> (call <?> "function call") <|> (atom <?> "atom")
  where
    atom = do id <- identifier
              if all (not.isLower) id then
                return $ Atom id
              else fail "atom names cannot contain lowercases"
    call = do id <- squares identifier
              if all (not.isUpper) id then
                return $ Call id
              else fail "call names cannot contain uppercases"
opTable = [ [binary ";" (|>) AssocLeft], [binary "||" (||) AssocLeft] ]
  where
    binary name fun assoc = Infix (do reservedOp name; return fun) assoc

lexer = T.makeTokenParser emptyDef

whiteSpace = T.whiteSpace lexer
identifier = T.identifier lexer
parens     = T.parens lexer
squares    = T.squares lexer
reservedOp = T.reservedOp lexer



-- Graph semantics from MiniCore------------------------------------------------
sem1 :: CoreSyn -> G String
sem1 (Atom a)  = G [a] [] []
sem1 (Seq a b) =
  let G va ea cva = sem1 a
      G vb eb cvb = sem1 b in
  G (va++vb)
    -- the actions of [a] are sequenced before those of [b].
    (ea++eb ++ [ Edge x y Syntax | x <- va, y <- vb ]) -- TODO: bad annotation for edges coming by
                                                       -- transitivity from the syntax.
    (cva++cvb)
sem1 (Par a b) =
  let G va ea cva = sem1 a
      G vb eb cvb = sem1 b in
  G (va++vb) (ea++eb) (cva++cvb)
sem1 (Call a) = G [a] [] [a]


-- TODO: maybe make it monadic again when extending to the full Core with state
--       and such.
connectCall :: Eq a => a -> [a] -> [Edge a] -> [[Edge a]]
connectCall c vs es = foldM tryBoth es vs
  where
    tryEdge es x y = if isAccessible es y x then [] else [Edge x y Indet : es]
    tryBoth es v   = tryEdge es v c ++ tryEdge es c v

sem2 :: Eq a => G a -> [[Edge a]]
sem2 (G vs es cvs) =
  -- for each call [c]:
  --   for each action [v] not already sb-related to [c]:
  foldM (\es c -> [close (es `union` es') | es' <- connect c es]) es cvs
  where
    connect c es = connectCall c (unreachablesFrom c vs es) es

sem :: CoreSyn -> [[Edge String]]
sem = sem2 . sem1

-- Some tests ------------------------------------------------------------------
f1    = ((Call "f" || Atom "A") |> Atom "B") || Atom "C"
f2    = Call "f" || (Atom "A" |> Atom "B") || Atom "C"
test1 = (Atom "A" || Atom "B") |> (Atom "C" || Atom "D")
test2 = Atom "A" |> (Atom "B" || Atom "C") |> Atom "D"


main :: IO ()
main = bracketOnError (initializeInput defaultSettings)
            cancelInput
            (\hd -> start hd >> closeInput hd)
  where
    filename = "sb.dot"
    start, loop :: InputState -> IO ()
    start hd = do
               args <- getArgs
               case args of
                 []         -> loop hd
                 [filename] -> do
                               input <- readFile filename
                               process hd $ Just input
                 _          -> putStrLn "USAGE: miniCore <filename> \n       miniCore"

    loop hd = do
             input <- queryInput hd $ getInputLine "[^C to quit]> "
             process hd input
             loop hd
    process hd Nothing      = return ()
    process hd (Just input) = case parse miniCoreParser "" input of
                                Left err -> queryInput hd $ outputStrLn $ "\x1b[31m" ++ show err ++ "\x1b[0m"
                                Right e  -> do writeFile filename "digraph G{node[style=filled,color=white];"
                                               mapM_ (\(n,g) -> appendFile filename $ toDot n g) $ zip [1..] (sem e)
                                               appendFile filename "}"
                                               readProcess "./run" [] []
                                               queryInput hd $ outputStrLn "\x1b[32mdone.\x1b[0m\n"
