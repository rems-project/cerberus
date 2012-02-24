{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances,
             FlexibleInstances #-}
import Prelude hiding ((||))
import qualified Data.Map as M
import qualified Data.List as L

import Control.Monad.State

-- import Ail

-- THIS PART IS NOT USED FOR NOW. SEE AFTER THE LINE.

{-
-- Memory model
data Content
  = Val Integer
  | Trap
  | Undet


-- type Value   = Integer
type Address = Integer

-- Trace
data Action
  = Create
  | Kill
  | Load
  | Store

type Trace = [Action]


-- tentative syntax for Core (to discuss)
data Ty
  = SignedInt
  | UnsignedInt -- TODO (...)

data CoreSyn a
  = Kskip
  | Kfail
  | Kconst Integer
  | Klet a (CoreSyn a) (CoreSyn a)
{-  | Kseq (CoreSyn a) (CoreSyn a) -- is already in Let, but what about the names? -}
  | Kif (Formula a) (CoreSyn a) (CoreSyn a)
  | Kcreate Ty                               -- Create a new memory object
  | Kkill a                                  -- Destroy a memory object
  | Kstore Ty a Integer                      -- 
  | Kload Ty a                               -- 
  | Ksame -- TODO

-- Core expression (pure)
data CoreExpr a
  = Econst Value
  | Eident a
  | Eop CoreOp [CoreExpr a]
  | Emax Ty
  | Emin Ty

data CoreOp
  = OpPlus | OpMinus
  | OpMult | OpDiv


data Formula a
  = Ftrue
  | Ffalse
  | Feq a a
  | Flt a a
  | Fand (Formula a) (Formula a)
  | For (Formula a) (Formula a)
  | Fnot (Formula a)

type Constaint a = [(CoreExpr a, CoreExpr a)]
-}

{-
(JUST SOME HAND TESTS)


int main(void) {
  int x, y = 0;
  
  x = y + 1;
  return 0;
}

----------------------------------------

(a1, a2) <- create {signed int} || create {signed int};
            if (min{signed int} <= 0 <= max{signed int}) {
                         store {signed int} a2 0;
              (n1,n2) <- load {signed int} a2 || 1;
                         if (min{signed int} <= n1 + n2 <= max{signed int}) {
                           store {signed int} (n1 + n2);
                         } else {
                           fail
                         }
            } else {
              fail
            };
            0

========================================
int main(void) {
  int x = 42;
  unsigned char c = *(unsigned char *)(&x);
  return c;
}

----------------------------------------
a1 <- create{signed int};
      if (min{signed int} <= 0 <= max{signed int}) {
        store{signed int} a1 0
      } else {
        fail
      };
a2 <- create{unsigned char};
      


========================================
int fact(int x) {
  int ret = 1;
  while (x--) {
    ret *= x;
  };
  return ret;
}

----------------------------------------

a <- create {signed int};
     store {signed int} a 1;
     fix {
       n1 <- load {signed int} x;
             store {signed int} x (n1 + 1);
             if (n /= 0) {
               (n2, n3) <- load {signed int} a || load {signed int} x;
                           if (min{signed int} <= n2 * n3 <= max{signed int}) {
                             store {signed int} a (n2 * n3)
                           } else {
                             fail
                           };
                           
             } else {
               skip
             }
     }

-}

{- START OF THE WORKING BIT ================================================= -}

type Object = String
type Value  = Integer

data Expr a b
  = Eskip
  | Efail
  | Econst b
  | Eident a
  | Eassign a (Expr a b)
  | Eplus (Expr a b) (Expr a b)
  | Eneg (Expr a b)
  | Eseq (Expr a b) (Expr a b)
  deriving Show


data TraceAction
  = Load Object Value  -- R[x] -> n
  | Store Object Value -- W[x] := n
type Trace = [TraceAction]


-- example codes
ex1, ex2 :: Expr Object Value

-- x = 0; x + (x = 1)
ex1 = Eseq (Eassign "x" (Econst 0))
           (Eplus (Eident "x") (Eassign "x" (Econst 1)))

-- x = 0; x + (x = 1; x = 2; 0)
ex2 = Eseq (Eassign "x" (Econst 0))
           (Eplus (Eident "x")
                  (Eseq (Eassign "x" (Econst 1))
                        (Eseq (Eassign "x" (Econst 2))
                              (Econst 0))))


{- Memory representation #################################################### -}
class Memory mem where
  initial :: mem                           -- Initial memory state
  load    :: Object -> mem -> Value        -- Load the value of an object
  store   :: Object -> Value -> mem -> mem -- Store a value in an object


{- Actions sequencing #######################################################
   ########################################################################## -}

class (Memory mem, MonadState mem seq) => Sequencing seq mem where
  (+|+) :: seq a -> seq a -> seq a     -- nondeterministic composition
  (||)  :: seq a -> seq b -> seq (a,b) -- parallel composition
  seqPt :: seq ()                      -- sequence point


{- Dynamics #################################################################
   ########################################################################## -}
-- class Sequencing seq mem => Dynamics dyn seq mem where
--  runD  :: dyn seq mem a -> seq a
--  stepD :: seq a -> dyn seq mem a




-- Abstract memory representation
newtype AbstractMem = AMem (M.Map Object Value) deriving Show

instance Memory AbstractMem where
  initial = AMem M.empty
  load x (AMem s) = case M.lookup x s of
                      Just n -> n
                      Nothing -> error ("Assignable " ++ x ++
                                        " has not been initialized.")
  store x n (AMem s) = AMem $ M.insert x n s






-- Compute all the possible final values
type M1 mem = StateT mem []

instance Memory mem => Sequencing (M1 mem) mem where
  (StateT a) +|+ (StateT b) = StateT (\s -> a s ++ b s)
  a          ||  b          = (a >>= \va -> b >>= \vb -> return (va, vb)) +|+
                              (b >>= \vb -> a >>= \va -> return (va, vb))
  seqPt   = return ()


-- Compute all the execution traces
-- type M2 mem = TODO


{- ########################################################################## -}
-- sem :: (Memory mem, Sequencing (seq mem') mem, mem ~ mem') => CoreSyn Object Value -> (seq mem') Value
{-
  TODO: the type of [sem] should be parametric on the Sequencing monad, but
        currently GHC don't like it.
-}
sem :: Memory mem => Expr Object Value -> M1 mem Value
-- sem Eskip = return ()
sem (Econst n) =
  return n
sem (Eident x) = do
  s <- get
  return $ load x s
sem (Eassign x e) = do
  n <- sem e
  s <- get
  put (store x n s)
  return n
sem (Eplus e1 e2) = do
  (n1, n2) <- sem e1 || sem e2
  return $ n1 + n2
sem (Eneg e) = do
  n <- sem e
  return $ -n
sem (Eseq e1 e2) = do
  sem e1
  sem e2


-- x := 12; y := 10; tmp := y; y := x; x := tmp
swap :: Expr Object Value
swap = Eseq (Eassign "x" (Econst 12))
            (Eseq (Eassign "y" (Econst 10))
                  (Eseq (Eassign "tmp" (Eident "y"))
                        (Eseq (Eassign "y" (Eident "x"))
                              (Eassign "x" (Eident "tmp")))))

uninitLoad :: Expr Object Value
uninitLoad = Eident "x"

{-
Sample run:
  *Main> runStateT (sem ex1) (initial :: AbstractMem)
-}
