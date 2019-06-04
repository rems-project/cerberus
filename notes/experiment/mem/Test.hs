import Memory

import qualified Data.Map as M

state1 :: MemState
state1 = MemState {
  aidCounter= 0,
  sizeof= M.empty,
  effTypes= M.fromList [("a", Just (Array signedShort 4)), ("p", Just (Pointer noQualifiers signedInt))],
  
  tagDefinitions= M.empty,
  
  memWrites= [ ]
  }


{-
  short a1[4] = {10,20,30,40};
  int   *p = (int *)&a1;
  
  r1, r2, r3, r4 = a1[0], a1[1], a1[2], a1[3];
  
  r5, r6 = p[0], p[1];
-}
prog1 = do
  aPtr <- create (Array signedShort 4) "a"
  store (Array signedShort 4) aPtr (MVarray [MVinteger 10, MVinteger 20, MVinteger 30, MVinteger 40])
  
--  pPtr <- create (Pointer noQualifiers signedInt) "p"
--  store (Pointer noQualifiers signedInt) pPtr (MVpointer aPtr)
  
  r1 <- load signedShort (shift aPtr [(signedShort, 0)])
  r2 <- load signedShort (shift aPtr [(signedShort, 1)])
  r3 <- load signedShort (shift aPtr [(signedShort, 2)])
  r4 <- load signedShort (shift aPtr [(signedShort, 3)])

  r <- load (Array signedShort 4) aPtr
  
  r5 <- load signedInt (shift aPtr [(signedInt, 0)])
--  r6 <- load signedInt (shift aPtr [(signedInt, 1)])

--  return (r1, r2, r3, r4)
  return (r1, r2, r3, r4, r)



test :: Show a => MemM a -> IO ()
test act =
  either print (print.fst) $ runMem act state1



-- r5
r5Read :: MemRead
r5Read =
  MemRead 6 (PVobject "a" [(signedInt, 0)], signedInt)



-- =============================================================================


vs = [
  -- 10
  MVinteger 10,
  -- {10, 20}
  MVarray [MVinteger 10, MVinteger 20],
  -- (struct T1){.x= 10, .a {20,30}, .y= 40}
  MVstruct "T1" [("x", MVinteger 10), ("a", MVarray [MVinteger 20, MVinteger 30]), ("y", MVinteger 40)]
 ]



{-

OK:

getSubValue (vs!!0) [] [] == Nothing
getSubValue (vs!!0) [] [signedInt] == Just (Right (MVinteger 10))




KO:

getSubValue (vs!!0) [signedInt] [] == Just (Left [])

getSubValue (vs!!1) [signedInt] [] == "error: non exhaustive case"
-}


testGetSubValue =
     getSubValue (vs!!0) [] [signedInt] == Just (vs!!0)
  && getSubValue (vs!!0) [] []          == Nothing
  
  && getSubValue (vs!!1) []          [signedInt]            == Just (MVinteger 10)
  && getSubValue (vs!!1) [signedInt] [signedInt]            == Just (MVinteger 20)
  && getSubValue (vs!!1) []          [signedInt, signedInt] == Just (MVarray [MVinteger 10, MVinteger 20])
  
  && getSubValue (vs!!2) []                                [signedInt]                                  == Just (MVinteger 10)
  && getSubValue (vs!!2) [signedInt]                       [signedInt]                                  == Just (MVinteger 20)
  && getSubValue (vs!!2) [signedInt, signedInt]            [signedInt]                                  == Just (MVinteger 30)
  && getSubValue (vs!!2) [signedInt, signedInt, signedInt] [signedInt]                                  == Just (MVinteger 40)
  && getSubValue (vs!!2) [signedInt]                       [signedInt, signedInt]                       == Just (MVarray [MVinteger 20, MVinteger 30])
  && getSubValue (vs!!2) []                                [signedInt, signedInt, signedInt, signedInt] == Just (vs!!2)
