{-# LANGUAGE RecordWildCards #-}
module Memory (
  module Mem.Types,
  module Mem.Ctype,
  
--  initialState,
--  initialStateWithTags,
--  runMem,
  
  module Memory
) where

import Control.Applicative

import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Identity

import Data.Maybe (fromJust, catMaybes)
import Data.List (unfoldr, (\\))
import Data.Map (Map)
import qualified Data.Map as M

import Mem.Types
import Mem.Ctype



initialState :: MemState
initialState =
  MemState 0 M.empty M.empty M.empty []

initialStateWithTags :: Map Symbol [(Symbol, Ctype)] -> MemState
initialStateWithTags defs =
  MemState 0 M.empty M.empty defs []

runMem :: MemM a -> MemState -> Either MemoryError (a, MemState)
runMem m =
  runIdentity . runErrorT . runStateT m







-- Split a given offset at the point corresponding to the
-- footprint of the given memory value.
-- 
-- Returns 'Nothing' of the offset was too small to cover the
-- footprint of the memory value
offsetSplitAt :: Offset -> MemValue -> Maybe (Offset, Offset)
offsetSplitAt (ty:fp) (MVunspecified ty') | ty == ty' =
  return ([ty], fp)
offsetSplitAt (ty:fp) (MVinteger _) =
  return ([ty], fp)
offsetSplitAt (ty@(Pointer _ _):fp) (MVpointer _) =
  return ([ty], fp)
offsetSplitAt fp (MVarray vs) =
  foldM (\(acc,xs) v -> do
    (ys,zs) <- offsetSplitAt xs v
    return (acc ++ ys, zs)
   ) ([], fp) vs
offsetSplitAt fp (MVstruct _ xs) =
  foldM (\(acc,xs) (_, v) -> do
    (ys,zs) <- offsetSplitAt xs v
    return (acc ++ ys, zs)
   ) ([], fp) xs
offsetSplitAt fp (MVunion _ _ v) =
  offsetSplitAt fp v
offsetSplitAt _ _ =
  Nothing

fpMatches fp val = 
  case offsetSplitAt fp val of
    Just (_, []) ->
      True
    _ ->
      False




-- not allowing byte access for now
getSubValueAux :: MemValue -> Offset -> Footprint -> Maybe (Either Offset MemValue)
getSubValueAux val@(MVunspecified ty) [] [ty'] | ty == ty' =
  Just (Right val)

getSubValueAux val@(MVinteger _) [] [_] =
  Just (Right val)

getSubValueAux val@(MVpointer _) [] [Pointer _ _] =
  Just (Right val)

-- only allowing single and complete elem of an array to be a subvalue
getSubValueAux val@(MVarray vs) off fp =
  case off of
    [] ->
      if fp `fpMatches` val then
        Just (Right val)
       else
         aux vs off
    _ ->
      aux vs off
  where
    aux [] offAcc =
      Just (Left offAcc)
    aux (v:vs') offAcc =
      case getSubValueAux v offAcc fp of
        Just (Left offAcc') ->
          aux vs' offAcc'
        Just (Right v') ->
          Just (Right v')
        Nothing ->
          Nothing -- error $ "AA: " ++ show (v, off, fp) -- Nothing

getSubValueAux val@(MVstruct _ xs) off fp =
  case off of
    [] ->
      if fp `fpMatches` val then
        Just (Right val)
       else
         aux xs off
    _ ->
      aux xs off
  where
    aux [] offAcc =
      Just (Left offAcc)
    aux ((_, v):xs') offAcc =
      case getSubValueAux v offAcc fp of
        Just (Left offAcc') ->
          aux xs' offAcc'
        Just (Right v') ->
          Just (Right v')
        Nothing ->
          Nothing -- error $ "BB: " ++ show (v, off, fp) -- Nothing

getSubValueAux (MVunion _ _ val) off fp =
  getSubValueAux val off fp

getSubValueAux v off fp =
  case offsetSplitAt off v of
    Just (_, off') ->
      Just (Left off')
    _ ->
      Nothing


getSubValue val off fp =
  case getSubValueAux val off fp of
    Just (Right val') ->
      Just val'
    _ ->
      Nothing



unfoldCtypes :: TagDefinitions -> [Ctype] -> [Ctype]
unfoldCtypes _ [] =
  []

unfoldCtypes tagDefs (Array ty n : sh) =
  concatMap (replicate n) xs ++ ys
  where
    xs = unfoldCtypes tagDefs [ty]
    ys = unfoldCtypes tagDefs sh

unfoldCtypes tagDefs (Struct tag : sh) =
  xs ++ ys
  where
    idTys = fromJust $ M.lookup tag tagDefs
    xs    = unfoldCtypes tagDefs (map snd idTys)
    ys    = unfoldCtypes tagDefs sh

unfoldCtypes tagDefs (ty : sh) =
  ty : unfoldCtypes tagDefs sh


offsetFromShift :: TagDefinitions -> PointerShift -> Offset
offsetFromShift tagDefs =
  unfoldCtypes tagDefs . (unfoldr aux)
  where
    aux [] =
      Nothing
    aux ((_, 0) : sh') =
      aux sh'
    aux sh@((ty, n) : sh') =
      if n > 0 then
        Just (ty, (ty, n-1) : sh')
       else
        error $ "[Memory.offsetFromShift] found a negative shift: " ++ show sh


{-
footprintOfCtype :: TagDefinitions -> Ctype -> Footprint
footprintOfCtype tagDefs =
  unfoldCtypes tagDefs . (:[])



offsetFootprintOfRead :: TagDefinitions -> MemRead -> (Offset, Footprint)
offsetFootprintOfRead tagDefs (MemRead _ (PVobject _ sh, ty)) =
  (offsetFromShift tagDefs sh, footprintOfCtype tagDefs ty)
-}

























-- maybe effectfull?
shift :: PointerValue -> PointerShift -> PointerValue
shift (PVobject aid sh) sh' =
  PVobject aid (sh ++ sh')


-- deref :: MemValue -> PointerValue






create :: Ctype -> String -> MemM PointerValue
create ty name = do
  st <- get
  put st{ effTypes= M.insert oid (Just ty) (effTypes st) }
  return $ PVobject oid []
  where
    oid = name




store :: Ctype -> PointerValue -> MemValue -> MemM ()
store ty ptrVal val = do
--  checkValue ty val
  st <- get
  -- TODO: footprint
  put st{aidCounter= aidCounter st + 1, memWrites= MemWrite (aidCounter st) (ptrVal, ty, val) : memWrites st}


load :: Ctype -> PointerValue -> MemM MemValue
load ty ptrVal = do
  st <- get
  let aid = aidCounter st
  -- TODO: footprint
  put st{aidCounter= aid + 1}
  combineWrites (MemRead aid (ptrVal, ty)) (memWrites st)









getTagDeclaration :: Symbol -> MemM [(Symbol, Ctype)]
getTagDeclaration tag =
  get >>= \st ->
  case M.lookup tag $ tagDefinitions st of
    Nothing ->
      throwError $ MerrOther ("[getTagDeclaration] struct/union type '" ++
                              tag ++ "' is not declared")
    Just defs ->
      return defs



-- build a pointer shift to "one past" the footprint of a given type
mkShiftToEnd :: Ctype -> MemM PointerShift
mkShiftToEnd (Array ty n) =
  replicateM n (mkShiftToEnd ty) >>= return.concat
mkShiftToEnd (Struct tag) = do
  idTys <- getTagDeclaration tag
  concat <$> mapM (mkShiftToEnd.snd) idTys
mkShiftToEnd ty =
  return [(ty, 1)]




getAffection (MemRead _ (PVobject oid1 rSh, rTy)) (MemWrite _ (PVobject oid2 wSh, wTy, wVal))
  | oid1 /= oid2  =
      return Nothing
  | otherwise = do
      MemState{..} <- get
      let rOffset = offsetFromShift tagDefinitions rSh
      rFootprint <- offsetFromShift tagDefinitions <$> mkShiftToEnd rTy
      let wOffset = offsetFromShift tagDefinitions wSh
      wFootprint <- offsetFromShift tagDefinitions <$> mkShiftToEnd wTy
      
      return $ decider (rOffset, rFootprint) (wOffset, wFootprint) wVal


foo :: Eq a => [a] -> [a] -> Maybe (Either [a] [a])
foo [] ys         = Just (Right ys)
foo xs []         = Just (Left  xs)
foo (x:xs) (y:ys)
  | x == y        = foo xs ys
  | otherwise     = Nothing



decider (rOffset, rFootprint) (wOffset, wFootprint)  wVal =
  case foo rOffset wOffset of
    Nothing ->
      -- some type in the read / write offsets didn't match
      error "type problem"
    
    Just (Left rOffset') ->
      -- the read offset is larger than that of the write
      case foo rOffset' wFootprint of
        Just (Right xs) | not (null xs) ->
          Just (rOffset', rFootprint, wVal)
        _ ->
          Nothing
      
    Just (Right wOffset') ->
      -- the read offset is shorter than that of the write
      case foo rFootprint wOffset' of
        Nothing ->
          error "type problem"
        Just (Left rFootprint') ->
          Just ([], rFootprint', wVal)
          
        Just (Right _) ->
          -- the read footprint ends before that of the write
          Nothing



combineWrites :: MemRead -> [MemWrite] -> MemM MemValue
combineWrites r@(MemRead _ (PVobject _ rSh, rTy)) ws = do
  xs <- catMaybes <$> mapM (getAffection r) ws
  case xs of
    [] ->
      throwError $ MerrOther ("myCombineWrites: uninit ==> " ++ show (r, ws))
    _ -> do
      unV     <- mkUnspec rTy
      tagDefs <- get >>= return.tagDefinitions
      
      let rOff = offsetFromShift tagDefs rSh
      
      -- TODO: may need a reverse of xs
      foldM (\acc (wOff, wFp, wVal) ->
--        case getValue wVal wFp of
        case getSubValue wVal wOff wFp of
          Nothing ->
            throwError $ MerrOther ("myCombineWrites: some footprint was too big")
          Just val ->
            return $ setValue tagDefs acc (wOff \\ rOff) val
       ) unV xs





-- build an unspecified value of a given type
mkUnspec :: Ctype -> MemM MemValue
mkUnspec ty@(Basic _) =
  return $ MVunspecified ty
mkUnspec (Array ty n) =
  MVarray <$> replicateM n (mkUnspec ty)
mkUnspec ty@(Pointer _ _) =
  return $ MVunspecified ty
mkUnspec ty@(Atomic _) =
  return $ MVunspecified ty
mkUnspec (Struct tag) = do
  st <- get
  case M.lookup tag (tagDefinitions st) of
    Nothing ->
      throwError $ MErrInternal ("[mkUnspecs] no such struct: `" ++ tag ++ "'")
    Just idTys -> do
      MVstruct tag <$> mapM (\(id, ty) -> mkUnspec ty >>= \v -> return (id, v)) idTys
mkUnspec ty@(Union _) =
  return $ MVunspecified ty
mkUnspec ty@(Builtin _) =
  return $ MVunspecified ty
mkUnspec _ =
  throwError $ MErrInternal "[mkUnspecs] invalid type"








-- either build a memory value setter at the given shift and of the given
-- footprint, returns the excess shift
-- setValue :: Map Symbol [(Symbol, Ctype)] -> MemValue -> [Ctype] -> [Ctype] -> MemValue -> -- Either (MemValue -> MemValue) [Ctype]
setValue tagDefs (MVarray vs) [] val@(MVarray vs') =
  if length vs == length vs' then
    val
   else
    MVarray $ vs' ++ drop (length vs') vs

-- TODO: (for now) not doing the fancy thing for stores of a struct value, that would
--       work inside an array (e.g. struct {int,int} inside int[n>=2])
setValue tagDefs (MVarray (_:vs)) [] v =
  MVarray (v:vs)


setValue _ (MVunspecified _) [] v' =
  v' -- TODO: maybe check that v' match the footprint of the type of the unspec value

setValue _ v off v' =
  error $ "setValue(WIP): " ++ show (v, off, v')