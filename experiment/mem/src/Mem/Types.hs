module Mem.Types where

import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Identity

import Data.Map (Map)
import qualified Data.Map as M

import Mem.Ctype


type Symbol
  = String




-- TODO: peter doesn't like these
type ObjectId
  = String




type Offset
  = [Ctype] -- TODO: protection

type Footprint
  = [Ctype] -- TODO: protection




type PointerShift
  = [(Ctype, Int)]




data PointerValue
  = PVnull Ctype
  | PVobject ObjectId PointerShift
--  | PVfunction Symbol
  deriving (Eq, Show)


data MemValue
  = MVunspecified Ctype -- this should only be used for base and union types
  | MVinteger Int
  | MVpointer PointerValue
  | MVarray [MemValue]
  | MVstruct Symbol [(Symbol, MemValue)]
  | MVunion Symbol Symbol MemValue -- the symbols are respectively the tag and the member
--MVbyte Int MemValue -- some byte of a memvalue (should only be: MVunspecified, MVinteger or MVpointer)
  deriving (Show, Eq)



type ActionId
  = Int

data MemWrite
  = MemWrite ActionId (PointerValue, Ctype, MemValue)
  deriving (Show, Eq)

data MemRead
  = MemRead ActionId (PointerValue, Ctype)
  deriving (Show, Eq)


type TagDefinitions
  = Map Symbol [(Symbol, Ctype)]

data MemState = MemState {
  aidCounter     :: Int,
  sizeof         :: Map Ctype Int, -- partial information about the impl-defined sizeof
  effTypes       :: Map ObjectId (Maybe Ctype),
  tagDefinitions :: TagDefinitions,
  memWrites      :: [MemWrite]
} deriving Show


data MemoryError
  = MerrUnitialised MemRead
  | MErrTyping String
  | MErrNotYetSupported String
  | MErrInternal String
  | MerrOther String

instance Show MemoryError where
  show (MerrUnitialised r) =
    "MerrUnitialied: " ++ show r
  show (MErrTyping str) =
    "MErrType: " ++ show str
  show (MErrNotYetSupported str) =
    "MErrNotYetSupported: " ++ show str
  show (MErrInternal str) =
    "MErrInternal: \"" ++ str ++ "\""
  show (MerrOther str) = 
    "MerrOther: \"" ++ str ++ "\""

instance Error MemoryError where
  strMsg str = MerrOther str

type MemM = StateT MemState (ErrorT MemoryError Identity)
