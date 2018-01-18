module Mem.Ctype {- (
  Ctype(..),
  Qualifiers(..),
  noQualifiers,
  isIntegerType,
  signedInt,
  signedShort
) -} where


-- import Text.PrettyPrint.GenericPretty


type Identifier
  = String


data IntegerBaseType
  = Ichar
  | Short
  | Int_
  | Long
  | LongLong
  | IBBuiltin String
  deriving (Eq, Ord, Show)


data IntegerType
  = Char
  | Bool
  | Signed   IntegerBaseType
  | Unsigned IntegerBaseType
  | IBuiltin String
  | Enum Identifier
  deriving (Eq, Ord, Show)


data BasicType
  = Integer IntegerType
  deriving (Eq, Ord, Show)


data Ctype
  = Void -- TODO: not needed by the MLM ?
  | Basic BasicType
  | Array Ctype Int
  | Function Ctype [(Qualifiers, Ctype)] Bool
  | Pointer Qualifiers Ctype
  | Atomic Ctype
  | Struct Identifier
  | Union  Identifier
  | Builtin String
  deriving (Eq, Ord, Show)




data Qualifiers = Qualifiers {
  const    :: Bool,
  restrict :: Bool,
  volatile :: Bool,
  atomic   :: Bool
} deriving (Eq, Ord, Show)


noQualifiers :: Qualifiers
noQualifiers =
  Qualifiers False False False False



isIntegerType :: Ctype -> Bool
isIntegerType (Basic (Integer _)) =
  True
isIntegerType (Atomic ty) =
  isIntegerType ty
-- TODO: Builtin
isIntegerType _ =
  False






signedInt :: Ctype
signedInt =
  Basic (Integer (Signed Int_))

signedShort :: Ctype
signedShort =
  Basic (Integer (Signed Short))


-- TODO: something for union
isAggregate (Struct _)  = True
isAggregate (Array _ _) = True
isAggregate _           = False



{-
instance Show IntegerBaseType where
  show Ichar           = "ichar"
  show Short           = "short"
  show Int_            = "int"
  show Long            = "long"
  show LongLong        = "longlong"
  show (IBBuiltin str) = str
-}


{-
instance Show IntegerType where
  show Char            = "char"
  show Bool            = "_Bool"
  show (Signed ibty)   = "signed_" ++ show ibty
  show (Unsigned ibty) = "unsigned_" ++ show ibty
  show (IBuiltin str)  = str
  show (Enum tag)      = "enum " ++ tag
-}


{-
instance Show BasicType where
  show (Integer ity) = show ity
-}



{-
showCtypeAux :: Ctype -> String
showCtypeAux Void =
  "void"
showCtypeAux (Basic bty) =
  show bty
showCtypeAux (Array ty n) =
  showCtypeAux ty ++ "[" ++ show n ++ "]"
showCtypeAux (Function ty xs b) =
  -- TODO
  "FUNCTIONTYPE"
showCtypeAux (Pointer qs ty) =
  "ptr(" ++ show qs ++ ", " ++ showCtypeAux ty ++ ")"
showCtypeAux (Atomic ty) =
  "_Atomic(" ++ show ty ++ ")"
showCtypeAux (Struct tag) =
  "struct " ++ tag
showCtypeAux (Union tag) =
  "union " ++ tag
showCtypeAux (Builtin str) =
  str


instance Show Ctype where
  show ty = "\"" ++ showCtypeAux ty ++ "\""
-}