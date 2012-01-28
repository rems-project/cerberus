open AssocList
open Datatypes
open MetatheoryAtom

type __ = Obj.t

module EnvImpl = Make(AtomDT)(AtomSetImpl)

