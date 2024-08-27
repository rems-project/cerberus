module History = struct
  let str = "allocs"

  let sym = Sym.fresh_named str

  let loc = Locations.other __MODULE__

  let value_bt =
    BaseTypes.Record
      [ (Id.id "base", Memory.uintptr_bt); (Id.id "size", Memory.uintptr_bt) ]


  let bt = BaseTypes.Map (Alloc_id, value_bt)

  let sbt = SurfaceBaseTypes.of_basetype bt
end

module Predicate = struct
  let str = "Alloc"

  let loc = Locations.other __MODULE__

  let sym = Sym.fresh_named str

  let pred_name = ResourceTypes.PName sym

  let make pointer : ResourceTypes.predicate_type =
    { name = pred_name; pointer; iargs = [] }


  let def : ResourcePredicates.definition =
    { loc = Locations.other (__FILE__ ^ ":" ^ string_of_int __LINE__);
      pointer = Sym.fresh_named "ptr";
      iargs = [];
      oarg_bt = History.value_bt;
      clauses = None
    }
end
