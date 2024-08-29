module History = struct
  let str = "allocs"

  let sym = Sym.fresh_named str

  let loc = Locations.other __MODULE__

  let base_id = Id.id "base"

  let base_bt = Memory.uintptr_bt

  let size_id = Id.id "size"

  let size_bt = Memory.uintptr_bt

  let value_bt = BaseTypes.Record [ (base_id, base_bt); (size_id, size_bt) ]

  let make_value ~base ~size loc' =
    IndexTerms.(
      record_ [ (base_id, base); (size_id, num_lit_ (Z.of_int size) size_bt loc') ] loc')


  let bt = BaseTypes.Map (Alloc_id, value_bt)

  let it = IndexTerms.sym_ (sym, bt, loc)

  let lookup_ptr ptr loc' =
    assert (BaseTypes.(equal (IndexTerms.bt ptr) Loc));
    IndexTerms.(map_get_ it (allocId_ ptr loc') loc')


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
