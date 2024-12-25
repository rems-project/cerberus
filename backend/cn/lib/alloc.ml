module History = struct
  let str = "allocs"

  let sym = Sym.fresh_named str

  let base_id = Id.id "base"

  let base_bt = Memory.uintptr_bt

  let size_id = Id.id "size"

  let size_bt = Memory.uintptr_bt

  let value_bt = BaseTypes.Record [ (base_id, base_bt); (size_id, size_bt) ]

  let make_value ~base ~size loc =
    IndexTerms.(
      record_ [ (base_id, base); (size_id, num_lit_ (Z.of_int size) size_bt loc) ] loc)


  let bt = BaseTypes.Map (Alloc_id, value_bt)

  let it loc = IndexTerms.sym_ (sym, bt, loc)

  let lookup_ptr ptr loc =
    assert (BaseTypes.(equal (IndexTerms.get_bt ptr) (Loc ())));
    IndexTerms.(map_get_ (it loc) (allocId_ ptr loc) loc)


  type value =
    { base : IndexTerms.t;
      size : IndexTerms.t
    }

  let split value loc =
    IndexTerms.
      { base = recordMember_ ~member_bt:base_bt (value, base_id) loc;
        size = recordMember_ ~member_bt:size_bt (value, size_id) loc
      }


  let sbt = BaseTypes.Surface.inj bt
end

module Predicate = struct
  let str = "Alloc"

  let loc = Locations.other __MODULE__

  let sym = Sym.fresh_named str
end
