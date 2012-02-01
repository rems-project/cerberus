theory isa_fixes

imports Main

begin 

types num = "nat"

(* Definitions for the set library *)

definition isa_set_mem :: "'a => 'a set => bool" where
"isa_set_mem s S = (s : S)"

definition isa_set_subset :: "'a set => 'a set => bool" where
"isa_set_subset s1 s2 = (s1 < s2)"

definition isa_set_subset_eq :: "'a set => 'a set => bool" where
"isa_set_subset_eq s1 s2 = (s1 <= s2)"

definition isa_set_supset :: "'a set => 'a set => bool" where
"isa_set_supset s1 s2 = (s1 > s2)"

definition isa_set_supset_eq :: "'a set => 'a set => bool" where
"isa_set_supset_eq s1 s2 = (s1 >= s2)"

definition isa_set_union :: "'a set => 'a set => 'a set" where
"isa_set_union s1 s2 = (union s1 s2)"

definition isa_set_inter :: "'a set => 'a set => 'a set" where
"isa_set_inter s1 s2 = (inter s1 s2)"

definition isa_set_is_empty :: "'a set => bool" where 
"isa_set_is_empty s = (s = {})"

end
