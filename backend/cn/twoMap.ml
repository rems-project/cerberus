module Make(HL : Hashtbl.HashedType)(HR : Hashtbl.HashedType) = struct

  module HL_Table = Hashtbl.Make(HL)
  module HR_Table = Hashtbl.Make(HR)
  
  type t = {
      left_to_right : HR_Table.key HL_Table.t;
      right_to_left : HL_Table.key HR_Table.t;
    }

  let create n = {
      left_to_right = HL_Table.create n;
      right_to_left = HR_Table.create n;
    }

  let left_to_right table l = 
    HL_Table.find_opt table.left_to_right l

  let right_to_left table r = 
    HR_Table.find_opt table.right_to_left r
  
  let add table (l, r) = 
    HL_Table.add table.left_to_right l r;
    HR_Table.add table.right_to_left r l;

end
