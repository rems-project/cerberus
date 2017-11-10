let quote = function
  | "§6.5.9#2" ->
      "One of the following shall hold:\n\n- both operands have arithmetic type;\n- both operands are pointers to qualified or unqualified versions of compatible types;\n- one operand is a pointer to an object type and the other is a pointer to a qualified or unqualified version of **void**; or\n- one operand is a pointer and the other is a null pointer constant."
  | "§6.5.9#2, item 1" ->
      "both operands have arithmetic type;"
  | "§6.5.9#2, item 2" ->
      "both operands are pointers to qualified or unqualified versions of compatible types;"
  | "§6.5.9#2, item 3" ->
      "one operand is a pointer to an object type and the other is a pointer to a qualified or unqualified version of **void**; or"
  | "§6.5.9#2, item 4" ->
      "one operand is a pointer and the other is a null pointer constant."
  
  | "§6.5.3.2#1, register" ->
      "The operand of the unary & operator shall be (...) an lvalue that designates an object that (...) is not declared with the register storage-class specifier."
  
  | "§6.5.3.3#1" ->
      "The operand of the unary **+** or **-** operator shall have arithmetic type; of the **~** operator, integer type; of the **!** operator, scalar type."
  | "§6.5.3.3#1, sentence 1" ->
      "The operand of the unary **+** or **-** operator shall have arithmetic type;"
  | "§6.5.3.3#1, sentence 2" ->
      "[The operand] of the **~** operator, integer type;"
  | "§6.5.3.3#1, sentence 3" ->
      "[The operand] of the **!** operator, scalar type."
  
  | "§6.5.16#2" ->
      "An assignment operator shall have a modifiable lvalue as its left operand."
  
  | "§6.5.16.1#1" ->
      "One of the following shall hold:\n— the left operand has atomic, qualified, or unqualified arithmetic type, and the right has arithmetic type;\n— the left operand has an atomic, qualified, or unqualified version of a structure or union type compatible with the type of the right;\n— the left operand has atomic, qualified, or unqualified pointer type, and (considering the type the left operand would have after lvalue conversion) both operands are pointers to qualified or unqualified versions of compatible types, and the type pointed to by the left has all the qualifiers of the type pointed to by the right;\n— the left operand has atomic, qualified, or unqualified pointer type, and (considering the type the left operand would have after lvalue conversion) one operand is a pointer to an object type, and the other is a pointer to a qualified or unqualified version of void, and the type pointed to by the left has all the qualifiers of the type pointed to by the right;\n— the left operand is an atomic, qualified, or unqualified pointer, and the right is a null pointer constant; or\n— the left operand has type atomic, qualified, or unqualified _Bool, and the right is a pointer."
  
  | "§6.7.6.2#1, sentence 4" ->
      "The element type shall [of an array] not be an incomplete or function type."
  
  | "§6.7.2.1#3, incomplete or function" ->
      "A structure or union shall not contain a member with incomplete or function type (hence, a structure shall not contain an instance of itself, but may contain a pointer to an instance of itself)"
  
  | "§6.5.3.3#1, 2nd sentence" ->
      "such a structure [one with a flexible array member] (and any union containing, possibly recursively, a member that is such a structure) shall not be a member of a structure or an element of an array."

  | "§6.7.6.3#1" ->
      "A function declarator shall not specify a return type that is a function type or an array type."


  | std ->
      "QUOTE NOT FOUND: " ^ std
