class annotate_position : Position.t -> object
  method position : Position.t
end

class annotate_type : Position.t -> CpAil.type_class -> object
  method position : Position.t
  method type_class : CpAil.type_class
end

val a_pos : Position.t -> annotate_position
val a_type : Position.t -> CpAil.type_class -> annotate_type

val exp_of : ('id, 'a) CpAil.exp -> ('id, ('id, 'a) CpAil.exp) CpAil.expression
val pos_of : <position : Position.t; ..> * 'a -> Position.t
val type_of : <type_class : CpAil.type_class; ..> * 'a -> CpAil.type_class

val exp_type_of : <type_class : CpAil.type_class; ..> * 'a -> CpAil.ctype
val lvalue_type_of : <type_class : CpAil.type_class; ..> * 'a -> CpAil.ctype
val ctype_of : <type_class : CpAil.type_class; ..> * 'a -> CpAil.ctype
