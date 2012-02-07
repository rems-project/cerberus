val in_range_int :
  CpAil.int_type -> CpAilConstraint.constant -> CpAilConstraint.constr
val in_range :
  CpAil.ctype -> CpAilConstraint.constant -> CpAilConstraint.constr
val conv_int :
  CpAil.ctype -> CpAilConstraint.constant ->
  CpAilConstraint.constant * CpAilConstraint.constr
val conv :
  CpAil.ctype -> CpAil.ctype -> CpAilConstraint.constant
  -> CpAilConstraint.constant * CpAilConstraint.constr
val size : CpAil.ctype -> CpAilConstraint.constant
val align : CpAil.ctype -> CpAilConstraint.constant -> CpAilConstraint.constr
