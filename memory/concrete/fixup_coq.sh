sed -i 's/Definition t0_default{a: Type} : t0 a := Defined DAEMON./Definition t0_default{a: Type} : t0 a := Defined a DAEMON.\nArguments Defined {_} _.\nArguments Undef {_} _ _.\nArguments Error {_} _ _./g' coq_generated/undefined.v

sed -i 's/Definition kill_reason_default{err: Type} : kill_reason err := Undef0 unit_default DAEMON./Definition kill_reason_default{err: Type} : kill_reason err := Undef0 err unit_default DAEMON.\nArguments Undef0 {_} _ _.\nArguments Error0 {_} _ _.\nArguments Other {_} _.\n/g' coq_generated/nondeterminism.v


sed -i 's/Definition nd_action_default {a: Type} {info: Type} {err: Type} {cs: Type} {st: Type} : nd_action a info err cs st := NDactive DAEMON./Definition nd_action_default {a: Type} {info: Type} {err: Type} {cs: Type} {st: Type} : nd_action a info err cs st := NDactive a info err cs st DAEMON./g' coq_generated/nondeterminism.v
sed -i 's/Definition ndM_default {a: Type} {info: Type} {err: Type} {cs: Type} {st: Type} : ndM a info err cs st := ND (fun (x37 : st) => (DAEMON, DAEMON))./Definition ndM_default {a: Type} {info: Type} {err: Type} {cs: Type} {st: Type} : ndM a info err cs st := ND a info err cs st (fun (x37 : st) => (DAEMON, DAEMON)).\nArguments NDactive {_} {_} {_} {_} {_} _.\nArguments NDkilled {_} {_} {_} {_} {_} _.\nArguments NDnd {_} {_} {_} {_} {_} _ _.\nArguments NDguard {_} {_} {_} {_} {_} _ _ _.\nArguments NDbranch {_} {_} {_} {_} {_} _ _ _.\nArguments NDstep {_} {_} {_} {_} {_} _ _.\nArguments ND {_} {_} {_} {_} {_} _./g' coq_generated/nondeterminism.v


sed -i 's/Definition nd_status_default {a: Type} {err: Type} : nd_status a err := Active DAEMON./Definition nd_status_default {a: Type} {err: Type} : nd_status a err := Active a err DAEMON.\nArguments Active {_} {_} _.\nArguments Killed {_} {_} _.\n/g' coq_generated/nondeterminism.v

sed -i 's/Definition mem_constraint_default{a: Type} : mem_constraint a := MC_empty./Definition mem_constraint_default{a: Type} : mem_constraint a := MC_empty a.\nArguments MC_empty {_}.\nArguments MC_eq {_} _ _.\nArguments MC_le {_} _ _.\nArguments MC_lt {_} _ _.\nArguments MC_in_device {_} _.\nArguments MC_or {_} _ _.\nArguments MC_conj {_} _.\nArguments MC_not {_} _.\n/g' coq_generated/mem_common.v

sed -i 's/Program Fixpoint eq_core_object_type/Fixpoint eq_core_object_type/g' coq_generated/core.v

sed -i 's/Definition generic_name_default{sym: Type} : generic_name sym := Sym DAEMON./Definition generic_name_default{sym: Type} : generic_name sym := Sym sym DAEMON.\nArguments Sym {_} _.\nArguments Impl {_} _.\n/g' coq_generated/core.v

sed -i 's/Definition generic_object_value_default{sym: Type} : generic_object_value sym := OVinteger unit_default./Definition generic_object_value_default{sym: Type} : generic_object_value sym := OVinteger sym unit_default.\nArguments OVinteger {_} _.\nArguments OVfloating {_} _.\nArguments OVpointer {_} _.\nArguments OVarray {_} _.\nArguments OVstruct {_} _ _.\nArguments OVunion {_} _ _ _.\n/g' coq_generated/core.v

sed -i 's/Definition generic_loaded_value_default{sym: Type} : generic_loaded_value sym := LVspecified DAEMON./Definition generic_loaded_value_default{sym: Type} : generic_loaded_value sym := LVspecified sym DAEMON.\nArguments LVspecified {_} _.\nArguments LVunspecified {_} _.\n/g' coq_generated/core.v

sed -i 's/Definition generic_value_default{sym: Type} : generic_value sym := Vobject DAEMON./Definition generic_value_default{sym: Type} : generic_value sym := Vobject sym DAEMON.\nArguments Vobject {_} _.\nArguments Vloaded {_} _.\nArguments Vunit {_}.\nArguments Vtrue {_}.\nArguments Vfalse {_}.\nArguments Vctype {_} _.\nArguments Vlist {_} _ _.\nArguments Vtuple {_} _.\n/g' coq_generated/core.v

