Load IncludeHeader.

Variable A : ATOM.t.
Variable nativeop : Type.

Variable prog : Program.t A nativeop.

Variable cppsem : cppsemparam.
Variable sem : semparam A nativeop.

Variables s1 : State.t A nativeop.

(*
Variable aux_constr_state1 : list (ident * array_path A * Z * (Class.Inheritance.t * list ident) * FieldSignature.t A * construction_state).
*)

Hypothesis Hs1 : invariant prog s1 (* aux_constr_state1 *).

Variable s2 : State.t A nativeop.
Variable t : trace (evtr sem).

Hypothesis step : step prog cppsem s1 t s2.

Hypothesis hierarchy_wf : Well_formed_hierarchy.prop (Program.hierarchy prog).

Load NotationHeader.
