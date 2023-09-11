(** CPP.v: Copyright 2010 Tahina Ramananandro *)

Require Import LibLists.
Require Import Cplusconcepts.
Require Import Coqlib.
Require Import Tactics.
Require Import CplusWf.
Require Import LibMaps.
Require Import LayoutConstraints.
Require Import LibPos.
Require Import Dynamic.
Load Param.

Section Is_dynamic.

Variable A : ATOM.t.

Record CPPOPTIM : Type := CppOptim {
  is_empty : PTree.t (Class.t A) -> ident -> Prop;
  is_empty_prop : forall hierarchy, Is_empty.prop hierarchy (is_empty hierarchy);
(** 4.3 *)
  dynamic_nonempty : forall hierarchy id, is_dynamic hierarchy id -> is_empty hierarchy id -> False
}.

Section Optim.

Variable C : CPPOPTIM.

Definition Optim := Optim (is_empty_prop C) (dynamic_nonempty (c := C)).

End Optim.

End Is_dynamic.

