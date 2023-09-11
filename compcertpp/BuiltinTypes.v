Require Import Events.
Require Import List.
Require Import ZArith.
Load Param.

(** * Atomic types *)

(** Atomic types (int, short, bool, long, etc.) are left as parameters of our formalization. *)

Module ATOM.

Record t : Type := make {
  ty : Type;
  ty_eq_dec : forall a b : ty, {a = b} + {a <> b};
  val : ty -> Type;
  val_eq_dec : forall ty (a b : val ty), {a = b} + {a <> b}
}.

End ATOM.

Hint Resolve ATOM.ty_eq_dec.


Section Semparam.

Variable A : ATOM.t.
Variable nativeop : Type.

Record semparam : Type := Semparam {
  evtr : tr;
  evtr_sem : trsem evtr;
  nativeop_sem : nativeop -> list (sigT (ATOM.val (t := A))) -> option (sigT (ATOM.val (t := A))) -> trace evtr -> Prop;
  semZ : forall (ty : _ A), ATOM.val ty -> option Z;
  sembool : forall (ty : _ A), ATOM.val ty -> option bool;
  tyTRUE: ATOM.ty A;
  TRUE: ATOM.val tyTRUE;
  semTRUE: sembool TRUE = Some true;
  tyFALSE: ATOM.ty A;
  FALSE: ATOM.val tyFALSE;
  semFALSE: sembool FALSE = Some false;
  Zsem : Z -> sigT (ATOM.val (t := A));
  Zsem_semZ : forall z ty va, Zsem z = existT _ ty va -> semZ va = Some z;
  outcome_sem : forall (ty : _ A), ATOM.val ty -> outcome evtr -> Prop (* required for final states *);
  CONST : forall ty : _ A, ATOM.val ty -> nativeop;
  semCONST : forall (ty : _ A) va, nativeop_sem (CONST va) nil (Some (existT _ ty va)) E0
}.

End Semparam.