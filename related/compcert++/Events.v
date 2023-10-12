(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Representation of observable events and execution traces. *)

(** The observable behaviour of programs is stated in terms of
  input/output events, which can also be thought of as system calls 
  to the operating system.  An event is generated each time an
  external function (see module AST) is invoked.  The event records
  the name of the external function, the arguments to the function
  invocation provided by the program, and the return value provided by
  the outside world (e.g. the operating system).  Arguments and values
  are either integers or floating-point numbers.  We currently do not
  allow pointers to be exchanged between the program and the outside
  world. *)

Load Param.

Record tr : Type := make_tr {
  trace : Type;
  E0 : trace;
  Eapp : trace -> trace -> trace;
  traceinf : Type;
  Eappinf : trace -> traceinf -> traceinf;
  outcome : Type
}.

(** Concatenation of traces is written [**] in the finite case
  or [***] in the infinite case. *)
Infix "**" := Eapp (at level 60, right associativity).
Infix "***" := Eappinf (at level 60, right associativity).
Implicit Arguments E0 [t].

Record trsem (t0 : tr) : Prop := trsem_intro {
  E0_left: forall t : _ t0, E0 ** t = t;
  E0_right: forall t : _ t0, t ** E0 = t;
  Eapp_assoc: forall t1 t2 t3 : _ t0, (t1 ** t2) ** t3 = t1 ** (t2 ** t3);
  Eapp_E0_inv: forall t1 t2 : _ t0, t1 ** t2 = E0 -> t1 = E0 /\ t2 = E0;
  E0_left_inf: forall T : _ t0, E0 *** T = T;
  Eappinf_assoc: forall (t1 t2 : _ t0) T, (t1 ** t2) *** T = t1 *** (t2 *** T)
}.

Hint Rewrite E0_left E0_right Eapp_assoc
             E0_left_inf Eappinf_assoc: trace_rewrite.
