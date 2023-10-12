Load IncludeHeader.

(** * POPL 2012 submission: Lemma 1 and 2 (invariant preservation) *)

Require Import PreservationAux.

Variable A : ATOM.t.
Variable nativeop : Type.

Variable prog : Program.t A nativeop.

Theorem init : forall s1, initial_state prog s1 ->
  invariant prog s1.
Proof.
  inversion 1; subst.
  split; simpl; try (intros; tauto); try (intros; discriminate); try 
    (intros ? ?; rewrite PTree.gempty; congruence); try (destruct l1; simpl; congruence); try (intros; split; try congruence; simpl in *; intros; omegaContradiction); try (constructor; fail).

  (* 3 valid *)
  constructor.
  simpl.
  intros.
  apply PTree.gempty.

  (* 2 defined object in stack *)
  intro.
  rewrite PTree.gempty.
  congruence.

  (* 1 unconstructed structure fields *)
  destruct hp.
  rewrite H1.
  trivial.
Qed.

Variable cppsem : cppsemparam.
Variable sem : semparam A nativeop.

Theorem goal : forall
( hierarchy_wf : Well_formed_hierarchy.prop (Program.hierarchy prog) )
(s1 : State.t A nativeop)
(Hs1 : invariant prog s1 (* aux_constr_state1 *) )
( t : trace (evtr sem) )
( s2 : State.t A nativeop )
( step : step prog cppsem s1 t s2 )
,
invariant prog s2.
Proof.
 intros.
 constructor.
 eauto using valid_global.
 eauto using construction_states_none.
 eauto using construction_states_fields_none.
 eauto using valid_object_classes.
 eauto using object_arraysizes_nonnegative.
 Require Import PreservationKind. eauto using goal.
 Require Import PreservationStack. eauto using goal.
 Require Import PreservationStack2. eauto using goal.
 eauto using stack_state.
 Require Import PreservationStackStateWf. eapply goal; eassumption. 
 Require Import PreservationStackWf. eauto using goal.
 Require Import PreservationConstructionStatesDirectNonVirtual. eauto using goal.
 Require Import PreservationConstructionStatesVirtual. eauto using goal.
 Require Import PreservationConstructionStatesFields. eauto using goal.
 Require Import PreservationConstructionStatesStructureFields. eauto using goal.
 Require Import PreservationBreadthVirtual. eauto using goal.
 Require Import PreservationBreadthVirtualDirectNonVirtual. eauto using goal.
 Require Import PreservationBreadthDirectNonVirtual. eauto using goal.
 Require Import PreservationBreadthFields. eauto using goal.
 Require Import PreservationBreadthArrays. eauto using goal.
 eauto using stack_objects_no_dup.
 eauto using stack_objects_exist.
 eauto using constructed_stack_objects_correct.
 eauto using constructed_stack_objects_no_kind.
 eauto using constructed_stack_objects_no_stackframe.
 eauto using stack_objects_in_construction.
 eauto using stack_objects_sorted.
 eauto using kind_object_in_construction.
 eauto using deallocated_objects_exist.
 eauto using deallocated_objects_not_in_stack. 
 eauto using deallocated_objects_destructed.
 eauto using stack_or_deallocated.
 eauto using unconstructed_scalar_fields.
Qed.

End Preservation.
