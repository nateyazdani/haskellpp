Require Import Relations.
Require Import Coqlib.
Require Import LibPos.
Require Import Maps.
Require Import LibLists.
Require Import Cppsem.
Require Import Cplusconcepts.
Require Import CplusWf.
Require Import Events.
Require Import Invariant.
Require Import Preservation.
Require Import Smallstep.
Require Import Dyntype.
Require Import SubobjectOrdering.
Require Import ConstrSubobjectOrdering.
Require Import Constrorder.
Load Param.
Open Scope Z_scope.

Section Constrorder.

Variable A : ATOM.t.
Variable nativeop : Type.

Open Scope Z_scope.

Variable prog : Program.t A nativeop.

Hypothesis hierarchy_wf : Well_formed_hierarchy.prop (Program.hierarchy prog).

Variable cppsem : cppsemparam.
Variable sem : semparam A nativeop.


Lemma construction_state_modify_topmost_object : forall s1
  (Hinv : invariant prog s1)
  t s2 (Hstep : step prog cppsem (sem := sem) s1 t s2)
  obj arihp
  (Hdiff :
    assoc (@pointer_eq_dec _) (obj, arihp) (State.construction_states s1)
    <>
    assoc (@pointer_eq_dec _) (obj, arihp) (State.construction_states s2)),
  exists p, stack_objects s1 = obj :: p.
Proof.
  inversion 2; subst; intros; try (simpl in *; congruence); simpl in Hdiff; revert Hdiff. 

  sdestruct (
pointer_eq_dec (A:=A)
                (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
                (obj0, arihp)
  ); try congruence.
  injection e; intros; subst.
  exact (stack_objects_in_construction Hinv (l1 := nil) (refl_equal _) (refl_equal _)).

  sdestruct (
    pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0, arihp)
  ); try congruence.
  injection e; intros; subst.
  exact (stack_objects_in_construction Hinv (l1 := nil) (refl_equal _) (refl_equal _)).

  sdestruct (
pointer_eq_dec (A:=A)
         (obj,
         (ar, i,
         (match k2 with
          | Constructor.direct_non_virtual => h
          | Constructor.virtual => Class.Inheritance.Shared
          end,
         match k2 with
         | Constructor.direct_non_virtual => p ++ b :: nil
         | Constructor.virtual => b :: nil
         end))) (obj0, arihp)
  ); try congruence.
  injection e; intros; subst.
  exact (stack_objects_in_construction Hinv (l1 := nil) (refl_equal _) (refl_equal _)).

  sdestruct ( 
pointer_eq_dec (A:=A)
         (obj,
         (ar, i,
         (match k2 with
          | Constructor.direct_non_virtual => h
          | Constructor.virtual => Class.Inheritance.Shared
          end,
         match k2 with
         | Constructor.direct_non_virtual => p ++ b :: nil
         | Constructor.virtual => b :: nil
         end))) (obj0, arihp)
  ); try congruence.
  injection e; intros; subst.
  exact (stack_objects_in_construction Hinv (l1 := nil) (refl_equal _) (refl_equal _)).

  sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p))) (obj0, arihp)
  ); try congruence.
  injection e; intros; subst.
  eauto using kind_object_in_construction.

  sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0, arihp)
  ); try congruence.
  injection e; intros; subst.
  eauto using kind_object_in_construction.

  sdestruct (
    pointer_eq_dec (A:=A) (obj, (ar, i, (h, p))) (obj0, arihp)
  ); try congruence.
  injection e; intros; subst.
  eauto using kind_object_in_construction.

  sdestruct(
pointer_eq_dec (A:=A)
         (obj,
         (ar, i,
         (match beta with
          | Constructor.direct_non_virtual => h
          | Constructor.virtual => Class.Inheritance.Shared
          end,
         match beta with
         | Constructor.direct_non_virtual => p ++ b :: nil
         | Constructor.virtual => b :: nil
         end))) (obj0, arihp)
  ); try congruence.
  injection e; intros; subst; eauto using kind_object_in_construction.

  sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, hp)) (obj0, arihp)
  ); try congruence.
  injection e; intros; subst; eauto using kind_object_in_construction.

  sdestruct( 
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p))) (obj0, arihp)
  ); try congruence.
  injection e; intros; subst; eauto using kind_object_in_construction.

Qed.


(** * POPL 2012 submission: Lemma 15 *)


Theorem lower_object_construction_states_no_change : forall s1 t s2, star _ (step prog cppsem (sem := sem)) s1 t s2 ->
  invariant prog s1 -> forall obj,
  In obj (stack_objects s1) ->
  In obj (stack_objects s2) ->
  forall obj', Plt obj' obj ->
    forall arihp,
    assoc (@pointer_eq_dec _) (obj', arihp) (State.construction_states s1)
    =
    assoc (@pointer_eq_dec _) (obj', arihp) (State.construction_states s2).
Proof.
  induction 1; trivial.
  intros.
  eapply trans_equal.
  Focus 2.
  eapply IHstar.
  eauto using Preservation.goal.
   eapply star_stack_objects.
   eassumption.
   eassumption.
   eassumption.
   eassumption.
   eright.
   eassumption.
   eleft.
   reflexivity.
   assumption.
  assumption.
  assumption.
 destruct (option_construction_state_eq_dec
   (  assoc (pointer_eq_dec (A:=A)) (obj', arihp) (State.construction_states s1))
   ( assoc (pointer_eq_dec (A:=A)) (obj', arihp) (State.construction_states s2)) ).
    assumption.
  apply False_rect.
  destruct (construction_state_modify_topmost_object H2 H n).
  generalize (stack_objects_sorted H2).
  rewrite H6.
  intro.
  refine (_ (sorted_sorted2 _ H7)).
   2 : eauto using Plt_trans.
  destruct 1.
  eapply Plt_irrefl.
  eapply Plt_trans.
  eassumption.
  apply H8.
  rewrite H6 in H3.
  destruct H3; auto.
  subst.
  destruct (Plt_irrefl _ H5).
Qed.

Theorem stack_storage_duration_included_in_other_lifetime :
  forall s0, 
    invariant prog s0 ->
    forall t1 s1,
      step prog cppsem (sem := sem) s0 t1 s1 ->
      forall obj, stack_objects s1 = obj :: stack_objects s0 ->
        forall t2 s2, star _ (step prog cppsem (sem := sem)) s1 t2 s2 ->
          forall obj', In obj' (stack_objects s0) ->
            forall arihp, 
              assoc (@pointer_eq_dec _) (obj',  arihp) (State.construction_states s1) <>
              assoc (@pointer_eq_dec _) (obj', arihp) (State.construction_states s2) ->
              exists s'1, exists t'1,
                star _ (step prog cppsem (sem := sem)) s1 t'1 s'1 /\
                exists s'2,
                  step prog cppsem (sem := sem) s'1 E0 s'2 /\
                  State.deallocated_objects s'2 = obj :: State.deallocated_objects s'1 /\
                  assoc (@pointer_eq_dec _) (obj', arihp) (State.construction_states s'2) =
                  assoc (@pointer_eq_dec _) (obj', arihp) (State.construction_states s1) /\
                  exists t'2,
                    star _ (step prog cppsem (sem := sem)) s'2 t'2 s2 /\
                    t2 = t'1 ** t'2.
Proof.
  intros.
  generalize (Preservation.goal hierarchy_wf H H0).
  intro.
  generalize (intermediate_values_left hierarchy_wf H2 H5 H4).
  intro; invall; subst.
  generalize (star_invariant _ (Preservation.goal hierarchy_wf) H5 H7).
  intro.
  destruct (construction_state_modify_topmost_object H10 H9 H8).
  refine (_ ( stack_dealloc hierarchy_wf H7 H5 _ _)).
  Focus 2.
  rewrite H1.
  eleft.
  reflexivity.
 intros; invall; subst.
 esplit.
 esplit.
 split.
  eexact H13.
  esplit.
  split.
   eassumption.
  split.
  assumption.
  split.
  generalize (increasing_star hierarchy_wf H5 H13 (objarihp := (obj', arihp))).
  generalize (star_invariant _ (Preservation.goal hierarchy_wf) H5 H13).
  intro.
  generalize (increasing H18 H15 (objarihp := (obj', arihp))).
  generalize (Preservation.goal hierarchy_wf H18 H15).
  intro.
  generalize (increasing_star hierarchy_wf H20 H19 (objarihp := (obj', arihp))).
  symmetry.
  rewrite <- H6 in H21.
  intros; eauto 8 using cs_le_trans, cs_le_antisym.
 esplit.
 split.
 eapply star_trans.
 apply evtr_sem.
 eassumption.
 eright.
 eassumption.
 eassumption.
 reflexivity.
 reflexivity.
 rewrite E0_left; try rewrite Eapp_assoc; eauto using evtr_sem.
refine (_ (sorted_sorted2 _ (stack_objects_sorted H5))); eauto using Plt_trans.
rewrite H1.
destruct 1.
generalize (H13 _ H3).
intro.
refine (_ (sorted_sorted2 _ (stack_objects_sorted H10))); eauto using Plt_trans.
rewrite H12.
destruct 1.
destruct 1.
 subst.
 eapply Plt_irrefl.
 eassumption.
generalize (H16 _ H18).
intro.
destruct (Plt_irrefl obj).
eapply Plt_trans.
eassumption.
assumption.
Qed.

End Constrorder.
