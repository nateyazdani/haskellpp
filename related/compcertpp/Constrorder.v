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
Load Param.
Open Scope nat_scope.

Section Constrorder.

Variable A : ATOM.t.
Variable nativeop : Type.

Open Scope Z_scope.

Variable prog : Program.t A nativeop.

Variable cppsem : cppsemparam.
Variable sem : semparam A nativeop.

(** * POPL 2012 submission: Lemma 6 *)

Lemma construction_state_modify_only_one_subobject : forall s1,
  forall t s2, step prog cppsem (sem := sem) s1 t s2 ->
    forall objarihp,
      assoc (@pointer_eq_dec _) objarihp (State.construction_states s1)
      <>
      assoc (@pointer_eq_dec _) objarihp (State.construction_states s2) ->
      forall objarihp', 
        objarihp' <> objarihp ->
        assoc (@pointer_eq_dec _) objarihp' (State.construction_states s1) =
        assoc (@pointer_eq_dec _) objarihp' (State.construction_states s2)
.
Proof.
 inversion 1; subst; unfold Globals.update in *; simpl in *; intros; try abstract congruence. 

(* Sconstructor Kconstrarray *)
sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil))) objarihp'
); try abstract congruence.
revert H3.
sdestruct (
 pointer_eq_dec (A:=A)
             (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil))) objarihp
); abstract congruence.

(* Sreturn Kconstrothercells *)
sdestruct (
 pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil))) objarihp'
); try abstract congruence.
revert H0.
sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil))) objarihp
); abstract congruence.

(* Sconstructor Kconstr base *)
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
         end))) objarihp'
); try abstract congruence.
revert H3.
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
         end))) objarihp
); abstract congruence.

(* Sreturn Kconstrother base *)
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
         end))) objarihp'
); try abstract congruence.
revert H0.
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
         end))) objarihp
); abstract congruence.

(* constr base direct non virtual nil *)
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p))) objarihp'
); try abstract congruence.
revert H2.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p))) objarihp
); abstract congruence.

(* destr array *)
sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil))) objarihp'
); try abstract congruence.
revert H5.
sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil))) objarihp
); abstract congruence.

(* destr field nil *)
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p))) objarihp'
); try abstract congruence.
revert H3.
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p))) objarihp
); abstract congruence.

(* destr base *)
sdestruct (
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
         end))) objarihp'
); try abstract congruence.
revert H0.
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
         end))) objarihp
); abstract congruence.

(* destr base direct non virtual nil *)
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, hp)) objarihp'
); try abstract congruence.
revert H0.
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, hp)) objarihp
); abstract congruence.

(* destr base virtual nil *)
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p))) objarihp'
); try abstract congruence.
revert H1.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p))) objarihp
); abstract congruence.

Qed.
    
(** * POPL 2012 submission: Lemma 6 (contd.) *)

(** Increasing *)

Lemma increasing_aux : forall s1,
  (invariant prog s1) ->
  forall t s2, step prog cppsem (sem := sem) s1 t s2 ->
    forall objarihp,
      assoc (@pointer_eq_dec _) objarihp (State.construction_states s1)
    =
    assoc (@pointer_eq_dec _) objarihp (State.construction_states s2) \/
    (Z_of_construction_state (assoc (@pointer_eq_dec _) objarihp (State.construction_states s1)) + 1 = 
    Z_of_construction_state (assoc (@pointer_eq_dec _) objarihp (State.construction_states s2)) /\ t = E0)
.
Proof. 
intros until 1.

generalize (kind H).
unfold state_kind_inv.
 inversion 2; subst; simpl in *; intros; try (left; reflexivity). 

 (* 10 Sconstructor Kconstrarray *)
 sdestruct (
pointer_eq_dec (A:=A)
        (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil))) objarihp
 ); try (left; reflexivity).
 invall; subst.
 assert (i <= i)%Z by eauto with zarith.
 unfold_ident_in_all.
 rewrite (H12 _ (conj H7 H13)).
 right; split; reflexivity.

(* 9 Sreturn Kconstrothercells *)
sdestruct (
 pointer_eq_dec (A:=A)
        (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil))) objarihp
); try (left; reflexivity).
 invall; subst.
 unfold_ident_in_all.
 rewrite H2.
 right; split; reflexivity.

(* 8 Sconstructor Kconstr base *)
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
        end))) objarihp
); try (left; reflexivity).
 invall; subst.
 destruct k2; invall; subst; unfold_ident_in_all.
  (* direct non virtual *)
  rewrite (H10 _ (or_introl _ (refl_equal _))).  
  right; split; reflexivity.
 rewrite (H13 _ (or_introl _ (refl_equal _))).
 right; split; reflexivity.

(* 7 Sreturn Kconstrother base *)
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
        end))) objarihp
); try (left; reflexivity).
subst.
 destruct k2; intros; invall; subst; unfold_ident_in_all.
  (* direct non virtual *)
  rewrite H2.
  right; split; reflexivity.
 rewrite H2.
 right; split; reflexivity.

(* constr base direct non virtual nil *)
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p))) objarihp
); try (left; reflexivity).
subst.
invall; subst.
unfold_ident_in_all.
rewrite H0.
right; split; reflexivity.

(*  Destruction *)
(* destr_array cons *)
sdestruct (
pointer_eq_dec (A:=A)
        (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil))) objarihp
); try (left; reflexivity).
subst.
invall; subst.
assert (j <= j)%Z by eauto with zarith.
unfold_ident_in_all.
rewrite (H11 _ (conj H2 H10)).
right; split; reflexivity.

(* destr field nil *)
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p))) objarihp
); try (left; reflexivity).
subst.
invall; subst.
unfold_ident_in_all.
rewrite H0.
right; split; reflexivity.

(* destr base cons *)
sdestruct (
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
        end))) objarihp
); try (left; reflexivity).
subst.
destruct beta; invall; subst; unfold_ident_in_all.
 (* direct non virtual *)
 rewrite (H13 _ (or_introl _ (refl_equal _))).
 right; split; reflexivity.
(* virtual *)
rewrite H14.
right; split; reflexivity.
auto.

(* destr base direct non virtual nil *)
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, hp)) objarihp
); try (left; reflexivity).
subst.
destruct hp.
invall; subst.
unfold_ident_in_all.
rewrite H0.
right; split; reflexivity.

(* destr base virtual nil *)
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p))) objarihp
); try (left; reflexivity).
subst.
invall; subst.
unfold_ident_in_all.
rewrite H0.
right; split; reflexivity.

Qed.

Corollary increasing : forall s1,
  (  invariant prog s1 ) ->
  forall t s2, step prog cppsem (sem := sem) s1 t s2 ->
    forall objarihp,  
  (assoc (@pointer_eq_dec _) objarihp (State.construction_states s1)
    =<
    assoc (@pointer_eq_dec _) objarihp (State.construction_states s2)).
Proof.
  intros; destruct (increasing_aux H H0 objarihp).
   rewrite H1; omega.
  destruct H1; omega.
Qed. 

Hypothesis hierarchy_wf : Well_formed_hierarchy.prop (Program.hierarchy prog).

Corollary increasing_star : forall s1,
  ( invariant prog s1 ) ->
  forall t s2, star (evtr sem) (step prog cppsem (sem := sem)) s1 t s2 ->
    forall objarihp,  
  (assoc (@pointer_eq_dec _) objarihp (State.construction_states s1)
    =<
    assoc (@pointer_eq_dec _) objarihp (State.construction_states s2)).
Proof.
 intros until 2.
 revert H.
 induction H0.
  intros; apply cs_le_refl.
 intros.
 eapply cs_le_trans.
  eapply increasing.
  assumption.
  eassumption.
 eapply IHstar.
 eauto using Preservation.goal.
Qed. 


(** * POPL 2012 submission: Corollary 7 *)
(** Subobjects are constructed/destructed only once *)

Corollary construction_states_change_only_once : forall s1,
  invariant prog s1 ->
  forall t s2, star (evtr sem) (step prog cppsem (sem := sem)) s1 t s2 ->
    forall objarihp c,   
      assoc (@pointer_eq_dec _) objarihp (State.construction_states s1) <> c ->
      assoc (@pointer_eq_dec _) objarihp (State.construction_states s2) = c ->
      forall t3 s3,  star (evtr sem) (step prog cppsem (sem := sem)) s2 t3 s3 ->
      forall t4 s4,  star (evtr sem) (step prog cppsem (sem := sem)) s3 t4 s4 ->
        assoc (@pointer_eq_dec _) objarihp (State.construction_states s3) <> c ->
        assoc (@pointer_eq_dec _) objarihp (State.construction_states s4) = c ->
        False.
Proof.
 intros.
 generalize (star_invariant _ (Preservation.goal hierarchy_wf) H H0).
 intro.
 generalize (star_invariant _ (Preservation.goal hierarchy_wf) H7 H3).
 intro.
 generalize (star_invariant _ (Preservation.goal hierarchy_wf) H8 H4).
 intro.
 generalize (increasing_star H7 H3 (objarihp := objarihp)).
 intro.
 generalize (increasing_star H8 H4 (objarihp := objarihp)).
 intro.
 subst.
 rewrite H6 in H11.
 generalize (cs_le_antisym H11 H10).
 assumption.
Qed.

(** * POPL 2012 submission: Theorem 8 *)

(** Intermediate values *)

Lemma intermediate_values_aux :
  forall s1 t s2, star (evtr sem) (step prog cppsem (sem := sem)) s1 t s2 ->
    (
      invariant prog s1 ) ->
    forall objarihp,  
  (assoc (@pointer_eq_dec _) objarihp (State.construction_states s1)
    <<
    assoc (@pointer_eq_dec _) objarihp (State.construction_states s2)) ->
  exists s'1, exists t1, 
    star (evtr sem) (step prog cppsem (sem := sem)) s1 t1 s'1 /\
    Z_of_construction_state (assoc (@pointer_eq_dec _) objarihp (State.construction_states s'1)) + 1 = Z_of_construction_state (assoc (@pointer_eq_dec _) objarihp (State.construction_states s2)) /\
      exists s'2,
        step prog cppsem (sem := sem) s'1 E0 s'2 /\
        assoc (@pointer_eq_dec _) objarihp (State.construction_states s'2) = assoc (@pointer_eq_dec _) objarihp (State.construction_states s2) /\
          exists t2,
            star (evtr sem) (step prog cppsem (sem := sem)) s'2 t2 s2 /\
            t = t1 ** t2
            .
Proof.
 induction 1.
  intros.
  apply False_rect.
  eauto using cs_lt_irrefl.
 intro.
 intro.
 generalize (Preservation.goal  hierarchy_wf H2 H).
 intro.
 generalize (increasing_aux H2 H objarihp).
 intro.
 intro.
 assert (
     assoc (pointer_eq_dec (A:=A)) objarihp
     (State.construction_states s2)
     =<
     assoc (pointer_eq_dec (A:=A)) objarihp (State.construction_states s3)
 ).
  destruct H4.
   rewrite <- H4; omega.
  omega.
 destruct (Z_le_lt_eq_dec _ _ H6).
  generalize (IHstar H3 _ z).
  intro; invall; subst.
  esplit.
  esplit.
  split.
   eright.
    eassumption.
    eexact H8.
    reflexivity.
    split.
     assumption.
    esplit.
    split.
     eassumption.
    split.
     assumption.
    esplit.
    split.
     eassumption.
    rewrite Eapp_assoc.
    trivial.
    apply evtr_sem.
  generalize (
    Z_of_construction_state_inj e
  ).
  intros.
  destruct H4.
   apply False_rect.
   apply cs_lt_irrefl with (assoc (@pointer_eq_dec _) objarihp (State.construction_states s1)).
   rewrite H4 at 2.
   rewrite H7.
   assumption.
  destruct H4; subst.
  esplit.
  esplit.
  split.
  eleft.
  split.
  rewrite <- H7.
  assumption.
  esplit.
  split.
   eassumption.
  split.
   assumption.
  esplit.
  split.
   eassumption.
  reflexivity.
Qed.

Lemma intermediate_values_rec_aux : forall q, 0 <= q ->
  forall s1 t s2, star (evtr sem) (step prog cppsem (sem := sem)) s1 t s2 ->
    (
      invariant prog s1 ) ->
    forall p, 0 <= p -> forall objarihp,  
      Z_of_construction_state (assoc (@pointer_eq_dec _) objarihp (State.construction_states s1)) + p + 1 + q =
      Z_of_construction_state (assoc (@pointer_eq_dec _) objarihp (State.construction_states s2)) ->
  exists s'1, exists t1, 
    star (evtr sem) (step prog cppsem (sem := sem)) s1 t1 s'1 /\
    Z_of_construction_state (assoc (@pointer_eq_dec _) objarihp (State.construction_states s'1)) + 1 + q = Z_of_construction_state (assoc (@pointer_eq_dec _) objarihp (State.construction_states s2)) /\
      exists s'2,
        step prog cppsem (sem := sem) s'1 E0 s'2 /\
        Z_of_construction_state (assoc (@pointer_eq_dec _) objarihp (State.construction_states s'2)) + q = Z_of_construction_state (assoc (@pointer_eq_dec _) objarihp (State.construction_states s2)) /\
          exists t2,
            star (evtr sem) (step prog cppsem (sem := sem)) s'2 t2 s2 /\
            t = t1 ** t2
            .
Proof.
 refine (natlike_ind _ _ _).
 intros.
 rewrite Zplus_0_r in *.
 assert (
(assoc (pointer_eq_dec (A:=A)) objarihp
            (State.construction_states s1)) <<
 (assoc (pointer_eq_dec (A:=A)) objarihp
            (State.construction_states s2))
 ) by omega.
 generalize (intermediate_values_aux H H0 H3).
 intros; invall; subst.
 esplit.
 esplit.
 split.
  eexact H5.
 rewrite Zplus_0_r in *.
 split.
  assumption.
 esplit.
 split.
  eassumption.
 rewrite Zplus_0_r in *.
 split.
  congruence.
 esplit.
 split.
  eassumption.
 trivial.
intros.
unfold Zsucc in *.
assert (
 (assoc (pointer_eq_dec (A:=A)) objarihp
            (State.construction_states s1)) <<
(assoc (pointer_eq_dec (A:=A)) objarihp
            (State.construction_states s2))
) by omega.
generalize (intermediate_values_aux H1 H2 H5).
intro.
revert H2. 
invall; subst.
assert (
 Z_of_construction_state
      (assoc (pointer_eq_dec (A:=A)) objarihp (State.construction_states s1)) +
    p + 1 + x =
    Z_of_construction_state
      (assoc (pointer_eq_dec (A:=A)) objarihp (State.construction_states x0))
) by omega.
intros.
generalize (H0 _ _ _ H2 H11 _ H3 _ H9).
intros; invall; subst.
esplit.
esplit.
split.
 eexact H13.
split.
 omega.
esplit.
split.
 eassumption.
split.
 omega.
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
 rewrite E0_left.
 rewrite Eapp_assoc.
 trivial.
 apply evtr_sem.
 apply evtr_sem.
Qed.

Corollary intermediate_values :
  forall s1 t s2, star (evtr sem) (step prog cppsem (sem := sem)) s1 t s2 ->
    (
      invariant prog s1 ) ->
    forall objarihp a,  
      (assoc (@pointer_eq_dec _) objarihp (State.construction_states s1) << a) ->
      (a =< assoc (@pointer_eq_dec _) objarihp (State.construction_states s2)) ->
      exists s'1, exists t1, 
        star (evtr sem) (step prog cppsem (sem := sem)) s1 t1 s'1 /\
        Z_of_construction_state (assoc (@pointer_eq_dec _) objarihp (State.construction_states s'1)) + 1 = Z_of_construction_state a /\
      exists s'2,
        step prog cppsem (sem := sem) s'1 E0 s'2 /\
        a  = assoc (@pointer_eq_dec _) objarihp (State.construction_states s'2) /\
          exists t2,
            star (evtr sem) (step prog cppsem (sem := sem)) s'2 t2 s2 /\
            t = t1 ** t2
            .
Proof.
 intros.
 refine (_ (intermediate_values_rec_aux
   (q := Z_of_construction_state (assoc (@pointer_eq_dec _) objarihp (State.construction_states s2)) - Z_of_construction_state a) _
   H H0
   (p := (Z_of_construction_state a - 1) - Z_of_construction_state (assoc (@pointer_eq_dec _) objarihp (State.construction_states s1))) _
   (objarihp := objarihp) _)); try omega.
 intros; invall; subst.
 esplit.
 esplit.
 split.
  eexact H3.
 split.
  omega.
 esplit.
 split.
  eassumption.
 split.
  eapply Z_of_construction_state_inj.
  omega.
 esplit.
 split.
 eassumption.
 trivial.
Qed.

Corollary intermediate_values_left :
  forall s1 t s2, star (evtr sem) (step prog cppsem (sem := sem)) s1 t s2 ->
    (
      invariant prog s1 ) ->
    forall objarihp,  
      (assoc (@pointer_eq_dec _) objarihp (State.construction_states s1) <>
        assoc (@pointer_eq_dec _) objarihp (State.construction_states s2)) ->
      exists s'1, exists t1, 
        star (evtr sem) (step prog cppsem (sem := sem)) s1 t1 s'1 /\
        assoc (@pointer_eq_dec _) objarihp (State.construction_states s1) = assoc (@pointer_eq_dec _) objarihp (State.construction_states s'1) /\
      exists s'2,
        step prog cppsem (sem := sem) s'1 E0 s'2 /\
        assoc (@pointer_eq_dec _) objarihp (State.construction_states s'1) <> assoc (@pointer_eq_dec _) objarihp (State.construction_states s'2) /\
        exists t2,
          star (evtr sem) (step prog cppsem (sem := sem)) s'2 t2 s2 /\
          t = t1 ** t2
          .
Proof.
  intros.
  generalize (increasing_star H0 H (objarihp := objarihp)).
  intro.
  destruct (
    cs_le_dec_2
     (assoc (pointer_eq_dec (A:=A)) objarihp (State.construction_states s2))
     (assoc (pointer_eq_dec (A:=A)) objarihp (State.construction_states s1))
  ).
    generalize (cs_le_antisym H2 z).
    intro; contradiction.
   refine (_ (intermediate_values_rec_aux (q := Z_of_construction_state (assoc (@pointer_eq_dec _) objarihp (State.construction_states s2)) - Z_of_construction_state (assoc (@pointer_eq_dec _) objarihp (State.construction_states s1)) - 1) _ H H0 (Zle_refl _) (objarihp := objarihp) _)).
  intros; invall. 
  esplit.
  esplit.
  split.
   eassumption.
   split.
   apply Z_of_construction_state_inj.
   omega.
  esplit.
  split.
   eassumption.
  split.
  intro.
  rewrite H7 in *.
  omega.
 esplit.
 split.
 eassumption.
 assumption.
 omega.
 omega.
Qed.

Corollary intermediate_values_right :
  forall s1 t s2, star (evtr sem) (step prog cppsem (sem := sem)) s1 t s2 ->
    (
      invariant prog s1 ) ->
    forall objarihp,  
      (assoc (@pointer_eq_dec _) objarihp (State.construction_states s1) <>
        assoc (@pointer_eq_dec _) objarihp (State.construction_states s2)) ->
      exists s'1, exists t1, 
        star (evtr sem) (step prog cppsem (sem := sem)) s1 t1 s'1 /\
      exists s'2,
        step prog cppsem (sem := sem) s'1 E0 s'2 /\
        assoc (@pointer_eq_dec _) objarihp (State.construction_states s'1) <> assoc (@pointer_eq_dec _) objarihp (State.construction_states s'2) /\
        exists t2,
          star (evtr sem) (step prog cppsem (sem := sem)) s'2 t2 s2 /\
          assoc (@pointer_eq_dec _) objarihp (State.construction_states s'2) = assoc (@pointer_eq_dec _) objarihp (State.construction_states s2) /\
          t = t1 ** t2
          .
Proof.
  intros.
  generalize (increasing_star H0 H (objarihp := objarihp)).
  intro.
  destruct (
    cs_le_dec_2
     (assoc (pointer_eq_dec (A:=A)) objarihp (State.construction_states s2))
     (assoc (pointer_eq_dec (A:=A)) objarihp (State.construction_states s1))
  ).
    generalize (cs_le_antisym H2 z).
    intro; contradiction.
   refine (_ (intermediate_values_rec_aux (Zle_refl _) H H0 (p := Z_of_construction_state (assoc (@pointer_eq_dec _) objarihp (State.construction_states s2)) - Z_of_construction_state (assoc (@pointer_eq_dec _) objarihp (State.construction_states s1)) - 1) _ (objarihp := objarihp) _)).
  intros; invall. 
  esplit.
  esplit.
  split.
   eassumption.
  esplit.
  split.
   eassumption.
  split.
  intro.
  rewrite H7 in *.
  omega.
 esplit.
 split.
 eassumption.
 split.
 apply Z_of_construction_state_inj.
 omega.
 assumption.
 omega.
 omega.
Qed.

Corollary intermediate_values' :
  forall s1 t s2, star (evtr sem) (step prog cppsem (sem := sem)) s1 t s2 ->
    (
      invariant prog s1 ) ->
    forall objarihp a,  
      (assoc (@pointer_eq_dec _) objarihp (State.construction_states s1) =< a) ->
      forall a', Z_of_construction_state a + 1 = Z_of_construction_state a' ->
        (a' =< assoc (@pointer_eq_dec _) objarihp (State.construction_states s2)) ->
      exists s'1, exists t1, 
        star (evtr sem) (step prog cppsem (sem := sem)) s1 t1 s'1 /\
        assoc (@pointer_eq_dec _) objarihp (State.construction_states s'1) = a /\
          exists s'2,
            step prog cppsem (sem := sem) s'1 E0 s'2 /\
            assoc (@pointer_eq_dec _) objarihp (State.construction_states s'2) = a' /\
              exists t2,
                star (evtr sem) (step prog cppsem (sem := sem)) s'2 t2 s2 /\
                t = t1 ** t2
                .
Proof.
 intros.
 refine (_ (intermediate_values H H0 _ H3)).
 intros; invall; subst.
 esplit.
 esplit.
 split.
 eexact H4.
 split.
 eapply Z_of_construction_state_inj.
 omega.
 esplit.
 split.
 eassumption.
 split.
 trivial.
 eauto.
 simpl in *; omega.
Qed.

Open Scope Z_scope.

Lemma step_object : forall s1,
  invariant prog s1 ->
  forall t s2, step prog cppsem (sem := sem) s1 t s2 ->
    forall obj o_, (Globals.heap (State.global s1)) ! obj = Some o_ ->
      (Globals.heap (State.global s2)) ! obj = Some o_
      .
Proof.
  inversion 2; subst; simpl; trivial.

  (* new *)
  injection H3; intros; subst; simpl in *.
  rewrite PTree.gso.
  assumption.
  intro.
  subst.
  generalize (Globals.valid_none (valid_global H) (Ple_refl (Globals.next_object gl))).
  simpl.
  intro;   abstract congruence.
Qed.

Corollary star_object : forall s1,
  forall t s2, star (evtr sem) (step prog cppsem (sem := sem)) s1 t s2 ->
  (
  invariant prog s1 ) ->  
    forall obj o_, (Globals.heap (State.global s1)) ! obj = Some o_ ->
      (Globals.heap (State.global s2)) ! obj = Some o_
        .
Proof.
  induction 1; intros; eauto using step_object, Preservation.goal.
Qed. 

(** * POPL 2012 submission: Theorem 13 *)
  
Theorem subobjects_are_destructed_in_reverse_order_of_construction : 
  forall s0
    (Hs0_inv : invariant prog s0)
    obj ar i h p hp
    (Hs0_valid : valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s0))
      (Value.subobject obj ar i h p hp))
(** first subobject enters lifetime *)
    (Hs0_not_constructed : assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (h, p)))
      (State.construction_states s0) <> Some Constructed)
    t1 s1
    (Hs0_s1_step : step prog cppsem (sem := sem) s0 t1 s1)
    (Hs1_constructed : assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (h, p)))
      (State.construction_states s1) = Some Constructed)
(** some dummy events *)
    t2 s2
    (Hs1_s2_star: star (evtr sem) (step prog cppsem (sem := sem)) s1 t2 s2)
    ar' i' h' p' hp'
    (Hs2_valid' : valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s2))
          (Value.subobject obj ar' i' h' p' hp'))
    (** second subobject enters lifetime *)
    (Hs2_not_constructed' : assoc (pointer_eq_dec (A:=A)) (obj, (ar', i', (h', p')))
          (State.construction_states s2) <> Some Constructed)
    t3 s3
    (Hs2_s3_step : step prog cppsem (sem := sem) s2 t3 s3)
    (Hs3_constructed' : assoc (pointer_eq_dec (A:=A)) (obj, (ar', i', (h', p')))
      (State.construction_states s3) = Some Constructed)
(** some dummy events *)
    t4 s4
    (Hs3_s4_star : star (evtr sem) (step prog cppsem (sem := sem)) s3 t4 s4)
(** first subobject exits lifetime *)
    (Hs4_constructed : assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (h, p)))
      (State.construction_states s4) = Some Constructed)
    t5 s5
    (Hs4_s5_step : step prog cppsem (sem := sem) s4 t5 s5)
    (Hs5_not_constructed :
      assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (h, p)))
      (State.construction_states s5) <> Some Constructed)
    ,
(** CONCLUSION : second subobject must have exited lifetime before *)
    exists t3', exists s3', 
                star (evtr sem) (step prog cppsem (sem := sem)) s3 t3' s3' /\
                assoc (pointer_eq_dec (A:=A)) (obj, (ar', i', (h', p')))
                (State.construction_states s3') = Some Constructed /\
                exists t4', exists s4',
                  step prog cppsem (sem := sem) s3' t4' s4' /\
                  assoc (pointer_eq_dec (A:=A)) (obj, (ar', i', (h', p'))) 
                  (State.construction_states s4') <> Some Constructed /\
                  exists t5', star (evtr sem) (step prog cppsem (sem := sem)) s4' t5' s4 /\
                    t4 = t3' ** t4' ** t5'
                    .
Proof.
 intros.

(* Compute invariants *)
 inversion_clear Hs0_valid as [ | ? o Hs0_o ? ? ? ? ? ? Hvalid_rel ]; subst.
 generalize (step_object Hs0_inv Hs0_s1_step Hs0_o).
 intro Hs1_o.
 generalize (Preservation.goal hierarchy_wf Hs0_inv Hs0_s1_step).
 intro Hs1_inv.
 generalize (star_object Hs1_s2_star Hs1_inv Hs1_o).
 intro Hs2_o.
 inversion_clear Hs2_valid' as [ | ? o' Hs2_o' ? ? ? ? ? ? Hvalid_rel' ]; subst.
 replace o' with o in * by abstract congruence.
 generalize (star_invariant _ (Preservation.goal hierarchy_wf) Hs1_inv Hs1_s2_star).
 intro Hs2_inv.
 generalize (step_object Hs2_inv Hs2_s3_step Hs2_o).
 intro Hs3_o.
 generalize (Preservation.goal hierarchy_wf Hs2_inv Hs2_s3_step).
 intro Hs3_inv.
 generalize (star_object Hs3_s4_star Hs3_inv Hs3_o).
 intro Hs4_o.
 generalize (star_invariant _ (Preservation.goal hierarchy_wf) Hs3_inv Hs3_s4_star).
 intro Hs4_inv.
 generalize (step_object Hs4_inv Hs4_s5_step Hs4_o).
 intro Hs5_o.
 generalize (Preservation.goal hierarchy_wf Hs4_inv Hs4_s5_step).
 intro Hs5_inv.

(* subobject S is Constructed between s1 and s4. *) 
 generalize (increasing_star Hs1_inv Hs1_s2_star (objarihp := (obj, (ar, i, (h, p))))).
 rewrite Hs1_constructed.
 intro Hs1_s2_le.
 generalize (increasing Hs2_inv Hs2_s3_step (objarihp := (obj, (ar, i, (h, p))))).
 intro Hs2_s3_le.
 generalize (increasing_star Hs3_inv Hs3_s4_star (objarihp := (obj, (ar, i, (h, p))))).
 rewrite Hs4_constructed.
 intro Hs3_s4_le.
 generalize (cs_le_antisym Hs1_s2_le (cs_le_trans Hs2_s3_le Hs3_s4_le)).
 intro Hs2_constructed; symmetry in Hs2_constructed.
 rewrite Hs2_constructed in *.
 generalize (cs_le_antisym Hs2_s3_le Hs3_s4_le).
 intro Hs3_constructed; symmetry in Hs3_constructed.
 rewrite Hs3_constructed in *.

(* determine subobject lifetime order *)
 destruct (lifetime_total hierarchy_wf Hvalid_rel' Hvalid_rel) as [ Habs | Hlifetime ].
 generalize (lifetime_construction_order Hs2_inv Hs2_o Habs Hs2_constructed).
 intro ; contradiction.

(* subobject S' has its state increasing between s3 and s4, and not changing through s5. So, at s4, it is strictly more than Constructed *)
generalize (increasing_star Hs3_inv Hs3_s4_star (objarihp := (obj, (ar', i', (h', p'))))).
rewrite Hs3_constructed'.
intro Hs3_s4_le'.
refine (_ (construction_state_modify_only_one_subobject
Hs4_s5_step (objarihp := (obj, (ar, i, (h, p)))) (objarihp' := (obj, (ar', i', (h', p')))) _ _)).
2 : congruence.
2 : congruence.
intro Hs4_s5_eq'.
destruct (cs_le_dec_2 (assoc (pointer_eq_dec (A := A)) (obj, (ar', i', (h', p'))) (State.construction_states s4)) (Some Constructed)) as [ Hs4_le_constructed' | Hs4_gt_constructed' ].
 generalize (cs_le_antisym Hs4_le_constructed' Hs3_s4_le').
 rewrite Hs4_s5_eq'.
 intro Hs5_constructed'.
 generalize (lifetime_construction_order Hs5_inv Hs5_o Hlifetime Hs5_constructed').
 intro; contradiction.

(* intermediate values thm to conclude *)
 refine (_ (intermediate_values (objarihp := (obj, (ar', i', (h', p')))) (a := Some StartedDestructing)
Hs3_s4_star Hs3_inv _ _)).
 2 : rewrite Hs3_constructed'; simpl; omega.
 2 : simpl in *; omega.
 intros [
   s3' [
     t3' [
       Hs3_s3'_star [
         Hs3'_constructed' [
           s4' [
             Hs3'_s4'_step [
               Hs4'_started_destructing' [
                 t5' [
                   Hs4'_s4_star
                   Ht4_t3'_t4'_t5'_eq
                 ]
               ]
             ]
           ]
         ]
       ]
     ]
   ]
 ].
 esplit.
 esplit.
 split.
  eexact Hs3_s3'_star.
 split.
  eapply Z_of_construction_state_inj.
  simpl in *; omega.
 esplit.
 esplit.
 split.
  eassumption.
 split.
  congruence.
 esplit.
 split.
  eassumption.
 rewrite E0_left.
 assumption.
 apply evtr_sem.

Qed.

(** * POPL 2012 submission: Theorem 18 *)

(** Dynamic type evolution *)

Section DynType.

 Variable s1 : State.t A nativeop.

 Hypothesis Hs1_inv : invariant prog s1.

 Variable s2 : State.t A nativeop.

 Variable t : trace (evtr sem).
 Hypothesis Hstep : step prog cppsem (sem := sem) s1 t s2.

 Let Hs2_inv : invariant prog s2.
 Proof.
   eauto using Preservation.goal.
 Qed.

 Lemma construction_states_next_none : forall obj,
   (Globals.heap (State.global s1)) ! obj = None ->
   forall arihp,
     assoc (@pointer_eq_dec _) (obj, arihp) (State.construction_states s2) = None.
 Proof.
   inversion Hstep; subst; simpl in *; try exact (construction_states_none Hs2_inv); exact (construction_states_none Hs1_inv).
 Qed.   

Lemma get_set_dynamic_type_other_after :
  forall obj ar i hp b,
    State.construction_states s2 = ((obj, (ar, i, hp)), b) :: State.construction_states s1 ->
      forall obj' ar' i', (obj, ar, i) <> (obj', ar', i') ->
        forall h' p',
          get_dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s1)) (State.construction_states s1) obj' ar' i' h' p' ->
          get_dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s2)) (State.construction_states s2) obj' ar' i' h' p'.
Proof.
  intros.
  rewrite H.
  inversion H1; subst.
   eleft.
   eauto using step_object.
   eassumption.
   assumption.
   simpl.
   sdestruct (pointer_eq_dec (A:=A) (obj, (ar, i, hp))
         (obj', (ar', i', (Class.Inheritance.Repeated, ato :: nil)))
   ); eauto.
   congruence.
  eright.
  eauto using step_object.
  eassumption.
  assumption.
  eassumption.
  simpl.
  sdestruct ( pointer_eq_dec (A:=A) (obj, (ar, i, hp)) (obj', (ar', i', (h', p')))
  ).
  2 : reflexivity.
  congruence.
  assumption.
Qed.
   
Lemma get_set_dynamic_type_other_before :
  forall obj ar i hp b,
    State.construction_states s2 = ((obj, (ar, i, hp)), b) :: State.construction_states s1 ->
      forall obj' ar' i', (obj, ar, i) <> (obj', ar', i') ->
        forall h' p',
          get_dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s2)) (State.construction_states s2) obj' ar' i' h' p' ->
          get_dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s1)) (State.construction_states s1) obj' ar' i' h' p'.
Proof.
  intros.
  rewrite H in H1.
  inversion H1; subst.
   generalize H5.
   simpl.
   sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, hp))
(obj', (ar', i', (Class.Inheritance.Repeated, ato :: nil)))
   ).
    congruence.
    case_eq ((Globals.heap (State.global s1)) ! obj').
     intros.
     rewrite (step_object Hs1_inv Hstep H6) in H2.
     injection H2; intros; subst.
     eleft; eauto.
    intro.
    rewrite (construction_states_none Hs1_inv H6).
    intro; discriminate.
   generalize H7.
   simpl.
   sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, hp)) (obj', (ar', i', (h', p')))
   ); try congruence.
   intro.
   case_eq ((Globals.heap (State.global s1)) ! obj').
     intros.
     rewrite (step_object Hs1_inv Hstep H8) in H2.
     injection H2; intros; subst.
     eright; eauto.
    intro.
    revert H6.    
    rewrite (construction_states_none Hs1_inv H8).
    destruct 1; discriminate.
Qed.

 Lemma get_set_dynamic_type_BasesConstructed_after : 
   forall obj ar i h p hp,
     valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s1)) (Value.subobject obj ar i h p hp) ->
     forall b,
     State.construction_states s2 = ((obj, (ar, i, (h, p))), b) :: State.construction_states s1 ->
     b = BasesConstructed \/ b = StartedDestructing ->
     get_dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s2)) (State.construction_states s2) obj ar i h p.
Proof.
 inversion 1; subst; intros.
 inversion H6; subst.
 eright.
 eapply step_object.
 eexact Hs1_inv.
 eassumption.
 eassumption.
 eassumption.
 split; assumption.
 eassumption.
 reflexivity.
 rewrite H0.
 simpl.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p))) (obj, (ar, i, (h, p)))
 ); try congruence.
 destruct H1; subst; auto.
Qed.

 Lemma get_set_dynamic_type_BasesConstructed_before : 
   forall obj ar i h p hp,
     valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s1)) (Value.subobject obj ar i h p hp) ->
     forall b,
       assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s2) = Some b ->
       b = BasesConstructed \/ (b = StartedDestructing /\ forall cn, (h, p) <> (Class.Inheritance.Repeated, cn :: nil)) ->
       assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s1) <> assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s2) ->
       forall h' p',
         get_dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s1)) (State.construction_states s1) obj ar i h' p' -> False.
 Proof.
   inversion 1; subst; intros.
   inversion H6; subst.
   destruct (increasing_aux Hs1_inv Hstep (obj, (ar, i, (h, p)))).
    contradiction.
   destruct H10; subst.
   rewrite H0 in H10.   
   inversion H4; subst.
    replace o0 with o in * by abstract congruence.
    generalize (valid_array_path_last H5 H12).
    intro; subst.
    generalize (inclusion_inheritance_subobject_of_full_object H12 H13 H9).
    intro.
    destruct H1; invall; subst; simpl in *.
     generalize (inclusion_construction_order Hs1_inv H11 H15).
     intros.
     generalize (construction_includes_constructed H1 H14).
     intro.
     unfold_ident_in_all.
     rewrite H13 in H10.
     simpl in *; congruence.    
    assert ((obj, (ar, i, (Class.Inheritance.Repeated, ato :: nil))) <> (obj, (ar, i, (h, p)))).
   generalize (H18 ato).
   congruence.
  generalize (construction_state_modify_only_one_subobject Hstep H3 H1).
  intro.
  unfold_ident_in_all.
  rewrite H13 in H14.
  generalize (step_object Hs1_inv Hstep H11).
  intro.
  generalize (inclusion_construction_order Hs2_inv H19 H15).
  intro.
  generalize (construction_includes_constructed H20 H14).
   unfold_ident_in_all; congruence.
  assert ((obj, (ar, i, (h', p'))) <> (obj, (ar, i, (h, p)))).
   intro.
   injection H15; intros; subst.
   generalize (increasing Hs1_inv Hstep (objarihp := (obj, (ar, i, (h, p))))).
   intro.
   destruct H1; invall; subst.
    destruct H16; try congruence.
    rewrite H1 in H10; simpl in *; congruence.
   destruct H16; try congruence.
   rewrite H1 in H10; simpl in *; congruence.
  generalize (construction_state_modify_only_one_subobject Hstep H3 H15).
  intro.
  rewrite H17 in H16.
  assert (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (h, p)))
          (State.construction_states s2) = Some BasesConstructed \/
        assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (h, p)))
          (State.construction_states s2) = Some StartedDestructing
  ).
   destruct H1; invall; subst; auto.  
  replace o0 with o in * by abstract congruence.
  generalize (valid_array_path_last H5 H12).
  intro; subst.
  assert ((h, p) = (h', p')).
   eapply bases_constructed_unique.
   eassumption.
   eassumption.
   eauto using step_object.
   eassumption.
   split; eassumption.
   eassumption.
   reflexivity.
   assumption.
   eassumption.
   reflexivity.
   assumption.
  congruence.
Qed.

Lemma get_set_dynamic_type_StartedConstructing_after : 
   forall obj ar i h p hp,
     valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s1)) (Value.subobject obj ar i h p hp) ->
     forall b,
       assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s2) = b ->
       b = Some StartedConstructing \/ b = Some DestructingBases \/ b = Some Destructed ->
       assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s1) <> assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s2) ->     
       forall h' p',
       get_dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s2)) (State.construction_states s2) obj ar i h' p' -> False.
Proof.
 inversion 1; subst; intros.
 inversion H6; subst.
 inversion H4; subst.

  (* full object Constructed *)
  replace o0 with o in *.
  generalize (valid_array_path_last H5 H10).
  intro; subst.
  refine (_ (bases_constructed Hs2_inv hierarchy_wf (p := _ :: nil) (hp := I) _ _ _ (refl_equal _) H9 _ _)).
  Focus 2.
  econstructor.
  eassumption.
  econstructor.
  eassumption.
  eassumption.
  assumption.
  eleft with (lt := nil).
  reflexivity.
  reflexivity.
  simpl.
  generalize (path_defined_from H9).
  destruct ((Program.hierarchy prog) ! ato); congruence.
  Focus 4.
  intro.
  injection H13; intros; subst.
  unfold_ident_in_all.
  rewrite H12 in H1.
  destruct H1; try discriminate.
  destruct H1; discriminate.
  Focus 4.
  symmetry.
  eapply concat_trivial_left.
  eassumption.
  intros.
  destruct H1; try congruence.
  destruct H1; congruence.
  rewrite H12; simpl; omega.
  rewrite H12; simpl; omega.
  generalize (step_object Hs1_inv Hstep H2).
  congruence.

(* other object BasesConstructed or StartedDestructing *)
 replace o0 with o in *.
 assert ((h, p) <> (h', p')).
  unfold_ident_in_all; destruct H14; destruct H1 as [? |[ ? | ? ]]; congruence.
assert ((obj, (ar, i, (h', p'))) <> (obj, (ar, i, (h, p)))) by congruence.
  generalize (construction_state_modify_only_one_subobject Hstep H3 H15).
  intro.
 generalize (valid_array_path_last H5 H10). 
 intro; subst.
 refine (_ (inheritance_construction_states_total
 hierarchy_wf obj H10 H11 H12 H9 _)).
 2 : congruence.
 intro.
 destruct (increasing_aux Hs1_inv Hstep (obj, (ar, i, (h, p)))).
  contradiction.
 destruct H17; subst.
 revert H17.
 destruct H1.
 (* StartedConstructing *)
 rewrite H1.
 simpl.
 case_eq (assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states s1)).
  destruct c; simpl; intros; omegaContradiction.
 intros ? _.
 destruct x.
  destruct H18.
   generalize (H18 _ Hs2_inv H0).
   unfold_ident_in_all.
   rewrite H1.
   destruct H14.
    rewrite H14.
    intros.    
    generalize (constructed_sibling_before_none H19 (Z_lt_dec_reflexion 2 3)).
    intro; discriminate.
   rewrite H14.
   intros.
   generalize (constructed_sibling_before_destructed H19 (Z_lt_dec_reflexion 3 4)).
   intro; discriminate.
  generalize (H18 _ Hs2_inv H0).
  intro.
  refine (_ (constructed_base_child_of_constructed H19 _ _)).
  unfold_ident_in_all; congruence.
  unfold_ident_in_all; destruct H14; rewrite H14; simpl; omega.
  unfold_ident_in_all; destruct H14; rewrite H14; simpl; omega.
 destruct H18.
  generalize (H18 _ Hs2_inv H0).
  unfold_ident_in_all.
  rewrite H1.
  intro.
  generalize (constructed_sibling_before_none H19 (Z_lt_dec_reflexion 1 3)).
  destruct H14; unfold_ident_in_all; congruence.
 generalize (H18 _ Hs1_inv H2).
 unfold_ident_in_all.
 intro.
 generalize (constructed_base_child_of_none H19 H17).
 unfold_ident_in_all; destruct H14; congruence.
destruct H1.
 (* DestructingBases *)
 rewrite H1.
 case_eq (
 (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (h, p)))
        (State.construction_states s1))
 ); simpl; try (intros; omegaContradiction).
 destruct c; try (intros; omegaContradiction).
 intros ? _.
 destruct x.
  destruct H18.
   generalize (H18 _ Hs2_inv H0).
   unfold_ident_in_all.
   rewrite H1.
   destruct H14.
    rewrite H14.
    intro.
    generalize (constructed_sibling_before_none H19 (Z_lt_dec_reflexion 2 3)).
    intro; discriminate.
   rewrite H14.
   intro.
   generalize (constructed_sibling_before_destructed H19 (Z_lt_dec_reflexion 3 4)).
   intro; discriminate.
  generalize (H18 _ Hs2_inv H0).
  unfold_ident_in_all.
  rewrite H1.
  intro.
  refine (_ (constructed_base_child_of_constructed H19 _ _)).
  unfold_ident_in_all; congruence.
  unfold_ident_in_all; destruct H14; rewrite H14; simpl; omega.
  unfold_ident_in_all; destruct H14; rewrite H14; simpl; omega.
 destruct H18.
  generalize (H18 _ Hs1_inv H2).
  unfold_ident_in_all.
  rewrite H17.
  intro.
  generalize (constructed_sibling_before_destructed H19 (Z_lt_dec_reflexion 3 4)).
  unfold_ident_in_all; destruct H14; congruence.
 generalize (H18 _ Hs1_inv H2).
 unfold_ident_in_all.
 rewrite H17.
 intro.
 refine (_ (constructed_base_child_of_constructed H19 _ _)); try (simpl; omega).
 unfold_ident_in_all; destruct H14; congruence.
(* Destructed *)
rewrite H1.
case_eq (
(assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (h, p)))
        (State.construction_states s1))
); simpl; try (intros; omegaContradiction).
destruct c; try (intros; omegaContradiction).
intros ? _.
destruct x.
 destruct H18.
  generalize (H18 _ Hs1_inv H2).
  unfold_ident_in_all.
  rewrite H17.
  rewrite <- H16 in H14.
  destruct H14; simpl in *; rewrite H14.
   intro.
   refine (_ (constructed_sibling_before_none H19 _)); simpl; intros; try discriminate; omega.
  intro.
  refine (_ (constructed_sibling_before_destructed H19 _)); simpl; intros; try discriminate; omega.
 generalize (H18 _ Hs2_inv H0).
 intro.
 refine (_ (constructed_base_child_of_constructed H19 _ _)).
 unfold_ident_in_all; congruence.
 unfold_ident_in_all; destruct H14; rewrite H14; simpl; omega.
 unfold_ident_in_all; destruct H14; rewrite H14; simpl; omega.
destruct H18.
 generalize (H18 _ Hs1_inv H2).
 unfold_ident_in_all.
 rewrite H17.
 intro.
 generalize (constructed_sibling_before_destructed H19 (Z_lt_dec_reflexion 3 5)).
 unfold_ident_in_all; destruct H14; congruence.
generalize (H18 _ Hs2_inv H0).
unfold_ident_in_all.
intro.
generalize (constructed_base_child_of_destructed H19 H1).
unfold_ident_in_all; destruct H14; congruence.

 generalize (step_object Hs1_inv Hstep H2).  
unfold_ident_in_all; intros; congruence.
Qed.
  
Lemma get_set_dynamic_type_StartedConstructing_before : 
   forall obj ar i h p hp,
     valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s1)) (Value.subobject obj ar i h p hp) ->
     forall b,
       assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s2) = b ->
       b = Some StartedConstructing \/ b = Some Destructed ->
       assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s1) <> assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s2) ->     
       forall h' p',
       get_dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s1)) (State.construction_states s1) obj ar i h' p' -> False.
Proof.
 inversion 1; subst; intros.
 inversion H6; subst.
 generalize (step_object Hs1_inv Hstep H2).
 intro.
 destruct (increasing_aux Hs1_inv Hstep (obj, (ar, i, (h, p)))).
  contradiction.
 destruct H10.
 inversion H4; subst.

  (* full object Constructed *)
  replace o0 with o in * by congruence.
  generalize (valid_array_path_last H5 H13).
  intro; subst.
  refine (_ (bases_constructed Hs1_inv hierarchy_wf (p := _ :: nil) (hp := I) _ _ _ (refl_equal _) H9 _ _)).
  Focus 2.
  econstructor.
  eassumption.
  econstructor.
  eassumption.
  eassumption.
  assumption.
  eleft with (lt := nil).
  reflexivity.
  reflexivity.
  simpl.
  generalize (path_defined_from H9).
  destruct ((Program.hierarchy prog) ! ato); congruence.
  Focus 4.
  intro.
  injection H11; intros; subst.
  unfold_ident_in_all.
  unfold_ident_in_all.
  rewrite H15 in H10.
  destruct H1; rewrite H1 in H10; simpl in *; omega.
  Focus 4.
  symmetry.
  eapply concat_trivial_left.
  eassumption.
  intros.
  rewrite x in H10.
  destruct H1; rewrite H1 in H10; simpl in *; omega.
  rewrite H15; simpl; omega.
  rewrite H15; simpl; omega.

(* other object BasesConstructed or StartedDestructing *)
 replace o0 with o in * by congruence.
 assert ((h, p) <> (h', p')).
  intro.
  injection H11; intros; subst.
  unfold_ident_in_all; destruct H1 as [ J | J]; destruct H17 as [ K | K]; rewrite J in H10; rewrite K in H10; simpl in *; omega.
assert ((obj, (ar, i, (h', p'))) <> (obj, (ar, i, (h, p)))) by congruence.
  generalize (construction_state_modify_only_one_subobject Hstep H3 H16).
  intro.
 generalize (valid_array_path_last H5 H13). 
 intro; subst.
 refine (_ (inheritance_construction_states_total
 hierarchy_wf obj H13 H14 H15 H9 _)).
 2 : congruence.
 intro.
 revert H10.
 destruct H1.
 (* StartedConstructing *)
 rewrite H1.
 simpl.
 case_eq (assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states s1)).
  destruct c; simpl; intros; omegaContradiction.
 intros ? _.
 destruct x.
  destruct H19.
   generalize (H19 _ Hs2_inv H0).
   unfold_ident_in_all.
   rewrite H1.
   rewrite <- H18.
   destruct H17.
    rewrite H17.
    intros.    
    generalize (constructed_sibling_before_none H20 (Z_lt_dec_reflexion 2 3)).
    intro; discriminate.
   rewrite H17.
   intros.
   generalize (constructed_sibling_before_destructed H20 (Z_lt_dec_reflexion 3 4)).
   intro; discriminate.
  generalize (H19 _ Hs1_inv H2).
  intro.
  refine (_ (constructed_base_child_of_constructed H20 _ _)).
  unfold_ident_in_all; congruence.
  unfold_ident_in_all; destruct H17; rewrite H17; simpl; omega.
  unfold_ident_in_all; destruct H17; rewrite H17; simpl; omega.
 destruct H19.
  generalize (H19 _ Hs1_inv H2).
  unfold_ident_in_all.
  rewrite H10.
  intro.
  generalize (constructed_sibling_before_none H20 (Z_lt_dec_reflexion 1 3)).
  destruct H17; unfold_ident_in_all; congruence.
 generalize (H19 _ Hs1_inv H2).
 unfold_ident_in_all.
 rewrite H10.
 intro.
 generalize (constructed_base_child_of_none H20 (refl_equal _)).
 unfold_ident_in_all; destruct H17; congruence.
 (* Destructed *)
 rewrite H1.
 case_eq (
 (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (h, p)))
        (State.construction_states s1))
 ); simpl; try (intros; omegaContradiction).
 destruct c; try (intros; omegaContradiction).
 intros ? _.
 destruct x.
  destruct H19.
   generalize (H19 _ Hs1_inv H2).
   unfold_ident_in_all.
   rewrite H10.
   destruct H17.
    rewrite H17.
    intro.
    generalize (constructed_sibling_before_none H20 (Z_lt_dec_reflexion 2 3)).
    intro; discriminate.
   rewrite H17.
   intro.
   generalize (constructed_sibling_before_destructed H20 (Z_lt_dec_reflexion 3 4)).
   intro; discriminate.
  generalize (H19 _ Hs1_inv H2).
  unfold_ident_in_all.
  rewrite H10.
  intro.
  refine (_ (constructed_base_child_of_constructed H20 _ _)).
  unfold_ident_in_all; congruence.
  unfold_ident_in_all; destruct H17; rewrite H17; simpl; omega.
  unfold_ident_in_all; destruct H17; rewrite H17; simpl; omega.
 destruct H19.
  generalize (H19 _ Hs1_inv H2).
  unfold_ident_in_all.
  rewrite H10.
  intro.
  generalize (constructed_sibling_before_destructed H20 (Z_lt_dec_reflexion 3 4)).
  unfold_ident_in_all; destruct H17; congruence.
 generalize (H19 _ Hs2_inv H0).
 unfold_ident_in_all.
 rewrite H1.
 rewrite <- H18.
 intro.
 refine (_ (constructed_base_child_of_destructed H20 (refl_equal _))). 
 unfold_ident_in_all. destruct  H17; congruence.
Qed.

  Lemma get_set_dynamic_type_Constructed_before : 
    forall obj ar i h p hp,
      valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s1)) (Value.subobject obj ar i h p hp) ->
      assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s2) = Some Constructed ->
      assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s1) <> assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s2) ->
      get_dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s1)) (State.construction_states s1) obj ar i h p.
Proof.
 inversion 1; subst.
 inversion H6; subst.
 intros.
 destruct (increasing_aux Hs1_inv Hstep (obj, (ar, i, (h, p)))).
  contradiction.
 destruct H8.
 subst.
 revert H8.
 rewrite H5.
 case_eq (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (h, p)))
   (State.construction_states s1)); simpl; try (intros; omegaContradiction).
  destruct c; try (intros; omegaContradiction).
  intros ? _.
  eright.
  eassumption.
  eassumption.
  tauto.
  eassumption.
  reflexivity.
  auto.
Qed.

Lemma get_set_dynamic_type_Constructed_after_not_most_derived :
  forall obj ar i h p hp,
    valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s1)) (Value.subobject obj ar i h p hp) ->
    assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s2) = Some Constructed ->
    (forall cn, (h, p) <> (Class.Inheritance.Repeated, cn :: nil)) ->
    assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s1) <> assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s2) ->
    forall h' p',
      get_dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s2)) (State.construction_states s2) obj ar i h' p' -> False.
 Proof.
  inversion 1; subst.
  inversion H6; subst.
  intros.
  destruct (increasing_aux Hs1_inv Hstep (obj, (ar, i, (h, p)))).
   contradiction.
 destruct H10; subst.
 revert H10.
 rewrite H5.
 case_eq (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (h, p)))
   (State.construction_states s1)); simpl; try (intros; omega).
 destruct c; try (intros; omega).
 intros ? _. 
 assert (get_dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s1)) (State.construction_states s1) obj ar i h p).
 eright.
 eassumption.
 eassumption.
 tauto.
 eassumption.
 reflexivity.
 auto.
 generalize (step_object Hs1_inv Hstep H2).
 intro.
 inversion H9; subst.
  replace o0 with o in * by congruence.
  generalize (valid_array_path_last H0 H14).
  intro; subst.
  assert ((h, p) <> (Class.Inheritance.Repeated, ato :: nil)) by eauto.
  assert ( (obj, (ar, i, (Class.Inheritance.Repeated, ato :: nil))) <> (obj, (ar, i, (h, p))) ) by congruence.
  generalize (construction_state_modify_only_one_subobject
 Hstep H8 H18).
  rewrite H16.
  intro.
  destruct H17.
  eapply get_dynamic_type_unique.
  eassumption.
  eexact Hs1_inv.
  eassumption.
  eleft.
  eassumption.
  eassumption.
  auto.
  assumption.
 replace o0 with o in * by congruence.
 assert ( (((h', p'))) <> (((h, p))) ) by (destruct H18; congruence).
 assert ( (obj, (ar, i, (h', p'))) <> (obj, (ar, i, (h, p))) ) by congruence.
 destruct H17.
 generalize (construction_state_modify_only_one_subobject Hstep H8 H19).
 intro.
 eapply get_dynamic_type_unique.
 eassumption.
 eexact Hs1_inv.
 eright.
 eassumption.
 eassumption.
 eassumption.
 eassumption.
 reflexivity.
 rewrite H17.
 assumption.
 assumption.
Qed.

Lemma get_set_dynamic_type_Constructed_after_most_derived :
  forall obj o,
    (Globals.heap (State.global s1)) ! obj = Some o ->
    forall ar ato zto,
      valid_array_path (Program.hierarchy prog) ato zto (Object.class o) (Object.arraysize o) ar ->
      forall i, 0 <= i < zto ->        
        assoc (@pointer_eq_dec _)  (obj, (ar, i, (Class.Inheritance.Repeated, ato :: nil))) (State.construction_states s2) = Some Constructed ->
        get_dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s2)) (State.construction_states s2) obj ar i Class.Inheritance.Repeated (ato :: nil).
 Proof.
   intros; eauto using step_object, get_dynamic_type_most_derived_constructed.
 Qed.

Lemma get_set_dynamic_type_StartedDestructing_before_most_derived :
  forall obj o,
    (Globals.heap (State.global s1)) ! obj = Some o ->
    forall ar ato zto,
      valid_array_path (Program.hierarchy prog) ato zto (Object.class o) (Object.arraysize o) ar ->
      forall i, 0 <= i < zto ->        
        assoc (@pointer_eq_dec _)  (obj, (ar, i, (Class.Inheritance.Repeated, ato :: nil))) (State.construction_states s2) = Some StartedDestructing ->
        assoc (@pointer_eq_dec _)  (obj, (ar, i, (Class.Inheritance.Repeated, ato :: nil))) (State.construction_states s1) <> assoc (@pointer_eq_dec _)  (obj, (ar, i, (Class.Inheritance.Repeated, ato :: nil))) (State.construction_states s2) ->
        get_dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s1)) (State.construction_states s1) obj ar i Class.Inheritance.Repeated (ato :: nil).
 Proof.
  intros.
  destruct (increasing_aux Hs1_inv Hstep (obj, (ar, i, (Class.Inheritance.Repeated, ato :: nil)))).
   contradiction.
  destruct H4; subst.
  revert H4.
  rewrite H2.
  case_eq  (assoc (pointer_eq_dec (A:=A))
        (obj, (ar, i, (Class.Inheritance.Repeated, ato :: nil)))
        (State.construction_states s1)); simpl; try (intros; omegaContradiction).
  destruct c; simpl; try (intros; omegaContradiction).
  intros ? _.
  eleft; eauto.
Qed.

(** More precisely *)

Lemma set_dynamic_type_other_before :
  forall obj ar i hp b,
    State.construction_states s2 = ((obj, (ar, i, hp)), b) :: State.construction_states s1 ->
      forall obj' ar' i', (obj, ar, i) <> (obj', ar', i') ->
        forall h1 p1 h' p' h'' p'',
          dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s2)) (State.construction_states s2) obj' ar' i' h1 p1 h' p' h'' p'' ->
          dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s1)) (State.construction_states s1) obj' ar' i' h1 p1 h' p' h'' p''.
Proof.
  intros.
  generalize (dynamic_type_prop H1).
  intro; invall; subst.
  generalize (dynamic_type_get_dynamic_type H1).
  intro.
  generalize (get_set_dynamic_type_other_before H H0 H4). 
  intro.
  eauto using get_dynamic_type_dynamic_type, path_last.
Qed.

Lemma set_dynamic_type_other_after :
  forall obj ar i hp b,
    State.construction_states s2 = ((obj, (ar, i, hp)), b) :: State.construction_states s1 ->
      forall obj' ar' i', (obj, ar, i) <> (obj', ar', i') ->
        forall h1 p1 h' p' h'' p'',
          dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s1)) (State.construction_states s1) obj' ar' i' h1 p1 h' p' h'' p'' ->
          dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s2)) (State.construction_states s2) obj' ar' i' h1 p1 h' p' h'' p''.
Proof.
  intros.
  generalize (dynamic_type_prop H1).
  intro; invall; subst.
  generalize (dynamic_type_get_dynamic_type H1).
  intro.
  generalize (get_set_dynamic_type_other_after H H0 H4). 
  intro.
  eauto using get_dynamic_type_dynamic_type, path_last.
Qed.

Lemma set_dynamic_type_StartedConstructing_before : 
   forall obj ar i h p hp,
     valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s1)) (Value.subobject obj ar i h p hp) ->
     forall b,
       assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s2) = b ->
       b = Some StartedConstructing \/ b = Some Destructed ->
       assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s1) <> assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s2) ->     
       forall h1 p1 h' p' h'' p'',
         dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s1)) (State.construction_states s1) obj ar i h1 p1 h' p' h'' p'' -> False.
Proof.
  intros.
  generalize (dynamic_type_get_dynamic_type H3).
  eauto using get_set_dynamic_type_StartedConstructing_before.
Qed.

Lemma set_dynamic_type_StartedConstructing_after : 
   forall obj ar i h p hp,
     valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s1)) (Value.subobject obj ar i h p hp) ->
     forall b,
       assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s2) = b ->
       b = Some StartedConstructing \/ b = Some DestructingBases \/ b = Some Destructed ->
       assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s1) <> assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s2) ->     
       forall h1 p1 h' p' h'' p'',
         dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s2)) (State.construction_states s2) obj ar i h1 p1 h' p' h'' p'' -> False.
Proof.
  intros.
  generalize (dynamic_type_get_dynamic_type H3).
  eauto using get_set_dynamic_type_StartedConstructing_after.
Qed.

Lemma set_dynamic_type_BasesConstructed_before : 
   forall obj ar i h p hp,
     valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s1)) (Value.subobject obj ar i h p hp) ->
     forall b,
       assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s2) = Some b ->
       b = BasesConstructed \/ (b = StartedDestructing /\ forall cn, (h, p) <> (Class.Inheritance.Repeated, cn :: nil)) ->
       assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s1) <> assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s2) ->
       forall h1 p1 h' p' h'' p'',
         dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s1)) (State.construction_states s1) obj ar i h1 p1 h' p' h'' p'' -> False.
 Proof.
  intros;
    eauto using get_set_dynamic_type_BasesConstructed_before, dynamic_type_get_dynamic_type.
Qed.

Lemma set_dynamic_type_BasesConstructed_after_same_path :
  forall obj ar i h p hp,
    valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s1)) (Value.subobject obj ar i h p hp) ->
    forall b,
      State.construction_states s2 = ((obj, (ar, i, (h, p))), b) :: State.construction_states s1 ->
      b = BasesConstructed \/ b = StartedDestructing ->
      forall cn,
        last p = Some cn ->
        forall to h' p',
          path (Program.hierarchy prog) to p' cn h' ->
          forall h1 p1, (h1, p1) = concat (h, p) (h', p') ->
            dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s2)) (State.construction_states s2) obj ar i h1 p1 h p h' p'.
Proof.
 intros; eauto using get_set_dynamic_type_BasesConstructed_after, get_dynamic_type_dynamic_type.
Qed.

Lemma set_dynamic_type_BasesConstructed_after_other_path :
  forall obj ar i h p hp,
    valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s1)) (Value.subobject obj ar i h p hp) ->
    forall b,
      State.construction_states s2 = ((obj, (ar, i, (h, p))), b) :: State.construction_states s1 ->
      b = BasesConstructed \/ b = StartedDestructing ->
      forall cn,
        last p = Some cn ->
        forall h1 p1,
          (
            forall to h' p',
              path (Program.hierarchy prog) to p' cn h' ->
              (h1, p1) = concat (h, p) (h', p') -> False
          ) ->
          forall h0 p0 h' p', dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s2)) (State.construction_states s2) obj ar i h1 p1 h0 p0 h' p' -> False.
Proof.
  intros.
  assert (Hdyn : get_dynamic_type  (Program.hierarchy prog) (Globals.heap (State.global s2)) (State.construction_states s2) obj ar i h p).
   inversion H; subst.
   inversion H11; subst.
   eright.
   eapply step_object.
   2 : eassumption.
   assumption.
   eassumption.
   eassumption.
   split; assumption.
   eassumption.
   reflexivity.
   rewrite H0.
   simpl.
   sdestruct (
     pointer_eq_dec (A:=A) (obj, (ar, i, (h, p))) (obj, (ar, i, (h, p)))
   ); try congruence.
   destruct H1; subst; auto.
  generalize (dynamic_type_get_dynamic_type H4).
  intro Hdyn'.
  generalize (get_dynamic_type_unique hierarchy_wf Hs2_inv Hdyn' Hdyn).
  intro Hinj.
  injection Hinj; intros Heq1 Heq2; subst.
  generalize (dynamic_type_prop H4).
  intros; invall; subst.
  generalize (path_last H9).
  rewrite H2.
  injection 1; intros; subst; eauto.
Qed.

Lemma set_dynamic_type_Constructed_before_same_path : 
  forall obj ar i h p hp,
    valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s1)) (Value.subobject obj ar i h p hp) ->
    assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s2) = Some Constructed ->
    assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s1) <> assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s2) ->
    forall cn,
      last p = Some cn ->
      forall to h' p',
        path (Program.hierarchy prog) to p' cn h' ->
        forall h1 p1, (h1, p1) = concat (h, p) (h', p') ->    
          dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s1)) (State.construction_states s1) obj ar i h1 p1 h p h' p'.
Proof.
 intros; eauto using get_set_dynamic_type_Constructed_before, get_dynamic_type_dynamic_type.
Qed.

Lemma set_dynamic_type_Constructed_after_not_most_derived :
  forall obj ar i h p hp,
    valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s1)) (Value.subobject obj ar i h p hp) ->
    assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s2) = Some Constructed ->
    (forall cn, (h, p) <> (Class.Inheritance.Repeated, cn :: nil)) ->
    assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s1) <> assoc (@pointer_eq_dec _)  (obj, (ar, i, (h, p))) (State.construction_states s2) ->
    forall h1 p1 h' p' h'' p'',
      dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s2)) (State.construction_states s2) obj ar i h1 p1 h' p' h'' p'' -> False.
 Proof.
  intros; eauto using dynamic_type_get_dynamic_type, get_set_dynamic_type_Constructed_after_not_most_derived.
Qed.

Lemma set_dynamic_type_Constructed_after_most_derived :
  forall obj o,
    (Globals.heap (State.global s1)) ! obj = Some o ->
    forall ar ato zto,
      valid_array_path (Program.hierarchy prog) ato zto (Object.class o) (Object.arraysize o) ar ->
      forall i, 0 <= i < zto ->        
        assoc (@pointer_eq_dec _)  (obj, (ar, i, (Class.Inheritance.Repeated, ato :: nil))) (State.construction_states s2) = Some Constructed ->
        forall h' p' to,
          path (Program.hierarchy prog) to p' ato h' ->
          dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s2)) (State.construction_states s2) obj ar i h' p' Class.Inheritance.Repeated (ato :: nil) h' p'.
 Proof.
   intros.
   eapply get_dynamic_type_dynamic_type.
   eauto using get_set_dynamic_type_Constructed_after_most_derived.
   reflexivity.
   eassumption.
   erewrite concat_trivial_left.
   reflexivity.
   eassumption.
 Qed.

Lemma set_dynamic_type_StartedDestructing_before_most_derived :
  forall obj o,
    (Globals.heap (State.global s1)) ! obj = Some o ->
    forall ar ato zto,
      valid_array_path (Program.hierarchy prog) ato zto (Object.class o) (Object.arraysize o) ar ->
      forall i, 0 <= i < zto ->        
        assoc (@pointer_eq_dec _)  (obj, (ar, i, (Class.Inheritance.Repeated, ato :: nil))) (State.construction_states s2) = Some StartedDestructing ->
        assoc (@pointer_eq_dec _)  (obj, (ar, i, (Class.Inheritance.Repeated, ato :: nil))) (State.construction_states s1) <> assoc (@pointer_eq_dec _)  (obj, (ar, i, (Class.Inheritance.Repeated, ato :: nil))) (State.construction_states s2) ->
        forall h' p' to,
          path (Program.hierarchy prog) to p' ato h' ->
          dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s1)) (State.construction_states s1) obj ar i h' p' Class.Inheritance.Repeated (ato :: nil) h' p'.
 Proof.
  intros.
   eapply get_dynamic_type_dynamic_type.
   eauto using get_set_dynamic_type_StartedDestructing_before_most_derived.
   reflexivity.
   eassumption.
   erewrite concat_trivial_left.
   reflexivity.
   eassumption.
 Qed.


End DynType.

  
(** RAII *)


Lemma construction_state_modify_stack_no_change : forall s1  t s2 (Hstep : step prog cppsem (sem := sem) s1 t s2)
  obj arihp
  (Hdiff :
    assoc (@pointer_eq_dec _) (obj, arihp) (State.construction_states s1)
    <>
    assoc (@pointer_eq_dec _) (obj, arihp) (State.construction_states s2)),
  stack_objects s1 = stack_objects s2.
Proof.
  inversion 1; subst; intros; simpl in *; congruence.
Qed.  

Lemma option_construction_state_eq_dec : forall c1 c2 : option construction_state,
  {c1 = c2} + {c1 <> c2}.
Proof.
  apply option_eq_dec.
  decide equality.
Qed.

Lemma step_stack_objects_recip : forall s1, invariant prog s1 -> forall t s2, step prog cppsem (sem := sem) s1 t s2 ->
  forall obj, In obj (stack_objects s2) ->
    In obj (stack_objects s1) \/ (Globals.heap (State.global s1)) ! obj = None.
Proof.
  intros until 1.
  generalize (valid_global H).  
  inversion 2; subst; simpl in *; eauto.
  destruct 1; eauto.
  subst.
  right.
  injection H4; intros; subst.
  eapply Globals.valid_none.
  assumption.
  apply Ple_refl.
Qed.

Corollary star_stack_objects : forall s2 t s3,
  star _ (step prog cppsem (sem := sem)) s2 t s3 ->
  forall obj, In obj (stack_objects s3) ->
    forall s1, invariant prog s1 ->
      forall t', star _ (step prog cppsem (sem := sem)) s1 t' s2 ->
        In obj (stack_objects s1) ->
        In obj (stack_objects s2).
Proof.
  induction 1; trivial.
  intros.
  refine (_ (IHstar _ H2 _ H3 _ _ H5)).
  intro.
  generalize (star_invariant _ (Preservation.goal hierarchy_wf) H3 H4).
  intro.
  destruct (step_stack_objects_recip H6 H x).
   assumption.
  apply False_rect.
  generalize (stack_objects_exist H3 H5).
  case_eq (
    (Globals.heap (State.global s0)) ! obj
  ); try congruence.
  intros until 1.
  intros _.
  generalize (star_object H4 H3 H8).
  congruence.
 eapply star_trans.
 apply evtr_sem.
 eassumption.
 eright.
 eassumption.
 eleft.
 reflexivity.
 reflexivity.
Qed. 

Lemma stack_dealloc_step : forall s1, invariant prog s1 ->
  forall t s2,
  step prog cppsem (sem := sem) s1 t s2 ->
  forall obj, In obj (stack_objects s1) ->
    (In obj (stack_objects s2) -> False) ->
    t = E0 /\
    stack_objects s1 = obj :: stack_objects s2 /\
    State.deallocated_objects s2 = obj :: State.deallocated_objects s1 /\
    State.construction_states s1 = State.construction_states s2.
Proof.
  inversion 2; subst; simpl in *; intros; try contradiction.

  intros.
  destruct H5.
  auto.

  generalize (kind H).
  unfold state_kind_inv; simpl.
  intros; invall; subst.
  destruct H1; try contradiction.
  subst; auto.
Qed.

Lemma stack_dealloc : forall s1 t s2, star _ (step prog cppsem (sem := sem)) s1 t s2 ->
  invariant prog s1 -> forall obj,
    In obj (stack_objects s1) ->
    (In obj (stack_objects s2) -> False) ->
    exists s'1, exists t'1,
      star _ (step prog cppsem (sem := sem)) s1 t'1 s'1 /\
      exists s'2, 
        step prog cppsem (sem := sem) s'1 E0 s'2 /\
        stack_objects s'1 = obj :: stack_objects s'2 /\
        State.deallocated_objects s'2 = obj :: State.deallocated_objects s'1 /\
        State.construction_states s'1 = State.construction_states s'2 /\
        exists t'2,
          star _ (step prog cppsem (sem := sem)) s'2 t'2 s2 /\
          t = t'1 ** t'2.
Proof.
 induction 1.
  intros; contradiction.
 intros.
 destruct (In_dec peq obj (stack_objects s2)).
  generalize (Preservation.goal hierarchy_wf H2 H).
  intro.
  generalize (IHstar H5 _ i H4).  
  intro; invall; subst.
  esplit.
  esplit.
  split.
  eright.
  eassumption.
  eexact H7.
  reflexivity.
  esplit.
  split.
  eassumption.
  split.
  assumption.
  split.
  assumption.
  split.
  trivial.
  esplit.
  split.
   eassumption.
  symmetry.
  eapply Eapp_assoc. 
  eapply evtr_sem.
 destruct (stack_dealloc_step H2 H H3 n).
 invall; subst.
 esplit.
 esplit.
 split.
 eleft.
 eauto 8.
Qed.

Lemma step_dealloc : forall obj s1,
  In obj (State.deallocated_objects s1) ->
  forall t s2, (step prog cppsem (sem := sem)) s1 t s2 ->
    In obj (State.deallocated_objects s2).
Proof.
  inversion 2; subst; simpl in *; auto.
Qed.

Corollary star_dealloc : forall obj s1,
  In obj (State.deallocated_objects s1) ->
  forall t s2, star _ (step prog cppsem (sem := sem)) s1 t s2 ->
    In obj (State.deallocated_objects s2).
Proof.
  intro.
  apply star_invariant.
  apply step_dealloc.
Qed.

Lemma step_stack_discipline : forall  s1
  (Hs1_inv : invariant prog s1)
  obj l1 l1'
  (Hs1 : stack_objects s1 = l1 ++ obj :: l1')
  t s2 (Hstep : (step prog cppsem (sem := sem)) s1 t s2) 
  l2 l2'
  (Hs2 : stack_objects s2 = l2 ++ obj :: l2')
  ,
    l1' = l2'.
Proof.
  intros.
  inversion Hstep; subst; simpl in *; try eauto using stack_objects_no_dup, nodup_right.

  (* alloc *)
  destruct l2; simpl in *.
   injection Hs2; intros; subst.
   injection H1; intros; subst; simpl in *.   
   generalize (stack_objects_exist Hs1_inv).
   simpl.
   rewrite Hs1.
   intro.
   refine (_ (H2 _ _)).
   2 : eapply in_or_app; right; left; reflexivity.
   destruct 1.
   eapply Globals.valid_none.
   exact (valid_global Hs1_inv).
   apply Ple_refl.
  injection Hs2; intros; subst.
  exact (nodup_right (stack_objects_no_dup Hs1_inv) Hs1 H2).

 (* dealloc *)
 destruct l1.
  simpl in *.
  injection Hs1; intros; subst.
  generalize (stack_objects_no_dup Hs1_inv).
  simpl.
  inversion 1; subst.
  destruct H2.
  rewrite Hs2.
  eauto using in_or_app.
 injection Hs1; intros; subst.
 assert (
   i :: block_objects bl ++ stackframe_objects stk = (i :: l2) ++ obj :: l2'
 ) by (simpl; congruence).
 exact (nodup_right (stack_objects_no_dup Hs1_inv) Hs1 H0). 
Qed. 
  
Corollary star_stack_discipline : forall s1 t s2 (Hstep : star _ (step prog cppsem (sem := sem)) s1 t s2) 
  (Hs1_inv : invariant prog s1)
  obj l1 l1'
  (Hs1 : stack_objects s1 = l1 ++ obj :: l1')
  l2 l2'
  (Hs2 : stack_objects s2 = l2 ++ obj :: l2')
  ,
    l1' = l2'.
Proof.
  induction 1.
  intros.
  eauto using nodup_right, stack_objects_no_dup.

  subst.
  intros.
  assert (In obj (stack_objects s2)).
   eapply star_stack_objects.
   eassumption.
   rewrite Hs2; eauto using in_or_app.
   eassumption.
   eapply star_left.
   eassumption.
   eleft.
   reflexivity.
   rewrite Hs1; eauto using in_or_app.
  destruct (In_split _ _ H0).
  invall.
  generalize (step_stack_discipline Hs1_inv Hs1 H H2).
  intro; subst.
  eauto using Preservation.goal.
Qed.

Theorem RAII_all_stack_objects_deallocated : forall s0, 
  invariant prog s0 ->
  forall t1 s1,
    step prog cppsem (sem := sem) s0 t1 s1 ->
    forall obj, stack_objects s1 = obj :: stack_objects s0 ->
      forall t sf, star _ (step prog cppsem (sem := sem)) s1 t sf ->
        forall i,
          final_state (sem := sem) sf i ->
          exists su, exists tu,
            star _ (step prog cppsem (sem := sem)) s1 tu su /\
            exists su', 
              step prog cppsem (sem := sem) su E0 su' /\
              stack_objects su = obj :: stack_objects su' /\
              State.deallocated_objects su' = obj :: State.deallocated_objects su /\
              exists tu',
                star _ (step prog cppsem (sem := sem)) su' tu' sf /\
                t = tu ** tu'.
Proof.
  intros.
  generalize (Preservation.goal hierarchy_wf H H0).
  intro.
  refine (_ (stack_dealloc H2 _ _ _ (obj := obj))).
  intro; invall; subst.
  eauto 10.
  assumption.
  rewrite H1; eauto.
  intro.
  inversion H3; subst; simpl in *; contradiction.
Qed.

Lemma no_self_cons : forall (A : Type) l (u : A), l = u :: l -> False.
Proof.
  induction l.
   intros; discriminate.
  injection 1; eauto.
Qed.

Lemma dealloc_from_stack : forall su
  (Hinv : invariant prog su)
  tu' su'
  (Hstep : step prog cppsem (sem := sem) su tu' su' )
  obj
    (Hdealloc : State.deallocated_objects su' = obj :: State.deallocated_objects su ),
    stack_objects su = obj :: stack_objects su'.
Proof.
  inversion 2; intros; subst; simpl in *; try destruct (no_self_cons Hdealloc).
  generalize (kind Hinv).
  unfold state_kind_inv.
  simpl.
  injection Hdealloc; intros; invall; subst; trivial.
Qed.

Corollary dealloc_only_once : forall s
  (Hinv : invariant prog s)
  tu1 su1
  (Hstep1 : step prog cppsem (sem := sem) s tu1 su1 )
  obj
    (Hdealloc1 : State.deallocated_objects su1 = obj :: State.deallocated_objects s )
    t' s'
    (Hstar : star _ (step prog cppsem (sem := sem)) su1 t' s')
    tu2 su2
    (Hstep2 : step prog cppsem (sem := sem) s' tu2 su2 )
    (Hdealloc2 : State.deallocated_objects su2 = obj :: State.deallocated_objects s' ),
    False.
Proof.
  intros.
  generalize (Preservation.goal hierarchy_wf Hinv Hstep1).
  intro Hsu1_inv.
  generalize (star_invariant _ (Preservation.goal hierarchy_wf) Hsu1_inv Hstar).
  intro Hs'_inv.
  generalize (dealloc_from_stack Hs'_inv Hstep2 Hdealloc2).
  intro Hstack'.  
  generalize (dealloc_from_stack Hinv Hstep1 Hdealloc1).
  intro Hstack.
  refine (_ (star_stack_objects (s2 := su1) (s3 := s') _ _ (obj := obj) (s1 := s) Hinv _ _)).
  generalize (stack_objects_no_dup Hinv).
  rewrite Hstack.
  inversion 1; subst.
  assumption.
  eassumption.
  rewrite Hstack'; eauto.
  eapply star_left.
  eassumption.
  eleft.
  reflexivity.
  rewrite Hstack; eauto.
Qed.

Lemma alloc_only_once : forall s
  (Hinv : invariant prog s)
  tu1 su1
  (Hstep1 : step prog cppsem (sem := sem) s tu1 su1 )
  obj
  (Halloc1 : stack_objects su1 = obj :: stack_objects s )
  t' s'
  (Hstar : star _ (step prog cppsem (sem := sem)) su1 t' s')
  tu2 su2
  (Hstep2 : step prog cppsem (sem := sem) s' tu2 su2 )
  (Halloc2 : stack_objects su2 = obj :: stack_objects s'),
    False.
Proof.
  intros.
  generalize (Preservation.goal hierarchy_wf Hinv Hstep1).
  intro Hsu1_inv.
  generalize (star_invariant _ (Preservation.goal hierarchy_wf) Hsu1_inv Hstar).
  intro Hs'_inv.
  generalize (Preservation.goal hierarchy_wf Hs'_inv Hstep2).
  intro Hsu2_inv.
  refine (_ (star_stack_objects (s2 := s') (s3 := su2) _ _ (obj := obj) (s1 := su1) Hsu1_inv _ _)).
  generalize (stack_objects_no_dup Hsu2_inv).
  rewrite Halloc2.
  inversion 1; subst; assumption.
  eapply star_step.
  eassumption.
  eleft.
  reflexivity.
  rewrite Halloc2; eauto.
  eassumption.
  rewrite Halloc1; eauto.
Qed.

Theorem first_alloc : forall s0 t sf,
  star _ (step prog cppsem (sem := sem)) s0 t sf ->
  forall obj, (In obj (stack_objects s0) -> False) ->
    In obj (stack_objects sf) ->
    exists s1, exists t1,
      star _ (step prog cppsem (sem := sem)) s0 t1 s1 /\
      exists s2,
        step prog cppsem (sem := sem) s1 E0 s2 /\
        stack_objects s2 = obj :: stack_objects s1 /\
        exists t2,
          star _ (step prog cppsem (sem := sem)) s2 t2 sf /\
          t = t1 ** t2.
Proof.
  induction 1.
   intros; contradiction.
  intros.
  destruct (In_dec peq obj (stack_objects s2)).
   assert (t1 = E0 /\ stack_objects s2 = obj :: stack_objects s1).
    inversion H; subst; try contradiction; simpl in *.
     split; trivial.
     injection H6; intros; subst.
     destruct i.
      congruence.
     contradiction.
    destruct H2; eauto.
   destruct H4; subst.
   esplit.
   esplit.
   split.
   eleft.
   esplit.
   split.
   eassumption.
   split; trivial.
   esplit.
   split.
    eassumption.
   reflexivity.
  generalize (IHstar _ n H3).
  intros; invall; subst.
  esplit.
  esplit.
  split.
  eapply star_left.
  eassumption.
  eexact H5.
  reflexivity.
  esplit.
  split.
   eassumption.
  split; trivial.
  esplit.
  split.
   eassumption.
  rewrite Eapp_assoc; eauto using evtr_sem.
Qed.
      

Corollary init_first_alloc : forall s0,
  initial_state prog s0 ->
  forall t sf,
  star _ (step prog cppsem (sem := sem)) s0 t sf ->
  forall obj,
    In obj (stack_objects sf) ->
    exists s1, exists t1,
      star _ (step prog cppsem (sem := sem)) s0 t1 s1 /\
      exists s2,
        step prog cppsem (sem := sem) s1 E0 s2 /\
        stack_objects s2 = obj :: stack_objects s1 /\
        exists t2,
          star _ (step prog cppsem (sem := sem)) s2 t2 sf /\
          t = t1 ** t2.
Proof.
  inversion 1; subst.
  intros.
  eapply first_alloc.
  assumption.
  simpl; intro; assumption.
  assumption.
Qed.  


Theorem RAII_alloc_dealloc : 
  forall s0,
    invariant prog s0 ->
    forall s1 t1,
      step prog cppsem (sem := sem) s0 t1 s1 ->
      forall obj,
        stack_objects s1 = obj :: stack_objects s0 ->
        forall sf1 tf1, 
          star _ (step prog cppsem (sem := sem)) s1 tf1 sf1 ->
          forall sf tf,
            step prog cppsem (sem := sem) sf1 tf sf ->
            State.deallocated_objects sf = obj :: State.deallocated_objects sf1 ->
            forall ar i h p hp,
              valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s1)) (Value.subobject obj ar i h p hp) ->
              exists sc, exists tc, star _ (step prog cppsem (sem := sem)) s1 tc sc /\
                assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states sc) <> Some Constructed /\
                exists sc', step prog cppsem (sem := sem) sc E0 sc' /\
                  assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states sc') = Some Constructed /\
                  exists sd, exists td, star _ (step prog cppsem (sem := sem)) sc' td sd /\
                    assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states sd) = Some Constructed /\
                    exists sd', step prog cppsem (sem := sem) sd E0 sd' /\
                      assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states sd') = Some StartedDestructing /\
                      exists td', star _ (step prog cppsem (sem := sem)) sd' td' sf1 /\
                        assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states sf1) = Some Destructed /\
                        tf1 = tc ** td ** td'.
Proof.
  (** invariants *)
  intros.
  generalize (Preservation.goal hierarchy_wf H H0).
  intro.
  generalize (star_invariant _ (Preservation.goal hierarchy_wf) H6 H2).
  intro.
  generalize (Preservation.goal hierarchy_wf H7 H3).
  intro.
  (** subobject is Destructed before deallocation *)
  generalize (dealloc_from_stack H7 H3 H4).
  intro.
  assert (In obj (stack_objects s1)).
   rewrite H1; eauto.
  assert (In obj (stack_objects sf1)).
   rewrite H9; eauto.
  assert (In obj (stack_objects sf) -> False).
   generalize (stack_objects_no_dup H7).
   rewrite H9.
   inversion 1; subst; assumption.
  generalize (stack_dealloc_step H7 H3 H11 H12).
  clear H9 H4.
  intro; invall; subst.
  inversion H5; subst.
  generalize (star_object H2 H6 H16).
  intro.
  generalize (step_object H7 H3 H9).
  intro.
  generalize (inclusion_subobject_of_full_object H20).
  intro; invall; subst.
  assert (In obj (State.deallocated_objects sf)).
   rewrite H13; eauto.  
  generalize (deallocated_objects_destructed H8 H17 H14 (conj H18 H21)).
  intro.
  generalize (construction_includes_destructed (inclusion_construction_order H8 H14 H19) H22).
  rewrite <- H15.
  intro.
  (** subobject is Unconstructed after allocation *)
  destruct (step_stack_objects_recip H H0 H10).
   apply False_rect.
   generalize (stack_objects_no_dup H6).
   rewrite H1.
   inversion 1; subst; eauto.
   generalize (construction_states_next_none H H0 H24 (ar, i, (h, p))).
   intro.
  (** now construct subobject *)
  refine (_ (intermediate_values' H2 H6 (objarihp := (obj, (ar, i, (h, p)))) (a := Some BasesConstructed) (a' := Some Constructed) _ (refl_equal _) _)).
  intro; invall; subst.
  generalize (star_invariant _ (Preservation.goal hierarchy_wf) H6 H26).
  intro.
  generalize (Preservation.goal hierarchy_wf H30 H29).
  intro.
  (** now destruct subobject *)
  refine (_ (intermediate_values' H31 H32 (objarihp := (obj, (ar, i, (h, p)))) (a := Some Constructed) (a' := Some StartedDestructing) _ (refl_equal _) _)).
  intros; invall; subst.
  (** conclude *)
  esplit.
  esplit.
  split.
  eexact H26.
  split.
  congruence.
  esplit.
  split.
  eassumption.
  split.
  assumption.
  esplit.
  esplit.
  split.
  eexact H33.
  split.
  assumption.
  esplit.
  split.
  eassumption.
  split.
  assumption.
  esplit.
  split.
  eassumption.
  eauto.
 rewrite H28; apply cs_le_refl.
 unfold_ident_in_all; rewrite H23; simpl; omega.
 unfold_ident_in_all; rewrite H25; simpl; omega.
 unfold_ident_in_all; rewrite H23; simpl; omega.
Qed.

Corollary RAII_dealloc : 
  forall s0,
    initial_state prog s0 ->    
    forall sf1 tf1, 
      star _ (step prog cppsem (sem := sem)) s0 tf1 sf1 ->
      forall sf tf,
        step prog cppsem (sem := sem) sf1 tf sf ->
        forall obj,
          State.deallocated_objects sf = obj :: State.deallocated_objects sf1 ->
          exists s'0, exists t0,
            star _ (step prog cppsem (sem := sem)) s0 t0 s'0 /\
            exists s1,
              step prog cppsem (sem := sem) s'0 E0 s1 /\
              stack_objects s1 = obj :: stack_objects s'0 /\
              forall ar i h p hp,
                valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s1)) (Value.subobject obj ar i h p hp) ->
                exists sc, exists tc, star _ (step prog cppsem (sem := sem)) s1 tc sc /\
                  assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states sc) <> Some Constructed /\
                  exists sc', step prog cppsem (sem := sem) sc E0 sc' /\
                    assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states sc') = Some Constructed /\
                    exists sd, exists td, star _ (step prog cppsem (sem := sem)) sc' td sd /\
                      assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states sd) = Some Constructed /\
                      exists sd', step prog cppsem (sem := sem) sd E0 sd' /\
                        assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states sd') = Some StartedDestructing /\
                        exists td', star _ (step prog cppsem (sem := sem)) sd' td' sf1 /\
                          assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states sf1) = Some Destructed /\
                          tf1 = t0 ** tc ** td ** td'.
Proof.
 intros.
 generalize (init H).
 intro.
 generalize (star_invariant _ (Preservation.goal hierarchy_wf) H3 H0).
 intro.
 generalize (Preservation.goal hierarchy_wf H4 H1).
 intro.
 generalize (dealloc_from_stack H4 H1 H2).
 intro.
 refine (_ (init_first_alloc H H0 (obj := obj) _)).
 intros; invall; subst.
 clear H0.
 generalize (star_invariant _ (Preservation.goal hierarchy_wf) H3 H7).
 intro.
 esplit.
 esplit.
 split.
  eassumption.
 esplit.
 split.
  eassumption.
 split.
  assumption.
 intros.
 generalize (RAII_alloc_dealloc H0 H9 H8 H11 H1 H2 H10).
 clear H11.
 intros; invall; subst.
 esplit.
 esplit.
 split.
  eassumption.
 split.
  assumption.
 esplit.
 split.
  eassumption.
 split.
  assumption.
 esplit.
 esplit.
 split.
   eassumption.
 split.
 assumption.
 esplit.
 split.
  eassumption.
 split.
 assumption.
 esplit.
 split.
  eassumption.
 split.
  assumption.
 reflexivity.
rewrite H6; eauto.
Qed.

Lemma eventually_dealloc_step : forall s t s', 
  step prog cppsem (sem := sem) s t s' ->
  forall obj,
    (In obj (State.deallocated_objects s) -> False) ->
    (In obj (State.deallocated_objects s')) ->
    State.deallocated_objects s' = obj :: State.deallocated_objects s /\ t = E0.
Proof.
  inversion 1; subst; simpl; try (intros; contradiction).
  intros.
   destruct H1; try contradiction.
   unfold_ident_in_all; split; congruence.
Qed.  

Lemma eventually_dealloc : forall s t s', star _ (step prog cppsem (sem := sem)) s t s' ->
  forall obj,
    (In obj (State.deallocated_objects s) -> False) ->
    (In obj (State.deallocated_objects s')) ->
    exists s1, exists t1, 
      star _ (step prog cppsem (sem := sem)) s t1 s1 /\
      exists s'1, 
        step prog cppsem (sem := sem) s1 E0 s'1 /\
        State.deallocated_objects s'1 = obj :: State.deallocated_objects s1 /\
        exists t'1,
          star _ (step prog cppsem (sem := sem)) s'1 t'1 s' /\
          t = t1 ** t'1.
Proof.
  induction 1.
   intros; contradiction.
  subst.
  intros.
  destruct (In_dec peq obj (State.deallocated_objects s2)).
   destruct (eventually_dealloc_step H H1 i).
   subst.
   esplit.
   esplit.
   split.
   eleft.
   esplit.
   split.
    eassumption.
   split.
    assumption.
   eauto.
  generalize (IHstar _ n H2).
  clear H0.
  intros; invall; subst.
  esplit.
  esplit.
  split.
  eapply star_left.
  eassumption.
  eassumption.
  reflexivity.
  esplit.
  split.
   eassumption.
  split.
   assumption.
  esplit.
  split.
   eassumption.
  rewrite Eapp_assoc; eauto using evtr_sem.
Qed.

(** * POPL 2012 submission: Theorem 16 *)

Corollary RAII : 
  forall s0,
    initial_state prog s0 ->    
    forall sfz tfz, 
      star _ (step prog cppsem (sem := sem)) s0 tfz sfz ->
      forall res,
        final_state (sem := sem) sfz res ->
        forall obj, (Globals.heap (State.global sfz)) ! obj <> None ->
          exists sf, exists tf,
            star _ (step prog cppsem (sem := sem)) sf tf sfz /\
            exists sf1,
              step prog cppsem (sem := sem) sf1 E0 sf /\
              State.deallocated_objects sf = obj :: State.deallocated_objects sf1 /\
              exists s'0, exists t0,
                star _ (step prog cppsem (sem := sem)) s0 t0 s'0 /\
                exists s1,
                  step prog cppsem (sem := sem) s'0 E0 s1 /\
                  stack_objects s1 = obj :: stack_objects s'0 /\
                  forall ar i h p hp,
                    valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s1)) (Value.subobject obj ar i h p hp) ->
                    exists sc, exists tc, star _ (step prog cppsem (sem := sem)) s1 tc sc /\
                      assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states sc) <> Some Constructed /\
                      exists sc', step prog cppsem (sem := sem) sc E0 sc' /\
                        assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states sc') = Some Constructed /\
                        exists sd, exists td, star _ (step prog cppsem (sem := sem)) sc' td sd /\
                          assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states sd) = Some Constructed /\
                          exists sd', step prog cppsem (sem := sem) sd E0 sd' /\
                            assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states sd') = Some StartedDestructing /\
                            exists td', star _ (step prog cppsem (sem := sem)) sd' td' sf1 /\
                              assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states sf1) = Some Destructed /\
                              tfz = t0 ** tc ** td ** td' ** tf.
Proof.
 intros.
 inversion H1; subst.
 simpl in *.
 generalize (init H).
 intro.
 generalize (star_invariant _ (Preservation.goal hierarchy_wf) H5 H0).
 intro.
 generalize (stack_or_deallocated H6 H2).
 simpl.
 destruct 1.
  contradiction.
 refine (_ (eventually_dealloc H0 _ H7)).
 clear H0.
 intros; invall; subst.
 esplit.
 esplit.
 split.
  eassumption.
 esplit.
 split.
  eassumption.
 split.
  assumption.
 generalize (RAII_dealloc H H0 H9 H8).
 intros; invall; subst.
 esplit.
 esplit.
 split.
  eassumption.
 esplit.
 split.
  eassumption.
 split.
 assumption.
 intros.
 generalize (H15 _ _ _ _ _ H14).
 intro; invall; subst.
 esplit.
 esplit.
 split.
 eassumption.
 split.
 assumption.
 esplit.
 split.
  eassumption.
 split.
  assumption.
 esplit.
 esplit.
 split.
  eassumption.
 split.
  assumption.
 esplit.
 split.
  eassumption.
 split.
  assumption.
 esplit.
 split.
  eassumption.
 split.
 assumption.
 repeat rewrite Eapp_assoc; eauto using evtr_sem.
inversion H; subst; simpl; intro; assumption.
Qed.


End Constrorder.
