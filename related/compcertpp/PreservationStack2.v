Load PreservationHeader.

Lemma goal :  (forall sf l1 l2, (State.stack s2) = l1 ++ sf :: l2 -> stack2_inv prog s2 sf l2).
Proof.
  Opaque Zminus.
  intros sf l1 l2 H.
  unfold stack2_inv.
  split.
  Focus 2.
  generalize (fun sf1 l1 l2 H => let (_, C) := stack2 Hs1 (sf1 := sf1) (l1 := l1) (l2 := l2) H in C).
  intros.
  revert sf l1 l2 H H1.
  inversion step; subst; simpl in *; eauto; try (
    intros sf l1 l2 K;
      exact (H0 _ _ _ (app_cons K _))
  );
  intros sf l1 l2 K;
  destruct l1 as [| ? l1']; simpl in K; injection K; intros K' ?; try exact (H0 _ _ _ K'); try exact (H0 _ _ _ (app_cons K' _)); subst; try (simpl in *; tauto); try (
    generalize (stack2 Hs1 (l1 := nil) (refl_equal _)); unfold stack2_inv; simpl; tauto
);
  try (generalize (kind Hs1);
unfold state_kind_inv; simpl; intros; invall;
destruct l2 as [ | sf2 ?]; try contradiction; (split; auto); destruct sf2; simpl in *; contradiction).

(* 5: constr cons *)
generalize (kind Hs1);
unfold state_kind_inv; simpl.
destruct hp.
intros; invall.
destruct k; invall.
 destruct k2; invall.
 destruct l2 as [ | sf2 l2'] ; try destruct sf2; simpl in *; tauto.
destruct l2 as [ | sf2 l2'] ; try destruct sf2; simpl in *; tauto.
destruct k2; invall.
 destruct l2 as [ | sf2 l2'] ; try destruct sf2; simpl in *; tauto.

(* 4: constr field cons struct *)
destruct hp;
generalize (kind Hs1);
unfold state_kind_inv; simpl; intros; invall.
destruct l2; try tauto.
split; auto.
destruct t0; simpl in H9; simpl; try contradiction.

(* Destruction *)

(* 3: destr array cons *)
generalize (kind Hs1);
unfold state_kind_inv; simpl; intros; invall.
destruct l1'.
 simpl in K'.
 injection K'; intros; subst; simpl.
 destruct l2; try contradiction.
 split; auto.
 destruct t; simpl; simpl in H8; contradiction.
simpl in K'.
injection K'; intros; subst.
exact (H0 _ _ _ (refl_equal _) H6).

(* 2: destr base cons, Kdestr *)
generalize (kind Hs1); destruct beta;
unfold state_kind_inv; simpl; intros; invall; subst; tauto.

(* 1: destr base cons, Kdestrother *)
generalize (kind Hs1);
unfold state_kind_inv; simpl.
destruct beta; intros; invall; subst.
destruct l1'.
 simpl in K'; injection K'; intros; subst.
 destruct l2; try contradiction.
 simpl.
 split; auto.
 destruct t; simpl in *; contradiction.
simpl in K'.
injection K'; intros; subst.
exact (H0 _ _ _ (refl_equal _) H1).
destruct l1'.
 simpl in K'; injection K'; intros; subst.
 destruct l2; try contradiction.
 simpl.
 split; auto.
 split; eauto.
 destruct t; simpl in *; contradiction.
simpl in K'.
injection K'; intros; subst.
exact (H0 _ _ _ (refl_equal _) H1).

(* le gros cas *)
destruct l2; try tauto.
revert t0 sf l1 l2 H.
destruct t0; try (intros; exact I).
Require Import PreservationStack2KConstr.
destruct inhpath; intros; eauto using goal.
Require Import PreservationStack2Kconstrarray.
intros; eauto using goal.
Require Import PreservationStack2Kconstrother.
destruct inhpath; intros; eauto using goal.
Require Import PreservationStack2Kconstrothercells.
intros; eauto using goal.
Require Import PreservationStack2Kdestr.
destruct inhpath; intros; eauto using goal.

Qed.

End Preservation.