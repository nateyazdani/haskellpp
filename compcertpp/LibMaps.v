Require Export Maps.
Require Import Coqlib.
Require Export LibPos.
Load Param.

Section Maxindex.
Variable A: Type.

Theorem max_index : forall t : PTree.t A,
  {i | forall j, t ! j <> None -> Plt j i}.
Proof.
 intros.
 cut {i | forall j x, In (j, x) (PTree.elements t) -> Plt j i}.
  destruct 1.
  exists x.
  intros.
  case_eq (t ! j).
   intros.
   generalize (PTree.elements_correct  _ _   H0).
   eauto.
   congruence.
  generalize (PTree.elements t).
  clear t.
  induction l ; simpl.
  exists 1%positive.
  tauto.
  destruct IHl.
  destruct a.
  destruct (plt  p0 x).
   exists x.
   inversion 1.
   congruence.
   eauto.
  exists (Psucc p0).
  inversion 1.
  injection H0 ; intros ; subst.
  apply Plt_succ.
  generalize (p _ _ H0).
  intros.
  eapply Plt_trans with x.
  assumption.
  unfold Plt in *.
  rewrite Zpos_succ_morphism.
  unfold Zsucc.
  omega.
Qed.

End Maxindex.

(* Et maintenant, construisons une table progressive. *)

Section Progressive.

Variables A : Type. 

Variable P : positive -> A -> Type.

Hypothesis f : forall
  n
  (t : PTree.t A)
  (H_nonempty : forall i, Plt i n -> t ! i <> None)
  (H_property : forall i c, t ! i = Some c -> P i c),
  {y : _ & P n y}.
 
Theorem progressive : forall n,
  {t : _ &
    ((forall i, Plt i n -> t ! i <> None) *
    forall i c, t ! i = Some c -> P i c)%type}.
Proof.
intros.
destruct (peq n 1%positive).
 subst.
 exists (@PTree.empty A).
  split.
  intros.
  unfold Plt in H.
  destruct i ; compute in H ; congruence.
  intros. 
  rewrite PTree.gempty in H.
  congruence.
 assert (Zpos n > 0) by (compute ; trivial).
 assert (Zpos n <> 1) by congruence.
 assert (Zpos n - 1 > 0) by omega.
 revert H1.
 case_eq (Zpos n - 1).
  intros ; omegaContradiction.
  Focus 2. 
   intros.
   apply False_rect.
   compute in H2.
   congruence.
  intros.
  assert (n = Psucc p).
   cut (Zpos n = Zpos (Psucc p)).
   congruence.
   rewrite Psucc_Zsucc.
   unfold Zsucc.
   omega.
   subst.
  clear H2 n0 H H0 H1.  
cut (
  forall m t, Plt m (Psucc p) ->
      (forall i, Plt i m -> t ! i <> None) ->
      (forall i c, t ! i = Some c -> P i c)
      ->
      {t' : _ &
        ((forall i, Plt i (Psucc p) -> t' ! i <> None) *
        forall i c, t' ! i = Some c -> P i c)%type}
).
 intros.
 apply (X 1%positive (@PTree.empty A)).
  unfold Plt.
  rewrite Psucc_Zsucc.
  unfold Zsucc.
  assert (Zpos p > 0) by (compute; trivial). 
  omega.
 intros.      
 unfold Plt in H.
 destruct i ; compute in H ; congruence.
 intros.
 rewrite PTree.gempty in H.
 congruence.
 induction m using (well_founded_induction_type (bounded_gt_wf (Psucc p))).
 intros.
 generalize (f H0 X0).
 destruct 1. 
 assert (Ple (Psucc m) (Psucc p)).
 unfold Plt in H.
 unfold Ple.
 repeat rewrite Psucc_Zsucc in *.
 unfold Zsucc in *.
 omega.
 assert (forall i, Plt i (Psucc m) -> ((PTree.set m x t) ! i <> None)).
  intros.
  destruct (peq i m).
   subst.
   rewrite PTree.gss.
   congruence.
  rewrite PTree.gso.
  apply H0.
  unfold Plt in *.
  rewrite Psucc_Zsucc in *.
  unfold Zsucc in *.
  assert (Zpos i <> Zpos m) by congruence.  
  omega.
  assumption.
 assert (forall i c, (PTree.set m x t) ! i = Some c -> P i c).
  intros i c.
  destruct (peq m i).
   subst.
   rewrite PTree.gss.
   congruence.
  rewrite PTree.gso.
  auto.
  auto.
 destruct (peq m p).
  subst.
  exists (PTree.set p x t).
  auto.
 assert (Plt (Psucc m) (Psucc p)).
 unfold Ple, Plt in *.  
 repeat rewrite Psucc_Zsucc in *.
 unfold Zsucc in *.
 assert (Zpos m <> Zpos p) by congruence.
 omega.
 assert (bounded_gt (Psucc p) (Psucc m) m). 
  constructor.
  apply Plt_succ.
  assumption.
 eapply X.
 eassumption.
 assumption.
 eassumption.
 assumption.
Qed.

End Progressive.

Require Import LibLists.

Section Assoc_to_ptree.

Variables K U V : Type.
Variable f : K -> U -> option (positive * V).

Function assoc_to_ptree (l : list (K * U)) (t : PTree.t V) {struct l} : PTree.t V :=
  match l with
    | nil => t
    | (k, u) :: l' =>
      match f k u with
        | None => assoc_to_ptree l' t
        | Some (i, v) => PTree.set i v (assoc_to_ptree l' t)
      end
  end.

Hypothesis f_func : forall k u i v, f k u = Some (i, v) -> forall k' u' v', f k' u' = Some (i, v') -> k = k' \/ v = v'.

Hypothesis K_eq_dec : forall k1 k2 : K, {k1 = k2} + {k1 <> k2}.

Theorem assoc_to_ptree_some : forall l k u,
  assoc K_eq_dec k l = Some u ->
  forall i v, f k u = Some (i, v) ->
  forall t,
    (assoc_to_ptree l t) ! i = Some v.
Proof.
  induction l; simpl.
   intros; discriminate.
  destruct a.
  intros k0 u0.
  destruct (K_eq_dec k k0).
   injection 1; intro; subst.
   intros until 1.
   rewrite H0.
   intro.
   rewrite PTree.gss.
   trivial.
  intros.
  case_eq (f k u).
   destruct p.
   intros.
   destruct (peq i p).
    subst.
    destruct (f_func H1 H0).
     contradiction.
    subst.
    rewrite PTree.gss.
    trivial.
   rewrite PTree.gso.
   eauto.
   assumption.   
  intros; eauto.
Qed.

Theorem assoc_to_ptree_other : forall l i, (forall k u v, f k u <> Some (i, v)) ->
  forall t,
    (assoc_to_ptree l t) ! i = t ! i.
Proof.
 induction l; simpl.
  auto.
 destruct a.
 intros.
 case_eq (f k u); eauto.
 destruct p.
 intros.
 rewrite PTree.gso.
 eauto.
 intro; subst.
 destruct (H _ _ _ H0).
Qed.

End Assoc_to_ptree.

Section Ptree_to_ptree.

Variable U : Type.

Lemma ptree_assoc : forall t i (u : U), t ! i = Some u -> assoc peq i (PTree.elements t) = Some u.
Proof.
   intros.
   generalize (In_split _ _ (PTree.elements_correct _ _ H)).
   clear H.
   destruct 1.
   destruct H.  
   revert i u x x0 H.
   generalize (PTree.elements_keys_norepet t).
   generalize (PTree.elements t).
   clear t.
   induction l; simpl.
    intros.
    destruct x; discriminate.
   destruct a; simpl.
   inversion 1; subst.
   destruct x.
    simpl.
    injection 1; intros; subst.
    destruct (peq i i); congruence.
   injection 1; intros; subst.
   rewrite (IHl H3 _ _ _ _ (refl_equal _)).
   destruct (peq p i); try congruence.
   subst.
   destruct H2.
   rewrite map_app.
   simpl.
   eauto using in_or_app.
Qed.

Variable V : Type.
Variable f : positive -> U -> option (positive * V).

Definition ptree_to_ptree (tu : PTree.t U) (tv : PTree.t V) : PTree.t V :=
  assoc_to_ptree f (PTree.elements tu) tv.

Hypothesis f_func : forall k u i v, f k u = Some (i, v) -> forall k' u' v', f k' u' = Some (i, v') -> k = k' \/ v = v'.

Theorem ptree_to_ptree_some : forall tu k u,
  tu ! k = Some u ->
  forall i v, f k u = Some (i, v) ->
  forall tv,
    (ptree_to_ptree tu tv) ! i = Some v.
Proof.
  unfold ptree_to_ptree.
  intros.
  eapply assoc_to_ptree_some with (K_eq_dec := peq); eauto using ptree_assoc.
Qed.

Theorem ptree_to_ptree_other : forall l i, (forall k u v, f k u <> Some (i, v)) ->
  forall t,
    (ptree_to_ptree l t) ! i = t ! i.
Proof.
 unfold ptree_to_ptree; eauto using assoc_to_ptree_other.
Qed.

End Ptree_to_ptree.
