Require Import Coqlib.
Require Import Cplusconcepts.
Require Import LibLists.
Require Import Tactics.
Require Import LibMaps.
Load Param.
Open Scope Z_scope.


Notation var := (ident) (only parsing).


Section Set_dynamic_type.

Variable A : ATOM.t .

Definition list_dynamic_type := (list ((positive * (array_path A * Z * (Class.Inheritance.t * list ident))) * ((Class.Inheritance.t * list ident) * (Class.Inheritance.t * list ident)))).    

Variable hierarchy : PTree.t (Class.t A).
Variable obj : positive.
Variable ar : array_path A.
Variable i : Z.

Variable h0 : Class.Inheritance.t.
Variable p0 : list ident.

Inductive set_dynamic_type_non_virtual_aux : Class.Inheritance.t -> list ident -> list ident -> list_dynamic_type -> list_dynamic_type -> Prop :=
| set_dynamic_type_non_virtual_aux_nil : forall h p h' p',
  (h', p') = concat (h0, p0) (h, p) ->  
  forall l,
  set_dynamic_type_non_virtual_aux h p nil l (((obj, (ar, i, (h', p'))), ((h0, p0), (h, p))) :: l)
| set_dynamic_type_non_virtual_aux_cons : forall p b,
  forall c, hierarchy ! b = Some c ->
  forall h l l1,
    set_dynamic_type_non_virtual_aux h (p ++ b :: nil)
    (
      (map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b) (filter (fun hb : _ * ident =>
    match hb with
      | (Class.Inheritance.Shared, _) => false
      | _ => true
    end
      ) (Class.super c)))
    )
    l l1 ->
    forall lb l2, set_dynamic_type_non_virtual_aux h p lb l1 l2 ->
      set_dynamic_type_non_virtual_aux h p (b :: lb) l l2
      .

Lemma set_dynamic_type_non_virtual_aux_func : forall h p l l1 l2,
  set_dynamic_type_non_virtual_aux h p l l1 l2 ->
  forall l2',
  set_dynamic_type_non_virtual_aux h p l l1 l2' ->
  l2 = l2'.
Proof.
  induction 1; inversion 1; subst; try congruence; eauto.
  replace c0 with c in * by congruence.
  assert (l1 = l3) by eauto.
  subst; eauto.
Qed.  

Lemma set_dynamic_type_non_virtual_aux_same : forall h p l l1 l2,
  set_dynamic_type_non_virtual_aux h p l l1 l2 ->
  forall h' p',
    (h', p') = concat (h0, p0) (h, p) ->
    assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) l2 = Some ((h0, p0), (h, p)).
Proof.
  induction 1; eauto.
   rewrite <- H.
   injection 1; intros; subst.
   simpl.
   destruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h', p')))
         (obj, (ar, i, (h', p')))
   ); congruence.
Qed.

Lemma set_dynamic_type_non_virtual_aux_other_cell : forall h p l l1 l2,
  set_dynamic_type_non_virtual_aux h p l l1 l2 ->
  forall obj' ar' i',
    (obj', ar', i') <> (obj, ar, i) ->
    forall h' p',
      assoc (@pointer_eq_dec _) (obj', (ar', i', (h', p'))) l2 =
      assoc (@pointer_eq_dec _) (obj', (ar', i', (h', p'))) l1.
Proof.
  induction 1; intros; simpl.
   destruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h', p')))
         (obj', (ar', i', (h'0, p'0)))
   ); congruence.
  eauto using trans_equal.
Qed.

Lemma set_dynamic_type_non_virtual_aux_other_path : forall h p l l1 l2,
  set_dynamic_type_non_virtual_aux h p l l1 l2 ->
 forall h' p',
(h', p') <> concat (h0, p0) (h, p) ->
(forall b', In b' l ->
  forall l', is_valid_repeated_subobject hierarchy (b' :: l') = true ->
    (h', p') <> concat (h0, p0) (h, p ++ b' :: l'))
    -> assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) l2 = assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) l1.
Proof.
  Opaque is_valid_repeated_subobject concat.
  induction 1; simpl.
   intros.
   destruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h', p')))
         (obj, (ar, i, (h'0, p'0)))
   ); congruence.
  intros.
  eapply trans_equal.
  eapply IHset_dynamic_type_non_virtual_aux2.
  assumption.
  eauto.
  eapply IHset_dynamic_type_non_virtual_aux1.
  eapply H3.
  auto.
  Transparent is_valid_repeated_subobject. simpl.
  rewrite H. trivial.
 intros.
 generalize (in_map_bases_elim H4).
 intro.
 rewrite app_ass.
 simpl.
 eapply H3.
 auto.
 simpl.
 rewrite H.
 destruct (
In_dec super_eq_dec (Class.Inheritance.Repeated, b') (Class.super c)
 ); try contradiction.
 assumption.
Qed.

Lemma set_dynamic_type_non_virtual_aux_same_path : forall h p l l1 l2,
  set_dynamic_type_non_virtual_aux h p l l1 l2 ->
  p <> nil ->
  forall b, In b l ->    
    forall l', is_valid_repeated_subobject hierarchy (b :: l') = true ->
      forall h' p',
        (h', p') = concat (h0, p0) (h, p ++ b :: l') ->
        assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) l2 = Some ((h0, p0), (h, p ++ b :: l'))
.
Proof.
  Opaque is_valid_repeated_subobject concat.
  induction 1; simpl; try tauto.
  destruct 2; eauto.
  subst.
  destruct (
   In_dec peq b0 lb
  ).
   eauto.
  intros.
  eapply trans_equal.
   eapply set_dynamic_type_non_virtual_aux_other_path.
   eassumption.
   rewrite H4.
   rewrite (app_nil_end p) at -1.
   eapply concat_other.
    assumption.
    congruence.
   rewrite H4.
   intros.
   eapply concat_other.
   assumption.
   unfold_ident_in_all; congruence.
  functional inversion H3; subst.
   eapply  set_dynamic_type_non_virtual_aux_same.
    eassumption.
    assumption.
  unfold_ident.
  clear H11.
  replace cl1 with c in * by congruence.
  transitivity (Some (h0, p0, (h, (p ++ b0 :: nil) ++ id2 :: l4))).
   eapply IHset_dynamic_type_non_virtual_aux1.
   destruct p; simpl; congruence.
   eapply in_map_bases_intro.
   assumption.
   assumption.
   rewrite app_ass.
   assumption.
  rewrite app_ass.
  reflexivity.
Qed.  

    
Inductive set_dynamic_type_non_virtual : Class.Inheritance.t -> list ident -> list_dynamic_type -> list_dynamic_type -> Prop :=
| set_dynamic_type_non_virtual_intro : forall p cn,
  last p = Some cn ->
  forall c, hierarchy ! cn = Some c ->
    forall h l1 l2,
      set_dynamic_type_non_virtual_aux h p
      (
        (map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b) (filter (fun hb : _ * ident =>
          match hb with
            | (Class.Inheritance.Shared, _) => false
            | _ => true
          end
        ) (Class.super c)))
      )
      l1 l2 ->
      set_dynamic_type_non_virtual h p l1 l2
      .

Lemma set_dynamic_type_non_virtual_func : forall h p l1 l2,
  set_dynamic_type_non_virtual h p l1 l2 ->
  forall l2',
    set_dynamic_type_non_virtual h p l1 l2' ->
    l2 = l2'.
Proof.
 inversion 1; inversion 1; subst.
 replace c0 with c in * by abstract congruence.
 eauto using set_dynamic_type_non_virtual_aux_func.
Qed.

Lemma set_dynamic_type_non_virtual_other_cell : forall h p l1 l2,
  set_dynamic_type_non_virtual h p l1 l2 ->
  forall obj' ar' i',
    (obj', ar', i') <> (obj, ar, i) ->
    forall h' p',
      assoc (@pointer_eq_dec _) (obj', (ar', i', (h', p'))) l2 =
      assoc (@pointer_eq_dec _) (obj', (ar', i', (h', p'))) l1.
Proof.
  inversion 1; subst; eauto using  set_dynamic_type_non_virtual_aux_other_cell.
Qed.

Lemma set_dynamic_type_non_virtual_other_path : forall h p from cn, 
  path hierarchy cn p from h ->
  forall h' p',
    (forall p1 to, path hierarchy to p1 cn Class.Inheritance.Repeated -> (h', p') <> concat (h0, p0) (concat (h, p) (Class.Inheritance.Repeated, p1))) ->
    forall l1 l2,
      set_dynamic_type_non_virtual h p l1 l2 ->
      assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) l2 =
      assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) l1.
Proof.
 inversion 3; subst.
 generalize (path_last H).
 intro.
 unfold_ident_in_all.
 replace cn0 with cn in * by abstract congruence.
 eapply set_dynamic_type_non_virtual_aux_other_path.
 eassumption.
 rewrite <- (concat_trivial_right H).
 eapply H0.
 eleft with (lt := nil).
 reflexivity.
 reflexivity.
 Transparent is_valid_repeated_subobject. simpl.
 rewrite H3.
 trivial.
 intros.
 case_eq (last (cn :: b' :: l')).
  intros.
  destruct (last_correct H8).
 cut ( (h, p ++ b' :: l') = (concat (h, p) (Class.Inheritance.Repeated, cn :: b' :: l')) ).
 unfold_ident.
 intro.
 rewrite H9.
 eapply H0.
 eleft.
 reflexivity.
 eassumption.
 simpl.
 rewrite H3.
 destruct (
In_dec super_eq_dec (Class.Inheritance.Repeated, b') (Class.super c)
 ).
  assumption.
 destruct n.
 eauto using in_map_bases_elim.
 Transparent concat. simpl.
 rewrite (path_last H).
 destruct (peq cn cn); unfold_ident; congruence.
 intro.
 refine (False_rect _ (last_nonempty _ H8)).
 congruence.
Qed.

Lemma set_dynamic_type_non_virtual_same_path : forall h p from cn, 
  path hierarchy cn p from h ->
  forall p1 to, path hierarchy to p1 cn Class.Inheritance.Repeated ->
    forall h' p',
      (h', p') = concat (h0, p0) (concat (h, p) (Class.Inheritance.Repeated, p1)) ->
      forall l1 l2,
        set_dynamic_type_non_virtual h p l1 l2 ->
        assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) l2 =
        Some ((h0, p0), concat (h, p) (Class.Inheritance.Repeated, p1))
        .
Proof.
  inversion 4; subst.
  generalize (path_last H).
  intro.
  unfold_ident_in_all.
  replace cn0 with cn in * by abstract congruence.
  inversion H0; subst.
  functional inversion H9; subst.
   replace cl1 with c in * by abstract congruence.
   revert H1.
   erewrite concat_trivial_right.   
   intro.
   eapply set_dynamic_type_non_virtual_aux_same.
   eassumption.
   assumption.
   eassumption.
  revert H1.
  simpl.
  rewrite (path_last H).
  destruct (peq cn cn); try congruence.
  intro.
  clear H15.
  replace cl1 with c in * by abstract congruence.
  eapply set_dynamic_type_non_virtual_aux_same_path.
  eassumption.
  eauto using path_nonempty.
  eauto using in_map_bases_intro.
  assumption.
  assumption.
Qed.

Inductive set_dynamic_type_virtual_aux : list ident -> list_dynamic_type -> list_dynamic_type -> Prop :=
| set_dynamic_type_virtual_aux_nil : forall l,
  set_dynamic_type_virtual_aux nil l l
| set_dynamic_type_virtual_aux_cons : forall b l1 l2,
  set_dynamic_type_non_virtual Class.Inheritance.Shared (b :: nil) l1 l2 ->
  forall l l3,
    set_dynamic_type_virtual_aux l l2 l3 ->
    set_dynamic_type_virtual_aux (b :: l) l1 l3.

Lemma set_dynamic_type_virtual_aux_func : forall l l1 l2,
  set_dynamic_type_virtual_aux l l1 l2 ->
  forall l2', set_dynamic_type_virtual_aux l l1 l2' ->
    l2 = l2'.
Proof.
  induction 1; inversion 1; subst; trivial.
  generalize (set_dynamic_type_non_virtual_func H H4).
  intro; subst; eauto.
Qed.

Lemma set_dynamic_type_virtual_aux_other_cell : forall l l1 l2,
  set_dynamic_type_virtual_aux l l1 l2 ->
  forall obj' ar' i',
    (obj', ar', i') <> (obj, ar, i) ->
    forall h' p',
      assoc (@pointer_eq_dec _) (obj', (ar', i', (h', p'))) l2 =
      assoc (@pointer_eq_dec _) (obj', (ar', i', (h', p'))) l1.
Proof.
  induction 1; eauto using  set_dynamic_type_non_virtual_other_cell, trans_equal.
Qed.


Section Virtual.

Variable dt : ident.

Lemma set_dynamic_type_virtual_aux_other_path : forall l l1 l2,
  set_dynamic_type_virtual_aux l l1 l2 ->
  (forall b, In b l -> path hierarchy b (b :: nil) dt Class.Inheritance.Shared) ->
  forall h' p',
    (forall b, In b l -> forall p'' to, path hierarchy to (b :: p'') b Class.Inheritance.Repeated -> (h', p') <> (Class.Inheritance.Shared, b :: p'')) ->
    assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) l2 =
    assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) l1.
Proof.
 induction 1; trivial.
 intros.
 eapply trans_equal.
 eapply IHset_dynamic_type_virtual_aux; eauto.
 eapply set_dynamic_type_non_virtual_other_path.
 eauto.
 intros.
 simpl.
 unfold plus.
 destruct p1.
  destruct (path_nonempty H3 (refl_equal _)).
 simpl.
 inversion H3; subst.
 injection H4; intros; subst.
 destruct (peq b b); subst; eauto.
 assumption.
Qed.

Lemma set_dynamic_type_virtual_aux_same_path :
  forall l l1 l2,
    set_dynamic_type_virtual_aux l l1 l2 ->
    (forall b, In b l -> path hierarchy b (b :: nil) dt Class.Inheritance.Shared) ->
    forall b, In b l ->
      forall to p, path hierarchy to p b Class.Inheritance.Repeated ->
        assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, p))) l2 =
        Some ((h0, p0), (Class.Inheritance.Shared, p)).
       
Proof.
 induction 1. 
  simpl; tauto.
 destruct 2; eauto.
 subst.
 destruct (In_dec peq b0 l); eauto.
 intros.
 eapply trans_equal.
 eapply set_dynamic_type_virtual_aux_other_path.
 eassumption.
 eauto.
  inversion H2; intros; unfold_ident_in_all; congruence.  
  cut ((Class.Inheritance.Shared, p) = (concat (Class.Inheritance.Shared, b0 :: nil) (Class.Inheritance.Repeated, p))).
  intro.
  rewrite H3 at -1.
 eapply set_dynamic_type_non_virtual_same_path.
 eauto.
 eauto.
 assumption.
 eassumption.
 simpl.
 unfold plus.
 destruct p.
  destruct (path_nonempty H2).
  trivial.
 simpl.
 inversion H2; subst.
 destruct (peq b0 i0); congruence.
Qed.

End Virtual.

Inductive set_dynamic_type : list_dynamic_type -> list_dynamic_type -> Prop :=
| set_dynamic_type_intro : forall cn,
  last p0 = Some cn ->
  forall c, hierarchy ! cn = Some c ->
    forall v, vborder_list hierarchy (Class.super c) v ->
      forall l1 l2,
        set_dynamic_type_virtual_aux v l1 l2 ->
        forall l3,
          set_dynamic_type_non_virtual Class.Inheritance.Repeated (cn :: nil) l2 l3 ->
          set_dynamic_type l1 l3.

Lemma set_dynamic_type_func : forall l1 l2,
  set_dynamic_type l1 l2 ->
  forall l2', set_dynamic_type l1 l2' -> l2 = l2'.
Proof.
  induction 1; inversion 1; subst; trivial.
  replace cn0 with cn in * by abstract congruence.
  replace c0 with c in * by abstract congruence.
  generalize (vborder_list_func H1 H7).
  intro; subst.
  generalize (set_dynamic_type_virtual_aux_func H8 H2). 
  intro; subst;  eauto using set_dynamic_type_non_virtual_func.
Qed.

Lemma set_dynamic_type_other_cell : forall l1 l2,
  set_dynamic_type l1 l2 ->
  forall obj' ar' i',
    (obj', ar', i') <> (obj, ar, i) ->
    forall h' p',
      assoc (@pointer_eq_dec _) (obj', (ar', i', (h', p'))) l2 =
      assoc (@pointer_eq_dec _) (obj', (ar', i', (h', p'))) l1.
Proof.
  induction 1; eauto using  set_dynamic_type_non_virtual_other_cell, set_dynamic_type_virtual_aux_other_cell, trans_equal.
Qed.

(** for the remaining, we NEED a well-formed hierarchy. Please see IntermSetDynTypeWf. *)

Section Subtract.

Variable U : Type.
Hypothesis U_eq_dec : forall u1 u2 : U, {u1 = u2} + {u1 <> u2}.

Lemma subtract (lshort llong : list U) : {
  lcompl | llong = lshort ++ lcompl
} + {
  forall lcompl, llong <> lshort ++ lcompl
}.
Proof.
 induction lshort; simpl; eauto.
 destruct llong.
  right; congruence.
 destruct (U_eq_dec u a).
  2 : right; congruence.
 subst.
 destruct (IHlshort llong).
  destruct s; subst; eauto.
 right; intros; intro.
 injection H.
 eapply n.
Qed.

End Subtract.

Variable is_primary_path : list ident -> bool.

Lemma primary_ancestor_dec : forall h' p', {
  p'' : _ & {a | last p' = Some a /\ is_primary_path (a :: p'') = true /\
    (h0, p0) = concat (h', p') (Class.Inheritance.Repeated, a :: p'')}
} + {
  forall a, last p' = Some a -> forall p'', is_primary_path (a :: p'') = true ->
    (h0, p0) = concat (h', p') (Class.Inheritance.Repeated, a :: p'') -> False
}.
Proof.
  intros.
  case_eq (last p').
   2 : right; intros; discriminate.
  intros.
  destruct (Class.Inheritance.eq_dec h' h0).
   2 : right; simpl; intros; congruence.
  subst.
  destruct (subtract peq p' p0).
   destruct s.
   subst.
   case_eq (is_primary_path (i0 :: x)).
    intros.
    left.
    exists x.
    exists i0.
    split; trivial.
    split; trivial.
    simpl.
    rewrite H.
    destruct (peq i0 i0).
     trivial.
    congruence.
   intros.
   right.
   simpl.
   rewrite H.
   injection 1; intro; subst.
   destruct (peq a a); try congruence.
   intros.
   injection H3.
   intro.
   generalize (app_reg_l H4).
   congruence.
  right.
  injection 1; intro; subst.
  simpl.
  rewrite H.
  destruct (peq a a); try congruence.
  intros.
  injection H2.
  apply n.
Qed.

Function non_primary_ancestor (objarihphphp : 
  ((ident * (array_path A * Z * (Class.Inheritance.t * list ident))) *
    ((Class.Inheritance.t * list ident) * (Class.Inheritance.t * list ident)))
) : bool :=
  match objarihphphp with
    | ((obj', (ar', i', (h', p'))), _) =>
      if prod_eq_dec (prod_eq_dec peq (@array_path_eq_dec _)) Z_eq_dec (obj', ar', i') (obj, ar, i)
        then
          if primary_ancestor_dec h' p' then false else true
        else true
  end.

Definition erase_non_primary_ancestor_dynamic_type (l : list_dynamic_type) : list_dynamic_type := filter non_primary_ancestor l.

Lemma erase_non_primary_ancestor_other_cell : forall obj' ar' i' h' ,
  (obj', ar', i') <> (obj, ar, i) ->
  forall l1 p',
    assoc (@pointer_eq_dec _) (obj', (ar', i', (h', p'))) (erase_non_primary_ancestor_dynamic_type l1) =
      assoc (@pointer_eq_dec _) (obj', (ar', i', (h', p'))) l1.
Proof.
 intros.
 revert obj' ar' i' h' H p'.
 unfold erase_non_primary_ancestor_dynamic_type.
 induction l1; simpl.
  trivial.
 intros.
 destruct a.
 destruct (pointer_eq_dec (A:=A) p (obj', (ar', i', (h', p')))).
 var (p, p1).
 functional induction (non_primary_ancestor v); try congruence.
 simpl.
 destruct (
   pointer_eq_dec (A:=A) (obj'0, (ar'0, i'0, (h'0, p'0)))
   (obj', (ar', i', (h', p')))
 ); congruence.
 destruct (non_primary_ancestor (p, p1)); auto.
 simpl.
 destruct (
   pointer_eq_dec (A:=A) p (obj', (ar', i', (h', p')))
 ); try congruence.
 auto.
Qed.

Corollary set_dynamic_type_strong_other_cell : forall l1 l2,
  set_dynamic_type (erase_non_primary_ancestor_dynamic_type l1) l2 ->
  forall obj' ar' i',
    (obj', ar', i') <> (obj, ar, i) ->
    forall h' p',
      assoc (@pointer_eq_dec _) (obj', (ar', i', (h', p'))) l2 =
      assoc (@pointer_eq_dec _) (obj', (ar', i', (h', p'))) l1.
Proof.
  intros.
  eapply trans_equal.
  eapply set_dynamic_type_other_cell; eauto.
  eapply erase_non_primary_ancestor_other_cell.
  congruence.
Qed.

Lemma erase_non_primary_ancestor_same : forall p' a, last p' = Some a -> forall p'', is_primary_path (a :: p'') = true -> forall h', (h0, p0) = concat (h', p') (Class.Inheritance.Repeated, a :: p'') ->
  forall l1,
    assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) (erase_non_primary_ancestor_dynamic_type l1) = None.
Proof.
 intros.
  case_eq (
    assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (h', p')))
    (erase_non_primary_ancestor_dynamic_type l1)
  ); auto.
  intros.
  generalize (assoc_In H2).
  unfold erase_non_primary_ancestor_dynamic_type.
  intros.
  destruct (let (K, _) := filter_In _ _ _ in K H3).
  functional inversion H5; try congruence.
   clear H13 H14.
   subst.
   edestruct _x1; eauto.
  destruct _x0; trivial.
Qed.

Lemma erase_non_primary_ancestor_other : forall h' p',
 (forall a, last p' = Some a -> forall p'', is_primary_path (a :: p'') = true -> (h0, p0) <> concat (h', p') (Class.Inheritance.Repeated, a :: p'')) ->
  forall l1,
    assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) (erase_non_primary_ancestor_dynamic_type l1) = 
    assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) (l1).
Proof.
 intros.
 unfold erase_non_primary_ancestor_dynamic_type.
 induction l1; simpl; auto.
 destruct a.
 destruct (
   pointer_eq_dec (A:=A) p (obj, (ar, i, (h', p')))
 ).
  var (p, p1).
  functional induction (non_primary_ancestor v); try congruence.
  clear e1 e2.
  destruct _x1.
  destruct s.
  destruct a.
  destruct H2.
  subst.
  injection H0; intros; subst.
  edestruct H; eauto.
 simpl.
 clear e1 e2.
 destruct (
 pointer_eq_dec (A:=A) (obj', (ar', i', (h'0, p'0)))
         (obj, (ar, i, (h', p')))
 ); congruence.
 clear e1.
 simpl.
 destruct (
pointer_eq_dec (A:=A) (obj', (ar', i', (h'0, p'0)))
         (obj, (ar, i, (h', p')))
 ); congruence.
destruct (non_primary_ancestor (p, p1)); auto.
simpl.
destruct (
  pointer_eq_dec (A:=A) p (obj, (ar, i, (h', p')))
); auto.
congruence.
Qed.
 
End Set_dynamic_type.

