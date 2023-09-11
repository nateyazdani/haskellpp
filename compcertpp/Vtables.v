Require Import Coqlib.
Require Import Cplusconcepts.
Require Import CplusWf.
Require Import LibLists.
Require Import Tactics.
Require Import LibMaps.
Require Import Relations.
Require Import LayoutConstraints.
Require Import Target.
Require Import CPP.
Require Import Dynamic.
Require Import DynamicWf.
Require Import Wellfounded.
Load Param.
Open Scope Z_scope.

Section Ass.

Variable A : Type.

Hypothesis A_eq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}.


Section Attach.

  Variable B : Type.

  Variable f : A -> B.

  Definition attach a := (a, f a).

  Lemma assoc_attach_some : forall l a, In a l ->
    assoc A_eq_dec a (map attach l) = Some (f a).
  Proof.
    induction l; simpl; try tauto.
    intro.
    destruct (A_eq_dec a a0); try congruence.
    destruct 1; try contradiction.
    eauto.
  Qed.

  Lemma assoc_attach_none : forall l a, (In a l -> False) ->
    assoc A_eq_dec a (map attach l) = None.
  Proof.
    induction l; simpl; auto.
    intros.
    destruct (A_eq_dec a a0).
     tauto.
    eauto.
  Qed.

End Attach.


Section Remove.

Lemma In_remove : forall l a a', a <> a' -> (In a' l <-> In a' (remove A_eq_dec a l)).
Proof.
  induction l; simpl.
   tauto.
  intros.
  destruct (A_eq_dec a0 a).
   subst.
   split.
    destruct 1.
     contradiction.
    eapply IHl; eauto.
   right.
   eapply IHl; eauto.
  split.
  destruct 1.
   subst; auto.
  right.
  eapply IHl; eauto.
  destruct 1.
   auto.
  right; eapply IHl; eauto.
Qed.

Function remove_dup (l : list A) : list A :=
  match l with
    | nil => nil
    | a :: q => a :: (remove A_eq_dec a (remove_dup q))
  end.

Lemma remove_dup_In : forall l a, In a l <-> In a (remove_dup l).
Proof.
  intro.
  functional induction (remove_dup l).
   tauto.
  intro; split.
   destruct (A_eq_dec a a0).
    subst; auto.
   destruct 1.
    contradiction.
   right.
   refine  (let (H, _) := In_remove _ _ in H _).
   assumption.
   eapply IHl0.
   assumption.
  destruct (A_eq_dec a a0).
   subst; auto.
  destruct 1.
   contradiction.
  right.
  eapply IHl0.
  eapply In_remove.
  eassumption.
  assumption.
Qed.
  
End Remove.

Section Initass.

Variable B : Type.

Variable f : A -> option B.

Function initass (l : list A) : list (A * B) :=
  match l with
    | nil => nil
    | a :: q =>
      match f a with
        | None => initass q
        | Some b => (a, b) :: initass q
      end
  end.

Lemma initass_assoc_none : forall l a, (In a l -> False) ->
  assoc A_eq_dec a (initass l) = None.
Proof.
  intro.
  functional induction (initass l); simpl.
   trivial.
  eauto.
  intros.
  destruct (A_eq_dec a a0); eauto.
  destruct H; auto.
Qed.

Lemma initass_assoc : forall l a, In a l ->
  assoc A_eq_dec a (initass l) = f a.
Proof.
  intro.
  functional induction (initass l); simpl.
   tauto.
  destruct 1.
   subst.
   destruct (In_dec A_eq_dec a0 q).
    eauto.
   rewrite e0; eauto using initass_assoc_none.
  eauto.
  intros.
  destruct (A_eq_dec a a0).
   congruence.
  destruct H; eauto.
  contradiction.
Qed.

End Initass.

Section Remass.
  
Variable a : A.

Variable B : Type.

Function remass (l : list (A * B)) : list (A * B) :=
  match l with
    | nil => nil
    | (a', b') :: q => if A_eq_dec a' a then remass q else (a', b') :: remass q
  end.

Lemma remass_assoc_same : forall l, assoc A_eq_dec a (remass l) = None.
Proof.
  intro.
  functional induction (remass l); simpl; auto.
  rewrite e0; auto.
Qed.

Lemma remass_assoc_other : forall l a', a <> a' -> assoc A_eq_dec a' (remass l) = assoc A_eq_dec a' l.
Proof.
  intro.
  functional induction (remass l); simpl; auto.
  clear e0.
  subst.
  intros.
  rewrite (IHl0 _ H).
  destruct (A_eq_dec a a'); congruence.
  intros.
  rewrite (IHl0 _ H).
  trivial.
Qed.

End Remass.

Section Mapass.

Variables B C : Type.

Variable f : A -> B -> option C.

Function mapass (l : list (A * B)) : list (A * C) :=
  match l with
    | nil => nil
    | (a, b) :: q =>
      match f a b with
        | Some c => (a, c) :: mapass q
        | None => remass a (mapass q)
      end
  end.

Lemma mapass_none : forall l a,
  assoc A_eq_dec a l = None ->
  assoc A_eq_dec a (mapass l) = None.
Proof.
  intro.
  functional induction (mapass l); simpl.
   trivial.
  intro.
  destruct (A_eq_dec a a0); try congruence.
  eauto.
  intro.
  destruct (A_eq_dec a a0); try congruence.
  intros.
  erewrite (remass_assoc_other); eauto.
Qed.

Lemma mapass_some : forall l a b,
  assoc A_eq_dec a l = Some b ->
  assoc A_eq_dec a (mapass l) = f a b.
Proof.
  intro.
  functional induction (mapass l); simpl.
   congruence.
  intro.
  destruct (A_eq_dec a a0).
   congruence.
  auto.
  intro.
  destruct (A_eq_dec a a0).
   injection 1; intros; subst.
   rewrite e0; eauto using remass_assoc_same.
  erewrite remass_assoc_other; eauto.
Qed.

End Mapass.

End Ass.


      (** Construction of virtual tables *)

Section Common.

  Variable A : ATOM.t.

  Variable hierarchy : PTree.t (Class.t A).

  Hypothesis Hhier : Well_formed_hierarchy.prop hierarchy.


      (** Dynamic cast for non-bases : show that if C is a class defining some behaviour (success or failure) to dyncast to X,
           if X is not a base of C, then, for any base B of C, the dynamic cast to X has the same behaviour.
      *)  


      Lemma non_base_dyncast_stable : forall real c x, (forall h p, path hierarchy x p c h -> False) ->
      forall h p h' p',
         dynamic_cast hierarchy real h p c x h' p' ->
         forall b l, path hierarchy b (c :: l) c Class.Inheritance.Repeated ->
         dynamic_cast hierarchy real h (p ++ l) b x h' p'.
      Proof.
        inversion 2; subst.
        (* derived-to-base : absurd *)
        destruct (H _ _ H2).

        (* base-to-derived, non-virtual *)
        intros.
        assert (path hierarchy b (p0 ++ l) x Class.Inheritance.Repeated).
         eapply path_concat.
         eassumption.
         eassumption.
         simpl.
         rewrite (path_last H2).
         destruct (peq c c); congruence.
        eapply dynamic_cast_downcast.
        assumption.
        eassumption.
        inversion H2; subst.
        revert H3.
        simpl.
        rewrite (path_last H1).
        destruct (peq x x); try congruence.
        rewrite <- app_ass.
        congruence.
       intros.
       eapply dynamic_cast_crosscast.
       eapply path_concat.
       eexact H1.
       eassumption.
       simpl.
       rewrite (path_last H1).
       destruct (peq c c); congruence.
       assumption.
       assumption.
Qed.

      Lemma non_base_dyncast_stable_recip : forall real c x, (forall h p, path hierarchy x p c h -> False) ->
         forall b l, path hierarchy b (c :: l) c Class.Inheritance.Repeated ->
         forall h p,
         path hierarchy c p real h ->
         forall h' p',
         dynamic_cast hierarchy real h (p ++ l) b x h' p' ->
         dynamic_cast hierarchy real h p c x h' p'.
      Proof.
        inversion 4; subst.
        (* derived-to-base : absurd *)
        generalize (path_concat H0 H4).
        case_eq (concat (Class.Inheritance.Repeated, c :: l)
   (k, p0)
        ).
        intros.
        generalize (H8 _ _ (refl_equal _)).
        intro.
        destruct (H _ _ H9).
       (* base-to-derived *)
       generalize (path_concat H1 H0).
       simpl.
       rewrite (path_last H1).
       destruct (peq c c); try congruence.
       intros.
       generalize (H6 _ _ (refl_equal _)).
       intros.
       inversion H4; subst.
       revert H5.
       simpl.
       rewrite (path_last H3).
       destruct (peq x x); try congruence.
       injection 1; intros; subst.
       destruct (last_correct (path_last H3)).
       subst.
       revert H8.
       rewrite app_ass.
       simpl.
       destruct (last_correct (path_last H1)).
       subst.
       intros.
       assert (In c (x0 ++ x :: lf)).
       rewrite <- H8.
       eauto using in_or_app.
       destruct (in_app_or _ _ _ H11).
        destruct (member_extract H12).
        invall; subst.
        assert (
          is_valid_repeated_subobject hierarchy ((x2 ++ c :: x3) ++ x :: nil) = true
        ).
          generalize (path_path0 H3).
          inversion 1; congruence.
        rewrite app_ass in H13.
        simpl in H13.
        generalize (is_valid_repeated_subobject_split_right H13).
        intro.
        destruct (H Class.Inheritance.Repeated ((c :: x3) ++ x :: nil)).
        eleft.
        reflexivity.
        reflexivity.
        assumption.
     destruct (member_extract H12).
     invall.
     assert (exists l', x :: l' = x2 ++ c :: nil).
       destruct x2; simpl in *.
       exists nil.
        congruence.
       injection H14; intros; subst.
       esplit.
       reflexivity.
      invall.        
     assert (path hierarchy c (x2 ++ c :: nil) x Class.Inheritance.Repeated).
     eleft.
     symmetry; eassumption.
     reflexivity.
     generalize H10.
     rewrite H14.
     intro.
     eauto using is_valid_repeated_subobject_split_left.
    eapply dynamic_cast_downcast.
    assumption.
    eassumption.
    simpl.
    rewrite <- H15.
    simpl.
    rewrite last_complete.
    destruct (peq x x); try congruence.
    assert (x4 ++ x3 = lf).
     cut ((x :: x4) ++ x3 = x :: lf).
     simpl; congruence.
     rewrite H15.
     rewrite app_ass.
     simpl.
     auto.
    subst.    
    rewrite app_ass.
    simpl.
    rewrite H15.
    cut (x1 = x0 ++ x2).
     rewrite <- app_ass.
     congruence.
    revert H8.
    rewrite H14.
    rewrite app_ass.
    simpl.
    rewrite <- app_ass.
    assert (is_valid_repeated_subobject hierarchy (x1 ++ c :: nil) = true).
      generalize (path_path0 H1).
      inversion 1; congruence.
    inversion H0; subst.
    generalize (is_valid_repeated_subobject_join H8 H18).
    intro.
    generalize (Well_formed_hierarchy.is_valid_repeated_subobject_sorted Hhier H19).
    intros.
    refine (_ (sorted_decomp_unique _ (sorted_elim _ H20) (refl_equal _) H21)).
    congruence.
    apply Plt_irrefl.
    intros; eauto using Plt_trans.
   (* cross *)
   eapply dynamic_cast_crosscast.
   assumption.
   assumption.
   assumption.

Qed.

Notation is_dynamic := (Dynamic.is_dynamic).

Variable COP : CPPOPTIM A.

Definition OP := Optim COP.

Variable vop' : valop' A Z.

Hypothesis vop'_pos : forall k t, 0 < vop' k t.     

Function valtype_of_typ (ty : Typ.t A) : valtype A :=
  match ty with
    | Typ.atom a => tyAtom a
    | Typ.class _ => tyPtr _
  end.

Definition typ_data k ty := vop' k (valtype_of_typ ty).

Remark typ_pos : forall k ty, 0 < typ_data k ty.
Proof.
  unfold typ_data; simpl; eauto.
Qed.

Definition PF := Platform (typ_pos Size) (typ_pos Align) (vop'_pos Size (tyVptr _)) (vop'_pos Align (tyVptr _)).
  
  Variable offsets : PTree.t (LayoutConstraints.t A).
      
      Hypothesis intro : forall ci o, offsets ! ci = Some o -> class_level_prop OP PF offsets hierarchy ci o.
      
      Hypothesis guard : forall ci, offsets ! ci <> None -> hierarchy ! ci <> None.

      Hypothesis exis: forall ci, hierarchy ! ci <> None -> offsets ! ci <> None. 

      Hypothesis empty_prop : forall (ci : positive) (oc : LayoutConstraints.t A),
        offsets ! ci = Some oc ->
        disjoint_empty_base_offsets OP offsets hierarchy ci oc.


Lemma primary_subobject_offset : forall l d,
  is_primary_path offsets (d :: l) = true ->
  forall h p hr pr h0 p0, (h0, p0) = concat (hr, pr) (h, p) ->
    last p = Some d ->
    forall h_ p_, (h_, p_) = concat (hr, pr) (h, p ++ l) ->
      forall hyperreal z, subobject_offset offsets hyperreal p0 = Some z ->
        subobject_offset offsets hyperreal p_ = Some z.
Proof.
  intros.
  assert ((h, p ++ l) = concat (h, p) (Class.Inheritance.Repeated, d :: l)).
   simpl.
   rewrite H1.
   destruct (peq d d); congruence.
  rewrite H4 in H2.
  rewrite <- concat_assoc in H2.
  rewrite <- H0 in H2.
  simpl in H2.
  refine (_ (concat_last _ H0)).
  rewrite H1.
  intro.
  rewrite x in H2.
  destruct (peq d d); try congruence.
  injection H2; intros; subst.
  functional inversion H3; subst.
  unfold subobject_offset.
  rewrite H6.
  Opaque non_virtual_subobject_offset.
  simpl.
  rewrite H9.
  destruct (last_correct x).
  replace (b :: _x ++ l) with ((b :: _x) ++ l) by reflexivity.
  rewrite e0 in *.
  rewrite app_ass.
  simpl.
  erewrite non_virtual_subobject_offset_app.
  2 : eassumption.
  rewrite (primary_path_offset intro H).
  congruence.
  destruct p; try discriminate.
Qed.


Lemma primary_subobject_offset_recip : forall l d,
  is_primary_path offsets (d :: l) = true ->
  forall h p hr pr h0 p0, (h0, p0) = concat (hr, pr) (h, p) ->
    last p = Some d ->
    forall h_ p_, (h_, p_) = concat (hr, pr) (h, p ++ l) ->
      forall hyperreal z, subobject_offset offsets hyperreal p_ = Some z ->
        subobject_offset offsets hyperreal p0 = Some z.
Proof.
  intros.
  assert ((h, p ++ l) = concat (h, p) (Class.Inheritance.Repeated, d :: l)).
   simpl.
   rewrite H1.
   destruct (peq d d); congruence.
  rewrite H4 in H2.
  rewrite <- concat_assoc in H2.
  rewrite <- H0 in H2.
  simpl in H2.
  refine (_ (concat_last _ H0)).
  rewrite H1.
  intro.
  rewrite x in H2.
  destruct (peq d d); try congruence.
  injection H2; intros; subst.
  destruct p0; try discriminate.
  functional inversion H3; subst.
  unfold subobject_offset.
  rewrite H8.
  rewrite H10.
  rewrite H7.
  destruct (last_correct x).
  replace (i :: p0 ++ l) with ((i :: p0) ++ l) in H7 by reflexivity.
  rewrite e0 in *.
  rewrite app_ass in H7.  
  simpl in H7.
  destruct (non_virtual_subobject_offset_app_recip H7).
  destruct H5.
  rewrite (primary_path_offset intro H) in H6.
  congruence.
  destruct p; try discriminate.
Qed.

Inductive dyncast_offset_spec : ident -> (Class.Inheritance.t * list ident) -> (Class.Inheritance.t * list ident) -> ident -> option Z -> Prop :=
| dyncast_offset_not_base_some :
  forall real h p cn,
  last p = Some cn ->
  forall x, (forall h' p', path hierarchy x p' cn h' -> False) ->
  forall h' p',
  dynamic_cast hierarchy real h p cn x h' p' ->
  forall hyperreal hr pr, path hierarchy real pr hyperreal hr ->
    forall h_ p_, (h_, p_) = concat (hr, pr) (h, p) ->
      forall z, subobject_offset offsets hyperreal p_ = Some z ->
        forall h'_ p'_, (h'_, p'_) = concat (hr, pr) (h', p') ->
          forall z', subobject_offset offsets hyperreal p'_ = Some z' ->
            forall res, res = z' - z ->
              dyncast_offset_spec hyperreal (hr, pr) (h, p) x (Some res)
              
| dyncast_offset_not_base_none :
  forall real h p cn,
    last p = Some cn ->
    forall x, (forall h' p', path hierarchy x p' cn h' -> False) ->
      (forall h' p',
        dynamic_cast hierarchy real h p cn x h' p' -> False) ->
      forall hyperreal hr pr, path hierarchy real pr hyperreal hr ->
        dyncast_offset_spec hyperreal (hr, pr) (h, p) x None
        
| dyncast_offset_base_with_primary : 
  forall p cn,
    last p = Some cn ->
    forall x h' p', path hierarchy x p' cn h' ->
      forall of, offsets ! cn = Some of ->
        forall b, primary_base of = Some b ->
          forall hr pr hyperreal h res, dyncast_offset_spec hyperreal (hr, pr) (h, p ++ b :: nil) x res ->
            dyncast_offset_spec hyperreal (hr, pr) (h, p) x res
.

Lemma dyncast_offset_spec_complete : forall l d,
is_primary_path offsets (d :: l) = true ->
forall c, path hierarchy c (d :: l) d Class.Inheritance.Repeated ->
forall x, (forall h' p', path hierarchy x p' c h' -> False) ->
forall real h p, path hierarchy d p real h ->
  forall hyperreal pr hr, path hierarchy real pr hyperreal hr ->
    (forall h' p', dynamic_cast hierarchy real h (p ++ l) c x h' p' ->
      forall h_ p_, (h_, p_) = concat (hr, pr) (h, p ++ l) ->
        forall z, subobject_offset offsets hyperreal p_ = Some z ->
          forall h'_ p'_, (h'_, p'_) = concat (hr, pr) (h', p') ->
            forall z', subobject_offset offsets hyperreal p'_ = Some z' ->
              dyncast_offset_spec hyperreal (hr, pr) (h, p) x (Some (z' - z))) /\
    ((forall h' p', dynamic_cast hierarchy real h (p ++ l) c x h' p' -> False) ->
      dyncast_offset_spec hyperreal (hr, pr) (h, p) x None).
Proof.
  induction l.
  intros until 2.
  generalize (path_last H0).
  injection 1; intro; subst.
  intros.
  rewrite <- app_nil_end.
  split.
   intros.
   econstructor.
   eapply path_last.
   eassumption.
   assumption.
   eassumption.
   eassumption.
   eassumption.
   eassumption.
   eassumption.
   eassumption.
   trivial.
intros.
econstructor.
eapply path_last.
eassumption.
assumption.
eassumption.
assumption.

intros until 1.
generalize H.
rewrite is_primary_path_equation.
case_eq (offsets ! d); try congruence.
intros until 1.
destruct (
option_eq_dec peq (primary_base t) (Some a)
); try congruence.
intros.
assert (path hierarchy c (a :: l) a Class.Inheritance.Repeated).
 inversion H2; subst.
 injection H6; intros; subst.
 generalize H7.
 destruct lt; simpl; try congruence.
 injection 1; intros; subst.
 functional inversion H8; subst.
 eleft.
   reflexivity.
   eassumption.
   assumption.
assert (path hierarchy a (d :: a :: nil) d Class.Inheritance.Repeated).
 inversion H2; subst.
 generalize (is_valid_repeated_subobject_split_left (l1 := d :: nil) H9).
 intros.
 eleft with (lt := d :: nil).
 reflexivity.
 reflexivity.
 assumption.
generalize (path_concat H4 H7).
intro.
simpl in H8.
rewrite (path_last H4) in H8.
destruct (peq d d); try congruence.
generalize (H8 _ _ (refl_equal _)).
intros.
destruct (Well_formed_hierarchy.paths Hhier).
invall.
assert (
 (exists h', exists p', path hierarchy x p' d h') \/ forall h' p',
 path hierarchy x p' d h' -> False
). 
case_eq (hierarchy ! x).
 intros.
 assert (hierarchy ! x <> None) by congruence.
 assert (x0 ! x <> None) by eauto.
 case_eq (x0 ! x); try congruence.
 intros.
 generalize (H11 _ _ H15).
 destruct 1.
 assert (hierarchy ! d <> None) by eauto using path_defined_to.
 assert (t1 ! d <> None) by eauto.
 case_eq (t1 ! d); try congruence.
 intros.
 destruct l0.
  right.
  intros.
  generalize (H17 _ _ H20 (h', p')).
  simpl; tauto.
 generalize (H17 _ _ H20 p0).
 destruct 1.
 destruct p0.
 generalize (H21 (or_introl _ (refl_equal _))).
 eauto.
 intros.
 right.
  intros.
  eapply path_defined_to.
  eexact H13.
  assumption.
 generalize (IHl _ H1 _ H6 _ H3 _ _ _ H9 _ _ _ H5).
 repeat rewrite app_ass.
 Opaque concat. simpl. Transparent concat.
 destruct 1.
destruct H12.
invall.
split.
intros.
eapply dyncast_offset_base_with_primary.
 eauto using path_last.
 eassumption.
 eassumption.
 eassumption.
 eauto.
intros.
eapply dyncast_offset_base_with_primary.
 eauto using path_last.
 eassumption.
 eassumption.
 eassumption.
 eauto.
split.

Focus 2.
intros.
eapply dyncast_offset_not_base_none.
eauto using path_last.
assumption.
intros.
eapply H15.
eapply non_base_dyncast_stable.
eassumption.
eassumption.
eassumption.
assumption.

intros.
case_eq (concat (hr, pr) (h, p)).
intros until 1.
symmetry in H20.
generalize (primary_subobject_offset_recip H H20 (path_last H4) H16 H17).
intro.
eapply dyncast_offset_not_base_some.
eauto using path_last.
assumption.
eapply non_base_dyncast_stable_recip.
assumption.
3 : eassumption.
eassumption.
eassumption.
assumption.
eassumption.
eassumption.
eassumption.
eassumption.
reflexivity.
Qed.

Corollary dyncast_offset_spec_reduce_path :
forall c x, (forall h' p', path hierarchy x p' c h' -> False) ->
forall real h p, path hierarchy c p real h ->
  forall hyperreal hr pr, path hierarchy real pr hyperreal hr ->
(forall h' p', dynamic_cast hierarchy real h p c x h' p' ->
  forall h_ p_, (h_, p_) = concat (hr, pr) (h, p) ->
forall z, subobject_offset offsets hyperreal p_ = Some z ->
  forall h'_ p'_, (h'_, p'_) = concat (hr, pr) (h', p') ->
forall z', subobject_offset offsets hyperreal p'_ = Some z' ->
dyncast_offset_spec hyperreal (hr, pr) (h, reduce_path offsets p) x (Some (z' - z))) /\
((forall h' p', dynamic_cast hierarchy real h p c x h' p' -> False) ->
dyncast_offset_spec hyperreal (hr, pr) (h, reduce_path offsets p) x None).
Proof.
 intros.
 destruct (reduce_path_prefix offsets Hhier H0).
 invall.
revert H2 H4.
generalize (reduce_path offsets p).
intros; subst.
eauto using dyncast_offset_spec_complete.
Qed.

Lemma dyncast_offset_spec_func : forall hyperreal hpr hp x oz1,
dyncast_offset_spec hyperreal hpr hp x oz1 ->
forall oz2, dyncast_offset_spec hyperreal hpr hp x oz2 ->
oz1 = oz2.
Proof.
 induction 1; inversion 1; subst; try congruence;
 replace cn0 with cn in * by congruence;
   try match goal with H : path _ ?real ?hpr _ _,
     H0 : path _ ?real0 ?hpr _ _ |- _ =>
       let Hz := fresh "H" in
         (generalize (path_last H); rewrite (path_last H0); intro Hz; injection Hz; clear Hz; intro; subst)
   end.
 generalize (Well_formed_hierarchy.dynamic_cast_unique Hhier H1 H15).
 congruence.
 destruct (H18 _ _ H1).
 destruct (H0 _ _ H15).
 destruct (H1 _ _ H10).
 destruct (H0 _ _ H10).
 destruct (H10 _ _ H0).
 destruct (H11 _ _ H0).
 replace of0 with of in * by congruence.
 replace b0 with b in * by congruence.
 eauto.
Qed.

Lemma dyncast_offset_spec_exists : forall hyperreal hpr hp x,
  {oz | dyncast_offset_spec hyperreal hpr hp x oz} + {forall oz, dyncast_offset_spec hyperreal hpr hp x oz -> False}.
Proof.
  intros.
  case_eq (hierarchy ! hyperreal).
   Focus 2.
   intros.
   right.
   intros.
   revert hyperreal hpr hp x oz H0 H.
   induction 1; eauto;
    generalize (path_defined_from H2); intro; contradiction.
   intros hrc Hhrc.
  destruct (Well_formed_hierarchy.paths Hhier).
  invall.
  case_eq hpr.
  intros.   
   case_eq (last l).
    Focus 2.
    intro.
    right.
    rewrite <- H1.
    intros.
    revert hpr hp x oz H3 H1 H2.
    induction 1; eauto.
     injection 1; intros; subst.
     generalize (path_last H4); congruence.
     injection 1; intros; subst.
     generalize (path_last H4); congruence.
  intros real Hreal.
  case_eq (hierarchy ! real).
   Focus 2.
   intros.
   right.
   rewrite <- H1.
   intros.
   revert hpr hp x oz H3 H1 real Hreal H2.
   induction 1; eauto;
    injection 1; intros; subst;
    replace real0 with real in * by (generalize (path_last H4); intros; congruence);
      generalize (path_defined_to H4); 
        intro; contradiction.
  intros rc Hrc.
  case_eq (x0 ! real).
   Focus 2.
   intros.
   destruct (H real).
   congruence.
   assumption.
  intros.
  generalize (H0 _ _ H2).
  destruct 1.
  case_eq (t0 ! hyperreal).
   Focus 2.
   intro.
   destruct  (H3 hyperreal).
   congruence.
   assumption.
  intros.
  destruct (H4 _ _ H5 (t, l)).
  destruct (In_dec path_eq_dec (t, l) l0).
   Focus 2.
   right.
   intros.
   destruct n.
   apply H7.
   clear Hrc H2 H3 H4 H5 H6 H7 t0 l0.
   rewrite <-  H1 in H8.
   clear rc.
   revert hpr hp x oz H8 t l H1 real Hreal.
   induction 1; eauto;
    injection 1; intros; subst;
      replace real0 with real in * by (generalize (path_last H4); intros; congruence);
        assumption.
  generalize (H6 i).
  intro.
  clear H2 H3 H4 l0 H5 H6 H7 i.
  case_eq hp.
  intros.
  case_eq (last l0).
   Focus 2.
   intro.
   right.   
   inversion 1; congruence.  
  intros.
  subst.
  revert t1 l0 H3 x.
  induction i using (well_founded_induction Plt_wf).
  intros.
  case_eq (hierarchy ! x).
   Focus 2.
   intros.
   left.
   exists None.
   eapply dyncast_offset_not_base_none.
   eassumption.
   intros.
   generalize (path_defined_to H4).
   tauto.
   intros.
   2 : eassumption.
   assert (path hierarchy x p' real h').
    inversion H4;    eauto using path_concat.
   generalize (path_defined_to H5).
   tauto.  
  intros.
  assert (hierarchy ! x <> None) by congruence.
  assert (x0 ! x <> None) by eauto.
  case_eq (x0 ! x); try congruence.
  case_eq (hierarchy ! i).
   Focus 2.
   intros.
   left.
   exists None.
   eapply dyncast_offset_not_base_none.
   eassumption.
   intros.
   generalize (path_defined_from H9).
   tauto.
   intros.
   2 : eassumption.
   assert (path hierarchy i l0 real t1).
    inversion H9; subst;  eauto using path_concat.
   generalize (path_defined_to H10).
   tauto.
  intros.
  assert (hierarchy ! i <> None) by congruence.
  destruct (H0 _ _ H7).
  assert (t4 ! i <> None) by eauto.
  case_eq (t4 ! i); try congruence.
  destruct l1.
   (* no path : I am not a base *)
   intros.
   generalize (fun k p => let (_, l) := H11 _ _ H13 (k, p) in l).
   simpl.
   intros.
   destruct (Well_formed_hierarchy.dynamic_cast_dec Hhier real t1 l0 i x).
    (* case some *)
    invall.
   assert (path hierarchy i l0 real t1).
    inversion H16; subst;  eauto using path_concat.
   assert (path hierarchy x x2 real x1).
    inversion H16; eauto using path_concat.
   case_eq (concat (t, l) (t1, l0)).
   intros.
   symmetry in H18.
   refine (_ (subobject_offset_exist Hhier intro guard _ (Plt_succ _) (path_concat H8 H15 H18))).
   2 : eauto.
   case_eq (subobject_offset offsets hyperreal l1); try congruence.
   case_eq (concat (t, l) (x1, x2)).
   intros.
   symmetry in H19.
   refine (_ (subobject_offset_exist Hhier intro guard _ (Plt_succ _) (path_concat H8 H17 H19))).
   2 : eauto.
   case_eq (subobject_offset offsets hyperreal l2); try congruence.
   intros.
   left.
   exists (Some (z0 - z)).
   eapply dyncast_offset_not_base_some.
   eassumption.
   assumption.
   eassumption.
   assumption.
   eassumption.
   eassumption.
   eassumption.
   eassumption.
   reflexivity.
  (* case none *)
  left.
  exists None.
  eapply dyncast_offset_not_base_none.
  eassumption.
  assumption.
  eassumption.
  assumption.
 (* I am a base *)
 intro.
 destruct (H11 _ _ H13 p).
 generalize (H14 (or_introl _ (refl_equal _))).
 destruct p.
 intros.
 assert (offsets ! i <> None) by eauto.
 case_eq (offsets ! i); try congruence.
 intros.
 case_eq (primary_base t6).
 (* some primary base: IH *)
 intros.
 generalize (non_virtual_primary_base_offset (intro H18) H19).
 intros.
 assert ((non_virtual_direct_base_offsets t6) ! i0 <> None) by congruence.
 generalize (non_virtual_direct_base_offsets_guard (intro H18) H21 H6).
 intros.
 assert (Plt i0 i) by eauto using Well_formed_hierarchy.well_founded.
 assert (last (l0 ++ i0 :: nil) = Some i0) by eauto using last_complete.
 destruct (H1 _ H23  t1 _ H24 x).
  invall.
  left.
  exists x1.
  eapply dyncast_offset_base_with_primary.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  assumption.
 right.
 inversion 1; subst; replace cn with i in * by congruence.
  destruct (H31 _ _ H16).
  destruct (H32 _ _ H16).
  replace i0 with b in * by congruence.
  destruct (f _ H37).
(* no primary base *)
right.
inversion 1; intros; subst; replace cn with i in * by congruence.
 destruct (H26 _ _ H16).
 destruct (H27 _ _ H16).
congruence.
Qed.

Definition dyncast_offset (hyperreal : ident) (hpr hp : (Class.Inheritance.t * list ident)) (x : ident) : option Z :=
  match dyncast_offset_spec_exists hyperreal hpr hp x with
    | inleft (Coq.Init.Specif.exist oz _) => oz
    | _ => None
  end.

Corollary dyncast_offset_reduce_path :
forall c x, (forall h' p', path hierarchy x p' c h' -> False) ->
forall real h p, path hierarchy c p real h ->
  forall hyperreal hr pr, path hierarchy real pr hyperreal hr ->
(forall h' p', dynamic_cast hierarchy real h p c x h' p' ->
  forall h_ p_, (h_, p_) = concat (hr, pr) (h, p) ->
    forall z, subobject_offset offsets hyperreal p_ = Some z ->
      forall h'_ p'_, (h'_, p'_) = concat (hr, pr) (h', p') ->
        exists z', subobject_offset offsets hyperreal p'_ = Some z' /\
          dyncast_offset hyperreal (hr, pr) (h, reduce_path offsets p) x = (Some (z' - z))) /\
((forall h' p', dynamic_cast hierarchy real h p c x h' p' -> False) ->
  dyncast_offset hyperreal (hr, pr) (h, reduce_path offsets p) x = None).
Proof.
  intros.
  destruct (dyncast_offset_spec_reduce_path H H0 H1).
  split;  intros.
   assert (path hierarchy x p' real h') by
     (inversion H4; subst; eauto using path_concat).
   generalize (subobject_offset_exist Hhier intro guard (fun ci _ => exis(ci := ci)) (Plt_succ _) (path_concat H1 H8 H7)).
   case_eq (subobject_offset offsets hyperreal p'_); try congruence.
   intros until 1.
   intros _.
   esplit.
   split.
   reflexivity.
   unfold dyncast_offset.
   destruct (dyncast_offset_spec_exists hyperreal (hr, pr) (h, reduce_path offsets p) x).
  destruct s.
  eauto using dyncast_offset_spec_func.
  edestruct f; eauto.
unfold dyncast_offset.
 destruct (dyncast_offset_spec_exists hyperreal (hr, pr) (h, reduce_path offsets p) x).
  destruct s.
  eauto using dyncast_offset_spec_func.
  trivial.
Qed.



(** * Virtual function dispatch *)

(**
The following theorem states that if a final overrider [(rk1, rp1)] exists for a class [ac1], and another one for a base [ac2] of [ac1], then [(rk1, rp1)] is also a final overrider for [ac1].
*)

Theorem final_overrider_base : forall ms ac1 rc rck1 rcp1 rk1 rp1,
  final_overrider hierarchy ms ac1 rc rck1 rcp1 rk1 rp1 ->
  forall ac2 k12 p12,
    path hierarchy ac2 p12 ac1 k12 ->
    forall rck2 rcp2, (rck2, rcp2) = concat (rck1, rcp1) (k12, p12) ->
      forall rk2 rp2,
        final_overrider hierarchy ms ac2 rc rck2 rcp2 rk2 rp2 ->        
        final_overrider hierarchy ms ac2 rc rck2 rcp2 rk1 rp1
        .
Proof.
  inversion 4; subst; eauto using Well_formed_hierarchy.final_overrider_dominates.
Qed.

(** 

Then, as method dispatch succeeds only if the final overrider for a class is unique, we have the following result: if a class *and one of its bases* dispatch to a method, then they dispatch to the same method.

*)

Corollary method_dispatch_base : forall ms ac1 rc rck1 rcp1 rk1 rp1,
  method_dispatch hierarchy ms ac1 rc rck1 rcp1 rk1 rp1 ->
  forall ac2 k12 p12,
    path hierarchy ac2 p12 ac1 k12 ->
    forall rck2 rcp2, (rck2, rcp2) = concat (rck1, rcp1) (k12, p12) ->
      forall rk2 rp2,
        method_dispatch hierarchy ms ac2 rc rck2 rcp2 rk2 rp2 -> (rk1, rp1) = (rk2, rp2).
Proof.
  inversion 1; subst.
  inversion 3; subst.
  symmetry.
  eapply H14.
  eauto using final_overrider_base.
Qed.


Section Generalize_to_primary_paths.
  Variable U : Type.
  Variable f : list ident -> option U.  

  Definition llt := (fun l1 l2 =>
    match last l1, last l2 with
      | Some e1, Some e2 => Plt e1 e2
      | _, _ => False
    end
  ).

    Lemma primary_base_lt : forall b o, offsets ! b = Some o ->
      forall b', primary_base o = Some b' -> Plt b' b.
    Proof.
      intros.
      generalize (non_virtual_primary_base_offset (intro H) H0).
      intro.
      assert ( (non_virtual_direct_base_offsets o) ! b' <> None
      ) by congruence.
      assert (offsets ! b <> None) by congruence.
      generalize (guard H3).
      intro.
      case_eq (hierarchy ! b); try congruence.
      intros.
      eauto using Well_formed_hierarchy.well_founded, non_virtual_direct_base_offsets_guard.      
    Qed.


  Function genprim (l : list positive) {wf llt l} : option U :=
    match last l with
      | None => None
      | Some las =>            
        match f l with
          | Some o => Some o
          | None =>
            match offsets ! las with
              | None => None
              | Some of =>
                match primary_base of with
                  | None => None
                  | Some las' =>
                    genprim (l ++ las' :: nil)
                end
            end
        end
    end.
  Proof.
    intros.
    unfold llt.
    rewrite last_complete.
    rewrite teq.
    eauto using primary_base_lt.
    unfold well_founded.
    unfold llt.
    intro.
    var (match last a with Some ll => Psucc ll | _ => xH end).
    revert v a H.
    induction v using (well_founded_induction Plt_wf).
     intros.
     case_eq (last a).
      intros.
      rewrite H1 in H0.
       subst.
       constructor.
       intro.
       case_eq (last y).
       rewrite H1.
       intros.
       eapply H.
       2 : rewrite H0.
       2 : reflexivity.
       unfold Plt in *.
       rewrite Psucc_Zsucc.
       rewrite Psucc_Zsucc.
       unfold Zsucc.
       omega.
      tauto.
     intro.
     rewrite H1 in H0.
     subst.
     constructor.
     intro.
     case_eq (last y).
      rewrite H1; tauto.
     tauto.
   Qed.
     
    Hypothesis f_primary : forall l o, f l = Some o ->
      forall a, last l = Some a -> forall l', is_primary_path offsets (a :: l') = true ->
        is_valid_repeated_subobject hierarchy (a :: l') = true ->
        forall o', f (l ++ l') = Some o' ->
          o = o'.

   Lemma genprim_complete : forall l a,
     last l = Some a ->
     forall l', is_primary_path offsets (a :: l') = true ->
       is_valid_repeated_subobject hierarchy (a :: l') = true ->
       forall o, f (l ++ l') = Some o ->
         genprim l = Some o.
   Proof.
     intros.
     revert l' l a H H0 H1 o H2.
     induction l'.
      intros.
      rewrite <- app_nil_end in H2.
      rewrite genprim_equation.
      unfold ident in *.
      rewrite H.
      rewrite H2.
      reflexivity.
     intros.
     functional inversion H0; subst.
     rewrite genprim_equation.
     unfold ident in *.
     rewrite H.
     case_eq (f l).
      intros.
      generalize (f_primary H3 H H0 H1 H2).
      congruence.
     intros.
     rewrite H9.
     rewrite _x0.
     functional inversion H1; subst.
     eapply IHl'.
     eapply last_complete.
     assumption.
     assumption.
     rewrite app_ass.
     assumption.
   Qed.
      
End Generalize_to_primary_paths.


Definition unique (A : Type) (eqd : forall a1 a2 : A,  {a1 = a2} + {a1 <> a2}) l :=
  if at_most_list eqd l then false else true.

Section Dispatch.

Variable compile_method_name : ident -> MethodSignature.t A -> ident.

Function dispfunc_naive (ms : MethodSignature.t A) (hyperreal : ident) (hr : Class.Inheritance.t) (pr : list ident) (h : Class.Inheritance.t) (p : list ident) : option ident :=
  match last pr with
    | None => None
    | Some real =>
      match last p with
        | None => None
        | Some apparent =>
          let (l, _) := Well_formed_hierarchy.final_overrider_list Hhier ms apparent real h p in
            if unique (path_eq_dec ) l then
              match l with
                | nil => None
                | (h', p') :: _ => 
                  match last p' with
                    | None => None
                    | Some cl => Some (compile_method_name cl ms)
                  end
              end
              else
                None
      end
  end.

Lemma dispfunc_naive_primary : forall  (ms : MethodSignature.t A) (hyperreal : ident) (hr : Class.Inheritance.t) (pr : list ident) (h : Class.Inheritance.t) (p : list ident) o,
  dispfunc_naive ms hyperreal hr pr h p = Some o ->
  forall a, last p = Some a -> forall l', is_primary_path offsets (a :: l') = true ->
    is_valid_repeated_subobject hierarchy (a :: l') = true ->
    forall o', dispfunc_naive ms hyperreal hr pr h (p ++ l') = Some o' ->
      o = o'.
Proof.
  intros.
  functional inversion H; subst.
  functional inversion H3; subst.
  replace a with apparent in * by congruence.
  assert (last (apparent :: l') = Some apparent0).
   destruct (last_correct H6).
   subst.
   rewrite app_ass in H11.
   simpl in H11.
   assert (apparent :: l' <> nil) by congruence.
   generalize (last_app_left H4 x).
   rewrite H11.
   congruence.
  destruct (last_correct H4).
  generalize (let (H, _) := _x _ _ in H (or_introl _ (refl_equal _))).
  intro.
  generalize (let (H, _) := _x1 _ _ in H (or_introl _ (refl_equal _))).
  intro.
  clear H12 H7.
  replace real0 with real in * by congruence.
  refine (_ (final_overrider_base H14 _ _ H16)).
  intro.
  unfold unique in H13.
  destruct (at_most_list path_eq_dec ((h'0, p'0) :: _x2)).
   discriminate.
  generalize (e0 _ (or_introl _ (refl_equal _)) _ (let (_, K) := _x1 _ _ in K x0)).
  congruence.
  eleft.
  reflexivity.
  eassumption.
  assumption.
  simpl.
  rewrite H6.
  destruct (peq apparent apparent); congruence.
Qed.


Definition dispfunc hyperreal hr pr rck1 rcp1 ms :=
  genprim (dispfunc_naive ms hyperreal hr pr rck1) rcp1.

Corollary dispfunc_reduce_path : forall ms ac1 real rck1 rcp1 rk1 rp1,
  method_dispatch hierarchy ms ac1 real rck1 rcp1 rk1 rp1 ->
  forall pr, last pr = Some real ->
    forall hyperreal hr,
      exists cn,
        last rp1 = Some cn /\
        dispfunc hyperreal hr pr rck1 (reduce_path offsets rcp1) ms = Some (compile_method_name cn ms).
Proof.
  unfold dispfunc.
  inversion 1; subst.
  intros.
  inversion H4; subst.
  rewrite (path_last H13).
  destruct (reduce_path_prefix offsets Hhier H7).
  esplit.
  split.
  reflexivity.
  invall.
  eapply genprim_complete.
  eauto using dispfunc_naive_primary.
  unfold ident in *.
  eauto using path_last.
  eassumption.
  inversion H19; assumption.
  rewrite <- H20.
  unfold dispfunc_naive.
  rewrite H6.
  rewrite (path_last H7).
  destruct (
    Well_formed_hierarchy.final_overrider_list Hhier ms ac1 real rck1 rcp1
  ).
  unfold unique.
  destruct (at_most_list path_eq_dec x1).
   destruct s.
   destruct s.
   invall.
   destruct x2.
   destruct x3.
   generalize (let (K, _) := i _ _ in K H21).
   generalize (let (K, _) := i _ _ in K H24).
   intros.
   generalize (H5 _ _ H23).
   generalize (H5 _ _ H26).
   congruence.
   destruct x1.
    destruct (let (_, K) := i _ _ in K H4).
   destruct p1.
   generalize (e _ (or_introl _ (refl_equal _)) _ (let (_, K) := i _ _ in K H4)).
   injection 1; intros; subst t l.
   rewrite (path_last H13).
   reflexivity.
 Qed.

End Dispatch.

Function dispoff_naive  (ms : MethodSignature.t A) (hyperreal : ident) (hr : Class.Inheritance.t) (pr : list ident) (h : Class.Inheritance.t) (p : list ident) : option Z :=
  match last pr with
    | None => None
    | Some real =>
      match last p with
        | None => None
        | Some apparent =>
          let (l, _) := Well_formed_hierarchy.final_overrider_list Hhier ms apparent real h p in
            if unique (path_eq_dec ) l then
              match l with
                | nil => None
                | (h', p') :: _ => 
                  let (h0, p0) := concat (hr, pr) (h, p) in
                    let (h'0, p'0) := concat (hr, pr) (h', p') in
                      match subobject_offset offsets hyperreal p0 with
                        | None => None
                        | Some o =>
                          match subobject_offset offsets hyperreal p'0 with
                            | None => None
                            | Some o' => Some (o' - o)
                          end
                      end                  
              end
              else
                None
      end
  end.

Lemma dispoff_naive_primary : forall  (ms : MethodSignature.t A) (hyperreal : ident) (hr : Class.Inheritance.t) (pr : list ident) (h : Class.Inheritance.t) (p : list ident) o,
  dispoff_naive ms hyperreal hr pr h p = Some o ->
  forall a, last p = Some a -> forall l', is_primary_path offsets (a :: l') = true ->
    is_valid_repeated_subobject hierarchy (a :: l') = true ->
    forall o', dispoff_naive ms hyperreal hr pr h (p ++ l') = Some o' ->
      o = o'.
Proof.
  intros.
  functional inversion H; subst.
  functional inversion H3; subst.
  replace a with apparent in * by congruence.  
  assert (last (apparent :: l') = Some apparent0).
   destruct (last_correct H6).
   subst.
   rewrite app_ass in H14.
   simpl in H14.
   assert (apparent :: l' <> nil) by congruence.
   generalize (last_app_left H4 x).
   rewrite H14.
   congruence.
  destruct (last_correct H4).
  generalize (let (H, _) := _x _ _ in H (or_introl _ (refl_equal _))).
  intro.
  generalize (let (H, _) := _x1 _ _ in H (or_introl _ (refl_equal _))).
  intro.
  clear H15 H7.
  replace real0 with real in * by congruence.
  assert ((h, p ++ l') = concat (h, p) (Class.Inheritance.Repeated, apparent :: l')).
   simpl.
   rewrite H6.
   destruct (peq apparent apparent); congruence.
  refine (_ (final_overrider_base H17 _ _ H22)).
  3 : eassumption.
  intro.
  unfold unique in H16.
  destruct (at_most_list path_eq_dec ((h'1, p'1) :: _x2)).
   discriminate.
  generalize (e0 _ (or_introl _ (refl_equal _)) _ (let (_, K) := _x1 _ _ in K x0)).
  injection 1; intros; subst.
  symmetry in H18.
  symmetry in H10.
  generalize (primary_subobject_offset H1 H10 H6 H18 H12).
  congruence.
  eleft; eauto.
Qed.

Definition dispoff hyperreal hr pr rck1 rcp1 ms :=
  genprim (dispoff_naive ms hyperreal hr pr rck1) rcp1.

Corollary dispoff_reduce_path : forall ms ac1 real rck1 rcp1 rk1 rp1,
  method_dispatch hierarchy ms ac1 real rck1 rcp1 rk1 rp1 ->
    forall hr pr hyperreal, path hierarchy real pr hyperreal hr ->
      forall h0 p0, (h0, p0) = concat (hr, pr) (rck1, rcp1) ->
        forall z, subobject_offset offsets hyperreal p0 = Some z ->
          forall h' p', (h', p') = concat (hr, pr) (rk1, rp1) ->
            exists z',
              subobject_offset offsets hyperreal p' = Some z' /\
              dispoff hyperreal hr pr rck1 (reduce_path offsets rcp1) ms = Some (z' - z).
Proof.
  unfold dispoff.
  inversion 1; subst.
  intros.
  inversion H4; subst.
  generalize (subobject_offset_exist Hhier intro guard (fun ci _ => exis(ci := ci)) (Plt_succ _) (path_concat H6 H16 H9)).
  case_eq (subobject_offset offsets hyperreal p'); try congruence.
  intros until 1.
  intros _.
  esplit.
  split.
   reflexivity. 
  destruct (reduce_path_prefix offsets Hhier H10).
  invall.
  eapply genprim_complete.
  eauto using dispoff_naive_primary.
  unfold ident in *.
  eauto using path_last.
  eassumption.
  inversion H23; assumption.
  unfold dispoff_naive.
  rewrite (path_last H6).
  rewrite <- H24.
  rewrite (path_last H10).
  destruct (
    Well_formed_hierarchy.final_overrider_list Hhier ms ac1 real rck1 rcp1
  ).
  unfold unique.
  destruct (at_most_list path_eq_dec x1).
   destruct s.
   destruct s.
   invall.
   destruct x2.
   destruct x3.
   generalize (let (K, _) := i _ _ in K H25).
   generalize (let (K, _) := i _ _ in K H28).
   intros.
   generalize (H5 _ _ H27).
   generalize (H5 _ _ H30).
   congruence.
   destruct x1.
    destruct (let (_, K) := i _ _ in K H4).
   destruct p2.   
   generalize (e _ (or_introl _ (refl_equal _)) _ (let (_, K) := i _ _ in K H4)).
   injection 1; intros until 2; subst t l.
   rewrite <- H7.
   rewrite <- H9.
   rewrite H8.
   rewrite H21.
   reflexivity.
 Qed.


(** * Virtual base offsets *)

Function vboffsets (hyperreal : ident) (hr : Class.Inheritance.t) (pr : list ident) (h : Class.Inheritance.t) (p : list ident)  (vb : ident) : option Z :=
  let (h', p') := concat (hr, pr) (h, p) in
    match subobject_offset offsets hyperreal p' with
      | None => None
      | Some off =>
        match offsets ! hyperreal with
          | None => None
          | Some o => 
            match (virtual_base_offsets o) ! vb with
              | None => None
              | Some off' => Some (off' - off)
            end
        end         
    end
    .

Lemma vboffsets_reduce_path : forall hyperreal hr pr class,
  path hierarchy class pr hyperreal hr ->
  forall h p cn, path hierarchy cn p class h ->
    forall h0 p0, (h0, p0) = concat (hr, pr) (h, p) ->
      forall z, subobject_offset offsets hyperreal p0 = Some z ->
        forall vb, is_virtual_base_of hierarchy vb cn ->
          exists o, offsets ! hyperreal = Some o /\
            exists z', (virtual_base_offsets o) ! vb = Some z' /\
              vboffsets hyperreal hr pr h (reduce_path offsets p) vb = Some (z' - z).
Proof.
  intros.
  generalize (exis(path_defined_from H)).
  case_eq (offsets ! hyperreal); try congruence.
  intros until 1.
  intros _.
  esplit.
  split.
   reflexivity.
  generalize (path_is_virtual_base_of H (path_is_virtual_base_of H0 H3)).
  intro.
  generalize (virtual_base_offsets_exist (intro H4) H5).
  case_eq ((virtual_base_offsets t) ! vb); try congruence.
  intros until 1.
  intros _.
  esplit.
  split.
   reflexivity.
 destruct (reduce_path_prefix offsets Hhier H0).
 invall.
 unfold vboffsets.
 rewrite H9 in H1.
 case_eq (concat (hr, pr) (h, reduce_path offsets p)).
 intros.
 symmetry in H10.
 rewrite (primary_subobject_offset_recip H11  H10 (path_last H7) H1  H2).
 rewrite H4.
 rewrite H6.
 reflexivity.
Qed.


(** * Construction of virtual tables *)

  Definition PVTable := (ident * (Class.Inheritance.t * list ident) * (Class.Inheritance.t * list ident))%type.

  Definition VBase := ident.

Lemma vborder_list_ex : forall class, {vb | exists c, (hierarchy) ! class = Some c /\ vborder_list (hierarchy) (Class.super c) vb} + {(hierarchy ) ! class = None}.
Proof.
  intros.
  case_eq ((hierarchy) ! class).
   intros.
   left.
   destruct (Well_formed_hierarchy.vborder_list_exists Hhier H).
   esplit.
   esplit.
   split.
    reflexivity.
   eassumption.
  right; trivial.
Qed.

  Definition vboffsets_l (pv : PVTable) : list (VBase * Z) :=
    match pv with
      | (hyperreal, (hr, pr), (h, p)) => 
        match last p with
          | None => nil
          | Some c =>
            match vborder_list_ex c with
              | inleft (exist l _) =>
                initass (vboffsets hyperreal hr pr h p) l
              | _ => nil
            end
        end
    end.
  
  Lemma vboffsets_l_complete : forall hyperreal hr pr class,
    path hierarchy class pr hyperreal hr ->
    forall h p cn, path hierarchy cn p class h ->
      forall h0 p0, (h0, p0) = concat (hr, pr) (h, p) ->
        forall z, subobject_offset offsets hyperreal p0 = Some z ->
          forall vb, is_virtual_base_of hierarchy vb cn ->
            exists o, offsets ! hyperreal = Some o /\
              exists z', (virtual_base_offsets o) ! vb = Some z' /\
                assoc peq vb (vboffsets_l (hyperreal, (hr, pr), (h, reduce_path offsets p))) = Some (z' - z).
  Proof.
    intros.
    generalize (vboffsets_reduce_path H H0 H1 H2 H3).
    intros; invall.
    esplit.
    split.
     eassumption.
    esplit.
    split.
     eassumption.
    unfold vboffsets_l.
    destruct (reduce_path_prefix offsets Hhier H0).
    invall.
    rewrite (path_last H5).
    destruct (vborder_list_ex x1).
     destruct s.
     invall.
     eapply trans_equal.
     eapply initass_assoc.
     eauto using virtual_base_vborder_list, path_is_virtual_base_of.
     assumption.
    destruct (path_defined_to H5).
    assumption.
  Qed.


(** Enumerating classes *)

  Definition classes := map (@fst _ _) (PTree.elements hierarchy).

  Lemma classes_complete : forall i, hierarchy ! i <> None -> In i classes.
  Proof.
    intros.
    case_eq (hierarchy ! i); try congruence.
    intros.
    unfold classes.
    change i with (fst (i, t)).
    apply in_map.
    apply PTree.elements_correct.
    assumption.
  Qed.

  (** Enumerating paths (in a better way than in CplusWf. Maybe later, this will be merged elsewhere.) *)
    
  Lemma enum_paths_from : forall from, {l |
    forall h p, In (h, p) l <-> exists to, path hierarchy to p from h
  }.
  Proof.
    induction from using (well_founded_induction Plt_wf).
    case_eq (hierarchy ! from).
     Focus 2.
     exists nil.
     simpl.
     split; try tauto.
     destruct 1.
     generalize (path_defined_from H1).
     intro; contradiction.
    intros cfrom Hcfrom.
    exists (
      remove_dup path_eq_dec
      (
        (Class.Inheritance.Repeated, from :: nil) ::
        flatten
        (
          map
          (
            fun hb : _ * _ =>
              let (h, b) := hb in
                match plt b from with
                  | left Hlt =>
                    let (l, _) := H _ Hlt in
                      map (fun hp =>
                        concat
                        (
                          h,
                          match h with
                            | Class.Inheritance.Repeated => from :: b :: nil
                            | Class.Inheritance.Shared => b :: nil
                          end
                        )
                        hp
                      ) l
                  | _ => nil
                end
          )
          (Class.super cfrom)
        )
      )
    ).
    intros.
    cut (
In (h, p)
     (
        ((Class.Inheritance.Repeated, from :: nil)
         :: flatten
              (map
                 (fun hb : Class.Inheritance.t * positive =>
                  let (h0, b) := hb in
                  match plt b from with
                  | left Hlt =>
                      let (l, _) := H b Hlt in
                      map
                        (fun hp : Class.Inheritance.t * list ident =>
                         concat
                           (h0,
                           match h0 with
                           | Class.Inheritance.Repeated => from :: b :: nil
                           | Class.Inheritance.Shared => b :: nil
                           end) hp) l
                  | right _ => nil
                  end) (Class.super cfrom)))) <->
   (exists to : ident, path (A:=A) hierarchy to p from h)
    ).
     generalize (remove_dup_In path_eq_dec
       (
         ((Class.Inheritance.Repeated, from :: nil)
           :: flatten
           (map
             (fun hb : Class.Inheritance.t * positive =>
                  let (h0, b) := hb in
                  match plt b from with
                  | left Hlt =>
                      let (l, _) := H b Hlt in
                      map
                        (fun hp : Class.Inheritance.t * list ident =>
                         concat
                           (h0,
                           match h0 with
                           | Class.Inheritance.Repeated => from :: b :: nil
                           | Class.Inheritance.Shared => b :: nil
                           end) hp) l
                  | right _ => nil
                  end) (Class.super cfrom))))
       (h, p)
     ).
     unfold ident.
     tauto.
    split.
    destruct 1.
     injection H0; intros; subst.
     esplit.
     eleft with (lt := nil).
     reflexivity.
     reflexivity.
     simpl.
     rewrite Hcfrom.
     trivial.
    destruct (member_flatten_elim H0).
    destruct H1.
    destruct (let (J, _) := in_map_iff _ _ _ in J H1).
    destruct H3.
    destruct x0.
    destruct (plt p0 from).
     Focus 2.
     subst.
     contradiction.
    destruct (H p0 p1).
    subst.
    destruct (let (J, _) := in_map_iff _ _ _ in J H2).
    destruct H3.
    destruct x.
    destruct (let (J, _) := i _ _ in J H5).
    esplit.
    eapply path_concat.
    2 : eassumption.
    2 : symmetry; eassumption.
    case_eq (hierarchy ! p0).
     Focus 2.
     generalize (path_defined_from H6).
     intros; contradiction.
    intros.    
    destruct t.
     eleft with (lt := from :: nil).
     reflexivity.
     reflexivity.
     simpl.
     rewrite Hcfrom.
     cut (
       (if In_dec super_eq_dec (Class.Inheritance.Repeated, p0)
         (Class.super cfrom)
         then match hierarchy ! p0 with
                | Some _ => true
                | None => false
              end
         else false) = true
     ); try tauto.
     destruct (
In_dec super_eq_dec (Class.Inheritance.Repeated, p0)
         (Class.super cfrom)
     ); try contradiction.
     rewrite H7.
     trivial.
    eright.
    eleft.
    eassumption.
    eassumption.
    eleft with (lt := nil).
    reflexivity.
    reflexivity.
    simpl.
    rewrite H7.
    trivial.

    (** reciprocally *)
    destruct 1.
    destruct (path_concat_recip H0).
     invall; subst.
     generalize (Well_formed_hierarchy.self_path_trivial Hhier H0).
     injection 1; intros; subst; eauto.
    generalize (H1 _ Hcfrom).
    intro; invall; subst.
    right.
    case_eq (plt x0 from).
     Focus 2.
     generalize (Well_formed_hierarchy.well_founded Hhier Hcfrom H3).
     intros; contradiction.
    intros.
    case_eq (H _ p0).
    intros.
    eapply member_flatten_intro.
    eapply in_map_iff.
    exists (x1, x0).
    rewrite H4.
    rewrite H6.
    split.
     reflexivity.
    assumption.
    eapply in_map_iff.
    esplit.
    split.
    symmetry.
    eassumption.
    eapply i.
    eauto.
  Qed.

  Definition enum_paths_from_weak_2 (from : ident) :=
    let (l, _) := enum_paths_from from in l.

  Definition enum_paths_from_weak (from : ident) (_ : Class.t A) :=
    enum_paths_from_weak_2 from.

  Definition paths_from := (PTree.map enum_paths_from_weak hierarchy).

  Lemma paths_from_complete : forall from to h p, path hierarchy to p from h -> exists l,
    paths_from ! from = Some l /\ In (h, p) l.
  Proof.
    intros.
    unfold paths_from.
    rewrite PTree.gmap.
    unfold option_map.
    generalize (path_defined_from H).
    case_eq (hierarchy ! from); try congruence.
    intros until 1.
    intros _.
    esplit.
    split.
     reflexivity.
    unfold enum_paths_from_weak, enum_paths_from_weak_2.
    destruct (enum_paths_from from).
    eapply i.
    eauto.
  Qed.    

  (** Virtual functions of a class and its bases *)

  Definition vf_constr hp := 
    match hp with
      | (h, p) =>
        let _ : Class.Inheritance.t := h in
        match last p with
          | None => nil
          | Some cn =>
            match hierarchy ! cn with
              | None => nil
              | Some c => filter
                (fun ms => 
                  match Method.find ms (Class.methods c) with
                    | None => false
                    | Some m => Method.virtual m
                  end
                )
                (map (@Method.signature A) (Class.methods c))
            end
        end
    end.

  Definition virtual_functions from :=
    remove_dup
    (@MethodSignature.eq_dec _)
    (flatten
      (map vf_constr (enum_paths_from_weak_2 from))
    ).
  
  Lemma method_find_sig : forall l ms (m : _ A),
    Method.find ms l = Some m -> Method.signature m = ms.
  Proof.
    induction l; simpl; try congruence.
    intros.
    destruct (MethodSignature.eq_dec (Method.signature a) ms); try congruence.
    eauto.
  Qed.

  Lemma virtual_functions_complete : forall from to p h,
    path hierarchy to p from h ->
    forall c, hierarchy ! to = Some c ->
      forall ms m, Method.find ms (Class.methods c) = Some m ->
        Method.virtual m = true ->
        In ms (virtual_functions from).
  Proof.
    intros.
    rewrite <- (method_find_sig H1).
    unfold virtual_functions.
    refine (let (K, _) := remove_dup_In _ _ _ in K _).
    case_eq (enum_paths_from from).
    intros.    
    refine (member_flatten_intro (l0 := vf_constr _) _ _ ).
    eapply in_map.
    unfold enum_paths_from_weak_2.
    rewrite H3.
    eapply i.
    eauto.
    unfold vf_constr.
    cut (
In (Method.signature m)
     match last p with
     | Some cn =>
         match hierarchy ! cn with
         | Some c0 =>
             filter
               (fun ms0 : MethodSignature.t A =>
                match Method.find ms0 (Class.methods c0) with
                | Some m0 => Method.virtual m0
                | None => false
                end) (map (@Method.signature A) (Class.methods c0))
         | None => nil
         end
     | None => nil
     end
    ); try tauto.
    rewrite (path_last H).
    rewrite H0.
    eapply filter_In.
    split.
     eapply in_map.
     eauto using Method.find_in.
    rewrite (method_find_sig H1).
    rewrite H1.
    assumption.
  Qed.

  Definition Dispatch := MethodSignature.t A.

  Section SDispatch.

    Variable compile_method_name : ident -> MethodSignature.t A -> ident.

  Definition dispfunc_l (pvtbl : PVTable) : list (Dispatch * ident) :=
    match pvtbl with
      | (hyperreal, (hr, pr), (h, p)) => 
        match last p with
          | None => nil
          | Some c =>
            initass (dispfunc compile_method_name hyperreal hr pr h p) (virtual_functions c)
        end
    end.

  Lemma dispfunc_l_reduce_path : forall ms ac1 real rck1 rcp1 rk1 rp1,
  method_dispatch hierarchy ms ac1 real rck1 rcp1 rk1 rp1 ->
  forall pr, last pr = Some real ->
    forall hyperreal hr,
      exists cn,
        last rp1 = Some cn /\
        assoc (@MethodSignature.eq_dec _) ms (dispfunc_l (hyperreal, (hr, pr), (rck1, reduce_path offsets rcp1))) = Some (compile_method_name cn ms).
Proof.
  intros.
  generalize (dispfunc_reduce_path compile_method_name H H0 hyperreal hr).
  intros; invall.
  esplit.
  split.
   eassumption.
  unfold dispfunc_l.
  inversion H; subst.
  inversion H7; subst.
  destruct (reduce_path_prefix offsets Hhier H9).
  invall.
  rewrite (path_last H20).
  rewrite initass_assoc.
  assumption.
  case_eq (concat (Class.Inheritance.Repeated, x0 :: x1) (h, p)).
  intros.
  symmetry in H23.
  eauto using virtual_functions_complete, path_concat.
Qed.

End SDispatch.

  Definition dispoff_l (pvtbl : PVTable) : list (Dispatch * Z) :=
    match pvtbl with
      | (hyperreal, (hr, pr), (h, p)) => 
        match last p with
          | None => nil
          | Some c =>
            initass (dispoff hyperreal hr pr h p) (virtual_functions c)
        end
    end.

Lemma dispoff_l_reduce_path : forall ms ac1 real rck1 rcp1 rk1 rp1,
  method_dispatch hierarchy ms ac1 real rck1 rcp1 rk1 rp1 ->
    forall hr pr hyperreal, path hierarchy real pr hyperreal hr ->
      forall h0 p0, (h0, p0) = concat (hr, pr) (rck1, rcp1) ->
        forall z, subobject_offset offsets hyperreal p0 = Some z ->
          forall h' p', (h', p') = concat (hr, pr) (rk1, rp1) ->
            exists z',
              subobject_offset offsets hyperreal p' = Some z' /\
              assoc (@MethodSignature.eq_dec _) ms (dispoff_l (hyperreal, (hr, pr), (rck1, reduce_path offsets rcp1))) = Some (z' - z).
Proof.
  intros.
  generalize (dispoff_reduce_path H H0 H1 H2 H3).
  intros; invall.
  esplit.
  split.
   eassumption.
  unfold dispoff_l.
  inversion H; subst.
  inversion H10; subst.
  destruct (reduce_path_prefix offsets Hhier H12).
  invall.
  rewrite (path_last H23).
  rewrite initass_assoc.
  assumption.
  case_eq (concat (Class.Inheritance.Repeated, x0 :: x1) (h, p)).
  intros.
  symmetry in H26.
  eauto using virtual_functions_complete, path_concat.
Qed.

Definition DCast := ident.

Definition dyncast_offset_l (pv : PVTable) : list (DCast * Z) :=
  match pv with
    | (hyperreal, hpr, hp) =>
      initass (dyncast_offset hyperreal hpr hp) classes
  end.

Corollary dyncast_offset_l_reduce_path :
forall c x, (forall h' p', path hierarchy x p' c h' -> False) ->
forall real h p, path hierarchy c p real h ->
  forall hyperreal hr pr, path hierarchy real pr hyperreal hr ->
(forall h' p', dynamic_cast hierarchy real h p c x h' p' ->
  forall h_ p_, (h_, p_) = concat (hr, pr) (h, p) ->
    forall z, subobject_offset offsets hyperreal p_ = Some z ->
      forall h'_ p'_, (h'_, p'_) = concat (hr, pr) (h', p') ->
        exists z', subobject_offset offsets hyperreal p'_ = Some z' /\
          assoc peq x (dyncast_offset_l (hyperreal, (hr, pr), (h, reduce_path offsets p))) = (Some (z' - z))) /\
((forall h' p', dynamic_cast hierarchy real h p c x h' p' -> False) ->
  assoc peq x (dyncast_offset_l (hyperreal, (hr, pr), (h, reduce_path offsets p))) = None).
Proof.
  intros.
  unfold dyncast_offset_l.
  destruct (In_dec peq x classes).
   rewrite initass_assoc; eauto using dyncast_offset_reduce_path.
  split; intros.
   absurd (hierarchy ! x <> None).   
    intro; destruct n; eauto using classes_complete.
    inversion H2; eauto using path_defined_to.
  rewrite initass_assoc_none; eauto.
Qed.
  

(** * Construction of VTTs *)

Definition PVTT := (ident * (Class.Inheritance.t * list ident))%type.

  Lemma PVTT_eq_dec : forall pvtt1 pvtt2 : PVTT,
    {pvtt1 = pvtt2} + {pvtt1 <> pvtt2}.
  Proof.
    apply prod_eq_dec.
     exact peq.
    apply path_eq_dec.
  Qed.

  Definition SubVTT := (Class.Inheritance.t * ident)%type.

  Section SubVTT.

  Function filter_repeated (hb : Class.Inheritance.t * ident) : bool :=
    match hb with
      | (Class.Inheritance.Repeated, _) => true
      | _ => false
    end.

  Variable (pvtt : PVTT) .

  Function sub_pvtt_repeated (hb : Class.Inheritance.t * ident) : option PVTT :=
    match hb with
      | (Class.Inheritance.Repeated, b) =>
        if is_dynamic_dec Hhier b
          then
            match pvtt with
              | (c, (h, p)) => Some (c, (h, p ++ b :: nil))
            end
          else None
      | _ => None
    end.

  Function sub_pvtt_shared (hb : Class.Inheritance.t * ident) : option PVTT :=
    match pvtt with
      | (c, (Class.Inheritance.Repeated, d :: nil)) =>
        if peq c d
          then
            match hb with
              | (Class.Inheritance.Shared, b) =>
                if is_dynamic_dec Hhier b
                  then
                    Some (c, (Class.Inheritance.Shared, b :: nil))
                  else
                    None
              | _ => None
            end
          else
            None
      | _ => None
    end.

  Definition sub_pvtt : list (SubVTT * PVTT) :=
    match pvtt with
      | (c, (h, p)) =>
        match last p with
          | Some cn =>
            match hierarchy ! cn with
              | Some c =>
                match vborder_list_ex cn with
                  | inleft (exist l _ ) =>
                    initass sub_pvtt_repeated (filter filter_repeated (Class.super c)) ++
                    initass sub_pvtt_shared (map (pair Class.Inheritance.Shared) l)
                  | _ => nil
                end
              | _ => nil
            end
          | _ => nil
        end
    end.

End SubVTT.

  Lemma sub_pvtt_non_virtual_complete : forall from through h p,
    path hierarchy through p from h ->
    forall to, is_dynamic hierarchy to ->
      forall cl, hierarchy ! through = Some cl ->
        In (Class.Inheritance.Repeated, to) (Class.super cl) ->       
        assoc super_eq_dec (Class.Inheritance.Repeated, to) (sub_pvtt (from, (h, p))) = Some (from, (h, p ++ to :: nil)).
  Proof.
    intros.
    unfold sub_pvtt.
    rewrite (path_last H).
    destruct (vborder_list_ex through).
     2 : congruence.
    destruct s.
    destruct e.
    destruct H3.
    rewrite H1.
    eapply assoc_app_some.
    erewrite initass_assoc.
    simpl.
    destruct (is_dynamic_dec Hhier); try contradiction.
    reflexivity.
   eapply filter_In.
   split; trivial.
Qed.

Lemma sub_pvtt_virtual_complete : forall  to, is_dynamic hierarchy to ->
  forall from, is_virtual_base_of hierarchy to from ->
    assoc super_eq_dec (Class.Inheritance.Shared, to) (sub_pvtt (from, (Class.Inheritance.Repeated, from :: nil))) = Some (from, (Class.Inheritance.Shared, to :: nil)).
  Proof.
    intros.
    unfold sub_pvtt.
    simpl.
    destruct (vborder_list_ex from).
     destruct s.
     destruct e.
     destruct H1.
     rewrite H1.
     erewrite assoc_app_none.
     erewrite initass_assoc.
     simpl.
     destruct (peq from from); try congruence.
     destruct (is_dynamic_dec Hhier to); try contradiction.
     reflexivity.
    eapply member_map.
    eauto using virtual_base_vborder_list.
    eapply initass_assoc_none.
    intro.
    generalize (let (K, _) := filter_In _ _ _ in K H3).
    simpl.
    destruct 1; discriminate.
   rewrite e.
   destruct (is_virtual_base_of_defined H0 e).
Qed.

  Function is_dynamic_repeated_subobject (p : list ident) : bool :=    
    match last p with
      | None => false
      | Some c => if is_dynamic_dec Hhier c then true else false
    end.

  Function is_reduced_repeated_subobject (p : list ident) : bool :=
    if list_eq_dec peq p (reduce_path offsets p) then true else false.


  Definition VtblPath := (Class.Inheritance.t * list ident)%type.

  Definition reduced_dynamic_paths class :=
    (filter
      (fun hp : _ * _ => let (_, p) := hp in if is_dynamic_repeated_subobject p then is_reduced_repeated_subobject p else false)
      (enum_paths_from_weak_2 class)).

  Lemma reduced_dynamic_paths_complete : forall to,
    is_dynamic hierarchy to ->
    forall p, p = reduce_path offsets p ->
      forall class h, path hierarchy to p class h ->      
      In (h, p) (reduced_dynamic_paths class).
  Proof.
    intros.
    unfold reduced_dynamic_paths.
    eapply filter_In.
    split.
     unfold enum_paths_from_weak_2.
     destruct (enum_paths_from class).
     refine (let (_, K) := i _ _ in K _).
     eauto.
    unfold is_dynamic_repeated_subobject.
    rewrite (path_last H1).
    destruct (is_dynamic_dec Hhier to); try contradiction.
    unfold is_reduced_repeated_subobject.
    destruct (list_eq_dec peq p (reduce_path offsets p)); try contradiction.
    trivial.
  Qed.


  Lemma reduced_dynamic_paths_correct : forall class h p,
    In (h, p) (reduced_dynamic_paths class) ->
    exists to,
      path hierarchy to p class h /\
      is_dynamic hierarchy to /\
      p = reduce_path offsets p.
  Proof.
    unfold reduced_dynamic_paths.
    intros.
    destruct (let (K, _) := filter_In _ _ _ in K H).
    unfold enum_paths_from_weak_2 in H0.
    destruct (enum_paths_from class).
    destruct (let (K, _) := i _ _ in K H0).
    unfold is_dynamic_repeated_subobject in H1.
    rewrite (path_last H2) in H1.
    destruct (is_dynamic_dec Hhier x0); try discriminate.
    unfold is_reduced_repeated_subobject in H1.
    destruct (list_eq_dec peq p (reduce_path offsets p)); try discriminate.
    eauto.
  Qed.

  Function pvtables (pvtt : PVTT) : list (VtblPath * PVTable) :=
    match pvtt with
      | (_, (_, pr)) =>
        match last pr with
          | None => nil
          | Some class =>
            (
              map
              (attach (pair pvtt))
              (reduced_dynamic_paths class)
            )
        end
    end.

  Lemma pvtables_complete : forall hyperreal hr pr real,
    path hierarchy real pr hyperreal hr ->
    forall to, is_dynamic hierarchy to ->
      forall h p, path hierarchy to p real h ->
        p = reduce_path offsets p ->
        assoc path_eq_dec (h, p) (pvtables (hyperreal, (hr, pr))) = Some (hyperreal, (hr, pr), (h, p)).
  Proof.
    intros.
    unfold pvtables.
    rewrite (path_last H).
    apply assoc_attach_some.
    eauto using reduced_dynamic_paths_complete.
  Qed.

(** Assembling (determining which VTTs and PVTTs to generate) *) 

Definition dynamic_classes := filter (fun c => if is_dynamic_dec Hhier c then true else false) classes.

  Lemma dynamic_complete : forall c, is_dynamic hierarchy c -> In c dynamic_classes.
  Proof.
    intros.
    unfold dynamic_classes.
    eapply filter_In.
    split.
     apply classes_complete.
     inversion H; congruence.
    destruct (is_dynamic_dec Hhier c); congruence.
  Qed.

  Definition InitVTT := ident.

  Definition init_pvtt : list (InitVTT * PVTT) :=
    map (attach (fun c => (c, (Class.Inheritance.Repeated, c :: nil)))) dynamic_classes.

  Lemma init_pvtt_complete : forall c, is_dynamic hierarchy c -> assoc peq c init_pvtt = Some (c, (Class.Inheritance.Repeated, c :: nil)).
  Proof.
    unfold init_pvtt.
    intros.
    eapply trans_equal.
    apply assoc_attach_some.
    eauto using dynamic_complete.
    reflexivity.
  Qed.


  Definition VTableAccess := ident.

  Definition vtable_access (pv : PVTable) : option VTableAccess :=
    match pv with
      | (_, _, (_, p)) => last p
    end.

  Function vtable_access_sharing (v : VTableAccess) : option VTableAccess :=
    match offsets ! v with
      | None => None
      | Some o => primary_base o
    end.

  Definition vtable_access_VBase (v : VTableAccess) :=
    match vborder_list_ex v with
      | inleft (exist l _ ) => l
      | _ => nil
    end. 

  Definition VTTAccess := ident.

  Definition romty := ROMTypes
    InitVTT
    SubVTT
    VTableAccess
    VTTAccess
    VtblPath
    VBase
    DCast
    Dispatch
    PVTT
    PVTable
    .

  Lemma vtable_access_wf : well_founded (vtable_access_lt (romty := romty) (vtable_access_sharing)).
  Proof.
    unfold well_founded.
    induction a using (well_founded_induction Plt_wf).
    constructor.
    intros.
    apply H.
    clear H.
    induction H0.
     unfold vtable_access_prec in H.
     functional inversion H.
     generalize (non_virtual_primary_base_offset (intro H1) H0).
     intro.
     assert ((non_virtual_direct_base_offsets o) ! x <> None) by congruence.
     assert (offsets ! y <> None) by congruence.
     assert (hierarchy ! y <> None) by eauto.
     case_eq (hierarchy ! y); try congruence.
     intros; eauto using non_virtual_direct_base_offsets_guard, Well_formed_hierarchy.well_founded.
     eauto using Plt_trans.
   Qed.

Definition vtable compile_method_name (pv : PVTable) := VTable (romty := romty)
  (vboffsets_l pv)
  (dyncast_offset_l pv)
  (dispfunc_l compile_method_name pv)
  (dispoff_l pv).


  Definition vtt (pvtt : PVTT) := VTT (romty := romty)
    (sub_pvtt pvtt)
    (pvtables pvtt)
    .

  Section Pseudo_flatten.
    Variables U V : Type.
    
    Function pflatten (l : list (U * list V)) : list (U * V) :=
      match l with
        | nil => nil
        | (u, lv) :: q => map (pair u) lv ++ pflatten q
      end.

    Lemma pflatten_in_complete : forall l u lv,
      In (u, lv) l ->
      forall v, In v lv -> In (u, v) (pflatten l).
    Proof.
      intro.
      functional induction (pflatten l); simpl.
       tauto.
      intros.
      apply in_or_app.
      destruct H; eauto.
      left.
      injection H; intros; subst.
      eauto using in_map.
    Qed.
  End Pseudo_flatten.

  Definition all_paths := pflatten (PTree.elements paths_from).

  Lemma all_paths_complete : forall from to p h,
    path hierarchy to p from h ->
    In (from, (h, p)) all_paths.
  Proof.
    unfold all_paths.
    intros.
    generalize (paths_from_complete H).
    intros; invall.
    eapply pflatten_in_complete.
    eapply PTree.elements_correct.
    eassumption.
    assumption.
  Qed.

  Definition all_pvtt : list PVTT := filter
    (fun pvtt =>
      match pvtt with
        | (_, (_, p)) => is_dynamic_repeated_subobject p
      end
    )
    all_paths.

  Lemma all_pvtt_complete : forall from to p h,
    path hierarchy to p from h ->
    is_dynamic hierarchy to ->
    In (from, (h, p)) all_pvtt.
  Proof.
    unfold all_pvtt.
    intros.
    eapply filter_In.
    split.
     eauto using all_paths_complete.
    unfold is_dynamic_repeated_subobject.
    rewrite (path_last H).
    destruct (is_dynamic_dec Hhier to); auto.
  Qed.

  Definition map_all_pvtt := map (attach vtt) all_pvtt.

  Lemma map_all_pvtt_complete : forall from to p h,
    path hierarchy to p from h ->
    is_dynamic hierarchy to ->
    assoc PVTT_eq_dec (from, (h, p)) map_all_pvtt = Some (vtt (from, (h, p))).
  Proof.
    intros.
    unfold map_all_pvtt.
    apply assoc_attach_some.
    eauto using all_pvtt_complete.
  Qed.

  Definition extract_pvtables pvtt := map (@snd _ _) (pvtables pvtt).

  Definition all_pvtable : list PVTable := flatten (map extract_pvtables all_pvtt).

  Lemma all_pvtable_complete : forall hyperreal hr pr from,
    path hierarchy from pr hyperreal hr ->
    forall to p' h',
      path hierarchy to p' from h' ->
      p' = reduce_path offsets p' ->
      is_dynamic hierarchy to ->
      In (hyperreal, (hr, pr), (h', p')) all_pvtable.
  Proof.
    unfold all_pvtable.
    intros.
    refine (member_flatten_intro (l0 := extract_pvtables _) _ _).
    eapply in_map.
    eapply all_pvtt_complete.
    eexact H.
    eauto using is_dynamic_path.
   unfold extract_pvtables.
   exact (in_map _ _ _ (assoc_In (pvtables_complete H H2 H0 H1))).
 Qed.

 Definition map_all_pvtable  compile_method_name := map (attach (vtable  compile_method_name)) all_pvtable.   

  Definition PVTable_eq_dec : forall a1 a2 : PVTable, {a1 = a2} + {a1 <> a2}.
  Proof.
    unfold PVTable.
    eauto using prod_eq_dec, path_eq_dec, peq.
  Qed.

 Lemma map_all_pvtable_complete : forall hyperreal hr pr from,
    path hierarchy from pr hyperreal hr ->
    forall to p' h',
      path hierarchy to p' from h' ->
      p' = reduce_path offsets p' ->
      is_dynamic hierarchy to ->
      forall  compile_method_name,
      assoc PVTable_eq_dec (hyperreal, (hr, pr), (h', p')) (map_all_pvtable compile_method_name) = Some (vtable  compile_method_name (hyperreal, (hr, pr), (h', p'))).
 Proof.
   intros.
   unfold map_all_pvtable.
   apply assoc_attach_some.
   eauto using all_pvtable_complete.
 Qed.


 Function vtt_access (pv : PVTT) : option VTTAccess :=
   match pv with
     | (_, (_, p)) => last p
   end.
  
  Definition rom compile_method_name := ROMopsemparam (romty := romty)
    init_pvtt
    peq
    map_all_pvtt
    PVTT_eq_dec
    super_eq_dec
    path_eq_dec
    (map_all_pvtable  compile_method_name)
    PVTable_eq_dec
    peq
    peq
    (MethodSignature.eq_dec (A := A))
    vtable_access
    vtable_access_sharing
    vtable_access_VBase
    virtual_functions
    vtt_access
    .



      (** We need this decision procedure to prove the invariant. Remember for instance that "Object layout" technical report Theorem 5.4 is split into two parts: the empty part, and the non-empty part. 
  [    Variable is_empty_dec : forall cl, {is_empty hierarchy cl} + {~ is_empty OP hierarchy cl}. ]
*)


End Common.


