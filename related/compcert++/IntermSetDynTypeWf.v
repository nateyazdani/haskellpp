Require Import Coqlib.
Require Import Cplusconcepts.
Require Import LibLists.
Require Import Tactics.
Require Import LibMaps.
Require Import IntermSetDynType.
Require Import CplusWf.
Require Import Wellfounded.
Require Import Relations.
Load Param.
Open Scope Z_scope.

Section Set_dynamic_type.

Variable A : ATOM.t .

Variable hierarchy : PTree.t (Class.t A).

Section Concat_repeated.

Lemma concat_repeated : forall h' p' from to,
  path hierarchy to p' from h' ->
  forall p1 a, last p1 = Some a ->
    forall h1 p2, (h', p') = concat (h1, p1) (Class.Inheritance.Repeated, a :: p2) ->
      h1 = h' /\
      path hierarchy to (a :: p2) a Class.Inheritance.Repeated /\
      path hierarchy a p1 from h'.
Proof.
 simpl.
 intros.
rewrite H0 in H1.
destruct (peq a a); try congruence.
injection H1; intros; subst.
destruct (last_correct H0).
subst.
rewrite app_ass in H.
simpl in H.
assert (a :: p2 <> nil) by congruence.
generalize (last_app_left H2 x).
rewrite (path_last H).
intro.
symmetry in H3.
destruct (last_correct H3).
assert (
  is_valid_repeated_subobject hierarchy (x ++ a :: p2) = true /\
  exists f,
    match h1 with
      | Class.Inheritance.Repeated => f = from
      | Class.Inheritance.Shared => is_virtual_base_of hierarchy f from
    end /\
    exists q, 
      f :: q = x ++ a :: nil    
).
 generalize (path_path0 H).
 inversion 1; split; auto.
  exists from.
  split; auto.
  destruct x.
   exists nil.
    simpl in *; congruence.
   exists (x ++ a :: nil).
   simpl in *; congruence.
  esplit.
  split; eauto.
  destruct x.
   exists nil.
    simpl in *; congruence.
   exists (x ++ a :: nil).
   simpl in *; congruence.
invall.
split; auto.  
generalize (is_valid_repeated_subobject_split_left H5).
generalize (is_valid_repeated_subobject_split_right H5).
intros.   
split.
eleft; eauto.
apply path0_path.
destruct h1; econstructor; eauto.
subst.
symmetry.
eexact H4.
Qed.
   

End Concat_repeated.

Hypothesis hierarchy_wf : Well_formed_hierarchy.prop hierarchy.

Variable obj : positive.
Variable ar : array_path A.
Variable i : Z.

Variable h0 : Class.Inheritance.t.
Variable p0 : list ident.

Variable dt : ident.

Lemma set_dynamic_type_other_path : forall (Hdt : last p0 = Some dt) l1 l2,
  set_dynamic_type hierarchy obj ar i h0 p0 l1 l2 ->
  forall h' p',
    (forall to h p, path hierarchy to p dt h -> (h', p') <> concat (h0, p0) (h, p)) ->
    assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) l2 =
    assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) l1.
Proof.
 inversion 2; subst.
 replace cn with dt in * by abstract congruence.
 intros.
 eapply trans_equal.
 eapply set_dynamic_type_non_virtual_other_path.
 3 : eassumption.
 eleft with (lt := nil).
 reflexivity.
 reflexivity.
 simpl.
 case_eq (hierarchy ! dt); intros; congruence.
 intros.
 replace (
(concat (Class.Inheritance.Repeated, dt :: nil)
        (Class.Inheritance.Repeated, p1)))
  with (Class.Inheritance.Repeated, p1).
 eapply H5.
 eassumption.
 simpl.
 unfold plus.
 destruct p1.
  destruct (path_nonempty H6).
  trivial.
 simpl.
 inversion H6; subst.
 destruct (peq dt i0); congruence.
eapply set_dynamic_type_virtual_aux_other_path.
eassumption.
intros.
assert (
  is_virtual_base_of  hierarchy b dt
).
eapply vborder_list_virtual_base.
eassumption.
eassumption.
eassumption.
eright.
eassumption.
eleft with (lt := nil).
reflexivity.
reflexivity.
simpl.
case_eq (hierarchy ! b); trivial.
intro.
destruct (Well_formed_hierarchy.is_virtual_base_of_defined_base hierarchy_wf H7 H8).
intros.
replace (Class.Inheritance.Shared, b :: p'') with (concat (h0, p0) (Class.Inheritance.Shared, b :: p'')).
eapply H5.
eright.
eauto using vborder_list_virtual_base.
eassumption.
reflexivity.
Qed.

Corollary set_dynamic_type_other_path_2 : forall (Hdt : last p0 = Some dt) l1 l2,
  set_dynamic_type hierarchy obj ar i h0 p0 l1 l2 ->
  forall to' p', last p' = Some to' ->
    forall h',
    (forall h p, path hierarchy to' p dt h -> (h', p') <> concat (h0, p0) (h, p)) ->
    assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) l2 =
    assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) l1.
Proof.
  intros.
  eapply set_dynamic_type_other_path.
  assumption.
  assumption.
  intros.
  intro.
  generalize (concat_last (path_nonempty H2) H3).
  rewrite (path_last H2).
  rewrite H0.
  injection 1; intros; subst; eapply H1; eauto.
Qed.  

Section Same.

Variable from : ident.

Section S.

Hypothesis Hpath : path hierarchy dt p0 from h0.

Let Hdt : last p0 = Some dt.
Proof.
  eauto using path_last.
Qed.

Lemma set_dynamic_type_same_path : forall l1 l2,
  set_dynamic_type hierarchy obj ar i h0 p0 l1 l2 ->
  forall to h p, path hierarchy to p dt h ->
    forall h' p',
      (h', p') = concat (h0, p0) (h, p) ->
      assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) l2 = Some ((h0, p0), (h, p)).
Proof.
  inversion 1; subst.
  replace cn with dt in * by abstract congruence.
  intros.
  generalize (path_path1 H5).
  inversion 1; subst.
   rewrite <- (concat_trivial_left H5).
   eapply set_dynamic_type_non_virtual_same_path.
   2 : eassumption.
   eleft with (lt := nil).
   reflexivity.
   reflexivity.
   simpl.
   rewrite H1; reflexivity.
   rewrite (concat_trivial_left H5).
   assumption.
   eassumption.
  eapply trans_equal.
  eapply set_dynamic_type_non_virtual_other_path with (hierarchy := hierarchy).
  3 : eassumption.
  eleft with (lt := nil).
  reflexivity.
  reflexivity.
  simpl.
  rewrite H1.
  trivial.
 intros.
 rewrite (concat_trivial_left H10).
 injection H6; intros; subst.
 inversion H10; subst.
 simpl.
 rewrite H0.
 destruct (peq dt dt); try congruence.
 inversion H9; subst. 
 intro.
 destruct p0.
  destruct (path_nonempty Hpath (refl_equal _)).
 injection H11; intros; subst.
 destruct (Plt_irrefl i0).
 eapply Plt_Ple_trans.
 eapply Well_formed_hierarchy.is_virtual_base_of_lt.
 eassumption.
 eassumption. 
 eapply Well_formed_hierarchy.path_base_le.
 eassumption.
 eassumption.
injection H6; intros; subst.
eapply set_dynamic_type_virtual_aux_same_path with (dt := dt).
eassumption.
intros.
generalize (vborder_list_virtual_base H1 H2 H10).
eright.
eassumption.
eleft with (lt := nil).
reflexivity.
 reflexivity.
simpl.
case_eq (hierarchy ! b).
 trivial.
generalize (Well_formed_hierarchy.is_virtual_base_of_defined_base hierarchy_wf H11).
intros; contradiction.
eauto using virtual_base_vborder_list.
eassumption.
Qed.

End S.

Variable is_primary_path : list ident -> bool.

Variable h': Class.Inheritance.t.
Variable p' : list ident.
Variable to' : ident.
Variable Hpath' : path hierarchy to' p' from h'.

Hypothesis p'_not_base : forall h'' p'', path hierarchy to' p'' dt h'' -> (h', p') <> concat (h0, p0) (h'', p'').

Lemma set_dynamic_type_strong_other_not_primary_base : forall Hpath : path hierarchy dt p0 from h0,
  (forall p'', is_primary_path (to' :: p'') = true -> (h0, p0) <> concat (h', p') (Class.Inheritance.Repeated, to' :: p'')) ->
  forall l1 l2,
    set_dynamic_type hierarchy obj ar i h0 p0 (erase_non_primary_ancestor_dynamic_type obj ar i h0 p0 is_primary_path l1) l2 ->
    assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) l2 =
    assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) l1.
Proof.
  intros.
  eapply trans_equal.
  eapply set_dynamic_type_other_path_2.
  eauto using path_last.
  eassumption.
  eauto using path_last.
  assumption.
 eapply erase_non_primary_ancestor_other.
 rewrite (path_last Hpath').
 injection 1; intro; subst.
 assumption.
Qed. 

Lemma set_dynamic_type_strong_other_primary_base :
  last p0 = Some dt ->
  forall p'', is_primary_path (to' :: p'') = true ->
    (h0, p0) = concat (h', p') (Class.Inheritance.Repeated, to' :: p'') ->
    forall l1 l2,
      set_dynamic_type hierarchy obj ar i h0 p0 (erase_non_primary_ancestor_dynamic_type obj ar i h0 p0 is_primary_path l1) l2 ->
      assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) l2 = None.
Proof. 
  intros.
  eapply trans_equal.
  eapply set_dynamic_type_other_path_2.
  assumption.
  eassumption.
  eauto using path_last.
  assumption.
  eapply erase_non_primary_ancestor_same.
  eauto using path_last.
  eassumption.
  assumption.
Qed.

End Same.



Lemma set_dynamic_type_non_virtual_aux_exists : forall j p,
  last p = Some j ->
  forall l,
    (forall cn, In cn l -> Plt cn j) ->
    (forall cn, In cn l -> hierarchy ! cn <> None) ->
    forall h l1,
      {l2 | set_dynamic_type_non_virtual_aux hierarchy obj ar i h0 p0 h p l l1 l2}.
Proof.
  cut (
    forall  al, match al with
                  | existT j l =>
                    forall p,
                      last p = Some j ->
                      (forall cn, In cn l -> Plt cn j) ->
                      (forall cn, In cn l -> hierarchy ! cn <> None) ->
                      forall h l1,
                        {l2 | set_dynamic_type_non_virtual_aux hierarchy obj ar i h0 p0 h p l l1 l2}
                end
  ).
  intros.
  generalize (X (existT _ j l)).
  eauto.
 pose (lstlt := ltof  _ (@length (positive))).
 induction al using (well_founded_induction_type (wf_lexprod _ _ _ _ Plt_wf (fun _ => well_founded_ltof _ (@length (positive))))).
 destruct al.
 intros.
 destruct l.
  case_eq (concat (h0, p0) (h, p)).
  intros.
  symmetry in H2.
  esplit.
   eleft.
   eassumption.
 case_eq (hierarchy ! p1).
 intros.
 refine (_ (X (existT _ p1 (
   (map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b) (filter (fun hb : _ * ident =>
    match hb with
      | (Class.Inheritance.Shared, _) => false
      | _ => true
    end
  ) (Class.super t)
 )))) _ (p ++ p1 :: nil) _ _ _ h l1)).
 intro; invall.
 refine (_ (X (existT _ x l) _ _ H _ _ h x1)).
 intro; invall.
 esplit.
 eright.
 eassumption.
 eassumption.
 eassumption.
eright.
unfold ltof. simpl; omega.
eauto.
eauto.
eleft.
eauto.
eapply last_complete.
intros.
eapply Well_formed_hierarchy.well_founded.
eassumption.
eassumption.
eauto using in_map_bases_elim.
intros.
eapply Well_formed_hierarchy.complete; eauto using in_map_bases_elim.
intro.
apply False_rect.
eapply H1.
eleft; reflexivity.
assumption.
Qed.

Corollary set_dynamic_type_non_virtual_exists : forall j p,
  last p = Some j ->
  hierarchy ! j <> None ->
  forall h l1,
    {l2 | set_dynamic_type_non_virtual hierarchy obj ar i h0 p0 h p l1 l2}.
Proof.
  intros.
  case_eq (hierarchy ! j).
  intros.
 refine (_ (set_dynamic_type_non_virtual_aux_exists 
   H   
   (l := map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b) (filter (fun hb : _ * ident =>
    match hb with
      | (Class.Inheritance.Shared, _) => false
      | _ => true
    end
  ) (Class.super t)
   ))
   _ _ h l1
 )).
 intro; invall; econstructor; econstructor; eauto.
 intros; eauto using Well_formed_hierarchy.well_founded, in_map_bases_elim.
 intros; eauto using Well_formed_hierarchy.complete, in_map_bases_elim.   
 intros; contradiction.
Qed.

Lemma set_dynamic_type_virtual_aux_exists : forall l,
  (forall cn, In cn l -> hierarchy ! cn <> None) ->
  forall l1,
  {l2 | set_dynamic_type_virtual_aux hierarchy obj ar i h0 p0 l l1 l2}.
Proof.
induction l.
 intros; econstructor; econstructor; eauto.
 intros.
 destruct (set_dynamic_type_non_virtual_exists (p := a :: nil) (refl_equal _) (H _ (or_introl _ (refl_equal _))) Class.Inheritance.Shared l1).
 refine (_ (IHl _ x)).
 destruct 1.
 econstructor; econstructor; eauto.
 eauto.
Qed.

Corollary set_dynamic_type_exists : last p0 = Some dt ->
  hierarchy ! dt <> None ->
  forall l1,
    {l2 | set_dynamic_type hierarchy obj ar i h0 p0 l1 l2}.
Proof.
 intros.
 case_eq (hierarchy ! dt).
  intros.
  destruct (Well_formed_hierarchy.vborder_list_exists hierarchy_wf H1).
  refine (_ (set_dynamic_type_virtual_aux_exists (l := x) _ l1)).
  destruct 1.
  destruct (set_dynamic_type_non_virtual_exists (p := dt :: nil) (refl_equal _) H0 Class.Inheritance.Repeated x0).
  econstructor; econstructor; eauto.
  intros.
  eapply Well_formed_hierarchy.is_virtual_base_of_defined_base; eauto using vborder_list_virtual_base.
  intro; contradiction.
Qed.

End Set_dynamic_type.
