(** Various subobject orderings and their properties *)

Require Import Relations.
Require Import Coqlib.
Require Import LibPos.
Require Import Maps.
Require Import LibLists.
Require Import Cplusconcepts.
Require Import CplusWf.
Require Import Events.

Load Param.
Open Scope nat_scope.

Open Scope Z_scope.

Section SubobjectOrdering.

Variable A : ATOM.t.

Variable hier : PTree.t (Class.t A).

Inductive relptr_gt : (array_path A * Z * (Class.Inheritance.t * list ident)) -> (array_path A * Z * (Class.Inheritance.t * list ident)) -> Prop :=
| relptr_gt_cast : forall p1 cn,
  last p1 = Some cn ->
  forall h' p' to',
    path hier to' p' cn h' ->
    forall h1 hp2, hp2 = concat (h1, p1) (h', p') ->
      (h', p') <> (Class.Inheritance.Repeated, cn :: nil) ->
      forall ar i,
        relptr_gt (ar, i, hp2) (ar, i, (h1, p1))
| relptr_gt_array_path :
  forall ar2 ar1 l,
    ar2 = ar1 ++ l ->
    l <> nil ->
    forall i1 hp1 i2 hp2,
          relptr_gt (ar2, i2, hp2)  (ar1, i1, hp1)
.

Lemma relptr_gt_trans : forall ap1 ap2, relptr_gt ap1 ap2 -> forall ap3, relptr_gt ap2 ap3 -> relptr_gt ap1 ap3.
Proof.
  inversion 1; inversion 1; subst.  

  case_eq (concat (h'0, p'0) (h', p')).
  intros.
  generalize (path_last H11).
  intros.
  assert (p'0 <> nil).
   intro; subst; simpl in *; discriminate.
  generalize (concat_last H5 H13).
  rewrite H0.
  rewrite H4.
  injection 1; intros; subst.
  eleft.
   eassumption.
   eapply path_concat.
   eassumption.
   eassumption.
   rewrite H2.
   reflexivity.
  rewrite H13.
  rewrite concat_assoc.
  rewrite H2.
  trivial.
  rewrite <- H2.
  unfold concat.
  destruct h'.
   unfold plus.
   destruct h'0.
    inversion H1; subst.
    rewrite H4.
    destruct (peq to'0 to'0); try congruence.
    inversion H11; subst.
    simpl.
    destruct lf0.
     congruence.
    simpl; congruence.
   congruence.
  congruence.
  
  eright.
  reflexivity.
  eassumption.

  eright.
  reflexivity.
  assumption.

  eright.
  rewrite app_ass.
  reflexivity.
  intro.
  destruct l0; simpl in H0.
   contradiction.
  discriminate.

Qed.


Lemma relptr_gt_array : forall ar1 i1 hp1 ar2 i2 hp2,
  relptr_gt (ar1, i1, hp1) (ar2, i2, hp2) ->
  exists l, ar1 = ar2 ++ l.
Proof.
  inversion 1; subst.
  exists nil.
  rewrite <- app_nil_end.
  trivial.
 esplit.
 reflexivity.
Qed.


Lemma relptr_gt_min :
forall array array_index x1 t l,
relptr_gt
     (array, array_index, (Class.Inheritance.Repeated, x1 :: nil))
     (array, array_index, (t, l))
-> False.
Proof.
   inversion 1.
    subst.
    revert H7.
    inversion H6; subst.
     simpl.
     rewrite H5.
     destruct (peq cn cn).
      injection 1; intros; subst.
      destruct l; try  discriminate.
      destruct l; try discriminate.
      destruct lf; try discriminate.
     destruct H8; trivial.
    destruct n; trivial.
    simpl.
    intro; discriminate.
   generalize (refl_equal (length array)).
   rewrite H2 at 1.
   rewrite app_length.
   destruct l0; simpl.
    destruct H7; trivial.
    intro; abstract omegaContradiction.
Qed.


Section Irrefl.

Hypothesis hierarchy_wf : Well_formed_hierarchy.prop hier.

Lemma relptr_gt_irrefl : forall ar,
  relptr_gt ar ar -> False.
Proof.
  inversion 1.
   generalize H3.
   Transparent concat.
   unfold concat.
   destruct h'.
    inversion H2; subst.
    simpl.
    rewrite H1.
    destruct (peq cn cn); try congruence.
    destruct lf.
     congruence.
    injection 1; intros.
    assert (length p1 = length (p1 ++ i0 :: lf)) by congruence.
    generalize H6.
    rewrite app_length.
    simpl.
    intros; omegaContradiction.
   injection 1; intros; subst.
   inversion H2; subst.
   generalize (Well_formed_hierarchy.path_le hierarchy_wf H4).
   generalize (Well_formed_hierarchy.is_virtual_base_of_lt hierarchy_wf H0).
   generalize (path_last H4).
   rewrite H1.
   injection 1; intros; subst.
   generalize (Plt_Ple _ _ H9).
   intros.
   generalize (Ple_antisym H8 H10).
   intros.
   subst.
   eapply Well_formed_hierarchy.no_self_virtual_base.
   eassumption.
   eassumption.
  assert (length ar2 = length ar2) by trivial.
  generalize H6.
  rewrite H3 at 1.
  rewrite app_length.
  simpl.
  destruct l; simpl; intros; try congruence; omega.
Qed.

End Irrefl.

(** * Subobject inclusion *)

Inductive inclusion_order : ident -> Z -> (array_path A * Z * (Class.Inheritance.t * list ident)) -> (array_path A * Z * (Class.Inheritance.t * list ident)) -> Prop :=
| inclusion_order_non_virtual : 
  forall afrom zfrom apath ato i h p pto,
    valid_relative_pointer (hier) afrom zfrom apath ato i h p pto ->
    forall p1 pto', path (hier) pto' p1 pto Class.Inheritance.Repeated ->
      forall h' p', (h', p') = concat (h, p) (Class.Inheritance.Repeated, p1) ->
        inclusion_order afrom zfrom (apath, i, (h', p')) (apath, i, (h, p))
| inclusion_order_virtual :
  forall to to_n from from_n ar,
    valid_array_path (hier) to to_n from from_n ar ->
    forall i, 0 <= i < to_n ->
      forall cn, is_virtual_base_of (hier) cn to ->
     inclusion_order from from_n (ar, i, (Class.Inheritance.Shared, cn :: nil)) (ar, i, (Class.Inheritance.Repeated, to :: nil))
| inclusion_order_field :
  forall afrom zfrom apath ato i h p pto,
    valid_relative_pointer (hier) afrom zfrom apath ato i h p pto ->
    forall c, (hier) ! pto = Some c ->
      forall fs, In fs (Class.fields c) ->
        forall cn n,
        FieldSignature.type fs = FieldSignature.Struct cn n ->
        forall j, 0 <= j < Zpos n ->
          forall apath', apath' = apath ++ (i, (h, p), fs) :: nil ->
            inclusion_order afrom zfrom (apath', j, (Class.Inheritance.Repeated, cn :: nil))  (apath, i, (h, p))
.

Lemma inclusion_order_refl : forall afrom zfrom apath ato i h p pto,
  valid_relative_pointer (hier) afrom zfrom apath ato i h p pto ->
  inclusion_order afrom zfrom (apath, i, (h, p)) (apath, i, (h, p)).
Proof.
  intros.
  inversion H.
  generalize (path_defined_to H3).
  intros.
  eapply inclusion_order_non_virtual.
  eassumption.
  eleft with (lt := nil).
  reflexivity.
  simpl ; reflexivity.
  simpl.
  revert H4.
  destruct ((hier) ! pto); congruence.
  simpl.
  rewrite (path_last H3).
  destruct (peq pto pto); try congruence.
  rewrite <- app_nil_end.
  trivial.
Qed.

Definition inclusion cn z := clos_trans _ (inclusion_order cn z).

Lemma inclusion_trans : forall cn z o1 o2, inclusion cn z o1 o2 -> forall o3, inclusion cn z o2 o3 -> inclusion cn z o1 o3.
Proof.
  intros.
  eapply t_trans; eauto.
Qed.

Lemma inclusion_refl : forall afrom zfrom apath ato i h p pto,
  valid_relative_pointer (hier) afrom zfrom apath ato i h p pto ->
  inclusion afrom zfrom (apath, i, (h, p)) (apath, i, (h, p)).
Proof.
  intros; eapply t_step; eauto using inclusion_order_refl.
Qed.

Lemma inclusion_lexical_order : forall cn z a1 i1 h1 p1 a2 i2 h2 p2, inclusion cn z (a1, i1, (h1, p1)) (a2, i2, (h2, p2)) ->
  (List.length a2 < List.length a1)%nat \/ a2 = a1 /\ i2 = i1 /\ (
    h1 = Class.Inheritance.Shared /\ h2 = Class.Inheritance.Repeated \/ (
      h1 = h2 /\ ((List.length p2 < List.length p1)%nat \/ p2 = p1)
    ) 
  )
.    
Proof.
  intros.
  revert H.
  var (a1, i1, (h1, p1)).
  var (a2, i2, (h2, p2)).
  intro Hincl.
  revert a1 i1 h1 p1 H a2 i2 h2 p2 H0.
  induction Hincl.
   intros; subst.
   inversion H; intros; subst.
    simpl in H12.
    unfold Cplusconcepts.plus in H12.
    inversion H5.
    rewrite (path_last H3) in H12.
    inversion H11; subst.
    destruct (peq pto pto); try abstract congruence.
    injection H12; intros; subst.
    right.
    repeat (split; auto).
    right.
    split; auto.
    destruct lf.
     right.
     rewrite <- app_nil_end.
     trivial.
    left.
    simpl.
    rewrite app_length.
    simpl.
    omega.
   right.
   repeat (split; auto).
  left.
  simpl.
  rewrite app_length.
  simpl.
  omega.

 destruct y. 
 destruct p.
 destruct p0.
 intros; subst.
 generalize (IHHincl2 _ _ _ _ (refl_equal _) _ _ _ _ (refl_equal _)).
 generalize (IHHincl1 _ _ _ _ (refl_equal _) _ _ _ _ (refl_equal _)).
 destruct 1.
  destruct 1.
   left; omega.
  destruct H0; subst; left; omega.
 invall; subst.
 destruct 1.
  left; assumption.
 invall; subst.
 right.
 split; auto.
 split; auto.
 destruct H2.
  invall; subst.
  destruct H3.
   invall; discriminate.
  invall; subst.
  left.
  auto.
 invall; subst. 
 destruct H3.
  left; assumption.
 right.
 invall; subst.
 split.
  trivial.
 destruct H2.
  destruct H1.
   left; omega.
  left; subst; omega.
 subst; assumption.
Qed.

Lemma inclusion_antisym : forall cn z o1 o2, inclusion cn z o1 o2 -> inclusion cn z o2 o1 -> o1 = o2.
Proof.
  destruct o1.
  destruct p0.
  destruct p.
  destruct o2.
  destruct p0.
  destruct p.
  intros.
  generalize (inclusion_lexical_order H).
  generalize (inclusion_lexical_order H0).
  destruct 1.
   destruct 1.
    omegaContradiction.
   invall; subst; omegaContradiction.
  invall; subst.
  destruct 1.
   omegaContradiction.
  invall; subst.
  destruct H4.
   invall; subst.
   destruct H5; invall; discriminate.
  invall; subst.
  destruct H5.
   invall; subst; discriminate.
  invall; subst.
  destruct H6.
   destruct H5; subst; omegaContradiction.
  subst; trivial.
Qed.

Lemma inclusion_inheritance_subobject_of_full_object : forall to to_n from from_n ar,
  valid_array_path (hier) to to_n from from_n ar ->
  forall i, 0 <= i < to_n ->
    forall pto h p, path (hier) pto p to h ->
      inclusion from from_n (ar, i, (h, p)) (ar, i, (Class.Inheritance.Repeated, to :: nil)).
Proof.
   intros.
   generalize (path_path1 H1).
   inversion 1; subst.
    (* case repeated *)
    eleft.   
    eapply inclusion_order_non_virtual.
    econstructor.
    eassumption.
    abstract omega.
    abstract omega.
    2 : eassumption.
    eleft with (lt := nil).
    reflexivity.
    reflexivity.
    revert H5.
    simpl.
    destruct ((hier) ! to); abstract congruence.
    symmetry. eapply concat_trivial_left.
    eassumption.
   (* case shared *)
   inversion H4; subst.
   eright.
   eleft.   
   eapply inclusion_order_non_virtual.
   econstructor.
   eassumption.
   abstract omega.
   abstract omega.
   eright.
   eassumption.
   eleft with (lf := nil) (lt := nil).
   reflexivity.
   reflexivity.
   revert H7.
   simpl.
   destruct ((hier) ! base); abstract congruence.
   eassumption.
   simpl.
   destruct (peq base base); abstract congruence.
   eleft.
   eapply inclusion_order_virtual.
   eassumption.
   split; abstract omega.
   assumption.
Qed.

Lemma inclusion_subobject_of_array_path_full_object : forall a to to_n ato i h' p' pto,
  valid_relative_pointer (hier) to to_n a ato i h' p' pto ->
  forall from from_n ar,
    valid_array_path (hier) to to_n from from_n ar ->
    exists j, 0 <= j < to_n /\
      inclusion from from_n (ar ++ a, i, (h', p')) (ar, j, (Class.Inheritance.Repeated, to :: nil)).
Proof.
  induction a.
   inversion 1.
   inversion H0; subst.
   intros.   
   rewrite <- app_nil_end.
   esplit.
   split.
   split.
   eexact H1.
   abstract omega.
   eapply inclusion_inheritance_subobject_of_full_object.
   eassumption.
   split.
    assumption.
   abstract omega.
   eassumption.
  (* inductive case *)
  intros.
  destruct a.
  destruct p.
  inversion H; subst.
  inversion H1; subst.
  assert (valid_relative_pointer (hier) by (Zpos by_n) a0 ato i h' p' pto).
  econstructor.
  eassumption.
  assumption.
  assumption.
  assumption.
  assert (valid_array_path (hier) by (Zpos by_n) from from_n (ar ++ (z, (h, l), t) :: nil)).
   eapply valid_array_path_concat.
   eassumption.
   econstructor.
   assumption.
   assumption.
   eassumption.
   eassumption.
   assumption.
   eassumption.
   econstructor.
   compute. abstract congruence.
   abstract omega.
  generalize (IHa _ _ _ _ _ _ _ H5 _ _ _ H6).
  destruct 1.
  destruct H7.
  rewrite app_ass in H8.
  simpl in H8.
  exists z.
  split.
   auto.
  eright.
   eassumption.
  eright.
  eleft.
  eapply inclusion_order_field.
  econstructor.
  eexact H0.
  eassumption.
  assumption.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  assumption.
  reflexivity.
 eapply inclusion_inheritance_subobject_of_full_object.
 eassumption.
 auto.
 eassumption.
Qed.

Corollary inclusion_subobject_of_full_object : forall a to to_n ato i h' p' pto,
  valid_relative_pointer (hier) to to_n a ato i h' p' pto ->
  exists j, 0 <= j < to_n /\
    inclusion to to_n (a, i, (h', p')) (nil, j, (Class.Inheritance.Repeated, to :: nil)).
Proof.
  intros.
  change a with (nil ++ a).
  eapply inclusion_subobject_of_array_path_full_object.
  eassumption.
  constructor.
  inversion H.
  eauto using valid_array_path_nonnegative_from.
  omega.
Qed.   

Lemma inclusion_relative_pointer_alt : forall afrom zfrom ato pto j h p f,  valid_relative_pointer_alt (hier) afrom zfrom ato pto (relative_pointer_alt_intro j (h, p) f) ->
  inclusion afrom zfrom (relative_pointer_of_relative_pointer_alt (relative_pointer_alt_intro j (h, p) f)) (nil, j, (h, p)).
Proof.
  inversion 1; subst; simpl.
  destruct f.
   destruct p0.
   destruct p0.
   destruct p0.
   destruct p1.
   invall; subst.
   inversion H7; subst.
   assert (valid_array_path (hier) x0 (Zpos x1) afrom zfrom ((j, (h, p), t) :: nil)).
    econstructor.
    assumption.
    assumption.
    eassumption.
    eassumption.
    assumption.
    eassumption.
    econstructor.
    compute; abstract congruence.
    abstract omega.
   generalize (inclusion_subobject_of_array_path_full_object H7 H11).
   destruct 1.
   destruct H12.
   simpl in H13.
   eright.
   eassumption.
   eleft.
   eapply inclusion_order_field.
   econstructor.
   econstructor.
   2 : eapply Zle_refl.
   abstract omega.
   assumption.
   assumption.
   eassumption.
   eassumption.
   eassumption.
   eassumption.
   assumption.
   reflexivity.
 
 destruct H7.
 subst.
 eapply inclusion_refl.
 econstructor.
 eleft.
 2 : eapply Zle_refl.
 abstract omega.
 assumption.
 assumption.
 eassumption.

Qed.

(** * Sibling subobjects (in construction order) ("appears before") *)

Inductive lifetime_order_horizontal : ident -> Z -> (array_path A * Z * (Class.Inheritance.t * list ident)) -> (array_path A * Z * (Class.Inheritance.t * list ident)) -> Prop :=

| lifetime_order_horizontal_array_path : forall to to_n from from_n ar,
   valid_array_path (hier) to to_n from from_n ar ->
   forall i1, 0 <= i1 -> forall i2, i1 < i2 -> i2 < to_n ->
     lifetime_order_horizontal from from_n (ar, i1, (Class.Inheritance.Repeated, to :: nil)) (ar, i2, (Class.Inheritance.Repeated, to :: nil))

| lifetime_order_horizontal_field : forall afrom zfrom apath ato i h p pto,
    valid_relative_pointer (hier) afrom zfrom apath ato i h p pto ->
    forall c, (hier) ! pto = Some c ->
      forall l0 l1 fs1 fs2 l2, (Class.fields c) = l0 ++ fs1 :: l1 ++ fs2 :: l2 ->
        forall cn1 n1,
        FieldSignature.type fs1 = FieldSignature.Struct cn1 n1 ->
        forall j1, 0 <= j1 < Zpos n1 ->
          forall apath1, apath1 = apath ++ (i, (h, p), fs1) :: nil ->
            forall cn2 n2,
              FieldSignature.type fs2 = FieldSignature.Struct cn2 n2 ->
              forall j2, 0 <= j2 < Zpos n2 ->
                forall apath2, apath2 = apath ++ (i, (h, p), fs2) :: nil ->
                  lifetime_order_horizontal afrom zfrom (apath1, j1, (Class.Inheritance.Repeated, cn1 :: nil)) (apath2, j2, (Class.Inheritance.Repeated, cn2 :: nil))

| lifetime_order_horizontal_virtual_base : forall to to_n from from_n ar,
   valid_array_path (hier) to to_n from from_n ar ->
   forall i, 0 <= i < to_n ->
     forall c, (hier) ! to = Some c ->
       forall l0 l1 cn1 cn2 l2, vborder_list (hier) (Class.super c) (l0 ++ cn1 :: l1 ++ cn2 :: l2) ->
         lifetime_order_horizontal from from_n (ar, i, (Class.Inheritance.Shared, cn1 :: nil)) (ar, i, (Class.Inheritance.Shared, cn2 :: nil))

| lifetime_order_horizontal_non_virtual_base : forall afrom zfrom apath ato i h p pto,
    valid_relative_pointer (hier) afrom zfrom apath ato i h p pto ->
    forall c, (hier) ! pto = Some c ->
      forall l0 l1 fs1 fs2 l2,  map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b) (filter (fun hb : _ * ident =>
          match hb with
            | (Class.Inheritance.Shared, _) => false
            | _ => true
          end
      ) (Class.super c)) = l0 ++ fs1 :: l1 ++ fs2 :: l2 ->
      forall p'1, p'1 = p ++ fs1 :: nil ->
        forall p'2, p'2 = p ++ fs2 :: nil ->
          lifetime_order_horizontal  afrom zfrom (apath, i, (h, p'1)) (apath, i, (h, p'2))

| lifetime_order_horizontal_virtual_non_virtual_base : forall to to_n from from_n ar,
   valid_array_path (hier) to to_n from from_n ar ->
   forall i, 0 <= i < to_n ->
     forall vb, is_virtual_base_of (hier) vb to ->
       forall c, (hier) ! to = Some c ->
         forall nvb, In (Class.Inheritance.Repeated, nvb) (Class.super c) ->
           lifetime_order_horizontal from from_n (ar, i, (Class.Inheritance.Shared, vb :: nil)) (ar, i, (Class.Inheritance.Repeated, to :: nvb :: nil))

| lifetime_order_horizontal_non_virtual_base_field : forall afrom zfrom apath ato i h p pto,
    valid_relative_pointer (hier) afrom zfrom apath ato i h p pto ->
    forall c, (hier) ! pto = Some c ->
      forall fs1, In (Class.Inheritance.Repeated, fs1) (Class.super c) ->
        forall fs, In fs (Class.fields c) ->
          forall fs2 n2, FieldSignature.type fs = FieldSignature.Struct fs2 n2 ->
            forall i2, 0 <= i2 < Zpos n2 ->
              forall p'1, p'1 = p ++ fs1 :: nil ->
                forall apath2, apath2 = apath ++ (i, (h, p), fs) :: nil ->
                  lifetime_order_horizontal  afrom zfrom (apath, i, (h, p'1)) (apath2, i2, (Class.Inheritance.Repeated, fs2 :: nil))

| lifetime_order_horizontal_virtual_base_field : forall to to_n from from_n ar,
   valid_array_path (hier) to to_n from from_n ar ->
   forall i, 0 <= i < to_n ->
     forall fs1, is_virtual_base_of (hier) fs1 to ->
      forall c, (hier) ! to = Some c ->
        forall fs, In fs (Class.fields c) ->
          forall fs2 n2, FieldSignature.type fs = FieldSignature.Struct fs2 n2 ->
            forall i2, 0 <= i2 < Zpos n2 ->
              forall apath2, apath2 = ar ++ (i, (Class.Inheritance.Repeated, to :: nil), fs) :: nil ->
                lifetime_order_horizontal  from from_n (ar, i, (Class.Inheritance.Shared, fs1 :: nil)) (apath2, i2, (Class.Inheritance.Repeated, fs2 :: nil))
.
  

(** * Subobject lifetime relation ("R" in technical report, <= in POPL 2012 submission) *)

Inductive lifetime : ident -> Z -> (array_path A * Z * (Class.Inheritance.t * list ident)) -> (array_path A * Z * (Class.Inheritance.t * list ident)) -> Prop :=
| lifetime_vertical : forall afrom zfrom o1 o2,
  inclusion afrom zfrom o1 o2 -> 
  lifetime afrom zfrom o1 o2
  
| lifetime_horizontal : forall afrom zfrom o1 o2,
  lifetime_order_horizontal afrom zfrom o1 o2 ->
  forall o'1, inclusion afrom zfrom o'1 o1 ->
  forall o'2, inclusion afrom zfrom o'2 o2 ->
    lifetime afrom zfrom o'1 o'2
.

Lemma lifetime_inclusion : forall afrom zfrom o1 o2,
  lifetime afrom zfrom o1 o2 ->
  forall o0,
    inclusion afrom zfrom o0 o1 ->
    lifetime afrom zfrom o0 o2.
Proof.
  inversion 1; subst.
  intros.
  eleft.
  eauto using inclusion_trans.
  intros.
  eright.
  eassumption.
  eauto using inclusion_trans.
  eassumption.
Qed.  

Lemma inclusion_order_array_path_prefix : forall afrom zfrom apath i h p apath' i' h' p',  
  inclusion_order afrom zfrom (apath', i', (h', p')) (apath, i, (h, p)) ->
  forall afrom0 zfrom0 apath0, valid_array_path (hier) afrom zfrom afrom0 zfrom0 apath0 ->
    inclusion_order afrom0 zfrom0 (apath0 ++ apath', i', (h', p')) (apath0 ++ apath, i, (h, p)).
Proof.
  inversion 1; subst.
   intros.
   inversion H5; subst.
   eapply inclusion_order_non_virtual.
   econstructor; eauto using valid_array_path_concat.
   eassumption.
   assumption.
  intros.
  eapply inclusion_order_virtual; eauto using valid_array_path_concat.
 inversion H9; subst.
 intros.
 eapply inclusion_order_field.
 econstructor; eauto using valid_array_path_concat.
 eassumption.
 eassumption.
 eassumption.
 assumption.
 rewrite app_ass.
 reflexivity.
Qed.

Corollary inclusion_array_path_prefix : forall afrom zfrom apath i h p apath' i' h' p',  
  inclusion afrom zfrom (apath', i', (h', p')) (apath, i, (h, p)) ->
  forall afrom0 zfrom0 apath0, valid_array_path (hier) afrom zfrom afrom0 zfrom0 apath0 ->
    inclusion afrom0 zfrom0 (apath0 ++ apath', i', (h', p')) (apath0 ++ apath, i, (h, p)).
Proof.
  intros until 1.
  revert H.
  var (apath', i', (h', p')).
  var (apath, i, (h, p)).
  intro.
  revert apath i h p apath' i' h' p' H H0.
  induction x; intros; subst.
   eapply t_step; eauto using inclusion_order_array_path_prefix.
  destruct y.
  destruct p0.
  destruct p1.
  eapply t_trans.
   eapply IHx1.
   reflexivity.
   reflexivity.
   assumption.
  eapply IHx2.
  reflexivity.
  reflexivity.
  assumption.
Qed.

Lemma lifetime_horizontal_array_path_prefix : forall afrom zfrom apath i h p apath' i' h' p',  
  lifetime_order_horizontal afrom zfrom (apath', i', (h', p')) (apath, i, (h, p)) ->
  forall afrom0 zfrom0 apath0, valid_array_path (hier) afrom zfrom afrom0 zfrom0 apath0 ->
    lifetime_order_horizontal afrom0 zfrom0 (apath0 ++ apath', i', (h', p')) (apath0 ++ apath, i, (h, p)).
Proof.
  inversion 1; subst.

   intros.
   eapply lifetime_order_horizontal_array_path; eauto using valid_array_path_concat.

  intros.
  inversion H8; subst.
  eapply lifetime_order_horizontal_field; eauto. 
   econstructor.
   eapply valid_array_path_concat.
   eassumption.
   eassumption.
   2: eassumption.
   assumption.
   eassumption.
   rewrite app_ass. reflexivity.
   rewrite app_ass. reflexivity.

   intros.
   eapply lifetime_order_horizontal_virtual_base; eauto using valid_array_path_concat.

  intros.
  inversion H8; subst.
  eapply lifetime_order_horizontal_non_virtual_base; eauto. 
   econstructor.
   eapply valid_array_path_concat.
   eassumption.
   eassumption.
   2: eassumption.
   assumption.
   eassumption.

  intros.   
  eapply lifetime_order_horizontal_virtual_non_virtual_base; eauto using valid_array_path_concat.

  intros.
  inversion H10; subst.  
  eapply lifetime_order_horizontal_non_virtual_base_field; eauto.
   econstructor.
   eapply valid_array_path_concat.
   eassumption.
   eassumption.
   2: eassumption.
   assumption.
   eassumption.
  rewrite app_ass. reflexivity.

  intros.   
  eapply lifetime_order_horizontal_virtual_base_field; eauto using valid_array_path_concat.
  rewrite app_ass.
  trivial.

Qed.

Corollary lifetime_array_path_prefix : forall afrom zfrom apath i h p apath' i' h' p',  
  lifetime afrom zfrom (apath', i', (h', p')) (apath, i, (h, p)) ->
  forall afrom0 zfrom0 apath0, valid_array_path (hier) afrom zfrom afrom0 zfrom0 apath0 ->
    lifetime afrom0 zfrom0 (apath0 ++ apath', i', (h', p')) (apath0 ++ apath, i, (h, p)).
Proof.
  inversion 1; subst.
   intros; eleft; eauto using inclusion_array_path_prefix.
  intros.
  destruct o1.
  destruct p0.
  destruct p1.
  destruct o2.
  destruct p0.
  destruct p1.
  eright.
   eapply lifetime_horizontal_array_path_prefix.
   eassumption.
   eassumption.
  eauto using inclusion_array_path_prefix.
  eauto using inclusion_array_path_prefix.
Qed.


     Remark distinct_paths_cases : forall (A : Type) (aeq : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}) (l1 l2 : _ A),
       (length l1 <= length l2)%nat ->
       l1 <> l2 ->
       {a : _ & {l2' | l2 = l1 ++ a :: l2'}} + 
       {l : _ & { a1 : _ & { a2 : _ & { l1' : _ & { l2' |
         l1 = l ++ a1 :: l1' /\ l2 = l ++ a2 :: l2' /\ a1 <> a2}}}}}.
     Proof.
       induction l1 ; simpl.
       destruct l2 ; simpl.
       congruence.
       intros _ _.
       left.
       esplit.
       esplit.
       reflexivity.
       destruct l2 ; simpl.
       intro.
       omegaContradiction.
       intros until 2.
       destruct (aeq a a0).
       subst.
       assert (length l1 <= length l2)%nat by omega.
       assert (l1 <> l2) by congruence.
       destruct (IHl1 _ H1 H2).
       destruct s.
       destruct s.
       subst.
       left.
       esplit.
       esplit.
       reflexivity.
       destruct s.
       destruct s.
       destruct s.
       destruct s.
       destruct s.
       destruct a.
       destruct H4.
       subst.
       right.
       exists (a0 :: x).
       esplit.
       esplit.
       esplit.
       esplit.
       split.
       simpl.
       reflexivity.
       split.
       simpl.
       reflexivity.
       assumption.
       right.
       exists (@nil A0).
       esplit.
       esplit.
       esplit.
       esplit.
       split.
       simpl.
       reflexivity.
       split.
       simpl.
       reflexivity.
       assumption.
     Qed.

Section Lifetime_total.


Hypothesis hierarchy_wf : Well_formed_hierarchy.prop (hier).


Lemma lifetime_inheritance_subobject : forall afrom zfrom apath ato i h p pto,
    valid_relative_pointer (hier) afrom zfrom apath ato i h p pto ->
    forall h1 p1 pto', path (hier) pto' p1 pto h1 ->
      forall h' p', (h', p') = concat (h, p) (h1, p1) ->
        lifetime afrom zfrom (apath, i, (h', p')) (apath, i, (h, p)).
Proof.
  intros.
  generalize (path_path1 H0).
  inversion 1; subst.
   (* repeated *)
   eleft.
   eleft.
   eapply inclusion_order_non_virtual.
   eassumption.
   eassumption.
   assumption.
  (* shared *)
  injection H1; intros; subst.
  inversion H4; subst.
  inversion H; subst.
  assert (is_virtual_base_of hier base ato) by eauto using path_is_virtual_base_of.
  assert (valid_relative_pointer hier afrom zfrom apath ato i Class.Inheritance.Shared (base :: nil) base    
  ).
   econstructor.
   eassumption.
   assumption.
   assumption.
   eright.
   eassumption.
   eleft with (lt := nil).
   reflexivity.
   reflexivity.
   simpl.
   generalize (path_defined_from H4).
   destruct (hier ! base); congruence.
  assert (inclusion afrom zfrom (apath, i, (Class.Inheritance.Shared, base :: lf)) (apath, i, (Class.Inheritance.Shared, base :: nil))) as Hi.
   eleft.
   eapply inclusion_order_non_virtual.
   eassumption.
   eassumption.
   simpl.
   destruct (peq base base); congruence.
  generalize (path_path1 H10).  
  inversion 1; subst.
   (* repeated *)
   functional inversion H16; subst.
    (* most-derived *)
    eleft.
    eright.
    eassumption.
    eleft.
    eapply inclusion_order_virtual.
    eassumption.
    split; assumption.
    assumption.
   (* non-virtual subobject *)
   eright.
   eapply lifetime_order_horizontal_virtual_non_virtual_base.
   eassumption.
   split; eassumption.
   eassumption.
   eassumption.
   eassumption.
   assumption.
  eleft.
  case_eq (last (id2 :: l3)).
   intros.
   destruct (last_correct H14).
   eapply inclusion_order_non_virtual.
   econstructor.
   eassumption.
   assumption.
   assumption.
   eleft with (lt := ato :: nil).
   reflexivity.
   simpl; reflexivity.
   simpl.
   rewrite H19.
   rewrite H22.
   revert X.
   simpl.
   destruct (hier ! id2); congruence.
 eleft.
 reflexivity.
 eassumption.
 assumption.
 simpl.
 destruct (peq id2 id2); congruence.
 intro.
 assert (id2 :: l3 <> nil) by congruence.
 generalize (last_nonempty H17).
 intro; contradiction.
(* virtual *)
inversion H15; subst.
generalize (path_defined_from H10).
intro.
case_eq (hier ! ato); try contradiction.
clear H16.
intros.
destruct (Well_formed_hierarchy.vborder_list_exists hierarchy_wf H16).
assert (is_virtual_base_of hier base base0) by eauto using path_is_virtual_base_of.
generalize (vborder_list_bases_first v (virtual_base_vborder_list H14 H16 v) H19).
destruct 1.
invall; subst.
eright.
eapply lifetime_order_horizontal_virtual_base.
eassumption.
split; eassumption.
eassumption.
eassumption.
assumption.
eleft.
eapply inclusion_order_non_virtual.
econstructor.
eassumption.
assumption.
assumption.
eright.
eassumption.
eleft with (lt := nil).
reflexivity.
reflexivity.
simpl.
generalize (path_defined_from H15).
destruct (hier ! base0); congruence.
eassumption.
simpl. destruct (peq base0 base0); congruence.
Qed.

Lemma inclusion_field_subobject : forall afrom zfrom apath ato i h' p' pto',
  valid_relative_pointer (hier) afrom zfrom apath ato i h' p' pto' ->
  forall c, hier ! pto' = Some c ->
    forall f, In f (Class.fields c) ->
      forall cl sz, FieldSignature.type f = FieldSignature.Struct cl sz ->
        forall a'' ato'' i'' h'' p'' pto'',
          valid_relative_pointer hier cl (Zpos sz) a'' ato'' i'' h'' p'' pto'' ->
          inclusion afrom zfrom (apath ++ (i, (h', p'), f) :: a'', i'', (h'', p'')) (apath, i, (h', p')).
Proof.
  intros.
  destruct (inclusion_subobject_of_full_object H3).
  invall.
  inversion H; subst.
  inversion H3; subst.
  eright.
  replace (apath ++ (i, (h', p'), f) :: a'') with ((apath ++ (i, (h', p'), f) :: nil) ++ a'').
  eapply inclusion_array_path_prefix.
  eassumption.
  eapply valid_array_path_concat.
  eassumption.
  econstructor.
  assumption.
  assumption.
  eassumption.
  eassumption.
  assumption.
  eassumption.
  econstructor.
  omega.
  omega.
  rewrite app_ass; trivial.
 rewrite app_ass.
 simpl.
 eleft.
 eapply inclusion_order_field.
 eassumption.
 eassumption.
 eassumption.
 eassumption.
 split; assumption.
 reflexivity.
Qed. 

Corollary lifetime_field_subobject : forall afrom zfrom apath ato i h p pto,
    valid_relative_pointer (hier) afrom zfrom apath ato i h p pto ->
    forall h1 p1 pto', path (hier) pto' p1 pto h1 ->
      forall h' p', (h', p') = concat (h, p) (h1, p1) ->
        forall c, hier ! pto' = Some c ->
          forall f, In f (Class.fields c) ->
            forall cl sz, FieldSignature.type f = FieldSignature.Struct cl sz ->
              forall a'' ato'' i'' h'' p'' pto'',
              valid_relative_pointer hier cl (Zpos sz) a'' ato'' i'' h'' p'' pto'' ->
              lifetime afrom zfrom (apath ++ (i, (h', p'), f) :: a'', i'', (h'', p'')) (apath, i, (h, p)).
Proof.
  intros.
  eapply lifetime_inclusion.
  eauto using lifetime_inheritance_subobject.
  inversion H; subst.
  eapply inclusion_field_subobject.
  econstructor.
  eassumption.
  assumption.
  assumption.
  eauto using path_concat.
  eassumption.
  assumption.
  eassumption.
  eassumption.
Qed.

Section Is_subobject_of.

Variable afrom : ident.
Variable zfrom : Z.

Inductive is_subobject_of : (array_path A * Z * (Class.Inheritance.t * list ident)) -> (array_path A * Z * (Class.Inheritance.t * list ident)) -> Prop :=
| is_subobject_if_base : forall apath ato i h p pto,
    valid_relative_pointer (hier) afrom zfrom apath ato i h p pto ->
    forall h1 p1 pto', path (hier) pto' p1 pto h1 ->
      forall h' p', (h', p') = concat (h, p) (h1, p1) ->
        is_subobject_of (apath, i, (h', p')) (apath, i, (h, p))
| is_subobject_of_field : forall apath ato i h p pto,
  valid_relative_pointer (hier) afrom zfrom apath ato i h p pto ->
  forall h1 p1 pto', path (hier) pto' p1 pto h1 ->
    forall h' p', (h', p') = concat (h, p) (h1, p1) ->
      forall c, hier ! pto' = Some c ->
        forall f, In f (Class.fields c) ->
          forall cl sz, FieldSignature.type f = FieldSignature.Struct cl sz ->
            forall a'' ato'' i'' h'' p'' pto'',
              valid_relative_pointer hier cl (Zpos sz) a'' ato'' i'' h'' p'' pto'' ->
              forall apath'', apath'' = apath ++ (i, (h', p'), f) :: a'' ->
              is_subobject_of (apath'', i'', (h'', p'')) (apath, i, (h, p))
.

Theorem lifetime_subobject : forall arihp1 arihp2,
  is_subobject_of arihp1 arihp2 ->
  lifetime afrom zfrom arihp1 arihp2.
Proof.
  inversion 1; subst;
  eauto using lifetime_inheritance_subobject,
    lifetime_field_subobject.
Qed.

End Is_subobject_of.

(** * POPL 2012 submission: Lemma 10 *)

Theorem lifetime_total : forall apath1 afrom zfrom ato1 i1 h1 p1 pto1,
    valid_relative_pointer (hier) afrom zfrom apath1 ato1 i1 h1 p1 pto1 ->
    forall apath2 ato2 i2 h2 p2 pto2,
    valid_relative_pointer (hier) afrom zfrom apath2 ato2 i2 h2 p2 pto2 ->
    lifetime afrom zfrom (apath1, i1, (h1, p1)) (apath2, i2, (h2, p2)) \/
    lifetime afrom zfrom (apath2, i2, (h2, p2)) (apath1, i1, (h1, p1)).
Proof.
 intro.
 generalize (refl_equal (length apath1)).
 generalize (length apath1) at 1.
 intro.
 revert apath1.
 induction n using (well_founded_induction lt_wf).
  intros.  
  rewrite <- (relative_pointer_default_to_alt_to_default).
  rewrite <- (relative_pointer_default_to_alt_to_default).
  generalize (valid_relative_pointer_valid_relative_pointer_alt H1).
  clear H1.
  generalize (valid_relative_pointer_valid_relative_pointer_alt H2).
  clear H2.
  revert H0.
  rewrite <- (relative_pointer_alt_length_correct apath1 i1 (h1, p1)).
  generalize (relative_pointer_alt_of_relative_pointer apath1 i1 (h1, p1)).
  generalize (relative_pointer_alt_of_relative_pointer apath2 i2 (h2, p2)).
  clear apath1 i1 h1 p1 apath2 i2 h2 p2.
  destruct r.
  destruct r.
  destruct (Z_eq_dec i i0).

   Focus 2. (* different cells *)
   intros.
   clear H0.
   revert i p f i0 p0 f0 n0 ato1 pto1 ato2 pto2 H1 H2.
   cut (
      forall (i : Z) (p : Class.Inheritance.t * list ident)
     (f : option
            (FieldSignature.t A * array_path A * Z *
             (Class.Inheritance.t * list ident))) (i0 : Z)
     (p0 : Class.Inheritance.t * list ident)
     (f0 : option
             (FieldSignature.t A * array_path A * Z *
              (Class.Inheritance.t * list ident))),
   i < i0 ->
   forall ato1 pto1 ato2 pto2 : ident,
   valid_relative_pointer_alt (hier) afrom zfrom ato2 pto2
     (relative_pointer_alt_intro i p f) ->
   valid_relative_pointer_alt (hier) afrom zfrom ato1 pto1
     (relative_pointer_alt_intro i0 p0 f0) ->
     lifetime afrom zfrom
     (relative_pointer_of_relative_pointer_alt
       (relative_pointer_alt_intro i p f))
     (relative_pointer_of_relative_pointer_alt
       (relative_pointer_alt_intro i0 p0 f0))
   ).
    intros.
    destruct (Z_lt_dec i i0).
     eauto 8.
    assert (i0 < i) by abstract omega.
    eauto.
   intros.
   inversion H1; subst.
   inversion H2; subst.
   eright.
    eapply lifetime_order_horizontal_array_path.
    eleft.
    2 : eapply Zle_refl.
    abstract omega.
    eapply H6.
    eexact H0.
    assumption.
    eright.
    eapply inclusion_relative_pointer_alt.
    eassumption.
   eapply inclusion_inheritance_subobject_of_full_object.
   econstructor.
   2 : eapply Zle_refl.
   abstract omega.
   auto.
   eassumption.
  eright.
    eapply inclusion_relative_pointer_alt.
    eassumption.
   eapply inclusion_inheritance_subobject_of_full_object.
   econstructor.
   2 : eapply Zle_refl.
   abstract omega.
   auto.
   eassumption.
 (* same cells *)
   subst.
   destruct p0.
   destruct p.
   destruct (Class.Inheritance.eq_dec t t0).

   Focus 2.  (* virtual and non-virtual bases *)
   intros _.
   revert t t0 l0 f l f0 n0 ato1 pto1 ato2 pto2.
   cut (forall 
      (l0 : list ident)
     (f : option
            (FieldSignature.t A * array_path A * Z *
             (Class.Inheritance.t * list ident))) (l : list ident)
     (f0 : option
             (FieldSignature.t A * array_path A * Z *
              (Class.Inheritance.t * list ident))) ato1 pto1 ato2 pto2,
   valid_relative_pointer_alt (hier) afrom zfrom ato2 pto2
     (relative_pointer_alt_intro i0 (Class.Inheritance.Repeated, l0) f) ->
   valid_relative_pointer_alt (hier) afrom zfrom ato1 pto1
     (relative_pointer_alt_intro i0 (Class.Inheritance.Shared, l) f0) ->
   lifetime afrom zfrom
     (relative_pointer_of_relative_pointer_alt
        (relative_pointer_alt_intro i0 (Class.Inheritance.Shared, l) f0))
     (relative_pointer_of_relative_pointer_alt
        (relative_pointer_alt_intro i0 (Class.Inheritance.Repeated, l0) f))
   ).
    intros; destruct t; destruct t0; try abstract congruence; eauto.
   intros.
   inversion H0; subst.
   inversion H1; subst.
   generalize (path_path1 H12).
   inversion 1; subst.
   inversion H4; subst.
   inversion H8; subst.
   assert (inclusion afrom zfrom
     (relative_pointer_of_relative_pointer_alt
       (relative_pointer_alt_intro i0 (Class.Inheritance.Shared, base :: lf)
         f0))
     (nil, i0, (Class.Inheritance.Shared, base :: nil))
   ).
    eright.
    eapply inclusion_relative_pointer_alt.
    eassumption.
   eleft.
   eapply inclusion_order_non_virtual.
   econstructor.
   econstructor.
   2 : eapply Zle_refl.
   abstract omega.
   assumption.
   assumption.
   eright.
    eassumption.
    eleft with (lt := nil).
    reflexivity.
    reflexivity.
    generalize H15.
    simpl.
    destruct ((hier) ! base); abstract congruence.
   eexact H4.
   simpl.
   destruct (peq base base); abstract congruence.
  destruct lf0.

   destruct f. (* vb and field *)
     destruct p.
     destruct p.
     destruct p.
     destruct p0.
     invall; subst.
     generalize (refl_equal (last (afrom :: nil))).
     rewrite H16 at 1.
     rewrite last_complete.
     injection 1; intros; subst.
     var (
 (relative_pointer_of_relative_pointer_alt
        (relative_pointer_alt_intro i0 (Class.Inheritance.Shared, base :: lf)
           f0))
     ).
     simpl.
     assert (exists j, 0 <= j < Zpos x1 /\ inclusion afrom zfrom ((i0, (Class.Inheritance.Repeated, afrom :: nil), t) :: a, z, (t0, l))  ((i0, (Class.Inheritance.Repeated, afrom :: nil), t) :: nil, j, (Class.Inheritance.Repeated, x0 :: nil))).
     change (
       (i0, (Class.Inheritance.Repeated, afrom :: nil), t) :: a
     ) with (
       ((i0, (Class.Inheritance.Repeated, afrom :: nil), t) :: nil) ++ a
     ).
     eapply  inclusion_subobject_of_array_path_full_object.
     eassumption.
     econstructor.
     assumption.
     assumption.
     eassumption.
     eassumption.
     assumption.
     eassumption.
     econstructor.
     compute; abstract congruence.
     eapply Zle_refl.
    destruct H23.
    destruct H23.
    subst.
    eapply lifetime_horizontal. 
    eapply lifetime_order_horizontal_virtual_base_field.
    eleft.
    3 : eexact (conj H6 H7).
    abstract omega.
    abstract omega.    
      eassumption.
     eassumption.
     eassumption.
     eassumption.
     eassumption.
     reflexivity.
     eassumption.
     eassumption.

    (* vb and full object *)
    eapply lifetime_vertical.
    eapply inclusion_trans.
    eassumption.
    eleft.
    eapply inclusion_order_virtual.
    eleft.
    3 : split; eassumption.
    abstract omega.
    abstract omega.
    assumption.

   (* vb and non vb *)
   functional inversion H17; subst.
   destruct lt0; simpl in H16; try discriminate.
   injection H16; intros; subst.
   eapply lifetime_horizontal.
   eapply lifetime_order_horizontal_virtual_non_virtual_base.
   3 : eassumption.
   3 : eassumption.
   3 : eassumption.
   3 : eassumption.
   2 : split; eassumption.
   eleft.
   abstract omega.
   abstract omega.
   eright.   
   eapply inclusion_relative_pointer_alt.
   eassumption.
   eleft.
   eapply inclusion_order_non_virtual.
   econstructor.
   econstructor.
   2 : eapply Zle_refl.
   abstract omega.
   assumption.
   assumption.
   eleft with (lt := i1 :: nil).
   reflexivity.
   simpl.
   reflexivity.
   revert X.
   simpl.
   rewrite H22.
   rewrite H25.
   destruct ((hier) ! i); abstract congruence.
  eleft.
  reflexivity.
  eassumption.
  assumption.
  simpl.
  destruct (peq i i); abstract congruence.

 (* same virtuality *)
  subst.
  destruct (list_eq_dec peq l0 l).
   (* same paths *)
   subst.
   cut (
     forall ato1 pto1 f1,
       valid_relative_pointer_alt (hier) afrom zfrom ato1 pto1
       (relative_pointer_alt_intro i0 (t0, l) (Some f1)) ->
       lifetime afrom zfrom
       (relative_pointer_of_relative_pointer_alt
         (relative_pointer_alt_intro i0 (t0, l) (Some f1)))
       (relative_pointer_of_relative_pointer_alt
         (relative_pointer_alt_intro i0 (t0, l) None))
   ).
   intros.
   destruct f; destruct f0; eauto; simpl in *.
    (* IH *)
    destruct p.
    destruct p.
     destruct p.
     destruct p0.
     destruct p.
     destruct p.
    inversion H2; subst.
    destruct p1.
    invall; subst.
    inversion H3; subst.
    destruct p0.
    invall; subst.
    destruct (FieldSignature.eq_dec t1 t).
     subst. (* same field : IH *)
     assert (length a0 < S (length a0))%nat by abstract omega.
     replace x4 with x1 in * by abstract congruence.
     replace x3 with x0 in * by abstract congruence.
     assert (valid_array_path (hier) x0 (Zpos x1) afrom zfrom ((i0, (t0, l), t) :: nil)).
     econstructor.
      assumption.
      assumption.
      eassumption.
      eassumption.
      assumption.
      eassumption.
      econstructor.
      compute; abstract congruence.
      apply Zle_refl.
     change (
       (i0, (t0, l), t) :: a0
     ) with (
       ((i0, (t0, l), t) :: nil) ++ a0
     ).
     change (
       (i0, (t0, l), t) :: a
     ) with (
       ((i0, (t0, l), t) :: nil) ++ a
     ).
     destruct (H _ H13 _ (refl_equal _) _ _ _ _ _ _ _ H17 _ _ _ _ _ _ H7);    
      eauto using lifetime_array_path_prefix.
   
   (* different fields *)
     generalize (path_last H10).
     generalize (path_last H16).
     intros.
     replace through0 with through in * by abstract congruence.
     replace x2 with x in * by abstract congruence.
     clear H2 H3.
     clear H.
     revert t H1 x0 x1 H5 t1 H6 x3 x4 H12 n a0 z0 t3 l1 a z t2 l0  ato1 pto1 ato2 pto2 H7 H17.
     cut (
       forall fl0 t1 fl1 t2 fl4,
         Class.fields x = fl0 ++ t1 :: fl1 ++ t2 :: fl4 ->
         forall (x0 : ident) (x1 : positive),
           FieldSignature.type t1 = FieldSignature.Struct x0 x1 ->
           forall (x3 : ident) (x4 : positive),
             FieldSignature.type t2 = FieldSignature.Struct x3 x4 ->
             forall (a0 : array_path A) (z0 : Z) (t3 : Class.Inheritance.t)
               (l1 : list ident) (a : array_path A) (z : Z) (t4 : Class.Inheritance.t)
               (l0 : list ident) (ato1 pto1 ato2 pto2 : ident),
               valid_relative_pointer (A:=A) (hier) x0 
               (Zpos x1) a ato2 z t4 l0 pto2 ->
               valid_relative_pointer (A:=A) (hier) x3 
               (Zpos x4) a0 ato1 z0 t3 l1 pto1 ->
               lifetime afrom zfrom ((i0, (t0, l), t2) :: a0, z0, (t3, l1))
               ((i0, (t0, l), t1) :: a, z, (t4, l0)) \/
               lifetime afrom zfrom ((i0, (t0, l), t1) :: a, z, (t4, l0))
               ((i0, (t0, l), t2) :: a0, z0, (t3, l1))
     ).
      intros.
      destruct (list_lt_total  (@FieldSignature.eq_dec _) H6 H1); try contradiction.
      unfold list_lt in s.
       destruct s;
       invall; subst; eauto.
       assert (forall A B : Prop, A \/ B -> B \/ A) by tauto.
       eauto.
      intros.
      right.
      assert (
        valid_array_path (A:=A) (hier) x0 
        (Zpos x1) afrom zfrom ((i0, (t0, l), t1) :: nil)      
      ).
       econstructor.
       assumption.
       assumption.
       eassumption.
       eassumption.
       rewrite H; eauto using in_or_app.
       eassumption.
       econstructor.
       compute; abstract congruence.
       abstract omega.
      assert (
        valid_array_path (A:=A) (hier) x3 
        (Zpos x4) afrom zfrom ((i0, (t0, l), t2) :: nil)      
      ).
       econstructor.
       assumption.
       assumption.
       eassumption.
       eassumption.
       rewrite H; eauto 6 using in_or_app.
       eassumption.
       econstructor.
       compute; abstract congruence.
       abstract omega.       
      generalize (inclusion_subobject_of_array_path_full_object H3 H6).
      intros; invall; subst.
      generalize (inclusion_subobject_of_array_path_full_object H5 H7).
      intros; invall; subst.
      simpl in H19, H22.
      eright.
      eapply lifetime_order_horizontal_field.
      econstructor.
      eleft.
      2 : eapply Zle_refl.
      abstract omega.
      2 : eassumption.
      assumption.
      eassumption.
      eassumption.
      eassumption.
      eassumption.
      split. 
      2 : eassumption.
      assumption.
      reflexivity.
      eassumption.
      split.
      2 : eassumption.
      assumption.
      reflexivity.
      assumption.
      assumption.

  (* no field, same subobject *)
  left.
  eleft.
  eapply inclusion_refl.
  eauto using valid_relative_pointer_alt_valid_relative_pointer.

  (* a field on one side, none on the other *)
  inversion 1; subst.
  destruct f1.
  destruct p.
  destruct p.
  destruct p0.
  invall; subst.
  simpl.
  assert (
    valid_array_path (hier) x0 (Zpos x1) afrom zfrom ((i0, (t0, l), t) :: nil)
  ).
   econstructor; eauto.
   econstructor.
   compute; abstract congruence.
   eapply Zle_refl.
  generalize (inclusion_subobject_of_array_path_full_object H8 H4).
  simpl; intro; invall; subst.
  eleft.
  eright.
  eassumption.
  eleft.
  eapply inclusion_order_field.
  econstructor.
  eleft.
  2 : eapply Zle_refl.
  abstract omega.
  assumption.
  assumption.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  auto.
  reflexivity.

(* different paths *)
intros _.
clear H.
 revert l0 l n0 ato1 pto1 ato2 pto2 f f0.
 cut (
   forall l0 l : list ident,
     l0 <> l ->
     (length l0 <= length l)%nat ->
   forall (ato1 pto1 ato2 pto2 : ident)
     (f
      f0 : option
             (FieldSignature.t A * array_path A * Z *
              (Class.Inheritance.t * list ident))),
   valid_relative_pointer_alt (hier) afrom zfrom ato2 pto2
     (relative_pointer_alt_intro i0 (t0, l0) f) ->
   valid_relative_pointer_alt (hier) afrom zfrom ato1 pto1
     (relative_pointer_alt_intro i0 (t0, l) f0) ->
   lifetime afrom zfrom
     (relative_pointer_of_relative_pointer_alt
        (relative_pointer_alt_intro i0 (t0, l) f0))
     (relative_pointer_of_relative_pointer_alt
        (relative_pointer_alt_intro i0 (t0, l0) f)) \/
   lifetime afrom zfrom
     (relative_pointer_of_relative_pointer_alt
        (relative_pointer_alt_intro i0 (t0, l0) f))
     (relative_pointer_of_relative_pointer_alt
        (relative_pointer_alt_intro i0 (t0, l) f0))
 ).
  intros.
  destruct (le_lt_dec (length l0) (length l)).
   eauto.
  assert (length l <= length l0)%nat by abstract omega.
  assert (l <> l0) by abstract congruence.
  assert (forall A B : Prop, A \/ B -> B \/ A) by tauto.
  eauto.
 intros until 2.
 destruct (distinct_paths_cases peq H0 H).

  (* non-virtual subobject *)
  destruct s.
  destruct s.
  subst.
  intros.
  generalize (inclusion_relative_pointer_alt H2).
  intros.
  inversion H1; subst.
  inversion H2; subst.
  generalize (path_last H10).
  intros.
  destruct (last_correct H4).
  subst.
  assert (
    is_valid_repeated_subobject (hier) (x1 ++ through :: x :: x0) = true
  ).
   generalize (path_path0 H14).
   rewrite app_ass.
   simpl.
   inversion 1; subst; assumption.
  generalize (is_valid_repeated_subobject_split_right H5).
  functional inversion 1; subst.
  assert (
    path (hier) through0 (x :: x0) x Class.Inheritance.Repeated
  ).
   generalize (path_last H14).
   rewrite last_app_left; try abstract congruence.
   intro.
   destruct (last_correct H7).
   eleft.
   reflexivity.
   eassumption.
   assumption.
  destruct f.
    (* field vs nvbase *)
    destruct p.
    destruct p.
    destruct p.
    destruct p0.
    invall; subst.
    replace x2 with cl1 in * by abstract congruence.
    assert (
      valid_array_path (hier) x3 (Zpos x4) afrom zfrom ((i0, (t0, x1 ++ through :: nil), t) :: nil)
    ).
     econstructor.
     assumption.
     assumption.
     eassumption.
     eassumption.
     assumption.
     eassumption.
     eleft.
     compute; abstract congruence.
     abstract omega.
    generalize (inclusion_subobject_of_array_path_full_object H20 H18).
    intro; invall; subst.
    simpl in H24.
    left.
    eright.     
     eapply lifetime_order_horizontal_non_virtual_base_field.
     2 : eassumption.
     econstructor.
     eleft.
     2 : eapply Zle_refl.
     abstract omega.
     2 : eassumption.
     assumption.
     eassumption.
     eassumption.
     eassumption.
     eassumption.
     split.
      2 : eassumption.
     assumption.
     reflexivity.
     reflexivity.
    eright.
    eassumption.
    eleft.
    eapply inclusion_order_non_virtual.
    2 : eexact H7.
    3 : eassumption.
    econstructor.
    econstructor.
    2 : eapply Zle_refl.
    abstract omega.
    assumption.
    assumption.
    eapply path_concat.
    eexact H10.
    eleft with (lt := through :: nil).
    reflexivity.
    simpl.
    reflexivity.
    simpl.
    rewrite H11.
    rewrite H22.
    revert X.
    simpl.
    destruct ((hier) ! x); abstract congruence.
    simpl.
    rewrite last_complete.
    destruct (peq through through); try abstract congruence.
    simpl.
    rewrite last_complete.
    destruct (peq x x); try abstract congruence.
    rewrite app_ass.
    rewrite app_ass.
    rewrite app_ass.
    reflexivity.

  (* no field : non-virtual subobject *)
  left.
  generalize (path_last H7).
  intro.
  destruct (last_correct H16).
  eleft.
  eright.
  eassumption.
  simpl.
  eleft.
  eapply inclusion_order_non_virtual.
  econstructor.
  econstructor.
  2 : eapply Zle_refl.
  abstract omega.
  assumption.
  assumption.
  eassumption.
  eleft with (lf := x :: x0) (lt := through :: x2).
  reflexivity.
  rewrite e.
  simpl.
  reflexivity.
  assumption.
  simpl.
  rewrite last_complete.
  destruct (peq through through); try abstract congruence.
  trivial.

(* divergent paths *)
clear H H0.
destruct s.
destruct s.
destruct s.
destruct s.
destruct s.
invall; subst.
destruct x.
 (* different virtual bases *)
 change (nil ++ x0 :: x2) with (x0 :: x2).
 change (nil ++ x1 :: x3) with (x1 :: x3).
 intros until 2.
 assert (t0 = Class.Inheritance.Shared /\ is_virtual_base_of (hier) x0 afrom /\ is_virtual_base_of (hier) x1 afrom).
  inversion H; subst.
  inversion H0; subst.
  generalize (path_path1 H8).
  inversion 1; subst.
   inversion H12; subst.
   abstract congruence.
  generalize (path_path1 H12).
  inversion 1; subst.
  inversion H15; subst.
  injection H16; intros; subst.
  inversion H4; subst.
  injection H19; intros; subst.
  auto.
 invall; subst.
 generalize (is_virtual_base_of_defined H1).
 intros.
 case_eq ((hier) ! afrom); try abstract congruence.
 intros.
 destruct  (Well_formed_hierarchy.vborder_list_exists hierarchy_wf H4).
 generalize (virtual_base_vborder_list H1 H4 v).
 intros.
 generalize (virtual_base_vborder_list H5 H4 v).
 intros.
 revert x0 x1 H2 H6 H7  H1 H5 x3 f0 x2 f ato1 pto1 ato2 pto2 H H0.
 cut (
   forall v0 x0 v1 x1 x2, x = v0 ++ x0 :: v1 ++ x1 :: x2 ->
       is_virtual_base_of (A:=A) (hier) x0 afrom ->
   is_virtual_base_of (A:=A) (hier) x1 afrom ->
   forall (x3 : list positive)
     (f0 : option
             (FieldSignature.t A * array_path A * Z *
              (Class.Inheritance.t * list ident))) 
     (x2 : list positive)
     (f : option
            (FieldSignature.t A * array_path A * Z *
             (Class.Inheritance.t * list ident)))
     (ato1 pto1 ato2 pto2 : ident),
   valid_relative_pointer_alt (hier) afrom zfrom ato2 pto2
     (relative_pointer_alt_intro i0 (Class.Inheritance.Shared, x0 :: x2) f) ->
   valid_relative_pointer_alt (hier) afrom zfrom ato1 pto1
     (relative_pointer_alt_intro i0 (Class.Inheritance.Shared, x1 :: x3) f0) ->
   lifetime afrom zfrom
     (relative_pointer_of_relative_pointer_alt
        (relative_pointer_alt_intro i0 (Class.Inheritance.Shared, x1 :: x3)
           f0))
     (relative_pointer_of_relative_pointer_alt
        (relative_pointer_alt_intro i0 (Class.Inheritance.Shared, x0 :: x2) f)) \/
   lifetime afrom zfrom
     (relative_pointer_of_relative_pointer_alt
        (relative_pointer_alt_intro i0 (Class.Inheritance.Shared, x0 :: x2) f))
     (relative_pointer_of_relative_pointer_alt
        (relative_pointer_alt_intro i0 (Class.Inheritance.Shared, x1 :: x3)
           f0))
 ).
  intros.
  generalize (list_lt_total peq H6 H7).
  unfold list_lt.
  destruct 1; try contradiction.
  destruct s; invall; subst.
  eauto.
  assert (forall A B : Prop, A \/ B -> B \/ A) by tauto.
  eauto.
 intros; subst.
 inversion H2; subst.
 right.
 eright.
 eapply lifetime_order_horizontal_virtual_base.
 eleft.
 2 : eapply Zle_refl.
 abstract omega.
 split.
 2 : eassumption.
 assumption.
 eassumption.
 eassumption.
 eright.
 eapply inclusion_relative_pointer_alt.
 eassumption.
 generalize (path_path1 H11).
 inversion 1; subst.
 inversion H7; subst.
 injection H8; intros; subst.
 eleft.
 eapply inclusion_order_non_virtual.
 econstructor.
 econstructor.
 2 : eapply Zle_refl.
 abstract omega.
 assumption.
 assumption.
 eright.
 eassumption.
 eleft with (lt := nil).
 reflexivity.
 reflexivity.
 simpl.
 generalize (Well_formed_hierarchy.is_virtual_base_of_defined_base hierarchy_wf H0).
 destruct ((hier) ! base); abstract congruence.
 eassumption.
 simpl.
 destruct (peq base base); abstract congruence.
 eright.
 eapply inclusion_relative_pointer_alt.
 eassumption.
 inversion H5; subst.
 generalize (path_path1 H15).
 inversion 1; subst.
 inversion H7; subst.
 injection H8; intros; subst.
 eleft.
 eapply inclusion_order_non_virtual.
 econstructor.
 econstructor.
 2 : eapply Zle_refl.
 abstract omega.
 assumption.
 assumption.
 eright.
 eassumption.
 eleft with (lt := nil).
 reflexivity.
 reflexivity.
 simpl.
 generalize (Well_formed_hierarchy.is_virtual_base_of_defined_base hierarchy_wf H1).
 destruct ((hier) ! base); abstract congruence.
 eassumption.
 simpl.
 destruct (peq base base); abstract congruence.

(* different non-virtual bases (of the same (maybe virtual) inheritance subobject)  *)
assert (p :: x <> nil) by abstract congruence.
generalize (last_nonempty H).
case_eq (last (p :: x)); try abstract congruence.
intros ? ? _.
destruct (last_correct H0).
rewrite e in *.
clear p x e H H0.
inversion 1; subst.
assert (is_valid_repeated_subobject (hier) ((x4 ++ p0 :: nil) ++ x0 :: x2) = true).
 generalize (path_path1 H7).
 inversion 1; subst; trivial.
 inversion H3; subst; trivial.
generalize H0.
rewrite app_ass at 1.
intro.
generalize (is_valid_repeated_subobject_split_left H1).
intro.
assert (
  path (hier) p0 (x4 ++ p0 :: nil) afrom t0
).
  case_eq (x4 ++ p0 :: nil).
   destruct x4; simpl; intro; discriminate.
  intros.
 generalize (path_path1 H7).
 inversion 1; subst.
  rewrite H4 in H10.
  simpl in H10.
  injection H10; intros; subst.
  eleft.
  reflexivity.
  symmetry; eassumption.
  rewrite <- H4; assumption.
 inversion H11; subst.
 rewrite H4 in H12.
 simpl in H12.
 injection H12; intros; subst.
 eright.
 eassumption.
 eleft.
 reflexivity.
 symmetry; eassumption.
 rewrite <- H4; assumption.
 generalize (is_valid_repeated_subobject_split_right H1).
 functional inversion 1; subst.
 assert (
   path (hier) through ( x0 :: x2) x0 Class.Inheritance.Repeated
 ).
  generalize (path_last H7).
  rewrite last_app_left; try abstract congruence.
  intro.
  destruct (last_correct H10).
  eleft with (lt :=  x).
   reflexivity.
   simpl; assumption.
   assumption.
 inversion 1; subst.
assert (is_valid_repeated_subobject (hier) ((x4 ++ p0 :: nil) ++ x1 :: x3) = true).
 generalize (path_path1  H20 ).
 inversion 1; subst; trivial.
 inversion  H15 ; subst; trivial.
generalize  H12.
rewrite app_ass at 1.
intro.
generalize (is_valid_repeated_subobject_split_right H13 ).
 functional inversion 1; subst.
 assert (
   path (hier) through0 ( x1 :: x3) x1 Class.Inheritance.Repeated
 ).
  generalize (path_last H20).
  rewrite last_app_left; try abstract congruence.
  intro.
  destruct (last_correct H16).
  eleft with (lt :=  x).
   reflexivity.
   assumption.
   assumption.
  clear H17 H28 .
  replace cl0 with cl1 in * by abstract congruence.
  clear H7 H8 H0 H1 H3 H9 X H18 H19 H20 H21 H13 cl0 H25 H15 X0 H12.
  assert (In x0 (
    map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b) (filter (fun hb : _ * ident =>
          match hb with
            | (Class.Inheritance.Shared, _) => false
            | _ => true
          end
        ) (Class.super cl1)) 
  )).
   eapply in_map_iff.
   exists (Class.Inheritance.Repeated, x0).
   split.
    trivial.
   eapply filter_In.
   auto.
  assert (In x1 (
    map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b) (filter (fun hb : _ * ident =>
          match hb with
            | (Class.Inheritance.Shared, _) => false
            | _ => true
          end
        ) (Class.super cl1)) 
  )).
   eapply in_map_iff.
   exists (Class.Inheritance.Repeated, x1).
   split.
    trivial.
   eapply filter_In.
   auto.
  revert x0 x1 H2 H0 H1 _x _x0 x2 x3 ato1 pto1 ato2 pto2 f f0 H through through0 H10 H11 H16.
  cut (
    forall x0 x1 m0 m1 m2,
       (map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b)
        (filter
           (fun hb : Class.Inheritance.t * ident =>
            let (y, _) := hb in
            match y with
            | Class.Inheritance.Repeated => true
            | Class.Inheritance.Shared => false
            end) (Class.super cl1))) = m0 ++ x0 :: m1 ++ x1 :: m2 ->
       In (Class.Inheritance.Repeated, x0) (Class.super cl1) ->
   In (Class.Inheritance.Repeated, x1) (Class.super cl1) ->
   forall (x2 x3 : list positive) (ato1 pto1 ato2 pto2 : ident)
     (f
      f0 : option
             (FieldSignature.t A * array_path A * Z *
              (Class.Inheritance.t * list ident))),
   valid_relative_pointer_alt (hier) afrom zfrom ato2 pto2
     (relative_pointer_alt_intro i0 (t0, (x4 ++ p0 :: nil) ++ x0 :: x2) f) ->
   forall through through0 : ident,
   path (A:=A) (hier) through (x0 :: x2) x0
     Class.Inheritance.Repeated ->
   valid_relative_pointer_alt (hier) afrom zfrom ato1 pto1
     (relative_pointer_alt_intro i0 (t0, (x4 ++ p0 :: nil) ++ x1 :: x3) f0) ->
   path (A:=A) (hier) through0 ( x1 :: x3) x1
     Class.Inheritance.Repeated ->
   lifetime afrom zfrom
     (relative_pointer_of_relative_pointer_alt
        (relative_pointer_alt_intro i0 (t0, (x4 ++ p0 :: nil) ++ x1 :: x3) f0))
     (relative_pointer_of_relative_pointer_alt
        (relative_pointer_alt_intro i0 (t0, (x4 ++ p0 :: nil) ++ x0 :: x2) f)) \/
   lifetime afrom zfrom
     (relative_pointer_of_relative_pointer_alt
        (relative_pointer_alt_intro i0 (t0, (x4 ++ p0 :: nil) ++ x0 :: x2) f))
     (relative_pointer_of_relative_pointer_alt
        (relative_pointer_alt_intro i0 (t0, (x4 ++ p0 :: nil) ++ x1 :: x3) f0))
  ).
   intros.
   generalize (list_lt_total peq H0 H1).
   unfold list_lt.
   destruct 1; try contradiction.
   assert (forall a b : Prop, a \/ b -> b \/ a) by tauto.
   destruct s; invall; subst; eauto.
  intros.
  right.
  eright.
  eapply lifetime_order_horizontal_non_virtual_base.
  econstructor.
  eleft.
  2 : eapply Zle_refl.
  abstract omega.
  2 : eassumption.
  assumption.
  eexact H4.
  eassumption.
  eassumption.
  reflexivity.
  reflexivity.
  eright.
  eapply inclusion_relative_pointer_alt.
  eassumption.
  eleft.
  eapply inclusion_order_non_virtual.
  econstructor.
  econstructor.
  2 : eapply Zle_refl.
  abstract omega.
  assumption.
  assumption.
  eapply path_concat.
  eassumption.
  eleft with (lf := x0 :: nil) (lt := p0 :: nil).
  reflexivity.
  simpl. reflexivity.
  simpl.
  rewrite H14.
  destruct ( In_dec super_eq_dec (Class.Inheritance.Repeated, x0) (Class.super cl1)
  ); try contradiction.
  generalize (path_defined_from H3).
  destruct ( (hier) ! x0 ); abstract congruence.
  simpl.
  rewrite last_complete.
  destruct (peq p0 p0); abstract congruence.
  eassumption.
  simpl.
  rewrite last_complete.
  destruct (peq x0 x0); try abstract congruence.
  rewrite app_ass.
  rewrite app_ass.
  rewrite app_ass.
  reflexivity.
  eright.
  eapply inclusion_relative_pointer_alt.
  eassumption.
  eleft.
  eapply inclusion_order_non_virtual.
  econstructor.
  econstructor.
  2 : eapply Zle_refl.
  abstract omega.
  assumption.
  assumption.
  eapply path_concat.
  eassumption.
  eleft with (lf := x1 :: nil) (lt := p0 :: nil).
  reflexivity.
  simpl. reflexivity.
  simpl.
  rewrite H14.
  destruct ( In_dec super_eq_dec (Class.Inheritance.Repeated, x1) (Class.super cl1)
  ); try contradiction.
  generalize (path_defined_from H8).
  destruct ( (hier) ! x1 ); abstract congruence.
  simpl.
  rewrite last_complete.
  destruct (peq p0 p0); abstract congruence.
  eassumption.
  simpl.
  rewrite last_complete.
  destruct (peq x1 x1); try abstract congruence.
  rewrite app_ass.
  rewrite app_ass.
  rewrite app_ass.
  reflexivity.

Qed.

End Lifetime_total.

End SubobjectOrdering.
