Require Import Relations.
Require Import Coqlib.
Require Import LibPos.
Require Import Maps.
Require Import LibLists.
Require Import Cppsem.
Require Import Cplusconcepts.
Require Import Events.
Require Import SubobjectOrdering.
Require Import Invariant.
Require Import CplusWf.
Load Param.
Open Scope Z_scope.

(** Relations between construction states *)

  Lemma constructed_base_child_of_trans : forall a b, constructed_base_child_of a b -> forall c, constructed_base_child_of b c -> constructed_base_child_of a c.
  Proof.
    destruct 1; destruct 1; split; intros; subst; eauto.    
    generalize (constructed_base_child_of_started_constructing0 (refl_equal _)).
    intro.
    destruct b.
     destruct c; simpl in *; try omegaContradiction; eauto;
    rewrite constructed_base_child_of_constructed; simpl; omega.
    rewrite constructed_base_child_of_none.
    assumption.
    trivial.
   generalize (constructed_base_child_of_constructed0 H H0).
   intro; subst; simpl in *.
   apply constructed_base_child_of_constructed; omega.
  generalize (constructed_base_child_of_destructing_bases0 (refl_equal _)).
  destruct b; simpl in *; try (intros; omegaContradiction).
  destruct c; intros; try omegaContradiction; eauto.
  rewrite constructed_base_child_of_constructed; simpl; try omega.
  rewrite constructed_base_child_of_constructed; simpl; try omega.
  rewrite constructed_base_child_of_destructed.
   simpl; omega.
   trivial.
Qed.  
  


Lemma constructed_sibling_before_trans : forall cs1 cs2, constructed_sibling_before cs1 cs2 -> forall cs3, constructed_sibling_before cs2 cs3 -> constructed_sibling_before cs1 cs3.
Proof.
inversion 1.
inversion 1.
split.
 intros. 
 apply constructed_sibling_before_none0.
 rewrite (constructed_sibling_before_none H1).
 simpl; omega.
intros.
apply constructed_sibling_before_destructed0.
rewrite (constructed_sibling_before_destructed H1).
simpl; omega.
Qed.

Lemma constructed_sibling_before_constructed : forall cs cs', constructed_sibling_before cs cs' -> (None << cs') -> (cs' << Some Destructed) -> cs = Some Constructed.
Proof.
  inversion 1.
  intros.
  destruct (cs_le_dec_2 cs (Some Constructed)).
  destruct (cs_le_dec_2 (Some Constructed) cs).
   eauto using cs_le_antisym.
  rewrite (constructed_sibling_before_none z0) in H0.
  simpl in H0; omegaContradiction.
  rewrite (constructed_sibling_before_destructed z) in H1.
  simpl in H1; omegaContradiction.
Qed.

Lemma constructed_sibling_before_base_child : forall cs1 cs2, constructed_sibling_before cs1 cs2 -> forall cs3, constructed_base_child_of cs3 cs2 -> constructed_sibling_before cs1 cs3.
Proof.
  inversion 1; subst.
  inversion 1; subst.
  split; eauto.
Qed.


Lemma constructed_sibling_before_base_child_left : forall cs1 cs2, constructed_sibling_before cs1 cs2 -> 
  forall cs1', constructed_base_child_of cs1' cs1 ->
      constructed_sibling_before cs1' cs2.
Proof.
  split; intros.
   destruct (
     cs_le_dec_2 (Some Constructed) cs1
   ).
    2 : eauto using constructed_sibling_before_none.
   apply False_rect.
   destruct (
     cs_le_dec_2 cs1 (Some StartedDestructing)
   ).        
    assert (Some BasesConstructed =< cs1) by (simpl in *; omega).
    generalize (constructed_base_child_of_constructed H0 H2 z0). 
    intro; subst; simpl in *; omega.
   destruct cs1; simpl in *; try omega.
   destruct c; try omega.
    generalize (constructed_base_child_of_destructing_bases H0 (refl_equal _)).
     simpl; omega.
    generalize (constructed_base_child_of_destructed H0 (refl_equal _)).
     intro; subst; simpl in *; omega.
   destruct (
     cs_le_dec_2 cs1 (Some Constructed) 
   ).
    2 : eauto using constructed_sibling_before_destructed.
   apply False_rect.
   destruct (
     cs_le_dec_2 (Some BasesConstructed) cs1
   ).        
    assert (cs1 =< Some StartedDestructing) by (simpl in *; omega).
    generalize (constructed_base_child_of_constructed H0 z0 H2). 
    intro; subst; simpl in *; omega.
   destruct cs1; simpl in *; try omega.
   destruct c; try omega.
    generalize (constructed_base_child_of_started_constructing H0 (refl_equal _)).
     simpl; omega.
    generalize (constructed_base_child_of_none H0 (refl_equal _)).
     intro; subst; simpl in *; omega.
Qed.

Corollary constructed_sibling_before_base_child_strong : forall cs1 cs2, constructed_sibling_before cs1 cs2 -> 
  forall cs1', constructed_base_child_of cs1' cs1 ->
    forall cs2', constructed_base_child_of cs2' cs2 ->
      constructed_sibling_before cs1' cs2'.
Proof.
 intros; eauto using constructed_sibling_before_base_child, constructed_sibling_before_base_child_left.
Qed.


Lemma constructed_sibling_before_field_child_strong : forall cs1 cs2, constructed_sibling_before cs1 cs2 -> 
  forall cs1', constructed_field_child_of cs1' cs1 ->
    forall cs2', constructed_field_child_of cs2' cs2 ->
      constructed_sibling_before cs1' cs2'.
Proof.
  inversion 1; subst.
  inversion 1; subst.
  inversion 1; subst.
  split; intros.
  apply constructed_field_child_of_none0.
  destruct cs1; simpl in *; try omega.
  destruct c; simpl in *; try omega.
  generalize (constructed_sibling_before_none (Z_lt_dec_reflexion 1 3)).
  intros; subst; simpl; omega.
  generalize (constructed_sibling_before_none (Z_lt_dec_reflexion 2 3)).
  intros; subst; simpl; omega.
  generalize (constructed_field_child_of_constructed (refl_equal _)).
  intros; subst; simpl in *; omegaContradiction.
  generalize (constructed_field_child_of_started_destructing (refl_equal _)).
  destruct 1.
   subst; simpl in *; omegaContradiction.
  destruct H3; subst; simpl in *; omegaContradiction.
  generalize (constructed_field_child_of_destructed (Z_le_dec_reflexion 5 5)).
  intros; subst; simpl in *; omegaContradiction.
  generalize (constructed_field_child_of_destructed (Z_le_dec_reflexion 5 6)).
  intros; subst; simpl in *; omegaContradiction.
  generalize (constructed_sibling_before_none (Z_lt_dec_reflexion 0 3)).
  intros; subst; simpl; omega.
  apply constructed_field_child_of_destructed0.
destruct cs1; simpl in *; try omega.
destruct c; simpl in *; try omega.
 generalize (constructed_field_child_of_none (Z_le_dec_reflexion 1 1)).
  intro; subst; simpl in *; omegaContradiction.
 destruct (constructed_field_child_of_bases_constructed (refl_equal _)).
  subst; simpl in *; omegaContradiction.
 destruct H3;   subst; simpl in *; omegaContradiction.
generalize (constructed_field_child_of_constructed (refl_equal _)).
intro; subst; simpl in *; omegaContradiction.
generalize (constructed_sibling_before_destructed (Z_lt_dec_reflexion 3 4)).
intros; subst; simpl in *; omega.
generalize (constructed_sibling_before_destructed (Z_lt_dec_reflexion 3 5)).
intros; subst; simpl in *; omega.
generalize (constructed_sibling_before_destructed (Z_lt_dec_reflexion 3 6)).
intros; subst; simpl in *; omega.
generalize (constructed_field_child_of_none (Z_le_dec_reflexion 0 1)).
intros; subst; simpl in *; omegaContradiction.
Qed.


Lemma constructed_sibling_before_field_array_cell_strong : forall cs1 cs2, constructed_sibling_before cs1 cs2 -> 
  forall cs1', constructed_field_array_cell cs1 cs1' ->
    forall cs2', constructed_field_array_cell cs2 cs2' ->
      constructed_sibling_before cs1' cs2'.
Proof.
  inversion 1.
  inversion 1.
  inversion 1.
  split.
  intros.
  apply constructed_field_array_cell_none0.
  apply constructed_sibling_before_none.
  destruct cs1; simpl; try omega.
  destruct c; simpl; try omega; apply False_rect; eauto.
  generalize (constructed_field_array_cell_constructed (refl_equal _)).
   intro; subst; simpl in *; omegaContradiction.
  generalize (constructed_field_array_cell_started_destructing (refl_equal _)).
  simpl in *; omega.
  generalize (constructed_field_array_cell_destructed (refl_equal _)).
  intro; subst; simpl in *; omega.
 intros.
 apply constructed_field_array_cell_destructed0.
 apply constructed_sibling_before_destructed.
 destruct cs1; simpl; try omega.
 destruct c; simpl; try omega; apply False_rect; eauto.
 generalize (constructed_field_array_cell_started_constructing (refl_equal _)).
 intros; simpl in *; omega.
 generalize (constructed_field_array_cell_constructed (refl_equal _)).
 intro; subst; simpl in *; omega.
 generalize (constructed_field_array_cell_none (refl_equal _)).
 intro; subst; simpl in *; omega.
Qed.

Lemma constructed_base_before_field_cell : forall c cb,
  constructed_base_child_of cb c ->
  forall cf,
    constructed_field_child_of cf c ->
    forall c',
      constructed_field_array_cell cf c' ->
      constructed_sibling_before cb c'.
Proof.
  inversion 1.
  inversion 1.
  inversion 1.
  destruct (cs_le_dec_2 (Some BasesConstructed) c).
  destruct (cs_le_dec_2 c (Some StartedDestructing)).
  generalize (constructed_base_child_of_constructed z z0).
  intro; subst.
  split; simpl; intro; omegaContradiction.
  destruct (cs_le_dec_2 (Some DestructingBases) c); try (simpl in *; omegaContradiction).
  generalize (constructed_field_child_of_destructed z1).
  intro; subst.
  generalize (constructed_field_array_cell_destructed (refl_equal _)).
  intro; subst.
  split; auto.
  destruct c; simpl in *; intros; try omegaContradiction.
  destruct c; try omegaContradiction.
  generalize (constructed_base_child_of_destructing_bases (refl_equal _)).
  simpl; intro; omegaContradiction.
  generalize (constructed_base_child_of_destructed (refl_equal _)).
  intro; subst; simpl in *; omegaContradiction.
  destruct (cs_le_dec_2 c (Some StartedConstructing)  ); try (simpl in *; omegaContradiction).
  generalize (constructed_field_child_of_none z0).
  intro; subst.
  generalize (constructed_field_array_cell_none (refl_equal _)).
  intro; subst.
  split; auto.
  intros.
  destruct c; simpl in *; intros; try omegaContradiction.
  destruct c; try omegaContradiction.
  generalize (constructed_base_child_of_started_constructing (refl_equal _)).
  simpl in *; intro; omegaContradiction.
 generalize (constructed_base_child_of_none (refl_equal _)).
 intros; subst; simpl in *; omegaContradiction.
Qed.


Section ConstrOrder.


Variable A : ATOM.t.
Variable nativeop : Type.
Variable sem : semparam A nativeop.
Let evtr := evtr sem.
Let trace := trace evtr.

Variable prog : Program.t A nativeop.

Notation hier := (Program.hierarchy prog) (only parsing).

Section State.

Variable s : State.t A nativeop.

Hypothesis Hinv : invariant prog s.

  Lemma construction_states_nonempty_non_virtual_bases : forall gl,
    gl = Globals.heap (State.global s) ->
    forall obj ar i h p hp,
      valid_pointer hier gl (Value.subobject obj ar i h p hp) ->
      forall cn, last p = Some cn ->
        forall l cn', is_valid_repeated_subobject (Program.hierarchy prog) (cn :: l ++ cn' :: nil) = true ->
          forall cs, cs = (State.construction_states s) ->
            constructed_base_child_of (assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p ++ l ++ cn' :: nil))) cs) (assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) cs).
  Proof.
   intros until 1; subst.
   inversion 1; subst.
   clear hp hp1 H.
   inversion H6; subst.
   clear H6.
   intros until 1.
   intro l.
   rewrite (path_last H3) in H4.
   injection H4; intros; subst.
   clear H4.
   revert cn p H3 cn' H6.
   induction l.
    simpl.
    intros until 1.
    case_eq (hier ! cn); try (intros; discriminate).
    intros until 1.
    intro.
    sdestruct (
      In_dec super_eq_dec (Class.Inheritance.Repeated, cn') (Class.super t)
    ); try (intros; discriminate).
    case_eq (hier ! cn') ; try (intros; discriminate).
    intros.
    assert (is_some (last p)).
     rewrite (path_last H3).
     exact I.
    eapply construction_states_direct_non_virtual_bases with (hp := H7).
    eassumption.
    econstructor.
     eassumption.
     trivial.
     econstructor.
     eassumption.
     assumption.
     assumption.
     eassumption.
    eapply path_last.
    eassumption.
    eassumption.
    assumption.
   intros.
   replace (cn :: (a :: l) ++ cn' :: nil) with (cn :: a :: l ++ cn' :: nil) in H6 by reflexivity.
   functional inversion H6; subst.
   clear H6.
   assert (path hier a (cn :: a :: nil) cn Class.Inheritance.Repeated).
    eleft with (lt := cn :: nil).
    reflexivity.
    reflexivity.
    simpl.
    rewrite H9.
    rewrite H12.
    functional inversion X.
     rewrite H7; trivial.
    rewrite H7; trivial.
   generalize (path_concat H3 H4).
   intro.
   simpl in H5.
   rewrite (path_last H3) in H5.
   destruct (peq cn cn); try abstract congruence.
   generalize (H5 _ _ (refl_equal _)).
   clear e H5.
   intro.    
   replace (a :: l ++ cn' :: nil) with ((a :: l) ++ cn' :: nil) in X by reflexivity.
   generalize (IHl _ _ H5 _ X).
   rewrite app_ass.
   intro.
   simpl in H6.
   eapply constructed_base_child_of_trans.
   eassumption.
   assert (is_some (last p)).
   rewrite (path_last H3).
   exact I.
   eapply construction_states_direct_non_virtual_bases with (hp := H7).
   eassumption.
   econstructor.
   eassumption.
   trivial.
   econstructor.
   eassumption.
   assumption.
   assumption.
   eassumption.
   eapply path_last.
   eassumption.
   eassumption.
   assumption.
Qed.

Corollary breadth_virtual_nonempty_non_virtual_bases : forall gl,
  gl = Globals.heap (State.global s) ->
  forall obj ar i cn l cn' hp,
    valid_pointer hier gl (Value.subobject obj ar i Class.Inheritance.Repeated (cn :: l ++ cn' :: nil) hp) ->
    forall cs,
      cs = (State.construction_states s) -> 
      forall b, is_virtual_base_of (Program.hierarchy prog) b cn ->
        constructed_sibling_before (assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b :: nil))) cs) (assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Repeated, cn :: l ++ cn' :: nil))) cs).
Proof.
 intros until 1; subst.
 inversion 1; subst.
 intros until 1; subst.
 inversion H6; subst.
 inversion H4; subst.
 generalize (last_complete lt to).
 rewrite <- H7.
 intro.
 change (cn :: l ++ cn' :: nil) with ((cn :: l) ++ cn' :: nil) in H9.
 revert H9.
 rewrite last_complete.
 injection 1; intro; subst.
 injection H5; intros until 2; subst.
 case_eq (l ++ to :: nil).
  intro.
  destruct l; simpl in H10; discriminate.
 intros until 1.
 rewrite H10 in H8.
 functional inversion H8; subst.
 intros until 1.
 destruct (maximize_array_path H0).
 destruct H12.
 destruct H13.
 assert (0 <= i < x) by abstract omega.
 generalize (breadth_virtual_non_virtual_bases Hinv H2 H12 H14 H16 H11 H15 _x).
 intro.
 functional inversion X; subst.
  assumption.
  assert (valid_pointer hier (Globals.heap (State.global s)) (Value.subobject (obj) ar i Class.Inheritance.Repeated (through :: i0 :: nil) I)).
   econstructor.
   eassumption.
   trivial.
   econstructor.
    eassumption.
    assumption.
    abstract omega.
   eleft with (lt := through :: nil).
   reflexivity.
   simpl. reflexivity.
   change (through :: i0 :: nil) with ((through :: nil) ++ i0 :: nil).
   change (through :: i0 :: id2 :: l3) with ((through :: nil) ++ i0 :: id2 :: l3) in H8.
   eauto using is_valid_repeated_subobject_split_left.
  destruct l; simpl in H10; try discriminate.
  injection H10; intros; subst.
  rewrite <- H20 in X.
  generalize (construction_states_nonempty_non_virtual_bases (refl_equal _) H19 (refl_equal _) X (refl_equal _)).
  simpl.
  intros.
  rewrite <- H20.
  eauto using constructed_sibling_before_base_child.
Qed.

  Corollary construction_states_non_virtual_bases : forall gl,
    gl = Globals.heap (State.global s) ->
    forall obj ar i h p hp,
      valid_pointer hier gl (Value.subobject obj ar i h p hp) ->
      forall cn, last p = Some cn ->
        forall l, is_valid_repeated_subobject (Program.hierarchy prog) (cn :: l) = true ->
          forall cs, cs = (State.construction_states s) ->
            forall c1, c1 = (assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p ++ l))) cs) ->
              forall c2, c2 =  (assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) cs) ->
                (c1 = c2 /\ l = nil) \/ constructed_base_child_of c1 c2
.
Proof.
  intros; subst.
  generalize (rev_involutive l).
   destruct (rev l).
    simpl; intro; subst.
    rewrite <- app_nil_end; auto.
   simpl.
   generalize (rev l0).
   clear l0.
   intros; subst; eauto using  construction_states_nonempty_non_virtual_bases.
Qed.       

Record construction_includes (c1 c2 : option construction_state) : Prop := construction_includes_intro {
  construction_includes_none : c1 = None -> c2 = None;
  construction_includes_constructed : c1 = Some Constructed -> c2 = Some Constructed;
  construction_includes_destructed : c1 = Some Destructed -> c2 = Some Destructed
}.

Lemma construction_includes_refl : forall c, construction_includes c c.
Proof.
  split; tauto.
Qed.

Lemma construction_includes_trans : forall c1 c2, construction_includes c1 c2 -> forall c3, construction_includes c2 c3 -> construction_includes c1 c3.
Proof.
  inversion 1; inversion 1; split; eauto.
Qed.

Lemma construction_includes_constructed_base_child_of : forall c1 c2, constructed_base_child_of c1 c2 -> construction_includes c2 c1.
Proof.
  inversion 1; split; intros; subst; simpl in *.
   eauto.
  apply constructed_base_child_of_constructed; omega.
  eauto.
Qed.

Lemma construction_includes_constructed_field_child_of : forall c1 c2, constructed_field_child_of c1 c2 -> construction_includes c2 c1.
Proof.
  inversion 1; split; intros; subst; simpl in *.
  apply constructed_field_child_of_none; omega.
  eauto.
  apply constructed_field_child_of_destructed; omega.
Qed.

Lemma construction_includes_constructed_field_array_cell : forall c1 c2, constructed_field_array_cell c1 c2 -> construction_includes c1 c2.
Proof.
  inversion 1; split; assumption.
Qed.

Lemma construction_includes_non_virtual_bases : 
  forall obj ar i h p hp,
    valid_pointer hier ( Globals.heap (State.global s) ) (Value.subobject obj ar i h p hp) ->
    forall pto, last p = Some pto ->
      forall p1 pto', path (Program.hierarchy prog) pto' p1 pto Class.Inheritance.Repeated ->
        forall h' p', (h', p') = concat (h, p) (Class.Inheritance.Repeated, p1) ->
          construction_includes (assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states s)) (assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) (State.construction_states s)).
Proof.
  Opaque is_valid_repeated_subobject.
  inversion 3; subst; simpl in *.
  rewrite H0.
  destruct (peq pto pto); try congruence.
  destruct lf.
   rewrite <- app_nil_end.
   injection 1; intros; subst; eauto using construction_includes_refl.
  injection 1; intros; subst.
  eapply construction_includes_constructed_base_child_of.
  destruct lt; try discriminate.
  injection H3; intros; subst.
  rewrite H5.
  eapply construction_states_nonempty_non_virtual_bases.
  reflexivity.
  eassumption.
  eassumption.
  congruence.
  trivial.
Qed.

(** if p1 is a direct subobject of p2, then the lifetime of p2 is included in the lifetime of p1 *)

Lemma inclusion_order_construction_order : forall obj o,
    (Globals.heap (State.global s)) ! obj = Some o ->
    forall o1 o2,
    inclusion_order hier (Object.class o) (Object.arraysize o) o1 o2 ->
    construction_includes (assoc (@pointer_eq_dec _) (obj, o2) (State.construction_states s)) (assoc (@pointer_eq_dec _) (obj, o1) (State.construction_states s)).
Proof.
  inversion 2; subst.
   (* append inheritance path *)
   inversion H1; subst.
   generalize (path_last H7).
   intros.
   assert (is_some (last p)).
    rewrite H8; exact I.
   eapply construction_includes_non_virtual_bases with (hp := H9); eauto.
   econstructor; eauto.

 (* virtual base *)
   destruct (maximize_array_path H1).
   invall.
   assert (0 <= i < x) by omega.
   eauto using construction_states_virtual_bases,  construction_includes_constructed_base_child_of.

(* field *)
intros.
inversion H1; subst.
generalize (path_last H9).
intros.
assert (is_some (last p)).
 rewrite H10; exact I.
eapply construction_includes_trans.
eapply construction_includes_constructed_field_child_of.
eapply construction_states_fields  with (hp := H11); eauto.
econstructor; eauto.
eapply construction_includes_constructed_field_array_cell.
eapply construction_states_structure_fields with (hp := H11); eauto.
econstructor; eauto.
Qed.

(** if p1 included in p2, then the lifetime of p2 is included in the lifetime of p1 *)

Corollary inclusion_construction_order :
  forall obj o,
    (Globals.heap (State.global s)) ! obj = Some o ->
    forall o1 o2,
      inclusion hier (Object.class o) (Object.arraysize o) o1 o2 ->
      construction_includes (assoc (@pointer_eq_dec _) (obj, o2) (State.construction_states s)) (assoc (@pointer_eq_dec _) (obj, o1) (State.construction_states s)).
Proof.
  induction 2; eauto using inclusion_order_construction_order, construction_includes_trans.
Qed.


(** if p1 occurs before p2, then the lifetime of p2 is included in the lifetime of p1 *)

Lemma lifetime_order_horizontal_construction_order :
  forall obj o,
    (Globals.heap (State.global s)) ! obj = Some o ->
  forall o1 o2,
    lifetime_order_horizontal hier (Object.class o) (Object.arraysize o) o1 o2 ->
    constructed_sibling_before (assoc (@pointer_eq_dec _) (obj, o1) (State.construction_states s)) (assoc (@pointer_eq_dec _) (obj, o2) (State.construction_states s))
        .
Proof.
  inversion 2; subst.

 (* array path *)
 intros.
 destruct (maximize_array_path H1).
 invall.
 eapply breadth_arrays.
 eassumption.
 eassumption.
 eassumption.
 eassumption.
 eassumption.
 eassumption.
 abstract omega.

 (* fields *)
 inversion H1; subst.
 generalize (path_last H11).
 intros.
 assert (is_some (last p)).
  rewrite H12.
  exact I.
 eapply constructed_sibling_before_field_array_cell_strong.
 eapply breadth_fields with (hp := H13); eauto.
 econstructor; eauto.
 eapply construction_states_structure_fields with (hp := H13); eauto.
 econstructor; eauto.
 rewrite H3; eauto using in_or_app.
 eapply construction_states_structure_fields with (hp := H13); eauto.
 econstructor; eauto.
 rewrite H3; eauto 8 using in_or_app.

(* virtual bases *)
generalize (maximize_array_path H1).
intros; invall; subst.
assert (0 <= i < x) by abstract omega.
eauto using breadth_virtual_bases.

(* non-virtual bases *)
inversion H1; subst.
generalize (path_last H7).
intro.
assert (is_some (last p)).
 rewrite H8.
 exact I.
eapply breadth_non_virtual_bases with (hp := H9); eauto.
econstructor; eauto.

(* vbase nvbase *)
generalize (maximize_array_path H1).
intros; invall; subst.
assert (0 <= i < x) by abstract omega.
eauto using breadth_virtual_non_virtual_bases.

(* nvb field *)
 inversion H1; subst.
 generalize (path_last H10).
 intros.
 assert (is_some (last p)).
  rewrite H11.
  exact I.
  assert (
  valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s))
     (Value.subobject obj apath i h p H12)
 ).
   econstructor; eauto.
   generalize (construction_states_fields Hinv H13 H11 H2 H4).
   intro.
   generalize (construction_states_structure_fields Hinv H13 H11 H2 H4 H5 H6).
   intro.
   generalize  (construction_states_direct_non_virtual_bases Hinv H13 H11 H2 H3).
   intro.
   eauto using constructed_base_before_field_cell.

(* virtual vs field *)
 assert (last (to :: nil) = Some to) by reflexivity.
 assert (is_some (last (to :: nil))) by exact I.
 assert (
  valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s))
     (Value.subobject obj ar i Class.Inheritance.Repeated (to :: nil) H9)
 ).
  econstructor; eauto.
  econstructor.
  eassumption.
  omega.
  omega.
  eleft with (lt := nil).
  reflexivity.
  reflexivity.
  Transparent is_valid_repeated_subobject.
  simpl.
  rewrite H4.
  trivial.
 generalize (maximize_array_path H1).
 intros [? [HV1 [HV2 HV3]]].
 assert (0 <= i < x) by abstract omega.
 generalize (construction_states_fields Hinv H10 H8 H4 H5).
 intro.
 generalize (construction_states_structure_fields Hinv H10 H8 H4 H5 H6 H7).
 intro.
 generalize (construction_states_virtual_bases Hinv H HV1 HV3 H11 H3).
 intro.
 eauto using constructed_base_before_field_cell.
Qed.

(** * POPL 2012 submission: Lemma 11 *)

(** if p1 R p2 (p1 <= p2), then the lifetime of p2 is included in the lifetime of p1. *)

Theorem lifetime_construction_order : forall obj o,
  (Globals.heap (State.global s)) ! obj = Some o ->
  forall o1 o2,
    lifetime hier (Object.class o) (Object.arraysize o) o1 o2 ->
    assoc (@pointer_eq_dec _) (obj, o2) (State.construction_states s) = Some Constructed ->
    assoc (@pointer_eq_dec _) (obj, o1) (State.construction_states s) = Some Constructed
    .
Proof.
 inversion 2; subst.
 destruct (inclusion_construction_order H H1). 
 eauto.
 intro.
 destruct (inclusion_construction_order H H2). 
 destruct (inclusion_construction_order H H3).  
 apply construction_includes_constructed0.
 eapply constructed_sibling_before_constructed.
 eapply lifetime_order_horizontal_construction_order.
 eassumption.
 eassumption.
 revert construction_includes_none1.
 sdestruct (
   (assoc (pointer_eq_dec (A:=A)) (obj, o3) (State.construction_states s))
 ); simpl; intros.
 destruct c; omega.
 generalize (construction_includes_none1 (refl_equal _)).
 unfold_ident_in_all; intro; apply False_rect; congruence.
 revert construction_includes_destructed1.
 sdestruct (
   (assoc (pointer_eq_dec (A:=A)) (obj, o3) (State.construction_states s))
 ); simpl; intros; try omega.
 destruct c; try omega.
 generalize (construction_includes_destructed1 (refl_equal _)).
 unfold_ident_in_all; intro; apply False_rect; congruence.
Qed.

Hypothesis hierarchy_wf : Well_formed_hierarchy.prop hier.


(** * POPL 2012 submission: Theorem 12 *)

(** The lifetime of an object is included in the lifetime of all of its subobjects. *)

Corollary subobject_construction_order : forall obj o,
  (Globals.heap (State.global s)) ! obj = Some o ->
  forall o1 o2,
    is_subobject_of hier (Object.class o) (Object.arraysize o) o1 o2 ->
    assoc (@pointer_eq_dec _) (obj, o2) (State.construction_states s) = Some Constructed ->
    assoc (@pointer_eq_dec _) (obj, o1) (State.construction_states s) = Some Constructed
    .
Proof.
  eauto using lifetime_construction_order, lifetime_subobject.
Qed.     

Theorem bases_constructed : forall obj ar i h p hp,
  valid_pointer hier (Globals.heap (State.global s)) (Value.subobject obj ar i h p hp) ->
  (Some BasesConstructed =< (assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states s))) ->
  ((assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p)))  (State.construction_states s)) =< Some StartedDestructing) ->  
  forall cn, last p = Some cn ->
    forall h1 p1 to1,
      path hier to1 p1 cn h1 ->
      (h1, p1) <> (Class.Inheritance.Repeated, cn :: nil) ->
      forall h' p', (h', p') = concat (h, p) (h1, p1) ->
        assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) (State.construction_states s) = Some Constructed.
Proof.
  inversion 1; subst.
  inversion H6; subst.
  rewrite (path_last H4).
  injection 3; intro; subst.
  intros until 1.
  generalize (path_path1 H9).
  inversion 1; intros; subst.
  (* non-virtual base *)
  destruct (construction_states_non_virtual_bases 
(* Hinv *) (refl_equal _) H (path_last H4) H13 (refl_equal _) (refl_equal _) (refl_equal _)).
   invall; congruence.
  injection H17; intros; subst.
  rewrite (path_last H4).
  destruct (peq cn cn); try congruence.
  eauto using constructed_base_child_of_constructed.
 (* virtual base *)
  generalize (path_is_virtual_base_of H4 H11).
  intro.
  injection H16; intros; subst.
  inversion H12; subst.
  assert (is_some (last (base :: nil))).
   exact I.
  refine (_ (construction_states_non_virtual_bases (* Hinv *) (refl_equal _) (hp := H14) _ (refl_equal _) H18 (refl_equal _) (refl_equal _) (refl_equal _))).
  Focus 2.
   econstructor.
   eassumption.
   econstructor.
   eassumption.
   eassumption.
   assumption.
   eright.
   eassumption.
   eleft with (lt := nil).
    reflexivity.
    reflexivity.
    simpl.
    generalize (path_defined_from H12).
    destruct ((Program.hierarchy prog) ! base); congruence.
   intro.
  destruct (maximize_array_path H0).
  invall.
  generalize (path_path1 H4). 
  inversion 1; subst.
   (* virtual vs non-virtual *)
   destruct lt0.
    (* full object *)
    injection H24; intros; subst.
    assert (
      constructed_base_child_of 
      (assoc (pointer_eq_dec (A:=A))
        (obj, (ar, i, (Class.Inheritance.Shared, (base :: nil))))
        (State.construction_states s))
      (assoc (pointer_eq_dec (A:=A))
        (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
        (State.construction_states s))
    ).
     eapply construction_states_virtual_bases.
     eassumption.
     eassumption.
     eassumption.
     assumption.
     omega.
     assumption.
    destruct x.
     invall; subst.
     eapply constructed_base_child_of_constructed.
      eassumption.
      assumption.
      assumption.
     eapply constructed_base_child_of_constructed.
     eapply constructed_base_child_of_trans.
      eassumption.
     eassumption.
     assumption.
     assumption.
   (* nonempty non-virtual *)
   injection H24; intros; subst.
   assert (is_some (last (i0 :: lt0 ++ cn :: nil))).
    rewrite (path_last H4).
    exact I.
   assert (
     assoc (pointer_eq_dec (A:=A))
     (obj, (ar, i, (Class.Inheritance.Shared, base :: nil)))
     (State.construction_states s) = Some Constructed
   ).
   eapply constructed_sibling_before_constructed.
   eapply breadth_virtual_nonempty_non_virtual_bases with (hp := H23).
   reflexivity.
   econstructor.
   eassumption.
   econstructor.
   eassumption.
   assumption.
   omega.
   eassumption.
   reflexivity.
   assumption.
   simpl in *; omega.
   simpl in *; omega.
  destruct x.
   invall; congruence.
  eapply constructed_base_child_of_constructed.
  eassumption.
  rewrite H26; simpl; omega.
  rewrite H26; simpl; omega.
 (* two different virtual bases *)
 inversion H24; intros; subst.
 refine (_
   (construction_states_non_virtual_bases 
     (* Hinv *) (refl_equal _) (p := _ :: nil) (hp := I) _ (refl_equal _) H27 (refl_equal _) (refl_equal _) (refl_equal _))).
 Focus 2.
 econstructor.
 eassumption.
 econstructor.
 eassumption.
 eassumption.
 omega.
 eright.
 eassumption.
 eleft with (lt := nil).
 reflexivity.
 reflexivity.
 simpl.
 generalize (path_defined_from H24).
 destruct ((Program.hierarchy prog) ! base0); congruence.
 simpl.
 intro.
 case_eq ((Program.hierarchy prog) ! through); try congruence.
 2 : generalize (path_defined_from H4); congruence.
 intros.
 destruct (Well_formed_hierarchy.vborder_list_exists hierarchy_wf H25).
 generalize (path_is_virtual_base_of H24 H11).
 intro.
 destruct (vborder_list_bases_first v (virtual_base_vborder_list H23 H25 v) H28).
 invall; subst.
 assert (0 <= i < x0) by omega.
 generalize (breadth_virtual_bases Hinv H2 H20 H22 H29 H25 v).
 intro.
 destruct (
   cs_le_dec_2
   (Some Constructed)
   (assoc (pointer_eq_dec (A:=A))
     (obj, (ar, i, (Class.Inheritance.Shared, base :: nil)))
     (State.construction_states s)
   )
 ).
  destruct (
   cs_le_dec_2
   (assoc (pointer_eq_dec (A:=A))
     (obj, (ar, i, (Class.Inheritance.Shared, base :: nil)))
     (State.construction_states s)
   )
   (Some Constructed)
  ).
   generalize (cs_le_antisym z0 z).
   intro.
   simpl in x.
   destruct x.
    invall; congruence.
   eapply constructed_base_child_of_constructed.
   eassumption.
   rewrite H31; simpl; omega. 
   rewrite H31; simpl; omega.
  apply False_rect.
  generalize (constructed_sibling_before_destructed H30 z0).
  intro.
  destruct x1.
   unfold_ident_in_all; invall; subst; rewrite H31 in *; simpl in *; omega.
  generalize (constructed_base_child_of_destructed H32 H31).
  intro.
  rewrite H33 in *; simpl in *; omega.
 apply False_rect.
 generalize (constructed_sibling_before_none H30 z).
  intro.
  destruct x1.
   unfold_ident_in_all; invall; subst; rewrite H31 in *; simpl in *; omega.
  generalize (constructed_base_child_of_none H32 H31).
  intro.
  rewrite H33 in *; simpl in *; omega.
Qed.

(** * POPL 2012 submission: Theorem 5 *)

Corollary function_dispatch_constructed : forall obj ar i sh sp ch cp dh dp,
  dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s)) (State.construction_states s) obj ar i sh sp ch cp dh dp -> (* static pointer sh, sp is the dh, dp subobject of the dynamic complete object ch, cp *)
  forall cn,
    last sp = Some cn ->
    forall ccn,
      last cp = Some ccn (* complete object so far (dynamic type) *) ->
      forall ms mh mp,
        method_dispatch (Program.hierarchy prog) ms cn ccn dh dp mh mp -> (* mh, mp is the path from the dynamic type *)
        forall h' p',
        (h', p') = concat (ch, cp) (mh, mp) -> (* THIS pointer adjustment *)
        (Some BasesConstructed =< 
          (assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p'))) (State.construction_states s))) /\
        ((assoc (@pointer_eq_dec _) (obj, (ar, i, (h', p')))  (State.construction_states s)) =< Some StartedDestructing).
Proof.
 inversion 4; subst.
 inversion H7; subst.
 inversion H; subst.
  (** most-derived object *)
  injection H1; intro; subst.
  intros ? ?.
  erewrite (concat_trivial_left).
  2 : eassumption.
  injection 1; intros until 2; subst.
  destruct (path_eq_dec (mh, mp) (Class.Inheritance.Repeated, ccn :: nil)).
   injection e; intros; subst.
   rewrite H23.
   simpl; omega.
  inversion H22.
  refine (_ (bases_constructed (h := Class.Inheritance.Repeated) _ _ _ H1 H15 n _)).
  5 : erewrite concat_trivial_left.
  5 : reflexivity.
  5 : eassumption.
  Focus 2.
   eright with (hp := I).
   eassumption.
   econstructor.
   eassumption.
   eassumption.
   assumption.
   eleft with (lt := nil).
   reflexivity.
   reflexivity.
   simpl.
   generalize (path_defined_from H15).
   destruct ((Program.hierarchy prog) ! ccn); congruence.
  intro.
  unfold_ident_in_all.
  rewrite x.
  simpl; omega.
  unfold_ident_in_all; rewrite H23; simpl; omega.
  unfold_ident_in_all; rewrite H23; simpl; omega.
 (** subobject *)
  generalize (path_last H23).
  rewrite H1.
  injection 1; intro; subst.
 destruct (path_eq_dec (mh, mp) (Class.Inheritance.Repeated, mdto :: nil)).
  injection e; intros until 2; subst.
  intros ? ?.
  erewrite concat_trivial_right.
  injection 1; intros; subst.
  unfold_ident_in_all.
  destruct H25 as [K | K]; rewrite K; simpl; omega.
 eassumption.
 assert (is_some (last cp)).
  rewrite H1.
  exact I.
 intros.
 inversion H22.
 refine (_ (bases_constructed _ _ _ H1 H15 n H29)).
 Focus 2.
  eright with (hp := H28).
  eassumption.
  econstructor.
  eassumption.
  eassumption.
  assumption.
  eassumption.
 unfold_ident.
 intro.
 rewrite x.
 simpl; omega.
 unfold_ident_in_all; destruct H25 as [K | K]; rewrite K; simpl; omega.
 unfold_ident_in_all; destruct H25 as [K | K]; rewrite K; simpl; omega.
Qed.

Corollary dynamic_type_base_constructed : forall obj ar i sh sp ch cp dh dp,
  dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s)) (State.construction_states s) obj ar i sh sp ch cp dh dp -> 
  (Some BasesConstructed =< 
    (assoc (@pointer_eq_dec _) (obj, (ar, i, (sh, sp))) (State.construction_states s))) /\
  ((assoc (@pointer_eq_dec _) (obj, (ar, i, (sh, sp)))  (State.construction_states s)) =< Some StartedDestructing).
Proof.
 inversion 1; subst.
  (** most-derived object *)
  destruct (path_eq_dec (dh, dp) (Class.Inheritance.Repeated, ato :: nil)).
   injection e; intros; subst.
   rewrite H3.
   simpl; omega.   
  destruct H2.
  refine (_ (bases_constructed (h := Class.Inheritance.Repeated) _ _ _ _ _ n _)).
  6 : eassumption.
  6 : erewrite concat_trivial_left.
  6 : reflexivity.
  6 : eassumption.
  Focus 2.
   eright with (hp := I).
   eassumption.
   econstructor.
   eassumption.
   eassumption.
   assumption.
   eleft with (lt := nil).
   reflexivity.
   reflexivity.
   simpl.
   generalize (path_defined_from H4).
   destruct ((Program.hierarchy prog) ! ato); congruence.
  intro.
  unfold_ident_in_all.
  rewrite x.
  simpl; omega.
  unfold_ident_in_all; rewrite H3; simpl; omega.
  unfold_ident_in_all; rewrite H3; simpl; omega.
  reflexivity.  
 (** subobject *)
 destruct (path_eq_dec (dh, dp) (Class.Inheritance.Repeated, mdto :: nil)).
  injection e; intros until 2; subst.
  erewrite concat_trivial_right in H7.
  injection H7; intros; subst.
  unfold_ident_in_all.
  destruct H5 as [K | K]; rewrite K; simpl; omega.
 eassumption.
 destruct H2.
 assert (is_some (last cp)).
  rewrite (path_last H3).
  exact I.
 refine (_ (bases_constructed _ _ _ _ _ n _)).
 5 : eauto using path_last.
 5 : eassumption.
 5 : eassumption.
 Focus 2.
  eright with (hp := H8).
  eassumption.
  econstructor.
  eassumption.
  eassumption.
  assumption.
  eassumption.
 unfold_ident.
 intro.
 rewrite x.
 simpl; omega.
 unfold_ident_in_all; destruct H5 as [K | K]; rewrite K; simpl; omega.
 unfold_ident_in_all; destruct H5 as [K | K]; rewrite K; simpl; omega.
Qed.

                                                             

End State.

Hypothesis hierarchy_wf : Well_formed_hierarchy.prop hier.

(** * POPL 2012 submission: Theorem 9 *)

Corollary subobject_lifetime_total : forall o apath1 ato1 i1 h1 p1 pto1,
  valid_relative_pointer (Program.hierarchy prog) (Object.class o) (Object.arraysize o) apath1 ato1 i1 h1 p1 pto1 ->
  forall apath2 ato2 i2 h2 p2 pto2,
    valid_relative_pointer  (Program.hierarchy prog) (Object.class o) (Object.arraysize o) apath2 ato2 i2 h2 p2 pto2 ->
    (forall s, invariant prog s -> forall obj, (Globals.heap (State.global s)) ! obj = Some o -> 
      assoc (@pointer_eq_dec _) (obj, (apath1, i1, (h1, p1))) (State.construction_states s) = Some Constructed ->
      assoc (@pointer_eq_dec _) (obj, (apath2, i2, (h2, p2))) (State.construction_states s) = Some Constructed) \/
    (forall s, invariant prog s -> forall obj, (Globals.heap (State.global s)) ! obj = Some o -> 
      assoc (@pointer_eq_dec _) (obj, (apath2, i2, (h2, p2))) (State.construction_states s) = Some Constructed ->
      assoc (@pointer_eq_dec _) (obj, (apath1, i1, (h1, p1))) (State.construction_states s) = Some Constructed)
.      
Proof.
  intros.
  destruct (lifetime_total hierarchy_wf H H0); eauto using lifetime_construction_order.
Qed.
  

(** More precisely, we have this: *)

Lemma inheritance_construction_states_total :   forall obj
  (o : _)
  ar (ato : _) (zto  : _)
  (_ : valid_array_path (Program.hierarchy prog) ato zto (Object.class o) (Object.arraysize o) ar)
  i
  (_ : 0 <= i < zto)
  (mdh1 : _) (mdp1 : _) (to1 : _) (_ : path (Program.hierarchy prog) to1 mdp1 ato mdh1)
  (mdh2 : _) (mdp2 : _) (to2 : _) (_ : path (Program.hierarchy prog) to2 mdp2 ato mdh2)
  (_ : (mdh1, mdp1) <> (mdh2, mdp2))
  ,
  (((forall s, invariant prog s ->    (Globals.heap (State.global s)) ! obj = Some o ->
    constructed_sibling_before 
    (assoc (@pointer_eq_dec _) (obj, (ar, i, (mdh1, mdp1))) (State.construction_states s))
    (assoc (@pointer_eq_dec _) (obj, (ar, i, (mdh2, mdp2))) (State.construction_states s))
  )
    \/ 
    (forall s, invariant prog s ->    (Globals.heap (State.global s)) ! obj = Some o ->
      constructed_base_child_of
      (assoc (@pointer_eq_dec _) (obj, (ar, i, (mdh2, mdp2))) (State.construction_states s))
      (assoc (@pointer_eq_dec _) (obj, (ar, i, (mdh1, mdp1))) (State.construction_states s)))
  )\/(
    (forall s, invariant prog s ->    (Globals.heap (State.global s)) ! obj = Some o ->
      constructed_sibling_before (assoc (@pointer_eq_dec _) (obj, (ar, i, (mdh2, mdp2))) (State.construction_states s)) (assoc (@pointer_eq_dec _) (obj, (ar, i, (mdh1, mdp1))) (State.construction_states s))
    )
    \/ 
    (forall s, invariant prog s ->    (Globals.heap (State.global s)) ! obj = Some o ->
      constructed_base_child_of (assoc (@pointer_eq_dec _) (obj, (ar, i, (mdh1, mdp1))) (State.construction_states s)) (assoc (@pointer_eq_dec _) (obj, (ar, i, (mdh2, mdp2))) (State.construction_states s))
    )
  )).
Proof.
    intros.
    destruct (Class.Inheritance.eq_dec mdh1 mdh2).

(* same inheritance kind *)
     subst mdh1.
     destruct (list_eq_dec peq mdp1 mdp2).
      congruence.
     clear H3.
     revert mdp1 mdp2 n to1 H1 to2 H2.
     cut (
 forall mdp1 mdp2 : list ident,
   (List.length mdp1 <= List.length mdp2)%nat ->
  mdp1 <> mdp2 ->
   forall to1 : ident,
   path (A:=A) (Program.hierarchy prog) to1 mdp1 ato mdh2 ->
   forall to2 : ident,
   path (A:=A) (Program.hierarchy prog) to2 mdp2 ato mdh2 ->
   ((forall s : State.t A nativeop,
     invariant prog s ->
    (Globals.heap (State.global s)) ! obj = Some o ->
     constructed_sibling_before
       (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (mdh2, mdp1)))
          (State.construction_states s))
       (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (mdh2, mdp2)))
          (State.construction_states s))) \/
    (forall s : State.t A nativeop,
     invariant prog s ->
    (Globals.heap (State.global s)) ! obj = Some o ->
     constructed_base_child_of
       (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (mdh2, mdp2)))
          (State.construction_states s))
       (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (mdh2, mdp1)))
          (State.construction_states s)))) \/
   (forall s : State.t A nativeop,
    invariant prog s ->
    (Globals.heap (State.global s)) ! obj = Some o ->
    constructed_sibling_before
      (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (mdh2, mdp2)))
         (State.construction_states s))
      (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (mdh2, mdp1)))
         (State.construction_states s))) \/
   (forall s : State.t A nativeop,
    invariant prog s ->
    (Globals.heap (State.global s)) ! obj = Some o ->
    constructed_base_child_of
      (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (mdh2, mdp1)))
         (State.construction_states s))
      (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (mdh2, mdp2)))
         (State.construction_states s)))
     ).
      assert (forall A B, A \/ B -> B \/ A) by tauto.
      intros.
      destruct (le_lt_dec (length mdp1) (length mdp2)).
       eauto.
      assert (length mdp2 <= length mdp1)%nat by auto with arith.
      eauto.
     intros until 2.
     destruct (distinct_paths_cases peq H1 H2).

     (* subpath *)
      destruct s.
      destruct s.
      intros until 2.
      subst.
      assert (
        is_valid_repeated_subobject (Program.hierarchy prog) (mdp1 ++ x :: x0) = true
      ).
      generalize (path_path1 H4).
       inversion 1.
        assumption.
       inversion H7.
       assumption.
      generalize (path_last H3).
      intro.
      destruct (last_correct H6).
      subst.
      rewrite app_ass in H5.
      simpl in H5.
      assert (is_some (last (x1 ++ to1 :: nil))).
       rewrite H6.
       exact I.
      case_eq (last (x :: x0)).
      intros until 1.
      destruct (last_correct H8).
      generalize (is_valid_repeated_subobject_split_right H5 ).
      rewrite e.
      intro.
      inversion H0.
      left.
      right.
      intros.
       refine (_ (construction_states_nonempty_non_virtual_bases H12 (refl_equal _) (hp := H7) _ H6 H9 (refl_equal _))).
       Focus 2.
       econstructor.
       eassumption.
       econstructor.
       eassumption.
       eassumption.
       assumption.
       eassumption.
      rewrite app_ass.
      rewrite app_ass.
      simpl.
      tauto.
     intro.
     apply False_rect.
     eapply last_nonempty.
     2 : eassumption.
     congruence.

  (* disjoint paths *)
  clear H1 H2.
  destruct s.
  destruct s.
  destruct s.
  destruct s.
  destruct s.
  destruct a.
  destruct H2.
  subst.
  destruct x.

   (* different virtual bases *)
   simpl.
   destruct mdh2.
    inversion 1; subst.
    inversion 1; subst.
    abstract congruence.
   intros until 1.
   generalize (path_path1 H1).
   inversion 1; subst.
   clear H1 H2.
   intros until 1.
   generalize (path_path1 H1).
   inversion 1; subst.
   clear H1 H2.
   replace base with x0 in * by (inversion H5; abstract congruence).
   replace base0 with x1 in * by (inversion H7; abstract congruence).
   case_eq ((Program.hierarchy prog) ! ato); try (intros;    generalize (is_virtual_base_of_defined H4); abstract congruence).
   intros until 1.
   destruct (Well_formed_hierarchy.vborder_list_exists hierarchy_wf H1).
   generalize (virtual_base_vborder_list H4 H1 v).
   intro.
   generalize (virtual_base_vborder_list H6 H1 v).
   intro.
   revert x0 x1 H3 H2 H8 H4 H6 x2 to1 H5 x3 to2 H7.
   cut (
     forall x0 x1 l0 l1 l2,
       x = l0 ++ x0 :: l1 ++ x1 :: l2 ->
       x0 <> x1 ->
 is_virtual_base_of (A:=A) (Program.hierarchy prog) x0 ato ->
   is_virtual_base_of (A:=A) (Program.hierarchy prog) x1 ato ->
   forall (x2 : list positive) (to1 : ident),
   path (A:=A) (Program.hierarchy prog) to1 (x0 :: x2) x0
     Class.Inheritance.Repeated ->
   forall (x3 : list positive) (to2 : ident),
   path (A:=A) (Program.hierarchy prog) to2 (x1 :: x3) x1
     Class.Inheritance.Repeated ->
   ((forall s : State.t A nativeop,
     invariant prog s ->
     (Globals.heap (State.global s)) ! obj = Some o ->
     constructed_sibling_before
       (assoc (pointer_eq_dec (A:=A))
          (obj, (ar, i, (Class.Inheritance.Shared, x0 :: x2)))
          (State.construction_states s))
       (assoc (pointer_eq_dec (A:=A))
          (obj, (ar, i, (Class.Inheritance.Shared, x1 :: x3)))
          (State.construction_states s))) \/
    (forall s : State.t A nativeop,
     invariant prog s ->
     (Globals.heap (State.global s)) ! obj = Some o ->
     constructed_base_child_of
       (assoc (pointer_eq_dec (A:=A))
          (obj, (ar, i, (Class.Inheritance.Shared, x1 :: x3)))
          (State.construction_states s))
       (assoc (pointer_eq_dec (A:=A))
          (obj, (ar, i, (Class.Inheritance.Shared, x0 :: x2)))
          (State.construction_states s)))) \/
   (forall s : State.t A nativeop,
    invariant prog s ->
    (Globals.heap (State.global s)) ! obj = Some o ->
    constructed_sibling_before
      (assoc (pointer_eq_dec (A:=A))
         (obj, (ar, i, (Class.Inheritance.Shared, x1 :: x3)))
         (State.construction_states s))
      (assoc (pointer_eq_dec (A:=A))
         (obj, (ar, i, (Class.Inheritance.Shared, x0 :: x2)))
         (State.construction_states s))) \/
   (forall s : State.t A nativeop,
    invariant prog s ->
    (Globals.heap (State.global s)) ! obj = Some o ->
    constructed_base_child_of
      (assoc (pointer_eq_dec (A:=A))
         (obj, (ar, i, (Class.Inheritance.Shared, x0 :: x2)))
         (State.construction_states s))
      (assoc (pointer_eq_dec (A:=A))
         (obj, (ar, i, (Class.Inheritance.Shared, x1 :: x3)))
         (State.construction_states s)))
   ).
    intros until 4.
    destruct (list_lt_total peq H4 H8).
     destruct s.
     destruct l.
     destruct H5.
     destruct H5.
     eauto.
    destruct l.
    destruct H5.
    destruct H5.
    assert (forall A B : Prop, A \/ B -> B \/ A) by tauto.
    eauto.
   contradiction.
   intros.
   destruct (maximize_array_path H).
   invall.
   assert (0 <= i < x4) by omega.
   subst x.
   left.
   left.
   intros.
   generalize (breadth_virtual_bases H2 H13 H9 H11 H0 H1 v).
   intro.
   inversion H6; subst.
   injection H15; intros; subst.
   inversion H7; subst.
   injection H18; intros; subst.
   refine (_ (construction_states_non_virtual_bases 
 H2 (refl_equal _) (p := _ :: nil) (hp := I) _ (refl_equal _) H17 (refl_equal _) (refl_equal _) (refl_equal _))).
   Focus 2.
    econstructor.
    eassumption.
    econstructor.
    eassumption.
    eassumption.
    omega.
    eright.
    eexact H4.
    eleft with (lt := nil).
    reflexivity.
    reflexivity.
    simpl.
    generalize (path_defined_from H6).
    destruct ((Program.hierarchy prog) ! x0); congruence.
   refine (_ (construction_states_non_virtual_bases 
 H2 (refl_equal _) (p := _ :: nil) (hp := I) _ (refl_equal _) H20 (refl_equal _) (refl_equal _) (refl_equal _))).
    Focus 2.
    econstructor.
    eassumption.
    econstructor.
    eassumption.
    eassumption.
    omega.
    eright.
    eexact H5.
    eleft with (lt := nil).
    reflexivity.
    reflexivity.
    simpl.
    generalize (path_defined_from H7).
    destruct ((Program.hierarchy prog) ! x1); congruence.
   simpl.
   destruct 1; destruct 1; invall; subst;
   eauto using constructed_sibling_before_base_child, constructed_sibling_before_base_child_left.

 (* different non-virtual bases *)
 assert (p :: x <> nil) by abstract congruence.
 generalize (last_nonempty H1).
 case_eq (last (p :: x)); try abstract congruence.
 intros until 1.
 destruct (last_correct H2).
 rewrite e in *.
 clear p x H1 H2 e.
 intros _.
 intros until 1.
 assert (
   is_valid_repeated_subobject (Program.hierarchy prog)  ((x4 ++ p0 :: nil) ++ x0 :: x2) = true
 ).
  generalize (path_path1 H1).
  inversion 1; subst.
   assumption.
  inversion H5; subst; assumption.
 rewrite app_ass in H2.
 simpl in H2.
 generalize (is_valid_repeated_subobject_split_left H2).
 intro.
 generalize (is_valid_repeated_subobject_split_right H2).
 functional inversion 1; subst.
 intros until 1.
 assert (
   is_valid_repeated_subobject (Program.hierarchy prog)  ((x4 ++ p0 :: nil) ++ x1 :: x3) = true
 ).
  generalize (path_path1 H6).
  inversion 1; subst.
   assumption.
  inversion H9; subst; assumption.
 rewrite app_ass in H7.
 simpl in H7.
 generalize (is_valid_repeated_subobject_split_right H7).
 functional inversion 1; subst.
 clear H18 H13.
 replace cl1 with cl0 in * by abstract congruence.
 assert (
   path (Program.hierarchy prog) p0 (x4 ++ p0 :: nil) ato mdh2
 ).
  generalize (path_path1 H6).
  inversion 1; subst.
  case_eq (x4 ++ p0 :: nil).
   destruct x4; simpl; abstract congruence.
  intros until 1.
  rewrite <- H14.
  rewrite H14 in H11.
  simpl in H11.
  injection H11; intros; subst.
  eleft.
   eassumption.
   reflexivity.
   assumption.
  inversion H12; subst.
  case_eq (x4 ++ p0 :: nil).
   destruct x4; simpl; abstract congruence.
  intros.
  rewrite <- H17.
  rewrite H17 in H13.
  simpl in H13.
  injection H13; intros; subst.
  eright.
  eassumption.
  eleft.
  eassumption.
  reflexivity.
  assumption.
 rewrite app_ass.
 rewrite app_ass.
 simpl. 
 clear H1 H2 H4 H5 H6 H7 H15 H8.
  revert x0 x1 H3 _x _x0 x2 x3 X X0.
  cut (
    forall l0 x0 l1 x1 l2,
      map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b) (filter (fun hb : _ * ident =>
        match hb with
          | (Class.Inheritance.Shared, _) => false
          | _ => true
        end
      ) (Class.super cl0))
      = l0 ++ x0 :: l1 ++ x1 :: l2 ->
      forall (HI0 : In (Class.Inheritance.Repeated, x0) (Class.super cl0)) (HI1 : In (Class.Inheritance.Repeated, x1) (Class.super cl0))
        (x2 x3 : list positive),
   is_valid_repeated_subobject (A:=A) (Program.hierarchy prog) (x0 :: x2) =
   true ->
   is_valid_repeated_subobject (A:=A) (Program.hierarchy prog) (x1 :: x3) =
   true ->
   ((forall s : State.t A nativeop,
     invariant prog s ->
     (Globals.heap (State.global s)) ! obj = Some o ->
     constructed_sibling_before
       (assoc (pointer_eq_dec (A:=A))
          (obj, (ar, i, (mdh2, x4 ++ p0 :: x0 :: x2)))
          (State.construction_states s))
       (assoc (pointer_eq_dec (A:=A))
          (obj, (ar, i, (mdh2, x4 ++ p0 :: x1 :: x3)))
          (State.construction_states s))) \/
    (forall s : State.t A nativeop,
     invariant prog s ->
     (Globals.heap (State.global s)) ! obj = Some o ->
     constructed_base_child_of
       (assoc (pointer_eq_dec (A:=A))
          (obj, (ar, i, (mdh2, x4 ++ p0 :: x1 :: x3)))
          (State.construction_states s))
       (assoc (pointer_eq_dec (A:=A))
          (obj, (ar, i, (mdh2, x4 ++ p0 :: x0 :: x2)))
          (State.construction_states s)))) \/
   (forall s : State.t A nativeop,
    invariant prog s ->
    (Globals.heap (State.global s)) ! obj = Some o ->
    constructed_sibling_before
      (assoc (pointer_eq_dec (A:=A))
         (obj, (ar, i, (mdh2, x4 ++ p0 :: x1 :: x3)))
         (State.construction_states s))
      (assoc (pointer_eq_dec (A:=A))
         (obj, (ar, i, (mdh2, x4 ++ p0 :: x0 :: x2)))
         (State.construction_states s))) \/
   (forall s : State.t A nativeop,
    invariant prog s ->
    (Globals.heap (State.global s)) ! obj = Some o ->
    constructed_base_child_of
      (assoc (pointer_eq_dec (A:=A))
         (obj, (ar, i, (mdh2, x4 ++ p0 :: x0 :: x2)))
         (State.construction_states s))
      (assoc (pointer_eq_dec (A:=A))
         (obj, (ar, i, (mdh2, x4 ++ p0 :: x1 :: x3)))
         (State.construction_states s)))
  ).
  intros until 4.
  generalize (in_map_bases_intro _x).
  intro.
  generalize (in_map_bases_intro _x0).
  intro.
  destruct (list_lt_total peq H2 H4).
  2 : contradiction.
  destruct s.
   destruct l.
   destruct H5.
   destruct H5.
   eauto.
  destruct l.
  destruct H5.
  destruct H5.
  assert (forall A B, A \/ B -> B \/ A) by tauto.
  eauto.
 intros.
 assert (is_some (last (x4 ++ p0 :: nil))).
  rewrite last_complete.
  exact I.
 invall.
 left.
 left.
 intros.
 refine (_ (breadth_non_virtual_bases (hp := H4) _ _ _ _ _)). 
 2 : eassumption.
 3 : eapply last_complete.
 3 : eassumption.
 3 : eassumption.
 Focus 2.
  econstructor.
  eassumption.
  econstructor.
  eassumption.
  eassumption.
  assumption.
  eassumption.
 rewrite app_ass.
 rewrite app_ass.
 simpl.
 intro.
 assert (last (x4 ++ p0 :: x0 :: nil) = Some x0).
  rewrite last_app_left.
  reflexivity.
  congruence.
 assert (is_some (last (x4 ++ p0 :: x0 :: nil))).
  rewrite H8; exact I.
 assert  (last (x4 ++ p0 :: x1 :: nil) = Some x1).
  rewrite last_app_left.
  reflexivity.
  congruence.
 assert (is_some (last (x4 ++ p0 :: x1 :: nil))).
  rewrite H12; exact I.
 refine (_ (construction_states_non_virtual_bases (hp := H11) _ _ _ _ _ _ _ _)).
 2 : eassumption.
 2 : reflexivity.
 3 : eassumption.
 3 : eassumption.
 3 : reflexivity.
 3 : reflexivity.
 3 : reflexivity.
 Focus 2.
 econstructor.
 eassumption.
 econstructor.
 eassumption.
 eassumption.
 eassumption.
 eapply path_concat.
 eassumption.
 eleft with (lf := x0 :: nil) (lt := p0 :: nil).
 reflexivity.
 simpl; reflexivity.
 simpl.
 rewrite H10.
 sdestruct (
In_dec super_eq_dec (Class.Inheritance.Repeated, x0) (Class.super cl0)
 ); try contradiction.
 case_eq ((Program.hierarchy prog) ! x0); try congruence.
 functional inversion H2; congruence.
 simpl.
 rewrite last_complete.
 destruct (peq p0 p0); try congruence.
 rewrite app_ass.
 reflexivity.
 refine (_ (construction_states_non_virtual_bases (hp := H13) _ _ _ _ _ _ _ _)).
 2 : eassumption.
 2 : reflexivity.
 3 : eassumption.
 3 : eassumption.
 3 : reflexivity.
 3 : reflexivity.
 3 : reflexivity.
 Focus 2.
 econstructor.
 eassumption.
 econstructor.
 eassumption.
 eassumption.
 eassumption.
 eapply path_concat.
 eassumption.
 eleft with (lf := x1 :: nil) (lt := p0 :: nil).
 reflexivity.
 simpl; reflexivity.
 simpl.
 rewrite H10.
 sdestruct (
In_dec super_eq_dec (Class.Inheritance.Repeated, x1) (Class.super cl0)
 ); try contradiction.
 case_eq ((Program.hierarchy prog) ! x1); try congruence.
 functional inversion H3; congruence.
 simpl.
 rewrite last_complete.
 destruct (peq p0 p0); try congruence.
 rewrite app_ass.
 reflexivity.
rewrite app_ass.
rewrite app_ass.
simpl.
destruct 1; destruct 1; invall; subst; eauto using constructed_sibling_before_base_child, constructed_sibling_before_base_child_left.

(* non-virtual vs virtual *)
  clear H3.
  revert mdh1 mdh2 n mdp1 to1 H1 mdp2 to2 H2. 
  cut (
   forall (mdp1 : list ident) (to1 : ident),
   path (A:=A) (Program.hierarchy prog) to1 mdp1 ato Class.Inheritance.Shared ->
   forall (mdp2 : list ident) (to2 : ident),
   path (A:=A) (Program.hierarchy prog) to2 mdp2 ato Class.Inheritance.Repeated ->
  ((forall s : State.t A nativeop,
     invariant prog s ->
     (Globals.heap (State.global s)) ! obj = Some o ->
     constructed_sibling_before
       (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (Class.Inheritance.Shared, mdp1)))
          (State.construction_states s))
       (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (Class.Inheritance.Repeated, mdp2)))
          (State.construction_states s))) \/
    (forall s : State.t A nativeop,
     invariant prog s ->
     (Globals.heap (State.global s)) ! obj = Some o ->
     constructed_base_child_of
       (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (Class.Inheritance.Repeated, mdp2)))
          (State.construction_states s))
       (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (Class.Inheritance.Shared, mdp1)))
          (State.construction_states s)))) \/
   (forall s : State.t A nativeop,
    invariant prog s ->
    (Globals.heap (State.global s)) ! obj = Some o ->
    constructed_sibling_before
      (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (Class.Inheritance.Repeated, mdp2)))
         (State.construction_states s))
      (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (Class.Inheritance.Shared, mdp1)))
         (State.construction_states s))) \/
   (forall s : State.t A nativeop,
    invariant prog s ->
    (Globals.heap (State.global s)) ! obj = Some o ->
    constructed_base_child_of
      (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (Class.Inheritance.Shared, mdp1)))
         (State.construction_states s))
      (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (Class.Inheritance.Repeated, mdp2)))
         (State.construction_states s)))
  ).
  assert (forall A B, A \/ B -> B \/ A) by tauto.
   destruct mdh1; destruct mdh2; intro; try abstract congruence; eauto.
 intros until 1.
  generalize (path_path1 H1).
  clear H1.
  inversion 1; subst.
  clear H1.
  inversion H3; subst.  
  invall.
  inversion 1; subst.
 destruct (maximize_array_path H).
 invall.
 assert (0 <= i < x) by abstract omega.
  functional inversion H9; subst.
   (* most derived *)
  right.
  right.
  intros.
   refine (_ (construction_states_non_virtual_bases 
H13 (refl_equal _) (p := _ :: nil) (hp := I) _ (refl_equal _) _ (refl_equal _) (refl_equal _) (refl_equal _))).
   3 : eexact H5.
  Focus 2.
   econstructor.
   eassumption.
   econstructor.
   eexact H.
   eassumption.
   assumption.
   eright.
   eassumption.
   eleft with (lt := nil).
   reflexivity.
   reflexivity.
  revert H5.
  simpl.
  destruct (
(Program.hierarchy prog) ! base
  ); congruence.
   destruct lt0.
    injection H8; intros; subst.
    generalize (construction_states_virtual_bases H13 H14 H10 H12 H11 H2).
    intros.
    destruct x0; invall; subst; eauto using constructed_base_child_of_trans.
  destruct lt0; discriminate.
 (* non-virtual base *)
left.
left.
intros.  
   refine (_ (construction_states_non_virtual_bases 
H13 (refl_equal _) (p := _ :: nil) (hp := I) _ (refl_equal _) _ (refl_equal _) (refl_equal _) (refl_equal _))).
   3 : eexact H5.
  Focus 2.
   econstructor.
   eassumption.
   econstructor.
   eexact H.
   eassumption.
   assumption.
   eright.
   eassumption.
   eleft with (lt := nil).
   reflexivity.
   reflexivity.
  revert H5.
  simpl.
  destruct (
(Program.hierarchy prog) ! base
  ); congruence.
  destruct lt0.
   discriminate.
   injection H8; intros; subst.
   rewrite H8 in H0; simpl in H0.
   assert (is_some (last (i0 :: lt0 ++ to2 :: nil))).
    erewrite path_last.
    exact I.
    eassumption.
   refine (_
     (breadth_virtual_nonempty_non_virtual_bases (hp := H17) _ _ _ _ _)
   ).
   2 : eassumption.
    2 : reflexivity.
    3 : reflexivity.
    3 : eassumption.
   Focus 2.
   econstructor.
   eassumption.
   econstructor.
   eexact H.
   eassumption.
   eassumption.
   eassumption.
  rewrite H8; simpl.
  intro; destruct x0; invall; subst; eauto using constructed_sibling_before_base_child, constructed_sibling_before_base_child_left.
Qed.


End ConstrOrder.
