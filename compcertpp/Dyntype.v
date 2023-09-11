(* The dynamic type of a subobject *)

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
Require Import SubobjectOrdering.
Require Import ConstrSubobjectOrdering.
Load Param.
Open Scope nat_scope.

Lemma constructed_sibling_before_not_bases_constructed :
  forall a1 a2,
    constructed_sibling_before a1 a2 ->
    (a1 = Some BasesConstructed \/ a1 = Some StartedDestructing) ->
    (a2 = Some BasesConstructed \/ a2 = Some StartedDestructing) ->
    False.
Proof.
  intros.
    destruct (cs_le_dec_2 a1 (Some Constructed)).
    destruct (cs_le_dec_2 (Some Constructed) a1).     
     generalize (cs_le_antisym z z0).
     destruct H0; congruence.
   generalize (constructed_sibling_before_none H z0).
   destruct H1; congruence.
  generalize (constructed_sibling_before_destructed H z).
  destruct H1; congruence.
Qed.

Lemma constructed_base_child_of_not_bases_constructed :
  forall a1 a2,
    constructed_base_child_of a2 a1 ->
    (a1 = Some BasesConstructed \/ a1 = Some StartedDestructing) ->
    (a2 = Some BasesConstructed \/ a2 = Some StartedDestructing) ->
    False.
Proof.
  intros.
  assert (a2 = Some Constructed).
   eapply constructed_base_child_of_constructed.
   eassumption.
   destruct H0; subst; simpl; omega.
   destruct H0; subst; simpl; omega.
   destruct H1; congruence.
Qed.


Section DynamicType.

Variable A : ATOM.t.

Open Scope Z_scope.

  Section Get_dynamic_type.

  Variable hierarchy : PTree.t (Class.t A).

  Variable heap : PTree.t Object.t.

  Variable construction_states : list ((ident * (array_path A * Z * (Class.Inheritance.t * list ident))) * construction_state).

  Variable obj : ident.
  
  Variable ar : array_path A.
  
  Variable i : Z.

  Inductive get_dynamic_type : Class.Inheritance.t -> list ident -> Prop :=
  | get_dynamic_type_most_derived_constructed 
    (o : _)
    (_ : (heap) ! obj = Some o)
    (ato : _) (zto  : _)
    (_ : valid_array_path (hierarchy ) ato zto  (Object.class o) (Object.arraysize o) ar)
    (_ : 0 <= i < zto)
    (_ : assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Repeated, ato :: nil))) (construction_states) = Some Constructed) :
    get_dynamic_type
    Class.Inheritance.Repeated
    (ato :: nil)
  | get_dynamic_type_constructing_or_destructing
    (o : _)
    (_ : (heap) ! obj = Some o)
    (ato : _) (zto  : _)
    (_ : valid_array_path (hierarchy ) ato zto  (Object.class o) (Object.arraysize o) ar)
    (_ : 0 <= i < zto)
    (mdto : _) (mdh : _) (mdp : _)
    (_ : path (hierarchy ) mdto mdp ato mdh)
    (mdcs : _)
    (_ : mdcs = assoc (@pointer_eq_dec _) (obj, (ar, i, (mdh, mdp))) (construction_states))
    (_ : mdcs = Some BasesConstructed \/ mdcs = Some StartedDestructing)
    :
    get_dynamic_type
    mdh
    mdp
    .

  Lemma dynamic_type_get_dynamic_type : forall h p h1 p1 h2 p2,
    dynamic_type hierarchy heap construction_states obj ar i h p h1 p1 h2 p2 ->
    get_dynamic_type h1 p1.
  Proof.
    inversion 1; subst.
     eleft; eauto.
    eright; eauto.
  Qed.

  Lemma get_dynamic_type_dynamic_type : forall h1 p1,
    get_dynamic_type h1 p1 ->
    forall cn, last p1 = Some cn ->
      forall to h2 p2, path hierarchy to p2 cn h2 ->
        forall h' p', (h', p') = concat (h1, p1) (h2, p2) ->
          dynamic_type hierarchy heap construction_states obj ar i h' p' h1 p1 h2 p2.
  Proof.
    inversion 1; subst.
     injection 1; intros; subst.
     erewrite concat_trivial_left in H7.
     injection H7; intros; subst.
     eleft; eauto.
    eassumption.
   rewrite (path_last H3).
   injection 1; intros; subst.
   eright; eauto.
 Qed.

 Lemma get_dynamic_type_prop : forall h1 p1,
   get_dynamic_type h1 p1 -> exists o,
     (heap) ! obj = Some o /\
     exists ato, exists zto,
       valid_array_path (hierarchy ) ato zto  (Object.class o) (Object.arraysize o) ar /\
       0 <= i < zto /\
       (
         ((h1, p1) = (Class.Inheritance.Repeated, ato :: nil) /\ assoc (@pointer_eq_dec _) (obj, (ar, i, (h1, p1))) construction_states  = Some Constructed)
         \/
         exists mdto,
           path (hierarchy ) mdto p1 ato h1
           /\
           (
             assoc (@pointer_eq_dec _) (obj, (ar, i, (h1, p1))) (construction_states) = Some BasesConstructed \/
             assoc (@pointer_eq_dec _) (obj, (ar, i, (h1, p1))) (construction_states) = Some StartedDestructing
           )
       ).
Proof.
 inversion 1; subst; eauto 10.
Qed.   

 End Get_dynamic_type.

Variable nativeop : Type.
Variable sem : semparam A nativeop.

Variable prog : Program.t A nativeop.

Hypothesis hierarchy_wf : Well_formed_hierarchy.prop (Program.hierarchy prog).


  Variable state : State.t A nativeop.


  Variable Hinv: invariant prog state.


  Variable obj : ident.
  
  Variable ar : array_path A.
  
  Variable i : Z.

  Lemma bases_constructed_unique : forall 
    (o : _)
    (_ : (Globals.heap (State.global state)) ! obj = Some o)
    (ato : _) (zto  : _)
    (_ : valid_array_path (Program.hierarchy prog) ato zto (Object.class o) (Object.arraysize o) ar)
    (_ : 0 <= i < zto)
    (mdh1 : _) (mdp1 : _) (to1 : _) (_ : path (Program.hierarchy prog) to1 mdp1 ato mdh1)
    (mdcs1 : _)
    (_ : mdcs1 = assoc (@pointer_eq_dec _) (obj, (ar, i, (mdh1, mdp1))) (State.construction_states state))
    (_ : mdcs1 = Some BasesConstructed \/ mdcs1 = Some StartedDestructing)
    (mdh2 : _) (mdp2 : _) (to2 : _) (_ : path (Program.hierarchy prog) to2 mdp2 ato mdh2)
    (mdcs2 : _)
    (_ : mdcs2 = assoc (@pointer_eq_dec _) (obj, (ar, i, (mdh2, mdp2))) (State.construction_states state))
    (_ : mdcs2 = Some BasesConstructed \/ mdcs2 = Some StartedDestructing)
    ,
    (mdh1, mdp1) = (mdh2, mdp2)
    .
  Proof.
    intros; subst.
    destruct (path_eq_dec (mdh1, mdp1) (mdh2, mdp2)).
     assumption.
    apply False_rect.
    generalize (inheritance_construction_states_total hierarchy_wf obj H0 H1 H2 H5 n).
    destruct 1 as [J | J]; destruct J; eauto using  constructed_sibling_before_not_bases_constructed , constructed_base_child_of_not_bases_constructed.
  Qed.

Corollary get_dynamic_type_unique :
forall
  mdh1 mdp1,
  get_dynamic_type (Program.hierarchy prog) (Globals.heap (State.global state)) (State.construction_states state) obj ar i mdh1 mdp1 ->
  forall mdh2 mdp2,
    get_dynamic_type  (Program.hierarchy prog) (Globals.heap (State.global state)) (State.construction_states state) obj ar i mdh2 mdp2 ->
    (mdh1, mdp1) = (mdh2, mdp2).  
Proof.
  inversion 1; subst.
   inversion 1; subst.
    replace o0 with o in * by abstract congruence.
    generalize (valid_array_path_last H1 H6).
    congruence.
   replace o0 with o in * by abstract congruence.
   generalize (valid_array_path_last H1 H6).
   intro; subst.
   generalize (inclusion_inheritance_subobject_of_full_object H1 H2 H8).
   intro.
   generalize (inclusion_construction_order Hinv H5 H9). 
   intro.
   generalize (construction_includes_constructed H11 H3).
   unfold_ident_in_all.
   destruct H10; abstract congruence.
  inversion 1; subst.
   replace o0 with o in * by abstract congruence.
   generalize (valid_array_path_last H1 H7).
   intro; subst.
   generalize (inclusion_inheritance_subobject_of_full_object H1 H2 H3).
   intro.
   generalize (inclusion_construction_order Hinv H6 H10). 
   intro.
   generalize (construction_includes_constructed H11 H9).
   unfold_ident_in_all.
   destruct H5; abstract congruence.
  replace o0 with o in * by abstract congruence.
  generalize (valid_array_path_last H1 H7).
  intros; subst.
  eauto using bases_constructed_unique.
Qed.

Corollary dynamic_type_unique_very_strong : forall
  h1 p1 mdh1 mdp1 mdh'1 mdp'1,
  dynamic_type (Program.hierarchy prog) (Globals.heap (State.global state)) (State.construction_states state) obj ar i h1 p1 mdh1 mdp1 mdh'1 mdp'1 ->
  forall h2 p2 mdh2 mdp2 mdh'2 mdp'2,
    dynamic_type  (Program.hierarchy prog) (Globals.heap (State.global state)) (State.construction_states state) obj ar i h2 p2  mdh2 mdp2 mdh'2 mdp'2 ->
    (mdh1, mdp1) = (mdh2, mdp2).
Proof.
  intros; eauto using dynamic_type_get_dynamic_type, get_dynamic_type_unique.
Qed.

Section Dynamic_type_unique.

  Variable h: Class.Inheritance.t.
  
  Variable p: list ident.        

Lemma dynamic_type_same_complement :  forall mdh mdp mdh' mdp',
  dynamic_type (Program.hierarchy prog)  (Globals.heap (State.global state)) (State.construction_states state) obj ar i h p  mdh mdp mdh' mdp' ->
  forall mdh'2 mdp'2,
    dynamic_type (Program.hierarchy prog)  (Globals.heap (State.global state)) (State.construction_states state) obj ar i h p  mdh mdp mdh'2 mdp'2 ->
    (mdh', mdp') = (mdh'2, mdp'2).
Proof.
 intros until 1.
 generalize  (dynamic_type_prop H).
  intros; invall; subst.
 generalize (dynamic_type_prop H1).
 intros; invall; subst.
 replace x4 with x in * by abstract congruence.
 generalize (valid_array_path_last H2 H9).
 intros; subst.
 generalize (path_last H12).
 rewrite (path_last H5).
 injection 1; intros; subst.
 eapply Well_formed_hierarchy.concat_path_unique.
 eassumption.
 eassumption.
 eassumption.
 eassumption.
 eapply trans_equal.
 symmetry.
 eassumption.
 assumption.
Qed. 

(** * POPL 2012 submission: Theorem 17 *)

Corollary dynamic_type_unique : forall
  mdh1 mdp1 mdh'1 mdp'1,
  dynamic_type (Program.hierarchy prog) (Globals.heap (State.global state)) (State.construction_states state) obj ar i h p mdh1 mdp1 mdh'1 mdp'1 ->
  forall mdh2 mdp2 mdh'2 mdp'2,
    dynamic_type  (Program.hierarchy prog) (Globals.heap (State.global state)) (State.construction_states state) obj ar i h p  mdh2 mdp2 mdh'2 mdp'2 ->
    (mdh1, mdp1) = (mdh2, mdp2).
Proof.
  eauto using dynamic_type_unique_very_strong.
Qed.

Corollary dynamic_type_unique_strong : forall
  mdh1 mdp1 mdh'1 mdp'1,
  dynamic_type (Program.hierarchy prog) (Globals.heap (State.global state)) (State.construction_states state) obj ar i h p mdh1 mdp1 mdh'1 mdp'1 ->
  forall mdh2 mdp2 mdh'2 mdp'2,
    dynamic_type  (Program.hierarchy prog) (Globals.heap (State.global state)) (State.construction_states state) obj ar i h p  mdh2 mdp2 mdh'2 mdp'2 ->
    (mdh1, mdp1, mdh'1, mdp'1) = (mdh2, mdp2, mdh'2, mdp'2).
Proof.
 intros.
 generalize (dynamic_type_unique H H0).
 injection 1; intros; subst.
 generalize (dynamic_type_same_complement H H0).
 congruence.
Qed.


Lemma dynamic_type_not_deallocated : forall 
  mdh1 mdp1 mdh'1 mdp'1,
  dynamic_type (Program.hierarchy prog) (Globals.heap (State.global state)) (State.construction_states state) obj ar i h p mdh1 mdp1 mdh'1 mdp'1  ->
  In obj (State.deallocated_objects  state) -> False.
Proof.
intros; eauto using dynamic_type_get_dynamic_type .
generalize (dynamic_type_prop H).
intro; invall.
assert (
valid_relative_pointer (A:=A) (Program.hierarchy prog) 
     (Object.class x) (Object.arraysize x) ar x0 i mdh1 mdp1 
     x2
).
 econstructor; eauto.
 generalize (inclusion_subobject_of_full_object H3).
 intros; invall.
 generalize (deallocated_objects_destructed Hinv H0 H1 (conj H10 H12)).
 intro.
 generalize (inclusion_construction_order Hinv H1 H11).
 intro.
 generalize (construction_includes_destructed H13 H9).
 simpl.
 inversion H; subst; unfold_ident_in_all; try congruence.
  destruct H19; congruence.
Qed.

End Dynamic_type_unique.

Corollary get_dynamic_type_not_deallocated : forall 
  mdh1 mdp1,
  get_dynamic_type (Program.hierarchy prog) (Globals.heap (State.global state)) (State.construction_states state) obj ar i mdh1 mdp1 ->
  In obj (State.deallocated_objects  state) -> False.
Proof.
intros.
generalize (get_dynamic_type_prop H).
intro; invall.
assert (exists x, path (Program.hierarchy prog) x mdp1 x0 mdh1).
 destruct H5; invall; eauto.
  injection H5; intros; subst; simpl.
  esplit.
  eleft with (lf := nil) (lt := nil).
  reflexivity.
  simpl; reflexivity.
  simpl.
 case_eq ((Program.hierarchy prog) ! x0); trivial.
 intro.
 refine (False_rect _ (Well_formed_hierarchy.array_path_valid hierarchy_wf H2 _ H3)). 
 eauto using valid_object_classes.
invall.
eapply dynamic_type_not_deallocated.
eapply get_dynamic_type_dynamic_type.
eassumption.
eauto using path_last.
eleft with (lf := nil) (lt := nil).
 reflexivity.
 simpl; reflexivity.
 simpl.
 case_eq ((Program.hierarchy prog) ! x2); trivial.
 intro.
 generalize (path_defined_to H7).
 intro; contradiction.
symmetry; eapply concat_trivial_right.
eassumption.
assumption.
Qed.

End DynamicType.
