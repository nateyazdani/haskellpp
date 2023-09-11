(** Cplusconcepts.v: Copyright 2010 Tahina Ramananandro *)

Require Import LibLists.
Require Import Relations.
Require Import Tactics.
Load Param.
Require Import Recdef.

Require Import Maps.
Require Import Coqlib.
Require Import Eqdep_dec.
Require Export BuiltinTypes.
Definition ident := positive. (* unable to turn it into a Notation, because of automatic Coq variable names which would become p instead of i *)
Ltac unfold_ident := unfold ident.
Ltac unfold_ident_in_all := unfold ident in *.
Ltac unfold_ident_in H := unfold ident in H.

(** * C++ notions *)

(** Static type of a scalar : atomic or pointer to class instance *)

 Module Typ.
  Section Typ.
    Variable A : ATOM.t.

    Inductive t : Type :=
    | atom (_ : ATOM.ty A)
    | class (_ : ident)
      .

  Lemma eq_dec : forall a b : t, {a = b} + {a <> b}.
  Proof.
    repeat decide equality.
  Qed.
 End Typ.
 Implicit Arguments class [A].

End Typ.

(** Static weak type of a scalar (atomic or pointer) *)
Module WeakTyp.
 Section WeakTyp.
  Variable A : ATOM.t.

  Inductive t : Type :=
  | atom (_ : ATOM.ty A)
  | object
    .

  Fixpoint of_type (u : Typ.t A) : t :=
    match u with
      | Typ.atom a => atom a
      | Typ.class _ => object
    end.

  Fixpoint option_of_type (u : option (Typ.t A)) : option t :=
  match u with
    | None => None
    | Some t' => Some (of_type t')
  end.

  Lemma eq_dec : forall u1 u2 : t, {u1 = u2} + {u1 <> u2}.
  Proof.
   repeat decide equality.
  Qed.
End WeakTyp.
Implicit Arguments object [A].
End WeakTyp.

(** Methods. *)

Module MethodSignature.
  Section MS.
  Variable A : ATOM.t.
  Record t : Type := make {
    name : ident;
    params : list (Typ.t A);
    return_type : option (Typ.t A)
  }.
  Lemma eq_dec : forall a b : t, {a = b} + {a <> b}.
  Proof.
    repeat decide equality.
  Qed.
End MS.
End MethodSignature.

Module Method.
  Section M.
    Variable A : ATOM.t.

(** The code for a method is not included in the hierarchy. Instead, [entry] specifies the "address" of the method code into a "code pool" provided separately from the hierarchy *)

    Inductive method_kind : Set :=
    | abstract 
    | concrete (entry : ident)
      .

  Record t : Type := make {
    signature : MethodSignature.t A;
    kind : method_kind; 
    virtual : bool 
  }.

  Definition find (s : MethodSignature.t A) :=
    find (fun m => if MethodSignature.eq_dec (signature m) s then true else false).

  Lemma find_in : forall s m l, find s l = Some m -> In m l.
  Proof.
   induction l; simpl; try congruence.
   destruct (MethodSignature.eq_dec (signature a) s).
    injection 1; eauto.
   eauto.
  Qed.

End M.

End Method.

(** Fields *)

Module FieldSignature.
  Section FS.
    Variable A : ATOM.t.

(** A field may be scalar, or structure array. The number of elements in an array cannot be zero. *)

  Inductive field_type : Type :=
  | Scalar (_ : Typ.t A)
  | Struct (struct : ident) (arraysize : positive)
    .

  Record t : Type := make {
    name : ident;
    type : field_type
  }.

  Lemma eq_dec : forall a b : t, {a = b} + {a <> b}.
  Proof.
    intros.
    repeat decide equality.
  Qed.
End FS.

  Implicit Arguments Struct [A].

End FieldSignature.

(** Classes. *)

Module Class.  
  Module Inheritance.
    Inductive t : Set :=
    | Repeated | Shared
      .
    Theorem eq_dec : forall a b : t, {a = b} + {a <> b}.
    Proof.
      decide equality.
    Qed.
  End Inheritance.
  Section C.
    Variable A : ATOM.t.
  Record t : Type := make {
    super : list (Inheritance.t * ident) ;
    fields : list (FieldSignature.t A);
    methods : list (Method.t A)
  }.
End C.

End Class.


Lemma in_map_bases_intro : forall l c, In (Class.Inheritance.Repeated, c) l -> In c (map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b) (filter (fun hb : _ * ident =>
    match hb with
      | (Class.Inheritance.Shared, _) => false
      | _ => true
    end
  ) l)).
Proof.
 intros.
 eapply in_map_iff.
 refine (ex_intro _ (_, _) _).
 split.
  reflexivity.
 eapply filter_In.
 split.
  eassumption.
 reflexivity.
Qed.

Lemma in_map_bases_elim : forall l c,  In c (map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b) (filter (fun hb : _ * ident =>
    match hb with
      | (Class.Inheritance.Shared, _) => false
      | _ => true
    end
  ) l)) -> In (Class.Inheritance.Repeated, c) l.
Proof.
  intros.
  destruct (let (h, _) := in_map_iff _ _ _ in h H).
  destruct H0.
  destruct x.
  subst.
  destruct (let (h, _) := filter_In _ _ _ in h H1).
  destruct t.
   assumption.
  discriminate.
 Qed.


(** A hierarchy is a mapping of classes: [PTree.t Class.t]. Remember that a hierarchy does not include the code for methods *)

(** * Operational semantics *)

Function is_some (A : Type) (x : option A) : Prop :=
  match x with None => False | Some _ => True end.

Definition is_some_constr {A : Type} (x : option A) (h : is_some x) : {y | x = Some y}.
Proof.
  intros.
  functional induction (is_some x).
   contradiction.
  repeat esplit. 
Qed.

Lemma is_some_eq : forall (A : Type) (x : _ A) (h1 h2 : is_some x), h1 = h2.
Proof.
  intros A x.
  functional induction (is_some x).
   contradiction.
  dependent inversion h1 ; dependent inversion h2 ; trivial.
Qed.

Lemma is_some_last_one_elem : forall (A : Type) (a : A), is_some (last (a :: nil)).
Proof.
  simpl.
  tauto.
Qed.

Section Subobjects.
  Variable A : ATOM.t.

(** ** Path to a subobject (inheritance)

   Directly inspired from Wasserrab et al. 
*)

Section Paths.

Variable hierarchy : PTree.t (Class.t A).

Lemma super_eq_dec : forall i j : (Class.Inheritance.t * ident),
  {i = j} + {i <> j}.
Proof.
  repeat decide equality.
Qed.

(** [is_valid_repeated_subobject] decides whether a list of class identifiers represents a valid non-virtual inheritance path:
   - [a :: nil] is a valid non-virtual inheritance path if, and only if, [a] is defined
   - [a :: b :: l] is a valid non-virtual inheritance path if, and only if, [b] is a direct non-virtual base of [a] and [b :: l] is a valid non-virtual inheritance path
   *)

Function is_valid_repeated_subobject (l : list ident) : bool :=
  match l with
    | nil => false
    | id1 :: l2 =>
      match PTree.get id1 hierarchy with
        | None => false
        | Some cl1 =>
          match l2 with
            | nil => true
            | id2 :: l3 =>
              if In_dec super_eq_dec (Class.Inheritance.Repeated, id2) (Class.super cl1)
                then is_valid_repeated_subobject l2
                else false
          end
      end
  end.

Lemma is_valid_repeated_subobject_join : forall l1 p l2,
  is_valid_repeated_subobject (l1 ++ p :: nil) = true ->
  is_valid_repeated_subobject (p :: l2) = true ->
  is_valid_repeated_subobject (l1 ++ p :: l2) = true.
Proof.
  induction l1 ; simpl.
  (* case nil *)
  tauto.
  (* case cons *)
  case_eq (hierarchy ! a) ; try (intros ; discriminate).
  intros until l2.
  destruct l1 ; simpl.
  destruct (In_dec super_eq_dec (Class.Inheritance.Repeated, p) (Class.super t)) ; try (intros ; discriminate).
  tauto.
  destruct (In_dec super_eq_dec (Class.Inheritance.Repeated, i) (Class.super t)) ; try (intros ; discriminate).
  case_eq (hierarchy ! i) ; try (intros ; discriminate).
  case_eq (hierarchy ! p) ; try (intros ; discriminate).
  intros.
  simpl in IHl1.
  rewrite H1 in IHl1.
  generalize (IHl1 p l2).
  clear IHl1.
  intro IHl1.
  rewrite H0 in IHl1.
  eauto.
Qed.
  
Lemma is_valid_repeated_subobject_split_left : forall l1 p l2,
  is_valid_repeated_subobject (l1 ++ p :: l2) = true ->
  is_valid_repeated_subobject (l1 ++ p :: nil) = true.
Proof.
  induction l1 ; simpl.
  (* case nil *)
  intros ;  destruct (hierarchy ! p) ; congruence.
  (* case cons *)
  intros until l2.
  case_eq (hierarchy ! a) ; try congruence.
  intros until 1.
  destruct l1 ; simpl.
   destruct (In_dec super_eq_dec (Class.Inheritance.Repeated, p) (Class.super t)) ; try congruence.
   destruct (hierarchy ! p) ; try congruence.
  destruct (In_dec super_eq_dec (Class.Inheritance.Repeated, i) (Class.super t)) ; try congruence.
  case_eq (hierarchy ! i) ; try congruence.
  intros.
  generalize (IHl1 p l2).
  clear IHl1.
  simpl.
  rewrite H0.
  eauto.
Qed.

Lemma is_valid_repeated_subobject_split_right : forall l1 p l2,
  is_valid_repeated_subobject (l1 ++ p :: l2) = true ->
  is_valid_repeated_subobject (p :: l2) = true.
Proof.
  induction l1 ; simpl.
  (* case nil *)
  tauto.
  (* case cons *)
  intros until l2.
  case_eq (hierarchy ! a) ; try congruence.
  intros until 1.
  destruct l1 ; simpl.
   destruct (In_dec super_eq_dec (Class.Inheritance.Repeated, p) (Class.super t)) ; try congruence.
  destruct (In_dec super_eq_dec (Class.Inheritance.Repeated, i) (Class.super t)) ; try congruence.
  case_eq (hierarchy ! i) ; try congruence.
  intros.  
  generalize (IHl1 p l2).
  clear IHl1.
  simpl.
  rewrite H0.
  eauto.
Qed.

Lemma is_valid_repeated_subobject_cons_right : forall l1 p,
  is_valid_repeated_subobject (l1 ++ p :: nil) = true ->
  forall c, PTree.get p hierarchy = Some c ->
    forall q, In (Class.Inheritance.Repeated, q) (Class.super c) ->
      PTree.get q hierarchy <> None ->
      is_valid_repeated_subobject (l1 ++ p :: q :: nil) = true.
Proof.
  induction l1 ; simpl.
  (* nil *)
  intros.
  rewrite H0 in *.
  destruct (In_dec super_eq_dec (Class.Inheritance.Repeated, q) (Class.super c)) ; try contradiction.
  case_eq (hierarchy ! q) ; try contradiction.
  tauto.
  (* cons *)
  intros.
  generalize (fun Hp => IHl1 p Hp c H0 q H1 H2).
  clear IHl1.
  intro IHl1.
  revert H.
  case_eq (hierarchy ! q) ; try contradiction.
  intros until 1.
  destruct (hierarchy ! a) ; try congruence.
  destruct l1 ; simpl.
   rewrite H0.
   destruct (In_dec super_eq_dec (Class.Inheritance.Repeated, p) (Class.super t0));  try congruence.
   destruct (In_dec super_eq_dec (Class.Inheritance.Repeated, q) (Class.super c)) ; try contradiction.
   rewrite H.
   tauto.
  destruct (In_dec super_eq_dec (Class.Inheritance.Repeated, i) (Class.super t0)) ; try congruence.
  case_eq (hierarchy ! i) ; try congruence.
  simpl in IHl1.
  intros until 1.
  rewrite H3 in IHl1.
  assumption.
Qed.

Lemma is_valid_repeated_subobject_defined : forall l,
  is_valid_repeated_subobject l = true ->
  forall a, In a l -> hierarchy ! a <> None.
Proof.
  intro l.
  functional induction (is_valid_repeated_subobject l) ; try congruence.
   simpl.
   inversion 2 ; congruence.
   intros.
   simpl in H0.
   inversion H0.
    subst.
    congruence.
   eauto.
 Qed.
  
  
Section Virtual_base.

Variable bi : ident.

(** [bi] is a virtual base of a class [ci] if, and only if, either [bi] is a direct virtual base of [ci], or [bi] is a virtual base of some direct base [bi'] of [ci]. *)

Inductive is_virtual_base_of : ident -> Prop :=
| is_virtual_base_of_O :
  forall ci c,
    PTree.get ci hierarchy = Some c ->
    In (Class.Inheritance.Shared, bi) (Class.super c) ->
    is_virtual_base_of ci
| is_virtual_base_of_S :
  forall ci c,
    PTree.get ci hierarchy = Some c ->
    forall h' bi',
      In (h', bi') (Class.super c) ->
      is_virtual_base_of bi' ->
      is_virtual_base_of ci
.

Lemma is_virtual_base_of_defined : forall ci,
  is_virtual_base_of ci ->
  PTree.get ci hierarchy <> None.
Proof.
 inversion 1; abstract congruence.
Qed.


End Virtual_base.

Lemma is_virtual_base_of_trans : forall b c,
  is_virtual_base_of b c ->
  forall a,
    is_virtual_base_of a b ->
    is_virtual_base_of a c
.
Proof.
  induction 1.
   intros.
   eright.
   eassumption.
   eassumption.
   assumption.
  intros.
  eright.
  eassumption.
  eassumption.
  eauto.
Qed.

Section Path.

Variable to : ident.

Section path1.

Variable via : list ident.

(** [path hierarchy to via from h] holds if, and only if, [(h, via)] is a base class subobject of [from] of static type [to], i.e. if, and only if:
   - [h = Repeated] and [via] is a non-virtual path from [from] to [to]
   - or [h = Shared] and [(h', via)] is a base class subobject of some virtual base [base] of [from] of static type [to]
*)

Inductive path : forall from : ident, Class.Inheritance.t -> Prop :=
| path_repeated :
  forall from lf lt,
    via = from :: lf ->
    via = lt ++ to :: nil ->
    is_valid_repeated_subobject via = true ->
    path from Class.Inheritance.Repeated
| path_shared : forall from base h,
  is_virtual_base_of base from ->
  path base h ->
  path from Class.Inheritance.Shared
.

(** [path0] is an equivalent definition of the notion of base class subobject, which "collapses" the choice of the virtual base in case of a shared subobject:
   - [h = Repeated] and [via] is a non-virtual path from [from] to [to]
   - or [h = Shared] and [via] is a non-virtual path from some virtual base [base] of [from] of static type [to]
*)

Inductive path0 : forall from : ident, Class.Inheritance.t -> Prop :=
| path0_repeated :
  forall from lf lt,
    via = from :: lf ->
    via = lt ++ to :: nil ->
    is_valid_repeated_subobject via = true ->
    path0 from Class.Inheritance.Repeated
| path0_shared : forall from base,
  is_virtual_base_of base from ->
  forall lf lt,
    via = base ::lf ->
    via = lt ++ to :: nil ->
    is_valid_repeated_subobject via = true ->
    path0 from Class.Inheritance.Shared
.


Lemma path0_path : forall from h, path0 from h -> path from h.
Proof.
 induction 1.
  eleft;  eassumption.
  eright.
   eassumption.
  eleft ; eassumption.
Qed.

Lemma path_path0 : forall from h, path from h -> path0 from h.
Proof.
 induction 1.
 eleft ; eassumption.
 clear H0.
 inversion IHpath.
  subst from0.
  subst h.
  eright ;  eassumption.
 subst from0.
 subst h.
 eright.
  2 : eassumption.
  2 : eassumption.
  2 : assumption.
 eauto using is_virtual_base_of_trans.
Qed.


(** [path1] is a reformulation of [path0] *)

Inductive path1 : forall from : ident, Class.Inheritance.t -> Prop :=
| path1_repeated :
  forall from lf lt,
    via = from :: lf ->
    via = lt ++ to :: nil ->
    is_valid_repeated_subobject via = true ->
    path1 from Class.Inheritance.Repeated
| path1_shared : forall from base,
  is_virtual_base_of base from ->
  path base Class.Inheritance.Repeated ->
    path1 from Class.Inheritance.Shared
.


Lemma path1_path : forall from h, path1 from h -> path from h.
Proof.
 induction 1.
  econstructor.
  eassumption.
  eassumption.
  assumption.
 inversion H0.
 apply path0_path.
 econstructor.
 eassumption.
 eassumption.
 eassumption.
 assumption.
Qed.

Lemma path_path1 : forall from h, path from h -> path1 from h.
Proof.
 induction 1.
  econstructor.
  eassumption.
  eassumption.
  assumption.
 inversion IHpath.
  subst.
  econstructor.
  eassumption.
  assumption.
 subst.
 econstructor.
 eapply is_virtual_base_of_trans.
 eassumption.
 eassumption.
 assumption.
Qed.


End path1.

(** [path2] defines the notion of base class subobject in a "small-step" flavour *)

Inductive path2 : forall (via : list ident) (from : ident), Class.Inheritance.t -> Prop :=
| path_O :
  PTree.get to hierarchy <> None ->
  path2 (to :: nil) to Class.Inheritance.Repeated
| path_S_repeated :
  forall from cfrom,
    PTree.get from hierarchy = Some cfrom ->
    forall interm,
      In (Class.Inheritance.Repeated, interm) (Class.super cfrom) ->
      forall l,
        path2 l interm Class.Inheritance.Repeated ->
        path2 (from :: l) from Class.Inheritance.Repeated
| path_S_shared_1 :
  forall from cfrom,
    PTree.get from hierarchy = Some cfrom ->
    forall interm,
      In (Class.Inheritance.Shared, interm) (Class.super cfrom) ->
      forall l h,
        path2 l interm h ->
        path2 l from Class.Inheritance.Shared
| path_S_shared_2 :
  forall from cfrom,
    PTree.get from hierarchy = Some cfrom ->
    forall h interm,
      In (h, interm) (Class.super cfrom) ->
      forall l,
        path2 l interm Class.Inheritance.Shared ->
        path2 l from Class.Inheritance.Shared
.

Lemma path2_path : forall via from h,
  path2 via from h ->
  path via from h.
Proof.
  intros.
  apply path0_path.
  induction H.
   eleft.
   reflexivity.
   change (to :: nil) with (nil ++ to :: nil).
   reflexivity.
   simpl.
   revert H ; destruct (hierarchy ! to) ; congruence.

 inversion IHpath2.
 subst.
 eleft.
 reflexivity.
 rewrite H3.
 change (from :: lt ++ to :: nil) with ((from :: lt) ++ to :: nil).
 reflexivity.
 remember (interm :: lf) as l.
 simpl.
 rewrite H.
 pattern l at 1.
 rewrite Heql.
 destruct (
 In_dec super_eq_dec (Class.Inheritance.Repeated, interm)
         (Class.super cfrom) 
 ) ; congruence.

 clear H1.
 inversion IHpath2.

 subst.
 eright.
 eleft.
 eassumption.
 eassumption.
 reflexivity.
 eassumption.
 assumption.

 subst.
 eright.
 eapply is_virtual_base_of_trans.
 eleft.
 eassumption.
 eassumption.
 eassumption.
 reflexivity.
 eassumption.
 assumption.

 inversion IHpath2.
 subst.
 eright.
 eright.
 eassumption.
 eassumption.
 eassumption.
 reflexivity.
 eassumption.
 assumption.
Qed.
 
Lemma path_path2_repeated :
  forall l from,
    path l from Class.Inheritance.Repeated ->
    path2 l from Class.Inheritance.Repeated
.
Proof.
 intros.
 generalize (path_path0 H).
 clear H.
 revert from.
 induction l.
  inversion 1.
  discriminate.
 
 inversion 1.
 subst.
 destruct l.
  simpl in H2.
  destruct lt ; simpl in H1.
  injection H1 ; intro ; subst.
  injection H0 ; intros ; subst from.
  eapply path_O.
  revert H2 ; destruct (hierarchy ! to) ; congruence.
  injection H1.
  intro.
  destruct lt ; simpl in H3 ; congruence.

  injection H0 ; intros ; subst.
  simpl in H2.
  revert H2.
  case_eq (hierarchy ! from) ; try congruence.
  intros cfrom ?.
  destruct (
 In_dec super_eq_dec (Class.Inheritance.Repeated, i)
         (Class.super cfrom)
  ) ; try congruence.
  intro.
  eapply path_S_repeated.
  eassumption.
  eassumption.
  destruct lt.
   simpl in H1.
   discriminate.
  simpl in H1.
  injection H1.
  intros ; subst.
  eapply IHl.
  eleft.
  reflexivity.
  eassumption.
  assumption.
Qed.

Lemma path_path2 : forall l from h,
  path l from h ->
  path2 l from h
.
Proof.
 intros.
 generalize (path_path0 H).
 clear H.
 induction 1.
  eapply path_path2_repeated.
  econstructor ; eassumption.
 assert (path0 l base Class.Inheritance.Repeated).
  econstructor ; eassumption.
 clear lf lt H0 H1 H2.
 generalize (path_path2_repeated (path0_path H3)).
 clear H3.
 revert l. 
 induction H.
  intros.
  eapply path_S_shared_1.
  eassumption.
  eassumption.
  eassumption.
 intros.
 eapply path_S_shared_2.
 eassumption.
 eassumption.
 eauto.
Qed.

Lemma path_repeated_cons : forall i c,
  hierarchy ! i = Some c ->
  forall d, In (Class.Inheritance.Repeated, d) (Class.super c) ->
    forall l, path l d Class.Inheritance.Repeated ->
      path (i :: l) i Class.Inheritance.Repeated.
Proof.
  intros.
  inversion H1.
  subst.
  econstructor.
  reflexivity.
  rewrite H3.
  change (i :: lt ++ to :: nil) with ((i :: lt) ++ to :: nil).
  reflexivity.
  remember (d :: lf) as l'.
  simpl.
  rewrite H.
  pattern l' at 1.
  rewrite Heql'.
  destruct (In_dec super_eq_dec (Class.Inheritance.Repeated, d) (Class.super c)) ; try contradiction.
  assumption.
Qed.

Lemma path_last : forall l d k,
  path l d k ->
  last l = Some to.
Proof.
  induction 1.
   subst.
   rewrite H0.
   apply last_complete.
  assumption.
Qed.

Corollary path_nonempty : forall l d k,
  path l d k ->
  l <> nil.
Proof.
  intros.
  generalize (path_last H).
  destruct l; simpl; congruence.
Qed.

Lemma path_trivial : hierarchy ! to <> None -> path (to :: nil) to Class.Inheritance.Repeated.
Proof.
  econstructor.
  reflexivity.
  pattern (to :: nil) at 1.
  replace (to :: nil) with (nil ++ to :: nil) by reflexivity.
  reflexivity.
  unfold is_valid_repeated_subobject.
  destruct (hierarchy ! to); congruence.
Qed.
  

Lemma path_cons_repeated : forall from by l h,
  path (by :: l) from h ->
  path (by :: l) by Class.Inheritance.Repeated.
Proof.
  intros.
  generalize (path_path0 H).
  inversion 1.
   econstructor.
   reflexivity.
   eassumption.
   assumption.
  econstructor.
  reflexivity.
  eassumption.
  assumption.
Qed.

(** Subobject path concatenation (essential for casts)

[plus a b] concatenates two lists by confusing the last element of [a] with the first element of [b]. This is necessary for concatenating two non-virtual paths.
 *)

Function plus (a b : list ident) {struct b} : list ident :=
  match b with
    | nil => a
    | hb :: b' => 
      match last a with
        | None => hb :: b'
        | Some la => if peq la hb then a ++ b' else a ++ b
      end
  end.

Lemma plus_nil_left : forall a, plus nil a = a.
Proof.
  destruct a ; trivial.
Qed.

Lemma plus_cons : forall b, b <> nil -> forall a c,
  plus (a :: b) c = a :: plus b c.
Proof.
  intros.
  destruct c.
  simpl.
  trivial.
  Opaque last.  simpl.
  change (a :: b) with ((a :: nil) ++ b).
  rewrite (last_app_left H).
  case_eq (last b).
   intros.
   destruct (peq i0 i) ; trivial.
  intros.
  generalize (last_nonempty H).
  contradiction.
Qed. 

Transparent last.

Lemma plus_assoc : forall a b c,
  plus (plus a b) c = plus a (plus b c).
Proof.
  intros a b c.
  functional induction (plus b c) ; functional induction (plus a b) ; try reflexivity.
    assert (hb0 :: b'0 <> nil) by congruence.
    generalize (last_nonempty H).
    contradiction.
    assert (hb0 :: b'0 <> nil) by congruence.
    generalize (last_nonempty H).
    contradiction.
    assert (hb0 :: b'0 <> nil) by congruence.
    generalize (last_nonempty H).
    contradiction.
    simpl in e0.
    discriminate.
   clear e1.
   subst.
   destruct a.
   remember (hb0 :: b'0) as l.
   simpl.
   rewrite e0.
   destruct (peq hb hb).
    subst.
    reflexivity.
   congruence.
   assert (i :: a <> nil) by congruence.
   generalize (last_nonempty H).
   contradiction.
   clear e1 e3.
   subst.
   destruct b'0.
    rewrite <- app_nil_end.
    simpl in e0.
    f_equal.
    simpl.
    congruence.
   remember (i :: b'0) as l.
   assert (l <> nil) by congruence.
   clear i b'0 Heql.
   change ((hb0 :: l) ++ b') with (hb0 :: l ++ b').
   change (hb0 :: l) with ((hb0 :: nil) ++ l) in e0.
   rewrite (last_app_left H) in e0.
   simpl.
   rewrite (last_app_left H).
   rewrite e0.
   rewrite e2.
   destruct (peq hb hb) ; try congruence.
   destruct (peq hb0 hb0) ; try congruence.
   rewrite app_ass.
   reflexivity.
  clear e1 e3.
  subst.
  simpl.
  assert (hb0 :: b'0 <> nil) by congruence.
  rewrite (last_app_left H).
  rewrite e0.
  rewrite e2.
  destruct (peq hb hb) ; try congruence.
  destruct (peq la0 hb0) ; try congruence.
  rewrite app_ass.
  reflexivity.
 clear e1.
 remember (hb0 :: b'0) as l.
 destruct a.
  simpl.
  rewrite e0.
  destruct (peq la hb) ; try congruence.
  rewrite plus_nil_left.
  trivial.
 assert (i :: a <> nil) by congruence.
 generalize (last_nonempty H).
 contradiction.
 clear e1 e3.
 subst.
 destruct b'0.
  simpl in e0.
  rewrite <- app_nil_end.
  injection e0 ; intros ; subst.
  simpl.
  rewrite e2.
  destruct (peq la hb) ; try congruence.
  destruct (peq la la) ; try congruence.
 remember (i :: b'0) as l.
 assert (l <> nil) by congruence.
 clear i b'0 Heql.
 simpl.
 rewrite (last_app_left H).
 change (hb0 :: l) with ((hb0 :: nil) ++ l) in e0.
 rewrite (last_app_left H) in e0.
 rewrite e0.
 rewrite e2.
 destruct (peq la hb) ; try congruence.
 destruct (peq hb0 hb0) ; try congruence.
 rewrite app_ass.
 trivial.
assert (hb0 :: b'0 <> nil) by congruence.
simpl.
rewrite (last_app_left H).
rewrite e0.
rewrite e1.
rewrite e2.
rewrite e3.
rewrite app_ass.
simpl.
trivial.
Qed.

(** [concat kp1 kp2] concatenates two subobject paths. *)

Function concat (kp1 kp2 : Class.Inheritance.t * list ident) :
  Class.Inheritance.t * list ident :=
  let (k1, p1) := kp1 in
    let (k2, p2) := kp2 in
      match k2 with
        | Class.Inheritance.Shared => kp2
        | _ => (k1, plus p1 p2)
      end
. 

Lemma concat_assoc : forall kp1 kp2 kp3,
  concat (concat kp1 kp2) kp3 = concat kp1 (concat kp2 kp3).
Proof.
 unfold concat.
 destruct kp1.
 destruct kp2.
 destruct kp3.
 destruct t1.
  Focus 2.
   destruct t0 ; trivial.
 destruct t0.
 2 : trivial.
 f_equal.
 apply plus_assoc.
Qed.

Lemma concat_other : forall p,
  p <> nil ->
  forall q1 q2, q1 <> q2 ->
    forall h0 p0 h, concat (h0, p0) (h, p ++ q1) <> concat (h0, p0) (h, p ++ q2).
Proof.
  destruct h; simpl.
  unfold plus.
  destruct p.
   destruct H.
   trivial.
   simpl.
  destruct (last p0).
   destruct (peq i0 i).
    subst.
    intro.
    injection H1.
    intro.
    generalize (app_reg_l H2).
    intro.
    generalize (app_reg_l H3).
    assumption.
   intro.
   injection H1.
   intro.
   generalize (app_reg_l H2).
   injection 1.
   intro.
   generalize (app_reg_l H4).
   assumption.
  intro.
  injection H1; subst.
  intro.
  generalize (app_reg_l H2).
  assumption.
 intro.
 injection H1.
 intro.
 generalize (app_reg_l H2).
 assumption.
Qed.


End Path.

Lemma path2_concat : forall (a b : ident) k1 p1,
  path2 b p1 a k1 ->
  forall c k2 p2,
    path2 c p2 b k2 ->
    let (k, p) := concat (k1, p1) (k2, p2) in
      path2 c p a k
.
Proof.
  induction 1 ; simpl.
   inversion 1 ; subst.
   simpl.
   destruct (peq b b) ; try congruence.
  simpl.
  destruct (peq b b) ; try congruence.
  assumption.
  assumption.
  assumption.
 intros.
 generalize (IHpath2 _ _ _ H2).
 simpl.
 destruct k2.
  intros.
  assert (l <> nil). 
   generalize (path2_path H1).
   inversion 1.
    congruence.
   rewrite (plus_cons H4).
   econstructor.
   eassumption.
   eassumption.
   assumption.
  intros.
  eapply path_S_shared_2.
  eassumption.
  eassumption.
  assumption.
 destruct k2.
 intros.
  generalize (IHpath2 _ _ _ H2).
  simpl.
  intros.
  eapply path_S_shared_1.
  eassumption.
  eassumption.
  eassumption.

 intros.  
 generalize (IHpath2 _ _ _ H2).
 simpl.
 intros.
 eapply path_S_shared_2.
 eassumption.
 eassumption.
 assumption.

 intros.
 generalize (IHpath2 _ _ _ H2).
 simpl.
 case_eq (
 match k2 with
        | Class.Inheritance.Repeated => (Class.Inheritance.Shared, plus l p2)
        | Class.Inheritance.Shared => (k2, p2)
        end
 ).
 intros.
 destruct k2.
 injection H3 ; intros ; subst.
 eapply path_S_shared_2.
 eassumption.
 eassumption.
 assumption.
 injection H3 ; intros ; subst.
 eapply path_S_shared_2.
 eassumption.
 eassumption.
 assumption.
Qed.

Corollary path_concat : forall (a b : ident) k1 p1,
  path b p1 a k1 ->
  forall c k2 p2,
    path c p2 b k2 ->
    forall k p,
    (k, p) = concat (k1, p1) (k2, p2) ->
      path c p a k
.
Proof.
  intros.
  apply path2_path.
  generalize (path2_concat (path_path2 H) (path_path2 H0)).
  rewrite <- H1.
  tauto.
Qed.

 
Lemma path2_concat_recip : forall (a c : ident) k p,
  path2 c p a k ->
  (a = c /\ k = Class.Inheritance.Repeated) \/
  forall ka, hierarchy ! a = Some ka ->
  exists b, exists k1, exists k2, exists p2,
    In (k1, b) (Class.super ka) /\
    path2 c p2 b k2 /\
    (k, p) = concat (k1, match k1 with
                 | Class.Inheritance.Repeated => a :: b :: nil
                 | Class.Inheritance.Shared => b :: nil
               end) (k2, p2).
Proof.
 inversion 1 ; subst ; auto ; right ; intros.
 replace ka with cfrom in * by congruence.
 exists interm.
 exists Class.Inheritance.Repeated.
 exists Class.Inheritance.Repeated.
 exists (l).
 split.
  assumption.
 split.
  assumption.
 simpl.
 f_equal.
 generalize (path2_path H2).
 inversion 1.
  subst.
  simpl.
  destruct (peq interm interm) ; try congruence.
  trivial.
 
 replace ka with cfrom in * by congruence.
 esplit.
 esplit.
 esplit.
 esplit.
 split.
 eassumption.
 split.
 eassumption.
 simpl.
 destruct h.
  unfold plus.
  generalize (path2_path H2).
  inversion 1.
   subst p.
   simpl.
   destruct (peq interm interm) ; try congruence.
   trivial.

 replace ka with cfrom in * by congruence.
 esplit.
 esplit.
 esplit.
 esplit.
 split.
 eassumption.
 split.
 eassumption.
 simpl.
 trivial.
Qed.

Corollary path_concat_recip : forall (a c : ident) k p,
  path c p a k ->
  (a = c /\ k = Class.Inheritance.Repeated) \/
  forall ka, hierarchy ! a = Some ka ->
  exists b, exists k1, exists k2, exists p2,
    In (k1, b) (Class.super ka) /\
    path c p2 b k2 /\
    (k, p) = concat (k1, match k1 with
                 | Class.Inheritance.Repeated => a :: b :: nil
                 | Class.Inheritance.Shared => b :: nil
               end) (k2, p2).
Proof.
  intros.
  destruct (path2_concat_recip (path_path2 H)).
   tauto.
  right.
  intros.
destruct (H0 _ H1).
destruct H2.
destruct H2.
destruct H2.
destruct H2.
destruct H3.
generalize (path2_path H3).
intros.
repeat esplit ; eauto.
Qed.


Lemma path_elem : forall b kb,
  hierarchy ! b = Some kb ->
  forall k a, In (k, a) (Class.super kb) ->
    hierarchy ! a <> None ->
    path a (match k with 
               | Class.Inheritance.Repeated => (b :: a :: nil)
               | Class.Inheritance.Shared => a :: nil
             end) b k.
Proof.
 intros.
 destruct k.
 econstructor.
  reflexivity.
  change (b :: a :: nil) with ((b :: nil) ++ a :: nil).
  reflexivity.
  simpl.
  rewrite H.
  destruct (In_dec super_eq_dec (Class.Inheritance.Repeated, a) (Class.super kb)) ; try contradiction.
  case_eq (hierarchy ! a) ; congruence.
 econstructor.
 eleft.
  eassumption.
  eassumption.
 eleft.
 reflexivity.
 pattern (a :: nil) at 1.
  replace (a :: nil) with (nil ++ a :: nil) by reflexivity.
 reflexivity.
 simpl.
 case_eq (hierarchy ! a)  ; congruence.
Qed. 

Lemma path_defined_from : forall from to via by,
  path to via from by -> hierarchy ! from <> None.
Proof.
 intros.
 generalize (path_path2 H).
 inversion 1 ; try congruence.
Qed.

Lemma path_defined_to : forall from to via by,
  path to via from by -> hierarchy ! to <> None.
Proof.
  intros.
  generalize (path_path0 H).
  inversion 1 ; subst.
  eapply is_valid_repeated_subobject_defined.
  eassumption.
  rewrite H2.
  apply in_or_app.
  simpl ; auto.
  eapply is_valid_repeated_subobject_defined.
  eassumption.
  rewrite H3.
  apply in_or_app.
  simpl ; auto.
Qed.
   
Lemma path_eq_dec : forall p1 p2 : Class.Inheritance.t * list ident,
  {p1 = p2} + {p1 <> p2}.
Proof.
  repeat decide equality.
Qed.

Lemma concat_trivial_left : forall to via from by,
  path to via from by ->
  concat (Class.Inheritance.Repeated, from :: nil) (by, via) = (by, via).
Proof.
  inversion 1; subst; simpl; try trivial.
   destruct (peq from from); congruence.
 Qed.

Lemma concat_trivial_right : forall to via from by,
  path to via from by ->
  concat (by, via) (Class.Inheritance.Repeated, to :: nil) = (by, via).
Proof.
  intros.
  unfold concat, plus.
  rewrite (path_last H).
  destruct (peq to to); try congruence.
  rewrite <- app_nil_end.
  trivial.
Qed.

Lemma last_concat : forall l1 to, last l1 = Some to ->
  forall h l2, (h, l1 ++ l2) = concat (h, l1) (Class.Inheritance.Repeated, to :: l2).
Proof.
  simpl.
  intros until 1.
  rewrite H.
  destruct (peq to to).
   trivial.
  congruence.
Qed.

Lemma path_is_virtual_base_of : forall to via from by,
  path to via from by ->
  forall base, is_virtual_base_of base to ->
    is_virtual_base_of base from.
Proof.
induction 1.
 revert H1 from lf lt to H H0.
 functional induction (is_valid_repeated_subobject via); intros; try discriminate; subst.
  injection H; intros; subst.
  destruct lt; simpl in H0.
   abstract congruence.
  destruct lt; simpl in H0; discriminate.
 injection H; intros; subst.
 destruct lt; simpl in H0.
  discriminate.
 injection H0; intros; subst.  
 eright.
 eassumption.
 eassumption.
 eauto.
eauto using is_virtual_base_of_trans.
Qed.


Lemma plus_last : forall p2, p2 <> nil -> forall p1, last (plus p1 p2) = last p2.
Proof.
  intros.
  functional induction (plus p1 p2).
   congruence.
  trivial.
  clear e1; subst.
  destruct (last_correct e0).
  subst.
  rewrite app_ass.
  rewrite last_app_left.
  reflexivity.
  simpl; congruence.
  rewrite last_app_left.
  trivial.
  congruence.
Qed.

Lemma concat_last : forall p2, p2 <> nil -> forall h1 p1 h2 h p, (h, p) = concat (h1, p1) (h2, p2) ->
  last p = last p2.
Proof.
  intros.
  functional inversion H0; subst.
   congruence.
  eauto using plus_last.
Qed.    

End Paths.


(** ** Array paths (POPL 2011 Section 3.2) *)

Section Array_path.

Definition array_path := (list (Z * (Class.Inheritance.t * list ident) * (FieldSignature.t A))).

Variable hierarchy : PTree.t (Class.t A).

  Inductive valid_array_path : forall 
    (to : ident) (to_n : Z) (from : ident) (from_n : Z) (via : array_path), Prop :=
  | valid_array_path_nil : forall c to_n from_n,
    0 <= to_n ->
    to_n <= from_n ->
    valid_array_path c to_n c from_n nil
  | valid_array_path_cons : forall to to_n by through from from_n p h l fs via by_n,
    0 <= p ->
    p < from_n ->
    path hierarchy through l from h ->
    forall hthrough, hierarchy ! through = Some hthrough ->
      In fs (Class.fields hthrough) ->
      FieldSignature.type fs = FieldSignature.Struct by by_n  ->
      valid_array_path to to_n by (Zpos by_n) via ->
      valid_array_path to to_n from from_n ((p, (h, l), fs) :: via)
      .

  Lemma valid_array_path_widening : forall to to_n from from_n via,
    valid_array_path to to_n from from_n via ->
    forall to_n' from_n',
      to_n' <= to_n ->
      from_n <= from_n' ->
      0 <= to_n' ->
      valid_array_path to to_n' from from_n' via.
  Proof.
    induction 1.
     intros.
     constructor.
     assumption.
     omega.
    intros.
    econstructor.
    assumption.
     omega.
     eassumption.
     eassumption.
     assumption.
     eassumption.
     eapply IHvalid_array_path.
     assumption.
     omega.
     assumption.
  Qed.

  Lemma valid_array_path_nonnegative_to : forall by by_n from from_n via1,
    valid_array_path by by_n from from_n via1 ->
    0 <= by_n.
  Proof.
    induction 1 ; omega.
  Qed.

  Lemma valid_array_path_nonnegative_from :  forall by by_n from from_n via1,
    valid_array_path by by_n from from_n via1 ->
    0 <= from_n.
  Proof.
    induction 1 ; omega.
  Qed.

  Lemma valid_array_path_concat : forall by by_n from from_n via1,
    valid_array_path by by_n from from_n via1 ->
    forall to to_n via2,
      valid_array_path to to_n by by_n via2 ->
      valid_array_path to to_n from from_n (via1 ++ via2)
      .
  Proof.
    induction 1 ; simpl.
     intros.
     eapply valid_array_path_widening.
     eassumption.
     omega.
     assumption.
     generalize (valid_array_path_nonnegative_to H1).
     omega.
    intros.
    econstructor.
    assumption.
    assumption.
    eassumption.
    eassumption.
    assumption.
    eassumption.
    eauto.
  Qed.

  Corollary valid_array_path_concat_widening : forall by by_n from from_n via1,
    valid_array_path by by_n from from_n via1 ->
    forall by_n', by_n' <= by_n ->
      forall to to_n via2,
      valid_array_path to to_n by by_n' via2 ->
      valid_array_path to to_n from from_n (via1 ++ via2)
      .
  Proof.
    intros.
    eapply valid_array_path_concat.
     eassumption.
     eapply valid_array_path_widening.
     eassumption.
     omega.
     assumption.
     eauto using valid_array_path_nonnegative_to.
   Qed.

  Lemma valid_array_path_concat_recip : forall via1 to to_n via2 from from_n,
    valid_array_path to to_n from from_n (via1 ++ via2) ->
    exists by, exists by_n,
      valid_array_path by by_n from from_n via1 /\
      valid_array_path to to_n by by_n via2
      .
  Proof.
    induction via1 ; simpl.
     intros.
     esplit.
     esplit.
     split.
     econstructor.
     2 : eapply Zle_refl.
     eauto using valid_array_path_nonnegative_from.
     assumption.
    inversion 1 ; subst.
    generalize (IHvia1 _ _ _ _ _ H12).
    destruct 1.
    destruct H0.
    destruct H0.
    esplit ; esplit ; split.
    econstructor ; eauto.
    eassumption.
  Qed.

  Lemma valid_array_path_last : forall by1 by_n1 from from_n via,
    valid_array_path by1 by_n1 from from_n via ->
    forall by2 by_n2, 
      valid_array_path by2 by_n2 from from_n via ->
      by1 = by2.
  Proof.
    induction 1; inversion 1; subst; auto.
    apply IHvalid_array_path with by_n2.
    congruence.
  Qed.

 Lemma array_path_eq_dec : forall l1 l2 : array_path,
   {l1 = l2} + {l1 <> l2}.
 Proof. 
   intros. 
   apply list_eq_dec.
    apply prod_eq_dec.
     apply prod_eq_dec.
      apply Z_eq_dec.
     apply prod_eq_dec.
      apply Class.Inheritance.eq_dec.
     apply list_eq_dec.
     apply peq.
    apply FieldSignature.eq_dec.
 Qed.

Lemma maximize_array_path :
  forall from from_n ar to to_n, valid_array_path to to_n from from_n ar ->
      exists to_n', valid_array_path to to_n' from from_n ar  /\ to_n <= to_n' /\
        match last ar with
          | Some (pair (pair _ _) fs) =>
            exists n' : positive,
              to_n' = Zpos n' /\
              FieldSignature.type fs = FieldSignature.Struct to n'
          | None => to_n' = from_n /\ to = from
        end.
Proof.
  intros.
  revert H.
  rewrite <- (rev_involutive ar).
  destruct (rev ar); simpl.
   inversion 1; subst.
   esplit.
   split.
   econstructor.
   3 : eauto.
   abstract omega.
   abstract omega.
  rewrite last_complete.
  destruct p.
  destruct p.
  intro.
  generalize (valid_array_path_concat_recip H).
  intros; invall; subst.
  inversion H2; subst.
  inversion H16; subst.
  esplit.
  split.
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
  Focus 3.
  split.
  Focus 2.
  esplit.
  split.
  2 : eassumption.
  reflexivity.
  abstract omega.
  abstract omega.
  assumption.
Qed.  


(** ** Generalized subobjects (POPL 2011 Section 3.2) are called "relative pointers" because they are pointers to a suboject relatively to a structure array *)
   
 Inductive valid_relative_pointer (afrom: ident) (zfrom: Z) (apath: array_path) (ato: ident) (i : Z) (h : Class.Inheritance.t) (p : list ident) (pto : ident) : Prop :=
   | valid_relative_pointer_intro
     (zto : Z) (_ : valid_array_path ato zto afrom zfrom apath)
     (_ : 0 <= i) (_ : i < zto)
     (_ : path hierarchy pto p ato h)
.

Lemma valid_relative_pointer_last : forall afrom zfrom apath ato1 i h p pto1,
  valid_relative_pointer afrom zfrom apath ato1 i h p pto1 ->
  forall ato2 pto2, valid_relative_pointer afrom zfrom apath ato2 i h p pto2 -> ato1 = ato2 /\ pto1 = pto2.
Proof.
 inversion 1; subst.
 inversion 1; subst.
 asplit.
  eauto using valid_array_path_last.
 subst.
 generalize (path_last H8).
 generalize (path_last H3).
 congruence.
Qed.
 
(* An alternate definition of relative pointers *)

 End Array_path.


Section Relative_pointer_alt.


(** * Alternate definition for generalized subobjects (relative to a given structure array) (from POPL 2011) *)

 Inductive relative_pointer_alt: Type :=
   | relative_pointer_alt_intro
     (i : Z) (p : Class.Inheritance.t * list ident)
     (f : option (FieldSignature.t A * array_path * Z * (Class.Inheritance.t * list ident)))
     .
     
 Function relative_pointer_alt_of_relative_pointer (a : array_path) (i : Z) (p : Class.Inheritance.t * list ident) {struct a} : relative_pointer_alt :=
   match a with
     | nil => relative_pointer_alt_intro i p None
     | (i', p', f') :: a' => relative_pointer_alt_intro i' p' (Some (f', a', i, p))
   end.
 
 Function relative_pointer_of_relative_pointer_alt (rpa : relative_pointer_alt) : (array_path * Z * (Class.Inheritance.t * list ident)) :=
   match rpa with
     | relative_pointer_alt_intro i p None => (nil, i, p)
     | relative_pointer_alt_intro i' p' (Some (f', a, i, p)) => ((i', p', f') :: a, i, p)
   end.

 Fact relative_pointer_alt_to_default_to_alt : forall rpa a i p,
   relative_pointer_of_relative_pointer_alt rpa = (a, i, p) ->
   relative_pointer_alt_of_relative_pointer a i p = rpa.
 Proof.
   intros until 1.
   revert H.
   functional inversion 1; subst; simpl; trivial.
 Qed.

 Fact relative_pointer_default_to_alt_to_default: forall a i p,
   relative_pointer_of_relative_pointer_alt (relative_pointer_alt_of_relative_pointer a i p) = (a, i, p).
 Proof.
   intros.
   functional induction (relative_pointer_alt_of_relative_pointer a i p); subst; simpl; trivial.
 Qed.

 Function relative_pointer_alt_length (rpa : relative_pointer_alt) : nat :=
   match rpa with
     | relative_pointer_alt_intro _ _ None => O
     | relative_pointer_alt_intro _ _ (Some (_, a, _, _)) => S (length a)
   end.

 Fact relative_pointer_alt_length_correct: forall a i p,
   relative_pointer_alt_length (relative_pointer_alt_of_relative_pointer a i p) = length a.
 Proof.
   intros.
   functional induction (relative_pointer_alt_of_relative_pointer a i p); simpl; trivial.
 Qed.


 Variable hierarchy : PTree.t (Class.t A).

 Inductive valid_relative_pointer_alt (afrom : ident) (zfrom : Z) (ato : ident) (pto : ident) : relative_pointer_alt -> Prop :=
 | valid_relative_pointer_alt_intro : forall i',
   0 <= i' -> i' < zfrom -> forall h' p' through,
     path hierarchy through p' afrom h' ->
     forall f',
       match f' with
         | None => ato = afrom /\ pto = through
         | Some (f, a, i, (h, p)) =>
           exists cthrough, hierarchy ! through = Some cthrough /\
             In f (Class.fields cthrough) /\
             exists bfrom, exists bn,
               FieldSignature.type f = FieldSignature.Struct bfrom bn /\
               valid_relative_pointer hierarchy bfrom (Zpos bn) a ato i h p pto           
       end ->
       valid_relative_pointer_alt afrom zfrom ato pto (relative_pointer_alt_intro i' (h', p') f')
.

 Fact valid_relative_pointer_alt_valid_relative_pointer : forall p afrom zfrom ato pto,
   valid_relative_pointer_alt afrom zfrom ato pto p ->
   forall a i h' p', relative_pointer_of_relative_pointer_alt p = (a, i, (h', p')) ->
     valid_relative_pointer hierarchy afrom zfrom a ato i h' p' pto
.
Proof.
  inversion 1; simpl.
  destruct f'.
   destruct p0.
   destruct p0.
   destruct p0.
   injection 1 ; intros ; subst.
   invall.
   inversion H8 ; subst.
   econstructor.
    econstructor.
    assumption.
    assumption.
    eassumption.
    eassumption.
    assumption.
    eassumption.
    eassumption.
   assumption.
   assumption.
   assumption.
  injection 1 ; intros ; subst.
  invall ; subst.
  assert (i + 1 <= zfrom) by omega.
  econstructor.
   econstructor.
   2 : eassumption.
   omega.
   assumption.
   omega.
   assumption.
 Qed.

 Fact valid_relative_pointer_valid_relative_pointer_alt : forall afrom zfrom a ato i h' p' pto,
   valid_relative_pointer hierarchy afrom zfrom a ato i h' p' pto ->
   valid_relative_pointer_alt afrom zfrom ato pto (relative_pointer_alt_of_relative_pointer a  i (h', p')).
 Proof.
   inversion 1 ; intros ; subst.
   inversion H0 ; subst ; simpl.
    econstructor.
    assumption.
    omega.
    eassumption.
    tauto.
   econstructor.
   assumption.
   assumption.
   eassumption.
   esplit.
   split.
   eassumption.
   split.
   assumption.
   esplit.
   esplit.
   split.
   eassumption.
   econstructor.
   eassumption.
   assumption.
   assumption.
   assumption.
 Qed.

End Relative_pointer_alt.


End Subobjects.

(** ** Scalar values *)

 Module Value.

   (** A pointer either is null, or designates a generalized subobject within a full structure array created by "new" or by a static or automatic variable. *)

   (** [is_some (last l)] allows the computation of the last element of the base class subobject designated by the pointer. This last element will give the actual type of the pointer. Null pointers must also give their type. *)

Section V.
  Variable A : ATOM.t.

  Inductive pointer : Type :=
  | null (_ : ident)
  | subobject (array : ident) (arraypath : array_path A)
    (index : Z) (inhkind : Class.Inheritance.t) (l : list ident) (_ : is_some (last l))
    .
  Implicit Arguments subobject [].

  Lemma pointer_eq_dec : forall p1 p2 : pointer, {p1 = p2} + {p1 <> p2}.
  Proof.
    destruct p1 ; destruct p2 ; try (right ; congruence).
    destruct (peq i i0) ; (right ; congruence) || (left ; congruence).
    destruct (peq array array0) ; try (right ; congruence).
    subst.
    destruct (array_path_eq_dec arraypath arraypath0) ; try (right ; congruence).
    subst.
    destruct (Z_eq_dec index index0) ; try (right ; congruence).
    subst.
    destruct (Class.Inheritance.eq_dec inhkind inhkind0) ; try (right ; congruence) .
    subst.
    destruct (list_eq_dec peq l l0) ; try (right ; congruence).
    subst.
    left.
    rewrite (is_some_eq i i0).
    trivial.
  Qed.

  Inductive t : Type :=
  | atom (ty : ATOM.ty A) (_ : ATOM.val ty)
  | ptr (_ : pointer)
    .

  Lemma eq_dec : forall a b : t, {a = b} + {a <> b}.
  Proof.
    intros.
    destruct a; destruct b; try (right; intro; subst; discriminate).
    destruct (ATOM.ty_eq_dec ty ty0).
     subst.
     destruct (ATOM.val_eq_dec v v0).
      left; congruence.
     right; intro.
     injection H.
     intros.
     generalize (inj_pair2_eq_dec _ (@ATOM.ty_eq_dec A) _ _ _ _ H0).
     assumption.
    right; congruence.
    destruct (pointer_eq_dec p p0).
     left; congruence.
    right; congruence.  
   Qed.

   Function type_of (v : t) : Typ.t A :=
     match v with
       | atom a _ => Typ.atom a
       | ptr (null c) => Typ.class c
       | ptr (subobject _ _ _ _ l h) =>
         let (c, _) := is_some_constr h in Typ.class c
  end.

Function weaktype_of (v : t) : WeakTyp.t A :=
  match v with
    | atom a _ => WeakTyp.atom a
    | ptr _ => WeakTyp.object
  end.

Lemma weaktype_of_type_of_value : forall v,
  WeakTyp.of_type (type_of v) = weaktype_of v.
Proof.
  destruct v ; simpl ; try auto.
  destruct p ; simpl ; try auto.
  destruct (is_some_constr i) ; simpl ; try congruence.
Qed. 

Function weaktype_of_option (v : option t) : option (WeakTyp.t A) :=
  match v with
    | None => None
    | Some v' => Some (weaktype_of v')
  end.

Function check_weak (u : WeakTyp.t A) (v : t) {struct v} : option t :=
  match v with
    | atom a _ => 
      match u with
        | WeakTyp.atom a' => if ATOM.ty_eq_dec a a' then Some v else None
        | _ => None
      end
    | ptr _ =>
      match u with
        | WeakTyp.object => Some v
        | _ => None
      end
  end.


Lemma check_weak_some : forall u v v',
  check_weak u v = Some v' -> v' = v.
Proof.
  functional inversion 1; simpl; congruence.
Qed.

Lemma weaktype_of_check_weak_2 : forall u v v',
  check_weak u v = Some v' ->
  weaktype_of v = u.
Proof.
  functional inversion 1.
   clear H5.
   subst ; simpl ; trivial.
  subst; simpl; trivial.
Qed.

Corollary weaktype_of_check_weak : forall u v v',
  check_weak u v = Some v' ->
  weaktype_of v' = u.
Proof.
 intros.
 replace v' with v by (symmetry ; eauto using check_weak_some).
 eauto using weaktype_of_check_weak_2.
Qed. 
  

Function load_value_weak (v : option t) (ty : WeakTyp.t A) : option t :=
  match v with
    | None => None
    | Some v' => check_weak ty v'
  end.

Lemma weaktype_of_load_value_weak : forall v ty v',
  load_value_weak v ty = Some v' ->
  weaktype_of v' = ty.
Proof.
  destruct v ; simpl.
  intros ; eauto using weaktype_of_check_weak.
  congruence.
Qed.

Lemma load_value_weak_some : forall v ty v',
  load_value_weak (Some v) ty = Some v' ->
  v = v'.
Proof.
  simpl.
  intros.
  generalize (check_weak_some H).
  congruence.
Qed.  

Function check (u : Typ.t A) (v : t) {struct v} : option t :=
  match v with
    | atom a _ => 
      match u with
        | Typ.atom a' => if ATOM.ty_eq_dec a a' then Some v else None
        | _ => None
      end
    | ptr (null c) =>
      match u with
        | Typ.class c' =>
          if peq c c' then Some v else None
        | _ => None
      end
    | ptr (subobject _ _ _ _ l h) =>
      let (c, _) := is_some_constr h in
        match u with
          | Typ.class c' =>
            if peq c c' then Some v else None
          | _ => None
        end
  end. 

Lemma check_some : forall u v v',
  check u v = Some v' -> v' = v.
Proof.
  functional inversion 1 ; simpl ; congruence.
Qed.

Lemma type_of_check : forall u v v',
  check u v = Some v' ->
  type_of v' = u.
Proof.
 functional inversion 1.
  clear H5.
  subst; simpl; trivial.
  clear H5.
  subst; simpl; trivial.
  clear H6.
  subst.
  simpl.
  rewrite H2.
  trivial.
Qed.

Corollary type_of_check_2 : forall u v v',
  check u v = Some v' ->
  type_of v = u.
Proof.
  intros.
  replace v with v' by eauto using check_some.
  eauto using type_of_check.
Qed.

Function load_value (v : option t) (ty : Typ.t A) : option t :=
  match v with
    | None => None
    | Some v' => check ty v'
  end.

Lemma type_of_load_value : forall v ty v',
  load_value v ty = Some v' ->
  type_of v' = ty.
Proof.
  destruct v ; simpl.
  intros ; eauto using type_of_check.
  congruence.
Qed.

Lemma load_value_some : forall v ty v',
  load_value (Some v) ty = Some v' ->
  v = v'.
Proof.
  simpl.
  intros.
  generalize (check_some H).
  congruence.
Qed.

End V.
Implicit Arguments atom [A].
Implicit Arguments subobject [A].
End Value.

(** ** Object operations (field access, object creation) *)

Section Find_field.
Variable A : ATOM.t.

Definition field_key := (positive * array_path A * Z * (Class.Inheritance.t * list ident) * FieldSignature.t A)%type.

Lemma cfield_dec : forall a b : field_key,
  {a = b} + {a <> b}.
Proof.
  intros.
  apply prod_eq_dec.
   apply prod_eq_dec.
    apply prod_eq_dec.
     apply prod_eq_dec.
      apply peq.
     apply array_path_eq_dec.
    apply Z_eq_dec.
   apply prod_eq_dec.
    apply Class.Inheritance.eq_dec.
   apply list_eq_dec.
   apply peq.
  apply FieldSignature.eq_dec.
Qed.

Definition find_field f := List.find (fun n : field_key * Value.t A => let (a, _) := n in if cfield_dec a f then true else false).

  Function update_field (f : field_key) (v : Value.t A) (l : list (field_key * Value.t A)) {struct l} : 
    list (field_key * Value.t A) :=
    match l with
      | nil => (f, v) :: nil
      | a :: q =>
        let (i, _) := a in
          if cfield_dec i f then (i, v) :: q else a :: update_field f v q
    end.

  Lemma find_update_field_same : forall f v l,
    find_field f (update_field f v l) = Some (f, v).
  Proof.
    intros.
    functional induction (update_field f v l) ; simpl.
     destruct (cfield_dec f f) ; congruence.
    rewrite e1.
    congruence.
    rewrite e1.
    assumption.
  Qed.

  Lemma find_update_field_other : forall f f',
    f <> f' ->
    forall l v,
      find_field f' (update_field f v l) = find_field f' l.
  Proof.    
    intros until v.
    revert f' H.
    functional induction (update_field f v l); simpl.
     intros.
     destruct (cfield_dec f f') ; congruence.
    intros.
    destruct (cfield_dec i f') ; congruence.
    intros.
    destruct (cfield_dec i f'); try congruence.
    eauto.
  Qed.

  Function remove_field (f : field_key) (l : list (field_key * Value.t A)) {struct l} : 
    list (field_key * Value.t A) :=
    match l with
      | nil => nil
      | a :: q =>
        let (i, _) := a in
          if cfield_dec i f then remove_field f q else a :: remove_field f q
    end.

  Lemma find_remove_field_same : forall f l,
    find_field f (remove_field f l) = None.
  Proof.
    intros.
    functional induction (remove_field f l) ; simpl; trivial.
    rewrite e1.
    assumption.
  Qed.

  Lemma find_remove_field_other : forall f f',
    f <> f' ->
    forall l,
      find_field f' (remove_field f l) = find_field f' l.
  Proof.    
    intros until 1.
    intro l.
    revert f' H.
    functional induction (remove_field f l); simpl; trivial;
    intros;
    destruct (cfield_dec i f') ; try congruence; eauto.
  Qed.


End Find_field.

Module Object.
  Section O.
     
     Record t : Type := make {
(*       index : positive; *)
       class : ident;
       arraysize : Z
(*       fields : list (field_key A * Value.t A) *)
     }.

(** [new index ci size] creates a new array of [size] cells of type [ci]. [index] is the future identifier of the array within the "heap". *)

     Definition new (* index : ident *) (ci : ident) (size : Z) (* c : Class.t *) :=
       make (* index *) ci size (* nil *) .

 End O.

End Object.

Section Eq_dec.

Variable A : ATOM.t.

Lemma relative_pointer_eq_dec : forall p q :
  (array_path A * Z * (Class.Inheritance.t * list ident)),
{p = q} + {p <> q}.
Proof.
  apply prod_eq_dec.
   apply prod_eq_dec.
    apply array_path_eq_dec.
   exact Z_eq_dec.
  apply path_eq_dec.
Qed.


Lemma pointer_eq_dec : forall p q :
(ident * (array_path A * Z * (Class.Inheritance.t * list ident))),
{p = q} + {p <> q}.
Proof.
  apply prod_eq_dec.
   exact peq.
  exact relative_pointer_eq_dec.
Qed.

End Eq_dec.


Section Valid_pointer.

Variable A : ATOM.t.
Variables  (hierarchy : PTree.t (Class.t A)).

  Section Valid_ptr.
    Variable (heap : PTree.t Object.t).

(** A pointer is valid if, and only if, it is either null, or a valid relative pointer into an existing object of the heap *)

  Inductive valid_pointer : Value.pointer A -> Prop :=
  | valud_pointer_null : forall id,
    hierarchy ! id <> None ->
    valid_pointer (Value.null A id)
  | valid_pointer_subobject : forall id o,
    PTree.get id (heap (* globals *)) = Some o ->
    (* Object.index o = id -> *)
    forall ap through z h p to, 
      valid_relative_pointer hierarchy (Object.class o) (Object.arraysize o) ap through z h p to ->
      forall hp,
        valid_pointer (Value.subobject id ap z h p hp)
.


   Inductive pointer_array_size : Value.pointer A -> Z -> Prop :=
   | pointer_array_size_nil : forall r o sz z h p hp,
     (heap) ! r = Some o ->
     sz = Object.arraysize o ->
     pointer_array_size (Value.subobject r nil z h p hp) sz
   | pointer_array_size_cons : forall r ap apf kf cf f z h p hp psz,
     ap = apf ++ (kf, f) :: nil ->
     FieldSignature.type f = FieldSignature.Struct cf psz ->
     pointer_array_size (Value.subobject r ap z h p hp) (Zpos psz)
     .

(** Subscripting *)

   Function array_index (p : Value.pointer A) (i : Z) : Value.pointer A :=
     match p with         
       | Value.subobject ide ap z h p0 hp =>
         (Value.subobject ide ap (z + i) h p0 hp)
       | _ => p
     end.

(** A pointer is complete if, and only if, it points to a most-derived object. In this case, such an object is some cell of some array. *)

   Inductive complete_pointer : Value.pointer A -> Prop :=
   | complete_pointer_intro : forall r ap z ci hp,
     complete_pointer (Value.subobject r ap z Class.Inheritance.Repeated (ci :: nil) hp)
       .

   Lemma array_index_complete : forall p,
     complete_pointer p ->
     forall i, complete_pointer (array_index p i).
   Proof.
     inversion 1 ; subst.
     simpl.
     constructor.
   Qed.

(** [pointer_array_size he p n] holds if, and only if, pointer [p] points to an array of [n] cells (regardless of the base class subobject ultimately pointed to) *)


   Lemma array_index_valid : forall r ap z h p sp,
     valid_pointer (Value.subobject r ap z h p sp) ->
     complete_pointer (Value.subobject r ap z h p sp) ->
     forall sz, pointer_array_size (Value.subobject r ap z h p sp) sz ->
       forall j, 0 <= (z + j) -> z + j < sz ->
       valid_pointer (array_index (Value.subobject r ap z h p sp) j)
       .
   Proof.
     inversion 1 ; subst ; simpl in *.
     inversion H6; subst; simpl in *.
     inversion 1 ; subst ; simpl in *.
     inversion 1 ; subst ; simpl in *.
     (* cas racine *)
      replace o0 with o in * by congruence.
      inversion H0 ; subst ; simpl in *.
      intros.
      econstructor.
      eassumption.
      econstructor.
      econstructor.
      4 : eassumption.
      omega.
      omega.
      assumption.
      eassumption.
    (* cas champ *)
    generalize (valid_array_path_concat_recip H0).
    destruct 1.
    destruct H8.
    destruct H8.
    inversion H9 ; subst ; simpl in *.
    inversion H24 ; subst ; simpl in *.
    intros.
    econstructor.
    eassumption.
    econstructor.
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
    4 : eassumption.
    omega.
    replace psz with by_n by congruence.
    omega.
    assumption.
    eassumption.
  Qed.          

End Valid_ptr.

Lemma valid_pointer_preserve : forall obj heap heap', heap' ! obj = heap ! obj -> forall ar i h p hp, valid_pointer heap (Value.subobject obj ar i h p hp) -> valid_pointer heap' (Value.subobject obj ar i h p hp).
Proof.
  inversion 2; subst.
  rewrite <- H in H3.
  econstructor; eauto.
Qed.


End Valid_pointer.


Module Globals.
  Section G.
    Variable A : ATOM.t.

(** Global abstract memory model: all objects created in the free store, or as automatic storage, are stored in a single "heap". *)

  Record t : Type := make {
    heap : PTree.t (Object.t);
    next_object : positive;
    field_values: list (field_key A * Value.t A)
  }.     

  Definition new (h : t) (ci : ident) (arraysize : Z)  :=
    ((next_object h), make (PTree.set (next_object h) (Object.new ci arraysize) (heap h)) (Psucc (next_object h)) (field_values h)).

  Definition remove (h : t) (obj : positive) : t :=
    make (PTree.remove obj (heap h)) (next_object h) (field_values h).

  Definition empty :=
    make (PTree.empty (Object.t )) xH nil.

  Definition update (h : t) (l : list (field_key A * Value.t A)) :=
    make (heap h) (next_object h) l
    .

(** A heap is consistent ("valid") if, and only if any index beyond the "next object" is unassigned. *)

  Record valid (h : t) : Prop := valid_intro {
    valid_none : forall i,
      Ple (next_object h) i -> (heap h) ! i = None
      
(*    valid_index : forall i o,
      (heap h) ! i = Some o ->
      Object.index o = i *)
  }.

(*
  Lemma valid_update : forall h,
    valid h ->
    forall r o, (heap h) ! r = Some o -> forall o',
      Object.index o' = Object.index o ->
      valid (update h r o')
      .
  Proof.
    inversion 1 ; subst.
    intros.
    constructor.
    unfold update.
    simpl.
    intros.
    generalize (valid_none0 _ H2).
    intros.
    rewrite PTree.gso.
    assumption.
    congruence.
   unfold update.
   simpl.
   intro i.
   destruct (peq r i).
    subst.
    rewrite PTree.gss.
    injection 1 ; intros ; subst.
    rewrite H1.
    auto.
   rewrite PTree.gso.
   auto.
   congruence.
  Qed.
*)

  Lemma valid_new : forall h,
    valid h ->
    forall ci sz r h',
      new h ci sz = (r, h') ->
      valid h'
      .
  Proof.
    inversion 1 ; subst.
    unfold new.
    destruct h.
    simpl in *.
    injection 1 ; intros ; subst.
    constructor ; simpl.
    intros.
    generalize (Plt_succ r).
    intros.
    generalize (Plt_Ple_trans _ _ _ H2 H1).
    intros.
    generalize (Plt_Ple _ _ H3).
    intros.
    rewrite PTree.gso.
    auto.
    intro.
    subst.
    exact (Plt_irrefl _ H3).
(*
   intro i.
   destruct (peq i r).
    subst.
    rewrite PTree.gss.
    unfold Object.new.
    injection 1 ; intros ; subst ; reflexivity.
   rewrite PTree.gso ; auto.
*)
  Qed.

  Lemma valid_empty : valid empty.
  Proof.
    unfold empty.
    constructor.
    intros.
    simpl.
    apply PTree.gempty.
(*
   simpl.
   intro.
   rewrite PTree.gempty.
   congruence.
*)
  Qed.

 
  Lemma valid_pointer_new : forall hierarchy he,
    valid he ->
    forall p,
    valid_pointer (A := A) hierarchy (heap he) p ->
    forall ci sz r h',
      new he ci sz = (r, h') ->
      valid_pointer hierarchy (heap h') p
      .
  Proof.
    intros.
    inversion H0 ; subst.
     constructor.
     assumption.
    unfold new in H1.
    injection H1 ; intros ; subst ; simpl in *.
    inversion H0 ; subst.
    replace o0 with o in * by abstract congruence.
    econstructor ; simpl.
     rewrite PTree.gso.
     eassumption.
     intro.
     generalize (valid_none H (Ple_refl _)).
     congruence.
     eassumption.
(*     econstructor.
     eassumption.
     assumption.
     assumption.
     eassumption. *)
   Qed.

   Lemma valid_pointer_new_recip : forall he,
     valid he ->
     forall ci sz r h',
       new he ci sz = (r, h') ->
       forall hierarchy (p : _ A) ,
       valid_pointer hierarchy (heap h') p ->
       (forall ap' z' h' p' hp', p <> Value.subobject r ap' z' h' p' hp') ->
       valid_pointer hierarchy (heap he) p
       .
   Proof.
     inversion 3 ; subst.
      intros.
      constructor.
      assumption.
     inversion H1; subst.
     unfold new in H0.
     injection H0 ; intros ; subst ; simpl in *.
     rewrite PTree.gso in H2.
     econstructor ; eauto.
     generalize (H7 ap z h p0 hp).
     congruence.
   Qed.

(*
  Lemma valid_pointer_update : forall he,
    forall hierarchy p,
      valid_pointer hierarchy he p ->
      forall r o, (heap he) ! r = Some o -> forall o',
        Object.index o' = Object.index o ->
        Object.class o' = Object.class o ->
        Object.arraysize o' = Object.arraysize o ->
        valid_pointer hierarchy  (update he r o') p
        .
  Proof.
    inversion 1; subst.
     intros; constructor; assumption.
    intros.
    destruct (peq r (Object.index o)).
     subst.
     replace o0 with o in * by congruence.
     econstructor; simpl.
      rewrite PTree.gss.
      reflexivity.
      congruence.
      rewrite H5.
      rewrite H4.
      eassumption.     
    econstructor; simpl.
    rewrite PTree.gso; eauto.
    trivial.
    eassumption.
  Qed.

  Lemma valid_pointer_update_recip : forall he,
    forall r o, (heap he) ! r = Some o -> forall o',
      Object.index o' = Object.index o ->
      Object.class o' = Object.class o ->
      Object.arraysize o' = Object.arraysize o ->
    forall hierarchy p,
      valid_pointer hierarchy (update he r o') p ->
      valid_pointer hierarchy he p.
  Proof.
    inversion 5; subst.
     intros; constructor; assumption.
    intros.
    simpl in *.
    destruct (peq r (Object.index o0)).
     subst.
     rewrite PTree.gss in H4.
     replace o0 with o' in * by congruence.
     econstructor; simpl.
      eassumption.
      auto.
      rewrite <- H1.
      rewrite <- H2.
      eassumption.     
    rewrite PTree.gso in H4; eauto.
    econstructor; simpl.
    eassumption.
    trivial.
    eassumption.
  Qed.
*)





(** [get_field] : each object has its own list of field values.
   Consider a field [(ci, fs)] where [ci] is the complete path to the generalized subobject (including path to the complete object) containing the field.
   - If the field is not scalar, then [get_field] returns the pointer to the field array within the considered subobject.
   - If the value is :
   -- undefined, then [get_field] returns nothing
   -- of the right type, then returns it
   -- of a wrong type, then returns nothing
*)
   
  Function get_field (fields : list (field_key A * Value.t A)) (f : field_key A) : option (Value.t A) :=
    match f with
      (obj, ap, n, (h, l), fs) =>
      match FieldSignature.type fs with
        | FieldSignature.Scalar ty =>
          match find_field f (fields) with
            | Some (_, v) => Value.check ty v
            | None => None
          end        
        | FieldSignature.Struct cl _ => Some (Value.ptr (Value.subobject (obj) (ap ++ (n, (h, l), fs) :: nil) 0 Class.Inheritance.Repeated _ (is_some_last_one_elem cl)))
      end
    end.

(*
  Lemma get_field_new : forall i ci sz ci' fs' ty,
    FieldSignature.type fs' = FieldSignature.Scalar ty ->
    get_field (new i ci sz) (ci', fs') = None.
  Proof.
    unfold get_field.
    destruct fs' ; simpl.
    destruct type ; try congruence.
    destruct ci'.
    destruct p.
    destruct p0.
    tauto.
  Qed.
*)

  Lemma get_field_type_scalar : forall o ci fs v,
    get_field o (ci, fs) = Some v ->
    forall t,
      FieldSignature.type fs = FieldSignature.Scalar t ->
      t = (Value.type_of v).
  Proof.
    functional inversion 1 ; subst.
    rewrite H4.
    injection 1 ; intros ; subst.
    symmetry.
    eauto using Value.type_of_check.
    intros ; congruence.
  Qed.

  Lemma get_field_type_struct : forall o ci fs v,
    get_field o (ci, fs) = Some v ->
    forall cl n, FieldSignature.type fs = FieldSignature.Struct cl n ->
      Value.type_of v = Typ.class cl.
  Proof.
    functional inversion 1 ; subst.
     intros ; congruence.
    rewrite H4.
    injection 1 ; intros ; subst.
    simpl.
    destruct (is_some_constr (x := Some cl0) (is_some_last_one_elem cl0)).
    congruence.
  Qed.

  Function put_field (fields : list (field_key A * Value.t A)) (cifs : field_key A) (v : Value.t A) : option (list (field_key A * Value.t A)) := 
    let (_, fs) := cifs in
      match FieldSignature.type fs with
        | FieldSignature.Scalar ty =>
          match Value.check ty v with
            | Some v' => Some (update_field cifs v' (fields ))
            | None => None
          end
        | _ => None
      end
      .

  Lemma put_field_type : forall o ci fs v o',
    put_field o (ci, fs) v = Some o' ->
    FieldSignature.type fs = FieldSignature.Scalar (Value.type_of v).
  Proof.
    intros.
    functional inversion H ; subst.
    rewrite H5.
    f_equal.
    symmetry.
    eauto using Value.type_of_check_2.
  Qed.

  Lemma get_put_field_other : forall o cifs' v o', put_field o cifs' v = Some o' ->
    forall cifs,
    cifs' <> cifs ->
    get_field o' cifs = get_field o cifs.
  Proof.
    unfold get_field, put_field.
    intros until o'.
    destruct cifs'.
    destruct cifs.
    revert H.
    destruct (FieldSignature.type t0) ; try congruence.
    case_eq (Value.check t2 v) ; try congruence.
    injection 2 ; intro ; subst ; simpl in *.
    intros until 1.
    destruct (FieldSignature.type t1) ; try congruence.
    rewrite (find_update_field_other H1).
    trivial.
  Qed.

  Lemma get_put_field_same : forall o ci0fs0 v o', put_field o ci0fs0 v = Some o' ->
    get_field o' ci0fs0 = Some v.
  Proof.
    unfold put_field, get_field.
    intros until o'.
    destruct ci0fs0.
    destruct (FieldSignature.type t0) ; try congruence.
    case_eq (Value.check t1 v) ; try congruence.
    injection 2 ; intro ; subst ; simpl in *.
    rewrite find_update_field_same.
    destruct p.
    destruct p.
    destruct p.
    destruct p0.
    generalize (Value.check_some H) ; congruence.
  Qed.

(*
  Lemma class_put_field : forall o cifs v o',
    put_field o cifs v = Some o' ->
    class o' = class o.
  Proof.
    functional inversion 1 ; subst ; trivial.
  Qed. 

  Lemma arraysize_put_field : forall o cifs v o',
    put_field o cifs v = Some o' ->
    arraysize o' = arraysize o.
  Proof.
    functional inversion 1 ; subst ; trivial.
  Qed.

  Lemma index_put_field : forall o cifs v o',
    put_field o cifs v = Some o' ->
    index o' = index o.
  Proof.
    functional inversion 1 ; subst ; trivial.
  Qed.
*)


(*
    Function get_field (he : t) (p : Value.pointer A) (f : (Class.Inheritance.t * list ident) * FieldSignature.t A) {struct p} : option (Value.t A) :=
      match p with
        | Value.null _ => None
        | Value.subobject i ap z h p hp =>
          match PTree.get i (heap he) with
            | Some o => 
              match f with
                | ((hf, pf), fs) => Object.get_field o (ap, z, concat (h, p) (hf, pf), fs)
              end
          | _ => None
        end
    end.

    Lemma get_field_valid : forall hierarchy he p (p_not_null : forall cn, p <> Value.null _ cn),
      valid_pointer hierarchy he p ->
      forall ci, Value.type_of (Value.ptr p) = Typ.class ci ->
        forall hf pf to, path hierarchy to pf ci hf ->
          forall c, hierarchy ! to = Some c ->
            forall fs, In fs (Class.fields c) ->
              forall cf zf, FieldSignature.type fs = FieldSignature.Struct cf zf ->
                hierarchy ! cf <> None ->
                exists p',
                  get_field he p ((hf, pf), fs) = Some (Value.ptr p') /\
                  valid_pointer hierarchy he p'
                  .
    Proof.
      inversion 2 ; subst.
       destruct (p_not_null id).
        trivial.
      inversion H2; subst.
      functional inversion 1 ; subst.
      clear h1 H14 H H2.
      generalize (path_last H5).
      intro.
      replace to with ci in * by congruence.
      intros.
      unfold get_field.
      rewrite H0.
      unfold Object.get_field.
      case_eq (concat (h, p0) (hf, pf)).
      intros until 1.
      rewrite H9.
      esplit.
      split.
      reflexivity.
      econstructor.
      eassumption.
      trivial.
      econstructor.
      eapply valid_array_path_concat.
      eassumption.
      econstructor.
      assumption.
      assumption.
      eapply path_concat.
      eassumption.
      eassumption.
      congruence.
      eassumption.
      assumption.
      eassumption.
      econstructor.
      2 : apply Zle_refl.
      compute ; congruence.
      omega.
      compute ; trivial.
      econstructor.
      reflexivity.
      replace (cf :: nil) with (nil ++ cf :: nil) by reflexivity.
      reflexivity.
      simpl.
      (* Need well-formed hierarchy !!! *)
      case_eq (hierarchy ! cf) ; congruence.
    Qed.
      

    Function put_field (he : t) (p : Value.pointer A) (f : (Class.Inheritance.t * list ident) * FieldSignature.t A) (v : Value.t A) {struct p} : option t  :=
      match p with
        | Value.null _ => None
        | Value.subobject i ap z h p hp =>
          match PTree.get i (heap he) with
            | Some o => 
              match f with
                | ((hf, pf), fs) => 
                  match (Object.put_field o (ap, z, concat (h, p) (hf, pf), fs) v) with 
                    | Some o' => Some (update he i o')
                    | _ => None
                  end
              end
          | _ => None
        end
    end.
*)


  End G.
End Globals.

(** * Cast (inspired from Wasserrab et al.) *)

Section Wasserrab.
  Variable A : ATOM.t.

(** ** Domination *)

Section Domination.

Variable hierarchy : PTree.t (Class.t A).

Inductive dominates (from : ident) (kp1 kp2 : Class.Inheritance.t * list ident) : Prop :=
| dominates_intro : forall k1 p1,
  kp1 = (k1, p1) ->
  forall to1,
    path hierarchy to1 p1 from k1 ->
    forall to2 k p,
      path hierarchy to2 p to1 k ->
      kp2 = concat kp1 (k, p) ->
      dominates from kp1 kp2
      .

Lemma dominates_trans : forall from kp1 kp2,
  dominates from kp1 kp2 ->
  forall kp3,
    dominates from kp2 kp3 ->
    dominates from kp1 kp3
    .
Proof.
  destruct 1.
  subst.
  destruct 1.
  subst.
  generalize (path_concat H0 H1 (sym_equal H)).
  intros.
  generalize (path_last H2).
  generalize (path_last H4).
  intros.
  replace to0 with to2 in * by congruence.
  rewrite concat_assoc.
  case_eq (concat (k, p) (k2, p2)).
  intros.
  generalize (path_concat H1 H3 (sym_equal H7)).
  intros.
  econstructor.
  reflexivity.
  eassumption.
  eassumption.
  trivial.
Qed.

Lemma dominates_refl_weak : forall from to k p,
  path hierarchy to p from k ->
  dominates from (k, p) (k, p).
Proof.
  intros.
  eapply dominates_intro with (p := nil ++ to :: nil). 
  reflexivity.
  eassumption.
  eleft.
  simpl.
  reflexivity.
  reflexivity.
  simpl.
  generalize (path_path2 H).
  clear H.
  induction 1 ; auto.
   destruct (hierarchy ! to) ; congruence.
  simpl.  
  rewrite (path_last H).
  destruct (peq to to) ; try congruence.
  rewrite <- app_nil_end.
  trivial.
Qed.

Lemma dominates_concat_left_0 : forall from from' k' p',
    path hierarchy from p' from' k' ->
    forall k1 p1 k2 p2,
      dominates from (k1, p1) (k2, p2) ->
      forall k'1 p'1,
        (k'1, p'1) = concat (k', p') (k1, p1) ->
        forall k'2 p'2,
          (k'2, p'2) = concat (k', p') (k2, p2) ->          
          dominates from' (k'1, p'1) (k'2, p'2)
          .
Proof.
 inversion 2.
 injection H1 ; intros ; subst.
 generalize H8.
 intro.
 rewrite H4 in H5.
 rewrite <- concat_assoc in H5.
 rewrite <- H7 in H5.
 generalize (path_concat H H2 H7).
 intros.
 econstructor ; eauto.
Qed.

Lemma dominates_concat_left : forall from from' k' p',
    path hierarchy from p' from' k' ->
    forall k1 p1 k2 p2,
      forall k'1 p'1,
        (k'1, p'1) = concat (k', p') (k1, p1) ->
        forall k'2 p'2,
          (k'2, p'2) = concat (k', p') (k2, p2) ->          
          dominates from (k1, p1) (k2, p2) ->
          dominates from' (k'1, p'1) (k'2, p'2)
          .
Proof.
  intros ; eauto using dominates_concat_left_0.
Qed.

End Domination.

(** ** Dynamic cast *)

Section Dynamic_cast.


Variable hierarchy : PTree.t (Class.t A).

Variable real : ident.

Variable real_inheritance : Class.Inheritance.t.

Variable real_path : list ident.

Variable from : ident.

Variable cast : ident.

Section Dyncast.

Variable cast_inheritance : Class.Inheritance.t.

Variable cast_path : list ident.

Inductive dynamic_cast : Prop :=
| dynamic_cast_upcast
  (_ : path hierarchy from real_path real real_inheritance)
  k p
  (_ : path hierarchy cast p from k)
  (_ : forall k' p', path hierarchy cast p' from k' -> (k, p) = (k', p'))
  (_ : (cast_inheritance, cast_path) = concat (real_inheritance, real_path) (k, p))
| dynamic_cast_downcast
  (_ : path hierarchy cast cast_path real cast_inheritance)
  p
  (_ : path hierarchy from p cast Class.Inheritance.Repeated)
  (_ : (real_inheritance, real_path) = concat (cast_inheritance, cast_path) (Class.Inheritance.Repeated, p))
| dynamic_cast_crosscast
  (_ : path hierarchy from real_path real real_inheritance)
  (_ : path hierarchy cast cast_path real cast_inheritance)
  (_ : forall k p, path hierarchy cast p real k -> (k, p) = (cast_inheritance, cast_path))
.

Inductive dynamic_cast_aux : nat -> Prop :=
| dynamic_cast_aux_upcast : forall
  (_ : path hierarchy from real_path real real_inheritance)
  k p
  (_ : path hierarchy cast p from k)
  (_ : forall k' p', path hierarchy cast p' from k' -> (k, p) = (k', p'))
  (_ : (cast_inheritance, cast_path) = concat (real_inheritance, real_path) (k, p)),
  dynamic_cast_aux O
| dynamic_cast_aux_downcast : forall
  (_ : path hierarchy cast cast_path real cast_inheritance)
  p
  (_ : path hierarchy from p cast Class.Inheritance.Repeated)
  (_ : (real_inheritance, real_path) = concat (cast_inheritance, cast_path) (Class.Inheritance.Repeated, p)),
  dynamic_cast_aux (S O)
| dynamic_cast_aux_crosscast : forall
  (_ : path hierarchy from real_path real real_inheritance)
  (_ : path hierarchy cast cast_path real cast_inheritance)
  (_ : forall k p, path hierarchy cast p real k -> (k, p) = (cast_inheritance, cast_path)),
  dynamic_cast_aux (S (S O))
.

Lemma dynamic_cast_dynamic_cast_aux : 
  dynamic_cast -> exists n,
    dynamic_cast_aux n.
Proof.
 inversion 1 ; esplit ; eauto using dynamic_cast_aux_upcast, dynamic_cast_aux_downcast, dynamic_cast_aux_crosscast.
Qed.


End Dyncast.

End Dynamic_cast.

(** ** Static cast *)

Section Static_cast.

Variable hierarchy : PTree.t (Class.t A).

Variable real : ident.

Variable real_inheritance : Class.Inheritance.t.

Variable real_path : list ident.

Variables from cast : ident.

Section Statcast.

Variable cast_inheritance : Class.Inheritance.t.

Variable cast_path : list ident.

Inductive static_cast : Prop :=
| static_cast_upcast
  (_ : path hierarchy from real_path real real_inheritance)
  k p
  (_ : path hierarchy cast p from k)
  (_ : forall k' p', path hierarchy cast p' from k' -> (k, p) = (k', p'))
  (_ : (cast_inheritance, cast_path) = concat (real_inheritance, real_path) (k, p))
| static_cast_downcast
  (_ : path hierarchy cast cast_path real cast_inheritance)
  p
  (_ : path hierarchy from p cast Class.Inheritance.Repeated)
  (_ : forall p', path hierarchy from p' cast Class.Inheritance.Repeated -> p' = p)    
  (_ : (real_inheritance, real_path) = concat (cast_inheritance, cast_path) (Class.Inheritance.Repeated, p))
.

End Statcast.

End Static_cast.

Lemma static_cast_dynamic_cast : forall hierarchy real rh rp from cast ch cp,
  static_cast hierarchy real rh rp from cast ch cp ->
  dynamic_cast hierarchy real rh rp from cast ch cp.
Proof.
  inversion 1; subst.
  eapply dynamic_cast_upcast.
  assumption.
  eassumption.
  assumption.
  assumption.
  eapply dynamic_cast_downcast.
  assumption.
  eassumption.
  assumption.
Qed.
 
(** * Method dispatch (inspired from Wasserrab et al.) *)

Section Method_dispatch.

Variable hierarchy : PTree.t (Class.t A).

Inductive final_overrider 
  (ms : MethodSignature.t A (* the method to dispatch *)) 
  (apparent_class : ident   (* the static type of the pointer *)) 
  (most_derived : ident       (* the dynamic type (most-derived class) of the pointer *))
  (apparent_inheritance : Class.Inheritance.t)
  (apparent_path : list ident (* the path from the most-derived class to the static type subobject *))
  (dispatched_inheritance:  Class.Inheritance.t)
  (dispatched_path : list ident (* the path from the most-derived class to the dispatched method *)) : Prop :=
| final_overrider_intro 
    (_ : path hierarchy apparent_class apparent_path most_derived apparent_inheritance)
   apparent_method_class apparent_method_inheritance apparent_method_path
    (_ : path hierarchy apparent_method_class apparent_method_path apparent_class apparent_method_inheritance)
    apparent_method_class_body
    (_ : hierarchy ! apparent_method_class = Some apparent_method_class_body)
    (_ : Method.find ms (Class.methods apparent_method_class_body) <> None)
    (_ : forall to k p,
        path hierarchy to p apparent_class k ->
        forall c, hierarchy ! to = Some c ->
          Method.find ms (Class.methods c) <> None ->
          dominates hierarchy apparent_class (apparent_method_inheritance, apparent_method_path) (k, p))
    k0 p0
    (_ : (k0, p0) = concat (apparent_inheritance, apparent_path) (apparent_method_inheritance, apparent_method_path) )
    dispatched
    (_ : path hierarchy dispatched dispatched_path most_derived dispatched_inheritance)
    (_ : dominates hierarchy most_derived (dispatched_inheritance, dispatched_path) (k0, p0))
    dispatched_body
    (_ : hierarchy ! dispatched = Some dispatched_body)
    (_ : Method.find ms (Class.methods dispatched_body) <> None)
    (_ : forall to k p,
      path hierarchy to p most_derived k ->
      forall c, hierarchy ! to = Some c ->
        Method.find ms (Class.methods c) <> None ->
        dominates hierarchy most_derived (k, p) (dispatched_inheritance, dispatched_path) ->
        (k, p) = (dispatched_inheritance, dispatched_path)
    )
.

Inductive method_dispatch 
  (ms : MethodSignature.t A (* the method to dispatch *)) 
  (apparent_class : ident   (* the static type of the pointer *)) 
  (most_derived : ident       (* the dynamic type (most-derived class) of the pointer *))
  (apparent_inheritance : Class.Inheritance.t)
  (apparent_path : list ident (* the path from the most-derived class to the static type subobject *))
  (dispatched_inheritance:  Class.Inheritance.t)
  (dispatched_path : list ident (* the path from the most-derived class to the dispatched method *)) : Prop :=
  method_dispatch_intro
  h p tom
  (_ : path hierarchy tom p apparent_class h)
  tomc
  (_ : hierarchy ! tom = Some tomc)
  m
  (_ : Method.find ms (Class.methods tomc) = Some m)
  (_ : Method.virtual m = true)
  (_ : final_overrider ms apparent_class most_derived apparent_inheritance apparent_path dispatched_inheritance dispatched_path)
  (_ : forall di dp, final_overrider ms apparent_class most_derived apparent_inheritance apparent_path di dp -> (dispatched_inheritance, dispatched_path) = (di, dp))
.



End Method_dispatch.

End Wasserrab.



(** Virtual base construction order *)

Section VBorder.

  Variable A : ATOM.t.

  Function vborder_f (l : list ident) (b : ident) : bool :=
    if In_dec peq b l then false else true.

  Function pne (a b : ident) : bool :=
    if peq a b then false else true.

  Variable hier : PTree.t (Class.t A).

  Inductive vborder_list : list (Class.Inheritance.t * ident) -> list ident -> Prop :=
  | vborder_list_nil : vborder_list nil nil
  | vborder_list_cons : forall a c,
    hier ! a = Some c ->
    forall la, vborder_list (Class.super c) la ->
      forall l y, vborder_list l y ->
      forall h y',
        y' = match h with
               | Class.Inheritance.Repeated => y
               | Class.Inheritance.Shared => a :: (filter (pne a) y)
             end ->
        forall z,
          z = la ++ filter (vborder_f la) y' ->
          vborder_list ((h, a) :: l) z
.

  Lemma vborder_list_func : forall l l1,
    vborder_list l l1 ->
    forall l2, vborder_list l l2 ->
      l1 = l2.
  Proof.
    induction 1; inversion 1; subst.
     trivial.
    replace c0 with c in * by congruence.
    replace y0 with y in * by eauto.
    replace la0 with la in * by eauto.
    trivial.
  Qed.


(** Properties of virtual base ordering *)

   Lemma vborder_no_dup : forall l y,
     vborder_list l y -> NoDup y.
   Proof.
     induction 1.
      constructor.
     subst.
     apply NoDup_app_intro.
      assumption.
     apply NoDup_filter_compat.
     destruct h.
      assumption.
     constructor.
     intro.
     destruct (filter_In (pne a) a y).
     destruct (H3 H2).
     functional inversion H6.
     congruence.
     eauto using NoDup_filter_compat.
     intros.
     destruct (filter_In (vborder_f la) x
       match h with
         | Class.Inheritance.Repeated => y
         | Class.Inheritance.Shared => a :: filter (pne a) y
       end).
     destruct (H4 H3).
     functional inversion H7.
     contradiction.
   Qed.

   Definition vborder_list_no_dup := vborder_no_dup.

   Lemma filter_vborder_f_nil : forall y2, (filter (vborder_f nil) y2 = y2).
   Proof.
     induction y2; simpl.
      trivial.
      f_equal.
      assumption.
    Qed.

    Lemma filter_vborder_app : forall l1 l2 l,
      filter (vborder_f (l1 ++ l2)) l = filter (vborder_f l1) (filter (vborder_f l2) l).
    Proof.
      induction l; simpl.
       trivial.
      case_eq (vborder_f (l1 ++ l2) a); functional inversion 1.
       case_eq (vborder_f l2 a); functional inversion 1.
        simpl.
        case_eq (vborder_f l1 a); functional inversion 1.
         f_equal.
         eauto.
        destruct _x; eauto using in_or_app.
       destruct _x; eauto using in_or_app.
      case_eq (vborder_f l2 a); functional inversion 1.
       simpl.
       case_eq (vborder_f l1 a); functional inversion 1.
        destruct (in_app_or _ _ _ _x); contradiction.
       auto.
      auto.
    Qed.       

    Lemma filter_vborder_compo : forall l1 l2 l,
      filter (vborder_f l1) (filter (vborder_f (filter (vborder_f l1) l2)) l) = filter (vborder_f l1) (filter (vborder_f l2) l).
    Proof.
      induction l; simpl.
       trivial.
      case_eq (vborder_f l2 a); functional inversion 1; simpl.
       case_eq (vborder_f l1 a); functional inversion 1; simpl.
        case_eq (vborder_f (filter (vborder_f l1) l2) a); functional inversion 1; simpl.
         rewrite H1.
         f_equal.
         assumption.
        destruct _x.
        destruct (filter_In (vborder_f l1) a l2).
        destruct (H0 _x1).
        assumption.
       case_eq (vborder_f (filter (vborder_f l1) l2) a); functional inversion 1; simpl.
       rewrite H1.
       assumption.
       assumption.
      case_eq (vborder_f (filter (vborder_f l1) l2) a); functional inversion 1; simpl.      
       case_eq (vborder_f l1 a); functional inversion 1; simpl.
        destruct _x0.
        apply (filter_In (vborder_f l1) a l2).
         tauto.
        assumption.
        assumption.
      Qed.

(*
      Lemma filter_vborder_incl : forall l1 l2, (forall x, In x l2 -> In x l1) -> forall l,
        filter (vborder_f l2) (filter (vborder_f l1) l) = filter (vborder_f l1) l.
      Proof.
        induction l; simpl; try trivial.
        case_eq (vborder_f l1 a); functional inversion 1; simpl.
         case_eq (vborder_f l2 a); functional inversion 1; simpl.
          f_equal; assumption.
         destruct _x; auto.
        assumption.
      Qed.
*)

      Lemma filter_pne_vborder : forall a l,
        filter (pne a) l = filter (vborder_f (a::nil)) l.
      Proof.
        induction l; simpl; try trivial.
        functional induction (pne a a0);
         functional induction (vborder_f (a :: nil) a0).
          assumption.
         destruct _x0; simpl; auto.
        inversion _x0; contradiction.
       f_equal; assumption.
     Qed.

  Lemma vborder_list_app_intro : forall l1 y1,
    vborder_list l1 y1 ->
    forall l2 y2,
      vborder_list l2 y2 ->
      vborder_list (l1 ++ l2) (
        y1 ++ filter (vborder_f y1) y2
      ).
  Proof.
    induction 1; simpl.
     intros.
     rewrite filter_vborder_f_nil.
     assumption.
     intros.
     econstructor.
      eassumption.
      eassumption.
      eapply IHvborder_list2.
      eassumption.
      reflexivity.
     subst.
     rewrite app_ass.
     f_equal.
     clear c H H0 l H1 IHvborder_list1 IHvborder_list2 l2 H4.
     revert y2 a.
     destruct h.
      intros.
      rewrite filter_vborder_app.
      rewrite filter_app.
      rewrite filter_vborder_compo.
      trivial.
     intros.
      change (a :: filter (pne a) y) with ((a :: nil) ++ filter (pne a) y).
      change (a :: filter (pne a) (y ++ filter (vborder_f y) y2)) with ((a :: nil) ++ filter (pne a) (y ++ filter (vborder_f y) y2)).
      repeat rewrite filter_pne_vborder.
      repeat rewrite filter_app.
      rewrite app_ass.
      f_equal.
      f_equal.
      repeat rewrite filter_vborder_app.
      rewrite filter_vborder_compo.
      rewrite filter_commut.
      rewrite filter_vborder_compo.
      rewrite filter_commut.
      rewrite filter_vborder_compo.
      trivial.
    Qed.

  Lemma vborder_list_app_elim : forall l1 l2 y,
    vborder_list (l1 ++ l2) y ->
    (exists y1, vborder_list  l1 y1) /\
    (exists y2, vborder_list  l2 y2).
  Proof.
    induction l1; simpl.
     split.
     esplit.
      econstructor.
     esplit.
     eassumption.
    inversion 1; subst.
    destruct (IHl1 _ _ H4).
    destruct H0.
    split.
    2 : assumption.
    esplit.
    econstructor.
    eassumption.
    eassumption.
    eassumption.
    reflexivity.
    reflexivity.
  Qed.
  
  Lemma vborder_list_In : forall l y,
    vborder_list  l y ->
    forall b, In b y ->
      In (Class.Inheritance.Shared, b) l \/ (
        exists h', exists b', In (h', b') l /\
          exists c', hier ! b' = Some c' /\
            exists y', vborder_list (Class.super c') y' /\
              In b y'
      ).
  Proof.
    induction 1.
     simpl; tauto.
     rewrite H3.
     intros until 1.
     destruct (in_app_or _ _ _ H4).
      right.
      esplit.
      esplit.
      split.
      left.
      reflexivity.
      esplit.
      split.
      eassumption.
      esplit.
      split.
      eassumption.
      assumption.
     destruct (filter_In (vborder_f la) b y').
     destruct (H6 H5).
     functional inversion H9.
     clear H10.
     rewrite H2 in H8.
     destruct h.
      destruct (IHvborder_list2 _ H8).
       left.
       auto.
      right.
      destruct H10.
      destruct H10.
      destruct H10.
      esplit.
      esplit.
      esplit.
      right.
      eassumption.
     assumption.
    destruct H8.
    left.
    left.
    rewrite H8.
    trivial.
    destruct (filter_In (pne a) b y).
    destruct (H10 H8).
    destruct (IHvborder_list2 _ H12).
    left.
    auto.
    right.
    destruct H14.
    destruct H14.
    destruct H14.
    esplit.
    esplit.
    split.
     right.
     eassumption.
    assumption.
  Qed.


  Lemma virtual_base_vborder_list : forall a b,
    is_virtual_base_of hier b a ->
    forall c, hier ! a = Some c ->
      forall y, vborder_list  (Class.super c) y ->
        In b y.
  Proof.
    induction 1.
     intros.
     replace c0 with c in * by congruence.
     destruct (member_extract H0).
     destruct H3.
     rewrite H3 in H2.
     destruct (vborder_list_app_elim H2).
     destruct H5.
     inversion H5; subst.
     destruct H4.
     generalize (vborder_list_app_intro H4 H5).
     intro.
     generalize (vborder_list_func H2 H6).
     intro.
     subst.
     apply in_or_app.
     case_eq (vborder_f x1 b); functional inversion 1; try tauto.
     right.
     eapply filter_In.
     split; try assumption.
     apply in_or_app.
     case_eq (vborder_f la b); functional inversion 1; try tauto.
     right.
     eapply filter_In.
     split; auto.
    intros.
    replace c0 with c in * by congruence.
    destruct (member_extract H0).
    destruct H4.
    rewrite H4 in H3.
    destruct (vborder_list_app_elim H3).
    destruct H6.
    inversion H6; subst.
    destruct H5.
    generalize (vborder_list_app_intro H5 H6).
    intro.
    generalize (vborder_list_func H3 H7).
    intro; subst.
    generalize (IHis_virtual_base_of _ H10 _ H11).
    intros.
    apply in_or_app.
    case_eq (vborder_f x1 b); functional inversion 1; try tauto.
    right.
    eapply filter_In.
    split; try assumption.
    apply in_or_app; auto.
  Qed.

  Lemma vborder_list_virtual_base : forall a c,
    hier ! a = Some c ->
    forall y,
      vborder_list  (Class.super c) y ->
      forall b, In b y ->
        is_virtual_base_of hier b a.
  Proof.
    cut (
      forall l y,
        vborder_list  l y ->
        forall a c, hier ! a = Some c ->
          forall l', Class.super c = l' ++ l ->
            forall b, In b y ->
              is_virtual_base_of hier b a
    ).
     intros.
     eapply H with (l' := nil); eauto.
    induction 1.
     simpl; tauto.
    intros.
    rewrite H3 in H6.
    destruct (in_app_or _ _ _ H6).
     eright.
     eassumption.
     rewrite H5.
     eapply in_or_app.
     right.
     left.
     reflexivity.
     eapply IHvborder_list1 with (l' := nil).
     eassumption.
     reflexivity.
     assumption.
    destruct (filter_In (vborder_f la) b y').
    destruct (H8 H7).
    assert (l' ++ (h, a) :: l = (l' ++ (h, a) :: nil) ++ l) by (rewrite app_ass; reflexivity).
    destruct h.
     subst.
     eapply IHvborder_list2.
     eassumption.
     rewrite H5.
     eassumption.
     assumption.
    subst.
    destruct H10.
     subst.
     eleft.
     eassumption.
     rewrite H5.     
     apply in_or_app.
     auto.
    destruct (filter_In (pne a) b y).
    destruct (H3 H2).
     eapply IHvborder_list2.
     eassumption.
     rewrite H5.
     eassumption.
     assumption.
   Qed.    
          
   Lemma vborder_list_bases_first : forall l y,
     vborder_list  l y ->
     forall b, In b y ->
       forall a, is_virtual_base_of hier a b ->
         list_lt y a b.
   Proof.
     induction 1.
      simpl; tauto.
     rewrite H3.
     intros until 1.
     destruct (in_app_or _ _ _ H4).
      intros.
      eauto using list_lt_app_reg_r.
     destruct (filter_In (vborder_f la) b y').
     destruct (H6 H5).
     destruct h.
      subst.     
      intros.
      generalize (IHvborder_list2 _ H8 _ H2).
      intros.
      generalize (list_lt_In_left H3).
      intros.
      case_eq (vborder_f la a0); functional inversion 1.
      eapply list_lt_app_reg_l.
      eauto using list_lt_app_reg_l, list_lt_filter_aux.
     eauto using list_lt_app.
    subst.
    destruct H8.
     subst.
     simpl.
     rewrite H9.
     intros.
     eauto using list_lt_app, virtual_base_vborder_list.
    functional inversion H9.
    intros.
    case_eq (vborder_f la a0); functional inversion 1.
    apply list_lt_app_reg_l.
    simpl.
    case_eq (vborder_f la a).
     intros.
     cut (list_lt ((a :: nil) ++ (filter (vborder_f la) (filter (pne a) y))) a0 b).
      simpl; tauto.
     case_eq (pne a b); functional inversion 1.
      case_eq (pne a a0); functional inversion 1.
       apply list_lt_app_reg_l.
       rewrite filter_commut.
       apply list_lt_filter_aux; auto.
       apply list_lt_filter_aux; auto.
       eapply IHvborder_list2.
       destruct (filter_In (pne a) b y).
       destruct (H17 H2).
       assumption.
       assumption.
      apply list_lt_app.
      rewrite _x2.
      auto.
      eapply filter_In.
      auto.
     apply False_rect.
     clear H14 H13.
     subst.
     destruct (filter_In (pne b) b y).
     destruct (H13 H2).
     functional inversion H16.
     congruence.
    intros.
    apply list_lt_filter_aux; auto.
    destruct (filter_In (pne a) b y).
    destruct (H13 H2).
    case_eq (pne a a0); functional inversion 1.
     eauto using list_lt_filter_aux.
    apply False_rect.
    clear H18 H17.
    subst.
    congruence.
   apply list_lt_app.
   assumption.
   eapply filter_In.
   split; auto.
 Qed.
      
End VBorder.
