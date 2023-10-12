(** LayoutConstraints.v: Copyright 2010 Tahina Ramananandro *)

Require Import LibLists.
Require Import Maps.
Require Import Cplusconcepts.
Require Import Coqlib.
Require Import Tactics.
Require Import CplusWf.
Require Import LibMaps.

(** Status convention for propositions:
   - [Remark]:  not specific to C++ formalization
   - [Fact]:    specific to C++ formalization, intended for internal use only
   - [Lemma]:   specific to C++ formalization
   - [Theorem]: theorems of the POPL'11 paper
*)

(** * General-purpose tools *)

Load Param.

Remark option_eq_dec : forall (T : Type) (T_eq_dec : forall t1 t2 : T, {t1 = t2} + {t1 <> t2}),
  forall l1 l2 : option T, {l1 = l2} + {l1 <> l2}.
Proof.
  repeat decide equality.
Qed.

Remark prod_eq_dec : forall (U : Type) (U_eq_dec : forall u1 u2 : U, {u1 = u2} + {u1 <> u2})
  (V : Type) (V_eq_dec : forall v1 v2 : V, {v1 = v2} + {v1 <> v2})
  (p1 p2 : U * V), {p1 = p2} + {p1 <> p2}.
Proof.
  repeat decide equality.
Qed.


    Remark Zpos_positive : forall n, 0 < Zpos n.
    Proof.
      intros ; compute ; trivial.
    Qed.

    (* Corollary *) Remark Zpos_minus_1_nonnegative : forall n, 0 <= Zpos n - 1.
    Proof.
      intros.
      generalize (Zpos_positive n).
      omega.
    Qed.

    Remark Zmult_ge : forall a b, 0 <= a -> 0 <= b -> 0 <= a * b.
    Proof.
      intros.
      replace 0 with (0 * 0) by reflexivity.
      apply Zmult_le_compat ; omega.
    Qed.

    Remark Zmult_gt : forall a b, 0 < a -> 0 < b -> 0 < a * b.
    Proof.
      intros.
      assert (0 < a) by omega.
      assert (0 < b) by omega.
      cut (0 < (a * b)) ; [ omega | ].
      replace 0 with (0 * 0) by reflexivity.
      eapply Zmult_lt_compat ; omega.
    Qed.

    Remark Zmult_distr_1: forall x y, x * y + y = (x + 1) * y.
    Proof.
      intros.
      rewrite Zmult_plus_distr_l.
      omega.
    Qed.

    Remark array_cells_disjoint : forall i j, i <> j -> forall s, 0 < s ->
      i * s + s <= j * s \/ j * s + s <= i * s.
    Proof.
      intros.
      repeat rewrite Zmult_distr_1.
      cut (i + 1 <= j \/ j + 1 <= i).
       inversion 1.
       left.
       eapply Zmult_le_compat_r.
        assumption.
        omega.
       right.
       eapply Zmult_le_compat_r.
        assumption.
        omega.
       omega.
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
       exists (@nil A).
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

     (* Corollary *) Remark distinct_lists_rect : forall (A : Type) (aeq : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}) (P : list A -> list A -> Type),
       (forall l1 l2, P l1 l2 -> P l2 l1) ->
       (forall l1 a l2', P l1 (l1 ++ a :: l2')) ->
       (forall l a1 l1' a2 l2', a1 <> a2 -> P (l ++ a1 :: l1') (l ++ a2 :: l2')) ->
       forall l1 l2, l1 <> l2 -> P l1 l2.
     Proof.
       intros until 4.
       cut (forall l1 l2, (length l1 <= length l2)%nat -> l1 <> l2 -> P l1 l2).
        intros.
        destruct (le_lt_dec (length l1) (length l2)).
         auto.
        apply X.
        apply X2.
        omega.
        congruence.
      intros.
      destruct (distinct_paths_cases aeq H H0); invall; subst; auto.
    Qed.

(** * Requirements for a class to be empty (4.3) *)

Module Is_empty.

Section Is_empty.

Variable A : ATOM.t.

Variable hierarchy : PTree.t (Class.t A).

Variable is_empty : ident -> Prop.

Record prop : Prop := intro {
  defined: forall i, is_empty i -> hierarchy ! i <> None;
  fields_struct: forall i,
    is_empty i -> forall c,
      hierarchy ! i = Some c ->
      forall f, In f (Class.fields c) -> exists e, exists he, FieldSignature.type f = FieldSignature.Struct e he
        ;
  fields_struct_empty: forall i,
    is_empty i ->
    forall c, hierarchy ! i = Some c ->
      forall f, In f (Class.fields c) ->
        forall e he,  FieldSignature.type f = FieldSignature.Struct e he ->
          is_empty e
          ;
  bases_empty : forall i,
    is_empty i ->
    forall c, hierarchy ! i = Some c ->
      forall h b, In (h, b) (Class.super c) ->
        is_empty b
}.

Hypothesis Hprop : prop.

Lemma no_scalar_fields : forall ci,
  is_empty ci -> forall c,
    hierarchy ! ci = Some c -> forall f,
      In f (Class.fields c) -> forall t,
        FieldSignature.type f = FieldSignature.Scalar t ->
        False.
Proof.
  intros.
  generalize (fields_struct Hprop H H0 H1).
  destruct 1.
  invall.
  congruence.
Qed.

Lemma path_to : forall to via from by
  (Hpath : path hierarchy to via from by)
  (H_empty_from : is_empty from),
  is_empty to.
Proof.
  intros.
  generalize (path_path2 Hpath).
  clear Hpath.
  intro Hpath.
  revert H_empty_from.
  induction Hpath ; intros; eauto using bases_empty.
Qed.

(* Corollary *) Lemma path_from : forall l h to from, 
  path hierarchy to l from h ->
    (is_empty to -> False) ->
    (is_empty from -> False).
Proof.  
  intros; eauto using path_to.
Qed.

Lemma array_path_to : forall from zfrom to zto p,
  valid_array_path hierarchy to zto from zfrom p ->
  is_empty from ->
  is_empty to
.
Proof.
induction 1; subst; intros; eauto using fields_struct_empty, path_to.
Qed.

(* Corollary *) Lemma array_path_from : forall from zfrom to zto p,
  valid_array_path hierarchy to zto from zfrom p ->
  (is_empty to -> False) ->
  is_empty from -> False
.
Proof.
  intros;  eauto using array_path_to.
Qed.

(* Corollary *) Lemma relative_pointer_to : forall afrom zfrom a ato i h' p' pto,
   valid_relative_pointer hierarchy afrom zfrom a ato i h' p' pto ->
   is_empty afrom ->
   is_empty pto.
Proof.
 inversion 1; subst; intros; eauto using array_path_to, path_to.
Qed.

(* Corollary *) Lemma relative_pointer_from : forall afrom zfrom a ato i h' p' pto,
   valid_relative_pointer hierarchy afrom zfrom a ato i h' p' pto ->
   (is_empty pto -> False) ->  
   is_empty afrom -> False.
Proof.
  intros; eauto using relative_pointer_to.
Qed.

End Is_empty.

End Is_empty.

Section OPTIM.

Variable A : ATOM.t.

Record OPTIM : Type := Optim {
  is_empty : PTree.t (Class.t A) -> ident -> Prop;
  is_empty_prop : forall hierarchy, Is_empty.prop hierarchy (is_empty hierarchy);
  is_dynamic : PTree.t (Class.t A) -> ident -> Prop;
  (** 4.3 *)
  dynamic_nonempty : forall hierarchy id, is_dynamic hierarchy id -> is_empty hierarchy id -> False
}.
 
End OPTIM.

(** * Platform-dependent parameters (4.1) *)

Section PLATFORM.

Variable A : ATOM.t.

Record PLATFORM : Type := Platform {
  typ_size : Typ.t A -> Z; (** size of a scalar data of type atomic or pointer to class *)
  typ_size_positive : forall ty, 0 < typ_size ty;
  typ_align : Typ.t A -> Z;
  typ_align_positive : forall ty, 0 < typ_align ty;
  dynamic_type_data_size : Z;
  dynamic_type_data_size_low_bound : 0 < dynamic_type_data_size;
  dynamic_type_data_align : Z;
  dynamic_type_data_align_low_bound : 0 < dynamic_type_data_align
}.

End PLATFORM.

Section Offsets.

Variable A  : ATOM.t.
Variable OP : OPTIM A.
Variable PF : PLATFORM A.

(** * What a layout algorithm is expected to compute (4.2) *)

    Record t : Type := make {
      (** pbase     *) primary_base                       : option ident;
      (** dnvboff   *) non_virtual_direct_base_offsets    : PTree.t Z;
      (** fboundary *) own_fields_offset                  : Z;
      (** foff      *) field_offsets                      : list (FieldSignature.t A * Z);
      (** nvdsize   *) non_virtual_data_size              : Z;
      (** nvsize    *) non_virtual_size                   : Z;
      (** nvalign   *) non_virtual_align                  : Z;
      (** vboff     *) virtual_base_offsets               : PTree.t Z; (* will also include the class itself, with offset 0 *)
      (** dsize     *) data_size                          : Z;
      (** size      *) size                               : Z;
      (** align     *) align                              : Z
    }.

  Section OF.

  Variable offsets : PTree.t t.

  (** * Computation of offsets (4.4) *) 


    Function field_data_size (f : FieldSignature.t A) : option Z :=
      match FieldSignature.type f with
        | FieldSignature.Scalar ty => Some (typ_size PF ty)
        | FieldSignature.Struct c n =>
          match offsets ! c with
            | Some o => Some ((Zpos n - 1) * size o + data_size o)
            | None => None
          end
      end.

    Function field_size (f : FieldSignature.t A) : option Z :=
      match FieldSignature.type f with
        | FieldSignature.Scalar ty => Some (typ_size PF ty)
        | FieldSignature.Struct c n =>
          match offsets ! c with
            | Some o => Some ((Zpos n - 1) * size o + size o)
            | None => None
          end
      end.
    

    Function field_align (f : FieldSignature.t A) : option Z :=
      match FieldSignature.type f with
        | FieldSignature.Scalar ty => Some (typ_align PF ty)
        | FieldSignature.Struct c n =>
          match offsets ! c with
            | Some o => Some (align o)
            | _ => None
          end
      end.

  Function non_virtual_subobject_offset (accu : Z) (l : list ident) {struct l} : option Z :=
    match l with
      | nil => None
      | a :: l' =>
        match l' with
          | nil => Some accu
          | b :: _ =>
            match offsets ! a with
              | None => None
              | Some o =>
                match (non_virtual_direct_base_offsets o) ! b with
                  | Some of => non_virtual_subobject_offset (accu + of) l'
                  | _ => None
                end
            end
        end
    end.

Fact non_virtual_subobject_offset_app : forall l1 a accu accu',
  non_virtual_subobject_offset accu (l1 ++ a :: nil) = Some accu' ->
  forall l2,
  non_virtual_subobject_offset accu (l1 ++ a :: l2) = non_virtual_subobject_offset accu' (a :: l2)
.
Proof.
  induction l1.
   (* "case nil". *)
   simpl.
   injection 1 ; intros ; subst.
   reflexivity.
  (* "case a :: l1" *)
   intros.
   simpl in H.
   cut (forall v, non_virtual_subobject_offset accu' (a0 :: l2) = v ->   non_virtual_subobject_offset accu ((a :: l1) ++ a0 :: l2) =v).
    intros ; eauto.
   intros.
   change ((a :: l1) ++ a0 :: l2) with
     (a :: (l1 ++ a0 :: l2)).
   replace (l1 ++ a0 :: l2) with ((l1 ++ a0 :: nil) ++ l2).
   revert H.
   case_eq (l1 ++ a0 :: nil).
    intros.
    apply False_rect.
    destruct l1 ; simpl in * ; discriminate.
   intros until 1.
   rewrite <- H.
   simpl.
   replace ((l1 ++ a0 :: nil) ++ l2) with (i :: l ++ l2).
   change (i :: l ++ l2) with ((i :: l) ++ l2).
   rewrite <- H.
   replace ((l1 ++ a0 :: nil) ++ l2) with (l1 ++ a0 :: l2).
   destruct (offsets ! a).
    destruct ((non_virtual_direct_base_offsets t0) ! i).
     rewrite <- H0.
     intros.
     eauto.
     congruence.
    congruence.
   rewrite app_ass.
   reflexivity.
   rewrite H.
   reflexivity.
   rewrite app_ass.
   reflexivity.
 Qed.  

Fact non_virtual_subobject_offset_app_recip : forall l1 a l2 accu accu',
  non_virtual_subobject_offset accu (l1 ++ a :: l2) = Some accu' ->
  exists accu1, 
    non_virtual_subobject_offset accu (l1 ++ a :: nil) = Some accu1 /\
    non_virtual_subobject_offset accu1 (a :: l2) = Some accu'
.  
Proof.
induction l1.
 intros a l2 accu accu'.
 change (nil ++ a :: l2) with (a :: l2).
 intro.
 exists accu.
 split.
 reflexivity.
 assumption.
 intros.
 change ((a :: l1) ++ a0 :: l2) with (a :: l1 ++ a0 :: l2) in H.
 change ((a :: l1) ++ a0 :: nil) with (a :: l1 ++ a0 :: nil).
 simpl in H.
 case_eq (l1 ++ a0 :: nil).
  intros.
  destruct l1 ; simpl in H0 ; discriminate.
 intros.
 assert  (l1 ++ a0 :: l2 = i :: l ++ l2).
  change (a0 :: l2) with ((a0 :: nil) ++ l2).
  rewrite <- app_ass.
  rewrite H0.
  reflexivity.
 rewrite H1 in H.
 rewrite <- H1 in H.
 case_eq ((offsets) ! a).
  intros.
  rewrite H2 in H.
  case_eq ((non_virtual_direct_base_offsets t0) ! i).
   intros.
   rewrite H3 in H.
   destruct (IHl1 _ _ _ _ H).
   destruct H4.
   esplit.
   split.
   2 : eassumption.
   rewrite <- H0.
   simpl.
   rewrite H0.
   rewrite H2.
   rewrite H3.
   congruence.
   intros.
   rewrite H3 in H.
   discriminate.
  intros.
  rewrite H2 in H.
  discriminate.
Qed.

Fact non_virtual_subobject_offset_rewrite : forall l accu v,
  non_virtual_subobject_offset accu l = Some v ->
  forall accu',
    non_virtual_subobject_offset accu' l = Some (v + accu' - accu).
Proof.
  intro.
  rewrite <- (rev_involutive l).
  induction (rev l).
   simpl.
   congruence.
  simpl.
  intros.
  destruct l0.
   simpl in *.
   injection H.
   intros ; subst.
   f_equal.
   omega.
  simpl in *.
  rewrite app_ass in *.
  simpl in *.
  destruct (non_virtual_subobject_offset_app_recip H).
  destruct H0.
  generalize (IHl0 _ _ H0 accu').
  intros.
  rewrite (non_virtual_subobject_offset_app H2).
  revert H1.
  simpl.
  destruct ((offsets) ! i) ; try congruence.
  destruct ((non_virtual_direct_base_offsets t0) ! a) ; try congruence.
  injection 1 ; intros ; subst.
  f_equal.
  omega.
Qed.

Function subobject_offset (ci : ident) (l : list ident) {struct l} : option Z :=
  match offsets ! ci with
    | None => None
    | Some o =>
      match l with
        | nil => None
        | b :: _ =>
          match (virtual_base_offsets o) ! b with
            | None => None
            | Some of => non_virtual_subobject_offset of l
          end
      end
  end.

Function array_path_offset (accu : Z) (ci : ident) (l : array_path A) {struct l} : option Z :=
  match l with
    | nil => Some accu
    | (z, (_, p), f) :: l' =>
      match offsets ! ci with
        | Some o =>
          match subobject_offset ci p with
            | Some off =>
              match LibLists.last p with
                | Some clast =>
                  match offsets ! clast with
                    | Some olast =>
                      match FieldSignature.type f with
                        | FieldSignature.Struct ci'0 _ =>
                          match assoc (FieldSignature.eq_dec (A := A)) f (field_offsets olast) with
                            | Some fo =>
                              array_path_offset (accu + z * size o + off + fo) ci'0 l' (* ci' *)
                            | _ => None
                          end
                        | _ => None
                      end
                    | _ => None
                  end
                | _ => None
              end
            | _ => None
          end
        | _ => None
      end
  end.

 Fact array_path_offset_rewrite : forall accu ci l1 (* ci'1 *) z1,
    array_path_offset accu ci l1 (* ci'1 *) = Some z1 ->
    forall accu',
      array_path_offset accu' ci l1 (* ci'1 *) = Some (z1 + accu' - accu)
      .
 Proof.
   intros until 1.
   functional induction (array_path_offset accu ci l1 (* ci'1 *)) ; try congruence.
   simpl.
   injection H ; intros ; subst.
   f_equal.
   omega.
   simpl.
   rewrite e0.
   rewrite e1.
   rewrite e2.
   rewrite e3.
   rewrite e4.
   rewrite e5.
   intros.
   rewrite (IHo H).
   f_equal.
   omega.
 Qed.

 Function relative_pointer_offset (afrom ato : ident) (apath: array_path A) (i : Z) (p : list ident) : option Z :=
   match array_path_offset 0 afrom apath (* ato *) with
     | Some z1 =>
       match offsets ! ato with
         | None => None
         | Some ofto =>
           match subobject_offset ato p with
             | Some z2 => Some (z1 + i * size ofto + z2)
             | _ => None
           end
       end
     | _ => None
   end.

(** * An alternate definition for pointers (relative to a given structure array): [relative_pointer_alt] (cf. [SubobjectOrdering] *)

(** Not useful for casts, but useful to reason with offsets. This is a nasty thing (partial induction). Cf. proof of Theorem 1. *)

 Variable hierarchy : PTree.t (Class.t A).

 Function relative_pointer_alt_offset (rpa: relative_pointer_alt A) (from : ident) (ato : ident) : option Z :=
   match rpa with
     | relative_pointer_alt_intro i' (h', p') f' =>
       match offsets ! from with
         | None => None
         | Some ofrom =>
           match subobject_offset from p' with
             | Some of =>
               match f' with
                 | None => Some (i' * size ofrom + of)
                 | Some (f, a, i, (_, p)) =>
                   match FieldSignature.type f with
                     | FieldSignature.Struct afrom _ =>                       
                       match LibLists.last p' with
                         | Some pto =>
                           match offsets ! pto with
                             | None => None
                             | Some opto =>
                               match assoc (FieldSignature.eq_dec (A := A)) f (field_offsets opto) with
                                 | Some fo =>
                                   match relative_pointer_offset afrom ato a i p with
                                     | Some o => Some (i' * size ofrom + of + fo + o)
                                     | _ => None
                                   end
                                 | _ => None
                               end
                           end
                         | _ => None
                       end
                     | _ => None
                   end
               end
             | _ => None
           end
       end
   end.

 Fact relative_pointer_alt_offset_correct :  forall afrom zfrom a ato i h' p' pto,
   valid_relative_pointer hierarchy afrom zfrom a ato i h' p' pto ->
   forall of,
     relative_pointer_offset afrom ato a i p' = Some of ->
     relative_pointer_alt_offset (relative_pointer_alt_of_relative_pointer a  i (h', p')) afrom ato = Some of.
 Proof.
   inversion 1; subst.
   functional inversion 1; subst.
   inversion H0; subst; simpl.
    rewrite H7.
    rewrite H8.
    simpl in H6.
    injection H6 ; intros ; subst; simpl; reflexivity.
   functional inversion H6; subst.
   rewrite H21.
   rewrite H24.
   rewrite H28.
   rewrite H26.
   rewrite H27.
   rewrite H29.
   unfold relative_pointer_offset.
   rewrite (array_path_offset_rewrite X).
   rewrite H7.
   rewrite H8.
   f_equal; omega.
 Qed.

(** * Soundness conditions (4.5) *)

(** ** Sizes, field separation, field alignment and dynamic type data (4.5.1, 4.5.2, 4.5.3, 4.5.4) *)

(** Some conditions are considered guard conditions, e.g.:
   - an alignment is positive
   - an offset is nonnegative
   - the offset of a direct non-virtual base B within C exists if and only if B is actually a direct non-virtual base of C
*)

  Notation Is_empty := (is_empty OP hierarchy) (only parsing).

  Notation Is_dynamic := (is_dynamic OP hierarchy) (only parsing).
(*
  Notation Dynamic_type_data_size := (dynamic_type_data_size PF) (only parsing).

  Notation Dynamic_type_data_align := (dynamic_type_data_align PF) (only parsing).
*)


  Record class_level_prop (ci : ident) (o : t) : Prop := class_level_intro {

    (** 4.3 *)

    primary_base_dynamic : forall b,
      primary_base o = Some b ->
      Is_dynamic b
      ;
    (** Guard *)
    primary_base_offsets_exist : forall b,
      primary_base o = Some b ->
      offsets ! b <> None
      ;
    (** 4.3 *)
    primary_base_exist_dynamic :
      primary_base o <> None ->
      Is_dynamic ci
      ;
    (** Guard *)
    non_virtual_direct_base_offsets_exist :
      forall c,
        hierarchy ! ci = Some c ->
        forall bi,
          In (Class.Inheritance.Repeated, bi) (Class.super c) ->
          (non_virtual_direct_base_offsets o) ! bi <> None
          ;
    (** Guard *)
    non_virtual_direct_base_offsets_guard :
      forall bi,
        (non_virtual_direct_base_offsets o) ! bi <> None ->
        forall c,
          hierarchy ! ci = Some c ->
          In (Class.Inheritance.Repeated, bi) (Class.super c)
          ;
    (** C21 *)
    non_virtual_primary_base_offset : forall b,
      primary_base o = Some b ->
      (non_virtual_direct_base_offsets o) ! b = Some 0
      ;
    (** Guard *)
    non_virtual_direct_base_offsets_low_bound :
      forall bi of,
        (non_virtual_direct_base_offsets o) ! bi = Some of ->
        0 <= of
        ;
    (** C20 *)
    non_virtual_direct_base_offsets_dynamic_type_data_size :
      Is_dynamic ci ->
      primary_base o = None ->
      forall bi,
        (Is_empty bi -> False) ->
        forall of,
        (non_virtual_direct_base_offsets o) ! bi = Some of ->
        dynamic_type_data_size PF <= of
        ;
    (** C16 *)
    non_virtual_align_dynamic :
      Is_dynamic ci ->
      (dynamic_type_data_align PF | non_virtual_align o)
      ;
    (** C15 part 1/2 *)
    non_virtual_direct_base_offsets_align : forall  bi of,
      (non_virtual_direct_base_offsets o) ! bi = Some of ->
      forall bo,
        offsets ! bi = Some bo ->
        (non_virtual_align bo | of)
        ;
    (** C6 *)
    non_virtual_direct_base_nonempty_data_non_overlap : forall bi1 of1,
      (non_virtual_direct_base_offsets o) ! bi1 = Some of1 ->
      (Is_empty bi1 -> False) ->
      forall bi2 of2,
      (non_virtual_direct_base_offsets o) ! bi2 = Some of2 ->
      (Is_empty bi2 -> False) ->
      bi1 <> bi2 ->
      forall o1, offsets ! bi1 = Some o1 ->
        forall o2, offsets ! bi2 = Some o2 ->
      of1 + non_virtual_data_size o1 <= of2 \/
      of2 + non_virtual_data_size o2 <= of1
      ;
    (** C7 *)
    non_virtual_direct_base_offsets_nonempty_high_bound : 
      forall bi,
        (Is_empty bi -> False) ->
        forall of,
        (non_virtual_direct_base_offsets o) ! bi = Some of ->
        forall bo,
          offsets ! bi = Some bo ->
          of + non_virtual_data_size bo <= own_fields_offset o
          ;
    (** Guard *)
    own_fields_offset_low_bound :
      0 <= own_fields_offset o
      ;
    (** C19 *)
    own_fields_offset_dynamic_low_bound :
      Is_dynamic ci ->
      dynamic_type_data_size PF <= own_fields_offset o
      ;
    (** Guard *)
    field_offsets_exist : 
      forall c,
        hierarchy ! ci = Some c ->
        forall f,
          In f (Class.fields c) ->
          assoc (FieldSignature.eq_dec (A := A)) f (field_offsets o) <> None
          ;
    (** Guard *)
    field_offsets_guard :
      forall f,
        assoc (FieldSignature.eq_dec (A := A)) f (field_offsets o) <> None ->
        forall c,
          hierarchy ! ci = Some c ->
          In f (Class.fields c)
          ;
    (** Guard *)
    field_offsets_low_bound :
      forall f fi,
        assoc (FieldSignature.eq_dec (A := A)) f (field_offsets o) = Some fi ->
        0 <= fi
        ;
    (** C8 *)
    field_offsets_nonempty_low_bound :
      forall f fi,
        assoc (FieldSignature.eq_dec (A := A)) f (field_offsets o) = Some fi ->
        (forall ty n, FieldSignature.type f = FieldSignature.Struct ty n -> Is_empty ty -> False) ->        
        own_fields_offset o <= fi
        ;
    (** C14 part 1/2 *)
    field_offsets_align :
      forall f fo,
        assoc (FieldSignature.eq_dec (A := A)) f (field_offsets o) = Some fo ->
        forall al, field_align f = Some al ->
        (al | fo)
        ;
    (** C9 *)
    field_offsets_non_overlap :
      forall f1 fi1,
        assoc (FieldSignature.eq_dec (A := A)) f1 (field_offsets o) = Some fi1 ->
        forall f2 fi2,
          assoc (FieldSignature.eq_dec (A := A)) f2 (field_offsets o) = Some fi2 ->
          (forall ty n, FieldSignature.type f1 = FieldSignature.Struct ty n -> Is_empty ty -> False) ->
          (forall ty n, FieldSignature.type f2 = FieldSignature.Struct ty n -> Is_empty ty -> False) ->
          f1 <> f2 ->
          forall s1, field_data_size f1 = Some s1 ->
            forall s2, field_data_size f2 = Some s2 ->
          fi1 + s1 <= fi2 \/
          fi2 + s2 <= fi1
          ;
    (** C22 *)
    nonempty_non_virtual_data_size_positive :
      (Is_empty ci -> False) ->
      0 < non_virtual_data_size o
      ;
    (** C10 *)
    non_virtual_data_size_field_offsets :
      forall f fi,
        assoc (FieldSignature.eq_dec (A := A)) f (field_offsets o) = Some fi ->
        (forall ty n, FieldSignature.type f = FieldSignature.Struct ty n -> Is_empty ty -> False) ->
        forall s1, field_data_size f = Some s1 ->
          fi + s1 <= non_virtual_data_size o
          ;
    (** C2 *)
    non_virtual_size_field_offsets :
      forall f fi,
        assoc (FieldSignature.eq_dec (A := A)) f (field_offsets o) = Some fi ->
        forall s1, field_size f = Some s1 ->
          fi + s1 <= non_virtual_size o
          ;
    (** C11 *)
    non_virtual_data_size_own_fields_offset :
      own_fields_offset o <= non_virtual_data_size o
      ;
    (** C1 *)
    non_virtual_size_non_virtual_direct_bases : forall bi of,
      (non_virtual_direct_base_offsets o) ! bi = Some of ->
      forall bo, offsets ! bi = Some bo ->
        of + non_virtual_size bo <= non_virtual_size o
        ;
    (** C15 part 2/2 *)
    non_virtual_align_non_virtual_direct_bases : forall bi,
      (non_virtual_direct_base_offsets o) ! bi <> None ->
      forall bo,
        offsets ! bi = Some bo ->
        (non_virtual_align bo | non_virtual_align o)
        ;
    (** C14 part 2/2 *)
    non_virtual_align_fields : forall f,
      assoc (FieldSignature.eq_dec (A := A)) f (field_offsets o) <> None ->
      forall al, field_align f = Some al ->
        (al | (non_virtual_align o))
        ;
    (** Guard *)
    virtual_base_offsets_exist : forall b,
      is_virtual_base_of hierarchy b ci ->
      (virtual_base_offsets o) ! b <> None
      ;
    (** Guard *)
    virtual_base_offsets_guard : forall b,
      (virtual_base_offsets o) ! b <> None ->
      is_virtual_base_of hierarchy b ci (* ADDED : *) \/ b = ci
      ;
    (** 4.2 *)
    virtual_base_offsets_self :
      (virtual_base_offsets o) ! ci = Some 0
      ;
    (** C17 part 1/2  *)
    virtual_base_offsets_align : forall b of,
      (virtual_base_offsets o) ! b = Some of ->
      forall bo, offsets ! b = Some bo ->
        (non_virtual_align bo | of)
        ;
    (** Guard *)
    virtual_base_offsets_low_bound : forall b of,
      (virtual_base_offsets o) ! b = Some of ->
      0 <= of
      ;
    (** C12 *)
    virtual_base_offsets_nonempty_non_overlap : forall b1 of1,
      (virtual_base_offsets o) ! b1 = Some of1 ->
      forall bo1,
        offsets ! b1 = Some bo1 ->        
      forall b2 of2,
        (virtual_base_offsets o) ! b2 = Some of2 ->
        forall bo2,
          offsets ! b2 = Some bo2 ->
          (Is_empty b1 -> False) ->
          (Is_empty b2 -> False) ->
          b1 <> b2 ->          
          of1 + non_virtual_data_size bo1 <= of2 \/
          of2 + non_virtual_data_size bo2 <= of1
          ;
    (** C13 *)
    virtual_base_offsets_data_size : forall bi of,
      (virtual_base_offsets o) ! bi = Some of ->
      (Is_empty bi -> False) ->
      forall bo,
        offsets ! bi = Some bo ->
        of + non_virtual_data_size bo <= data_size o
        ;
    (** C4 *)
    data_size_high_bound :
      data_size o <= size o
      ;
    (** C3 *)
    virtual_base_offsets_high_bound : forall bi of,
      (virtual_base_offsets o) ! bi = Some of ->
      forall bo,
        offsets ! bi = Some bo ->
      of + non_virtual_size bo <= size o
      ;
    (** C17 part 2/2 *)
    align_virtual_base_offsets_align : forall b,
      (virtual_base_offsets o) ! b <> None ->
      forall bo, offsets ! b = Some bo ->
        (non_virtual_align bo | align o)
        ;
    (** C18 *)
    align_size :
      (align o | size o)
      ;
    (** Guard *)
    align_low_bound :
      0 < align o
      ;
    (** Guard *)
    non_virtual_align_low_bound :
      0 < non_virtual_align o
      ;
    (** C5 *)
    non_virtual_size_positive :
      0 < non_virtual_size o
  }.

Hypothesis Hhier : Well_formed_hierarchy.prop hierarchy.

Hypothesis intro : forall ci o, offsets ! ci = Some o -> class_level_prop ci o.

Hypothesis guard : forall ci, offsets ! ci <> None -> hierarchy ! ci <> None.


(** * Existence theorems *)

Section Exist.


(** Assume that the relevant data have been computed by the layout algorithm for all defined classes below some limit *)

Variable cilimit : ident.

Hypothesis exist : forall ci, Plt ci cilimit -> hierarchy ! ci <> None -> offsets ! ci <> None.


Fact is_valid_repeated_subobject_offset_exist :
  forall l a l', l = a :: l' -> is_valid_repeated_subobject hierarchy l = true ->
    Plt a cilimit ->
    forall accu, non_virtual_subobject_offset accu l <> None.
Proof.
  induction l ; simpl ; try congruence.
  injection 1 ; intros until 2; subst.
  case_eq (hierarchy ! a0) ; try congruence.
  intros until 1.
  destruct l' ; try congruence.
  destruct (In_dec super_eq_dec (Class.Inheritance.Repeated, i) (Class.super t0)) ; try congruence.
  intros until 2.
  assert (hierarchy ! a0 <> None) by congruence.
  assert ((offsets) ! a0 <> None) by eauto using exist.
  case_eq ((offsets) ! a0) ; try congruence.
  intros until 1.  
  assert ((non_virtual_direct_base_offsets t1) ! i <> None) by eauto using non_virtual_direct_base_offsets_exist.
  case_eq ((non_virtual_direct_base_offsets t1) ! i) ; try congruence.
  intros.
  eapply IHl.
  reflexivity.
  assumption.
  eauto using Plt_trans, Well_formed_hierarchy.well_founded.
Qed.

(* Corollary *) Fact non_virtual_subobject_offset_exist : forall from,
  Plt from cilimit ->
  forall p to,
    path hierarchy to p from Class.Inheritance.Repeated ->
      forall accu, non_virtual_subobject_offset accu p <> None.
Proof.
  inversion 2 ; subst ; eauto using (is_valid_repeated_subobject_offset_exist).
Qed.

Fact subobject_offset_exist : forall from,
  Plt from cilimit ->
  forall p to h,
    path hierarchy to p from h ->
    subobject_offset from p <> None.
Proof.
  intros.
  unfold subobject_offset.
  assert (hierarchy ! from <> None) by eauto using path_defined_from.
  assert (offsets ! from <> None) by eauto.
  case_eq (offsets ! from) ; try congruence.  
  intros.
  destruct p.
   generalize (path_path0 H0).
   inversion 1; discriminate.
  generalize (path_path1 H0).
  inversion 1.
   injection H5 ; intros ; subst.
   rewrite (virtual_base_offsets_self (intro H3)).
   eauto using non_virtual_subobject_offset_exist.
  subst.
  inversion H6 ; subst.
  injection H7 ; intros ; subst.
  generalize (virtual_base_offsets_exist (intro H3) H5).
  intros.
  case_eq ((virtual_base_offsets t0) ! base) ; try congruence.
  intros.
  eauto using non_virtual_subobject_offset_exist, Plt_trans, Well_formed_hierarchy.is_virtual_base_of_lt.
Qed.

Fact array_path_offset_exist : forall from zfrom to zto p,
  valid_array_path hierarchy to zto from zfrom p ->
  Plt from cilimit ->
  hierarchy ! to <> None ->
  forall accu,
    array_path_offset accu from p <> None
.
Proof.
  induction 1 ; subst ; simpl.
  intros.
  destruct (peq c c) ; try congruence.
  intros.
  generalize (path_defined_from H1).
  intros.
  assert (offsets ! from <> None) by eauto.
  case_eq (offsets ! from) ; try congruence.
  intros.
  generalize (subobject_offset_exist H6 H1).
  intro.
  case_eq (subobject_offset from l) ; try congruence.
  intros.
  rewrite (path_last H1).
  assert (hierarchy ! through <> None) by congruence.
  assert (Plt through cilimit) by eauto using Ple_Plt_trans, Well_formed_hierarchy.path_le.
  assert (offsets ! through <> None) by eauto.
  case_eq (offsets ! through) ; try congruence.
  intros.
  rewrite H4.
  generalize (field_offsets_exist (intro H16) H2 H3).
  intros.
  case_eq (assoc (FieldSignature.eq_dec (A := A)) fs (field_offsets t1)) ; try congruence.
  intros.
  eauto using Well_formed_hierarchy.well_founded_struct, Plt_trans, Plt_Ple_trans.
Qed.

(* Corollary *) Lemma relative_pointer_offset_exist : forall afrom,
  Plt afrom cilimit ->
  forall zfrom a ato i h' p' pto,
    valid_relative_pointer hierarchy afrom zfrom a ato i h' p' pto ->
    relative_pointer_offset afrom ato a i p' <> None.
Proof.
  inversion 2; subst.
  unfold relative_pointer_offset.
  generalize (path_defined_from H4).
  intro.
  generalize (array_path_offset_exist H1 H H5 (accu := 0)).
  case_eq (array_path_offset 0 afrom a); try congruence.
  intros.
  assert (Plt ato cilimit) by eauto using Ple_Plt_trans, Well_formed_hierarchy.array_path_le.
  assert (offsets ! ato <> None) by eauto.
  case_eq (offsets ! ato); try congruence.
  intros.
  generalize (subobject_offset_exist H8 H4).
  case_eq (subobject_offset ato p'); congruence.
Qed.

Fact non_virtual_path_field_align_exist : forall l from to,
  path hierarchy to l from Class.Inheritance.Repeated ->
    Plt from cilimit ->
    forall hto, hierarchy ! to = Some hto ->      
      forall f, In f (Class.fields hto) ->
        field_align f <> None.
Proof.
 intros.
 unfold field_align.
 case_eq (FieldSignature.type f).
  congruence.
 intros.
 case_eq (offsets ! struct).
  congruence.
 intros.
 apply False_rect.
 eapply exist.
 3 : eassumption.
 eapply Plt_Ple_trans.
 eauto using Well_formed_hierarchy.well_founded_struct.
 eauto using Plt_Ple, Ple_Plt_trans, Well_formed_hierarchy.path_le.
 eauto using Well_formed_hierarchy.complete_struct.
Qed.

(* Corollary *) Fact path_field_align_exist : forall l from to h,
  path hierarchy to l from h ->
    Plt from cilimit ->
    forall hto, hierarchy ! to = Some hto ->
      forall f, In f (Class.fields hto) ->
        field_align f <> None.
Proof.
 intros.
 destruct h.
  eauto using non_virtual_path_field_align_exist.
 generalize (path_path1 H).
 inversion 1; subst.
 assert (Plt base cilimit) by eauto using Plt_trans, Well_formed_hierarchy.is_virtual_base_of_lt.
 eauto using non_virtual_path_field_align_exist.
Qed.

(* Corollary *) Lemma relative_pointer_field_align_exist : forall afrom,
  Plt afrom cilimit ->
  forall zfrom a ato i h' p' pto,
    valid_relative_pointer hierarchy afrom zfrom a ato i h' p' pto ->
    forall hto, hierarchy ! pto = Some hto ->
      forall f, In f (Class.fields hto) ->
        field_align f <> None.
Proof.
  inversion 2; subst.
  clear H0.
  revert H i H2 H3.
  induction H1.
   intros; eauto using path_field_align_exist.
  intro.
  assert (Plt by cilimit).
   eauto using Plt_trans, Ple_Plt_trans, Well_formed_hierarchy.well_founded_struct, Well_formed_hierarchy.path_le.
  eauto.
Qed.

End Exist.

(** * Proofs of alignment properties (5.2) *)

Section Alignment.

Fact non_virtual_path_align : forall l from to,
  path hierarchy to l from Class.Inheritance.Repeated ->
    forall accu of, non_virtual_subobject_offset accu l = Some of ->
      forall ofrom, offsets ! from = Some ofrom ->
        forall oto, offsets ! to = Some oto ->
        (non_virtual_align oto | non_virtual_align ofrom) /\
        ((non_virtual_align oto | accu) -> (non_virtual_align oto | of)).
Proof.
  intros until 2.
  generalize (path_last H).
  revert H0.
  inversion H; subst.
  clear lt H H1 H2.
  var (from :: lf).
  intro.
  revert x from lf H.
  functional induction (non_virtual_subobject_offset accu v); try congruence.
   injection 1; intro; subst.
   injection 1; intros until 2; subst.
   injection 1; intro; subst.
   intros ? H1.
   rewrite H1.
   injection 1; intro; subst.
   split.
    apply Zdivide_refl.
   tauto.
  injection 2; intros until 2; subst.
  functional inversion 1; subst.
  intros.
  assert (offsets ! b <> None).
   functional inversion x; subst; try congruence.
   simpl in H6; congruence.
  case_eq (offsets ! b); try congruence.
  intros.
  destruct (IHo x _ _ (refl_equal _) H6 _ H3 _ H1).
  asplit.
   apply Zdivide_trans with (non_virtual_align t0).
    assumption.
   assert ((non_virtual_direct_base_offsets ofrom) ! b <> None) by congruence.
   eauto using non_virtual_align_non_virtual_direct_bases.
  intros.
  apply H7.
  apply Zdivide_plus_r.
  assumption.
  eauto using Zdivide_trans, non_virtual_direct_base_offsets_align.
Qed.

Fact path_align : forall l from to h,
  path hierarchy to l from h ->
    forall of, subobject_offset from l = Some of ->
      forall ofrom, offsets ! from = Some ofrom ->
        forall oto, offsets ! to = Some oto ->
          (non_virtual_align oto | align ofrom) /\
          (non_virtual_align oto | of).
Proof.
  functional inversion 2; subst.
  generalize (path_cons_repeated H).
  intros.
  assert (offsets ! b <> None).
   functional inversion H1; try congruence.
   subst. generalize (path_last H3). simpl. congruence.
  case_eq (offsets ! b); try congruence. intros.  destruct (non_virtual_path_align H3 H1 H8 H6). replace o with ofrom in * by congruence.
 split.
   assert ((virtual_base_offsets ofrom) ! b <> None) by congruence.
   eauto using align_virtual_base_offsets_align, Zdivide_trans.
  eauto using virtual_base_offsets_align, Zdivide_trans.
Qed.  

Lemma relative_pointer_align : forall afrom zfrom a ato i h' p' pto,
  valid_relative_pointer hierarchy afrom zfrom a ato i h' p' pto ->
  forall of,
    relative_pointer_offset afrom ato a i p' = Some of ->
    forall ofrom, offsets ! afrom = Some ofrom ->
      forall oto, offsets ! pto = Some oto ->
        (non_virtual_align oto | align ofrom) /\
        (non_virtual_align oto | of).
Proof.
  inversion 1; subst.
  clear H.
  functional inversion 1; subst.
  clear H.
  revert i h' p' pto H1 H2 H3 z1 ofto z2 H5 H6 H7.
  induction H0.
   simpl in *.
   injection 4; intros; subst.
   replace ofrom with ofto in * by congruence.
   destruct (path_align H3 H7 H6 H9).
   split.
    assumption.
   apply Zdivide_plus_r; eauto.
   apply Zdivide_plus_r; eauto using Zdivide_0.
   apply Zdivide_mult_r.
   eauto using  align_size, Zdivide_trans.
  functional inversion 4; subst.
  rewrite H16.
  injection 3; intro; subst.
  intros.
  generalize (path_last H1).
  intros.
  replace clast with through in * by congruence.
  replace ci'0 with by in * by congruence.
  replace _x0 with by_n in * by congruence.
  generalize (array_path_offset_rewrite X 0).
  intros.
  assert (offsets ! by <> None).
  functional inversion X; try congruence.
  subst. inversion H5; congruence.
  case_eq (offsets ! by); try congruence.
  intros.
  destruct (IHvalid_array_path _ _ _ _ H6 H7 H8 _ _ _ H15 H10 H11 _ H18 _ H13).
  generalize (field_offsets_align (intro H22) H24).
  unfold field_align.
  rewrite H23.
  rewrite H18.
  intro.
  generalize (H26 _ (refl_equal _)).
  intros.
  assert ( assoc (FieldSignature.eq_dec (A := A)) fs (field_offsets olast) <> None) by congruence.
  generalize (non_virtual_align_fields (intro H22) H28).
  unfold field_align.
  rewrite H23.
  rewrite H18.
  intros.
  generalize (H29 _ (refl_equal _)).
  intros.
  destruct (path_align H1 H19 H16 H22).
  split.
   eauto using Zdivide_trans.
  replace (z1 + i * size ofto + z2) with (( z1 + 0 - (0 + p * size ofrom + off + fo) + i * size ofto + z2) + (p * size ofrom + off + fo)) by omega.
  apply Zdivide_plus_r.
  assumption.
  apply Zdivide_plus_r; eauto using Zdivide_trans.
  apply Zdivide_plus_r; eauto using Zdivide_trans.
  apply Zdivide_mult_r.
  eauto 6 using Zdivide_trans, align_size.
Qed.

(** 5.2 Theorem 2 *)
Theorem field_align_prop : forall afrom zfrom a ato i h' p' pto,
  valid_relative_pointer hierarchy afrom zfrom a ato i h' p' pto ->
  forall of,
    relative_pointer_offset afrom ato a i p' = Some of ->
    forall ofrom, offsets ! afrom = Some ofrom ->
      forall oto, offsets ! pto = Some oto ->
        forall f fa, field_align f = Some fa ->
          forall foff, assoc (FieldSignature.eq_dec (A := A)) f (field_offsets oto) = Some foff ->
            (fa | align ofrom) /\ (fa | of + foff).
Proof.
  intros.
  destruct (relative_pointer_align H H0 H1 H2).
  generalize (field_offsets_align (intro H2) H4 H3).
  intros.
  assert (assoc (FieldSignature.eq_dec (A := A)) f (field_offsets oto) <> None) by congruence.
  generalize (non_virtual_align_fields (intro H2) H8 H3).
  intros; eauto using Zdivide_trans, Zdivide_plus_r.
Qed.

(** 5.2 Theorem 3 *)  
Theorem dynamic_align : forall afrom zfrom a ato i h' p' pto,
  valid_relative_pointer hierarchy afrom zfrom a ato i h' p' pto ->
  forall of,
    relative_pointer_offset afrom ato a i p' = Some of ->
    forall ofrom, offsets ! afrom = Some ofrom ->
    offsets ! pto <> None ->
    Is_dynamic pto ->
    (dynamic_type_data_align PF | align ofrom) /\
    (dynamic_type_data_align PF | of).
Proof.
  intros.
  case_eq (offsets ! pto); try congruence.
  intros.
  destruct (relative_pointer_align H H0 H1 H4).
  eauto 8 using Zdivide_trans, non_virtual_align_dynamic.
Qed.
  

End Alignment.

(** * Total size inclusion *)

Section Bounds.

Lemma size_positive : forall c o, offsets ! c = Some o ->
  0 < size o.
Proof.
  intros.
  generalize (virtual_base_offsets_high_bound (intro H) (virtual_base_offsets_self (intro H)) H).
  generalize (non_virtual_size_positive (intro H)).
  omega.
Qed.
  
Fact non_virtual_subobject_offset_size : forall l to from,
  path hierarchy to l from Class.Inheritance.Repeated ->
    forall accu o, non_virtual_subobject_offset accu l = Some o ->
      accu <= o /\
        forall ofrom, offsets ! from = Some ofrom ->
          forall oto, offsets ! to = Some oto ->
            o + non_virtual_size oto <= accu + non_virtual_size ofrom.
Proof.
  induction l; inversion 1; subst; try discriminate.
  injection H0; intros; subst.
  functional inversion H2; subst.
   destruct lt ; simpl in H1.
    injection H1; intros; subst.
    functional inversion H5; subst.
    split.
    omega.
    intros.
    replace oto with ofrom by congruence.
    omega.
   destruct lt; simpl in H1; discriminate.
  functional inversion H5; subst.
  rewrite H13.
  destruct lt; simpl in H1; try congruence.
  injection H1; intros; subst.
  assert (path hierarchy to (id2 :: l3) id2 Class.Inheritance.Repeated).
   eleft; eauto.
  generalize (non_virtual_direct_base_offsets_low_bound (intro H13) H14).
  intros.
  generalize (IHl _ _ H4 _ _ X0).
  destruct 1.
  split.
  omega.
  injection 1; intros; subst.
  assert (offsets ! id2 <> None).
   functional inversion X0; subst; try congruence.
   generalize (path_last H4).
   simpl.
   congruence.
  case_eq (offsets ! id2); try congruence.
  intros.
  generalize (non_virtual_size_non_virtual_direct_bases (intro H13) H14 H16).
  generalize (H9 _ H16 _ H15).
  omega.
Qed.

Fact subobject_offset_size : forall l to from h,
  path hierarchy to l from h ->
  forall so, subobject_offset from l = Some so ->    
    0 <= so /\ 
    forall ofrom, offsets ! from = Some ofrom ->
      forall oto, offsets ! to = Some oto ->        
        so + non_virtual_size oto <= size ofrom
    .
Proof.
  functional inversion 2.
  subst.
  generalize (virtual_base_offsets_low_bound (intro H2) H5).
  intros.
  generalize (path_cons_repeated H).
  intros.
  generalize (non_virtual_subobject_offset_size H4 H1).
  destruct 1.
  split.
   omega.
  rewrite H2.
  injection 1; intros; subst.
  assert (offsets ! b <> None).
   functional inversion H1; subst.
   inversion H4 ; subst.
   destruct lt.
    simpl in * ; congruence.
   destruct lt ; simpl in * ; congruence.
   congruence.
  case_eq (offsets ! b) ; try congruence.
  intros.
  generalize (H7 _ H11 _ H10).
  intros.
  eapply Zle_trans.
  eassumption.
  eapply virtual_base_offsets_high_bound.
  eapply intro.
  eassumption.
  eassumption.
  assumption.
Qed.

Fact array_path_offset_size : forall to to_n from from_n l,
  valid_array_path hierarchy to to_n from from_n l ->
  forall accu z, array_path_offset accu from l = Some z ->
    accu <= z /\ 
    forall ofrom, offsets ! from = Some ofrom ->
      forall oto, offsets ! to = Some oto ->
        z + to_n * size oto <= accu + from_n * size ofrom
.
Proof.
 induction 1.
  simpl.
  injection 1; intros; subst.
  split.
   omega.
  intros until 1.
  rewrite H2.
  injection 1; intros; subst.
  cut (to_n * size oto <= from_n * size oto).
   omega.
  apply Zmult_le_compat_r.
  assumption.
  generalize (size_positive H2).
  omega.
 intros ? ?.
 functional inversion 1; subst.
 rewrite H13.
  rewrite (path_last H1) in H18.
  injection H18; intros; subst.
  rewrite H4 in H20.
  injection H20; intros; subst.
  generalize (IHvalid_array_path _ _ X).
  destruct 1.
  assert (0 <= p * size o).
   generalize (size_positive H13).
   intros.
   eapply Zmult_ge.
   assumption.
   omega.
  functional inversion H16.
  subst.
  replace o0 with o in * by congruence.
  generalize (virtual_base_offsets_low_bound (intro H13) H15).
  intros.
  generalize (path_cons_repeated H1).
  intros.
  generalize (non_virtual_subobject_offset_size H14 H10).
  destruct 1.
  generalize (field_offsets_low_bound (intro H19) H21).
  intros.
  split.
   omega.
  injection 1; intros; subst.
  assert (offsets ! b <> None).
   functional inversion H10; subst.
   inversion H14; subst.
    destruct lt; simpl in *; try congruence.
    destruct lt; simpl in *; congruence.
   congruence.
  case_eq (offsets ! b); try congruence.
  intros.
  generalize (H22 _ H27 _ H19).
  intros.
  generalize (virtual_base_offsets_high_bound (intro H11) H15 H27).
  intros.
  generalize (non_virtual_size_field_offsets (intro H19) H21).
  unfold field_size.
  rewrite H4.
  assert (offsets ! ci'0 <> None).
   functional inversion X; subst ; try congruence.
   inversion H5; subst; congruence.
  case_eq (offsets ! ci'0); try congruence.
  intros.
  generalize (H32 _ (refl_equal _)).
  rewrite Zmult_distr_1.
  replace (Zpos _x0 - 1 + 1) with (Zpos _x0) by omega.
  intros.
  generalize (H8 _ H31 _ H26).
  intros.
  cut (p * size ofrom + size ofrom <= from_n * size ofrom).
   omega.
  rewrite Zmult_distr_1.
  apply Zmult_le_compat_r.
  omega.
  generalize (size_positive H13).
  omega.
Qed.

Lemma relative_pointer_offset_size : forall afrom zfrom a ato i h' p' pto,
  valid_relative_pointer hierarchy afrom zfrom a ato i h' p' pto ->
  forall of, relative_pointer_offset afrom ato a i p' = Some of ->
    0 <= of /\ forall ofrom,
      offsets ! afrom = Some ofrom ->
      forall opto, offsets ! pto = Some opto ->
        of + non_virtual_size opto <= zfrom * size ofrom.
Proof.
  inversion 1; subst.
  functional inversion 1; subst.
  destruct (subobject_offset_size H3 H8).
  destruct (array_path_offset_size H0 H6).
  generalize (size_positive H7).
  intros.
  assert (0 <= size ofto) by omega.
  generalize (Zmult_ge H1 H13). 
  intros.
  split.
   omega.
  intros.
  generalize (H9 _ H7 _ H16).
  generalize (H11 _ H15 _ H7).
  intros.
  cut (i * size ofto + size ofto <= zto * size ofto).
   omega.
  pattern (size ofto) at 2.
  replace (size ofto) with (1 * size ofto) by omega.
  rewrite <- (Zmult_plus_distr_l).
  apply Zmult_le_compat_r.
  omega.
  omega.
Qed.

Fact relative_pointer_alt_offset_size : forall i h p f afrom zfrom ato pto,
  valid_relative_pointer_alt hierarchy afrom zfrom ato pto (relative_pointer_alt_intro i (h, p) f) ->
  forall ofrom, offsets ! afrom = Some ofrom ->
    forall op, subobject_offset afrom p = Some op ->
      forall of, relative_pointer_alt_offset (relative_pointer_alt_intro i (h, p) f) afrom ato = Some of ->
        i * size ofrom + op <= of /\
        forall through, last p = Some through ->
          forall othrough, offsets ! through = Some othrough ->
            forall opto, offsets ! pto = Some opto ->
              of + non_virtual_size opto <= i * size ofrom + op + non_virtual_size othrough
.
Proof.
inversion 1; subst.
intros until 2.
unfold relative_pointer_alt_offset.
rewrite H0.
rewrite H1.
destruct f.
 Focus 2.
  injection 1; intros; subst.
  split.
   omega.
  invall; subst.
  rewrite (path_last H6).
  injection 1; intro; subst.
  intros until 1.
  rewrite H7.
  injection 1; intros; subst.
  omega.
 destruct p0.
 destruct p0.
 destruct p0.
 destruct p1.
 invall.
 rewrite H7.
 rewrite (path_last H6).
 case_eq (offsets ! through); try congruence.
 intros until 1.
 case_eq (assoc (FieldSignature.eq_dec (A := A)) t0 (field_offsets t2)); try congruence.
 intros until 1.
 case_eq (relative_pointer_offset x0 ato a z l); try congruence.
 functional inversion 1; subst.
 injection 1; intros; subst.
 generalize (field_offsets_low_bound (intro H8) H10).
 intros.
 inversion H9; subst.
 generalize (array_path_offset_size H17 H13).
 destruct 1.
 generalize (size_positive H14).
 intros.
 assert (0 <= z * size ofto).
  eapply Zmult_ge; omega.
 generalize (subobject_offset_size H20 H15).
 destruct 1.
 split.
  omega.
 injection 1; intro; subst.
 rewrite H8.
 injection 1; intro; subst.
 intros.
 assert (offsets ! x0 <> None).
  functional inversion H13; subst; try congruence.
  inversion H17; subst; congruence.
 case_eq (offsets ! x0); try congruence.
 intros.
 generalize (H22 _ H31 _ H14).
 intros.
 generalize (H26 _ H14 _ H29).
 intros.
 eapply Zle_trans with (  i * size ofrom + op + z0 + (z2 + (z * size ofto + size ofto))).
  omega. 
 rewrite Zmult_distr_1.
 eapply Zle_trans with  (  i * size ofrom + op + z0 + (z2 + (zto * size ofto))).
  cut ((z + 1) * size ofto <= zto * size ofto).
   omega.
  eapply Zmult_le_compat_r.
   omega.
  generalize (size_positive H14).
  omega.
 generalize (non_virtual_size_field_offsets (intro H8) H10).
 unfold field_size.
 rewrite H7.
 rewrite H31.
 rewrite Zmult_distr_1.
 replace (Zpos x1 - 1 + 1) with (Zpos x1) by omega.
 intros.
 generalize (H34 _ (refl_equal _)).
 omega.
Qed.

End Bounds.

Let Is_empty_prop := is_empty_prop OP hierarchy.

Section Empty_base_offsets.

(** * Specification of the sets of (non-virtual) empty base offsets (4.5.5) *)

Inductive non_virtual_empty_base_offset : ident -> ident -> Z -> Prop :=
| non_virtual_empty_base_offset_self : forall ci,
  Is_empty ci ->
  forall z, z = 0 ->
  non_virtual_empty_base_offset ci ci z
| non_virtual_empty_base_offset_non_virtual_base : forall ci oc,
  offsets ! ci = Some oc ->
  forall ci' o',
    (non_virtual_direct_base_offsets oc) ! ci' = Some o' ->
    forall b o,
      non_virtual_empty_base_offset ci' b (o - o') ->
      non_virtual_empty_base_offset ci b o
| non_virtual_empty_base_offset_field : forall ci oc,
  offsets ! ci = Some oc ->
  forall f fo,
    assoc (FieldSignature.eq_dec (A := A)) f (field_offsets oc) = Some fo ->
    forall cif arraysize, FieldSignature.type f = FieldSignature.Struct cif arraysize ->
      forall ocf, offsets ! cif = Some ocf ->
        forall ai, 0 <= ai -> ai < Zpos arraysize ->
          forall b x,
            empty_base_offset cif b (x - fo - ai * size ocf) ->
            non_virtual_empty_base_offset ci b x

with empty_base_offset : ident -> ident -> Z -> Prop :=
| empty_base_offset_intro : forall ci oc,
  offsets ! ci = Some oc ->
  forall ci' o', (virtual_base_offsets oc) ! ci' = Some o' ->
    forall b x,
      non_virtual_empty_base_offset ci' b (x - o') ->
      empty_base_offset ci b x
.

Scheme empty_base_offset_rec_mu := Minimality for empty_base_offset Sort Prop
with non_virtual_empty_base_offset_rec_mu := Minimality for non_virtual_empty_base_offset Sort Prop.

Combined Scheme combined_empty_base_offset_rec from empty_base_offset_rec_mu, non_virtual_empty_base_offset_rec_mu.

Fact non_virtual_empty_base_offset_intro_non_virtual_path : 
  forall from,
    forall p by,
      path hierarchy by p from Class.Inheritance.Repeated ->
        forall of accu,
          non_virtual_subobject_offset accu p = Some of ->
          forall to oz,
            non_virtual_empty_base_offset by to oz ->
            non_virtual_empty_base_offset from to (oz + of - accu)
            .
Proof.
  intros until p.
  revert from.
  induction p.
   inversion 1.
   discriminate.
  inversion 1.
  injection H0 ; intros until 2 ; subst.
  destruct lt.
   simpl in H1.
   injection H1 ; intros until 2 ; subst.
   simpl.
   injection 1 ; intros ; subst.
   replace (oz + of - of) with oz by omega.
   assumption.
  simpl in H1.
  injection H1 ; intros until 2.
  subst i ; subst.
  functional inversion H2.
   destruct lt ; simpl in * ; discriminate.
  subst.
  assert (path hierarchy by (lt ++ by :: nil) id2 Class.Inheritance.Repeated).
   eleft.
   symmetry ; eassumption.
   reflexivity.
   congruence.
  rewrite H4.
  clear H9.
  simpl.
  rewrite <- H4.
  rewrite -> H4.
  case_eq (offsets ! from) ; try congruence.
  intros fo Hfo.
  case_eq ((non_virtual_direct_base_offsets fo) ! id2) ; try congruence.
  intros.
  eapply non_virtual_empty_base_offset_non_virtual_base.
  eassumption.
  eassumption.
  replace (oz + of - accu - z) with (oz + of - (accu + z)) by omega.
  eauto using Plt_trans, Well_formed_hierarchy.well_founded.
Qed.
   

Fact non_virtual_path_empty_base_offsets : forall p to (to_empty : Is_empty to) from,
  path hierarchy to p from Class.Inheritance.Repeated ->
    forall of accu,
      non_virtual_subobject_offset accu p = Some of ->
      non_virtual_empty_base_offset from to (of - accu)
.
Proof.
  intros.
  replace (of - accu) with (0 + of - accu) by omega.
  eapply non_virtual_empty_base_offset_intro_non_virtual_path.
  eassumption.
  assumption.
  constructor.
  assumption.
  reflexivity.
Qed.

(* Corollary *) Fact empty_base_offset_intro_path : forall from,
    forall p by h,
      path hierarchy by p from h ->
        forall of,
          subobject_offset from p = Some of ->
          forall to oz,
            non_virtual_empty_base_offset by to oz ->
            empty_base_offset from to (oz + of)
            .
Proof.
  functional inversion 2 ; subst.
  intros.
  generalize (path_cons_repeated H).
  intros.
  econstructor.
  eassumption.
  eassumption.
  eapply non_virtual_empty_base_offset_intro_non_virtual_path.
  eassumption.
  assumption.
  assumption.
Qed.

(* Corollary *) Fact path_empty_base_offsets : forall p to (to_empty : Is_empty to) from,
  forall h,
    path hierarchy to p from h ->
    forall of,
      subobject_offset from p = Some of ->
      empty_base_offset from to of
      .
Proof.
  intros.
  replace of with (0 + of) by omega.
  eapply empty_base_offset_intro_path.
  eassumption.
  assumption.
  constructor.
  assumption.
  reflexivity.
Qed.

Fact field_non_virtual_empty_base_offsets : forall l from to1 p1,
  path hierarchy to1 p1 from Class.Inheritance.Repeated ->
    forall accu1 z1, non_virtual_subobject_offset accu1 p1 = Some z1 ->
      forall o1, offsets ! to1 = Some o1 ->
        forall f fz, assoc (FieldSignature.eq_dec (A := A)) f (field_offsets o1) = Some fz ->
          forall to2 ars2,
            FieldSignature.type f = FieldSignature.Struct to2 ars2 ->
            forall to3 arsz3,
              valid_array_path hierarchy to3 arsz3 to2 (Zpos ars2) l ->
              forall lz,
                array_path_offset (z1 + fz) to2 l = Some lz ->
                forall o3, offsets ! to3 = Some o3 ->
                  forall x, 0 <= x -> x < arsz3 ->
                    forall to4,
                      Is_empty to4 ->
                      forall p4 h4,
                        path hierarchy to4 p4 to3 h4 ->
                        forall p4z,
                          subobject_offset to3 p4 = Some p4z ->
                          non_virtual_empty_base_offset from to4 (lz + x * size o3 + p4z - accu1)
.
Proof.
  cut (
 forall l from to1 p1,
  path hierarchy to1 p1 from Class.Inheritance.Repeated ->
    True ->
    forall accu1 z1, non_virtual_subobject_offset accu1 p1 = Some z1 ->
      forall o1, offsets ! to1 = Some o1 ->
        forall f fz, assoc (FieldSignature.eq_dec (A := A)) f (field_offsets o1) = Some fz ->
          forall to2 ars2,
            FieldSignature.type f = FieldSignature.Struct to2 ars2 ->
            forall to3 arsz3,
              valid_array_path hierarchy to3 arsz3 to2 (Zpos ars2) l ->
              forall lz,
                array_path_offset (z1 + fz) to2 l = Some lz ->
                forall o3, offsets ! to3 = Some o3 ->
                  forall x, 0 <= x -> x < arsz3 ->
                    forall to4,
                      Is_empty to4 ->
                      forall p4 h4,
                        path hierarchy to4 p4 to3 h4 ->
                        forall p4z,
                          subobject_offset to3 p4 = Some p4z ->
                          non_virtual_empty_base_offset from to4 (lz + x * size o3 + p4z - accu1)
  ).
   intros.
   eauto.
  induction l ; simpl.
  inversion 7 ; subst.
  destruct (peq to2 to2) ; try congruence.
  intros until 2.
 (* rewrite H9 in H8. *)
  injection H8 ; intros ; subst.
  replace (z1 + fz + x * size o3 + p4z - accu1) with ((fz + x * size o3 + p4z) + z1 - accu1) by omega.
  eapply non_virtual_empty_base_offset_intro_non_virtual_path.  
  eassumption.
  eassumption.
  eapply non_virtual_empty_base_offset_field.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  omega.
  replace (fz + x * size o3 + p4z - fz - x * size o3) with p4z by omega.
  eapply path_empty_base_offsets.
  assumption.  
  assert (offsets ! to1 <> None) by congruence.
  assert (hierarchy ! to1 <> None) by eauto.
  case_eq (hierarchy ! to1) ; try congruence.
  intros.
  assert (assoc (FieldSignature.eq_dec (A := A)) f (field_offsets o1) <> None) by congruence.
  generalize (field_offsets_guard (intro H2) H18 H17).
  intros.
  eauto using Plt_trans, Well_formed_hierarchy.well_founded_struct, Ple_Plt_trans, Well_formed_hierarchy.path_le.
  eassumption.

  inversion 7 ; subst.
  case_eq (offsets  ! to2) ; try congruence.
  intros until 1.
  case_eq (subobject_offset to2 l0) ; try congruence.
  intros until 1.
  case_eq (last l0) ; try congruence.
  intros until 1.
  case_eq (offsets ! i) ; try congruence.
  intros until 1.
  rewrite H17.
  case_eq (assoc (FieldSignature.eq_dec (A := A)) fs (field_offsets t1)) ; try congruence.
  intros.
  generalize (path_last H10).
  intros.
  replace i with through in * by congruence.
  functional inversion H7 ; subst.
  generalize (path_cons_repeated H10).
  intros.
  generalize (array_path_offset_rewrite H16 (z + z0)).
  replace  (lz + (z + z0) - (z1 + fz + p * size t0 + z + z0))  with (lz - z1 - fz - p * size t0) by omega.
  intro.
  refine (
    _ (IHl _ _ _ H28 I _ _ H26 _ H14 _ _ H15 _ _ H17 _ _ H18 _ H29 _ H19 _ H20 H21 _ H22 _ _ H23 _ H24)
  ).
  intros.
  replace (lz + x * size o3 + p4z - accu1) with (lz + x * size o3 + p4z - z1 + z1 - accu1) by omega.
  eapply non_virtual_empty_base_offset_intro_non_virtual_path.
  eassumption.
  eassumption.
  eapply non_virtual_empty_base_offset_field.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  2 : eassumption.
  assumption.
  econstructor.
  eassumption.
  eassumption.
  replace (
    lz + x * size o3 + p4z - z1 - fz - p * size o - of
  ) with (
    lz - z1 - fz - p * size o + x * size o3 + p4z - of
  ) by omega.
  replace o with t0 by congruence.
  assumption.
Qed.

Fact field_empty_base_offsets : forall l from to1 p1 h1,
  path hierarchy to1 p1 from h1 ->
    forall z1, subobject_offset from p1 = Some z1 ->
      forall o1, offsets ! to1 = Some o1 ->
        forall f fz, assoc (FieldSignature.eq_dec (A := A)) f (field_offsets o1) = Some fz ->
          forall to2 ars2,
            FieldSignature.type f = FieldSignature.Struct to2 ars2 ->
            forall to3 arsz3,
              valid_array_path hierarchy to3 arsz3 to2 (Zpos ars2) l ->
              forall lz,
                array_path_offset (z1 + fz) to2 l = Some lz ->
                forall o3, offsets ! to3 = Some o3 ->
                  forall x, 0 <= x -> x < arsz3 ->
                    forall to4,
                      Is_empty to4 ->
                      forall p4 h4,
                        path hierarchy to4 p4 to3 h4 ->
                        forall p4z,
                          subobject_offset to3 p4 = Some p4z ->
                          empty_base_offset from to4 (lz + x * size o3 + p4z)
.
Proof.
functional inversion 2.
subst.
intros.
generalize (path_cons_repeated H).
intros.
eauto using empty_base_offset_intro, field_non_virtual_empty_base_offsets.
Qed.

Fact combined_empty_base_offset_elim : 
  (forall from to z, empty_base_offset from to z -> (
    Is_empty to /\     
    exists p1, exists h1, exists to1,
      path hierarchy to1 p1 from h1 /\
      exists z1, subobject_offset from p1 = Some z1 /\
        ((
          to = to1 /\
          z1 = z
        ) \/      
        exists o1, offsets ! to1 = Some o1 /\
          exists f, exists fz, assoc (FieldSignature.eq_dec (A := A)) f (field_offsets o1) = Some fz /\
            exists to2, exists ars2,
              FieldSignature.type f = FieldSignature.Struct to2 ars2 /\
              exists to3, exists arsz3, exists l,
                valid_array_path hierarchy to3 arsz3 to2 (Zpos ars2) l /\
                exists lz,
                  array_path_offset (z1 + fz) to2 l = Some lz /\
                  exists o3, offsets ! to3 = Some o3 /\
                    exists x, 0 <= x /\ x < arsz3 /\
                      exists p4, exists h4,
                        path hierarchy to p4 to3 h4 /\
                        exists p4z,
                          subobject_offset to3 p4 = Some p4z /\
                          z = lz + x * size o3 + p4z
      )
  )) /\
  (forall from to z, non_virtual_empty_base_offset from to z -> (
    Is_empty to /\        
    exists to1, exists p1,
      path hierarchy to1 p1 from Class.Inheritance.Repeated /\
      exists z1, non_virtual_subobject_offset 0 p1 = Some z1 /\
        ((
          to = to1 /\
          z1 = z
        ) \/        
        exists o1, offsets ! to1 = Some o1 /\
          exists f, exists fz, assoc (FieldSignature.eq_dec (A := A)) f (field_offsets o1) = Some fz /\
            exists to2, exists ars2,
              FieldSignature.type f = FieldSignature.Struct to2 ars2 /\
              exists to3, exists arsz3, exists l,
                valid_array_path hierarchy to3 arsz3 to2 (Zpos ars2) l /\
                exists lz,
                  array_path_offset (z1 + fz) to2 l = Some lz /\
                  exists o3, offsets ! to3 = Some o3 /\
                    exists x, 0 <= x /\ x < arsz3 /\
                      exists p4, exists h4,
                        path hierarchy to p4 to3 h4 /\
                        exists p4z,
                          subobject_offset to3 p4 = Some p4z /\
                          z = (lz + x * size o3 + p4z)
        )
  )).
Proof.
  apply combined_empty_base_offset_rec.

  (* "empty_base_offset_intro". *)
  intros.
  assert ((virtual_base_offsets oc) ! ci' <> None) by congruence.
  generalize (virtual_base_offsets_guard (intro H) H3).
  intros.
  invall.
  split.
  assumption.
  assert (exists h1, path hierarchy x0 x1 ci h1).
   inversion H4.
    exists Class.Inheritance.Shared.
    econstructor ; eauto.
    subst.
    exists Class.Inheritance.Repeated.
    assumption.
  invall.
  esplit.
  esplit.
  esplit.
  split.
  eassumption.
  unfold subobject_offset at 1.
  rewrite H.
  inversion H2 ; subst.
  rewrite H0.
  rewrite (non_virtual_subobject_offset_rewrite H7).
  esplit.
  split.
  reflexivity.
  inversion_clear H8.
   invall.
   subst.
   left.
   split.
   trivial.
   omega.
  right.
  invall.
  subst.
  repeat (esplit ; try eassumption).
  rewrite (array_path_offset_rewrite H15).
  reflexivity.
  omega.

  (* "self empty". *)
  intros.
  subst.
  split.
  assumption.
  exists ci.
  exists (ci :: nil).
  split.
   econstructor.
   reflexivity.
   pattern (ci :: nil) at 1.
   replace (ci :: nil) with (nil ++ ci :: nil).
   reflexivity.
   reflexivity.
   generalize (Is_empty.defined Is_empty_prop H).
   simpl.
   case_eq (hierarchy ! ci); congruence.
  simpl.
  esplit.
  split.
  reflexivity.
  tauto.

  (* "non_virtual_empty_base_offset_non_virtual_base_" *)
  intros.
  invall.
  split.
  assumption.
  inversion H2 ; subst.
  exists x.
  exists (ci :: ci' :: lf).
  asplit.
   econstructor.
   reflexivity.
   pattern (ci' :: lf) at 1.
   rewrite H7.
   change (ci :: lt ++ x :: nil) with ((ci :: lt) ++ x :: nil).
   reflexivity.
   case_eq (is_valid_repeated_subobject hierarchy (ci :: ci' :: lf)).
    tauto.
   functional inversion 1 ; subst.
    assert (offsets ! ci <> None) by congruence.
    assert (hierarchy ! ci <> None) by eauto.
    contradiction.
    congruence.
    assert ((non_virtual_direct_base_offsets oc) ! ci' <> None) by congruence.
    generalize (non_virtual_direct_base_offsets_guard (intro H) H9 H13).
    intros.
    contradiction.
   rewrite non_virtual_subobject_offset_equation.
   rewrite H.
   rewrite H0.
   rewrite (non_virtual_subobject_offset_rewrite H5).
   esplit.
   split.
    reflexivity.
   inversion_clear H6.
    invall.
    subst.
    left.
    split.
    trivial.
    omega.
   invall.
   subst.
   right.
   repeat (esplit ; try eassumption).
   rewrite (array_path_offset_rewrite H13).
   reflexivity.
   omega.

   (* "non_virtual_empty_base_offset_field". *)
   intros.
   invall.
   split.
    assumption.
   assert (offsets ! ci <> None) by congruence.
   assert (hierarchy ! ci <> None) by eauto.
   case_eq (hierarchy ! ci) ; try congruence.
   intros.
   exists ci.
   exists (ci :: nil).
   asplit.
    eleft with nil nil.
    reflexivity.
    reflexivity.
    simpl.
    rewrite H12 ; trivial.
   simpl.
   esplit.
   split.
   reflexivity.
   right.
   esplit.
   split.
   eassumption.
   esplit.
   esplit.
   split.
   eassumption.
   esplit.
   esplit.
   split.
   eassumption.
   inversion_clear H10.
    invall.
    subst.
    exists cif.
    exists (Zpos arraysize).
    exists nil.
    split.
    constructor.    
    compute ; congruence.
    omega.
    simpl.
    destruct (peq cif cif) ; try congruence.
(*    rewrite H2. *)
    esplit.
    split.
    reflexivity.
    esplit.
    split.
    eassumption. (* reflexivity. *)
    esplit.
    split.
    eassumption.
    split.
    assumption.
    esplit.
    esplit.
    split.
    eassumption.
    esplit.
    split.
    eassumption.
    omega.
   invall ; subst.
   exists x9.
   exists x10.
   exists ((ai, (x1, x0), x5) :: x11).
   generalize (path_defined_to H8).
   intros.
   case_eq (hierarchy ! x2) ; try congruence.
   intros.
   assert (assoc (FieldSignature.eq_dec (A := A)) x5 (field_offsets x4) <> None) by congruence.
   generalize (field_offsets_guard (intro H14) H26 H25).
   intros.
   split.
   econstructor.
   assumption.
   assumption.
   eassumption.
   eassumption.
   eassumption.
   eassumption.
   assumption.
   simpl.
   rewrite H2.
   rewrite H9.
   rewrite (path_last H8).
   rewrite H14.
   rewrite H15.
   rewrite H10.
   rewrite (array_path_offset_rewrite H18).
   esplit.
   split.
   reflexivity.
   repeat (esplit ; try eassumption).
   omega.
 Qed.

Lemma combined_empty_base_offset_equiv : 
  (forall from to z, empty_base_offset from to z <-> (
    Is_empty to /\     
    exists p1, exists h1, exists to1,
      path hierarchy to1 p1 from h1 /\
      exists z1, subobject_offset from p1 = Some z1 /\
        ((
          to = to1 /\
          z1 = z
        ) \/      
        exists o1, offsets ! to1 = Some o1 /\
          exists f, exists fz, assoc (FieldSignature.eq_dec (A := A)) f (field_offsets o1) = Some fz /\
            exists to2, exists ars2,
              FieldSignature.type f = FieldSignature.Struct to2 ars2 /\
              exists to3, exists arsz3, exists l,
                valid_array_path hierarchy to3 arsz3 to2 (Zpos ars2) l /\
                exists lz,
                  array_path_offset (z1 + fz) to2 l = Some lz /\
                  exists o3, offsets ! to3 = Some o3 /\
                    exists x, 0 <= x /\ x < arsz3 /\
                      exists p4, exists h4,
                        path hierarchy to p4 to3 h4 /\
                        exists p4z,
                          subobject_offset to3 p4 = Some p4z /\
                          z = lz + x * size o3 + p4z
      )
  )) /\
  (forall from to z, non_virtual_empty_base_offset from to z <-> (
    Is_empty to /\        
    exists to1, exists p1,
      path hierarchy to1 p1 from Class.Inheritance.Repeated /\
      exists z1, non_virtual_subobject_offset 0 p1 = Some z1 /\
        ((
          to = to1 /\
          z1 = z
        ) \/        
        exists o1, offsets ! to1 = Some o1 /\
          exists f, exists fz, assoc (FieldSignature.eq_dec (A := A)) f (field_offsets o1) = Some fz /\
            exists to2, exists ars2,
              FieldSignature.type f = FieldSignature.Struct to2 ars2 /\
              exists to3, exists arsz3, exists l,
                valid_array_path hierarchy to3 arsz3 to2 (Zpos ars2) l /\
                exists lz,
                  array_path_offset (z1 + fz) to2 l = Some lz /\
                  exists o3, offsets ! to3 = Some o3 /\
                    exists x, 0 <= x /\ x < arsz3 /\
                      exists p4, exists h4,
                        path hierarchy to p4 to3 h4 /\
                        exists p4z,
                          subobject_offset to3 p4 = Some p4z /\
                          z = (lz + x * size o3 + p4z)
        )
  )).
Proof.
  generalize (combined_empty_base_offset_elim).
  destruct 1.
  intros.
  split.
   intros.
   split.
   eauto.
   intros.
   invall.
   inversion H5 ; invall ; subst.
    eauto using path_empty_base_offsets.
   eauto using field_empty_base_offsets.
  intros.
  split.
   eauto.
  intros.
  invall.
  inversion_clear H5 ; invall ; subst.
  replace z with (z - 0) by omega.
   eauto using non_virtual_path_empty_base_offsets.
   replace (x10 + x12 * size x11 + x15) with (x10 + x12 * size x11 + x15 - 0) by omega.
  eauto using field_non_virtual_empty_base_offsets.
Qed.

  
(** * Soundness conditions for empty base offsets (4.5.5) *)

Record disjoint_empty_base_offsets (ci : ident) (oc : t) : Prop := disjoint_empty_base_offsets_intro {
  (** C23 C26 *)
  disjoint_empty_base_offsets_bases :
  forall baseref,
    (baseref = non_virtual_direct_base_offsets \/ baseref = virtual_base_offsets) ->
    forall ci1 o1,
      (baseref oc) ! ci1 = Some o1 ->
      forall ci2 o2,
        (baseref oc) ! ci2 = Some o2 -> 
        ci1 <> ci2 ->
        forall bi x1, non_virtual_empty_base_offset ci1 bi x1 ->
          forall x2, non_virtual_empty_base_offset ci2 bi x2 ->
            o1 + x1 <> o2 + x2
            ;
  (** C24 *)
  disjoint_empty_base_offsets_field_base :
    forall ci1 o1,
      (non_virtual_direct_base_offsets oc) ! ci1 = Some o1 ->
      forall f2 o2,
          assoc (FieldSignature.eq_dec (A := A)) f2 (field_offsets oc) = Some o2 ->
          forall ci2 n2, FieldSignature.type f2 = FieldSignature.Struct ci2 n2 ->             
            forall p2, 0 <= p2 -> p2 < Zpos n2 ->
              forall of2, offsets ! ci2 = Some of2 ->
                forall bi x1, non_virtual_empty_base_offset ci1 bi x1 ->
                  forall x2, empty_base_offset ci2 bi x2 ->
                    o1 + x1 <> o2 + p2 * size of2 + x2
                    ;
  (** C25 *)
  disjoint_empty_base_offsets_fields :
      forall f1 o1,
          assoc (FieldSignature.eq_dec (A := A)) f1 (field_offsets oc) = Some o1 ->
          forall ci1 n1, FieldSignature.type f1 = FieldSignature.Struct ci1 n1 ->            
            forall of1, offsets ! ci1 = Some of1 ->
              forall p1, 0 <= p1 -> p1 < Zpos n1 ->
      forall f2 o2,
          assoc (FieldSignature.eq_dec (A := A)) f2 (field_offsets oc) = Some o2 ->
          forall ci2 n2, FieldSignature.type f2 = FieldSignature.Struct ci2 n2 ->            
            forall of2, offsets ! ci2 = Some of2 ->
              forall p2, 0 <= p2 -> p2 < Zpos n2 ->
                f1 <> f2 ->
                forall bi x1, empty_base_offset ci1 bi x1 ->
                  forall x2, empty_base_offset ci2 bi x2 ->
                    o1 + p1 * size of1 + x1 <> o2 + p2 * size of2 + x2
}.

  
(** * Soundness proof of identity of subobjects for empty base offsets (5.3) *)

Section Disjoint_empty_base_offsets.


  Hypothesis disjoint : forall ci oc,
    offsets ! ci = Some oc ->
    disjoint_empty_base_offsets ci oc.
  
Fact disjoint_empty_base_offsets_disjoint_non_virtual_paths :
  forall p1 ci to, path hierarchy to p1 ci Class.Inheritance.Repeated ->
    forall (to_empty : Is_empty to),
      forall accu o, non_virtual_subobject_offset accu p1 = Some o ->
        forall p2, path hierarchy to p2 ci Class.Inheritance.Repeated ->
          non_virtual_subobject_offset accu p2 = Some o ->
          p1 = p2.
Proof.
 induction p1 ; simpl.
  congruence.
 intros until o.
 inversion H ; subst.
 injection H0 ; intros until 2 ; subst.
 pattern lf at 1.
 destruct lf.
  destruct lt ; simpl in H1 ; try discriminate.
  injection H1 ; intros ; subst.
  generalize (Well_formed_hierarchy.self_path_trivial Hhier H5).
  congruence.
  destruct lt ; simpl in H1 ; discriminate.
 case_eq (offsets ! ci); try congruence.
 intros until 1.
 case_eq ((non_virtual_direct_base_offsets t0) ! i); try congruence. 
 intros.
 inversion H6 ; subst.
 destruct lf0.
  destruct lt0 ; simpl in  H9.
   injection H9 ; intros ; subst.
   generalize (Well_formed_hierarchy.self_path_trivial Hhier H).
   congruence.
  destruct lt0 ; simpl in H9 ; discriminate.
 functional inversion H7.
 subst.
 replace o0 with t0 in * by congruence.
 functional inversion H2.
 subst.
 functional inversion H10.
 subst.
 generalize (last_equation (ci :: i0 :: lf0)).
 rewrite H9 at 1.
 rewrite last_complete.
 intros.
 symmetry in H8.
 generalize (last_correct H8).
 destruct 1.
 assert (path hierarchy to (i0 :: lf0) i0 Class.Inheritance.Repeated).
  eleft.
  reflexivity.
  eassumption.
  assumption.
 generalize (last_equation (ci :: i :: lf)).
 rewrite H1 at 1.
 rewrite last_complete.
 intros.
 symmetry in H12.
 generalize (last_correct H12).
 destruct 1.
 assert (path hierarchy to (i :: lf) i Class.Inheritance.Repeated).
  eleft.
  reflexivity.
  eassumption.
  assumption.
 destruct (peq i i0).
  subst.
  cut (i0 :: lf = i0 :: lf0).
   congruence.
  eapply IHp1.
   eassumption.
   assumption.
   eassumption.
   assumption.
   congruence.
  apply False_rect.
  generalize (non_virtual_path_empty_base_offsets to_empty H13 H5).
  intros.
  generalize (non_virtual_path_empty_base_offsets to_empty H11 X).
  intros.
  generalize (disjoint_empty_base_offsets_bases (disjoint H3) (or_introl _ (refl_equal _)) H4 H18 n H16 H20).
  omega.
Qed.

Fact disjoint_empty_base_offsets_disjoint_paths :
  forall p1 h1 ci to, path hierarchy to p1 ci h1 ->
    forall (to_empty : Is_empty to),
    forall o, subobject_offset ci (* h1 *) p1 = Some o ->
      forall p2 h2, path hierarchy to p2 ci h2 ->
        subobject_offset ci (* h2 *) p2 = Some o ->
        (h1, p1) = (h2, p2).
Proof.
 intros.
 functional inversion H0 ; subst.
 assert (path hierarchy to (b :: _x) b Class.Inheritance.Repeated) by (
   generalize (path_path0 H);
     inversion 1 ; subst ; try congruence; try eleft ; eauto using is_valid_repeated_subobject_defined
 ).
 generalize (non_virtual_path_empty_base_offsets to_empty H5 H3).
 intros.
 functional inversion H2 ; subst.
 assert (path hierarchy to (b0 :: _x0) b0 Class.Inheritance.Repeated) by (
   generalize (path_path0 H1);
     inversion 1 ; subst ; try congruence; try eleft ; eauto using is_valid_repeated_subobject_defined
 ).
 replace o1 with o0 in * by congruence.
 generalize (non_virtual_path_empty_base_offsets to_empty H10 H8).
 intros.
 destruct (peq b b0).
  subst.
  cut (b0 :: _x = b0 :: _x0).
   injection 1 ; intros ; subst.
   generalize (Well_formed_hierarchy.categorize_paths Hhier H1 (refl_equal _)).
   destruct 1.
   generalize (Well_formed_hierarchy.categorize_paths Hhier H (refl_equal _)).
   destruct 1.
   destruct h1 ; destruct h2 ; try congruence ; assert (b0 = ci) by eauto ; assert (Class.Inheritance.Shared = Class.Inheritance.Repeated) by eauto ; congruence.
  replace of0 with of in * by congruence.
  eauto using disjoint_empty_base_offsets_disjoint_non_virtual_paths.
 apply False_rect.
 generalize (disjoint_empty_base_offsets_bases (disjoint H4) (or_intror _ (refl_equal _)) H7 H12 n H6 H11).
 omega.
Qed.

(** 5.3 Theorem 4 empty *)
Theorem disjoint_empty_base_offsets_disjoint_pointer_paths :
  forall pto (pto_isempty : Is_empty pto) (pto_offsets_def: offsets ! pto <> None) ap1 afrom asfrom ato1 i1 h1 p1,
    valid_relative_pointer hierarchy afrom asfrom ap1 ato1 i1 h1 p1 pto ->
  forall ap2 ato2 i2 h2 p2,
    valid_relative_pointer hierarchy afrom asfrom ap2 ato2 i2 h2 p2 pto ->
    forall o, relative_pointer_offset afrom ato1 ap1 i1 p1 = Some o ->
      relative_pointer_offset afrom ato2 ap2 i2 p2 = Some o ->
      (ap1, i1, h1, p1) = (ap2, i2, h2, p2)
      .
Proof.
  (* symmetry *)
  cut (
    forall pto (pto_isempty : Is_empty pto)  (pto_offsets_def: offsets ! pto <> None) 
      ap1 afrom asfrom ato1 i1 h1 p1,
      valid_relative_pointer hierarchy afrom asfrom ap1 ato1 i1 h1 p1 pto ->
      forall ap2 (ap1_le : (length ap1 <= length ap2)%nat) ato2 i2 h2 p2,
    valid_relative_pointer hierarchy afrom asfrom ap2 ato2 i2 h2 p2 pto ->
    forall o, relative_pointer_offset afrom ato1 ap1 i1 p1 = Some o ->
      relative_pointer_offset afrom ato2 ap2 i2 p2 = Some o ->
      (ap1, i1, h1, p1) = (ap2, i2, h2, p2)
  ).   
   intros.
   destruct (le_lt_dec (length ap1) (length ap2)).
    eauto.
   assert (length ap2 <= length ap1)%nat by omega.
   cut ((ap2, i2, h2, p2) = (ap1, i1, h1, p1)) ; eauto.

  (* induction on length ap1 *)
  intros until ap1.
  var (length ap1).
  revert v ap1 H.    
  induction v using (well_founded_induction Wf_nat.lt_wf).

  (* alternate notion of relative pointers *)
  intros.
  subst.  
  revert ap1_le H.
  rewrite <- (relative_pointer_alt_length_correct ap1 i1 (h1, p1)).
  rewrite <- (relative_pointer_alt_length_correct ap2 i2 (h2, p2)).
  generalize (relative_pointer_alt_offset_correct H1 H3).
  clear H3.
  generalize (relative_pointer_alt_offset_correct H2 H4).
  clear H4.
  generalize (valid_relative_pointer_valid_relative_pointer_alt H1).
  clear H1. 
  generalize (valid_relative_pointer_valid_relative_pointer_alt H2).
  clear H2.
  inversion 1; subst.
  rewrite <- H0 in H.
  inversion 1; subst.
  rewrite <- H6 in H5.
  intros.
  cut ((i'0, h'0, p'0, f'0) = (i', h', p', f')).
   injection 1; intros; subst.
   generalize (relative_pointer_default_to_alt_to_default ap1 i1 (h1, p1)).
   generalize (relative_pointer_default_to_alt_to_default ap2 i2 (h2, p2)).
   rewrite <- H0.
   rewrite <- H6.
   intro.
   rewrite H15.
   injection 1; intros; subst; trivial.
  clear ap1 i1 h1 p1 ap2 i2 h2 p2 H0 H6.

  (* actual offset calculus *)
  generalize H11.
  unfold relative_pointer_alt_offset.
  case_eq (offsets ! afrom); try congruence.
  intros until 1.
  case_eq (subobject_offset afrom p'); try congruence.
  intros until 1.
  generalize (relative_pointer_alt_offset_size H H0 H6 H11).
  rewrite (path_last H3).
  destruct 1.
  generalize (H15 _ (refl_equal _)).
  clear H15.
  intros.
  assert (offsets ! through <> None).
   destruct f'.
    destruct p.
    destruct p.
    destruct p.
    destruct p0.
    invall.
    revert H16.
    rewrite H18.
    case_eq (offsets ! through); congruence.
   invall.
   congruence.
  case_eq (offsets ! through); try congruence.
  intros.
  rewrite H18 in *.

  generalize H12.
  unfold relative_pointer_alt_offset.
  rewrite H0.
  case_eq (subobject_offset afrom p'0); try congruence.
  intros until 1.
  generalize (relative_pointer_alt_offset_size H5 H0 H19 H12).
  rewrite (path_last H9).
  destruct 1.
  generalize (H21 _ (refl_equal _)).
  clear H21.
  intros.
  assert (offsets ! through0 <> None).
   destruct f'0.
    destruct p.
    destruct p.
    destruct p.
    destruct p0.
    invall.
    revert H22.
    rewrite H24.
    case_eq (offsets ! through0); congruence.
   invall.
   congruence.
  case_eq (offsets ! through0); try congruence.
  intros.
  rewrite H24 in *.
  
  case_eq (offsets ! pto); try congruence.
  intros.
  rewrite H25 in *.
  generalize (H21 _ (refl_equal _) _ (refl_equal _)).
  clear H21.
  intros.
  generalize (H15 _ (refl_equal _) _ (refl_equal _)).
  clear H15.
  intros.
  
  (* case analysis *)
  destruct (Z_eq_dec i'0 i').

  (* different cells *)
  Focus 2.
   apply False_rect.
   generalize (subobject_offset_size H3 H6).
   destruct 1.
   generalize (H27 _ H0 _ H18).
   intros.
   generalize (subobject_offset_size H9 H19).
   destruct 1.
   generalize (H30 _ H0 _ H24).
   intros.
   generalize (size_positive H0).
   intros.
   generalize (array_cells_disjoint n H32).
(*   generalize (non_virtual_size_non_virtual_data_size (intro H25)).
   generalize (non_virtual_data_size_own_fields_offset (intro H25)). *)
   generalize (own_fields_offset_low_bound (intro H25)).
   generalize (non_virtual_size_positive (intro H25)).
   omega.

  (* same cells *)
   subst.
   assert (non_virtual_empty_base_offset through pto (o - (i' * size t0 + z))).
    destruct f'.
     destruct p.
     destruct p.
     destruct p.
     destruct p0.
     invall.
     revert H16.
     rewrite H27.
     case_eq (assoc (FieldSignature.eq_dec (A := A)) t4 (field_offsets t1)); try congruence.
     intros until 1.
     case_eq (relative_pointer_offset x0 ato2 a z1 l); try congruence.
     functional inversion 1; subst.
     inversion H29; subst.
     injection 1; intros; subst.
     replace (
       (i' * size t0 + z + z2 + (z4 + z1 * size ofto + z5) - (i' * size t0 + z))
     ) with (
       (z2 + z4) + z1 * size ofto + z5 - 0
     ) by omega.
     eapply field_non_virtual_empty_base_offsets.
      eapply path_trivial.
      eapply path_defined_to.
      eassumption.
      simpl.
      reflexivity.
      eassumption.
      eassumption.
      eassumption.
      eassumption.
      rewrite (array_path_offset_rewrite H31).
      f_equal; omega.
      assumption.
      assumption.
      assumption.
      assumption.
      eassumption.
      assumption.
    invall.
    subst.
    injection H16; intros; subst.
    econstructor.
     assumption.
     omega.
   assert (non_virtual_empty_base_offset through0 pto (o - (i' * size t0 + z0))).
    destruct f'0.
     destruct p.
     destruct p.
     destruct p.
     destruct p0.
     invall.
     revert H22.
     rewrite H28.
     case_eq (assoc (FieldSignature.eq_dec (A := A)) t4 (field_offsets t2)); try congruence.
     intros until 1.
     case_eq (relative_pointer_offset x0 ato1 a z1 l); try congruence.
     functional inversion 1; subst.
     inversion H30; subst.
     injection 1; intros; subst.
     replace (
       (i' * size t0 + z0 + z2 + (z4 + z1 * size ofto + z5) - (i' * size t0 + z0))
     ) with (
       (z2 + z4) + z1 * size ofto + z5 - 0
     ) by omega.
     eapply field_non_virtual_empty_base_offsets.
      eapply path_trivial.
      eapply path_defined_to.
      eassumption.
      simpl.
      reflexivity.
      eassumption.
      eassumption.
      eassumption.
      eassumption.
      rewrite (array_path_offset_rewrite H32).
      f_equal; omega.
      assumption.
      assumption.
      assumption.
      assumption.
      eassumption.
      assumption.
    invall.
    subst.
    injection H22; intros; subst.
    econstructor.
     assumption.
     omega.

   functional inversion H6; subst.
   functional inversion H19; subst.
   generalize (path_cons_repeated H3).
   intros.
   generalize (path_cons_repeated H9).
   intros.
   destruct (list_eq_dec peq (b0 :: _x0) (b :: _x)).

   (* same path *)
    injection e; intros; subst.
    assert (h' = h'0) by eauto using Well_formed_hierarchy.path_eq_hierarchy_eq.
    subst.
    destruct (option_eq_dec
       (prod_eq_dec 
         (prod_eq_dec
           (prod_eq_dec (FieldSignature.eq_dec (A := A)) (array_path_eq_dec (A := A)))
           Z_eq_dec
         )
         (prod_eq_dec 
           Class.Inheritance.eq_dec
             (list_eq_dec peq)
         )
       )
       f' f'0
     ) ; try congruence.   
     apply False_rect.
     generalize (path_last H3).
     intros.
     generalize (path_last H9).
     intros.
     replace through0 with through in * by congruence.
     replace z0 with z in * by congruence.
     replace t2 with t1 in * by congruence.
     destruct f'.
      destruct p.
      destruct p.
      destruct p.
      destruct p0.
      invall; subst.
      revert H16.
      rewrite H39.
      inversion H41; subst.
      case_eq (assoc (FieldSignature.eq_dec (A := A)) t4 (field_offsets t1)); try congruence.
      intros until 1.
      case_eq (relative_pointer_offset x0 ato2 a z1 l); try congruence.
      injection 2; intros; subst.
      destruct f'0.
       destruct p.
       destruct p.
       destruct p.
       destruct p0.
       invall; subst.
       replace x2 with x in * by congruence.
       inversion H50; subst.
       revert H22.
       rewrite H48.
       case_eq (assoc (FieldSignature.eq_dec (A := A)) t6 (field_offsets t1)); try congruence.
       intros until 1.
       case_eq (relative_pointer_offset x3 ato1 a0 z4 l0); try congruence.
       injection 2; intros.
       destruct ((FieldSignature.eq_dec (A := A)) t4 t6).
        (* same field : use IH *)
        subst.
        rewrite H48 in H39.
        injection H39; intros; subst.
        replace z5 with z2 in * by congruence.
        replace z6 with z3 in * by omega.
        cut ( (a0, z4, t7, l0) = (a, z1, t5, l)).
         congruence.
        simpl in ap1_le.
        assert (length a0 <= length a)%nat by omega.
        simpl in H13.
        assert (length a0 < S (length a0))%nat by omega.
        eauto. (* induction hypothesis *) 
       (* different fields: use empty_base_offsets_disjoint hypothesis *)       
       assert (exists of0, offsets ! x0 = Some of0 /\ exists p0, 0 <= p0 /\ p0 < Zpos x1 /\ empty_base_offset x0 pto (z3 - p0 * size of0)).
        functional inversion H45; subst.
        functional inversion H58; subst; inversion H16; subst.
         esplit.
         esplit.
         eassumption.
         esplit.
         split.
         eexact H40.
         split.
         omega.
         eapply path_empty_base_offsets.
          assumption.
          eassumption.
          rewrite H60.
          f_equal.
          omega.
        esplit.
        split.
        eassumption.
        esplit.
        split.
        eassumption.
        split.
        eassumption.
        replace 
          (z7 + z1 * size ofto + z8 - z3 * size o)
          with
            ((z7 - z3 * size o) + z1 * size ofto + z8)
            by omega.
        rewrite (path_last H77) in H63.
        injection H63; intro; subst.             
        eapply field_empty_base_offsets.
        eassumption.
        eassumption.
        eassumption.
        eassumption.
        eassumption.
        eassumption.
        replace by with ci'0 in * by congruence.
        rewrite (array_path_offset_rewrite X).
        f_equal; omega.
        assumption.
        assumption.
        assumption.
        assumption.
        eassumption.
        assumption.
       assert (exists of3, offsets ! x3 = Some of3 /\ exists p3, 0 <= p3 /\ p3 < Zpos x4 /\ empty_base_offset x3 pto (z6 - p3 * size of3)).
        functional inversion H54; subst.
        functional inversion H59; subst; inversion H49; subst.
         esplit.
         esplit.
         eassumption.
         esplit.
         split.
         eexact H51.
         split.
         omega.
         eapply path_empty_base_offsets.
          assumption.
          eassumption.
          rewrite H61.
          f_equal.
          omega.
        esplit.
        split.
        eassumption.
        esplit.
        split.
        eassumption.
        split.
        eassumption.
        replace 
          (z7 + z4 * size ofto + z8 - z6 * size o)
          with
            ((z7 - z6 * size o) + z4 * size ofto + z8)
            by omega.
        rewrite (path_last H78) in H64.
        injection H64; intro; subst.             
        eapply field_empty_base_offsets.
        eassumption.
        eassumption.
        eassumption.
        eassumption.
        eassumption.
        eassumption.
        replace by with ci'0 in * by congruence.
        rewrite (array_path_offset_rewrite X).
        f_equal; omega.
        assumption.
        assumption.
        assumption.
        assumption.
        eassumption.
        assumption.
       invall.
       cut (z2 + x7 * size x6 + (z3 - x7 * size x6) <> z5 +  x8 * size x5 + (z6 - x8 * size x5)).
        omega.
       eauto using disjoint_empty_base_offsets_fields.

       (* absurd case : field from pto to pto in one of the two cases *)
       invall; subst.
       destruct (Plt_irrefl through).
       eapply Ple_Plt_trans.
        eauto using Well_formed_hierarchy.path_le.
        eapply Ple_Plt_trans.
        eauto using Well_formed_hierarchy.array_path_le.
       eauto using Well_formed_hierarchy.well_founded_struct.

       (* other absurd cases banned by the symmetry on the length of array paths *)
       destruct f'0; try congruence.
       simpl in ap1_le; destruct p; destruct p; destruct p; omega.

  (* different paths : induction hypothesis no longer useful *)
  clear H13.
  clear ap1_le.
  replace o0 with t0 in * by congruence.
  replace o1 with t0 in * by congruence.
  clear H17 H23.
  clear H29 H31.    
  clear H11 H12 H6 H19 .
  apply False_rect.
  clear H3 H9.
  clear H H5.
  destruct (peq b b0).

   (* same virtual base *)
   subst.
   assert (_x0 <> _x) by congruence.
   clear n.
   replace of0 with of in * by congruence.

  dependent_revert z0.
  dependent_revert z.
  dependent_revert f'.
  dependent_revert f'0.
  dependent_revert through.
  dependent_revert through0.
  dependent_revert t1.
  dependent_revert t2.
  dependent_revert ato1.
  dependent_revert ato2.
  pattern _x , _x0.
  apply distinct_lists_rect; try congruence.
   exact peq.
   intros; eauto.

   (* l2 is a tail of l1 *)
   intros.
   inversion H33; clear H33; subst.
   injection H3; clear H3; intros; subst.
   inversion H34; clear H34; subst.
   injection H3; intros; subst.  
   replace (b0 :: lf ++ a :: l2') with ((b0 :: lf) ++ a :: l2') in * by reflexivity.
   rewrite H5 in *.
   rewrite app_ass in *.
   replace ((through :: nil) ++ a :: l2') with (through :: a :: l2') in * by reflexivity.
   generalize (non_virtual_subobject_offset_app_recip H30).
   destruct 1.
   invall.
   replace x with z in * by congruence.
   clear H28 H13 H30 H6 H5 H3.
   generalize (is_valid_repeated_subobject_split_right H11).
   clear b0 lf H11 H32 H35.
   functional inversion 1; subst.
   clear H28.
   functional inversion H17; subst.
   replace o2 with t1 in * by congruence.
   assert {lt1 | a :: l2' = lt1 ++ through0 :: nil}.
    apply last_correct.
    assert (a :: l2' <> nil) by congruence.
    rewrite <- (last_app_left H5 (lt ++ through :: nil)).
    rewrite app_ass.
    simpl.
    rewrite H9.
    apply last_complete.
   destruct H5.
   clear lt H9.
   assert (path hierarchy through0 (a :: l2') a Class.Inheritance.Repeated).
    econstructor.
    reflexivity.
    eassumption.
    assumption.
   assert (non_virtual_empty_base_offset a pto (o - (i' * size t0 + z + of1))).
   replace (o - (i' * size t0 + z + of1)) with ((o - (i' * size t0 + z0)) + z0 - (z + of1)) by omega.
    eapply non_virtual_empty_base_offset_intro_non_virtual_path.
    eassumption.
    assumption.
    assumption.
   revert H4 H16.
   destruct f'.
    destruct p.
    destruct p.
    destruct p.
    destruct p0.
    destruct 1.
    invall.
    rewrite H11.
    case_eq (assoc (FieldSignature.eq_dec (A := A)) t4 (field_offsets t1)); try congruence.
    intros until 1.
    case_eq (relative_pointer_offset x2 ato2 a0 z1 l); try congruence.
    functional inversion 1.
    injection 1; intros; subst.
    inversion H16; subst.
    assert (
      exists p2, 0 <= p2 /\ p2 < Zpos x3 /\
        exists of2, offsets ! x2 = Some of2 /\
          empty_base_offset x2 pto (z4 - p2 * size of2 + z1 * size ofto + z5)
    ).
     inversion H23; subst.
     simpl in H28.
     injection H28; intros; subst.
     exists z1.
     split.
     assumption.
     split.
     omega.
     esplit.
     esplit.
     eassumption.
     replace  (0 - z1 * size ofto + z1 * size ofto + z5) with z5 by omega.
     eapply path_empty_base_offsets.
     assumption.
     eassumption.
     assumption.
     exists p.
     split.
     assumption.
     split.
     assumption.
     revert H28.
     rewrite array_path_offset_equation.
     case_eq (offsets ! x2); try congruence.
     intros until 1.
     case_eq (subobject_offset x2 l0); try congruence.
     intros until 1.
     rewrite (path_last H39).
     case_eq (offsets ! through1); try congruence.
     intros until 1.
     rewrite H42.
     case_eq (assoc (FieldSignature.eq_dec (A := A)) fs (field_offsets t7)); try congruence.
     intros.
     esplit.
     split.
     reflexivity.
     eapply field_empty_base_offsets.
     eassumption.
     eassumption.
     eassumption.
     eassumption.
     eassumption.
     eassumption.
     rewrite (array_path_offset_rewrite H47).
     f_equal; omega.
     assumption.
     assumption.
     assumption.
     assumption.
     eassumption.
     eassumption.
    invall.
    generalize (disjoint_empty_base_offsets_field_base (disjoint H18) H30 H12 H11 H37 H38 H40 H6 H41).
    omega.
   destruct 1; subst.
   injection 1; intros; subst.   
   apply (Plt_irrefl through).
   eapply Ple_Plt_trans.
   2 : eauto using Well_formed_hierarchy.well_founded.
   destruct f'0; invall; subst; eauto using Well_formed_hierarchy.path_le.
   destruct p; destruct p; destruct p; destruct p0.
   invall.
   inversion H12; subst.     
   eauto 9 using Plt_Ple, Ple_trans, Well_formed_hierarchy.path_le, Well_formed_hierarchy.array_path_le, Well_formed_hierarchy.well_founded_struct.
    
   (* the two paths diverge from one point *)
   intros until 2.
   assert (b0 :: l <> nil) by congruence.
   generalize (last_nonempty H4).
   intro.
   case_eq (last (b0 :: l)); try congruence.
   intros until 1.
   generalize (last_correct H6).
   destruct 1.
   inversion 1; subst.
   injection H9; intro; subst.
   inversion 2; subst.
   injection H12; intro; subst.
   revert H10 H13 H11 H14.
   replace (b0 :: l ++ a1 :: l1') with ((b0 :: l) ++ a1 :: l1') by reflexivity.
   replace (b0 :: l ++ a2 :: l2') with ((b0 :: l) ++ a2 :: l2') by reflexivity.
   rewrite e.
   clear b0 H35 H32 l H4 H5 H6 e H34 H9 H33 H12.
   intros until 2.
   repeat rewrite app_ass.
   simpl.
   assert (a2 :: l2' <> nil) by congruence.
   generalize (last_complete lt through0).
   rewrite <- H10.
   rewrite (last_app_left H4).
   intro.
   generalize (last_correct H5).
   destruct 1.
   assert (a1 :: l1' <> nil) by congruence.
   generalize (last_complete lt0 through).
   rewrite <- H13.
   rewrite (last_app_left H6).
   intro.
   generalize (last_correct H9).
   destruct 1.
   intros until 2.
   generalize (is_valid_repeated_subobject_split_right H11).
   functional inversion 1; subst.
   clear H23.
   generalize (is_valid_repeated_subobject_split_right H14).
   rewrite is_valid_repeated_subobject_equation.
   rewrite H20.
   destruct ( In_dec super_eq_dec (Class.Inheritance.Repeated, a1) (Class.super cl1)); try congruence.
   intro.
   assert (path hierarchy through (a1 :: l1') a1 Class.Inheritance.Repeated).
    eleft.
    reflexivity.
    eassumption.
    assumption.
   assert (path hierarchy through0 (a2 :: l2') a2 Class.Inheritance.Repeated).
    eleft.
    reflexivity.
    eassumption.
    assumption.
   intros.
   generalize (non_virtual_subobject_offset_app_recip H28).
   destruct 1.
   invall.
   functional inversion H36; subst.
   generalize (non_virtual_subobject_offset_app_recip H33).
   rewrite H35.
   destruct 1.
   invall.
   injection H37; intros; subst.
   revert H38.
   rewrite non_virtual_subobject_offset_equation.
   rewrite H43.
   case_eq ((non_virtual_direct_base_offsets o2) ! a2); try congruence.
   intros.
   dependent_revert of.
   dependent_revert x.
   apply False_rect.
   generalize (non_virtual_empty_base_offset_intro_non_virtual_path H16 X0 H27).
   generalize (non_virtual_empty_base_offset_intro_non_virtual_path H17 H38 H32).
   intros.
   generalize (disjoint_empty_base_offsets_bases (disjoint H43) (or_introl _ (refl_equal _)) H44 H34 H3 H11 H10).
   omega.

   (* different virtual bases *)
   generalize (non_virtual_empty_base_offset_intro_non_virtual_path H33 H28 H26).
   generalize (non_virtual_empty_base_offset_intro_non_virtual_path H34 H30 H27).
   intros.
   generalize (disjoint_empty_base_offsets_bases (disjoint H0) (or_intror _ (refl_equal _)) H32 H35 n0 H3 H).
   omega.

Qed.
  
End Disjoint_empty_base_offsets.



  Lemma non_virtual_empty_base_offset_incl : forall ci b z,
    non_virtual_empty_base_offset ci b z ->
    ((offsets ) ! b <> None) ->
    forall o', (offsets ) ! ci = Some o' ->
      0 <= z /\ z < non_virtual_size o'.
  Proof.
   induction 1.
     subst.
     intros.
     split.
      omega.
     eapply non_virtual_size_positive.
     eauto.
    intros.
    assert ((offsets ) ! ci' <> None).
     inversion H1; congruence.
    case_eq ((offsets ) ! ci'); try congruence.
    intros.
    generalize (IHnon_virtual_empty_base_offset H2 _ H5).
    generalize (non_virtual_size_positive (intro H5) ).
    replace oc with o'0 in * by congruence.
    generalize (non_virtual_size_non_virtual_direct_bases (intro H3) H0 H5).
    generalize (non_virtual_direct_base_offsets_low_bound (intro H3) H0).
    omega.
   intros.
   destruct (combined_empty_base_offset_elim). 
   destruct (H8 _ _ _ H5).
   clear H8 H9.
   invall.
   assert (exists r, exists ato, exists i, exists h, exists p, valid_relative_pointer hierarchy cif (Zpos arraysize) r ato i h p b /\ relative_pointer_offset  cif ato r i p = Some (x - fo)).
    destruct H12.
     invall; subst.
     exists nil.
     exists cif.
     exists ai.
     exists x1.
     exists x0.
     asplit.
      econstructor.
      3 : eassumption.
      econstructor.
      omega.
      omega.
      assumption.
      assumption.
     unfold relative_pointer_offset.
     simpl.
     rewrite H2.
     rewrite H11.
     f_equal.
     omega.
    invall; subst.
    exists ((ai, (x1, x0), x5) :: x11).
    exists x9.
    exists x14.
    exists x16.
    exists x15.
    assert (hierarchy ! x2 <> None).
     apply guard.
     congruence.
    case_eq (hierarchy ! x2); try congruence.
    intros.
    assert (In x5 (Class.fields t0)).
     eapply field_offsets_guard.
     3 : eassumption.
     eauto.
     congruence.
    asplit.
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
     unfold relative_pointer_offset.
     simpl.
     rewrite H2.
     rewrite H11.
     rewrite (path_last H9).
     rewrite H8.
     rewrite H13.
     rewrite H12.
     rewrite (array_path_offset_rewrite H16).
     rewrite H17.
     rewrite H21.
     f_equal.
     omega.
    clear ai H3 H4 H5 x0 x1 x2 H9 x3 H11 H12.
    invall.
    replace o' with oc in * by congruence.    
    case_eq ((offsets ) ! b); try congruence.
    intros.
    destruct (relative_pointer_offset_size  H4 H5).
    generalize (H9 _ H2 _ H3).
    intros.
    generalize (non_virtual_size_positive (intro H3)).
    intros.
    generalize (non_virtual_size_field_offsets (intro H) H0).
    unfold field_size.
    rewrite H1.
    rewrite H2.
    intros.
    generalize (H13 _ (refl_equal _)).
    pattern (size ocf) at 2.
    replace (size ocf) with (1 * size ocf) by omega.
    rewrite <- Zmult_plus_distr_l.
    replace (Zpos arraysize - 1 + 1) with (Zpos arraysize) by omega.
    generalize (field_offsets_low_bound (intro H) H0).
    omega.
  Qed.

  Lemma empty_base_offset_incl : forall ci b z,
    empty_base_offset ci b z ->
    ((offsets ) ! b <> None) ->
    forall o', (offsets ) ! ci = Some o' ->
      0 <= z /\ z < size o'.
  Proof.
   inversion 1; subst.
   intros.
   replace o'0 with oc in * by congruence.
   assert ((offsets ) ! ci' <> None).
     inversion H2; congruence.
   case_eq ((offsets ) ! ci'); try congruence.
   intros.
   destruct (non_virtual_empty_base_offset_incl H2 H3 H6).
   generalize (virtual_base_offsets_low_bound (intro H0) H1).
   intros.
   generalize (virtual_base_offsets_high_bound (intro H0) H1 H6).
   intros.
   omega.
 Qed.

  Lemma non_virtual_empty_base_offset_wf : forall ci b z,
    non_virtual_empty_base_offset ci b z ->
    Ple b ci /\ hierarchy ! b <> None.
  Proof.
    intros.
    destruct (combined_empty_base_offset_equiv ).
     eauto.
    destruct (H1 ci b z).
    clear H0 H1 H3.
    destruct (H2 H).
    clear H2 H.
    invall.
    destruct H3.
     invall; subst.
     split.
     eauto using Well_formed_hierarchy.path_le.
     eauto using path_defined_to.
    invall.
    split.
    2 : eauto using path_defined_to.
    eapply Ple_trans.
    eauto using Well_formed_hierarchy.path_le.
    eapply Ple_trans.
    eauto using Well_formed_hierarchy.array_path_le.
    assert ((offsets ) ! x <> None) by congruence.
    assert (hierarchy ! x <> None) by eauto.
    case_eq (hierarchy ! x); try congruence.
    intros.
    assert (assoc (FieldSignature.eq_dec (A := A)) x3 (field_offsets x2) <> None) by congruence.
    assert (In x3 (Class.fields t0)) by eauto using field_offsets_guard.
    eapply Plt_Ple.
    eapply Plt_Ple_trans.
    eauto using Well_formed_hierarchy.well_founded_struct.
    eauto using Well_formed_hierarchy.path_le.
  Qed.


  Lemma empty_base_offset_wf : forall ci b z,
    empty_base_offset ci b z ->
    Ple b ci /\ hierarchy ! b <> None.
  Proof.
    inversion 1; subst.
    assert (offsets ! ci <> None) by congruence.
    assert (hierarchy ! ci <> None) by eauto.
    case_eq (hierarchy ! ci); try congruence.
    intros.
    assert ((virtual_base_offsets oc) ! ci' <> None) by congruence.
    assert (Ple ci' ci).
     destruct (virtual_base_offsets_guard (intro H0) H6).
      eauto using Plt_Ple, Well_formed_hierarchy.is_virtual_base_of_lt.
     subst; apply Ple_refl.
    destruct (non_virtual_empty_base_offset_wf H2).
    split.
     eauto using Ple_trans.
    assumption.
  Qed.
  
End Empty_base_offsets.


Section Nonempty_base_offsets.

(** * Data inclusion for non-empty bases *)

Fact non_virtual_path_non_virtual_data_incl : forall l to from,
  path hierarchy to l from Class.Inheritance.Repeated ->
    (Is_empty to -> False) ->
    forall accu o, non_virtual_subobject_offset accu l = Some o ->
      accu <= o /\
      forall oto, offsets ! to = Some oto ->
        forall ofrom, offsets ! from = Some ofrom ->
          o + non_virtual_data_size oto <= accu + non_virtual_data_size ofrom.
Proof.
  induction l; inversion 1; subst; try discriminate.
  injection H0; intros; subst.
  functional inversion H2; subst.
   destruct lt ; simpl in H1.
    injection H1; intros; subst.
    functional inversion H6; subst.
    split.
    omega.
    intros.
    replace oto with ofrom by congruence.
    omega.
   destruct lt; simpl in H1; discriminate.
  functional inversion H6; subst.
  rewrite H14.
  destruct lt; simpl in H1; try congruence.
  injection H1; intros; subst.
  assert (path hierarchy to (id2 :: l3) id2 Class.Inheritance.Repeated).
   eleft; eauto.
  generalize (non_virtual_direct_base_offsets_low_bound (intro H14) H15).
  intros.
  generalize (IHl _ _ H4 H5 _ _ X0).
  destruct 1.
  split.
  omega.
  injection 2; intros; subst.
  assert (offsets ! id2 <> None).
   functional inversion X0; subst; try congruence.
   generalize (path_last H4).
   simpl.
   congruence.
  case_eq (offsets ! id2); try congruence.
  intros.
  generalize (Is_empty.path_from Is_empty_prop H4 H5).
  intros.
  generalize (non_virtual_direct_base_offsets_nonempty_high_bound (intro H14) H18 H15 H17).
  generalize (non_virtual_data_size_own_fields_offset (intro H14)).
  generalize (H10 _ H12 _ H17).
  omega.
Qed.
     
Fact non_virtual_path_disjoint_field_zones : forall l1 l2,
  l1 <> l2 ->
  forall to1,
    (Is_empty to1 -> False) ->
    forall from,
      path hierarchy to1 l1 from Class.Inheritance.Repeated ->
        forall to2,
          (Is_empty to2 -> False) ->
          path hierarchy to2 l2 from Class.Inheritance.Repeated ->
            forall accu z1, non_virtual_subobject_offset accu l1 = Some z1 ->
              forall z2, non_virtual_subobject_offset accu l2 = Some z2 ->
                forall o1, offsets ! to1 = Some o1 ->
                  forall o2, offsets ! to2 = Some o2 ->
                    z1 + non_virtual_data_size o1 <= z2 + own_fields_offset o2 \/
                    z2 + non_virtual_data_size o2 <= z1 + own_fields_offset o1
                    .
Proof.
  intros until 1.
  pattern l1, l2.
  eapply distinct_lists_rect; eauto using peq ; clear l1 l2 H.

  (* symmetry *)
  intros.
  assert (forall A B : Prop, A \/ B -> B \/ A) by tauto.
  eauto.

  (* l1 is a prefix of l2 *)
  inversion 2; subst.
  rewrite H2 in *.
  inversion 2; subst.
  revert H7.
  repeat rewrite app_ass.
  simpl.
  intro.
  generalize (is_valid_repeated_subobject_split_right H7).
  functional inversion 1; subst.
  intros until 2.
  generalize (non_virtual_subobject_offset_app_recip H10).
  destruct 1.
  invall.
  replace z1 with x in * by congruence.
  assert {lt1 | a :: l2' = lt1 ++ to2 :: nil}.
   apply last_correct.
   assert (a :: l2' <> nil) by congruence.
   rewrite <- (last_app_left H11 (lt ++ to1 :: nil)).
   rewrite H6.
   apply last_complete.
  destruct H11.  
  clear from lf lt H0 H2 H3 H4 lf0 lt0 H5 H6 H7 H16 H8 accu z1 H9 H10 H12.
  functional inversion H14; subst.
  clear H14.
  assert (path hierarchy to2 (a :: l2') a Class.Inheritance.Repeated).
   eleft; eauto.
  rewrite H8.
  injection 1; intro; subst.
  intros.
  assert (offsets ! a <> None).
   functional inversion X0; subst; try congruence.
   generalize (path_last H0); simpl; congruence.
  case_eq (offsets ! a); try congruence.
  intros.
  generalize (non_virtual_path_non_virtual_data_incl H0 H1 X0).
  destruct 1.
  generalize (H7 _  H3 _ H5).
  generalize (non_virtual_direct_base_offsets_nonempty_high_bound (intro H8) (Is_empty.path_from Is_empty_prop H0 H1) H9 H5).
  omega.

  (* disjoint paths *)
  destruct l.
   simpl.   
   inversion 3; subst.
   inversion 2; subst.
   congruence.
  inversion 3; subst.
  assert (i :: l <> nil) by congruence.
  generalize (last_nonempty H5).
  intro.
  case_eq (last (i :: l)); try congruence.
  intros until 1.
  generalize (last_correct H7).
  destruct 1.
  revert H4.
  rewrite e.
  assert {lt1 | a1 :: l1' = lt1 ++ to1 :: nil}.
   assert (a1 :: l1' <> nil) by congruence.
   generalize (last_app_left H4 (i :: l)).
   rewrite H3.
   rewrite last_complete.
   intros.
   symmetry in H8.
   eauto using last_correct.
  destruct H4.
  intro.
  rewrite app_ass in H4.
  simpl in H4.
  generalize (is_valid_repeated_subobject_split_right H4).
  functional inversion 1; subst.
  inversion 2; subst.
 assert {lt2 | a2 :: l2' = lt2 ++ to2 :: nil}.
   assert (a2 :: l2' <> nil) by congruence.
   generalize (last_app_left H15 (x ++ i0 :: nil)).
   rewrite H12.
   rewrite last_complete.
   intros.
   symmetry in H17.
   eauto using last_correct.
 destruct H15.
 revert H14.
 repeat rewrite app_ass.
 simpl.
 intro.
 generalize (is_valid_repeated_subobject_split_right H14).
 rewrite is_valid_repeated_subobject_equation.
 rewrite H13.
 destruct (In_dec super_eq_dec (Class.Inheritance.Repeated, a2) (Class.super cl1)); try congruence.
 intro.
 clear i l from H1 lf lt H2 H3 H5 H6 H7 e H4 H16 H8 H10 lf0 lt0 H11 H12 H14.
 intros until 1.
 generalize (non_virtual_subobject_offset_app_recip H1).
 destruct 1.
 invall.
 functional inversion H4; subst.
 intros until 1.
 generalize (non_virtual_subobject_offset_app_recip H2).
 rewrite H3.
 destruct 1.
 invall.
 injection H6; intro; subst.
 revert H7.
 rewrite non_virtual_subobject_offset_equation.
 rewrite H12.
 case_eq ( (non_virtual_direct_base_offsets o) ! a2 ); try congruence.
 intros.
 assert (path hierarchy to1 (a1 :: l1') a1 Class.Inheritance.Repeated) by (eleft; eauto).
 assert (path hierarchy to2 (a2 :: l2') a2 Class.Inheritance.Repeated) by (eleft; eauto).
 assert (offsets ! a1 <> None).
  functional inversion X0; subst; try congruence.
  generalize (path_last H11); simpl; congruence.
 case_eq (offsets ! a1); try congruence.
 intros.
 assert (offsets ! a2 <> None).
  functional inversion H7; subst; try congruence.
  generalize (path_last H16); simpl; congruence.
 case_eq (offsets ! a2); try congruence.
 intros.
 generalize (non_virtual_path_non_virtual_data_incl H11 H0 X0).
 destruct 1.
 generalize (H22 _ H8 _ H18).
 generalize (non_virtual_path_non_virtual_data_incl H16 H9 H7).
 destruct 1.
 generalize (H24 _ H10 _ H20).
 generalize (own_fields_offset_low_bound (intro H18)).
 generalize (own_fields_offset_low_bound (intro H20)).
 generalize (non_virtual_direct_base_nonempty_data_non_overlap (intro H12) H14 (Is_empty.path_from Is_empty_prop H11 H0) H5 (Is_empty.path_from Is_empty_prop H16 H9) H H18 H20).
 generalize (own_fields_offset_low_bound (intro H8)).
 generalize (non_virtual_data_size_own_fields_offset (intro H8)).
 generalize (own_fields_offset_low_bound (intro H10)).
 generalize (non_virtual_data_size_own_fields_offset (intro H10)).
 omega.
Qed.

(* Corollary *) Fact path_disjoint_field_zones : forall h1 l1 h2 l2,
  (h1, l1) <> (h2, l2) ->
  forall to1,
    (Is_empty to1 -> False) ->
    forall from,
      path hierarchy to1 l1 from h1 ->
        forall to2,
          (Is_empty to2 -> False) ->
          path hierarchy to2 l2 from h2 ->
            forall z1, subobject_offset from l1 = Some z1 ->
              forall z2, subobject_offset from l2 = Some z2 ->
                forall o1, offsets ! to1 = Some o1 ->
                  forall o2, offsets ! to2 = Some o2 ->
                    z1 + non_virtual_data_size o1 <= z2 + own_fields_offset o2 \/
                    z2 + non_virtual_data_size o2 <= z1 + own_fields_offset o1
                    .
Proof.
  intros.
  functional inversion H4; subst.
  functional inversion H5; subst.
  replace o0 with o in * by congruence.
  generalize (path_cons_repeated H1).
  intros.
  generalize (path_cons_repeated H3).
  intros.
  destruct (peq b b0).

  (* same virtual base *)
  subst.
  replace of0 with of in * by congruence.  
  assert (h1 = h2).
   generalize (Well_formed_hierarchy.categorize_paths Hhier H1 (refl_equal _)).
   destruct 1.
   generalize (Well_formed_hierarchy.categorize_paths Hhier H3 (refl_equal _)).
   destruct 1.
   destruct h1; destruct h2; eauto using sym_equal.
  assert (b0 :: _x <> b0 :: _x0) by congruence.
  eauto using non_virtual_path_disjoint_field_zones.

  (* different virtual bases *)
  assert (offsets ! b <> None).
   functional inversion H8; subst; try congruence.
   generalize (path_last H13); simpl; congruence.
  case_eq (offsets ! b); try congruence.
  assert (offsets ! b0 <> None).
   functional inversion H10; subst; try congruence.
   generalize (path_last H14); simpl; congruence.
  case_eq (offsets ! b0); try congruence.
  intros.
  assert (b_nonempty : Is_empty b -> False) by eauto using Is_empty.path_from.
  assert (b0_nonempty : Is_empty b0 -> False) by eauto using Is_empty.path_from.
  generalize (virtual_base_offsets_nonempty_non_overlap (intro H9) H12 H19 H15 H18 b_nonempty b0_nonempty n).
  generalize (own_fields_offset_low_bound (intro H6)).
  generalize (non_virtual_data_size_own_fields_offset (intro H6)).
  generalize (own_fields_offset_low_bound (intro H7)).
  generalize (non_virtual_data_size_own_fields_offset (intro H7)).
  generalize (non_virtual_path_non_virtual_data_incl H13 H0 H8).
  destruct 1.
  generalize (H21 _ H6 _ H19).
  generalize (non_virtual_path_non_virtual_data_incl H14 H2 H10).
  destruct 1.
  generalize (H23 _ H7 _ H18).
  omega.
Qed.

Definition Dynamic_nonempty : forall id, Is_dynamic id -> Is_empty id -> False := dynamic_nonempty (o := OP) (hierarchy := hierarchy).

Hint Resolve Dynamic_nonempty.

Fact non_virtual_path_dynamic_own_fields_offset :
 forall l from
   (* H_from_lt : Plt from cilimit *) to,
  path hierarchy to l from Class.Inheritance.Repeated ->
  Is_dynamic from ->
  forall (to_nonempty : Is_empty to -> False)
   oto, offsets ! to = Some oto ->
  forall accu z,
   non_virtual_subobject_offset accu l = Some z ->
  accu + dynamic_type_data_size PF <= z + own_fields_offset oto
.
Proof.
 induction l ; inversion 1 ; subst.
  discriminate.
 injection H0 ; intros until 2; subst. 
 destruct lf.

  (* trivial path *)
   simpl in *.
   destruct lt ; simpl in *.
    injection H1 ; intro ; subst.
    injection 4 ; intro ; subst.
    generalize (own_fields_offset_dynamic_low_bound (intro H4) H3).
    omega.
   destruct lt ; simpl in * ; discriminate.

(* non-trivial path *)
 destruct lt.
  simpl in * ; discriminate.
 simpl in H1.
 injection H1 ; intros ; subst.
 replace (i0 :: i :: lf) with ((i0 :: nil) ++ i :: lf) in H2 , H7 by reflexivity.
 generalize (is_valid_repeated_subobject_split_right H2).
 intros.
 assert (path hierarchy to (i :: lf) i Class.Inheritance.Repeated).
  econstructor.
  reflexivity.
  eassumption.
  assumption.
 generalize (non_virtual_subobject_offset_app_recip H7).
 destruct 1.
 destruct H9.
 functional inversion H9.
 subst.
 functional inversion X.
 subst.
 generalize (non_virtual_direct_base_offsets_low_bound (intro H18) H19).
 intro.
 generalize (own_fields_offset_low_bound (intro H6)).
 intros.
 assert (offsets ! i <> None).
  functional inversion H10; subst; try congruence.
  generalize (path_last H8); simpl; congruence.
 case_eq (offsets ! i); try congruence.
 intros.
 generalize (Is_empty.path_from Is_empty_prop H8 to_nonempty).
 intros.
 generalize (non_virtual_path_non_virtual_data_incl H8 to_nonempty H10).
 destruct 1.
 generalize (H17 _ H6 _ H14).
 intros.
 case_eq (primary_base o).
  intros.
  generalize (non_virtual_primary_base_offset (intro H18) H21).
  intros.
  generalize (primary_base_dynamic (intro H18) H21).
  intros.
  destruct (peq i i1).
   (* via primary base *)
   subst.
   replace of with 0 in * by congruence.
   generalize (IHl _ _ H8 H23 to_nonempty _ H6 _ _ H10).
   omega.
  (* non via primary base *)   
  generalize (primary_base_offsets_exist (intro H18) H21).
  intros.
  case_eq (offsets ! i1); try congruence.
  intros.
  generalize (dynamic_type_data_size_low_bound).
  intros.
  generalize (own_fields_offset_dynamic_low_bound (intro H25) H23).
  intros.
  generalize (non_virtual_data_size_own_fields_offset (intro H25)).
  intros.
  generalize (nonempty_non_virtual_data_size_positive (intro H14) H15).
  intros.
  generalize (non_virtual_direct_base_nonempty_data_non_overlap (intro H18) H19 H15 H22 (Dynamic_nonempty H23) n H14 H25).
  omega.

  (* no primary base *)
  intros.
  generalize (non_virtual_direct_base_offsets_dynamic_type_data_size (intro H18) H5 H21 H15 H19).
  omega.
Qed.

Fact non_virtual_path_own_fields_offset_dynamic :
 forall l from to,
  path hierarchy to l from Class.Inheritance.Repeated ->
  Is_dynamic to ->
  forall ofrom, offsets ! from = Some ofrom ->
    offsets ! to <> None ->
  forall accu z,
   non_virtual_subobject_offset accu l = Some z ->
  z + dynamic_type_data_size PF <= accu + own_fields_offset ofrom
.
Proof.
  functional inversion 5; subst.
   inversion H; subst.
   injection H4; intros; subst.
   generalize (path_last H).
   simpl.
   injection 1; intros; subst.
   generalize (own_fields_offset_dynamic_low_bound (intro H1) H0).
   omega.
  inversion H; subst.
  injection H4; intros; subst.
  destruct lt; simpl in H5; try discriminate.
  injection H5; intros; subst.
  functional inversion H8; subst.
  assert (path hierarchy to (b :: _x) b Class.Inheritance.Repeated).
   eleft; eauto.
  replace o with ofrom in * by congruence.
  assert (offsets ! b <> None).
   functional inversion X; subst; try congruence.
   generalize (path_last H10); simpl; congruence.
  case_eq (offsets ! b); try congruence.
  intros.
  case_eq (offsets ! to); try congruence.
  intros.
  generalize (non_virtual_path_non_virtual_data_incl H10 (dynamic_nonempty H0) X).
  destruct 1.
  generalize (H16 _ H13 _ H12).
  generalize (own_fields_offset_dynamic_low_bound (intro H13) H0).
  generalize (dynamic_type_data_size_low_bound PF).
  generalize (non_virtual_data_size_own_fields_offset (intro H13)).
  generalize (non_virtual_direct_base_offsets_nonempty_high_bound (intro H1) (Is_empty.path_from Is_empty_prop H10 (dynamic_nonempty H0)) H7 H12).
  omega.
Qed.

Fact non_virtual_paths_disjoint_field_dynamic_type :
 forall l1 b to1,
   path hierarchy to1 l1 b Class.Inheritance.Repeated ->
     (Is_empty to1 -> False) ->
     forall accu so1, non_virtual_subobject_offset accu l1 = Some so1 ->
       forall o1, offsets ! to1 = Some o1 ->
         forall to2,  Is_dynamic to2 ->
           forall l2,
             path hierarchy to2 l2 b Class.Inheritance.Repeated ->
               forall so2, non_virtual_subobject_offset accu l2 = Some so2 ->
                 offsets ! to2 <> None ->
                   so1 + non_virtual_data_size o1 <= so2 \/
                   so2 + dynamic_type_data_size PF <= so1 + own_fields_offset o1.
Proof.
  induction l1; inversion 1; subst; try discriminate.
  injection H0; intros until 2; subst.
  functional inversion 2; subst.
  (* l1 is trivial *)
   generalize (path_last H).
   simpl.
   injection 1; intro; subst.
   intros; eauto using non_virtual_path_own_fields_offset_dynamic.
  (* l1 is non-trivial *)
  functional inversion H2; subst.
  destruct lt; simpl in H1; try discriminate.
  injection H1; intros until 2; subst.
  assert (path hierarchy to1 (b0 :: _x) b0 Class.Inheritance.Repeated) by (eleft; eauto).
  inversion 3; subst.
  functional inversion 1; subst.
   (* l2 is trivial *)
   generalize (path_last H11).
   simpl.
   injection 1; intros; subst.
   eauto using non_virtual_path_dynamic_own_fields_offset.
  (* l2 is non-trivial *)
  intros.
  destruct lt0; simpl in H15; try discriminate.
  injection H15; intros; subst.
  functional inversion H16; subst.
  assert (path hierarchy to2 (b :: _x1) b Class.Inheritance.Repeated) by (eleft; eauto).
  replace o with o0 in * by congruence.
  destruct (peq b b0).
   (* same non-virtual bases *)
   subst.
   replace of with of0 in * by congruence.
   eauto. (* induction hypothesis *)
  (* different non-virtual bases *)
  case_eq (offsets ! to2); try congruence.
  intros.
  assert (offsets ! b <> None).
   functional inversion X1; subst; try congruence.
   generalize (path_last H19); simpl; congruence.
  case_eq (offsets ! b); try congruence.
  intros.
  assert (offsets ! b0 <> None).
   functional inversion X; subst; try congruence.
   generalize (path_last H6); simpl; congruence.
  case_eq (offsets ! b0); try congruence.
  intros.
  generalize (non_virtual_path_non_virtual_data_incl H6 H3 X).
  destruct 1.
  generalize (H30 _ H7 _ H27).
  generalize (non_virtual_path_non_virtual_data_incl H19 (dynamic_nonempty H8) X1).
  destruct 1.
  generalize (H32 _ H20 _ H23).
  generalize (dynamic_type_data_size_low_bound).
  generalize (own_fields_offset_dynamic_low_bound (intro H20) H8).
  generalize (non_virtual_data_size_own_fields_offset (intro H20)).
  generalize (own_fields_offset_low_bound (intro H7)).
  generalize (non_virtual_data_size_own_fields_offset (intro H7)).
  generalize (non_virtual_direct_base_nonempty_data_non_overlap (intro H10) H24 (Is_empty.path_from Is_empty_prop H19 (dynamic_nonempty H8)) H12 (Is_empty.path_from Is_empty_prop H6 H3) n H23 H27).
  omega.
Qed.

(* Corollary *) Fact paths_disjoint_field_dynamic_type: forall l1 b to1 h1,
   path hierarchy to1 l1 b h1 ->
     (Is_empty to1 -> False) ->
     forall so1, subobject_offset b l1 = Some so1 ->
       forall o1, offsets ! to1 = Some o1 ->
         forall to2,  Is_dynamic to2 ->
           forall l2 h2,
             path hierarchy to2 l2 b h2 ->
               forall so2, subobject_offset b l2 = Some so2 ->
                 offsets ! to2 <> None ->
                   so1 + non_virtual_data_size o1 <= so2 \/
                   so2 + dynamic_type_data_size PF <= so1 + own_fields_offset o1.
Proof.
  functional inversion 3; subst.
  functional inversion 4; subst.
  intros.
  generalize (path_cons_repeated H).
  intros.
  generalize (path_cons_repeated H7).
  intros.
  destruct (peq b0 b1).
   subst.
   replace of0 with of in * by congruence.
   eauto using non_virtual_paths_disjoint_field_dynamic_type.
  case_eq (offsets ! to2); try congruence.
  intros.
  assert (offsets ! b0 <> None).
   functional inversion H2; subst; try congruence.
   generalize (path_last H12); simpl; congruence.
  case_eq (offsets ! b0); try congruence.
  intros.
  assert (offsets ! b1 <> None).
   functional inversion H9; subst; try congruence.
   generalize (path_last H14); simpl; congruence.
  case_eq (offsets ! b1); try congruence.
  intros.
  generalize (non_virtual_path_non_virtual_data_incl H12 H0 H2).
  destruct 1.
  generalize (H21 _ H4 _ H17).
  generalize (non_virtual_path_non_virtual_data_incl H14 (dynamic_nonempty H5) H9).
  destruct 1.
  generalize (H23 _ H15 _ H19).
  generalize (dynamic_type_data_size_low_bound).
  generalize (own_fields_offset_dynamic_low_bound (intro H15) H5).
  generalize (non_virtual_data_size_own_fields_offset (intro H15)).
  generalize (own_fields_offset_low_bound (intro H4)).
  generalize (non_virtual_data_size_own_fields_offset (intro H4)).
  replace o0 with o in * by congruence.
  assert (b0_nonempty : Is_empty b0 -> False) by eauto using Is_empty.path_from.
  assert (b1_nonempty : Is_empty b1 -> False) by eauto using Is_empty.path_from, dynamic_nonempty.
  generalize (virtual_base_offsets_nonempty_non_overlap (intro H3) H6 H17 H13 H19 b0_nonempty b1_nonempty n).
  omega.
Qed.

Fact path_data_incl : forall l to from h,
  path hierarchy to l from h ->
  (Is_empty to -> False) ->
    forall o, subobject_offset from l = Some o ->
      0 <= o /\
      forall oto, offsets ! to = Some oto ->
        forall ofrom, offsets ! from = Some ofrom ->
          o + non_virtual_data_size oto <= data_size ofrom.
Proof.
  functional inversion 3; subst.
  generalize (path_cons_repeated H).
  intros.
  generalize (non_virtual_path_non_virtual_data_incl H4 H0 H2).
  destruct 1.
  generalize (virtual_base_offsets_low_bound (intro H3) H6).
  intros.
  split.
   omega.
  rewrite H3.
  injection 2; intros; subst.
  assert (offsets ! b <> None).
   functional inversion H2; subst; try congruence.
   generalize (path_last H4); simpl; congruence.
  case_eq (offsets ! b); try congruence.
  intros.
  generalize (H7 _ H9 _ H12).
  intros.
  assert (Is_empty b -> False) by eauto using Is_empty.path_from.
  generalize (virtual_base_offsets_data_size (intro H3) H6 H14 H12).  
  omega.
Qed.

Fact relative_pointer_data_incl : forall ap1 pto1 afrom asfrom ato1 i1 h1 p1,
    valid_relative_pointer hierarchy afrom asfrom ap1 ato1 i1 h1 p1 pto1 ->   
    forall (pto1_nonempty : Is_empty pto1 -> False) o1, relative_pointer_offset afrom ato1 ap1 i1 p1 = Some o1 ->
          0 <= o1 /\
          forall ofrom, offsets ! afrom = Some ofrom ->      
            forall of1, offsets ! pto1 = Some of1 ->              
              o1 + non_virtual_data_size of1 <= (asfrom - 1) * size ofrom + data_size ofrom
              .
Proof.
inversion 1; subst.
functional inversion 2; subst.
clear H H4.
dependent_revert p1.
dependent_revert ofto.
dependent_revert i1.
dependent_revert z1.
dependent_revert z2.
induction H0; subst.
(* empty array path *)
 simpl.
 injection 1; intros; subst.
 rewrite H7.
 generalize (size_positive  H7).
 intro.
 assert (0 <= size ofto) by omega.
 generalize (Zmult_ge H2 H5).
 generalize (path_data_incl H4 pto1_nonempty H8).
 destruct 1.
 intros.
 split.
  omega.
 injection 1; intro ; subst.
 intros.
 assert (i1 <= from_n - 1) by omega.
 generalize (Zmult_le_compat_r _ _ _ H14 H5).
 generalize (H10 _ H13 _ H7).
 omega.
(* nonempty array path *)
intros.
revert H6.
rewrite array_path_offset_equation.
case_eq (offsets ! from); try congruence.
intros until 1.
case_eq (subobject_offset from l); try congruence.
intros until 1.
rewrite (path_last H1).
case_eq (offsets ! through); try congruence.
intros until 1.
rewrite H4.
case_eq (assoc (FieldSignature.eq_dec (A := A)) fs (field_offsets t1)); try congruence.
intros.
generalize (array_path_offset_rewrite H15 0).
intros.
assert (offsets ! by <> None).
 functional inversion H16; subst; try congruence.
 inversion H5; congruence.
case_eq (offsets ! by); try congruence.
intros until 1.
generalize (IHvalid_array_path _ _ H16 _ H7 H8 _ H9 _ H10 H11).
destruct 1.
assert (forall ty n, FieldSignature.type fs = FieldSignature.Struct ty n -> Is_empty ty -> False).
 rewrite H4.
 injection 1; intros; subst.
 eauto using Is_empty.path_from, Is_empty.array_path_from.
generalize (field_offsets_low_bound (intro H13) H14).
generalize (non_virtual_data_size_field_offsets (intro H13) H14 H21).
unfold field_data_size.
rewrite H4.
rewrite H18.
intro.
generalize (H22 _ (refl_equal _)).
clear H22.
assert (Is_empty through -> False).
 intros.
 eapply H21.
 eassumption.
 eapply Is_empty.fields_struct_empty.
 eassumption.
 eassumption.
 eassumption.
 eassumption.
 eassumption.
generalize (path_data_incl H1 H22 H12).
destruct 1.
generalize (H24 _ H13 _ H6).
assert (0 <= size t0).
 generalize (size_positive H6).
 omega.
generalize (Zmult_ge H H25).
assert (p <= from_n - 1) by omega.
generalize (Zmult_le_compat_r _ _ _ H26 H25).
intros.
split.
omega.
injection 1; intros; subst.
generalize (H20 _ H18 _ H34).
omega.
Qed.

(* Corollary *) Fact relative_pointer_alt_fields_incl : forall afrom zfrom ato pto i h p f,
  valid_relative_pointer_alt hierarchy afrom zfrom ato pto (relative_pointer_alt_intro i (h, p) f) ->  
  forall (is_empty_pto : Is_empty pto -> False) of, relative_pointer_alt_offset (relative_pointer_alt_intro i (h, p) f) afrom ato = Some of ->
    forall ofrom, offsets ! afrom = Some ofrom ->
      forall ofp, subobject_offset afrom p = Some ofp ->
        forall pato, last p = Some pato ->
          forall oato, offsets ! pato = Some oato ->        
            forall opto, offsets ! pto = Some opto ->
              i * size ofrom + ofp <= of /\             
              i * size ofrom + ofp + own_fields_offset oato <= of + own_fields_offset opto /\
              of + non_virtual_data_size opto <= i * size ofrom + ofp + non_virtual_data_size oato.
Proof.
  inversion 1; subst.
  simpl.
  intros.
  revert H3 H0.
  rewrite H1.
  rewrite H2.
  rewrite (path_last H6).
  injection 1; intro; subst.
  rewrite H8.
  destruct f.
   (* some field *)
   destruct p0.
   destruct p0.
   destruct p0.
   destruct p1.
   invall.
   rewrite H10.
   case_eq (assoc (FieldSignature.eq_dec (A := A)) t0 (field_offsets oato)); try congruence.
   intros until 1.
   case_eq (relative_pointer_offset x0 ato a z l); try congruence.
   injection 2; intros; subst.
   generalize (field_offsets_nonempty_low_bound (intro H8) H11).
   assert (x0_nonempty : forall (ty : ident) (n : positive),
     FieldSignature.type t0 = FieldSignature.Struct ty n ->
     Is_empty ty -> False).    
    rewrite H10.
    injection 1; intros; subst.
    eauto using Is_empty.relative_pointer_from.
   intro.
   generalize (H15 x0_nonempty).
   assert (offsets ! x0 <> None).
    functional inversion H13; subst.
    inversion H12; subst.
    functional inversion H17; subst; try congruence.
    inversion H16; subst; congruence.
   case_eq (offsets ! x0); try congruence.
   intros.   
   generalize (relative_pointer_data_incl H12 is_empty_pto H13).
   destruct 1.
   generalize (own_fields_offset_low_bound (intro H9)).
   intros.
   generalize (H20 _ H17 _ H9).
   intros.
   generalize (non_virtual_data_size_field_offsets (intro H8) H11 x0_nonempty).
   unfold field_data_size.
   rewrite H10.
   rewrite H17.
   intros.
   generalize (H23 _ (refl_equal _)).
   intros.
   generalize (own_fields_offset_low_bound (intro H8)).
   omega.
 (* no field *)
 injection 1; intros; subst.
 invall.
 subst.
 replace oato with opto in * by congruence.
 omega.
Qed.

(** * Proof of field access (5.1) *)

(** 5.1 Theorem 1 *)
Theorem scalar_fields_disjoint :
  forall ap1 pto1 afrom asfrom ato1 i1 h1 p1,
    valid_relative_pointer hierarchy afrom asfrom ap1 ato1 i1 h1 p1 pto1 ->
    forall ap2 pto2 ato2 i2 h2 p2,
    valid_relative_pointer hierarchy afrom asfrom ap2 ato2 i2 h2 p2 pto2 ->    
    forall o1, relative_pointer_offset afrom ato1 ap1 i1 p1 = Some o1 ->
      forall o2, relative_pointer_offset afrom ato2 ap2 i2 p2 = Some o2 ->
        forall of1, offsets ! pto1 = Some of1 ->
          forall of2, offsets ! pto2 = Some of2 ->            
            forall f1 fo1, assoc (FieldSignature.eq_dec (A := A)) f1 (field_offsets of1) = Some fo1 ->
              forall ty1, FieldSignature.type f1 = FieldSignature.Scalar ty1 ->
                forall f2 fo2, assoc (FieldSignature.eq_dec (A := A)) f2 (field_offsets of2) = Some fo2 ->
                  forall ty2, FieldSignature.type f2 = FieldSignature.Scalar ty2 ->
                    ((ap1, i1, (h1, p1)), f1) <> ((ap2, i2, (h2, p2)), f2) ->
                    o1 + fo1 + typ_size PF ty1 <= o2 + fo2 \/
                    o2 + fo2 + typ_size PF ty2 <= o1 + fo1
                    .
Proof.
  (* symmetry *)
  cut (
  forall ap1 ap2,
    (length ap1 <= length ap2)%nat ->
    forall pto1 afrom asfrom ato1 i1 h1 p1,
    valid_relative_pointer hierarchy afrom asfrom ap1 ato1 i1 h1 p1 pto1 ->
    forall pto2 ato2 i2 h2 p2,
    valid_relative_pointer hierarchy afrom asfrom ap2 ato2 i2 h2 p2 pto2 ->    
    forall o1, relative_pointer_offset afrom ato1 ap1 i1 p1 = Some o1 ->
      forall o2, relative_pointer_offset afrom ato2 ap2 i2 p2 = Some o2 ->
        forall of1, offsets ! pto1 = Some of1 ->
          forall of2, offsets ! pto2 = Some of2 ->            
            forall f1 fo1, assoc (FieldSignature.eq_dec (A := A)) f1 (field_offsets of1) = Some fo1 ->
              forall ty1, FieldSignature.type f1 = FieldSignature.Scalar ty1 ->
                forall f2 fo2, assoc (FieldSignature.eq_dec (A := A)) f2 (field_offsets of2) = Some fo2 ->
                  forall ty2, FieldSignature.type f2 = FieldSignature.Scalar ty2 ->
                    ((ap1, i1, (h1, p1)), f1) <> ((ap2, i2, (h2, p2)), f2) ->
                    o1 + fo1 + typ_size PF ty1 <= o2 + fo2 \/
                    o2 + fo2 + typ_size PF ty2 <= o1 + fo1
  ).
   intros.
   destruct (le_lt_dec (length ap1) (length ap2)); eauto.
   assert (length ap2 <= length ap1)%nat by omega.
   assert (((ap2, i2, (h2, p2)), f2) <> ((ap1, i1, (h1, p1)), f1)) by congruence.
   assert (forall A B : Prop, A \/ B -> B \/ A) by tauto.
   eauto.
   (* induction on the length of the array path *) 
 intro ap1.
 var (length ap1).
 dependent_revert ap1.
 induction v using  (well_founded_induction Wf_nat.lt_wf).
 (* alternative pointer representation *)
 intros.
 subst.
 assert (pto1_nonempty: Is_empty pto1 -> False).
  intros.
  assert ( assoc (FieldSignature.eq_dec (A := A)) f1 (field_offsets of1) <> None) by congruence.  
  assert (offsets ! pto1 <> None) by congruence.
  generalize (guard H14).
  intros.
  case_eq (hierarchy ! pto1); try congruence.
  intros.
  generalize (field_offsets_guard (intro H6) H13 H16).
  intros.
  eauto using Is_empty.no_scalar_fields.
 assert (pto2_nonempty: Is_empty pto2 -> False).
  intros.
  assert ( assoc (FieldSignature.eq_dec (A := A)) f2 (field_offsets of2) <> None) by congruence.  
  assert (offsets ! pto2 <> None) by congruence.
  generalize (guard H14).
  intros.
  case_eq (hierarchy ! pto2); try congruence.
  intros.
  generalize (field_offsets_guard (intro H7) H13 H16).
  intros.
  eauto using Is_empty.no_scalar_fields.  
 assert ((relative_pointer_alt_of_relative_pointer ap1 i1 (h1, p1), f1) <> (relative_pointer_alt_of_relative_pointer ap2 i2 (h2, p2), f2)).
 assert (
 (relative_pointer_of_relative_pointer_alt
     (relative_pointer_alt_of_relative_pointer (A:=A) ap1 i1 (h1, p1)), f1) <>  (relative_pointer_of_relative_pointer_alt
     (relative_pointer_alt_of_relative_pointer (A:=A) ap2 i2 (h2, p2)), f2) 
 ).
  rewrite relative_pointer_default_to_alt_to_default.
  rewrite relative_pointer_default_to_alt_to_default.
  assumption. 
  congruence.
 clear H12.
 revert H0.
 revert H1 H.
 rewrite <- (relative_pointer_alt_length_correct ap1 i1 (h1, p1)).
 rewrite <- (relative_pointer_alt_length_correct ap2 i2 (h2, p2)).
 generalize (valid_relative_pointer_valid_relative_pointer_alt H2).
 generalize (relative_pointer_alt_offset_correct H2 H4).
 clear H2 H4.
 generalize (valid_relative_pointer_valid_relative_pointer_alt H3).
 generalize (relative_pointer_alt_offset_correct H3 H5).
 clear H3 H5.
 destruct (relative_pointer_alt_of_relative_pointer ap1 i1 (h1, p1)).
 destruct (relative_pointer_alt_of_relative_pointer ap2 i2 (h2, p2)).
 clear ap1 i1 h1 p1 ap2 i2 h2 p2.
 intros.
 inversion H0; subst.
 rename H0 into J0.
 inversion H2; subst.
 rename H2 into J2.
 generalize H.
 rename H into J.
 unfold relative_pointer_alt_offset.
 case_eq (offsets ! afrom); try congruence.
 intros until 1.
 case_eq (subobject_offset afrom p'); try congruence.
 intros.
 generalize H1.
 rename H1 into J1.
 unfold relative_pointer_alt_offset.
 rewrite H.
 case_eq (subobject_offset afrom p'0); try congruence.
 intros.
 assert (offsets ! through <> None).
  destruct f0.
   destruct p.
   destruct p.
   destruct p.
   destruct p0.
   destruct (FieldSignature.type t1); try congruence.
   rewrite (path_last H17) in H2.
   destruct (offsets ! through); try congruence.
  invall; congruence.
 case_eq (offsets ! through); try congruence.
 intros.
 assert (offsets ! through0 <> None).
  destruct f.
   destruct p.
   destruct p.
   destruct p.
   destruct p0.
   destruct (FieldSignature.type t2); try congruence.
   rewrite (path_last H20) in H12.
   destruct (offsets ! through0); try congruence.
  invall; congruence.
 case_eq (offsets ! through0); try congruence.
 intros.  
 generalize (relative_pointer_alt_fields_incl J0 pto2_nonempty J H H0).
 rewrite (path_last H17).
 intros.
 generalize (H25 _ (refl_equal _)).
 clear H25.
 rewrite H22.
 rewrite H7.
 intros.
 generalize (H25 _ (refl_equal _) _ (refl_equal _)).
 clear H25.
 destruct 1 as [_ [? ?]].
 generalize (relative_pointer_alt_fields_incl J2 pto1_nonempty J1 H H1).
 rewrite (path_last H20).
 intros.
 generalize (H27 _ (refl_equal _)).
 clear H27.
 rewrite H24.
 rewrite H6.
 intros.
 generalize (H27 _ (refl_equal _) _ (refl_equal _)).
 clear H27.
 destruct 1 as [_ [? ?]].
 assert (Is_empty through0 -> False).
  destruct f; invall; subst; try congruence.
  destruct p.
  destruct p.
  destruct p.
  destruct p0.
  invall.
  inversion H32; subst.
  intros.
  apply pto1_nonempty.
  eapply Is_empty.path_to.
  eassumption.
  eassumption.
  eapply Is_empty.array_path_to.
  eassumption.
  eassumption.
  eapply Is_empty.fields_struct_empty.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
 assert (Is_empty through -> False).
  destruct f0; invall; subst; try congruence.
  destruct p.
  destruct p.
  destruct p.
  destruct p0.
  invall.
  inversion H33; subst.
  intros.
  apply pto2_nonempty.
  eapply Is_empty.path_to.
  eassumption.
  eassumption.
  eapply Is_empty.array_path_to.
  eassumption.
  eassumption.
  eapply Is_empty.fields_struct_empty.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  assert (forall ty n,
    FieldSignature.type f1 = FieldSignature.Struct ty n ->
    Is_empty ty -> False).
   rewrite H9; congruence.
  assert (forall ty n,
    FieldSignature.type f2 = FieldSignature.Struct ty n ->
    Is_empty ty -> False).  
   rewrite H11; congruence.
  generalize (field_offsets_nonempty_low_bound (intro H6) H8 H31).
  intros.
  generalize (non_virtual_data_size_field_offsets (intro H6) H8 H31).
  unfold field_data_size.
  rewrite H9.
  intros.
  generalize (H34 _ (refl_equal _)).
  clear H34.
  intros.
  generalize (field_offsets_nonempty_low_bound (intro H7) H10 H32).
  intros.
  generalize (non_virtual_data_size_field_offsets (intro H7) H10 H32).
  unfold field_data_size.
  rewrite H11.
  intros.
  generalize (H36 _ (refl_equal _)).
  clear H36.
  intros.
  generalize (typ_size_positive PF ty1).
  intros.
  generalize (typ_size_positive PF ty2).
  intros.
  generalize (path_data_incl H17 H30 H0).
  destruct 1.
  generalize (H40 _ H22 _ H).
  intros.
  generalize (data_size_high_bound (intro H)).
  intros.
  generalize (path_data_incl H20 H29 H1).
  destruct 1.
  generalize (H44 _ H24 _ H).
  intros.
  generalize (own_fields_offset_low_bound (intro H22)).
  intros.
  generalize (own_fields_offset_low_bound (intro H24)).
  intros.

 (* case analysis *)
 destruct (Z_eq_dec i i0).
  Focus 2.
  (* different cells *) 
  generalize (size_positive H).
  intros.
  generalize (array_cells_disjoint n H48).
  omega.
 (* same cells *)
 subst.
 destruct (list_eq_dec peq p' p'0).
  Focus 2.
  (* different paths *)
  assert ((h', p') <> (h'0, p'0)) by congruence.
  generalize (path_disjoint_field_zones H48 H30 H17 H29 H20 H0 H1 H22 H24).
  omega.
 (* same paths *)  
 subst.
 assert (h' = h'0) by eauto using Well_formed_hierarchy.path_eq_hierarchy_eq.
 subst.
 assert (through = through0).
  generalize (path_last H17).
  generalize (path_last H20).
  congruence.
 subst.
 destruct (option_eq_dec 
   (prod_eq_dec
     (prod_eq_dec
       (prod_eq_dec (FieldSignature.eq_dec (A := A)) (array_path_eq_dec (A := A)))
       Z_eq_dec)
     (prod_eq_dec Class.Inheritance.eq_dec (list_eq_dec peq)))
   f f0).
  (* same field paths *)
   subst.
   assert (pto1 = pto2 /\ o1 = o2).
    destruct f0.
     destruct p.
     destruct p.
     destruct p.
     destruct p0.
     invall.
     replace x3 with x1 in * by congruence.
     replace x4 with x2 in * by congruence.
     generalize (valid_relative_pointer_last H51 H54).
     destruct 1; subst.
     split.
      reflexivity.
     congruence.
    invall.
    split; congruence.
   destruct H48.
   subst.
   assert (f1 <> f2) by congruence.
   replace of1 with of2 in * by congruence.
   generalize (field_offsets_non_overlap (intro H6) H8 H10 H31 H32 H48).
   unfold field_data_size.
   rewrite H9.
   rewrite H11.
   intros.
   generalize (H49 _ (refl_equal _) _ (refl_equal _)).
   omega.
  (* different field paths *)
  replace z with z0 in * by congruence.
  replace t1 with t2 in * by congruence.
  destruct f0.
  Focus 2.
   destruct f.
    simpl in H3.
    destruct p.
    destruct p.
    destruct p.
    omega. (* banned by symmetry *)
   congruence.
  destruct p.
  destruct p.
  destruct p.
  destruct p0.
  invall.
  revert H2 H21 H12.
  rewrite H49.
  rewrite (path_last H17).
  rewrite H22.
  case_eq (
    assoc (FieldSignature.eq_dec (A := A)) t3 (field_offsets t2)
  ); try congruence.
  case_eq (
    relative_pointer_offset x0 ato2 a z1 l
  ); try congruence.
  injection 3; intro; subst.
  rewrite H18.
  intro.
  assert (offsets ! x0 <> None).
   functional inversion H2; subst.
   functional inversion H53; subst; try congruence.
   inversion H51; subst.
   inversion H52; congruence.
  case_eq (offsets ! x0); try congruence.
  intros until 1.
  generalize (relative_pointer_data_incl H51 pto2_nonempty H2).
  destruct 1.
  generalize (H55 _ H53 _ H7).
  intros until 1.
  assert (forall ty n, FieldSignature.type t3 = FieldSignature.Struct ty n -> Is_empty ty -> False).
   rewrite H49.
   injection 1; intros; subst.
   apply pto2_nonempty.
   eapply Is_empty.relative_pointer_to.
   eassumption.
   eassumption.
   assumption.
  destruct f.
   destruct p.
   destruct p.
   destruct p.
   destruct p0.
   invall.
   injection H50; intro; subst.
   rewrite H59.
   case_eq (
     assoc (FieldSignature.eq_dec (A := A)) t6 (field_offsets t2)
   ); try congruence.
   case_eq (
     relative_pointer_offset x3 ato1 a0 z4 l0
   ); try congruence.
   injection 3; intros; subst.
   simpl in H3.
   simpl in H4.
   assert (length a0 <= length a)%nat by omega.
   assert (length a0 < S (length a0))%nat by omega.
   destruct ((FieldSignature.eq_dec (A := A)) t6 t3).
    (* same through field *)
    subst.
    assert (
      (a0, z4, (t7, l0), f1) <> (a, z1, (t4, l), f2)
    ) by congruence.
   replace x3 with x0 in * by congruence.
   replace x4 with x1 in * by congruence.
   generalize (H4 _ H65 _ (refl_equal _) _ H64 _ _ _ _ _ _ _ H61 _ _ _ _ _ H51 _ H60 _ H2 _ H6 _ H7 _ _ H8 _ H9 _ _ H10 _ H11 H66). (* induction hypothesis *)
   replace z6 with z3 in * by congruence.
   omega.
  (* different fields *)
  generalize (relative_pointer_data_incl H61 pto1_nonempty H60).
  destruct 1.
  assert (offsets ! x3 <> None).
   functional inversion H60; subst.
   functional inversion H69; subst; try congruence.
   inversion H61; subst.
   inversion H68; congruence.
  case_eq (offsets ! x3); try congruence.
  intros.
  generalize (H67 _ H69 _ H6).
  intros.
  assert (forall ty n, FieldSignature.type t6 = FieldSignature.Struct ty n -> Is_empty ty -> False).
    rewrite H59.
    injection 1; intros; subst.
    apply pto1_nonempty.
    eapply Is_empty.relative_pointer_to.
    eassumption.
    eassumption.
    assumption.
   generalize (field_offsets_non_overlap (intro H22) H62 H12 H71 H57 n0).
    unfold field_data_size.
    rewrite H49.
    rewrite H53.
    rewrite H59.
    rewrite H69.
    intros.
    generalize (H72 _ (refl_equal _) _ (refl_equal _)).
    intros.
    generalize (own_fields_offset_low_bound (intro H6)).
    generalize (own_fields_offset_low_bound (intro H7)).
    omega.
  (* one scalar field and one struct field *)
  injection 1; intros; subst.
  invall; subst.
  replace of1 with t2 in * by congruence.
  assert (f1 <> t3) by congruence.
  generalize (field_offsets_non_overlap (intro H22) H8 H12 H31 H57 H50).
  unfold field_data_size.
  rewrite H9.
  rewrite H49.
  rewrite H53.
  intros.
  generalize (H59 _ (refl_equal _) _ (refl_equal _)).
  generalize (own_fields_offset_low_bound (intro H7)).
  omega.
Qed.

(** * Proof of field access in the presence of dynamic type data (5.4) *)

(** 5.4 Theorem 5 *)
Theorem scalar_field_dynamic_type_data_disjoint :
  forall ap1 pto1 afrom asfrom ato1 i1 h1 p1,
    valid_relative_pointer hierarchy afrom asfrom ap1 ato1 i1 h1 p1 pto1 ->
    forall ap2 pto2 ato2 i2 h2 p2,
    valid_relative_pointer hierarchy afrom asfrom ap2 ato2 i2 h2 p2 pto2 ->    
    forall o1, relative_pointer_offset afrom ato1 ap1 i1 p1 = Some o1 ->
      forall o2, relative_pointer_offset afrom ato2 ap2 i2 p2 = Some o2 ->
        forall of1, offsets ! pto1 = Some of1 ->
          offsets ! pto2 <> None ->
            forall f1 fo1, assoc (FieldSignature.eq_dec (A := A)) f1 (field_offsets of1) = Some fo1 ->
              forall ty1, FieldSignature.type f1 = FieldSignature.Scalar ty1 ->
                Is_dynamic pto2 ->
                o1 + fo1 + typ_size PF ty1 <= o2 \/
                o2 + dynamic_type_data_size PF <= o1 + fo1
                .
Proof.
  intro.
  var (length ap1).
  revert ap1 H.
  induction v using (well_founded_induction Wf_nat.lt_wf).
  intros until 5.
  subst.
  generalize (valid_relative_pointer_valid_relative_pointer_alt H1).
  generalize (valid_relative_pointer_valid_relative_pointer_alt H2).
  generalize (relative_pointer_alt_offset_correct H1 H3).
  clear H1 H3.
  generalize (relative_pointer_alt_offset_correct H2 H4).
  clear H2 H4.
  revert H.
  rewrite <- (relative_pointer_alt_length_correct ap1 i1 (h1, p1)).
  destruct (relative_pointer_alt_of_relative_pointer ap1 i1 (h1, p1)).
  clear ap1 i1 h1 p1.
  destruct (relative_pointer_alt_of_relative_pointer ap2 i2 (h2, p2)).
  clear ap2 i2 h2 p2.
  intros.
  inversion H2; subst.
  inversion H3; subst.
  generalize H0 H1.
  unfold relative_pointer_alt_offset.
  case_eq (offsets ! afrom); try congruence.
  intros until 1.
  case_eq (subobject_offset afrom p'); try congruence.
  intros until 1.
  rewrite (path_last H14).
  case_eq (subobject_offset afrom p'0); try congruence.
  intros until 1.
  rewrite (path_last H18).
  intros until 2.
  assert (offsets ! through <> None).
   revert H20.
   destruct f0.
    case_eq (offsets ! through); try congruence.
    destruct p.
    destruct p.
    destruct p.
    destruct p0.
    invall.
    rewrite H22.
    congruence.
   invall; congruence.
  revert H20.
  case_eq (offsets ! through); try congruence.
  intros.
  assert (offsets ! through0 <> None).
   revert H21.
   destruct f.
    case_eq (offsets ! through0); try congruence.
    destruct p.
    destruct p.
    destruct p.
    destruct p0.
    invall.
    rewrite H24.
    congruence.
   invall; congruence.
  revert H21.
  case_eq (offsets ! through0); try congruence.
  intros.
  assert (pto1_nonempty : Is_empty pto1 -> False).
   assert (offsets ! pto1 <> None) by congruence.
   generalize (guard H26).
   intros.
   case_eq (hierarchy ! pto1); try congruence.
   intros.
   assert (assoc (FieldSignature.eq_dec (A := A)) f1 (field_offsets of1) <> None) by congruence.
   generalize (field_offsets_guard (intro H4) H30 H29).
   intros.
   eauto using Is_empty.no_scalar_fields.
  assert (pto2_nonempty : Is_empty pto2 -> False) by eauto using dynamic_nonempty.
  generalize (relative_pointer_alt_fields_incl H3 pto1_nonempty H1 H9 H11 (path_last H18) H21 H4).
  destruct 1.
  invall.
  case_eq (offsets ! pto2); try congruence.
  intros.
  generalize (dynamic_type_data_size_low_bound).
  intros.
  generalize (own_fields_offset_dynamic_low_bound (intro H27) H8).
  intros.
  generalize (non_virtual_data_size_own_fields_offset (intro H27)).
  intros.
  generalize (own_fields_offset_low_bound (intro H4)).
  intros.
  assert (forall ty n, FieldSignature.type f1 = FieldSignature.Struct ty n -> Is_empty ty -> False).
   intros; congruence.
  generalize (field_offsets_nonempty_low_bound (intro H4) H6 H34).
  intros.
  generalize (non_virtual_data_size_field_offsets (intro H4) H6 H34).
  unfold field_data_size.
  rewrite H7.
  intro.
  generalize (H36 _ (refl_equal _)).
  clear H36.
  intros.
  generalize (typ_size_positive PF ty1).
  intros.
  generalize (relative_pointer_alt_fields_incl H2 pto2_nonempty H0 H9 H10 (path_last H14) H20 H27).
  destruct 1.
  invall.
  assert (Is_empty through -> False).
   destruct f0 as [[[[? ?] ?] [? ?]] |]; invall; subst; try assumption.
   intros; apply pto2_nonempty.
   eapply Is_empty.relative_pointer_to; try eassumption.
   eapply Is_empty.fields_struct_empty; eassumption.
  assert (Is_empty through0 -> False).
   destruct f as [[[[? ?] ?] [? ?]] |]; invall; subst; try assumption.
   intros; apply pto1_nonempty.
   eapply Is_empty.relative_pointer_to; try eassumption.
   eapply Is_empty.fields_struct_empty; eassumption.
  generalize (own_fields_offset_low_bound (intro H20)).
  intros.
  generalize (own_fields_offset_low_bound (intro H21)).
  intros.
  

  (* Say that a pointer is "simple" iff it traverses no struct field, "complex" otherwise.
     6 cases :
     - same array cell
        - ap2 (towards the dynamic class pto2) is complex
           - and same inheritance path from this cell
             - ap1 (towards field f1) is complex
               1. struct fields targeted by both : use induction hypothesis
               2. different struct fields : they are disjoint
             3. ap1 is simple : p points to the scalar field, which is disjoint from the struct field pointed to within ap2
           4. different inheritance paths from the same cell : they are disjoint field zones
         5. ap2 is simple : disjoint field zone and dynamic type data.
      6. different array cells : disjoint data         
      *)
  destruct (Z_eq_dec i i0).
   (* same cell *)
   subst.      
   destruct f0  as [[[[? ?] ?] [? ?]] |].
   (* ap2 is complex *)
   invall.
   revert H23.
   rewrite H46.
   case_eq (assoc (FieldSignature.eq_dec (A := A)) t4 (field_offsets t1)); try congruence.
   intros until 1.
   case_eq (relative_pointer_offset x0 ato2 a z1 l); try congruence.
   injection 2; intros; subst.
   assert (offsets ! x0 <> None).
    inversion H48; subst.
    functional inversion H47; subst.
    functional inversion H55; subst; try congruence.
    inversion H50; congruence.
   case_eq (offsets ! x0); try congruence.
   intros. 
   generalize (relative_pointer_data_incl H48 pto2_nonempty H47).
   destruct 1.
   generalize (H53 _ H51 _ H27).
   intros.
   assert (forall ty n, FieldSignature.type t4 = FieldSignature.Struct ty n -> Is_empty ty -> False).
    rewrite H46.
    injection 1; intros; subst.
    apply pto2_nonempty.
    eapply Is_empty.relative_pointer_to; eassumption.
   generalize (field_offsets_nonempty_low_bound (intro H20) H23 H55) .
   intros.
   generalize (non_virtual_data_size_field_offsets (intro H20) H23 H55).
   unfold field_data_size.
   rewrite H46.
   rewrite H51.
   intros.
   generalize (H57 _ (refl_equal _)).
   clear H57.
   intros.
   destruct (list_eq_dec peq p'0 p').
    (* same inheritance paths *)
    subst.
    assert (through0 = through).
     generalize (path_last H18).
     generalize (path_last H14).
     congruence.
    subst.
    replace t2 with t1 in * by congruence.
    replace z0 with z in * by congruence.
    replace h'0 with h' in * by eauto using Well_formed_hierarchy.path_eq_hierarchy_eq.
    destruct f as  [[[[? ?] ?] [? ?]] |].
     (* ap1 is complex *)
     invall.
     revert H25.
     rewrite H59.
     case_eq ( assoc (FieldSignature.eq_dec (A := A)) t7 (field_offsets t1)); try congruence.
     intros until 1.
     case_eq (relative_pointer_offset x3 ato1 a0 z4 l0); try congruence.
     injection 2; intros; subst.
     destruct ((FieldSignature.eq_dec (A := A)) t4 t7).
      (* 1/6. same structure field : use induction hypothesis *)
      subst.
      replace x3 with x0 in * by congruence.
      replace x4 with x1 in * by congruence.
      replace z5 with z2 in * by congruence.
      simpl in H.
      generalize (H _ (lt_n_Sn _) _ (refl_equal _) _ _ _ _ _ _ _ H61 _ _ _ _ _ _ H48 _ H60 _ H47 _ H4 H5 _ _ H6 _ H7 H8).
      omega.
     (* 2/6 : different structure fields : they are disjoint *)
     assert (offsets ! x3 <> None).
      functional inversion H60; subst.
      functional inversion H64; subst; try congruence.
      inversion H61; subst.
      inversion H63; congruence.
     case_eq (offsets ! x3); try congruence.
     intros.
     assert (forall ty n, FieldSignature.type t7 = FieldSignature.Struct ty n -> Is_empty ty -> False).
      rewrite H59.
      injection 1; intros; subst.
      apply pto1_nonempty.
      eapply Is_empty.relative_pointer_to; eassumption.
     generalize (relative_pointer_data_incl H61 pto1_nonempty H60).
     destruct 1.
     generalize (H67 _ H64 _ H4).
     intros.
     generalize (field_offsets_non_overlap (intro H20) H23 H25 H55 H65 n).
     unfold field_data_size.
     rewrite H59.
     rewrite H64.
     rewrite H46.
     rewrite H51.
     intros.
     generalize (H69 _ (refl_equal _) _ (refl_equal _)).
     omega.
    (* 3/6 : ap1 is simple, so the scalar field is disjoint from the struct field of the complex ap2 *)
    invall; subst.
    replace of1 with t1 in * by congruence.
    injection H25; intros; subst.
    assert (f1 <> t4) by congruence.
    generalize (field_offsets_non_overlap (intro H4) H6 H23 H34 H55 H19).
    unfold field_data_size.
    rewrite H7.
    rewrite H46.
    rewrite H51.
    intros.
    generalize (H58 _ (refl_equal _) _ (refl_equal _)).
    omega.    
   (* 4/6 : p'0 <> p' : different inheritance paths to through, through'. In this case, their field data are disjoint. As pto2 is in ap2's field data, QED *)
   assert ((h'0, p'0) <> (h', p')) by congruence.
   generalize (path_disjoint_field_zones H58 H42 H18 H39 H14 H11 H10 H21 H20).
   omega.
  (* 5/6 : ap2 is simple : the field zone of ap1 (in which the scalar field is necessarily located) is disjoint from the dynamic data of ap2 *)
  invall; subst.
  injection H23; intros; subst.
  replace t3 with t1 in * by congruence.
  generalize (paths_disjoint_field_dynamic_type H18 H42 H11 H21 H8 H14 H10 H5).
  omega.
 (* 6/6. i <> i0 : different cells *)
 generalize (path_data_incl  H14 H39 H10).
 destruct 1.
 generalize (H46 _ H20 _ H9).
 intros.
 generalize (path_data_incl H18 H42 H11).
 destruct 1.
 generalize (H49 _ H21 _ H9).
 intros.
 generalize (size_positive H9).
 intros.
 generalize (array_cells_disjoint n H51).
 generalize (data_size_high_bound (intro H9)).
 omega.
Qed.

(** * Preservation of dynamic type data (5.4) *)

Section Primary_paths.

Function is_primary_path (p : list ident) {struct p} : bool :=
match p with
| nil => false
| a :: p' =>
  match p' with
    | nil => true
    | a' :: _ =>
      match offsets ! a with
        | None => false
        | Some o =>
          if (option_eq_dec peq (primary_base o) (Some a')) then is_primary_path p' else false
      end
  end
end.

Fact primary_path_offset : forall p,
 is_primary_path p = true ->
 forall accu, non_virtual_subobject_offset accu p = Some accu.
Proof.
 intro p.
 functional induction (is_primary_path p) ; try congruence.

  intros _.
  simpl.
  trivial.

 intros.
 change (non_virtual_subobject_offset accu (a :: a' :: _x))
 with
 (match offsets ! a with
  | None => None
  | Some o0 =>
    match (non_virtual_direct_base_offsets o0) ! a' with
    | Some oa' => non_virtual_subobject_offset (accu + oa') (a' :: _x)
    | None => None
    end
  end).
 rewrite e1.
 rewrite (non_virtual_primary_base_offset (intro e1) _x0).
 replace (accu + 0) with accu by omega.
 auto.
Qed.

Fact non_primary_path_offset : forall p,
  is_primary_path p = false ->
  forall from to, path hierarchy to p from Class.Inheritance.Repeated ->
    (Is_dynamic from) ->
    (Is_empty to -> False) ->
    offsets ! to <> None ->
    forall accu of, non_virtual_subobject_offset accu p = Some of -> accu + dynamic_type_data_size PF <= of.
Proof.
 intros p.
 functional induction (is_primary_path p) ; try congruence.

  inversion 2 ; discriminate.

  functional inversion 6 ; subst; congruence.
  
  functional inversion 6 ; subst.
  inversion H0; subst.
  destruct lt; simpl in H6; try discriminate.
  injection H5; intros; subst.
  injection H6; intros; subst.
  functional inversion H7; subst.
  assert (path hierarchy to (a' :: _x) a' Class.Inheritance.Repeated) by (eleft; eauto).
  generalize (non_virtual_primary_base_offset (intro e1) _x0).
  intros.
  replace of0 with 0 in * by congruence.
  replace accu with (accu + 0) by omega.
  generalize (primary_base_dynamic (intro e1) _x0).
  intros.
  eauto. (* IH *)

 functional inversion 6; subst.
 inversion H0; subst.
 injection H5; intros; subst.
 destruct lt; simpl in H6; try discriminate.
 injection H6; intros; subst.
 functional inversion H7; subst.
 assert (path hierarchy to (a' :: _x) a' Class.Inheritance.Repeated) by (eleft; eauto).
 assert (Is_empty a' -> False) by eauto using Is_empty.path_from.
 generalize (non_virtual_path_non_virtual_data_incl H9 H2 X).
 destruct 1.
 replace o0 with o in * by congruence.
 case_eq (primary_base o).

  intros.
  assert (i0 <> a') by congruence.
  generalize (non_virtual_primary_base_offset (intro e1) H16).
  intros.
  generalize (primary_base_offsets_exist (intro e1) H16).
  intros.
  case_eq (offsets ! i0); try congruence.
  intros.
  assert (offsets ! a' <> None).
   functional inversion X; subst; try congruence.
   generalize (path_last H9); simpl; congruence.
  case_eq (offsets ! a'); try congruence.
  intros.
  generalize (primary_base_dynamic (intro e1) H16).
  intros.
  generalize (Dynamic_nonempty H24).
  intros.
  generalize dynamic_type_data_size_low_bound.
  intros.
  generalize (own_fields_offset_dynamic_low_bound (intro H21) H24).
  intros.
  generalize (non_virtual_data_size_own_fields_offset (intro H21)).
  intros.
  generalize (nonempty_non_virtual_data_size_positive (intro H23) H10).
  intros.
  generalize (non_virtual_direct_base_nonempty_data_non_overlap (intro e1) H19 H25 H13 H10 H17 H21 H23).
  intros.
  generalize (non_virtual_direct_base_offsets_low_bound (intro e1) H13).
  omega.
  
 intro H_no_pb.
 generalize (non_virtual_direct_base_offsets_dynamic_type_data_size (intro e1) H1 H_no_pb H10 H13).
 generalize (dynamic_type_data_size_low_bound).
 omega.

Qed.

(** Mentioned in 4.5.4 *)
(* Corollary *) Fact non_virtual_direct_base_non_primary_offset_low_bound : forall cl,
  Is_dynamic cl ->
  forall of (Hof : offsets ! cl = Some of)
    cl', primary_base of <> Some cl' ->
      (Is_empty cl' -> False) ->
      offsets ! cl' <> None ->
      forall o' (Ho' : (non_virtual_direct_base_offsets of) ! cl' = Some o'),
        dynamic_type_data_size PF <= o'.
Proof.
  intros.
  replace (dynamic_type_data_size PF) with (0 + dynamic_type_data_size PF) by omega.
  eapply (@non_primary_path_offset (cl :: cl' :: nil)).
  simpl.
  rewrite Hof.
  destruct (option_eq_dec peq (primary_base of) (Some cl')); congruence.
  eleft.
  reflexivity.
  pattern (cl :: cl' :: nil) at 1.
  replace (cl :: cl' :: nil) with ((cl :: nil) ++ cl' :: nil) by reflexivity.
  reflexivity.
  simpl.
  assert (offsets ! cl <> None) by congruence.
  assert (hierarchy ! cl <> None) by eauto.
  case_eq (hierarchy ! cl); try congruence.
  assert ( (non_virtual_direct_base_offsets of) ! cl' <> None) by congruence.
  intros.
  destruct (In_dec super_eq_dec (Class.Inheritance.Repeated,cl') (Class.super t0)).
   assert (hierarchy ! cl' <> None) by eauto.
   case_eq (hierarchy ! cl'); congruence.
  destruct n.
  eauto using non_virtual_direct_base_offsets_guard.
  assumption.
  assumption.
  assumption.
  simpl.
  rewrite Hof.
  rewrite Ho'.
  reflexivity.
Qed.
  
Fact primary_path_join : forall l1 p l2,
  is_primary_path (l1 ++ p :: nil) = true ->
  is_primary_path (p :: l2) = true ->
  is_primary_path (l1 ++ p :: l2) = true.
Proof.
  induction l1 ; simpl.
  (* case nil *)
  intros; assumption.
  (* case cons *)
  intros until l2.
  destruct l1 ; simpl.
   case_eq (offsets ! a) ; try (intros ; discriminate).
   intros until 1.
   destruct (option_eq_dec peq (primary_base t0) (Some p)) ; try (intros ; discriminate).
   intros; assumption.
  case_eq (offsets ! a) ; try (intros ; discriminate).
  intros until 1.
  destruct (option_eq_dec peq (primary_base t0) (Some i)) ; try (intros ; discriminate).
  generalize (IHl1 p l2).
  simpl.
  intros.
  apply H0.
  assumption.
  assumption.
Qed.
  
Fact primary_path_split_left : forall l1 p l2,
  is_primary_path (l1 ++ p :: l2) = true ->
  is_primary_path (l1 ++ p :: nil) = true.
Proof.
  induction l1 ; simpl.
  (* case nil *)
  intros ; destruct l2;  destruct (offsets ! p) ; congruence.
  (* case cons *)
  intros until l2.
  destruct l1 ; simpl.
   case_eq (offsets ! a) ; try congruence.
   intros until 1.
   destruct (option_eq_dec peq (primary_base t0) (Some p)); congruence.
  destruct (offsets ! a); try congruence.
  destruct (option_eq_dec peq (primary_base t0) (Some i)) ; try congruence.
  generalize (IHl1 p l2).
  simpl.
  tauto.
Qed.

Fact primary_path_split_right : forall l1 p l2,
  is_primary_path (l1 ++ p :: l2) = true ->
  is_primary_path (p :: l2) = true.
Proof.
  induction l1 ; simpl.
  (* case nil *)
  tauto.
  (* case cons *)
  intros until l2.
  destruct l1; simpl.
   destruct (offsets ! a); try congruence.
   destruct (option_eq_dec peq (primary_base t0) (Some p)); congruence.
   generalize (IHl1 p l2).
   simpl.
  destruct (offsets ! a); try congruence.
  destruct (option_eq_dec peq (primary_base t0) (Some i)); try congruence.
  tauto.
Qed.
  
Fact minimal_path_unique : forall l1 p1 q1,
  is_primary_path (p1 :: q1 :: nil) = false ->
  forall l1', is_primary_path (q1 :: l1') = true ->
    forall l2 p2 q2,
  is_primary_path (p2 :: q2 :: nil) = false ->
  forall l2', is_primary_path (q2 :: l2') = true ->
    l1 ++ p1 :: q1 :: l1' = l2 ++ p2 :: q2 :: l2' ->
    (l1, p1, q1, l1') = (l2, p2, q2, l2').
Proof.
  induction l1 ; intros ; simpl in H3.
   destruct l2 ; simpl in H3.
    congruence.
   destruct l2 ; simpl in H3.
    injection H3 ; intros ; subst.
    replace (p2 :: q2 :: l2') with ((p2 :: nil) ++ q2 :: l2') in H0 by reflexivity.
    generalize (primary_path_split_left H0).
    replace ((p2 :: nil) ++ q2 :: nil) with (p2 :: q2 :: nil) by reflexivity.
    congruence.
   injection H3 ; intros ; subst.
   replace (i0 :: l2 ++ p2 :: q2 :: l2') with ((i0 :: l2) ++ p2 :: q2 :: l2') in H0 by reflexivity.
   generalize (primary_path_split_right H0).   
   replace (p2 :: q2 :: l2') with ((p2 :: nil) ++ q2 :: l2') by reflexivity.
   intros.
   generalize (primary_path_split_left H4).
   replace ((p2 :: nil) ++ q2 :: nil) with (p2 :: q2 :: nil) by reflexivity.
   congruence.
  destruct l2 ; simpl in H3.
   destruct l1 ; simpl in H3.
    injection H3 ; intros ; subst.
    replace (q2 :: q1 :: l1') with ((q2 :: nil) ++ q1 :: l1') in H2 by reflexivity.
    generalize (primary_path_split_left H2).
    replace ((q2 :: nil) ++ q1 :: nil) with (q2 :: q1 :: nil) by reflexivity.
    congruence.
   injection H3 ; intros ; subst.
   replace (q2 :: l1 ++ p1 :: q1 :: l1') with ((q2 :: l1) ++ p1 :: q1 :: l1') in H2 by reflexivity.
   generalize (primary_path_split_right H2).
   replace (p1 :: q1 :: l1') with ((p1 :: nil) ++ q1 :: l1') by reflexivity.
   intros.
   generalize (primary_path_split_left H4).
   replace ((p1 :: nil) ++ q1 :: nil) with (p1 :: q1 :: nil) by reflexivity.
   congruence.
  injection H3 ; intros ; subst.
  cut ((l1, p1, q1, l1') = (l2, p2, q2, l2')).
   intros ; congruence.
  eauto.
Qed.

Fact minimal_path_exist : forall l, l <> nil ->
  is_primary_path l = false -> {
    l2 : _ & {
      p2 : _ & {
        q2 : _ & {
          l2' | 
            is_primary_path (p2 :: q2 :: nil) = false /\
            is_primary_path (q2 :: l2') = true /\
            l = l2 ++ p2 :: q2 :: l2'            
        }
      }
    }
  }.
Proof.
 intro l.
 replace l with (rev (rev l)) by apply rev_involutive.
 induction (rev l).
  simpl; congruence.
 intros _.
 destruct l0.
  simpl.
  congruence.
 intro.
 simpl in H.
 rewrite app_ass in H.
 simpl in H.
 assert (rev (i :: l0) <> nil).
  replace (@nil ident) with (rev (@nil ident)) by reflexivity.
  intro.
  assert (rev (rev (i :: l0)) = rev (rev nil)) by congruence.
  rewrite rev_involutive in H1.
  rewrite rev_involutive in H1.
  discriminate.
 case_eq (is_primary_path (i :: a :: nil)).
  intros.
  case_eq (is_primary_path (rev (i :: l0))).
   intro.
   simpl in H2.
   generalize (primary_path_join H2 H1).
   congruence.
  intros.
  generalize (IHl0 H0 H2).
  destruct 1.
  invall.
  exists x.
  exists x0.
  exists x1.
  exists (x2 ++ a :: nil).
  split.
  assumption.
  split.
  replace (x1 :: x2 ++ a :: nil) with ((x1 :: x2) ++ a :: nil) by reflexivity.
  simpl in H6.
  generalize (last_complete (rev l0) i).
  rewrite H6.
  assert (x0 :: x1 :: x2 <> nil) by congruence.
  rewrite (last_app_left H5).
  rewrite last_equation.
  intros.
  generalize (last_correct H7).
  destruct 1.
  rewrite e.
  rewrite app_ass.
  apply primary_path_join.
  congruence.
  assumption.
  simpl.
  simpl in H6.
  rewrite H6.
  rewrite app_ass.
  reflexivity.
 intros.
 exists (rev l0).
 exists i.
 exists a.
 exists nil.
 split.
 assumption.
 split.
 reflexivity.
 simpl.
 rewrite app_ass.
 reflexivity.
Qed.

(* Corollary *) Fact reduce_path_aux : {f | forall l,
  l <> nil ->
  if is_primary_path l
    then exists p, exists q, l = p :: q /\ f l = p :: nil
    else exists l1, exists p, exists q, exists l2, l = l1 ++ p :: q :: l2 /\ is_primary_path (p :: q :: nil) = false /\ is_primary_path (q :: l2) = true /\ f l = l1 ++ p :: q :: nil
}.
Proof.
  cut (forall l,
    {y |
      l <> nil ->
      if is_primary_path l
        then exists p, exists q, l = p :: q /\ y = p :: nil
        else exists l1, exists p, exists q, exists l2, l = l1 ++ p :: q :: l2 /\ is_primary_path (p :: q :: nil) = false /\ is_primary_path (q :: l2) = true /\ y = l1 ++ p :: q :: nil
    }).
   intro H.
   refine (existT _ (fun l => let (y, _) := H l in y) _).
   intros.
   destruct (H l).
   apply y.
   assumption.
  intros.
  destruct l.
   exists nil.
   congruence.
   case_eq (is_primary_path (i :: l)).
    intros.
    repeat esplit.
   intros.
   assert (i :: l <> nil) by congruence.
   generalize (minimal_path_exist H0 H).
   destruct 1.
   invall.
   repeat esplit.   
   eassumption.
   assumption.
   assumption.
Qed.
 
Definition reduce_path := let (f, _) := reduce_path_aux in f.

Lemma reduce_path_prop : forall l,
  l <> nil ->
  if is_primary_path l
    then exists p, exists q, l = p :: q /\ reduce_path l = p :: nil
    else exists l1, exists p, exists q, exists l2, l = l1 ++ p :: q :: l2 /\ is_primary_path (p :: q :: nil) = false /\ is_primary_path (q :: l2) = true /\ reduce_path l = l1 ++ p :: q :: nil
.
Proof.
  unfold reduce_path.
  destruct reduce_path_aux.
  assumption.
Qed.

Opaque reduce_path.

Lemma reduce_path_primary : forall l,
  is_primary_path l = true ->
  exists p, exists q, l = p :: q /\ reduce_path l = p :: nil
.
Proof.
  intro l.
  destruct l.
   simpl; congruence.
  intros.
  assert (i :: l <> nil) by congruence.  
  generalize (reduce_path_prop H0).
  rewrite H.
  tauto.
Qed.

Lemma reduce_path_non_primary : forall l,
  l <> nil ->
  is_primary_path l = false -> 
  exists l1, exists p, exists q, exists l2, l = l1 ++ p :: q :: l2 /\ is_primary_path (p :: q :: nil) = false /\ is_primary_path (q :: l2) = true /\ reduce_path l = l1 ++ p :: q :: nil
.
Proof.
  destruct l.
   congruence.
  intros.
  generalize (reduce_path_prop H).
  rewrite H0.
  tauto.
Qed.

Lemma reduce_path_offset : forall l from to,
  path hierarchy to l from Class.Inheritance.Repeated ->
    forall accu,
      non_virtual_subobject_offset accu l = non_virtual_subobject_offset accu (reduce_path l).
Proof.
  inversion 1 ; subst.
  assert (from :: lf <> nil) by congruence.
  case_eq (is_primary_path (from :: lf)).
   intros.
   generalize (reduce_path_primary H3).
   destruct 1.
   invall.
   injection H4; intros; subst.
   rewrite H6.
   generalize (primary_path_split_left (l1 := nil) H3).
   change (nil ++ x :: nil) with (x :: nil).
   intros.
   repeat rewrite primary_path_offset ; trivial.
  intros.
  generalize (reduce_path_non_primary H0 H3).
  destruct 1.
  invall.
  rewrite H8.
  replace (x ++ x0 :: x1 :: x2) with ((x ++ x0 :: nil) ++ x1 :: x2) in H4 by (rewrite app_ass ; reflexivity).
  replace (x ++ x0 :: x1 :: nil) with ((x ++ x0 :: nil) ++ x1 :: nil) by (rewrite app_ass ; reflexivity).
  rewrite H4.
  rewrite H4 in H2.
  case_eq (non_virtual_subobject_offset accu ((x ++ x0 :: nil) ++ x1 :: nil)).
   intros.
   rewrite (non_virtual_subobject_offset_app H7).
   eauto using primary_path_offset.
  intros.
  case_eq (non_virtual_subobject_offset accu ((x ++ x0 :: nil) ++ x1 :: x2)).
   intros.
   generalize (non_virtual_subobject_offset_app_recip H9).
   destruct 1.
   invall.
   congruence.
  tauto.
Qed.

Lemma reduce_path_valid : forall l,
  is_valid_repeated_subobject hierarchy l = true ->
  is_valid_repeated_subobject hierarchy (reduce_path l) = true.
Proof.
  intros.
  assert (l <> nil) by (functional inversion H; congruence).
  generalize (reduce_path_prop H0).
  case_eq (is_primary_path l).
   destruct 2.
   invall.
   subst.
   rewrite H4.
   functional inversion H ; subst ; try congruence.
   simpl.
   rewrite H6 ; congruence.
  destruct 2.
  invall.
  rewrite H6.
  subst.
  replace (x ++ x0 :: x1 :: nil) with ((x ++ x0 :: nil) ++ x1 :: nil) by (rewrite app_ass ; reflexivity).
  eapply is_valid_repeated_subobject_split_left.
  rewrite app_ass.
  simpl.
  eassumption.
Qed.

Lemma reduce_path_idem : forall l,
  l <> nil ->
  reduce_path (reduce_path l) = reduce_path l.
Proof.
  intros.
  generalize (reduce_path_prop H).
  case_eq (is_primary_path l).
   destruct 2.
   invall.
   subst.
   assert (is_primary_path (x :: nil) = true) by reflexivity.
   rewrite H3.
   generalize (reduce_path_primary H1).
   destruct 1.
   invall.
   rewrite H5.
   congruence.
  destruct 2.
  invall.
  subst.
  rewrite H5.
  assert ((x ++ x0 :: nil) ++ x1 :: nil <> nil).
   rewrite app_ass.
   destruct x; simpl; congruence.  
  assert (is_primary_path ((x ++ x0 :: nil) ++ x1 :: nil) = false).
   rewrite app_ass.   
   case_eq (is_primary_path (x ++ (x0 :: nil) ++ x1 :: nil)) ; try congruence.
   intro.
   generalize (primary_path_split_right H4).
   congruence.
  generalize (reduce_path_non_primary H1 H4).
  rewrite app_ass.
  destruct 1.
  invall.
  simpl in H6.
  rewrite H6.
  assert (is_primary_path (x1 :: nil) = true) by reflexivity.
  generalize (minimal_path_unique H2 H9 H7 H8 H6).
  injection 1; intros; subst.
  simpl in H10.
  assumption.
Qed.

Lemma reduce_path_primary_right : forall l from to,
  path hierarchy to l from Class.Inheritance.Repeated ->
    forall l2, is_primary_path (to :: l2) = true ->
      reduce_path (l ++ l2) = reduce_path l.
Proof.
  inversion 1 ; subst.
  intros.
  case_eq (is_primary_path (lt ++ to :: nil)).
   intros.
   generalize (primary_path_join H3 H0).
   intros.
   generalize (reduce_path_primary H4).
   destruct 1.
   invall.
   generalize (reduce_path_primary H3).
   destruct 1.
   invall.
   replace ((lt ++ to :: nil) ++ l2) with (lt ++ to :: l2) by (rewrite app_ass ; reflexivity).
   rewrite H1.
   rewrite app_ass.
   simpl.
   rewrite H7.
   rewrite H9.
   destruct lt ; simpl in H5, H6 ; congruence.
  intros.
  case_eq (is_primary_path (lt ++ to :: l2)).
   intros.
   generalize (primary_path_split_left H4).
   congruence.
  intros.
  assert (lt ++ to :: nil <> nil) by (destruct lt; simpl in *; congruence).
  assert (lt ++ to :: l2 <> nil) by (destruct lt; simpl in *; congruence).
  rewrite H1.
  rewrite app_ass.
  simpl.
  generalize (reduce_path_non_primary H6 H4).
  destruct 1.
  invall.
  generalize (reduce_path_non_primary H5 H3).
  destruct 1.
  invall.  
  assert (x5 :: x6 <> nil) by congruence.
  assert (last (x5 :: x6) = Some to).
   rewrite <- (last_app_left H14 (x3 ++ x4 :: nil)).
   rewrite app_ass.
   simpl.
   rewrite <- H10.   
   apply last_complete.
  generalize (last_correct H16).
  destruct 1.
  assert (x ++ x0 :: x1 :: x2 = x3 ++ x4 :: x5 :: (x6 ++ l2)).
   change (x3 ++ x4 :: x5 :: x6 ++ l2) with (x3 ++ (x4 :: x5 :: x6) ++ l2).
   rewrite <- app_ass.
   rewrite <- H10.
   rewrite <- H7.
   rewrite app_ass.
   reflexivity.
  rewrite H11.
  rewrite H15.
  assert (is_primary_path (x5 :: x6 ++ l2) = true).
   change (x5 :: x6 ++ l2) with ((x5 :: x6) ++ l2) .
   rewrite e in *.
   rewrite app_ass.
   simpl.
   eauto using primary_path_join.
  generalize (minimal_path_unique H8 H9 H12 H18 H17).
  congruence.
Qed.
 
Lemma reduce_path_prefix_repeated : forall l from to,
  path hierarchy to l from Class.Inheritance.Repeated ->
    exists through, exists l',
      path hierarchy through (reduce_path l) from Class.Inheritance.Repeated /\
        path hierarchy to (through :: l') through Class.Inheritance.Repeated /\
          l = reduce_path l ++ l' /\
          is_primary_path (through :: l') = true.
Proof.
  inversion 1 ; subst.
  case_eq (is_primary_path (from :: lf)).
   intros.
   exists from.
   exists lf.
   generalize (reduce_path_primary H0).
   destruct 1.
   invall.
   injection H3 ; intros ; subst.
   rewrite H5.
   split.
   eleft with nil nil ; try trivial.
    functional inversion H2 ; subst ; try trivial.
    simpl.
    rewrite H8 ; trivial.
   eauto.
  intros.
  assert (from :: lf <> nil) by congruence.
  generalize (reduce_path_non_primary H3 H0).
  destruct 1.
  invall.
  rewrite H8.
  exists x1.
  exists x2.
  assert (exists ll, x ++ x0 :: x1 :: nil = from :: ll).   
   destruct x ; simpl in H4 ; simpl.
    injection H4 ; intros ; subst ; simpl.
    esplit.
    reflexivity.
   injection H4 ; intros ; subst ; simpl.
   esplit.
   reflexivity.
  destruct H7.
  assert (x ++ x0 :: x1 :: nil = (x ++ x0 :: nil) ++ x1 :: nil) by (rewrite app_ass ; reflexivity).
  generalize H2.
  rewrite H4.
  intros.
  split.
   eleft.
   eassumption.
   eassumption.
   rewrite H9.
   eapply is_valid_repeated_subobject_split_left.
   rewrite app_ass.
   simpl.
   eassumption.
  assert (x1 :: x2 <> nil) by congruence.
  assert (last (x1 :: x2) = Some to).
   rewrite <- (last_app_left H11 (x ++ x0 :: nil)).
   rewrite app_ass.
   simpl.
   rewrite <- H4.
   rewrite H1.
   apply last_complete.
  generalize (last_correct H12).
  destruct 1.
  split.
   eleft.
   reflexivity.
   eassumption.
   eapply is_valid_repeated_subobject_split_right with (x ++ x0 :: nil).
   rewrite app_ass.
   assumption.
  rewrite app_ass.
  eauto.
Qed.
   
(* Corollary *) Lemma reduce_path_prefix : forall l from to h,
  path hierarchy to l from h ->
    exists through, exists l',
      path hierarchy through (reduce_path l) from h /\
        path hierarchy to (through :: l') through Class.Inheritance.Repeated /\
          l = reduce_path l ++ l' /\
          is_primary_path (through :: l') = true.
Proof.
 destruct h.
  eauto using reduce_path_prefix_repeated.
 intros.
 generalize (path_path0 H).
 inversion 1 ; subst.
 assert (path hierarchy to (base :: lf) base Class.Inheritance.Repeated) by (eleft ; eauto).
 generalize (reduce_path_prefix_repeated H2).
 destruct 1.
 invall.
 exists x.
 exists x0.
 split.
 eright.
 eassumption.
 eassumption.
 eauto.
Qed.  

Fact primary_path_dynamic : forall l a,
 LibLists.last l = Some a ->
 is_primary_path l = true ->
 Is_dynamic a ->
 forall b, In b l ->
 Is_dynamic b.
Proof.
 induction l ; simpl ; try congruence.
 destruct l.
  simpl ; inversion 4 ; try congruence ; contradiction.
 case_eq (offsets ! a); try congruence.
 intros until 2.
 destruct (option_eq_dec peq (primary_base t0) (Some i)); try congruence.
 inversion 3; subst.
  assert (primary_base t0 <> None) by congruence.
  eauto using primary_base_exist_dynamic.
 eauto.
Qed.

Fact reduce_path_dynamic_type_disjoint_non_primary : forall l1 from to1,
  path hierarchy to1 l1 from Class.Inheritance.Repeated ->
    is_primary_path l1 = false ->
    Is_dynamic to1 ->    
    forall (to1_offsets : offsets ! to1 <> None) accu z1,
      non_virtual_subobject_offset accu l1 = Some z1 ->
      forall l2 to2,
        path hierarchy to2 l2 from Class.Inheritance.Repeated ->
          is_primary_path l2 = false ->
          Is_dynamic to2 ->
          forall (to2_offsets : offsets ! to2 <> None) z2,
            non_virtual_subobject_offset accu l2 = Some z2 ->
            reduce_path l1 <> reduce_path l2 ->
            z1 + dynamic_type_data_size PF <= z2 \/ z2 + dynamic_type_data_size PF <= z1
.
Proof.
 inversion 1 ; subst.
 intro.
 intro.
 intro.
 intro.
 rewrite (reduce_path_offset H).
 assert (from :: lf <> nil) by congruence.
 generalize (reduce_path_non_primary H4 H0).
 destruct 1.
 invall.
 rewrite H9.
 assert (Is_dynamic x1).
  eapply primary_path_dynamic.
  2 : eassumption.
  2 : eassumption.
  assert (x1 :: x2 <> nil) by congruence.
  rewrite <- (last_app_left H8 (x ++ x0 :: nil)).
  rewrite app_ass.
  simpl.
  rewrite <- H5.
  rewrite H1.
  apply last_complete.
  auto.
 assert (is_valid_repeated_subobject hierarchy (x ++ x0 :: x1 :: nil) = true).
  replace (x ++ x0 :: x1 :: nil) with ((x ++ x0 :: nil) ++ x1 :: nil) by (rewrite app_ass ; reflexivity).
  eapply is_valid_repeated_subobject_split_left with x2.
  rewrite app_ass.
  simpl.
  congruence. 
 assert (exists y1, x ++ x0 :: nil = from :: y1).
  symmetry in H5 ; destruct x ; simpl in H5 ; injection H5 ; intros ; subst ;  simpl ; repeat esplit.
 destruct H11 as [y1 Hy1].
 assert (x1_offsets : offsets ! x1 <> None).
  functional inversion H7; subst; try congruence.
  generalize (last_complete lt to1).
  rewrite <- H1.
  rewrite H5.
  replace (x ++ x0 :: x1 :: nil) with ((x ++ x0 :: nil) ++ x1 :: nil).
  rewrite last_complete.
  congruence.
  rewrite app_ass.
  reflexivity.
 clear to1 to1_offsets lf lt H H1 H2 H0 H3 H4 x2 H5 H7 H9.
 inversion 2 ; subst.
 intro.
 intro.
 intro.
 intro.
 rewrite (reduce_path_offset H0).
 assert (from :: lf <> nil) by congruence.
 generalize (reduce_path_non_primary H5 H1).
 destruct 1.
 invall.
 rewrite H13.
 assert (Is_dynamic x4).
  eapply primary_path_dynamic.
  2 : eassumption.
  2 : eassumption.
  assert (x4 :: x5 <> nil) by congruence.
  rewrite <- (last_app_left H12 (x2 ++ x3 :: nil)).
  rewrite app_ass.
  simpl.
  rewrite <- H7.
  rewrite H2.
  apply last_complete.
  auto.
 assert (is_valid_repeated_subobject hierarchy (x2 ++ x3 :: x4 :: nil) = true).
  replace (x2 ++ x3 :: x4 :: nil) with ((x2 ++ x3 :: nil) ++ x4 :: nil) by (rewrite app_ass ; reflexivity).
  eapply is_valid_repeated_subobject_split_left with x5.
  rewrite app_ass.
  simpl.
  congruence.
 assert (exists y2, x2 ++ x3 :: nil = from :: y2).
  symmetry in H7 ; destruct x2 ; simpl in H7 ; injection H7 ; intros ; subst ;  simpl ; repeat esplit.
 destruct H15. 
 assert (x4_offsets : offsets ! x4 <> None).
  functional inversion H11; subst; try congruence.
  generalize (last_complete lt to2).
  rewrite <- H2.
  rewrite H7.
  replace (x2 ++ x3 :: x4 :: nil) with ((x2 ++ x3 :: nil) ++ x4 :: nil).
  rewrite last_complete.
  congruence.
  rewrite app_ass.
  reflexivity.
 clear to2 to2_offsets lf lt H0 H2 H3 H1 H4 H5 x5 H7 H11 H13.
 intros.
 assert (y1 ++ x1 :: nil <> x6 ++ x4 :: nil).
  revert H1.
  replace (x ++ x0 :: x1 :: nil) with ((x ++ x0 :: nil) ++ x1 :: nil) by (rewrite app_ass ; reflexivity).
  replace (x2 ++ x3 :: x4 :: nil) with ((x2 ++ x3 :: nil) ++ x4 :: nil) by (rewrite app_ass ; reflexivity).
  rewrite Hy1.
  rewrite H15.
  simpl.
  congruence.
 clear H1.
 revert x accu x0 x1 x1_offsets H6 H8 H10 y1 Hy1 z1 H z2 x2 x3 x4 x4_offsets H9 H12 H14 x6 H15 H0 H2.
 cut (
 forall (x : list ident) accu (x0 x1 : ident) (x1_offsets : offsets ! x1 <> None),
   is_primary_path (x0 :: x1 :: nil) = false ->
   Is_dynamic x1 ->
   is_valid_repeated_subobject hierarchy (x ++ x0 :: x1 :: nil) = true ->
   forall y1 : list ident,
   x ++ x0 :: nil = from :: y1 ->
   forall z1 : Z,
   non_virtual_subobject_offset accu (x ++ x0 :: x1 :: nil) = Some z1 ->
   forall (z2 : Z) (x2 : list ident) (x3 x4 : ident) (x4_offsets : offsets ! x4 <> None),
   is_primary_path (x3 :: x4 :: nil) = false ->
   Is_dynamic x4 ->
   is_valid_repeated_subobject hierarchy (x2 ++ x3 :: x4 :: nil) = true ->
   forall x6 : list ident,
   x2 ++ x3 :: nil = from :: x6 ->
   non_virtual_subobject_offset accu (x2 ++ x3 :: x4 :: nil) = Some z2 ->
   y1 ++ x1 :: nil <> x6 ++ x4 :: nil ->
   (length (y1 ++ x1 :: nil) <= length (x6 ++ x4 :: nil))%nat ->
   z1 + dynamic_type_data_size PF <= z2 \/ z2 + dynamic_type_data_size PF <= z1
 ).
  intros.
  assert (forall A B, A \/ B -> B \/ A) by tauto.
  destruct (le_lt_dec (length (y1 ++ x1 :: nil)) (length (x6 ++ x4 :: nil))).
   eauto.
  assert ((length (x6 ++ x4 :: nil) <= length (y1 ++ x1 :: nil))%nat) by omega.
  eauto.
 intros.
 generalize (distinct_paths_cases peq H10 H9).
 destruct 1.
 
  (* "l'un herite de l'autre". *)
  invall.
  generalize H8 H6.
  replace (x2 ++ x3 :: x4 :: nil) with ((x2 ++ x3 :: nil) ++ x4 :: nil) by (rewrite app_ass ; reflexivity).
  rewrite H7.
  replace ((from :: x6) ++ x4 :: nil) with (from :: (x6 ++ x4 :: nil)) by reflexivity.
  rewrite H12. 
  intros.
  assert (
     non_virtual_subobject_offset accu ((from :: y1) ++ (x1 :: x5 :: x7)) =
   Some z2 /\ is_valid_repeated_subobject hierarchy ((from :: y1) ++ (x1 :: x5 :: x7)) = true
  ).  
   rewrite app_ass in H11, H13.
   split; assumption.
  clear H11 H13.
  revert H14.
  rewrite <- H2.
  generalize H3.
  replace (x ++ x0 :: x1 :: nil) with ((x ++ x0 :: nil) ++ x1 :: nil) by (rewrite app_ass ; reflexivity).
  intro.
  rewrite (non_virtual_subobject_offset_app H11).
  destruct 1.
  left.
  generalize (last_complete x6 x4).
  rewrite H12.
  rewrite app_ass.
  simpl.
  assert (x1 :: x5 :: x7 <> nil) by congruence.
  rewrite (last_app_left H15).
  intros.
  generalize (last_correct H16).
  destruct 1.
  cut (is_primary_path (x1 :: x5 :: x7) = false).
   intros.
   eapply non_primary_path_offset.
   eassumption.
   eleft.
    reflexivity.
    eassumption.
    eauto using is_valid_repeated_subobject_split_right.
   assumption.
   eauto using dynamic_nonempty.
   assumption.
   assumption.
  assert (last x8 = Some x3).
   destruct x8.
    simpl in e ; discriminate.
   simpl in e.
   injection e ; intros ; subst.
   assert (i :: x8 <> nil) by congruence.
   rewrite H17 in H12.
   rewrite <- app_ass in H12.
   generalize (app_reg_r H12).
   rewrite app_ass.
   intros.
   simpl in H19.
   subst.
   rewrite <- (last_app_left H18 (from :: y1)).
   replace ((from :: y1) ++ i :: x8) with (from :: y1 ++ i :: x8) by reflexivity.
   rewrite <- H7.
   apply last_complete.
  generalize (last_correct H17).
  destruct 1.
  subst.  
  rewrite e.
  rewrite app_ass.
  simpl.
  case_eq (is_primary_path (x9 ++ x3 :: x4 :: nil)) ; try congruence.
  intros.
  generalize (primary_path_split_right H18).
  congruence.

 (* "classes divergentes". *)
 invall.
 revert H1 H3.
 replace (x ++ x0 :: x1 :: nil) with ((x ++ x0 :: nil) ++ x1 :: nil) by (rewrite app_ass ; reflexivity).
 rewrite H2.
 replace ((from :: y1) ++ x1 :: nil) with (from :: (y1 ++ x1 :: nil)) by reflexivity.
 rewrite H12.
 replace (from :: x5 ++ x7 :: x9) with ((from :: x5) ++ x7 :: x9) by reflexivity.
 assert (from :: x5 <> nil) by congruence.
 generalize (last_nonempty H1).
 intro.
 case_eq (last (from :: x5)) ; try congruence.
 intros until 1.
 generalize (last_correct H13).
 destruct 1.
 rewrite e.
 rewrite app_ass.
 simpl.
 intros.
 generalize (non_virtual_subobject_offset_app_recip H16).
 destruct 1.
 destruct H17.
 functional inversion H18 ; subst.
 generalize (is_valid_repeated_subobject_split_right H15).
 functional inversion 1 ; subst.
 revert H6 H8.
 replace (x2 ++ x3 :: x4 :: nil) with ((x2 ++ x3 :: nil) ++ x4 :: nil) by (rewrite app_ass ; reflexivity).
 rewrite H7.
 replace ((from :: x6) ++ x4 :: nil) with (from :: x6 ++ x4 :: nil) by reflexivity.
 rewrite H11.
 replace (from :: x5 ++ x8 :: x10) with ((from :: x5) ++ x8 :: x10) by reflexivity.
 rewrite e.
 rewrite app_ass.
 simpl.
 intros.
 generalize (non_virtual_subobject_offset_app_recip H8).
 destruct 1.
 destruct H20.
 replace x13 with x12 in * by congruence.
 functional inversion H21 ; subst.
 replace o0 with o in * by congruence.
 generalize (is_valid_repeated_subobject_split_right H6).
 functional inversion 1 ; subst.
 clear H36 H29.
 replace cl1 with cl0 in * by congruence.
 assert (x7 :: x9 <> nil) by congruence.
 generalize (last_complete y1 x1).
 rewrite H12.
 rewrite (last_app_left H23).
 intros.
 assert (offsets ! x7 <> None).
  functional inversion X; subst; try congruence.
  generalize (last_complete y1 x1).
  rewrite H12.
  rewrite last_complete.
  congruence.
 case_eq (offsets ! x7) ; try congruence.
 intros.
 assert (x8 :: x10 <> nil) by congruence.
 generalize (last_complete x6 x4).
 rewrite H11.
 rewrite (last_app_left H30).
 intros.
 assert (offsets ! x8 <> None).
  functional inversion X1; subst; try congruence.
  generalize (last_complete x6 x4).
  rewrite H11.
  rewrite last_complete.
  congruence.
 case_eq (offsets ! x8) ; try congruence.
 intros.
 generalize (last_correct H32).
 destruct 1.
 assert (path hierarchy x4 (x8 :: x10) x8 Class.Inheritance.Repeated).
  eleft.
  reflexivity.
  eassumption.
  assumption.
 generalize (last_correct H25).
 destruct 1.
 assert (path hierarchy x1 (x7 :: x9) x7 Class.Inheritance.Repeated).
  eleft.
  reflexivity.
  eassumption.
  assumption.
 generalize (dynamic_type_data_size_low_bound PF).
 generalize (non_virtual_path_non_virtual_data_incl H38 (dynamic_nonempty H0) X).
 destruct 1.
 case_eq (offsets ! x1); try congruence.
 intros.
 generalize (H40 _ H41 _ H29).
 generalize (non_virtual_path_non_virtual_data_incl H37 (dynamic_nonempty H5) X1).
 destruct 1.
 case_eq (offsets ! x4); try congruence.
 intros.
 generalize (H44 _ H45 _ H36).
 generalize (own_fields_offset_dynamic_low_bound (intro H41) H0).
 generalize (non_virtual_data_size_own_fields_offset (intro H41)).
 generalize (own_fields_offset_dynamic_low_bound (intro H45) H5).
 generalize (non_virtual_data_size_own_fields_offset (intro H45)).
 assert (Is_empty x7 -> False) by eauto using Is_empty.path_from, dynamic_nonempty.
 assert (Is_empty x8 -> False) by eauto using Is_empty.path_from, dynamic_nonempty.
 generalize (non_virtual_direct_base_nonempty_data_non_overlap
 (intro H26) H27 H47 H34 H48 H14 H29 H36). 
 omega.
Qed.

(* Corollary *) Fact reduce_path_dynamic_type_disjoint_non_virtual_paths : forall l1 from to1,
  path hierarchy to1 l1 from Class.Inheritance.Repeated ->
    forall accu z1,
      non_virtual_subobject_offset accu l1 = Some z1 ->
      forall l2 to2,
        path hierarchy to2 l2 from Class.Inheritance.Repeated ->
          forall z2,
            non_virtual_subobject_offset accu l2 = Some z2 ->
            Is_dynamic to1 ->
            Is_dynamic to2 ->
            offsets ! to1 <> None ->
            offsets ! to2 <> None ->
            reduce_path l1 <> reduce_path l2 ->
            z1 + dynamic_type_data_size PF <= z2 \/ z2 + dynamic_type_data_size PF <= z1
.
Proof.
  cut (
  forall (l1 l2 : list ident) (from to1 : ident),
   path hierarchy to1 l1 from Class.Inheritance.Repeated ->
   forall accu z1 : Z,
   non_virtual_subobject_offset accu l1 = Some z1 ->
   forall (to2 : ident),
   path hierarchy to2 l2 from Class.Inheritance.Repeated ->
   forall z2 : Z,
   non_virtual_subobject_offset accu l2 = Some z2 ->
   Is_dynamic to1 ->
   Is_dynamic to2 ->
   offsets ! to1 <> None ->
   offsets ! to2 <> None ->
   reduce_path l1 <> reduce_path l2 ->
   (if is_primary_path l1 then is_primary_path l2 = true else True) ->
   z1 + dynamic_type_data_size PF <= z2 \/ z2 + dynamic_type_data_size PF <= z1
  ).
  intros.
  assert (reduce_path l2 <> reduce_path l1) by congruence.
  assert (forall A B, A \/ B -> B \/ A) by tauto.
   generalize (H l1 l2).
   generalize (H l2 l1).
   destruct (is_primary_path l1) ; destruct (is_primary_path l2) ; eauto.
  inversion 1 ; subst.
  inversion 2 ; subst.
  case_eq (is_primary_path (from :: lf)) ; intros.
   generalize (reduce_path_primary H13).
   destruct 1.
   invall.
   generalize (reduce_path_primary H4).
   destruct 1.
   invall.
   congruence.
  case_eq (is_primary_path (from :: lf0)).
   intros.
   generalize (primary_path_offset H14 accu).
   intros.
   replace z2 with accu in * by congruence.
   assert (Is_dynamic from). 
    eapply primary_path_dynamic.
    2 : eassumption.
    rewrite H5.
    eapply last_complete.
    assumption.
    auto.
   assert (Is_empty to1 -> False) by eauto using dynamic_nonempty.
   generalize (non_primary_path_offset H4 H H16 H17 H10 H0).
   omega.
  (* "les deux non primaires". *)
  intros.
  eauto using reduce_path_dynamic_type_disjoint_non_primary.
Qed.

(* Corollary *) Fact reduce_path_dynamic_type_disjoint_paths : forall l1 from to1 h1,
  path hierarchy to1 l1 from h1 ->
    forall z1,
      subobject_offset from l1 = Some z1 ->
      forall l2 to2 h2,
        path hierarchy to2 l2 from h2 ->
          forall z2,
            subobject_offset from l2 = Some z2 ->
            Is_dynamic to1 ->
            Is_dynamic to2 ->
            offsets ! to1 <> None ->
            offsets ! to2 <> None ->
            reduce_path l1 <> reduce_path l2 ->
            z1 + dynamic_type_data_size PF <= z2 \/ z2 + dynamic_type_data_size PF <= z1
.
Proof.
  functional inversion 2; subst.
  functional inversion 2; subst.
  generalize (path_cons_repeated H).
  intros.
  generalize (path_cons_repeated H3).
  intros.
  destruct (peq b b0).
   subst.
   replace of0 with of in * by congruence.
   eauto using reduce_path_dynamic_type_disjoint_non_virtual_paths.
  assert (offsets ! b <> None).
   functional inversion H1; subst; try congruence.
   generalize (path_last H); simpl; congruence.
  case_eq (offsets ! b); try congruence.
  intros.
  assert (offsets ! b0 <> None).
   functional inversion H6; subst; try congruence.
   generalize (path_last H3); simpl; congruence.
  case_eq (offsets ! b0); try congruence.
  intros.
  case_eq (offsets ! to1); try congruence.
  intros.
  case_eq (offsets ! to2); try congruence.
  intros.
  assert (Is_empty to1 -> False) by eauto using dynamic_nonempty.
  assert (Is_empty to2 -> False) by eauto using dynamic_nonempty.
  assert (Is_empty b -> False) by eauto using Is_empty.path_from. 
  assert (Is_empty b0 -> False) by eauto using Is_empty.path_from.
  generalize (non_virtual_path_non_virtual_data_incl H8 H22 H1).
  destruct 1.
  generalize (H27 _ H20 _ H17).
  generalize (non_virtual_path_non_virtual_data_incl H15 H23 H6).
  destruct 1.
  generalize (H29 _ H21 _ H19).
  generalize (own_fields_offset_dynamic_low_bound (intro H20) H9).
  generalize (non_virtual_data_size_own_fields_offset (intro H20)).
  generalize (own_fields_offset_dynamic_low_bound (intro H21) H11).
  generalize (non_virtual_data_size_own_fields_offset (intro H21)).
  generalize (dynamic_type_data_size_low_bound).
  replace o0 with o in * by congruence.
  generalize (virtual_base_offsets_nonempty_non_overlap (intro H2) H5 H17 H10 H19 H24 H25 n).
  omega.
Qed.

(** 5.4 Theorem 6 *)
Theorem reduce_path_dynamic_type_disjoint : forall afrom zfrom a1 ato1 i1 h1 p1 pto1,
   valid_relative_pointer hierarchy afrom zfrom a1 ato1 i1 h1 p1 pto1 ->
   forall a2 ato2 i2 h2 p2 pto2,
     valid_relative_pointer hierarchy afrom zfrom a2 ato2 i2 h2 p2 pto2 ->
     (a1, i1) <> (a2, i2) \/ reduce_path p1 <> reduce_path p2 ->
     offsets ! pto1 <> None ->
     offsets ! pto2 <> None ->
     Is_dynamic pto1 ->
     Is_dynamic pto2 ->
     forall of1, relative_pointer_offset afrom ato1 a1 i1 p1 = Some of1 ->
       forall of2, relative_pointer_offset afrom ato2 a2 i2 p2 = Some of2 ->
         of1 + dynamic_type_data_size PF <= of2 \/ of2 + dynamic_type_data_size PF <= of1
.
Proof.
  intros until 2.
  destruct (array_path_eq_dec a1 a2).
   subst.
   destruct (Z_eq_dec i1 i2).
    subst.
    inversion 1; try congruence.
    functional inversion 5; subst.
    inversion H; subst.
    inversion H0; subst.
    generalize (valid_array_path_last H8 H15).
    intro; subst.
    unfold relative_pointer_offset.
    rewrite H9.
    rewrite H10.
    case_eq (subobject_offset ato2 p2); try congruence.
    injection 2; intros; subst.
    generalize (reduce_path_dynamic_type_disjoint_paths H14 H11 H18 H19 H5 H6 H3 H4 H2).
    omega.
   intros.
   inversion H; subst.
   inversion H0; subst.
   generalize (valid_array_path_last H8 H12).
   intro; subst.
   functional inversion H6; subst.
   functional inversion H7; subst.
   replace ofto0 with ofto in * by congruence.
   case_eq (offsets ! pto1); try congruence.
   intros.
   case_eq (offsets ! pto2); try congruence.
   intros.
   assert (Is_empty pto1 -> False) by eauto using dynamic_nonempty.
   assert (Is_empty pto2 -> False) by eauto using dynamic_nonempty.
   generalize (path_data_incl H11 H24 H19).
   destruct 1.
   generalize (H27 _ H16 _ H18).
   generalize (path_data_incl H15 H25 H22).
   destruct 1.
   generalize (H29 _ H23 _ H21).
   generalize (data_size_high_bound (intro H18)).
   generalize (size_positive H18).
   intro.
   replace z1 with z0 in * by congruence.
   generalize dynamic_type_data_size_low_bound.
   generalize (array_cells_disjoint n H30).
   generalize (own_fields_offset_dynamic_low_bound (intro H16) H4).
   generalize (own_fields_offset_dynamic_low_bound (intro H23) H5).
   generalize (non_virtual_data_size_own_fields_offset (intro H16)).
   generalize (non_virtual_data_size_own_fields_offset (intro H23)).
   omega.
  intros _.
  revert a1 a2 n afrom zfrom ato1 i1 h1 p1 pto1 H ato2 i2 h2 p2 pto2 H0.
  cut (
      forall a1 a2 (n : a1 <> a2) (len : (length a1 <= length a2)%nat) (afrom : ident) (zfrom : Z) (ato1 : ident) 
     (i1 : Z) (h1 : Class.Inheritance.t) (p1 : list ident) 
     (pto1 : ident),
   valid_relative_pointer hierarchy afrom zfrom a1 ato1 i1 h1 p1 pto1 ->
   forall (ato2 : ident) (i2 : Z) (h2 : Class.Inheritance.t)
     (p2 : list ident) (pto2 : ident),
   valid_relative_pointer hierarchy afrom zfrom a2 ato2 i2 h2 p2 pto2 ->
   offsets ! pto1 <> None ->
   offsets ! pto2 <> None ->
   Is_dynamic pto1 ->
   Is_dynamic pto2 ->
   forall of1 : Z,
   relative_pointer_offset afrom ato1 a1 i1 p1 = Some of1 ->
   forall of2 : Z,
   relative_pointer_offset afrom ato2 a2 i2 p2 = Some of2 ->
   of1 + dynamic_type_data_size PF <= of2 \/ of2 + dynamic_type_data_size PF <= of1
   
  ).
   intros.
   destruct (le_lt_dec (length a1) (length a2)).
    eauto.
   assert (length a2 <= length a1)%nat by omega.
   assert (a2 <> a1) by congruence.
   assert (forall A B : Prop, A \/ B -> B \/ A)  by tauto.
   eauto.
  induction a1; destruct a2; intros n len; try congruence; simpl in len; try omegaContradiction.

  inversion 1; subst.
  inversion H0; subst.
  inversion 1; subst.
  inversion H7; subst.
  functional inversion 5; subst.
  functional inversion H24; subst.
  functional inversion 1; subst.
  functional inversion H28; subst.
  replace ofto with o in * by congruence.
  rewrite (path_last H15) in H41.
  injection H41; intros; subst.
  case_eq (offsets ! pto1) ; try congruence.
  intros.
  case_eq (offsets ! pto2) ; try congruence.
  intros.
  assert (Is_empty pto1 -> False) by eauto using dynamic_nonempty.
  assert (Is_empty pto2 -> False) by eauto using dynamic_nonempty.
  generalize (path_data_incl H3 H32 H26).
  destruct 1.
  generalize (H35 _ H27 _ H36).
  generalize (data_size_high_bound (intro H36)).
  generalize (size_positive H36).
  intros.
  generalize (dynamic_type_data_size_low_bound).
  intros.
  generalize (own_fields_offset_dynamic_low_bound (intro H31) H19).
  generalize (non_virtual_data_size_own_fields_offset (intro H31)).
  assert (valid_relative_pointer hierarchy by (Zpos by_n) a2 ato2 i2 h2 p2 pto2) by (econstructor; eauto).
  replace ci'0 with by in * by congruence.
  replace _x0 with by_n in * by congruence.
  assert (relative_pointer_offset by ato2 a2 i2 p2 = Some (z1 - (p0 * size o + off + fo) + i2 * size ofto0 + z0)).
   unfold relative_pointer_offset.
   rewrite (array_path_offset_rewrite X).
   rewrite H29.
   rewrite H30.
   f_equal.
   omega.
  generalize (relative_pointer_data_incl H46 H33 H47).
  destruct 1.
  assert (offsets ! by <> None).
   functional inversion X; subst; try congruence.
   inversion H23; congruence.
  case_eq (offsets ! by); try congruence.
  intros.
  generalize (H49 _ H51 _ H31).
  intros.
  assert (forall ty n, FieldSignature.type fs = FieldSignature.Struct ty n -> Is_empty ty -> False).
   rewrite H43.
   injection 1; intros until 2; subst.
   eauto using Is_empty.relative_pointer_from.
  generalize (field_offsets_nonempty_low_bound (intro H42) H44 H55).
  intros.
  generalize (non_virtual_data_size_field_offsets (intro H42) H44 H55).
  unfold field_data_size.
  rewrite H43.
  rewrite H51.
  intros.
  generalize (H57 _ (refl_equal _)).
  intros.
  assert (Is_empty clast -> False).
   intro.
   apply H33.
   eapply Is_empty.relative_pointer_to.
   eassumption.
   eassumption.   
   eapply Is_empty.fields_struct_empty.
   eassumption.
   eassumption.
   eassumption.
   eassumption.
   eassumption.  
  destruct (Z_eq_dec p0 i1).
   subst.
   generalize (paths_disjoint_field_dynamic_type H15 H59 H39 H42 H18 H3 H26 H11).
   omega.
  generalize (array_cells_disjoint n0 H37).
  intros.
  generalize (path_data_incl H15 H59 H39).
  destruct 1.
  generalize (H62 _ H42 _ H25).
  generalize (own_fields_offset_dynamic_low_bound (intro H27) H18).
  intros.
  generalize (non_virtual_data_size_own_fields_offset (intro H27)).
  generalize (H35 _ H27 _ H25).
  generalize (field_offsets_low_bound (intro H42) H44).
  omega.

 inversion 1; subst.
 inversion H0; subst.
 inversion 1; subst.
 inversion H5; subst.
 functional inversion 5; subst.
 functional inversion H29; subst.
 functional inversion 1; subst.
 functional inversion H33; subst.
 rewrite (path_last H8) in H42.
 injection H42; intros; subst.
 rewrite (path_last H20) in H52.
 injection H52; intros; subst.
 replace o0 with o in * by congruence.
 replace ci'0 with by in * by congruence.
 replace _x0 with by_n in * by congruence.
 replace ci'1 with by0 in * by congruence.
 replace _x1 with by_n0 in * by congruence.
 assert (valid_relative_pointer hierarchy by (Zpos by_n) a1 ato1 i1 h1 p1 pto1) by (econstructor; eauto).
 assert (valid_relative_pointer hierarchy by0 (Zpos by_n0) a2 ato2 i2 h2 p2 pto2) by (econstructor; eauto).
 assert (relative_pointer_offset by ato1 a1 i1 p1 = Some (z1 - (p0 * size o + off + fo) + i1 * size ofto + z2)).
  unfold relative_pointer_offset.
  rewrite (array_path_offset_rewrite X).
  rewrite H30.
  rewrite H31.
  f_equal.
  omega.
 assert (relative_pointer_offset by0 ato2 a2 i2 p2 = Some (z0 - (p3 * size o + off0 + fo0) + i2 * size ofto0 + z3)).
  unfold relative_pointer_offset.
  rewrite (array_path_offset_rewrite X0).
  rewrite H34.
  rewrite H35.
  f_equal.
  omega.
 generalize dynamic_type_data_size_low_bound.
 case_eq (offsets ! pto1); try congruence.
 intros until 1.
 generalize (own_fields_offset_dynamic_low_bound (intro H41) H23).
 generalize (non_virtual_data_size_own_fields_offset (intro H41)).
 assert (Is_empty pto1 -> False) by eauto using dynamic_nonempty.
 assert (offsets ! by <> None).
  functional inversion X; subst; try congruence.
  inversion H16; congruence.
 case_eq (offsets ! by); try congruence.
 intros until 1.
 generalize (relative_pointer_data_incl H32 H46 H38).
 destruct 1.
 generalize (H56 _ H49 _ H41).
 assert (Is_empty by -> False).
  eapply Is_empty.relative_pointer_from.
  eassumption.
  eassumption.
  assumption.
 assert (forall ty n, FieldSignature.type fs = FieldSignature.Struct ty n -> Is_empty ty -> False) by congruence. 
 generalize (field_offsets_nonempty_low_bound (intro H43) H45 H58).
 generalize (non_virtual_data_size_field_offsets (intro H43) H45 H58).
 unfold field_data_size.
 rewrite H15.
 rewrite H49.
 intro.
 generalize (H59 _ (refl_equal _)).
 case_eq (offsets ! pto2); try congruence.
 intros until 1.
 generalize (own_fields_offset_dynamic_low_bound (intro H60) H24).
 generalize (non_virtual_data_size_own_fields_offset (intro H60)).
 assert (Is_empty pto2 -> False) by eauto using dynamic_nonempty.
 assert (offsets ! by0 <> None).
  functional inversion X0; subst; try congruence.
  inversion H28; congruence.
 case_eq (offsets ! by0); try congruence.
 intros until 1.
 generalize (relative_pointer_data_incl H36 H61 H39).
 destruct 1.
 generalize (H65 _ H63 _ H60).
 assert (Is_empty by0 -> False).
  eapply Is_empty.relative_pointer_from.
  eassumption.
  eassumption.
  assumption.
 assert (forall ty n, FieldSignature.type fs0 = FieldSignature.Struct ty n -> Is_empty ty -> False) by congruence. 
 generalize (field_offsets_nonempty_low_bound (intro H53) H55 H67).
 generalize (non_virtual_data_size_field_offsets (intro H53) H55 H67).
  unfold field_data_size.
  rewrite H27.
  rewrite H63.
  intro.
  generalize (H68 _ (refl_equal _)).
  assert (clast_nonempty: Is_empty clast -> False).
   intro.
   apply H57.
   eapply Is_empty.fields_struct_empty.
   eassumption.
   eassumption.
   eassumption.
   eassumption.
   eassumption.
  assert (clast0_nonempty: Is_empty clast0 -> False).
   intro.
   apply H66.
   eapply Is_empty.fields_struct_empty.
   eassumption.
   eassumption.
   eassumption.
   eassumption.
   eassumption.

 destruct (Z_eq_dec p0 p3).
  subst.
  destruct (prod_eq_dec Class.Inheritance.eq_dec (list_eq_dec peq) (h, l) (h0, l0)).
   injection e; intros until 2; subst.
   assert (clast0 = clast).
    generalize (path_last H20).
    generalize (path_last H8).
    congruence.
   subst.
   replace olast0 with olast in * by congruence.
   replace off0 with off in * by congruence.
   destruct ((FieldSignature.eq_dec (A := A)) fs fs0).
    subst.
    replace by0 with by in * by congruence.
    replace by_n0 with by_n in * by congruence.
    replace t3 with t1 in * by congruence.
    replace fo0 with fo in * by congruence.
    intros.
    assert (a1 <> a2) by congruence.
    assert (length a1 <= length a2)%nat by omega.
    generalize (IHa1 _ H80 H81 _ _ _ _ _ _ _ H32 _ _ _ _ _ H36 H14 H17 H23 H24 _ H38 _ H39).
    omega.
   generalize (field_offsets_non_overlap (intro H43) H45 H55 H58 H67 n0).
   unfold field_data_size.
   rewrite H15.
   rewrite H49.
   rewrite H27.
   rewrite H63.
   intro.
   generalize (H69 _ (refl_equal _) _ (refl_equal _)).
   omega.
  generalize (path_disjoint_field_zones n0 clast_nonempty H8 clast0_nonempty H20 H40 H50 H43 H53).
  omega.
 generalize (own_fields_offset_low_bound (intro H43)).
 generalize (own_fields_offset_low_bound (intro H53)).
 generalize (path_data_incl H8 clast_nonempty H40).
 destruct 1.
 generalize (H70 _ H43 _ H37).
 generalize (path_data_incl H20 clast0_nonempty H50).
 destruct 1.
 generalize (H72 _ H53 _ H37).
 generalize (data_size_high_bound (intro H37)).
 generalize (size_positive H37).
 intro.
 generalize (array_cells_disjoint n0 H73).
 omega.
Qed.


End Primary_paths.

(** * Identity of subobjects for non-empty bases (5.1) *)
     
Fact non_virtual_path_nonempty_distinct_offsets : forall to,
  (Is_empty to -> False) ->
  offsets ! to <> None ->
  forall l1 l2,
    l1 <> l2 ->
    forall from,
        path hierarchy to l1 from Class.Inheritance.Repeated ->
          path hierarchy to l2 from Class.Inheritance.Repeated ->
            forall accu z1, non_virtual_subobject_offset accu l1 = Some z1 ->
              forall z2, non_virtual_subobject_offset accu l2 = Some z2 ->
                z1 <> z2.
Proof.
  intros until 3. 
  pattern l1, l2.
  eapply distinct_lists_rect; eauto using peq ; clear l1 l2 H1.

  (* l1 is a strict prefix of l2 : absurd *)
  inversion 1; subst.
  rewrite H3 in *.
  inversion 1; subst.
  revert H7.
  repeat rewrite app_ass.
  simpl.
  intro.
  generalize (is_valid_repeated_subobject_split_right H7).
  functional inversion 1; subst.
  apply False_rect.
  assert {lt1 | a :: l2' = lt1 ++ to :: nil}.
   apply last_correct.
   assert (a :: l2' <> nil) by congruence.
   rewrite <- (last_app_left H9 (lt ++ to :: nil)).
   rewrite H6.
   apply last_complete.
  destruct H9.
  assert (path hierarchy to (a :: l2') a Class.Inheritance.Repeated).
   eleft; eauto.
  cut (Plt to to).
   apply Plt_irrefl.
  eauto using Ple_Plt_trans,  Well_formed_hierarchy.well_founded, Well_formed_hierarchy.path_le.

  (* disjoint paths *)
  intros.
  revert H2 H3.
  destruct l.
   simpl.   
   inversion 1; subst.
   inversion 1; subst.
   congruence.
  inversion 1; subst.
  assert (i :: l <> nil) by congruence.
  generalize (last_nonempty H8).
  intro.
  case_eq (last (i :: l)); try congruence.
  intros until 1.
  generalize (last_correct H10).
  destruct 1.
  revert H4 H5 H7.
  rewrite e.
  assert {lt1 | a1 :: l1' = lt1 ++ to :: nil}.
   assert (a1 :: l1' <> nil) by congruence.
   generalize (last_app_left H4 (i :: l)).
   rewrite H6.
   rewrite last_complete.
   intros.
   symmetry in H5.
   eauto using last_correct.
  destruct H4.
  intros until 3.
  rewrite app_ass in H7.
  simpl in H7.
  generalize (is_valid_repeated_subobject_split_right H7).
  functional inversion 1; subst.
  inversion 1; subst.
 assert {lt2 | a2 :: l2' = lt2 ++ to :: nil}.
   assert (a2 :: l2' <> nil) by congruence.
   generalize (last_app_left H17 (x ++ i0 :: nil)).
   rewrite H14.
   rewrite last_complete.
   intros.
   symmetry in H18.
   eauto using last_correct.
 destruct H17.
 revert H15.
 repeat rewrite app_ass.
 simpl.
 intro.
 generalize (is_valid_repeated_subobject_split_right H15).
 rewrite is_valid_repeated_subobject_equation.
 rewrite H16.
 destruct (In_dec super_eq_dec (Class.Inheritance.Repeated, a2) (Class.super cl1)); try congruence.
 intro.
 revert H4 H5.
 repeat rewrite app_ass.
 simpl.
 intros.
 generalize (non_virtual_subobject_offset_app_recip H4).
 intros; invall.
 functional inversion H21; subst.
 generalize (non_virtual_subobject_offset_app_recip H5).
 intros; invall.
 functional inversion H23; subst.
 replace o0 with o in * by congruence.
 assert (path hierarchy to (a1 :: l1') a1 Class.Inheritance.Repeated) by (eleft; eauto).
 assert (path hierarchy to (a2 :: l2') a2 Class.Inheritance.Repeated) by (eleft; eauto).
 assert (offsets ! a1 <> None).
  functional inversion X0; subst; try congruence.
  generalize (path_last H22); simpl; congruence.
 case_eq (offsets ! a1); try congruence.
 intros.
 assert (offsets ! a2 <> None).
  functional inversion X1; subst; try congruence.
  generalize (path_last H24); simpl; congruence.
 case_eq (offsets ! a2); try congruence.
 intros.
 generalize (non_virtual_path_non_virtual_data_incl H22 H X0).
 destruct 1.
 case_eq (offsets ! to); try congruence.
 intros ? J0.
 generalize (H34 _ J0 _ H26).
 generalize (non_virtual_path_non_virtual_data_incl H24 H X1).
 destruct 1.
 generalize (H36 _ J0 _ H30).
 assert (Is_empty a1 -> False) by eauto using Is_empty.path_from.
 assert (Is_empty a2 -> False) by eauto using Is_empty.path_from.
 generalize (nonempty_non_virtual_data_size_positive (intro J0) H).
 generalize (non_virtual_direct_base_nonempty_data_non_overlap (intro H28) H29 H37 H33 H38 H1 H26 H30).
 replace x3 with x2 in * by congruence.
 omega.
Qed. 

(* Corollary *) Fact path_nonempty_distinct_offsets :
  forall to,
    (Is_empty to -> False) ->
    offsets ! to <> None ->
    forall h1 l1 h2 l2,
      (h1, l1) <> (h2, l2) ->
      forall from,
        path hierarchy to l1 from h1 ->
        path hierarchy to l2 from h2 ->
        forall z1, subobject_offset from l1 = Some z1 ->
          forall z2, subobject_offset from l2 = Some z2 ->
            z1 <> z2.
Proof.
  intros.
  functional inversion H4; subst.
  functional inversion H5; subst.
  replace o0 with o in * by congruence.
  generalize (path_cons_repeated H2).
  intros.
  generalize (path_cons_repeated H3).
  intros.
  destruct (peq b b0).

  (* same virtual base *)
  subst.
  replace of0 with of in * by congruence.  
  assert (h1 = h2).
   generalize (Well_formed_hierarchy.categorize_paths Hhier H2 (refl_equal _)).
   destruct 1.
   generalize (Well_formed_hierarchy.categorize_paths Hhier H3 (refl_equal _)).
   destruct 1.
   destruct h1; destruct h2; eauto using sym_equal.
  assert (b0 :: _x <> b0 :: _x0) by congruence.
  eauto using non_virtual_path_nonempty_distinct_offsets.

  (* different virtual bases *)
  assert (offsets ! b <> None).
   functional inversion H6; subst; try congruence.
   generalize (path_last H11); simpl; congruence.
  case_eq (offsets ! b); try congruence.
  assert (offsets ! b0 <> None).
   functional inversion H8; subst; try congruence.
   generalize (path_last H12); simpl; congruence.
  case_eq (offsets ! b0); try congruence.
  intros.
  assert (b_nonempty : Is_empty b -> False) by eauto using Is_empty.path_from.
  assert (b0_nonempty : Is_empty b0 -> False) by eauto using Is_empty.path_from.
  generalize (virtual_base_offsets_nonempty_non_overlap (intro H9) H10 H17 H13 H16 b_nonempty b0_nonempty n).
  case_eq (offsets ! to); try congruence.
  intros until 1.
  generalize (non_virtual_path_non_virtual_data_incl H11 H H6).
  destruct 1.
  generalize (H20 _ H18 _ H17).
  generalize (non_virtual_path_non_virtual_data_incl H12 H H8).
  destruct 1.
  generalize (H22 _ H18 _ H16).
  generalize (nonempty_non_virtual_data_size_positive (intro H18) H).
  omega.
Qed.

Remark paths_cases : forall (A : Type) (aeq : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}) (l1 l2 : _ A),
  {l' | l1 = l2 ++ l'} +
  {a : _ & {l2' | l2 = l1 ++ a :: l2'}} + 
  {l : _ & { a1 : _ & { a2 : _ & { l1' : _ & { l2' |
    l1 = l ++ a1 :: l1' /\ l2 = l ++ a2 :: l2' /\ a1 <> a2}}}}}.
Proof.
  intros.
  destruct (list_eq_dec aeq l1 l2).
   subst.
   left.
   left.
   exists nil.
   rewrite <- app_nil_end.
   trivial.
   destruct (le_lt_dec (length l1) (length l2)).
   generalize (distinct_paths_cases aeq l n).
    tauto.
   assert (length l2 <= length l1)%nat by omega.
   assert (l2 <> l1) by congruence.
   generalize (distinct_paths_cases aeq H H0).
   destruct 1.
    invall.
    subst.
    left.
    left.
    repeat esplit.
   invall.
   subst.
   assert (x1 <> x0) by congruence.
   right.
   repeat esplit.
   assumption.
Qed.

(** 5.3 Theorem 4 non-empty *)
Theorem nonempty_distinct_offsets :
  forall pto,
    (Is_empty pto -> False) ->
    offsets ! pto <> None ->
    forall ap1 afrom asfrom ato1 i1 h1 p1,
      valid_relative_pointer hierarchy afrom asfrom ap1 ato1 i1 h1 p1 pto ->
      forall ap2 ato2 i2 h2 p2,
        valid_relative_pointer hierarchy afrom asfrom ap2 ato2 i2 h2 p2 pto ->
        forall o1, relative_pointer_offset afrom ato1 ap1 i1 p1 = Some o1 ->
          forall o2, relative_pointer_offset afrom ato2 ap2 i2 p2 = Some o2 ->
            (ap1, i1, (h1, p1)) <> (ap2, i2, (h2, p2)) ->
            o1 <> o2.
Proof.
  (* symmetry *)
  intros until 2.
  cut (
 forall (ap1 ap2 : array_path A), 
   (length ap1 <= length ap2)%nat ->
   forall (afrom : ident) (asfrom : Z) 
     (ato1 : ident) (i1 : Z) (h1 : Class.Inheritance.t) 
     (p1 : list ident),
   valid_relative_pointer hierarchy afrom asfrom ap1 ato1 i1 h1 p1 pto ->
   forall (ato2 : ident) (i2 : Z)
     (h2 : Class.Inheritance.t) (p2 : list ident),
   valid_relative_pointer hierarchy afrom asfrom ap2 ato2 i2 h2 p2 pto ->
   forall o1 : Z,
   relative_pointer_offset afrom ato1 ap1 i1 p1 = Some o1 ->
   forall o2 : Z,
     relative_pointer_offset afrom ato2 ap2 i2 p2 = Some o2 ->
     (ap1, i1, (h1, p1)) <> (ap2, i2, (h2, p2)) ->            
     o1 <> o2
  ).
   intros.
   destruct (le_lt_dec (length ap1) (length ap2)); eauto.
   assert (length ap2 <= length ap1)%nat by omega.
   assert ((ap2, i2, (h2, p2)) <> (ap1, i1, (h1, p1))) by congruence.
   cut (o2 <> o1).
    congruence.
   eauto.
   (* induction on the length of the array path *) 
 intro ap1.
 var (length ap1).
 dependent_revert ap1.
 induction v using  (well_founded_induction Wf_nat.lt_wf).
 (* alternative pointer representation *)
 intros.
 subst.
 assert (relative_pointer_alt_of_relative_pointer ap1 i1 (h1, p1) <> relative_pointer_alt_of_relative_pointer ap2 i2 (h2, p2)).
  rewrite <- relative_pointer_default_to_alt_to_default in H8.
  rewrite <- relative_pointer_default_to_alt_to_default in H8.
  congruence.
 clear H8.
 revert H2.
 revert H1 H3.
 rewrite <- (relative_pointer_alt_length_correct ap1 i1 (h1, p1)).
 rewrite <- (relative_pointer_alt_length_correct ap2 i2 (h2, p2)).
 generalize (valid_relative_pointer_valid_relative_pointer_alt H4).
 generalize (relative_pointer_alt_offset_correct H4 H6).
 clear H4 H6.
 generalize (valid_relative_pointer_valid_relative_pointer_alt H5).
 generalize (relative_pointer_alt_offset_correct H5 H7).
 clear H5 H7.
 destruct (relative_pointer_alt_of_relative_pointer ap1 i1 (h1, p1)).
 destruct (relative_pointer_alt_of_relative_pointer ap2 i2 (h2, p2)).
 clear ap1 i1 h1 p1 ap2 i2 h2 p2.
 intros.
 inversion H4; subst.
 inversion H2; subst.
 generalize H3.
 unfold relative_pointer_alt_offset.
 case_eq (offsets ! afrom); try congruence.
 intros until 1.
 case_eq (subobject_offset afrom p'); try congruence.
 intros until 1.
 rewrite (path_last H13).
 intro.
 assert (offsets ! through <> None).
  destruct f.
   destruct p.
   destruct p.
   destruct p.
   destruct p0.
   destruct (FieldSignature.type t1); try congruence.
   destruct (offsets ! through); congruence.
  invall; congruence.
 case_eq (offsets ! through); try congruence.
 intros.
 rewrite H20 in H10.
 generalize H1.
 unfold relative_pointer_alt_offset.
 rewrite H8.
 case_eq (subobject_offset afrom p'0); try congruence.
 intros until 1.
 rewrite (path_last H17).
 intro.
 assert (offsets ! through0 <> None).
  destruct f0.
   destruct p.
   destruct p.
   destruct p.
   destruct p0.
   destruct (FieldSignature.type t2); try congruence.
   destruct (offsets ! through0); congruence.
  invall; congruence.
 case_eq (offsets ! through0); try congruence.
 intros.
 rewrite H24 in H22.  
 case_eq (offsets ! pto); try congruence.
 intros.
 generalize (relative_pointer_alt_fields_incl H4 H H3 H8 H9 (path_last H13) H20 H25).
 intros; invall.
 generalize (relative_pointer_alt_fields_incl H2 H H1 H8 H21 (path_last H17) H24 H25).
 intros ; invall.
 assert (Is_empty through -> False).
  destruct f; invall; subst; try congruence.
  destruct p.
  destruct p.
  destruct p.
  destruct p0.
  invall.
  intros.
  apply H.
  eapply Is_empty.relative_pointer_to.
  eassumption.
  eassumption.
  eapply Is_empty.fields_struct_empty.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
 assert (Is_empty through0 -> False).
  destruct f0; invall; subst; try congruence.
  destruct p.
  destruct p.
  destruct p.
  destruct p0.
  invall.
  intros.
  apply H.
  eapply Is_empty.relative_pointer_to.
  eassumption.
  eassumption.
  eapply Is_empty.fields_struct_empty.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
 generalize (nonempty_non_virtual_data_size_positive (intro H25) H).
 intros.
 generalize (path_data_incl H13 H31 H9).
 destruct 1.
 generalize (H36 _ H20 _ H8).
 intros.
 generalize (data_size_high_bound (intro H8)).
 intros.
 generalize (path_data_incl H17 H33 H21).
 destruct 1.
 generalize (H40 _ H24 _ H8).
 intros.

 (* case analysis *)
 destruct (Z_eq_dec i i0).
  Focus 2.
  (* different cells *) 
  generalize (size_positive H8).
  intros.
  generalize (array_cells_disjoint n H42).
  omega.
 (* same cells *)
 subst.
 destruct f0.
  destruct p.
  destruct p.
  destruct p.
  destruct p0.
  invall.
  revert H22.
  rewrite H43.
  case_eq (assoc (FieldSignature.eq_dec (A := A)) t4 (field_offsets t2)); try congruence.
  intros until 1.
  case_eq (relative_pointer_offset x0 ato2 a z1 l); try congruence.
  injection 2; intros; subst.
  assert (Is_empty x0 -> False) by eauto using Is_empty.relative_pointer_from.
  assert (forall ty n, FieldSignature.type t4 = FieldSignature.Struct ty n -> Is_empty ty -> False) by congruence.
  assert (offsets ! x0 <> None).
   functional inversion H44; subst.
   functional inversion H50; subst; try congruence.
   inversion H45; subst.
   inversion H49; congruence.
  case_eq (offsets ! x0); try congruence.
  intros.
  generalize (relative_pointer_data_incl H45 H H44).
  destruct 1.
  generalize (H52 _ H50 _ H25).
  intros.
  generalize (own_fields_offset_low_bound (intro H24)).
  intros.
  generalize (field_offsets_nonempty_low_bound (intro H24) H22 H48).
  intros.
  generalize (non_virtual_data_size_field_offsets (intro H24) H22 H48).
  unfold field_data_size.
  rewrite H43.
  rewrite H50.
  intros.
  generalize (H56 _ (refl_equal _)).
  intros.
  destruct f.
   destruct p.
   destruct p.
   destruct p.
   destruct p0.
   invall.
   revert H10.
   rewrite H59.
   case_eq ( assoc (FieldSignature.eq_dec (A := A)) t7 (field_offsets t1)); try congruence.
   intros until 1.
   case_eq (relative_pointer_offset x3 ato1 a0 z4 l0); try congruence.
   injection 2; intros; subst.
   functional inversion H9; subst.
   functional inversion H21; subst.
   generalize (path_cons_repeated H13).
   intro.
   generalize (path_cons_repeated H17).
   intro.
   assert (Is_empty x3 -> False) by eauto using Is_empty.relative_pointer_from.
   assert (forall ty n, FieldSignature.type t7 = FieldSignature.Struct ty n -> Is_empty ty -> False) by congruence.
   assert (offsets ! x3 <> None).
    functional inversion H60; subst.
    functional inversion H74; subst; try congruence.
    inversion H61; subst.
    inversion H73; congruence.
   case_eq (offsets ! x3); try congruence.
   intros.
   generalize (relative_pointer_data_incl H61 H H60).
   destruct 1.
   generalize (H76 _ H74 _ H25).
   intros.
   generalize (own_fields_offset_low_bound (intro H20)).
   intros.
   generalize (field_offsets_nonempty_low_bound (intro H20) H10 H72).
   intros.
   generalize (non_virtual_data_size_field_offsets (intro H20) H10 H72).
   unfold field_data_size.
   rewrite H59.
   rewrite H74.
   intros.
   generalize (H80 _ (refl_equal _)).
   intros.   
   destruct (prod_eq_dec Class.Inheritance.eq_dec (list_eq_dec peq) (h', b :: _x) (h'0, b0 :: _x0)).
    injection e; intros; subst.
    (* same paths *)
    assert (through0 = through).
     generalize (path_last H68).
     generalize (path_last H69).
     congruence.
    subst.
    generalize (Well_formed_hierarchy.path_eq_hierarchy_eq Hhier H17 H13).
    intro; subst.
    replace z0 with z in * by congruence.
    replace t2 with t1 in * by congruence.      
    destruct ((FieldSignature.eq_dec (A := A)) t4 t7).
     (* same fields : use induction hypothesis *)
     subst.
     simpl in H5, H6.
     assert (length a0 <= length a)%nat by omega.
     assert (length a0 < S (length a0))%nat by omega.
     replace x3 with x0 in * by congruence.
     replace x4 with x1 in * by congruence.
     replace t9 with t6 in * by congruence.
     replace z5 with z2 in * by congruence.
     assert ((a0, z4, (t8, l0)) <> (a, z1, (t5, l))) by congruence.
     assert (z6 <> z3) by eauto. (* IH *)
     omega.
    (* distinct fields : they are disjoint *)
    generalize (field_offsets_non_overlap (intro H20) H22 H10 H48 H72 n).
    unfold field_data_size.
    rewrite H43.
    rewrite H50.
    rewrite H59.
    rewrite H74.
    intro.
    generalize (H83 _ (refl_equal _) _ (refl_equal _)).
    omega.
   (* different paths : their field zones are disjoint *)
   generalize (path_disjoint_field_zones n H31 H13 H33 H17 H9 H21 H20 H24).
   omega.
  (* ap1 is simple *)
  invall; subst.
  replace t3 with t1 in * by congruence.
  functional inversion H9; subst.
  functional inversion H21; subst.
  generalize (path_cons_repeated H13).
  intros.
  generalize (path_cons_repeated H17).
  intros.
  replace t0 with o in * by congruence.
  replace o0 with o in * by congruence.  
  destruct (peq b0 b).
   (* same virtual bases *)
   subst.
   replace of0 with of in * by congruence.
   generalize (paths_cases peq _x0 _x).
   destruct 1.
    (* p1 is a prefix of p2 : absurd *)
    destruct s.
    invall.
    subst.
    apply False_rect.    
    assert (path hierarchy through0 (through :: x2) through Class.Inheritance.Repeated).
     inversion H63; subst.
     generalize (last_correct (path_last H62)).
     destruct 1.
     assert (b :: _x ++ x2 = (b :: _x) ++ x2) by reflexivity.    
     assert (b :: _x ++ x2 = (x3 ++ through :: nil) ++ x2) by congruence.
     revert H69.
     rewrite app_ass.
     simpl.
     intros.
     generalize (eq_ind _ (fun y => is_valid_repeated_subobject hierarchy y = true) H67 _ H69).
     intros.
     generalize (is_valid_repeated_subobject_split_right H70).
     intros.
     assert (x3 ++ through :: x2 = lt ++ through0 :: nil) by eauto using trans_equal.
     generalize (last_complete lt through0).
     rewrite <- H72.
     assert (through :: x2 <> nil) by congruence.
     rewrite (last_app_left H73).
     intros.
     generalize (last_correct H74).
     destruct 1.
     eleft; eauto.
    apply Plt_irrefl with through.
    inversion H45; subst.
    apply Ple_Plt_trans with ato2.
     eauto using Well_formed_hierarchy.path_le.
    apply Ple_Plt_trans with x0.
     eauto using Well_formed_hierarchy.array_path_le.
    apply Plt_Ple_trans with through0.
     eauto using Well_formed_hierarchy.well_founded_struct.
    eauto using Well_formed_hierarchy.path_le.
   (* p2 is a prefix of p1 : o1 on the left, o2 on the right *)
   invall.
   subst.
   injection H10; intros; subst.
   inversion H62; subst.   
   generalize H14 (path_last H62) H67.
   refine (eq_ind ((b :: _x0) ++ x2 :: x3) (fun y =>
     non_virtual_subobject_offset of y = Some z ->
     last y = Some through ->
     is_valid_repeated_subobject hierarchy y = true ->
     i0 * size o + z <> i0 * size o + z0 + z2 + z3
   ) _ _  _).
    assert (x2 :: x3 <> nil) by congruence.
    rewrite (last_app_left H68).
    intros.
    generalize (non_virtual_subobject_offset_app_recip H69).
    intros; invall.
    generalize (is_valid_repeated_subobject_split_right H71).
    intros.
    generalize (last_correct H70).
    destruct 1.
    assert (path hierarchy through (x2 :: x3) x2 Class.Inheritance.Repeated) by (eleft; eauto).
    revert H72.
    generalize (path_last H17).
    intro.
    generalize (last_correct H72).
    destruct 1.
    rewrite e0.
    rewrite app_ass.
    simpl.
    intros.
    generalize (non_virtual_subobject_offset_app_recip H76).
    destruct 1; invall.
    replace x7 with z0 in * by congruence.
    revert H79.
    simpl.
    rewrite H24.
    case_eq ((non_virtual_direct_base_offsets t2) ! x2); try congruence.
    injection 2; intros; subst.
    assert (offsets ! x2 <> None).
     functional inversion H74; subst; try congruence.
     generalize (path_last H75); simpl; congruence.
    case_eq (offsets ! x2); try congruence.
    intros.
    assert (Is_empty x2 -> False) by eauto using Is_empty.path_from.
    generalize (non_virtual_direct_base_offsets_nonempty_high_bound (intro H24) H82 H77 H81).
    generalize (non_virtual_direct_base_offsets_low_bound (intro H24) H77).
    generalize (non_virtual_path_non_virtual_data_incl H75 H31 H74).
    destruct 1.
    generalize (H84 _ H20 _ H81).
    omega.
    reflexivity.
   (* paths diverge : data are disjoint *)
   invall; subst.
   replace (b :: x2 ++ x3 :: x5) with ((b :: x2) ++ x3 :: x5) in * by reflexivity.
   replace (b :: x2 ++ x4 :: x6) with ((b :: x2) ++ x4 :: x6) in * by reflexivity.
   assert (b :: x2 <> nil) by congruence.
   generalize (last_nonempty H65).
   intros.
   case_eq (last (b :: x2)); try congruence.
   intros.
   generalize (last_correct H67).
   destruct 1.
   rewrite e in *.
   revert H62  H63.
   inversion 1; subst.
   inversion 1; subst.
   generalize (is_valid_repeated_subobject_split_right H70).
   generalize (is_valid_repeated_subobject_split_right H74).
   generalize (last_complete lt through).
   rewrite <- H69.
   assert (x4 :: x6 <> nil) by congruence.
   rewrite (last_app_left H75).
   intro.
   generalize (last_correct H76).
   destruct 1.
   generalize (last_complete lt0 through0).
   rewrite <- H73.
   assert (x3 :: x5 <> nil) by congruence.
   rewrite (last_app_left H77).
   intro.
   generalize (last_correct H78).
   destruct 1.
   intros.
   assert (path hierarchy through (x4 :: x6) x4 Class.Inheritance.Repeated) by (eleft; eauto).
   assert (path hierarchy through0 (x3 :: x5) x3 Class.Inheritance.Repeated) by (eleft; eauto).
   assert (Is_empty x4 -> False) by (eapply Is_empty.path_from; eassumption).
   assert (Is_empty x3 -> False) by (eapply Is_empty.path_from; eassumption).
   revert H14 H59.
   repeat rewrite app_ass.
   simpl.
   intros.
   generalize (non_virtual_subobject_offset_app_recip H14).
   destruct 1; invall.
   generalize (non_virtual_subobject_offset_app_recip H59).
   destruct 1; invall.
   replace x10 with x11 in * by congruence.
   functional inversion H87; subst.
   functional inversion H89; subst.
   replace o3 with o2 in * by congruence.
   assert (offsets ! x4 <> None).
    functional inversion X; subst; try congruence.
    generalize (path_last H81); simpl; congruence.
   case_eq (offsets ! x4); try congruence.
   intros.
   assert (offsets ! x3 <> None).
    functional inversion X0; subst; try congruence.
    generalize (path_last H82); simpl; congruence.
   case_eq (offsets ! x3); try congruence.
   intros.
   generalize (non_virtual_path_non_virtual_data_incl H81 H31 X).
   destruct 1.
   generalize (H94 _ H20 _ H90).
   generalize (non_virtual_path_non_virtual_data_incl H82 H33 X0).
   destruct 1.
   generalize (H100 _ H24 _ H92).
   generalize (non_virtual_direct_base_nonempty_data_non_overlap (intro H96) H99 H84 H97 H83 H68 H92 H90).
   omega.
  (* different virtual bases *)
  assert (offsets ! b <> None).
   functional inversion H14; subst; try congruence.
   generalize (path_last H62); simpl; congruence.
  case_eq (offsets ! b); try congruence.
  intros.
  assert (offsets ! b0 <> None).
   functional inversion H59; subst; try congruence.
   generalize (path_last H63); simpl; congruence.
  case_eq (offsets ! b0); try congruence.
  intros.
  generalize (non_virtual_path_non_virtual_data_incl H62 H31 H14).
  destruct 1.
  generalize (H70 _ H20 _ H66).
  generalize (non_virtual_path_non_virtual_data_incl H63 H33 H59).
  destruct 1.
  generalize (H72 _ H24 _ H68).
  assert (b_nonempty : Is_empty b -> False) by eauto using Is_empty.path_from.
  assert (b0_nonempty : Is_empty b0 -> False) by eauto using Is_empty.path_from.
  generalize (virtual_base_offsets_nonempty_non_overlap (intro H8) H64 H68 H61 H66 b0_nonempty b_nonempty n).
  omega.
 (* ap2 is simple : necessarily, ap1 is simple and we may reuse the inheritance-only theorem *)
 destruct f.
  destruct p.
  destruct p.
  destruct p.
  destruct p0.
  simpl in H6.
  omega.
 invall; subst.
 subst.
 assert  ((h', p') <> (h'0, p'0)) by congruence.
 injection H10; intros; subst.
 injection H22; intros; subst.
 cut (z <> z0).
  omega.
 eauto using path_nonempty_distinct_offsets.
Qed.


End Nonempty_base_offsets.

End OF.

(** * Incremental computing of offsets *)

(** This section is useful for layout algorithms that incrementally compute the offsets, from the most-inherited to the most-derived classes *)

Section OF_compare.


Variable hierarchy : PTree.t (Class.t A).

Hypothesis hierarchy_wf : Well_formed_hierarchy.prop hierarchy.

Section OF1.

Variables offsets1 offsets2 : PTree.t t.

Variable cilimit : positive.

Hypothesis offsets_eq : forall j, Plt j cilimit -> offsets1 ! j = offsets2 ! j.

Variable guard1 : forall ci, offsets1 ! ci <> None -> hierarchy ! ci <> None.

Section Class_level_prop_eq.

Variable ci : ident.

Hypothesis Hci : Plt ci cilimit.

Variable o1 : t.

Hypothesis Ho1 : offsets1 ! ci = Some o1.

Let Hhier1 : hierarchy ! ci <> None.
Proof.
  apply guard1.
  congruence.
Qed.

Let h0 : {h | hierarchy ! ci = Some h}.
Proof.
  case_eq (hierarchy ! ci).
   intros.
   exists t0.
   trivial.
  intros.
  apply False_rect.
  eapply guard1.
  2 : eassumption.
  congruence.
Qed.

Let h := let (h, _) := h0 in h.

Let Hh : hierarchy ! ci = Some h.
Proof.
  unfold h.
  destruct h0.
  assumption.
Qed.

Hypothesis Hprop1 :   class_level_prop offsets1 hierarchy ci o1.

Fact non_virtual_direct_base_offsets_lt : forall b,
  (non_virtual_direct_base_offsets o1) ! b <> None ->
  Plt b ci.
Proof.
  intros.
  generalize (non_virtual_direct_base_offsets_guard Hprop1 H Hh).
  eauto using Well_formed_hierarchy.well_founded, Plt_trans.
Qed.

(* Corollary *) Fact non_virtual_direct_base_offsets_eq : forall b,
  (non_virtual_direct_base_offsets o1) ! b <> None ->
  offsets1 ! b = offsets2 ! b.
Proof.
  intros.
  eauto using offsets_eq, non_virtual_direct_base_offsets_lt, Plt_trans.
Qed.

(* Corollary *) Fact non_virtual_direct_base_offsets_eq_some : forall b c,
  (non_virtual_direct_base_offsets o1) ! b = Some c ->
  offsets1 ! b = offsets2 ! b.
Proof.
  intros.
  apply non_virtual_direct_base_offsets_eq.
  congruence.
Qed.

Fact virtual_base_offsets_le : forall b,
  (virtual_base_offsets o1) ! b <> None ->
  Ple b ci.
Proof.
  intros.
  generalize (virtual_base_offsets_guard Hprop1 H).
   inversion 1.
    eauto using Well_formed_hierarchy.is_virtual_base_of_lt, Plt_Ple.
    subst; apply Ple_refl.
Qed. 

(* Corollary *) Fact virtual_base_offsets_eq : forall b,
  (virtual_base_offsets o1) ! b <> None ->
  offsets1 ! b = offsets2 ! b.
Proof.
  intros.
  eauto using offsets_eq, virtual_base_offsets_le, Ple_Plt_trans.
Qed.

(* Corollary *) Fact virtual_base_offsets_eq_some : forall b c,
  (virtual_base_offsets o1) ! b = Some c ->
  offsets1 ! b = offsets2 ! b.
Proof.
  intros.
  apply virtual_base_offsets_eq.
  congruence.
Qed.

Fact field_offsets_lt : forall f,
  assoc (FieldSignature.eq_dec (A := A)) f (field_offsets o1) <> None ->
  forall ty n, FieldSignature.type f = FieldSignature.Struct ty n ->
    Plt ty ci.
Proof.
  intros; eauto using field_offsets_guard, Well_formed_hierarchy.well_founded_struct.
Qed.

Let Hfo : forall f,
  assoc (FieldSignature.eq_dec (A := A)) f (field_offsets o1) <> None ->
  (field_data_size offsets1 f = field_data_size offsets2 f /\ field_size offsets1 f = field_size offsets2 f /\ field_align offsets1 f = field_align offsets2 f).
Proof.
  intros.
  unfold field_data_size, field_size, field_align.
   case_eq (FieldSignature.type f).
    tauto.
   intros.
  replace (offsets2 ! struct) with (offsets1 ! struct).
   tauto.
  apply offsets_eq.
  eauto using field_offsets_lt, Plt_trans.
Qed.

Let Hsfo : forall f fo,
  assoc (FieldSignature.eq_dec (A := A)) f (field_offsets o1) = Some fo ->
  (field_data_size offsets1 f = field_data_size offsets2 f /\ field_size offsets1 f = field_size offsets2 f /\ field_align offsets1 f = field_align offsets2 f).
Proof.
  intros.
  apply Hfo.
  congruence.
Qed.

Let Hfod := fun f h => match @Hfo f h with conj j _ => j end.

Let Hfos := fun f h => match @Hfo f h with conj _ (conj j _) => j end.

Let Hfoa := fun f h => match @Hfo f h with conj _ (conj _ j) => j end.

Let Hsfod := fun f c h => match @Hsfo f c h with conj j _ => j end.

Let Hsfos := fun f c h => match @Hsfo f c h with conj _ (conj j _) => j end.

Let Hsfoa := fun f c h => match @Hsfo f c h with conj _ (conj _ j) => j end.

Variable o2 : t.

Hypothesis Ho2 : offsets2 ! ci = Some o2.

Lemma class_level_prop_eq :
    class_level_prop offsets2 hierarchy ci o2.
Proof.
  rewrite <- (offsets_eq Hci) in Ho2.
  replace o2 with o1 by congruence.
  inversion Hprop1.
  constructor; try assumption.
  
  intros.
  generalize (non_virtual_primary_base_offset0 _ H).
  intros.
  rewrite <- (non_virtual_direct_base_offsets_eq_some H0).
  auto.

  intros until 1.
  rewrite <- (non_virtual_direct_base_offsets_eq_some H).
  eauto.

  intros until 3.
  rewrite <- (non_virtual_direct_base_offsets_eq_some H).
  rewrite <- (non_virtual_direct_base_offsets_eq_some H1).
  eauto.

  intros until 2.
  rewrite <- (non_virtual_direct_base_offsets_eq_some H0).
  eauto.

  intros until 1.
  rewrite <- (Hsfoa H).
  eauto.

  intros until 2.
  rewrite <- (Hsfod H).
  rewrite <- (Hsfod H0).
  eauto.

  intros until 1.
  rewrite <- (Hsfod H).
  eauto.

  intros until 1.
  rewrite <- (Hsfos H).
  eauto.

  intros until 1.
  rewrite <- (non_virtual_direct_base_offsets_eq_some H).
  eauto.

  intros until 1.
  rewrite <- (non_virtual_direct_base_offsets_eq H).
  eauto.

  intros until 1.
  rewrite <- (Hfoa H).
  eauto.

  intros until 1.
  rewrite <- (virtual_base_offsets_eq_some H).
  eauto.

  intros until 1.
  rewrite <- (virtual_base_offsets_eq_some H).
  intros until 2.
  rewrite <- (virtual_base_offsets_eq_some H1).
  eauto.

  intros until 1.
  rewrite <- (virtual_base_offsets_eq_some H).
  eauto.

  intros until 1.
  rewrite <- (virtual_base_offsets_eq_some H).
  eauto. 

  intros until 1.
  rewrite <- (virtual_base_offsets_eq H).
  eauto.
Qed.

End Class_level_prop_eq.

Hypothesis intro1 : forall ci, Plt ci cilimit -> forall o, offsets1 ! ci = Some o -> class_level_prop offsets1 hierarchy ci o.

Lemma combined_empty_base_offsets_eq : forall ci, Plt ci cilimit ->
(forall b z,
  non_virtual_empty_base_offset offsets1 hierarchy ci b z ->
   non_virtual_empty_base_offset offsets2 hierarchy ci b z)
  /\
  (forall b z,
    empty_base_offset offsets1 hierarchy ci b z ->
    empty_base_offset offsets2 hierarchy ci b z).
Proof.
 induction ci using (well_founded_induction Plt_wf).
 intros.
 asplit.
  inversion 1; subst.
   constructor.
   assumption.
   trivial.
  econstructor.
   rewrite <- (offsets_eq H0).
   eassumption.
   eassumption.
  assert ( (non_virtual_direct_base_offsets oc) ! ci' <> None) by congruence.
  assert (Plt ci' ci).
   eapply non_virtual_direct_base_offsets_lt.
   eassumption.
   auto.
  congruence.
  assert (Plt ci' cilimit) by eauto using Plt_trans.
  destruct (H _ H6 H7).
  auto.

  assert (assoc (FieldSignature.eq_dec (A := A)) f (field_offsets oc) <> None) by congruence.
  assert (Plt cif ci) by eauto using field_offsets_lt.
  assert (Plt cif cilimit) by eauto using Plt_trans.
  eapply non_virtual_empty_base_offset_field.
   rewrite <- (offsets_eq H0).
   eassumption.
   eassumption.
   eassumption.
   rewrite <- (offsets_eq H11).
   eassumption.
   eassumption.
   assumption.
   destruct (H _ H10 H11).
   auto.

 inversion 1; subst.
 econstructor.
  rewrite <- (offsets_eq H0).
  eassumption.
  eassumption.
 assert ((virtual_base_offsets oc) ! ci' <> None) by congruence.
 destruct (virtual_base_offsets_guard (intro1 H0 H3) H6).
  assert (Plt ci' ci) by eauto using Well_formed_hierarchy.is_virtual_base_of_lt.
  assert (Plt ci' cilimit) by eauto using Plt_trans.
  destruct (H _ H8 H9).
  auto.
 subst; auto.
Qed.

Definition non_virtual_empty_base_offsets_eq := fun ci h =>
  let (j, _) := @combined_empty_base_offsets_eq ci h in j.

Definition empty_base_offsets_eq := fun ci h =>
  let (_, j) := @combined_empty_base_offsets_eq ci h in j.

End OF1.

Variables offsets1 offsets2 : PTree.t t.

Variable cilimit : positive.

Hypothesis offsets_eq : forall j, Plt j cilimit -> offsets1 ! j = offsets2 ! j.

Let offsets_eq2 :  forall j, Plt j cilimit -> offsets2 ! j = offsets1 ! j.
Proof.
intros; symmetry; eauto.
Qed.

Hypothesis guard1 : forall ci, offsets1 ! ci <> None -> hierarchy ! ci <> None.

Hypothesis guard2 : forall ci, offsets2 ! ci <> None -> hierarchy ! ci <> None.

Hypothesis intro1 : forall ci, Plt ci cilimit -> forall o, offsets1 ! ci = Some o -> class_level_prop offsets1 hierarchy ci o.

Let intro2 : forall ci, Plt ci cilimit -> forall o, offsets2 ! ci = Some o -> class_level_prop offsets2 hierarchy ci o.
Proof.
  intros until 1.
  rewrite (offsets_eq2 H).
  intros.
  eapply class_level_prop_eq.
   eassumption.
   assumption.
   assumption.
   eassumption.
   auto.
   rewrite (offsets_eq2 H).
   assumption.
Qed.

Lemma disjoint_empty_base_offsets_eq : forall ci, Plt ci cilimit -> forall o1, offsets1 ! ci = Some o1 -> disjoint_empty_base_offsets offsets1 hierarchy ci o1 -> forall o2, offsets2 ! ci = Some o2 -> disjoint_empty_base_offsets offsets2 hierarchy ci o2.
Proof.
  destruct 3.
  rewrite <- (offsets_eq H).
  rewrite H0.
  injection 1; intros; subst.
  constructor.
    intros.
    assert (Plt ci1 cilimit /\ Plt ci2 cilimit).
     assert ((baseref o2) ! ci1 <> None) by congruence.
     assert ((baseref o2) ! ci2 <> None) by congruence.
     inversion H2; subst.
      split; eauto using Plt_trans, non_virtual_direct_base_offsets_lt.
     split; eauto using Ple_Plt_trans, virtual_base_offsets_le.
    invall.
    eauto using non_virtual_empty_base_offsets_eq.
   intros until 1.
   assert (Plt ci1 ci).
    eapply non_virtual_direct_base_offsets_lt.
    eexact guard1.
    eassumption.
    auto.
    congruence.
   intros until 2.
   assert (Plt ci2 ci).
    eapply field_offsets_lt.
    eexact guard1.
    eassumption.
    auto.
    2 : eassumption.
    congruence.
   assert (Plt ci2 cilimit) by eauto using Plt_trans.    
   assert (Plt ci1 cilimit) by eauto using Plt_trans.    
   rewrite (offsets_eq2 H7).
   intros.
   eauto using non_virtual_empty_base_offsets_eq, empty_base_offsets_eq.
  intros until 2.
  assert (Plt ci1 ci).
   eapply field_offsets_lt.
   eexact guard1.
   eassumption.
   auto.
   2 : eassumption.
   congruence.
  assert (Plt ci1 cilimit) by eauto using Plt_trans.
  rewrite (offsets_eq2 H5).
  intros until 5.
  assert (Plt ci2 ci).
   eapply field_offsets_lt.
   eexact guard1.
   eassumption.
   auto.
   2 : eassumption.
   congruence.
  assert (Plt ci2 cilimit) by eauto using Plt_trans.
  rewrite (offsets_eq2 H12).
  intros; eauto using non_virtual_empty_base_offsets_eq, empty_base_offsets_eq.
Qed.

End OF_compare.

End Offsets.
