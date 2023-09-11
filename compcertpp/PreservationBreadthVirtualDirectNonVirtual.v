Load PreservationHeader.

Ltac forward := constructor; simpl; intros; try discriminate; try omegaContradiction.
Ltac fin := forward; reflexivity.

Lemma nodup_v : forall cn c, (Program.hierarchy prog) ! cn = Some c ->
  forall l0 b1 l1 l2, vborder_list (Program.hierarchy prog) (Class.super c) (l0 ++ b1 :: l1 ++ b1 :: l2) -> False.
Proof.
  intros.
  eapply NoDup_elim.
  eapply vborder_list_no_dup.
  eassumption.
  reflexivity.
Qed.

Lemma nodup_nv : forall cn c, hier ! cn = Some c ->
        forall l0 b1 l1 l2, map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b) (filter (fun hb : _ * ident =>
          match hb with
            | (Class.Inheritance.Shared, _) => false
            | _ => true
          end
        ) (Class.super c)) = (l0 ++ b1 :: l1 ++ b1 :: l2) -> False.
Proof.
  intros.
  generalize (NoDup_repeated_bases (Well_formed_hierarchy.bases_no_dup hierarchy_wf H)).
  intro.
  eauto using NoDup_elim.
Qed.

Lemma goal : forall obj o,
    (Globals.heap (State.global s2)) ! obj = Some o ->
    forall ar cn n,
      valid_array_path hier cn n (Object.class o) (Object.arraysize o) ar ->
      match last ar with
        | None => n = Object.arraysize o /\ cn = Object.class o
        | Some (_, _, fs) => exists n', n = Zpos n' /\ FieldSignature.type fs = FieldSignature.Struct cn n'
      end ->
      forall i, 0 <= i < n ->
        forall vb, is_virtual_base_of hier vb cn ->
        forall c, hier ! cn = Some c ->
          forall nvb, In (Class.Inheritance.Repeated, nvb) (Class.super c) ->
            constructed_sibling_before (assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, vb :: nil))) (State.construction_states s2)) (assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nvb :: nil))) (State.construction_states s2))
            .
Proof.
 inversion Hs1.
 inversion step; subst; simpl in *; unfold Globals.update in *; simpl in *; subst; try assumption.

(* 11: Sblock Some *)
symmetry in H1.
unfold Globals.new in H1.
injection H1; intros until 2; subst; simpl in *.
intros until 1.
destruct (peq obj (Globals.next_object gl)).
 subst.
 rewrite PTree.gss in H2.
 injection H2; intros; subst; simpl in *.
 rewrite (construction_states_none _ (Globals.valid_none valid_global (Ple_refl _))).
 rewrite (construction_states_none _ (Globals.valid_none valid_global (Ple_refl _))).
 fin.
rewrite PTree.gso in H2; eauto.

(* 10: Sconstructor Kconstrarray *)
intros. 
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil)))
).
 discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn0 :: nvb :: nil)))
).
 discriminate.
eauto.

(* 9: Sreturn Kconstrothercells *)
intros.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil)))
).
  discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn0 :: nvb :: nil)))
).
  discriminate.
eauto.

(* 8: Sconstructor Kconstr base *)
intros.
unfold state_kind_inv in kind.
simpl in kind.
destruct k2; invall; subst.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil)))
 ).
  destruct p.
   discriminate.
  destruct p0; discriminate.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn :: nvb :: nil)))
 ).
  destruct p.
   discriminate.
  destruct p0.
   simpl in e.
   injection e; intros; subst.
   simpl in *.
   cut (
 (assoc (pointer_eq_dec (A:=A))
        (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil))) cs) = Some Constructed
   ).
    unfold_ident.
    intro.
    rewrite H5.
    forward.
   eauto.
  destruct p1; discriminate.
 eauto.
sdestruct (
  pointer_eq_dec (A:=A)
  (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
  (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn :: nvb :: nil)))
).
 discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil)))
).
 2 : eauto.
injection e; intros; subst.
forward.
generalize (H19 _ (or_introl _ (refl_equal _))).
unfold_ident.
intro.
eapply constructed_sibling_before_none.
eauto.
unfold_ident_in_all; rewrite H10; simpl; omega.

(* 7: Sreturn Kconstrother base *)
intros.
generalize (stack _ (or_introl _ (refl_equal _))).
simpl.
intro.
destruct k2;  invall; subst.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil)))
 ).
  destruct p.
   discriminate.
  destruct p; discriminate.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn :: nvb :: nil)))
 ).
  destruct p.
   discriminate.
  destruct p.
   simpl in e.
   injection e; intros; subst.
   simpl in *.
   cut (
 (assoc (pointer_eq_dec (A:=A))
        (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil))) cs) = Some Constructed
   ).
    unfold_ident.
    intro.
    rewrite H2.
    forward.
   unfold state_kind_inv in kind.
   simpl in kind.
   invall; subst.
   eapply constructed_sibling_before_constructed.
   eauto.
   unfold_ident_in_all; rewrite H2; simpl; omega.
   unfold_ident_in_all; rewrite H2; simpl; omega.
  destruct p; discriminate.
 eauto.
sdestruct (
  pointer_eq_dec (A:=A)
  (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
  (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn :: nvb :: nil)))
).
 discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil)))
).
 2 : eauto.
injection e; intros; subst.
forward.

(* 6: constr base direct non virtual nil *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil)))
).
 injection e; intros; subst.
 sdestruct (
   pointer_eq_dec (A:=A)
   (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil)))
   (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn0 :: nvb :: nil)))
 ).
  discriminate.
 forward.
 unfold state_kind_inv in kind.
 simpl in kind.
 intros; invall; subst.
 eapply constructed_sibling_before_none.
 eauto.
 unfold_ident_in_all; rewrite H10; simpl; omega.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn0 :: nvb :: nil)))
).
 2 : eauto.
injection e; intros; subst.
cut (
 (assoc (pointer_eq_dec (A:=A))
        (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil))) cs) = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H8.
 forward.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
eapply constructed_sibling_before_constructed.
eauto.
unfold_ident_in_all; rewrite H9; simpl; omega.
unfold_ident_in_all; rewrite H9; simpl; omega.

(* Destruction *)

(* 5: destr array cons *)
intros.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i, (Class.Inheritance.Shared, vb :: nil)))
).
 discriminate.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i, (Class.Inheritance.Repeated, cn0 :: nvb :: nil)))
).
 discriminate.
eauto.

(* 4: destr field nil *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil)))
).
 injection e; intros; subst.
 sdestruct (
pointer_eq_dec (A:=A)
           (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn0 :: nvb :: nil)))
 ).
  discriminate.
 forward.
 unfold state_kind_inv in kind.
 simpl in kind; invall; subst.
 eapply constructed_sibling_before_destructed.
 eauto.
 unfold_ident_in_all; rewrite H11; simpl; omega.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn0 :: nvb :: nil)))
).
 2 : eauto.
injection e; intros; subst.
cut (
(assoc (pointer_eq_dec (A:=A))
        (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil))) cs) = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H9.
 forward.
unfold state_kind_inv in kind.
simpl in kind; invall; subst.
eapply constructed_sibling_before_constructed.
eauto.
unfold_ident_in_all; rewrite H10; simpl; omega.
unfold_ident_in_all; rewrite H10; simpl; omega.

(* 3: destr *)
unfold state_kind_inv in kind.
simpl in kind.
destruct beta; intros; invall; subst. 
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil)))
 ).
  destruct p.
   discriminate.
  destruct p0; discriminate.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn :: nvb :: nil)))
 ).
  2 : eauto.
  destruct p.
   discriminate.
  destruct p0.
   simpl in e; injection e; intros; subst.
   cut (
 (assoc (pointer_eq_dec (A:=A))
        (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil))) cs) = Some Constructed
   ).
    unfold_ident.
    intro.
    rewrite H6.
    forward.
  eauto.
 destruct p1; discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn :: nvb :: nil)))
).
 discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil)))
).
 2 : eauto.
injection e; intros; subst.
forward.
 inversion H12; subst.
 inversion H27; subst.
 replace o0 with o in * by abstract congruence.
 generalize (valid_array_path_last H10 H0).
 intro; subst.
 inversion H25; subst.
 injection H26; intros; subst.
 replace x2 with c0 in * by abstract congruence.
 eauto.

(* 2: destr base direct non virtual nil Kdestrother base *)
intros.
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, hp))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil)))
).
 injection e; intros; subst.
 sdestruct (
pointer_eq_dec (A:=A)
           (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn :: nvb :: nil)))
 ). 
  discriminate.
forward.
revert kind.
unfold state_kind_inv; simpl.
intros; invall; subst.
eapply constructed_sibling_before_destructed.
eauto.
unfold_ident_in_all.
rewrite H8.
simpl; omega.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, hp))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn :: nvb :: nil)))
).
 2 : eauto.
injection e; intros; subst.
cut (
(assoc (pointer_eq_dec (A:=A))
        (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil))) cs) = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H6.
 forward.
revert kind.
unfold state_kind_inv; simpl.
intros; invall; subst.
eapply constructed_sibling_before_constructed.
eauto.
unfold_ident_in_all;rewrite H7; simpl; omega.
unfold_ident_in_all;rewrite H7; simpl; omega.

(* 1: destr base virtual nil *)
unfold state_kind_inv in kind. 
simpl in kind.
invall; subst.
intros.
sdestruct (pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, x1 :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, vb :: nil)))
).
 discriminate.
sdestruct (pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, x1 :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn0 :: nvb :: nil)))
).
 discriminate.
eauto.

Qed.

End Preservation.


 
 


