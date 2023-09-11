Load PreservationHeader.

Ltac forward := constructor; simpl; intros; try discriminate; try omegaContradiction.
Ltac fin := forward; reflexivity.

Lemma goal :forall obj o,
  (Globals.heap (State.global s2)) ! obj = Some o ->
    forall ar cn n,
      valid_array_path hier cn n (Object.class o) (Object.arraysize o) ar ->
      match last ar with
        | None => n = Object.arraysize o /\ cn = Object.class o
        | Some (_, _, fs) => exists n', n = Zpos n' /\ FieldSignature.type fs = FieldSignature.Struct cn n'
      end ->
      forall i1 i2, 0 <= i1 -> i1 < i2 -> i2 < n ->
        constructed_sibling_before (assoc (@pointer_eq_dec _) (obj, (ar, i1, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s2)) (assoc (@pointer_eq_dec _) (obj, (ar, i2, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s2))
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
           (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn0 :: nil)))
).
 injection e; intros; subst.
 sdestruct (
pointer_eq_dec (A:=A)
           (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn0 :: nil)))
           (obj0, (ar0, i2, (Class.Inheritance.Repeated, cn0 :: nil)))
 ).
  injection e0; intros; subst.
  abstract omegaContradiction.
 forward.
 unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 apply H17.
 assert (n0 = n).
  revert H13 H4.
  destruct (last ar0).
   destruct p.
   destruct p.
   intros; invall; congruence.
  intros; invall; congruence.
 subst.
 omega.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i2, (Class.Inheritance.Repeated, cn0 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
cut (
 (assoc (pointer_eq_dec (A:=A))
        (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn0 :: nil))) cs) = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H10.
 forward.
 unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 apply H14.
 omega.

(* 9: Sreturn Kconstrothercells *)
intros.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn0 :: nil)))
).
 forward.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i2, (Class.Inheritance.Repeated, cn0 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
cut (
 (assoc (pointer_eq_dec (A:=A))
        (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn0 :: nil))) cs) = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H5.
 forward.
 unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 eapply constructed_sibling_before_constructed.
 eauto.
 unfold_ident_in_all; rewrite H5; simpl; omega.
 unfold_ident_in_all; rewrite H5; simpl; omega.

(* 8: Sconstructor Kconstr base *)
revert kind.
unfold state_kind_inv.
simpl.
intros; invall; subst.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj,
           (ar, i,
           (match k2 with
            | Constructor.direct_non_virtual => h
            | Constructor.virtual => Class.Inheritance.Shared
            end,
           match k2 with
           | Constructor.direct_non_virtual => p ++ b :: nil
           | Constructor.virtual => b :: nil
           end))) (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn :: nil)))
).
 destruct k2; try discriminate.
 destruct p; try discriminate.
 destruct p0; discriminate.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj,
           (ar, i,
           (match k2 with
            | Constructor.direct_non_virtual => h
            | Constructor.virtual => Class.Inheritance.Shared
            end,
           match k2 with
           | Constructor.direct_non_virtual => p ++ b :: nil
           | Constructor.virtual => b :: nil
           end))) (obj0, (ar0, i2, (Class.Inheritance.Repeated, cn :: nil)))
).
 destruct k2; try discriminate.
 destruct p; try discriminate.
 destruct p0; discriminate.
eauto.

(* 7: Sreturn Kconstrother base *)
generalize (stack _ (or_introl _ (refl_equal _))).
simpl; intros; invall; subst.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj,
           (ar, i,
           (match k2 with
            | Constructor.direct_non_virtual => h
            | Constructor.virtual => Class.Inheritance.Shared
            end,
           match k2 with
           | Constructor.direct_non_virtual => p ++ b :: nil
           | Constructor.virtual => b :: nil
           end))) (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn :: nil)))
).
 forward.
sdestruct (
  pointer_eq_dec (A:=A)
           (obj,
           (ar, i,
           (match k2 with
            | Constructor.direct_non_virtual => h
            | Constructor.virtual => Class.Inheritance.Shared
            end,
           match k2 with
           | Constructor.direct_non_virtual => p ++ b :: nil
           | Constructor.virtual => b :: nil
           end))) (obj0, (ar0, i2, (Class.Inheritance.Repeated, cn :: nil)))
).
 destruct k2; try discriminate.
 destruct p; try discriminate.
 destruct p; discriminate.
eauto.

(* 6: constr base direct non virtual nil *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn0 :: nil)))
).
 injection e; intros; subst.
 sdestruct (
pointer_eq_dec (A:=A)
           (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn0 :: nil)))
           (obj0, (ar0, i2, (Class.Inheritance.Repeated, cn0 :: nil)))
 ).
  injection e0; intro; subst; omegaContradiction.
 forward.
 unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 eapply constructed_sibling_before_none. 
 eauto.
 unfold_ident_in_all; rewrite H9; simpl; omega.
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i2, (Class.Inheritance.Repeated, cn0 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
cut (
(assoc (pointer_eq_dec (A:=A))
        (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn0 :: nil))) cs) = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H7.
 fin.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
eapply constructed_sibling_before_constructed.
eauto.
unfold_ident_in_all; rewrite H8; simpl; omega.
unfold_ident_in_all; rewrite H8; simpl; omega.

(* Destruction *)

(* 5: destr array cons *)
intros.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn0 :: nil)))
).
 injection e; intros; subst.
 sdestruct (
 pointer_eq_dec (A:=A)
           (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn0 :: nil)))
           (obj0, (ar0, i2, (Class.Inheritance.Repeated, cn0 :: nil)))
 ).
  injection e0; intros; subst; omegaContradiction.
 forward.
 unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 apply H18.
 assert (n = x).
  revert H14 H6.
  destruct (last ar0).
   destruct p.
   destruct p.
   intros; invall; congruence.
  intros; invall; congruence.
 subst; omega.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i2, (Class.Inheritance.Repeated, cn0 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
cut (
(assoc (pointer_eq_dec (A:=A))
        (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn0 :: nil))) cs) = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H10.
 forward.
unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 apply H15.
omega.

(* 4: destr field nil *)
intros.
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn0 :: nil)))
).
 injection e; intros; subst.
 sdestruct (
 pointer_eq_dec (A:=A)
           (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn0 :: nil)))
           (obj0, (ar0, i2, (Class.Inheritance.Repeated, cn0 :: nil)))
 ).
  injection e0; intros; subst; omegaContradiction.
 forward.
 unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 eapply constructed_sibling_before_destructed.
 eauto.
 unfold_ident_in_all; rewrite H10; simpl; omega.
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i2, (Class.Inheritance.Repeated, cn0 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
cut (
(assoc (pointer_eq_dec (A:=A))
        (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn0 :: nil))) cs)
 = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H8.
 fin.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
eapply constructed_sibling_before_constructed.
eauto.
unfold_ident_in_all; rewrite H9; simpl; omega.
unfold_ident_in_all; rewrite H9; simpl; omega.

(* 3: destr *)
intros.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
sdestruct (
pointer_eq_dec (A:=A)
           (obj,
           (ar, i,
           (match beta with
            | Constructor.direct_non_virtual => h
            | Constructor.virtual => Class.Inheritance.Shared
            end,
           match beta with
           | Constructor.direct_non_virtual => p ++ b :: nil
           | Constructor.virtual => b :: nil
           end))) (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn :: nil)))
).
 destruct beta; try discriminate.
 destruct p; try discriminate.
 destruct p0; discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj,
           (ar, i,
           (match beta with
            | Constructor.direct_non_virtual => h
            | Constructor.virtual => Class.Inheritance.Shared
            end,
           match beta with
           | Constructor.direct_non_virtual => p ++ b :: nil
           | Constructor.virtual => b :: nil
           end))) (obj0, (ar0, i2, (Class.Inheritance.Repeated, cn :: nil)))
).
 destruct beta; try discriminate.
 destruct p; try discriminate.
 destruct p0; discriminate.
eauto.

(* 2: destr base direct non virtual nil Kdestrother base *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, hp))
           (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn :: nil)))
).
 injection e; intros; subst.
 sdestruct (
pointer_eq_dec (A:=A)
           (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i2, (Class.Inheritance.Repeated, cn :: nil)))
 ).
  injection e0; intros; subst; omegaContradiction.
 unfold state_kind_inv in kind; simpl in kind; invall; subst.
 forward.
 eapply constructed_sibling_before_destructed.
 eauto.
 unfold_ident_in_all; rewrite H6; simpl; omega.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, hp))
           (obj0, (ar0, i2, (Class.Inheritance.Repeated, cn :: nil)))
).
 2 : eauto.
injection e; intros; subst.
cut (
(assoc (pointer_eq_dec (A:=A))
        (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn :: nil))) cs)
 = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H5.
 fin.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
eapply constructed_sibling_before_constructed.
eauto.
unfold_ident_in_all; rewrite H6; simpl; omega.
unfold_ident_in_all; rewrite H6; simpl; omega.

(* 1: destr base virtual nil *)
unfold state_kind_inv in kind. 
simpl in kind.
invall; subst.
intros.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, x1 :: nil)))
           (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn0 :: nil)))
).
 injection e; intros; subst.
 sdestruct (
pointer_eq_dec (A:=A)
           (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn0 :: nil)))
           (obj0, (ar0, i2, (Class.Inheritance.Repeated, cn0 :: nil)))
 ).
  injection e0; intros; subst; omegaContradiction.
 forward.
 eapply constructed_sibling_before_destructed.
 eauto.
 unfold_ident_in_all; rewrite H1; simpl; omega.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, x1 :: nil)))
           (obj0, (ar0, i2, (Class.Inheritance.Repeated, cn0 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
cut (
 (assoc (pointer_eq_dec (A:=A))
        (obj0, (ar0, i1, (Class.Inheritance.Repeated, cn0 :: nil))) cs) = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H15.
 forward.
eapply constructed_sibling_before_constructed.
eauto.
unfold_ident_in_all; rewrite H1; simpl; omega.
unfold_ident_in_all; rewrite H1; simpl; omega.

Qed.

End Preservation.


 
 

