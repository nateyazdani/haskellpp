Load PreservationHeader.

Ltac forward := constructor; simpl; intros; try discriminate; try omegaContradiction.
Ltac fin := forward; reflexivity.


Lemma goal : forall obj o,
    (Globals.heap (State.global s2)) ! obj = Some o ->
    forall ar cn n,
      valid_array_path hier cn n (Object.class o) (Object.arraysize o) ar ->
      match last ar with
        | None => n = Object.arraysize o /\ cn = Object.class o
        | Some (_, _, fs) => exists n', n = Zpos n' /\ FieldSignature.type fs = FieldSignature.Struct cn n'
      end ->
      forall i, 0 <= i < n ->
        forall b, is_virtual_base_of hier b cn ->
          constructed_base_child_of (assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b :: nil))) (State.construction_states s2)) (assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s2))
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
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b :: nil)))
).
 discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn0 :: nil)))
).
2: eauto.
injection e; intros; subst.
revert kind.
unfold state_kind_inv; simpl.
intros; invall; subst.
assert (i0 <= i0 < n) by abstract omega.
generalize (H15 _ H5).
intro.
generalize (construction_states_virtual_bases _ _ H2 _ _ _ H3 H4 _ (conj H14 H17) _ H8).
unfold_ident_in_all.
rewrite H18.
destruct 1.
forward.
rewrite (constructed_base_child_of_none (refl_equal _)).
simpl; omega.

(* 9: Sreturn Kconstrothercells *)
intros.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b :: nil)))
).
  discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn0 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
revert kind.
unfold state_kind_inv; simpl.
intro; invall; subst.
forward.
eapply construction_states_virtual_bases.
eassumption.
eassumption.
assumption.
omega.
assumption.
unfold_ident_in_all; rewrite H4; simpl; omega.
unfold_ident_in_all; rewrite H4; simpl; omega.

(* 8: Sconstructor Kconstr base *)
intros.
unfold state_kind_inv in kind.
simpl in kind.
destruct k2; invall; subst.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b0 :: nil)))
 ).
  destruct p.
   discriminate.
  destruct p0; discriminate.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn :: nil)))
 ).
  destruct p.
   discriminate.
  destruct p0; discriminate.
 eauto.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn :: nil)))
).
 discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b0 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
inversion H10; subst.
inversion H23; subst.
replace o0 with o in * by abstract congruence.
generalize (valid_array_path_last H3 H5).
intro; subst.
inversion H21; subst.
injection H22; intros; subst.
unfold_ident_in_all.
rewrite H9.
fin.

(* 7: Sreturn Kconstrother base *)
intros.
generalize (stack _ (or_introl _ (refl_equal _))).
simpl.
intro.
destruct k2;  invall; subst.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b0 :: nil)))
 ).
  destruct p.
   discriminate.
  destruct p; discriminate.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn :: nil)))
 ).
  destruct p.
   discriminate.
  destruct p; discriminate.
 eauto.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn :: nil)))
).
 discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b0 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
inversion H6; subst.
inversion H17; subst.
replace o0 with o in * by abstract congruence.
generalize (valid_array_path_last H2 H0).
intro; subst.
inversion H15; subst.
injection H16; intros; subst.
unfold_ident_in_all.
rewrite H4.
fin.

(* 6: constr base direct non virtual nil *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn0 :: nil)))
).
 injection e; intros; subst.
 sdestruct (
pointer_eq_dec (A:=A)
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn0 :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b :: nil)))
 ).
   discriminate.
 forward.
 revert kind.
 unfold state_kind_inv; simpl.
 intro; invall; subst.
 eapply H18.
 trivial.
 reflexivity.
 assumption.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b :: nil)))
).
 2 : eauto.
injection e; intros; subst.
revert kind.
unfold state_kind_inv; simpl.
intros; invall; subst.
destruct stk; try contradiction.
destruct t; simpl in H13; try contradiction.
 generalize (stack _ (or_introl _ (refl_equal _))).
 simpl.
 destruct inhpath.
 destruct k; try contradiction.
  destruct kind; intros; invall; subst.
   destruct l.
    discriminate.
   destruct l; discriminate.
   inversion H18; subst.
   inversion H28; subst.
   replace o0 with o in * by abstract congruence.
   generalize (valid_array_path_last H6 H2).
   intros; subst.
   inversion H23; subst.
   injection H26; intros; subst.
   unfold_ident_in_all.
   rewrite H4.
   fin.
  invall; discriminate.

(* Destruction *)

(* 5: destr array cons *)
intros.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i, (Class.Inheritance.Shared, b :: nil)))
).
 discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i, (Class.Inheritance.Repeated, cn0 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
forward.
intros.
revert kind.
unfold state_kind_inv; simpl.
intros; invall; subst.
assert (0 <= i <= i) by omega.
generalize (H16 _ H7).
intro.
eapply construction_states_virtual_bases.
eassumption.
2 : eassumption.
assumption.
omega.
assumption.
unfold_ident_in_all; rewrite H21; simpl; omega.
unfold_ident_in_all; rewrite H21; simpl; omega.

(* 4: destr field nil *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn0 :: nil)))
).
 injection e; intros; subst.
 sdestruct (
pointer_eq_dec (A:=A)
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn0 :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b :: nil)))
 ).
  discriminate.
 unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 cut (
   (assoc (pointer_eq_dec (A:=A)) (obj0, (ar0, i0, (Class.Inheritance.Shared, b :: nil)))
     cs) = (Some Constructed)).
 intros.
 unfold_ident_in_all. 
 rewrite H5.
 fin.
eapply construction_states_virtual_bases.
eassumption.
eassumption.
assumption.
tauto.
assumption.
unfold_ident_in_all; rewrite H8; simpl; omega.
unfold_ident_in_all; rewrite H8; simpl; omega.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b :: nil)))
).
 2 : eauto.
injection e; intros; subst.
unfold state_kind_inv in kind.
simpl in kind; invall; subst.
destruct stk; try contradiction.
destruct t; simpl in H14; try contradiction.
 generalize (stack _ (or_introl _ (refl_equal _))).
 simpl.
 destruct inhpath.
 destruct k; intro; invall; subst; try contradiction.
 destruct kind; invall; subst.
  destruct l.
   discriminate.
  destruct l; discriminate.
 injection H28; intros; subst.
 inversion H18; subst.
 inversion H29; subst.
 replace o0 with o in * by abstract congruence.
 generalize (valid_array_path_last H7 H3).
 intro; subst.
 inversion H25; subst.
 injection H27; intros; subst.
 unfold_ident_in_all.
 rewrite H5.
 fin.
invall; discriminate.

(* 3: destr *)
unfold state_kind_inv in kind.
simpl in kind.
destruct beta; intros; invall; subst. 
 sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b0 :: nil)))
 ).
  destruct p.
   discriminate.
  destruct p0; discriminate.
 sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn :: nil)))
 ).
  destruct p.
   discriminate.
  destruct p0; discriminate.
 eauto.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn :: nil)))
).
 discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b0 :: nil)))
).
 2 : eauto.
 injection e; intros; subst.
inversion H10; subst.
inversion H24; subst.
replace o0 with o in * by abstract congruence.
generalize (valid_array_path_last H6 H0).
intro; subst.
inversion H22; subst.
injection H23; intros; subst.
unfold_ident_in_all.
rewrite H9.
fin.

(* 2: destr base direct non virtual nil Kdestrother base *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, hp))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn :: nil)))
).
 injection e; intros; subst.
 sdestruct (
pointer_eq_dec (A:=A)
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b0 :: nil)))
 ).
  discriminate.
 forward.
 revert kind.
 unfold state_kind_inv; simpl.
 intro; invall; subst.
 destruct hp'.
 destruct beta; invall; try discriminate.
 generalize (stack _ (or_introl _ (refl_equal _))).
 simpl.
 intros; invall.
 destruct l.
  discriminate.
 destruct l; discriminate.
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, hp))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b0 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
revert kind.
unfold state_kind_inv; simpl.
intros; invall; subst.
destruct hp'.
generalize (stack _ (or_introl _ (refl_equal _))).
simpl.
destruct beta; intros; invall; subst.
 destruct l.
  discriminate.
 destruct l; discriminate.
injection H27; intros; subst.
inversion H16; subst.
inversion H26; subst.
replace o0 with o in * by abstract congruence.
generalize (valid_array_path_last H4 H0).
intro; subst.
inversion H21; subst.
injection H24; intros; subst.
unfold_ident_in_all.
rewrite H2.
fin.

(* 1: destr base virtual nil *)
unfold state_kind_inv in kind. 
simpl in kind.
invall; subst.
intros.
sdestruct (pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, x1 :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b :: nil)))
).
 discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, x1 :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn0 :: nil)))
).
 2: eauto.
injection e; intros; subst.
forward.
eapply H7.
rewrite <- app_nil_end in H6.
eapply in_rev_elim.
eapply virtual_base_vborder_list.
eassumption.
eassumption.
assumption.

Qed.

End Preservation.


 
 

