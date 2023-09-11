Load PreservationHeader.

Ltac forward := constructor; simpl; intros; try discriminate; try omegaContradiction.
Ltac fin := forward; reflexivity.


Lemma goal : forall obj ar i h p hp,
    valid_pointer hier (Globals.heap (State.global s2)) (Value.subobject obj ar i h p hp) ->
    forall cn, last p = Some cn ->
      forall c, hier ! cn = Some c ->
      forall fs, In fs (Class.fields c) ->
        constructed_field_child_of (assoc aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs) (State.field_construction_states s2)) (assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states s2))
        .
Proof.
 inversion Hs1.
 Opaque Zminus. inversion step; subst; simpl in *; unfold Globals.update in *; simpl in *; subst; try assumption.

(* 18: Sblock Some *)
intros until 1.
symmetry in H1.
unfold Globals.new in H1.
injection H1; intros until 2; subst; simpl in *.
inversion H2; subst; simpl in *.
destruct (peq (obj0) (Globals.next_object gl)).
 rewrite e in H5.
rewrite PTree.gss in H5.
injection H5; intros; subst; simpl in *.
rewrite (construction_states_none _ (Globals.valid_none valid_global (Ple_refl _))).
rewrite (construction_states_fields_none _ (Globals.valid_none valid_global (Ple_refl _))).
fin.
rewrite PTree.gso in H5.
 2 : assumption.
assert (valid_pointer (Program.hierarchy prog) (Globals.heap gl) (Value.subobject ( obj0) ar i h p hp0)).
 econstructor; eauto.
eauto.

(* 17: Sconstructor Kconstrarray *)
intros. 
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (h, p)))
).
2: eauto.
injection e; intros; subst.
revert kind.
unfold state_kind_inv; simpl.
intros; invall; subst.
assert (i0 <= i0 < n) by abstract omega.
generalize (H14 _ H11).
intro.
injection H3; intros; subst.
forward.
eapply (construction_states_fields). 
4 : eassumption.
eassumption.
eassumption.
eassumption.
unfold_ident_in_all.
rewrite H16.
simpl; omega.

(* 16: Sreturn Kconstrothercells *)
intros.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (h, p)))
).
 2 : eauto.
injection e; intros; subst.
revert kind.
unfold state_kind_inv; simpl.
intro; invall; subst.
injection H0; intros; subst.
forward.
eapply H6.
congruence.

(* 15: constr field cons struct *)
destruct hp.
simpl.
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (t, l), fs)
           (obj0, ar0, i0, (h, p), fs0)
).
 2 : eauto.
injection e; intros; subst.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
unfold_ident_in_all.
rewrite H5.
forward.
auto.

(* 14: Sconstructor Kconstr base *)
intros.
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
           end))) (obj0, (ar0, i0, (h0, p0)))
 ).
 2 : eauto.
unfold state_kind_inv in kind.
simpl in kind.
destruct k2; injection e; intros; invall; subst.
 forward.
 eapply construction_states_fields.
 eassumption.
 3 : eassumption.
 eassumption.
 assumption.
 unfold_ident_in_all.
 rewrite (H19 _ (or_introl _ (refl_equal _))).
 simpl; omega.
forward.
eapply construction_states_fields.
eassumption.
3 : eassumption.
eassumption.
assumption.
unfold_ident_in_all.
rewrite (H21 _ (or_introl _ (refl_equal _))).
simpl; omega.

(* 13: Sreturn Kconstrother base *)
intros.
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
           end))) (obj0, (ar0, i0, (h0, p0)))
).
 2 : eauto.
 unfold state_kind_inv in kind.
 simpl in kind.
destruct k2; injection e; intros; invall; subst.
 forward.
 rewrite last_complete in H0.
 apply H11.
 congruence.
simpl in H0.
forward.
apply H11.
congruence.

(* 12: constr base direct non virtual nil *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (h0, p0)))
).
 2 : eauto.
injection e; intros; subst.
 unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
forward.
left.
eapply construction_states_fields.
eassumption.
3 : eassumption.
2 : eassumption.
assumption.
unfold_ident_in_all; rewrite H6; simpl; omega.

(* 11: constr field scalar no init *)
simpl.
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
           (obj0, ar0, i0, (h0, p0), fs0)
); eauto.
injection e; intros; subst.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
unfold_ident_in_all.
rewrite H6.
forward.
auto.

(* 10: Sinitscalar *)
intros until 1.
assert (
valid_pointer (Program.hierarchy prog)
         (Globals.heap gl) (Value.subobject obj0 ar0 i0 h0 p0 hp)
).
 assumption.
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
           (obj0, ar0, i0, (h0, p0), fs0)
).
 2 : eauto.
injection e; intros; subst.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
unfold_ident_in_all.
rewrite H10.
forward.
auto.

(* 9: constr array n Kconstrother field *)
simpl.
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj', ar', i', (h, p), fs)
           (obj0, ar0, i, (h0, p0), fs0)
).
 2 : eauto.
injection e; intros; subst.
generalize (stack _ (or_introl _ (refl_equal _))).
simpl.
intros; invall; subst.
unfold_ident_in_all.
rewrite H3.
forward.
auto.

(* Destruction *)

(* 8: destr array cons *)
intros.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i, (h, p)))
).
 2 : eauto.
injection e; intros; subst.
unfold state_kind_inv in kind.
simpl in kind.
intros; invall; subst.
assert (0 <= i <= i) by omega.
generalize (H13 _ H12).
intro.
forward.
left.
eapply constructed_field_child_of_constructed.
eauto.
assumption.

(* 7: destr field scalar cons *)
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
           (obj0, ar0, i0, (h0, p0), fs0)
).
 2 : eauto.
injection e; intros; subst.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
unfold_ident_in_all.
rewrite H5.
forward.
auto.

(* 6: destr field struct cons *)
unfold_ident.
simpl.
intros.
sdestruct (aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
           (obj0, ar0, i0, (h0, p0), fs0)
).
 2 : eauto.
injection e; intros; subst.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
unfold_ident_in_all.
rewrite H5.
forward.
auto.

(* 5: destr array nil Kconstrother field *)
destruct hp'.
simpl.
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj', ar', i', (t, l0), fs)
           (obj0, ar0, i, (h, p), fs0)
).
 2 : eauto.
injection e; intros; subst.
generalize (stack _ (or_introl _ (refl_equal _))).
simpl.
intros; invall; subst.
unfold_ident_in_all.
rewrite H3.
forward.
auto.

(* 4: destr field nil *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (h0, p0)))
).
 2 : eauto.
injection e; intros; subst.
 unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 rewrite <- app_nil_end in H11.
 subst.
 forward.
 apply H12.
 apply in_rev_intro.
 congruence.

(* 3: destr base cons *)
intros.
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
           end))) (obj0, (ar0, i0, (h0, p0)))
).
 2 : eauto.
forward.
left.
unfold state_kind_inv in kind.
simpl in kind.
destruct beta; injection e; intros; invall; subst; eauto using constructed_field_child_of_constructed.

(* 2: destr base direct non virtual nil Kdestrother base *)
intros.
destruct hp.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (t, l)))
           (obj0, (ar0, i0, (h, p)))
).
 2 : eauto.
injection e; intros; subst.
forward.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
eapply constructed_field_child_of_destructed.
eauto.
unfold_ident_in_all.
rewrite H5.
simpl; omega.

(* 1: destr base virtual nil *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (h0, p0)))
).
 2 : eauto.
injection e; intros; subst.
unfold state_kind_inv in kind. 
simpl in kind.
invall; subst.
forward.
eapply constructed_field_child_of_destructed.
eauto.
unfold_ident_in_all.
rewrite H5.
simpl; omega.

Qed.

End Preservation.


 
 

