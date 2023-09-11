Load PreservationHeader.

Ltac forward := constructor; simpl; intros; try discriminate; try omegaContradiction.
Ltac fin := forward; reflexivity.

Lemma goal : forall obj ar i h p hp,
    valid_pointer hier (Globals.heap (State.global s2)) (Value.subobject obj ar i h p hp) ->
    forall cn, last p = Some cn ->
      forall c, hier ! cn = Some c ->
        forall fs, In fs (Class.fields c) ->
          forall b n, FieldSignature.type fs = FieldSignature.Struct b n ->
            forall j, 0 <= j < Zpos n ->
              constructed_field_array_cell (assoc aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs) (State.field_construction_states s2)) (assoc (@pointer_eq_dec _) (obj, ((ar ++ (i, (h, p), fs) :: nil), j, (Class.Inheritance.Repeated, b :: nil))) (State.construction_states s2)).
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
           (obj0,
           (ar0 ++ (i0, (h, p), fs) :: nil, j,
           (Class.Inheritance.Repeated, b :: nil)))
).
2: eauto.
injection e; intros; subst.
destruct (stack2 _ nil _ (refl_equal _)).
generalize (H11 (fun x => x)).
destruct stk.
 intro; contradiction.
destruct 1.
destruct t; simpl in H12; try contradiction.
 destruct c1; try contradiction.
 invall.
 destruct ar0; simpl in H14; discriminate.
destruct inhpath.
destruct k; try contradiction.
destruct kind0; invall; subst.
destruct (list_cons_right_inj H18).
injection H14; intros; subst.
generalize (stack _ (or_intror _ (or_introl _ (refl_equal _)))).
simpl.
intros; invall; subst.
unfold_ident_in_all.
rewrite H26.
forward.

(* 16: Sreturn Kconstrothercells *)
intros.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0,
           (ar0 ++ (i0, (h, p), fs) :: nil, j,
           (Class.Inheritance.Repeated, b :: nil)))
).
 2 : eauto.
injection e; intros; subst.
destruct (stack2 _ nil _ (refl_equal _)).
generalize (H6 (fun x => x)).
destruct stk.
 intro; contradiction.
destruct 1.
destruct t; simpl in H7; try contradiction.
 destruct c0; try contradiction.
 invall.
 destruct ar0; simpl in H9; discriminate.
destruct inhpath.
destruct k; try contradiction.
destruct kind0; invall; subst.
generalize (stack _ (or_intror _ (or_introl _ (refl_equal _)))).
simpl; intro; invall; subst.
destruct (list_cons_right_inj H13).
injection H18; intros; subst.
unfold_ident_in_all.
rewrite H20.
forward.

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
cut (
 (assoc (pointer_eq_dec (A:=A))
        (obj0,
        (ar0 ++ (i0, (h, p), fs0) :: nil, j,
        (Class.Inheritance.Repeated, b0 :: nil))) cs)
= None ).
 intro.
 unfold_ident_in_all.
 rewrite H6.
 forward.
eapply construction_states_structure_fields.
4 : eassumption.
3 : eassumption.
eassumption.
assumption.
eassumption.
assumption.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
eauto.

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
           end)))
           (obj0,
           (ar0 ++ (i0, (h0, p0), fs) :: nil, j,
           (Class.Inheritance.Repeated, b0 :: nil)))
 ).
 2 : eauto.
destruct k2; try discriminate.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
destruct p.
 discriminate.
destruct p1; discriminate.

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
           end)))
           (obj0,
           (ar0 ++ (i0, (h0, p0), fs) :: nil, j,
           (Class.Inheritance.Repeated, b0 :: nil)))
).
 2 : eauto.
destruct k2; try discriminate. 
generalize (stack _ (or_introl _ (refl_equal _))).
simpl.
intro; invall; subst.
destruct p.
 discriminate.
destruct p; discriminate.

(* 12: constr base direct non virtual nil *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0,
           (ar0 ++ (i0, (h0, p0), fs) :: nil, j,
           (Class.Inheritance.Repeated, b :: nil)))
).
 2 : eauto.
injection e; intros; subst.
 unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
destruct stk; try contradiction.
destruct t; simpl in H14; try contradiction.
 destruct inhpath.
 destruct k; try contradiction.
 destruct kind; try discriminate.
 invall; subst.
 generalize (stack _ (or_introl _ (refl_equal _))).
 simpl.
 intros; invall.
 destruct l.
  discriminate.
 destruct l; discriminate.
invall; discriminate.
invall; subst.
destruct (stack2 _ nil _ (refl_equal _)).
generalize (H7 (fun x => x)).
destruct stk.
 intro; contradiction.
simpl.
destruct 1.
 destruct t0; simpl in H14; try contradiction.
  destruct c1; try contradiction.
  destruct H14.
   destruct ar0; simpl in H14; discriminate.
  destruct inhpath.
  destruct k; try contradiction.
destruct kind; invall; subst.
destruct (list_cons_right_inj H26).
injection H22; intros; subst.
generalize (stack _ (or_intror _ (or_introl _ (refl_equal _)))).
simpl.
intros; invall; subst.
unfold_ident_in_all.
rewrite H33.
forward.

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
abstract congruence.

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
abstract congruence.

(* 9: constr array n Kconstrother field *)
simpl.
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj', ar', i', (h, p), fs)
           (obj0, ar0, i, (h0, p0), fs0)
).
 2 : eauto.
injection e; intros; subst.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
rewrite last_complete in H8.
invall; subst.
replace x3 with n0 in * by abstract congruence.
replace b0 with b in * by abstract congruence.
generalize (H10 _ (conj H6 H18)). 
cut (
assoc (pointer_eq_dec (A:=A))
     (obj0,
     (ar0 ++ (i, (h0, p0), fs0) :: nil, j,
     (Class.Inheritance.Repeated, b :: nil))) cs = 
   Some Constructed ->
   constructed_field_array_cell (Some Constructed)
     (assoc (pointer_eq_dec (A:=A))
        (obj0,
        (ar0 ++ (i, (h0, p0), fs0) :: nil, j,
        (Class.Inheritance.Repeated, b :: nil))) cs)
).
 intro; assumption.
intro.
rewrite H4.
forward.
trivial.

(* Destruction *)

(* 8: destr array cons *)
intros.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0,
           (ar0 ++ (i, (h, p), fs) :: nil, j0,
           (Class.Inheritance.Repeated, b :: nil)))
).
 2 : eauto.
injection e; intros; subst.
unfold state_kind_inv in kind.
simpl in kind.
intros; invall; subst.
destruct stk; try contradiction.
destruct t; simpl in H11; try contradiction.
 destruct c1; try contradiction.
 destruct H11.
  destruct ar0; simpl in H9; discriminate.
destruct inhpath.
destruct k; try contradiction.
destruct kind; invall; subst.
destruct (list_cons_right_inj H23).
injection H11; intros; subst.
generalize (stack _ (or_introl _ (refl_equal _))).
simpl.
intros; invall; subst.
unfold_ident_in_all.
rewrite H30.
forward.

(* 7: destr field scalar cons *)
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
           (obj0, ar0, i0, (h0, p0), fs0)
).
 2 : eauto.
abstract congruence.

(* 6: destr field struct cons *)
unfold_ident.
simpl.
intros.
sdestruct ( aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
           (obj0, ar0, i0, (h0, p0), fs0)
).
 2 : eauto.
injection e; intros; subst.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
unfold_ident_in_all.
cut (
(assoc (pointer_eq_dec (A:=A))
        (obj0,
        (ar0 ++ (i0, (h0, p0), fs0) :: nil, j,
        (Class.Inheritance.Repeated, b0 :: nil))) cs) = Some Constructed
).
 unfold_ident_in_all.
 intro.
 rewrite H5.
 forward.
eapply construction_states_structure_fields.
eauto.
3 : eassumption.
2 : eassumption.
assumption.
eassumption.
tauto.
eapply H15.
auto.

(* 5: destr array nil Kdestrother field *)
destruct hp'.
simpl.
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj', ar', i', (t, l0), fs)
           (obj0, ar0, i, (h, p), fs0)
).
 2 : eauto.
injection e; intros; subst.
forward.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
rewrite last_complete in H9.
invall; subst.
replace cn with b in * by abstract congruence.
replace x4 with n in * by abstract congruence.
assert (-1 < j < Zpos n) by abstract omega.
eauto.

(* 4: destr field nil *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0,
           (ar0 ++ (i0, (h0, p0), fs) :: nil, j,
           (Class.Inheritance.Repeated, b :: nil)))
).
 2 : eauto.
injection e; intros; subst.
 unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 destruct stk; try contradiction.
 destruct t; simpl in H15; try contradiction.
  destruct inhpath.
  destruct k; try contradiction.
  destruct kind; invall; subst; try discriminate.
  generalize (stack _ (or_introl _ (refl_equal _))).
  simpl.
  intros; invall; subst.
  destruct l.
   discriminate.
  destruct l; discriminate.
 invall; subst. 
 destruct (stack2 _ nil _ (refl_equal _)).
 generalize (H8 (fun x => x)).
 destruct stk.
  intro; contradiction.
 destruct 1.
 destruct t0; simpl in H15; try contradiction.
  destruct c1; try contradiction.
  destruct H15; destruct ar0; discriminate.
 destruct inhpath.
 destruct k; try contradiction.
 destruct kind; invall; subst.
 destruct (list_cons_right_inj H26).
 injection H22; intros; subst.
 generalize (stack _ (or_intror _ (or_introl _ (refl_equal _)))).
 simpl.
 intros; invall; subst.
 unfold_ident_in_all.
 rewrite H33.
 forward.

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
           end)))
           (obj0,
           (ar0 ++ (i0, (h0, p0), fs) :: nil, j,
           (Class.Inheritance.Repeated, b0 :: nil)))
).
 2 : eauto.
destruct beta; try discriminate.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
destruct p.
 discriminate.
destruct p1; discriminate.

(* 2: destr base direct non virtual nil Kdestrother base *)
intros.
destruct hp.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (t, l)))
           (obj0,
           (ar0 ++ (i0, (h, p), fs) :: nil, j,
           (Class.Inheritance.Repeated, b0 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
destruct hp'.
destruct beta; invall; subst; try discriminate.
generalize (stack _ (or_introl _ (refl_equal _))).
simpl.
intros; invall; subst.
destruct l.
 discriminate.
destruct l; discriminate.

(* 1: destr base virtual nil *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0,
           (ar0 ++ (i0, (h0, p0), fs) :: nil, j,
           (Class.Inheritance.Repeated, b :: nil)))
).
 2 : eauto.
injection e; intros; subst.
unfold state_kind_inv in kind. 
simpl in kind.
invall; subst.
destruct stk; try contradiction.
destruct t; simpl in H14; try contradiction.
 destruct c0; try contradiction.
 destruct H14; destruct ar0; discriminate.
destruct inhpath.
destruct k; try contradiction.
destruct kind; invall; subst.
destruct (list_cons_right_inj H22).
injection H14; intros; subst.
generalize (stack _ (or_introl _ (refl_equal _))).
simpl.
intros; invall; subst.
unfold_ident_in_all.
rewrite H29.
forward.

Qed.

End Preservation.


 
 

