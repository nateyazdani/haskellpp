Load PreservationHeader.

Ltac forward := constructor; simpl; intros; try discriminate; try omegaContradiction.
Ltac fin := forward; reflexivity.

Lemma nodup : forall cn c, hier ! cn = Some c ->
        forall l0 b1 l1 l2, Class.fields c = (l0 ++ b1 :: l1 ++ b1 :: l2) -> False.
Proof.
  intros.
  eapply NoDup_elim.
  eapply Well_formed_hierarchy.fields_no_dup.
  eassumption.
  eassumption.
  eassumption.
Qed.

Lemma goal : forall obj ar i h p hp,
    valid_pointer hier (Globals.heap (State.global s2)) (Value.subobject obj ar i h p hp) ->
    forall cn, last p = Some cn ->
      forall c, hier ! cn = Some c ->
        forall l0 b1 l1 b2 l2, Class.fields c = (l0 ++ b1 :: l1 ++ b2 :: l2) ->
          constructed_sibling_before (assoc aux_constr_state_key_eq_dec (obj, ar, i, (h, p), b1) (State.field_construction_states s2)) (assoc aux_constr_state_key_eq_dec (obj, ar, i, (h, p), b2) (State.field_construction_states s2))
        .
Proof.
 inversion Hs1.
 Opaque Zminus. inversion step; subst; simpl in *; unfold Globals.update in *; simpl in *; subst; try assumption.

(* 8: Sblock Some *)
intros until 1.
symmetry in H1.
unfold Globals.new in H1.
injection H1; intros until 2; subst; simpl in *.
inversion H2; subst; simpl in *.
destruct (peq (obj0) (Globals.next_object gl)).
 rewrite e in H5.
rewrite PTree.gss in H5.
injection H5; intros; subst; simpl in *.
rewrite (construction_states_fields_none _ (Globals.valid_none valid_global (Ple_refl _))).
rewrite (construction_states_fields_none _ (Globals.valid_none valid_global (Ple_refl _))).
fin.
rewrite PTree.gso in H5.
 2 : assumption.
assert (valid_pointer (Program.hierarchy prog) (Globals.heap gl) (Value.subobject ( obj0) ar i h p hp0)).
 econstructor; eauto.
eauto.

(* 7: constr field cons struct *)
destruct hp.
simpl.
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (t, l), fs)
           (obj0, ar0, i0, (h, p), b1)
).
 injection e; intros; subst.
 cut (
constructed_sibling_before (Some StartedConstructing)
     (if aux_constr_state_key_eq_dec (obj0, ar0, i0, (h, p), b1)
           (obj0, ar0, i0, (h, p), b2)
      then Some StartedConstructing
      else
       assoc aux_constr_state_key_eq_dec (obj0, ar0, i0, (h, p), b2)
         auxcs)
 ); eauto.
 sdestruct (
 aux_constr_state_key_eq_dec (obj0, ar0, i0, (h, p), b1)
           (obj0, ar0, i0, (h, p), b2)
 ).
  injection e0; intros; subst.
  apply False_rect.
  eauto using nodup.
 forward.
 unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 generalize (H14 _ (or_introl _ (refl_equal _))).
 simpl.
 unfold_ident.
 intro.
 eapply constructed_sibling_before_none.
 eauto.
 unfold_ident.
 rewrite H5.
 simpl; omega.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (t, l), fs)
           (obj0, ar0, i0, (h, p), b2)
).
 2 : eauto.
injection e; intros; subst.
cut (
 (assoc aux_constr_state_key_eq_dec (obj0, ar0, i0, (h, p), b1)
        auxcs) = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H4.
 forward.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
apply H10.
replace x2 with c in * by abstract congruence.
rewrite H9 in H3.
generalize (Well_formed_hierarchy.fields_no_dup hierarchy_wf H8).
rewrite H9.
intro.
assert (x3 ++ b2 :: q = (l0 ++ b1 :: l1) ++ b2 :: l2).
 rewrite H3.
 rewrite app_ass.
 reflexivity.
generalize (NoDup_uniq H4 H12).
injection 1; intros; subst.
eauto using in_or_app.

(* 6: constr field cons scalar no init *)
simpl.
unfold_ident.
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
           (obj0, ar0, i0, (h0, p0), b1)
).
 forward.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
           (obj0, ar0, i0, (h0, p0), b2)
).
 2 : eauto.
injection e; intros; subst.
cut (
 (assoc (aux_constr_state_key_eq_dec)
        (obj0, ar0, i0, (h0, p0), b1) auxcs) = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H5.
 forward.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
apply H11.
unfold_ident_in_all.
replace x2 with c in * by abstract congruence.
generalize (Well_formed_hierarchy.fields_no_dup hierarchy_wf H9). 
revert H4.
rewrite H10.
replace (l0 ++ b1 :: l1 ++ b2 :: l2) with ((l0 ++ b1 :: l1) ++ b2 :: l2).
intros.
generalize (NoDup_uniq H5 H4).
injection 1; intros; subst.
eauto using in_or_app.
rewrite app_ass; reflexivity.

(* 5: Sinitscalar *)
intros until 1.
assert (
valid_pointer (Program.hierarchy prog)
         (Globals.heap gl) (Value.subobject obj0 ar0 i0 h0 p0 hp)
).
 assumption.
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
           (obj0, ar0, i0, (h0, p0), b1)
).
 forward.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
           (obj0, ar0, i0, (h0, p0), b2)
).
 2 : eauto.
injection e; intros; subst.
cut (
(assoc (aux_constr_state_key_eq_dec)
        (obj0, ar0, i0, (h0, p0), b1) auxcs)  = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H9.
 forward.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
apply H14.
unfold_ident_in_all.
replace x2 with c in * by abstract congruence.
generalize (Well_formed_hierarchy.fields_no_dup hierarchy_wf H13). 
revert H8.
rewrite H15.
replace (l0 ++ b1 :: l1 ++ b2 :: l2) with ((l0 ++ b1 :: l1) ++ b2 :: l2).
intros.
generalize (NoDup_uniq H9 H8).
injection 1; intros; subst.
eauto using in_or_app.
rewrite app_ass; reflexivity.

(* 4: constr array n Kconstrother field *)
simpl.
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj', ar', i', (h, p), fs)
           (obj0, ar0, i, (h0, p0), b1)
).
 forward.
sdestruct (
aux_constr_state_key_eq_dec (obj', ar', i', (h, p), fs)
           (obj0, ar0, i, (h0, p0), b2)
).
 2 : eauto.
injection e; intros; subst.
cut (
(assoc (aux_constr_state_key_eq_dec )
        (obj0, ar0, i, (h0, p0), b1) auxcs) = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H3.
 forward.
generalize (stack _ (or_introl _ (refl_equal _))).
simpl.
intros; invall; subst.
eapply constructed_sibling_before_constructed.
eauto.
unfold_ident_in_all; rewrite H10; simpl; omega.
unfold_ident_in_all; rewrite H10; simpl; omega.

(* Destruction *)

(* 3: destr field scalar cons *)
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
           (obj0, ar0, i0, (h0, p0), b1)
).
 injection e; intros; subst.
 sdestruct (
aux_constr_state_key_eq_dec (obj0, ar0, i0, (h0, p0), b1)
           (obj0, ar0, i0, (h0, p0), b2)
 ).
  injection e0; intros; subst.
  apply False_rect.
  eauto using nodup.
 forward.
 unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 apply H11.
 unfold_ident_in_all.
 replace x2 with c in * by abstract congruence.
 generalize (Well_formed_hierarchy.fields_no_dup hierarchy_wf H9). 
 revert H3.
 rewrite <- (rev_involutive (Class.fields c)).
 rewrite H10.
 rewrite rev_app.
 simpl.
 rewrite app_ass.
 simpl.
 intros.
 generalize (NoDup_uniq H5 H3).
 injection 1; intros; subst.
 apply in_rev_elim.
 rewrite H15.
 eauto using in_or_app.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
           (obj0, ar0, i0, (h0, p0), b2)
 ).
 2 : eauto.
injection e; intros; subst.
cut (
 (assoc (aux_constr_state_key_eq_dec)
        (obj0, ar0, i0, (h0, p0), b1) auxcs)  = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H4.
 forward.
unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 apply H13.
 right.
 unfold_ident_in_all.
 replace x2 with c in * by abstract congruence.
 generalize (Well_formed_hierarchy.fields_no_dup hierarchy_wf H8). 
 revert H3.
 replace (l0 ++ b1 :: l1 ++ b2 :: l2) with ((l0 ++ b1 :: l1) ++ b2 :: l2).
 rewrite <- (rev_involutive (Class.fields c)).
 rewrite H9.
 rewrite rev_app.
 simpl.
 rewrite app_ass.
 simpl.
 intros.
 generalize (NoDup_uniq H4 H3).
 injection 1; intros; subst.
 apply in_rev_elim.
 rewrite H15.
 eauto using in_or_app.
 rewrite app_ass; reflexivity.

(* 2: destr field struct cons *)
unfold_ident.
simpl.
intros.
sdestruct (aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
           (obj0, ar0, i0, (h0, p0), b1)
).
 sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
           (obj0, ar0, i0, (h0, p0), b2)
 ).
  injection e; intros; subst.
  injection e0; intros; subst.
  apply False_rect.
  eauto using nodup.
 injection e; intros; subst.
 forward.
 unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 apply H11.
 unfold_ident_in_all.
 replace x2 with c in * by abstract congruence.
 generalize (Well_formed_hierarchy.fields_no_dup hierarchy_wf H9). 
 revert H3.
 rewrite <- (rev_involutive (Class.fields c)).
 rewrite H10.
 rewrite rev_app.
 simpl.
 rewrite app_ass.
 simpl.
 intros.
 generalize (NoDup_uniq H5 H3).
 injection 1; intros; subst.
 apply in_rev_elim.
 rewrite H15.
 eauto using in_or_app.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
           (obj0, ar0, i0, (h0, p0), b2)
 ).
 2 : eauto.
injection e; intros; subst.
cut (
 (assoc (aux_constr_state_key_eq_dec)
        (obj0, ar0, i0, (h0, p0), b1) auxcs)  = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H4.
 forward.
unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 apply H13.
 right.
 unfold_ident_in_all.
 replace x2 with c in * by abstract congruence.
 generalize (Well_formed_hierarchy.fields_no_dup hierarchy_wf H8). 
 revert H3.
 replace (l0 ++ b1 :: l1 ++ b2 :: l2) with ((l0 ++ b1 :: l1) ++ b2 :: l2).
 rewrite <- (rev_involutive (Class.fields c)).
 rewrite H9.
 rewrite rev_app.
 simpl.
 rewrite app_ass.
 simpl.
 intros.
 generalize (NoDup_uniq H4 H3).
 injection 1; intros; subst.
 apply in_rev_elim.
 rewrite H15.
 eauto using in_or_app.
 rewrite app_ass; reflexivity.

(* 1: destr array nil Kdestrother field *)
destruct hp'.
simpl.
intros.
sdestruct ( 
aux_constr_state_key_eq_dec (obj', ar', i', (t, l0), fs)
           (obj0, ar0, i, (h, p), b1)
).
 sdestruct (
 aux_constr_state_key_eq_dec (obj', ar', i', (t, l0), fs)
           (obj0, ar0, i, (h, p), b2)
 ).
  injection e; intros; subst.
  injection e0; intros; subst.
  apply False_rect.
  eauto using nodup.
 injection e; intros; subst.
 forward.
generalize (stack _ (or_introl _ (refl_equal _))).
simpl.
intros; invall; subst.
eapply constructed_sibling_before_destructed.
eauto.
unfold_ident_in_all.
rewrite H11.
simpl; omega.
sdestruct (
aux_constr_state_key_eq_dec (obj', ar', i', (t, l0), fs)
           (obj0, ar0, i, (h, p), b2)
 ).
 2 : eauto.
injection e; intros; subst.
cut (
 (assoc (aux_constr_state_key_eq_dec )
        (obj0, ar0, i, (h, p), b1) auxcs)  = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H3.
 forward.
generalize (stack _ (or_introl _ (refl_equal _))).
simpl.
intros; invall; subst.
eapply constructed_sibling_before_constructed.
eauto.
unfold_ident_in_all; rewrite H10; simpl; omega.
unfold_ident_in_all; rewrite H10; simpl; omega.

Qed.

End Preservation.


 
 

