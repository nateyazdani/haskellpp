Load PreservationHeader.

Ltac forward := constructor; simpl; intros; try discriminate; try omegaContradiction.
Ltac fin := forward; reflexivity.


Lemma goal : forall obj ar i h p hp,
  valid_pointer hier (Globals.heap (State.global s2)) (Value.subobject obj ar i h p hp) ->
  forall cn, last p = Some cn ->
    forall c, hier ! cn = Some c ->
      forall b, In (Class.Inheritance.Repeated, b) (Class.super c) ->
        constructed_base_child_of (assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p ++ b :: nil))) (State.construction_states s2)) (assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states s2))
        .
Proof.
 inversion Hs1.
 inversion step; subst; simpl in *; unfold Globals.update in *; simpl in *; subst; try assumption.

(* 11: Sblock Some *)
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
rewrite (construction_states_none _ (Globals.valid_none valid_global (Ple_refl _))). 
fin.
rewrite PTree.gso in H5.
 2 : assumption.
assert (valid_pointer (Program.hierarchy prog) (Globals.heap gl) (Value.subobject (obj0) ar i h p hp0)).
 econstructor; eauto.
eauto.

(* 10: Sconstructor Kconstrarray *)
intros. 
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (h, p ++ b :: nil)))
).
 destruct p.
  discriminate.
 destruct p; discriminate.
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
generalize (construction_states_direct_non_virtual_bases _ _ _ _ _ _ H2 _ (refl_equal _) _ H4 _ H5).
simpl.
unfold_ident_in_all.
rewrite H16.
destruct 1.
rewrite (constructed_base_child_of_none (refl_equal _)).
fin.

(* 9: Sreturn Kconstrothercells *)
intros.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (h, p ++ b :: nil)))
).
 destruct p.
  discriminate.
 destruct p; discriminate.
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
generalize (construction_states_direct_non_virtual_bases _ _ _ _ _ _ H _ (refl_equal _) _ H1 _ H2).
simpl.
unfold_ident_in_all.
rewrite H3.
destruct 1.
rewrite (
  constructed_base_child_of_constructed
  (proj_sumbool_true (cs_le_dec (Some BasesConstructed) (Some BasesConstructed)) (refl_equal _))
  (proj_sumbool_true (cs_le_dec (Some BasesConstructed) (Some StartedDestructing)) (refl_equal _))
).
fin.

(* 8: Sconstructor Kconstr base *)
intros.
destruct k2.
 sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (h0, p0)))
 ).
  injection e; intros; subst.
  sdestruct (
    pointer_eq_dec (A:=A) (obj0, (ar0, i0, (h0, p ++ b :: nil)))
           (obj0, (ar0, i0, (h0, (p ++ b :: nil) ++ b0 :: nil)))
  ).
   fin.
  revert kind.
  unfold state_kind_inv.
  simpl.
  intro.
  invall; subst.
  generalize (H14 _ (or_introl _ (refl_equal _))).
  intro.
  destruct (construction_states_direct_non_virtual_bases _ _ _ _ _ _ H2 _ H3 _ H4 _ H5).
  unfold_ident_in_all.
  rewrite (constructed_base_child_of_none H6).
  fin.
 sdestruct (
   pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b0 :: nil)))
 ).
 2 : eauto.
 injection e; intros; subst.
 generalize (last_complete p b).
 unfold_ident_in_all; rewrite H6.
 rewrite last_complete.
 injection 1; intros; subst.
 generalize (app_reg_r H6).
 intro; subst.
 revert kind.
 unfold state_kind_inv; simpl.
 intro; invall; subst.
 unfold_ident_in_all.
 rewrite H10.
 fin.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b0 :: nil)))
).
 destruct p0.
  discriminate.
 destruct p0; discriminate.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (h0, p0)))
).
 2 : eauto.
forward.
injection e; intros; subst.
revert kind.
unfold state_kind_inv; simpl; intro; invall; subst; unfold_ident_in_all. 
generalize (H17 _ (or_introl _ (refl_equal _))).
intro.
destruct (construction_states_direct_non_virtual_bases _ _ _ _ _ _ H2 _ H3 _ H4 _ H5).
simpl in *.
rewrite (constructed_base_child_of_none H7).
simpl; omega.

(* 7: Sreturn Kconstrother base *)
intros.
destruct k2.
 sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (h0, p0)))
 ).
  injection e; intros; subst.
  sdestruct (
    pointer_eq_dec (A:=A) (obj0, (ar0, i0, (h0, p ++ b :: nil)))
           (obj0, (ar0, i0, (h0, (p ++ b :: nil) ++ b0 :: nil)))
  ).
   fin.
  revert kind.
  unfold state_kind_inv.
  simpl.
  intro.
  invall; subst.
  destruct (construction_states_direct_non_virtual_bases _ _ _ _ _ _ H _ H0 _ H1 _ H2).
  unfold_ident_in_all.
  rewrite H3 in *.
  rewrite (constructed_base_child_of_constructed 
    (proj_sumbool_true (cs_le_dec (Some BasesConstructed) (Some BasesConstructed)) (refl_equal _))
    (proj_sumbool_true (cs_le_dec (Some BasesConstructed) (Some StartedDestructing)) (refl_equal _))
  ).
  fin.
 sdestruct (
   pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b0 :: nil)))
 ).
 2 : eauto.
 injection e; intros; subst.
 generalize (last_complete p b).
 unfold_ident_in_all; rewrite H3.
 rewrite last_complete.
 injection 1; intros; subst.
 generalize (app_reg_r H3).
 intro; subst.
 generalize (stack _ (or_introl _ (refl_equal _))).
 simpl.
 intro; invall; subst.
 unfold_ident_in_all.
 rewrite H5.
 fin.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b0 :: nil)))
).
 destruct p0.
  discriminate.
 destruct p0; discriminate.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (h0, p0)))
).
 2 : eauto.
forward.
injection e; intros; subst.
revert kind.
unfold state_kind_inv; simpl; intro; invall; subst; unfold_ident_in_all. 
destruct (construction_states_direct_non_virtual_bases _ _ _ _ _ _ H _ H0 _ H1 _ H2).
rewrite H5 in *.
exact (constructed_base_child_of_constructed 
    (proj_sumbool_true (cs_le_dec (Some BasesConstructed) (Some BasesConstructed)) (refl_equal _))
    (proj_sumbool_true (cs_le_dec (Some BasesConstructed) (Some StartedDestructing)) (refl_equal _))
  ).

(* 6: constr base direct non virtual nil *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (h0, p0)))
).
 injection e; intros; subst.
 sdestruct (
    pointer_eq_dec (A:=A) (obj0, (ar0, i0, (h0, p0)))
           (obj0, (ar0, i0, (h0, p0 ++ b :: nil)))
 ).
  apply False_rect.
  injection e0.
  intro.
  generalize (refl_equal (length p0)).
  rewrite H5 at 1.
  rewrite app_length.
  simpl.
  unfold_ident_in_all.
  intro; omegaContradiction.
 forward.
 revert kind.
 unfold state_kind_inv; simpl.
 intro; invall; subst.
 intros.
 apply H13.
 rewrite <- app_nil_end in H12.
 subst.
 eapply in_map_bases_intro.
 congruence.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (h0, p0 ++ b :: nil)))
).
 2 : eauto.
injection e; intros; subst.
revert kind.
unfold state_kind_inv; simpl.
intros; invall; subst.
destruct stk; try contradiction.
destruct t; simpl in H12; try contradiction.
 generalize (stack _ (or_introl _ (refl_equal _))).
 simpl.
 destruct inhpath.
 destruct k; try contradiction.
  destruct kind; intros; invall; subst.
   generalize (last_complete p0 b).
   unfold_ident_in_all.
   rewrite H25.
   rewrite last_complete.
   injection 1; intros; subst.
   generalize (app_reg_r H25).
   intro; subst.
   rewrite H5.
   fin.
  destruct p0. 
   discriminate.
  destruct p0; discriminate.
 invall; subst. 
 destruct p0.
  discriminate.
 destruct p0; discriminate.

(* Destruction *)

(* 5: destr array cons *)
intros.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i, (h, p ++ b :: nil)))
).
 destruct p.
  discriminate.
 destruct p; discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i, (h, p)))
).
 2 : eauto.
injection e; intros; subst.
forward.
intros.
revert kind.
unfold state_kind_inv; simpl.
intros; invall; subst.
assert (0 <= i <= i) by omega.
generalize (H15 _ H14).
intro.
unfold_ident_in_all.
change (cn :: b :: nil) with ((cn :: nil) ++ b :: nil).
eapply construction_states_direct_non_virtual_bases.
eassumption.
3 : eassumption.
2 : eassumption.
assumption.
rewrite H19.
simpl; omega.
rewrite H19; simpl; omega.

(* 4: destr field nil *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (h0, p0)))
).
 injection e; intros; subst.
 sdestruct (
pointer_eq_dec (A:=A) (obj0, (ar0, i0, (h0, p0)))
           (obj0, (ar0, i0, (h0, p0 ++ b :: nil)))
 ).
  injection e0.
  intro.
  generalize (refl_equal (length p0)).
  rewrite H6 at 1.
  rewrite app_length.
  unfold_ident.
  simpl; intro; omegaContradiction.
 unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 cut (
   (assoc (pointer_eq_dec (A:=A)) (obj0, (ar0, i0, (h0, p0 ++ b :: nil)))
     cs) = (Some Constructed)).
 intros.
 unfold_ident_in_all. 
 rewrite H6.
 fin.
eapply construction_states_direct_non_virtual_bases.
eassumption.
3 : eassumption.
2 : eassumption.
assumption.
rewrite H7.
simpl; omega.
rewrite H7; simpl; omega.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (h0, p0 ++ b :: nil)))
).
 2 : eauto.
injection e; intros; subst.
unfold state_kind_inv in kind.
simpl in kind; invall; subst.
destruct stk; try contradiction.
destruct t; simpl in H13; try contradiction.
 generalize (stack _ (or_introl _ (refl_equal _))).
 simpl.
 destruct inhpath.
 destruct k; intro; invall; subst; try contradiction.
 destruct kind; invall; subst.
  generalize (last_complete p0 b). 
  unfold_ident_in_all.
  rewrite H24.
  rewrite last_complete.
  injection 1; intros; subst.
  generalize (app_reg_r H24).
  intro; subst.
  rewrite H6.
  fin.
 destruct p0.
  discriminate.
 destruct p0; discriminate.
invall; subst.
destruct p0.
 discriminate.
destruct p0; discriminate.

(* 3: destr *)
intros.
destruct beta.
 sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (h0, p0)))
 ).
  injection e; intros; subst.
  sdestruct (
    pointer_eq_dec (A:=A) (obj0, (ar0, i0, (h0, p ++ b :: nil)))
           (obj0, (ar0, i0, (h0, (p ++ b :: nil) ++ b0 :: nil)))
  ).
   injection e0.
   intro.
   generalize (refl_equal (length (p ++ b :: nil))).
   unfold_ident_in_all.
   rewrite H7 at 1.
   rewrite app_length at 1.
   simpl. intros. omegaContradiction.
  revert kind.
  unfold state_kind_inv.
  simpl.
  intro.
  invall; subst.
  generalize (H15 _ (or_introl _ (refl_equal _))).
  intro.
  forward.
  eapply constructed_base_child_of_constructed.
  eapply construction_states_direct_non_virtual_bases.
  4 : eassumption.
  eassumption.
  2 : eassumption.
  assumption.
  unfold_ident_in_all; rewrite H7; simpl; omega.
  unfold_ident_in_all; rewrite H7; simpl; omega.
 sdestruct (
   pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b0 :: nil)))
 ).
 2 : eauto.
 injection e; intros; subst.
 generalize (last_complete p b).
 unfold_ident_in_all; rewrite H7.
 rewrite last_complete.
 injection 1; intros; subst.
 generalize (app_reg_r H7).
 intro; subst.
 revert kind.
 unfold state_kind_inv; simpl.
 intro; invall; subst.
 unfold_ident_in_all.
 rewrite H10.
 fin.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b0 :: nil)))
).
 destruct p0.
  discriminate.
 destruct p0; discriminate.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (h0, p0)))
).
 2 : eauto.
forward.
injection e; intros; subst.
revert kind.
unfold state_kind_inv; simpl; intro; invall; subst; unfold_ident_in_all. 
generalize (H18 _ (or_introl _ (refl_equal _))).
intro.
change (b :: b0 :: nil) with ((b :: nil) ++ b0 :: nil).
eapply constructed_base_child_of_constructed.
eapply construction_states_direct_non_virtual_bases.
4 : eassumption.
3 : eassumption.
eassumption.
assumption.
unfold_ident_in_all; rewrite H9; simpl; omega.
unfold_ident_in_all; rewrite H9; simpl; omega.

(* 2: destr base direct non virtual nil Kdestrother base *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (hp)))
           (obj0, (ar0, i0, (h, p)))
).
 injection e; intros; subst.
 sdestruct (
    pointer_eq_dec (A:=A) (obj0, (ar0, i0, (h, p)))
           (obj0, (ar0, i0, (h, p ++ b0 :: nil)))
 ).
  apply False_rect.
  injection e0.
  intro.
  generalize (refl_equal (length p)).
  rewrite H3 at 1.
  rewrite app_length.
  simpl.
  unfold_ident_in_all.
  intro; omegaContradiction.
 forward.
 revert kind.
 unfold state_kind_inv; simpl.
 intro; invall; subst.
 intros.
 apply H10.
 rewrite <- app_nil_end in H9.
 subst.
 eapply in_rev_intro.
 eapply in_map_bases_intro.
 congruence.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (hp)))
           (obj0, (ar0, i0, (h, p ++ b0 :: nil)))
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
 unfold_ident_in_all.
 generalize (last_complete p b0).
 unfold_ident_in_all.
 rewrite H23.
 rewrite last_complete.
 injection 1; intros; subst.
 generalize (app_reg_r H23).
 intro; subst.
 rewrite H3.
 fin.
  destruct p. 
   discriminate.
  destruct p; discriminate.

(* 1: destr base virtual nil *)
unfold state_kind_inv in kind. 
simpl in kind.
invall; subst.
intros.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, x1 :: nil)))
           (obj0, (ar0, i0, (h, p ++ b :: nil)))
).
 destruct p.
  discriminate.
 destruct p; discriminate.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, x1 :: nil)))
           (obj0, (ar0, i0, (h, p)))
).
 2: eauto.
injection e; intros; subst.
forward.
eapply H11.
unfold_ident_in_all. congruence.

Qed.

End Preservation.


 
 

