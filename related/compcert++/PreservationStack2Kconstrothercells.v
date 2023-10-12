Load PreservationStack2Header.

Lemma goal : 
  forall t0 obj0 array array_count array_index cn init1 vars1, t0 = StackFrame.Kconstrothercells obj0 array array_count array_index cn init1 vars1 ->    

    forall (sf : StackFrame.t A nativeop)
      (l1 : list (StackFrame.t A nativeop))
      (l2 : list (StackFrame.t A nativeop)),
      State.stack s2 = l1 ++ sf :: t0 :: l2 ->
      is_code_frame sf ->
      stackframe_constructor_inv prog s2 t0
      .
Proof.
generalize stack2_2.
intro H.
intro sf2; intros until 1. 
revert H0.
intro Heq.
Opaque Zminus.
inversion step; try (clear Heq; subst; simpl in *; exact (H sf2)); try (clear Heq; subst; simpl in *; intros sf1 l1 l2 H'; exact (H _ _ _ _ (app_cons H' _))); subst; simpl in *; unfold Globals.update in *; simpl in *; subst.

(* 23: call *)
destruct l1.
 simpl; injection 1; intros; subst.
 generalize (kind Hs1).
 unfold state_kind_inv; simpl.
 unfold stackframe_constructor_inv. intro; assumption.
simpl; injection 1; intros until 2; subst.
generalize (H _ _ _ _ (refl_equal _)).
unfold stackframe_constructor_inv; intro; assumption.

(* 22: invoke *)
destruct l1.
 simpl; injection 1; intros; subst.
 generalize (kind Hs1).
 unfold state_kind_inv; simpl.
 unfold stackframe_constructor_inv. intro; assumption.
simpl; injection 1; intros until 2; subst.
generalize (H _ _ _ _ (refl_equal _)).
unfold stackframe_constructor_inv; intro; assumption.

(* 21: Sblock some *)
destruct l1.
 simpl; injection 1; intros; subst.
 exact (kind Hs1).
simpl; injection 1; intros; subst.
exact (H _ _ _ _ (refl_equal _) H6).

(* 20: constr_array < n *)
destruct (Z_eq_dec n i).
 abstract omegaContradiction.
destruct l1; simpl; injection 1; intros until 2; subst.
 simpl; tauto.
exact (H _ _ _ _ (refl_equal _)).

(* 19: Sconstructor Kconstrarray *)
destruct l1; simpl; injection 1; intros until 2; subst; simpl; try tauto.
intro.
generalize (H _ _ _ _ (app_cons (refl_equal _) _) H4).
simpl.
intros; invall; subst; split; eauto.
sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn0 :: nil)))
         (obj0,
         (array, array_index, (Class.Inheritance.Repeated, cn :: nil)))
); eauto.
injection e; intros; subst.
refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) _)).
2 : eapply in_or_app; right; right; left; reflexivity.
destruct 1.
destruct (H11 _ _ (refl_equal _) _ (refl_equal _)). 
invall.
destruct x0.
 abstract congruence.
generalize (refl_equal (length array)).
rewrite H13 at 1.
rewrite app_length.
simpl; intro; abstract omegaContradiction.

(* 18: Sreturn Kconstrothercells *)
intros.
generalize (H _ _ _ _ (app_cons H0 _) H1).
simpl.
subst.
intros; invall; subst; split; eauto.
sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn0 :: nil)))
         (obj0,
         (array, array_index, (Class.Inheritance.Repeated, cn :: nil)))
); eauto.
injection e; intros; subst.
refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) (in_or_app _ _ _ _))).
2 : right; right; left; reflexivity.
destruct 1.
destruct (H5 _ _ (refl_equal _) _ (refl_equal _)).
invall.
generalize (refl_equal (length array)).
rewrite H7 at 1.
rewrite app_length.
destruct x0.
 abstract congruence.
simpl; intro; abstract omegaContradiction.

(* 17: constr cons with initializer *)
intros.
destruct l1.
 (* new stack frame: Kconstr *)
 simpl in H2; injection H2; intros; subst.
 simpl in H3.
 contradiction.
(* other stack frames *)
simpl in H2.
injection H2; intros; subst.
generalize (H _ _ _ _ (refl_equal _) H3).
unfold stackframe_constructor_inv; intro; assumption.

(* 16: constr cons field struct *)
destruct l1; simpl.
 injection 1; intros until 2; subst; simpl; intro; contradiction.
injection 1; intros until 2; subst.
destruct hp.
simpl.
intro.
generalize (H _ _ _ _ (refl_equal _) H2).
simpl; intro; invall.
split; auto.
esplit; split; try eassumption.
intros.
sdestruct (
 aux_constr_state_key_eq_dec (obj, ar, i, (t, l), fs)
         (obj0, array, array_index, (Class.Inheritance.Repeated, cn :: nil),
         fs0)
); eauto.
injection e; intros; subst.
generalize (H6 _ H3).
generalize (kind Hs1).
unfold state_kind_inv; simpl.
intro; invall; subst.
generalize (H16 _ (or_introl _ (refl_equal _))).
unfold_ident_in_all; abstract congruence.

(* 15: Sconstructor Kconstr base *)
destruct l1; simpl; injection 1; intros; try (subst; simpl in *; contradiction).
generalize (H _ _ _ _ (app_cons H4 _) H6).
simpl; intro; invall; subst; split; eauto.
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
         (array, array_index, (Class.Inheritance.Repeated, cn :: nil)))
); eauto.
destruct k2; try discriminate.
generalize (kind Hs1).
unfold state_kind_inv; simpl.
intro; invall; subst.
destruct p.
 discriminate.
destruct p0; discriminate.

(* 14: Sreturn Kconstrother base *)
intros.
generalize (H _ _ _ _ (app_cons H0 _) H1).
simpl; intro; invall; subst; split; eauto.
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
         (array, array_index, (Class.Inheritance.Repeated, cn :: nil)))
); eauto.
destruct k2; try discriminate.
generalize (stack Hs1 (or_introl _ (refl_equal _))).
simpl.
intro; invall; subst.
destruct p.
 discriminate.
destruct p; discriminate.

(* 13: constr base direct_non_virtual nil *)
intros.
destruct (H _ _ _ _ H2 H3).
simpl in *.
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0,
         (array, array_index, (Class.Inheritance.Repeated, cn :: nil)))
); eauto.

(* 12: constr field scalar no init *)
simpl.
intros.
destruct (H _ _ _ _ H2 H3).
simpl in *; split; auto.
invall; subst.
esplit; split; try eassumption.
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, array, array_index, (Class.Inheritance.Repeated, cn :: nil),
         fs0)
); eauto.

(* 11: Sinitscalar Kconstr field *)
intros.
destruct (H _ _ _ _ (app_cons H5 _) H6).
simpl in *; split; auto.
invall; subst.
esplit; split; try eassumption.
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, array, array_index, (Class.Inheritance.Repeated, cn :: nil),
         fs0)
); eauto.

(* 10: constr_array n Kconstrother field *)
intros.
destruct (H _ _ _ _ (app_cons H0 _) H1).
simpl in *; split; auto.
invall; subst.
esplit; split; try eassumption.
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj', ar', i', (h, p), fs)
         (obj0, array, array_index, (Class.Inheritance.Repeated, cn :: nil),
         fs0)
); eauto.

(* Destruction *)

(* 9: destr array cons *)
destruct l1; simpl; try (intros; discriminate). 
destruct l1; simpl. 
 injection 1; intros until 3; subst; simpl; intros; contradiction.
injection 1; intros; subst.
destruct (H _ _ _ _ (refl_equal _) H9).
simpl in *.
split; auto.
sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, j, (Class.Inheritance.Repeated, cn0 :: nil)))
         (obj0,
         (array, array_index, (Class.Inheritance.Repeated, cn :: nil)))
); eauto.
injection e; intros; subst.
refine (_ (stack_state_wf Hs1 _ _ _ _)). 
2 : simpl; eapply in_or_app; right; right; left; reflexivity.
2 : simpl; reflexivity.
destruct 1; invall.
destruct x.
 abstract congruence.
generalize (refl_equal (length array)).
rewrite H10 at 1.
rewrite app_length.
simpl; intro; abstract omegaContradiction.

(* 8: destr field cons scalar *)
intros.
generalize (H _ _ _ _ H1 H2).
simpl; destruct 1; split; auto.
invall; esplit; split; try eassumption.
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, array, array_index, (Class.Inheritance.Repeated, cn :: nil),
         fs0)
); eauto.
apply False_rect.
injection e; intros; subst.
generalize (kind Hs1).
unfold state_kind_inv; simpl; intro; invall; subst.
destruct l1; simpl in H13.
 destruct sf; simpl in H13, H2; try contradiction.
destruct t; simpl in H13; try contradiction.
 destruct inhpath.
 destruct k; try contradiction.
 destruct kind; invall; try discriminate; subst.
 generalize (stack Hs1 (or_introl _ (refl_equal _))).
 simpl.
 intros; invall; subst.
 destruct l0.
  discriminate.
 destruct l0; discriminate.
invall; subst.
refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) _)).
2 : eapply in_or_app; right; right; left; reflexivity.
destruct 1.
destruct (H13 _ _ (refl_equal _) _ (refl_equal _)).
invall.
destruct x0.
 abstract congruence.
generalize (refl_equal (length array0)).
rewrite H17 at 1.
rewrite app_length.
simpl; intro; abstract omegaContradiction.

(* 7: destr field cons struct *)
destruct l1; simpl; injection 1; intros until 2; subst; simpl; intros; try contradiction. 
generalize (H _ _ _ _ (refl_equal _) H2).
simpl; destruct 1; split; auto; invall; esplit; split; try eassumption; intros.
sdestruct (
 aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, array, array_index, (Class.Inheritance.Repeated, cn :: nil),
         fs0)
); eauto.
apply False_rect.
injection e; intros; subst.
generalize (kind Hs1).
unfold state_kind_inv; simpl; intro; invall; subst.
destruct l1; simpl in H14.
 destruct sf; simpl in H14, H2; try contradiction.
destruct t; simpl in H14; try contradiction.
 destruct inhpath.
 destruct k; try contradiction.
 destruct kind; invall; try discriminate; subst.
 generalize (stack Hs1 (or_introl _ (refl_equal _))).
 simpl.
 intros; invall; subst.
 destruct l0.
  discriminate.
 destruct l0; discriminate.
invall; subst.
refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) _)).
2 : eapply in_or_app; right; right; left; reflexivity.
destruct 1.
destruct (H14 _ _ (refl_equal _) _ (refl_equal _)).
invall.
destruct x0.
 abstract congruence.
generalize (refl_equal (length array0)).
rewrite H18 at 1.
rewrite app_length.
simpl; intro; abstract omegaContradiction.

(* 6: destr array nil Kdestrother field *)
intros.
destruct hp'.
simpl.
generalize (H _ _ _ _ (app_cons H0 _) H1).
simpl; destruct 1; split; auto; invall; esplit; split; try eassumption; intros.
sdestruct (
aux_constr_state_key_eq_dec (obj', ar', i', (t, l0), fs)
         (obj0, array, array_index, (Class.Inheritance.Repeated, cn :: nil),
         fs0)
); eauto.
apply False_rect.
injection e; intros; subst.
generalize (kind Hs1).
unfold state_kind_inv; simpl; intro; invall; subst.
generalize (stack2 Hs1 (l1 := nil) (refl_equal _)). 
destruct 1.
generalize (H9 (fun x => x)).
destruct l1; simpl; destruct 1.
 destruct sf; simpl in H17, H1; try contradiction.
destruct t; simpl in H17; try contradiction.
 destruct inhpath.
 destruct k; try contradiction.
 destruct kind; invall; try discriminate; subst.
 generalize (stack Hs1 (or_intror _ (or_introl _ (refl_equal _)))). 
 simpl; intro; invall; subst.
 destruct l0.
  discriminate.
 destruct l0; discriminate.
invall; subst.
refine (_ (stack_wf Hs1 (l1 := _ :: nil) (refl_equal _) _)).
2 : eapply in_or_app; right; right; left; reflexivity.
destruct 1.
destruct (H19 _ _ (refl_equal _) _ (refl_equal _)).
invall.
destruct x5.
 abstract congruence.
generalize (refl_equal (length array0)).
rewrite H22 at 1.
rewrite app_length.
simpl.
intros; abstract omegaContradiction.

(* 5: destr field nil *)
intros.
generalize (H _ _ _ _ H3 H4).
simpl.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0,
         (array, array_index, (Class.Inheritance.Repeated, cn :: nil)))
); try tauto.
intros; apply False_rect; injection e; intros; invall; subst.
generalize (kind Hs1).
unfold state_kind_inv; simpl; intro; invall; subst.
destruct l1; simpl in H14.
 destruct sf; simpl in H14, H4; try contradiction.
destruct t; simpl in H14; try contradiction.
 destruct inhpath.
 destruct k; try contradiction.
 destruct kind; invall; try discriminate; subst.
 generalize (stack Hs1 (or_introl _ (refl_equal _))). 
 simpl; intro; invall; subst.
 destruct l.
  discriminate.
 destruct l; discriminate.
invall; subst.
refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) _)).
2 : eapply in_or_app; right; right; left; reflexivity.
destruct 1.
destruct (H14 _ _ (refl_equal _) _ (refl_equal _)).
invall.
destruct x0.
 abstract congruence.
generalize (refl_equal (length array0)).
rewrite H18 at 1.
rewrite app_length.
simpl; intro; abstract omegaContradiction.

(* 4: destr base cons *)
destruct l1; simpl; try (intros; discriminate).
destruct l1; simpl; injection 1; intros until 3; subst; simpl; intros; try contradiction.
generalize (H _ _ _ _ (refl_equal _) H1).
simpl; intro.
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
         (array, array_index, (Class.Inheritance.Repeated, cn :: nil)))
); eauto.
apply False_rect.
destruct beta; try discriminate.
generalize (kind Hs1).
 unfold state_kind_inv;
   simpl;
 intros; invall; subst.
 destruct p.
  discriminate.
 destruct p0; discriminate.

(* 3: destr base direct non virtual nil Kdestrother base *)
intros.
destruct hp.
generalize (H _ _ _ _ (app_cons H0 _) H1).
simpl.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (t, l)))
         (obj0,
         (array, array_index, (Class.Inheritance.Repeated, cn :: nil)))
); try tauto.
intros; apply False_rect; injection e; intros; invall; subst.
generalize (kind Hs1).
unfold state_kind_inv; simpl; intro; invall; subst.
destruct hp'.
destruct beta; invall; try discriminate; subst.
generalize (stack Hs1 (or_introl _ (refl_equal _))).
simpl; intro; invall; subst.
destruct l.
 discriminate.
destruct l; discriminate.

(* 2: destr base virtual nil *)
intros; subst.
generalize (H _ _ _ _ (refl_equal _) H2).
simpl.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0,
         (array, array_index, (Class.Inheritance.Repeated, cn :: nil)))
); try tauto.
intros; apply False_rect; injection e; intros; invall; subst.
refine (_ (stack_state_wf Hs1 _ _ _ _)).
2 : simpl; eapply in_or_app; right; right; left; reflexivity.
2 : simpl; reflexivity.
destruct 1; invall.
generalize (refl_equal (length array)).
rewrite H3 at 1.
rewrite app_length.
destruct x0.
 abstract congruence.
simpl; intro; abstract omegaContradiction.

(* 1: sdestruct *)
destruct l1; simpl.
 injection 1; intros; subst.
 exact (kind Hs1).
injection 1; intros; subst.
exact (H _ _ _ _ (refl_equal _) H5).

Qed.

End Preservation.