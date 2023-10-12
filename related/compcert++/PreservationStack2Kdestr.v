Load PreservationStack2Header.

Lemma goal : 
  forall t0 obj0 array array_index t l , t0 = StackFrame.Kdestr obj0 array array_index (t, l)  ->    

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
Opaque  Zminus.
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
 generalize (kind Hs1).
 unfold state_kind_inv; simpl.
 unfold stackframe_constructor_inv.
 destruct 1.
 destruct H5.
 split.
  assumption.
 destruct H5.
 esplit.
 split.
  eapply Globals.valid_pointer_new.
  eauto using valid_global.
  eassumption.
  symmetry; eassumption.
 assumption.
(* inductive case *)
 simpl; injection 1; intros until 3; subst.
 generalize (H _ _ _ _ (refl_equal _) H6).
 unfold stackframe_constructor_inv.
 simpl.
 destruct 1.
 destruct H5.
 destruct H5.
 split.
  auto.
 esplit.
 split.
  eapply Globals.valid_pointer_new.
  eauto using valid_global.
  eassumption.
  symmetry; eassumption.
 assumption.

(* 20: constr_array < n *)
destruct (Z_eq_dec n i).
 abstract omegaContradiction.
destruct l1; simpl; injection 1; intros until 2; subst.
 simpl; tauto.
intro.
generalize (H _ _ _ _ (refl_equal _) H2).
unfold stackframe_constructor_inv.
tauto.

(* 19: Sconstructor Kconstrarray *)
destruct l1; simpl; injection 1; intros until 2; subst; simpl; try tauto.
intro.
generalize (H _ _ _ _ (app_cons (refl_equal _) _) H4).
unfold stackframe_constructor_inv.
simpl.
 destruct 1.
 split; auto.
 sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0, (array, array_index, (t0, l)))
 ); eauto.
 apply False_rect.
 injection e; intros; subst.
 refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) _)).
 2 : eapply in_or_app; right; right; left; reflexivity.
 destruct 1.
 generalize (H10 _ _ (refl_equal _) _ (refl_equal _)).
 eauto using no_self_append_no_nil.

(* 18: Sreturn Kconstrothercells *)
intros.
generalize (H _ _ _ _ (app_cons H0 _) H1).
simpl.
destruct 1.
split; auto.
sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0, (array, array_index, (t0, l)))
); eauto.
apply False_rect.
injection e; intros; subst.
refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) (in_or_app _ _ _ _))).
2 : right; right; left; reflexivity.
destruct 1.
generalize (H4 _ _ (refl_equal _) _ (refl_equal _)).
eauto using no_self_append_no_nil.

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
intros.
destruct (H _ _ _ _ (refl_equal _) H2).
split; auto.
invall; subst.
esplit; split; eauto.
esplit; split; eauto.
esplit; split; eauto.
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (t, l0), fs)
         (obj0, array, array_index, (t0, l), fs0)
); eauto.
apply False_rect.
injection e; intros; subst.
refine (_ (stack_state_wf Hs1 _ _)).
2 : simpl; eapply in_or_app; right; right; left; reflexivity.
destruct 1.
generalize (H9 _ _ _ (refl_equal _)).
eauto using relptr_gt_irrefl.

(* 15: Sconstructor Kconstr base *)
destruct l1; simpl; injection 1; intros; try (subst; simpl in *; contradiction).
destruct (H _ _ _ _ (app_cons H4 _) H6).
split; auto.
   destruct (
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
         end))) (obj0, (array, array_index, (t0, l)))
   ); auto.
   apply False_rect.
   generalize (kind Hs1).
   unfold state_kind_inv; simpl in *; injection e; intros; destruct k2; invall; subst.
    generalize (H25 _ (or_introl _ (refl_equal _))).  
    unfold_ident_in_all; abstract congruence.
   generalize (H27 _ (or_introl _ (refl_equal _))).  
   unfold_ident_in_all; abstract congruence.

(* 14: Sreturn Kconstrother base *)
generalize (kind Hs1).
unfold state_kind_inv.
simpl.
intro; invall; subst.
intros.
destruct (H _ _ _ _ (app_cons H1 _) H2).
split; auto.
simpl in *; invall; subst.
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
         end))) (obj0, (array, array_index, (t0, l)))
); eauto.
apply False_rect.
   injection e; intros; destruct k2; invall; subst; unfold_ident_in_all; abstract congruence.

(* 13: constr base direct_non_virtual nil *)
generalize (kind Hs1).
unfold state_kind_inv.
simpl; intro; invall; subst.
rewrite <- app_nil_end in H7; subst.
intros.
generalize (H _ _ _ _ H3 H7).
simpl.
destruct 1.
split; auto.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0, (array, array_index, (t0, l)))
); eauto.
apply False_rect.
injection e; intros; invall; subst; unfold_ident_in_all; abstract congruence.

(* 12: constr field scalar no init *)
generalize (kind Hs1).
unfold state_kind_inv.
simpl.
intro; invall; subst.
intros.
generalize (H _ _ _ _ H3 H10).
simpl.
destruct 1. 
split; auto.
invall; subst.
esplit; split; eauto.
esplit; split; eauto.
esplit; split; eauto.
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, array, array_index, (t0, l), fs0)
); eauto.

(* 11: Sinitscalar Kconstr field *)
generalize (kind Hs1).
unfold state_kind_inv.
simpl.
intro; invall; subst.
intros.
generalize (H _ _ _ _ (app_cons H6 _) H12).
simpl.
intro; invall; subst.
split; auto.
esplit.
split.
 eassumption.
esplit; split; eauto.
esplit; split; eauto.
intros.
sdestruct (
 aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
          (obj0, array, array_index, (t0, l), fs0)
); eauto.

(* 10: constr_array n Kconstrother field *)
generalize (kind Hs1).
unfold state_kind_inv.
simpl.
intro; invall; subst.
rewrite last_complete in H3.
invall; subst.
intros.
generalize (H _ _ _ _ (app_cons H2 _) H3).
simpl.
intros; invall; subst.
split; auto.
repeat (esplit; split; [eassumption |]).
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj', ar', i', (h, p), fs)
         (obj0, array, array_index, (t0, l), fs0)
); eauto.

(* Destruction *)

(* 9: destr array cons *)
destruct l1; simpl; try (intros; discriminate). 
destruct l1; simpl. 
 injection 1; intros until 3; subst; simpl; intros; contradiction.
injection 1; intros; subst.
generalize (H _ _ _ _ (refl_equal _) H9).
simpl.
destruct 1.
split; auto.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (array, array_index, (t0, l)))
); eauto.

(* 8: destr field cons scalar *)
intros.
generalize (H _ _ _ _ H1 H2).
simpl; intro; invall; subst.
split; auto.
repeat (esplit; split; [eassumption |]).
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
          (obj0, array, array_index, (t0, l), fs0)
); eauto.
apply False_rect.
injection e; intros; subst.
refine (_ (stack_state_wf Hs1 _ _)).
2 : simpl; eapply in_or_app; right; right; left; reflexivity.
destruct 1.
generalize (H3 _ _ _ (refl_equal _)).
eauto using relptr_gt_irrefl.

(* 7: destr field cons struct *)
destruct l1; simpl; injection 1; intros until 2; subst; simpl; intros; try contradiction. 
generalize (H _ _ _ _ (refl_equal _) H2).
simpl; intro; invall; subst.
split; auto.
repeat (esplit; split; [eassumption |]).
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
          (obj0, array, array_index, (t0, l), fs0)
); eauto.
apply False_rect.
injection e; intros; subst.
refine (_ (stack_state_wf Hs1 _ _)).
2 : simpl; eapply in_or_app; right; right; left; reflexivity.
destruct 1.
generalize (H9 _ _ _ (refl_equal _)).
eauto using relptr_gt_irrefl.

(* 6: destr array nil Kdestrother field *)
intros.
destruct hp'.
generalize (H _ _ _ _ (app_cons H0 _) H1).
simpl.
intros; invall; subst.
split; auto.
repeat (esplit; split; [eassumption|]).
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj', ar', i', (t, l3), fs)
          (obj0, array, array_index, (t0, l), fs0)
); eauto.
apply False_rect.
injection e; intros; subst.
refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) _)).
2 : eapply in_or_app; right; right; left; reflexivity.
destruct 1.
destruct (H2 _ _ _ _ (refl_equal _)).
generalize (H9 _ _ _ (refl_equal _)).
eauto using relptr_gt_irrefl.

(* 5: destr field nil *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (array, array_index, (t0, l)))
).
 apply False_rect.
 injection e; intros; subst.
 refine (_ (stack_state_wf Hs1 _ _)).
 2 : simpl; eapply in_or_app; right; right; left; reflexivity.
 destruct 1.
 generalize (H3 _ _ _ (refl_equal _)).
 eauto using relptr_gt_irrefl.
exact (H _ _ _ _ H3 H4).

(* 4: destr base cons *)
destruct l1; simpl; try (intros; discriminate).
destruct l1; simpl; injection 1; intros until 3; subst; simpl; intros; try contradiction.
generalize (H _ _ _ _ (refl_equal _) H1).
simpl; destruct 1.
split; auto.
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
           end))) (obj0, (array, array_index, (t0, l)))
); eauto.

(* 3: destr base direct non virtual nil Kdestrother base *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, hp))
           (obj0, (array, array_index, (t0, l)))
).
 apply False_rect.
 injection e; intros; subst.
 refine (_ (stack_state_wf Hs1 _ _)).
 2 : simpl; right; eapply in_or_app; right; right; left; reflexivity.
 destruct 1.
 generalize (H0 _ _ _ (refl_equal _)).
 eauto using relptr_gt_irrefl.
destruct hp.
exact (H _ _ _ _ (app_cons H0 _) H1).

(* 2: destr base virtual nil *)
intros; subst.
generalize (kind Hs1).
unfold state_kind_inv.
simpl.
intro; invall; subst.
generalize (H _ _ _ _ (refl_equal _) H2).
simpl; destruct 1.
split; auto.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, x1 :: nil)))
           (obj0, (array, array_index, (t0, l)))
); eauto.
 apply False_rect.
 injection e; intros; subst; unfold_ident_in_all; try abstract congruence.

(* 1: sdestruct *)
destruct l1; simpl.
 injection 1; intros; subst.
 exact (kind Hs1).
injection 1; intros; subst.
exact (H _ _ _ _ (refl_equal _) H5).

Qed.

End Preservation.