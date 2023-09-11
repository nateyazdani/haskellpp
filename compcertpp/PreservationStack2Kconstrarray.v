Load PreservationStack2Header.

Lemma goal : 
  forall t0 obj0 array array_count array_index cn init1, t0 = StackFrame.Kconstrarray obj0 array array_count array_index cn init1 ->    

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
unfold Globals.new in H2.
injection H2; intros; subst; simpl.
destruct (peq obj0 (Globals.next_object gl)).
 apply False_rect.
 subst.
 destruct l1; simpl in *.
 injection H5; intros; subst; simpl in *.
 generalize (kind Hs1).
 unfold state_kind_inv; simpl.
 intros; invall; subst.
 generalize (Globals.valid_none (valid_global Hs1) (Ple_refl _)).
 simpl; abstract congruence.
injection H5; intros; subst.
generalize (H _ _ _ _ (refl_equal _) H6).
simpl.
intros; invall; subst.
generalize (Globals.valid_none (valid_global Hs1) (Ple_refl _)).
simpl; abstract congruence.
rewrite PTree.gso; eauto.
destruct l1; simpl in *.
injection H5; intros; subst; simpl in *; exact (kind Hs1).
injection H5; intros; subst; exact (H _ _ _ _ (refl_equal _) H6).

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
intros; invall; subst.
esplit; repeat (split; [ eassumption |]).
split; eauto.
bintro.
sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn0 :: nil)))
         (obj0,
         (array, b, (Class.Inheritance.Repeated, cn :: nil)))
); eauto.
injection e; intros; subst.
refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) _)).
2 : eapply in_or_app; right; right; left; reflexivity.
destruct 1.
destruct (H15 _ _ (refl_equal _) _ (refl_equal _)). 
invall.
destruct x0.
 abstract congruence.
generalize (refl_equal (length array)).
rewrite H17 at 1.
rewrite app_length.
simpl; intro; abstract omegaContradiction.

(* 18: Sreturn Kconstrothercells *)
intros.
generalize (H _ _ _ _ (app_cons H0 _) H1).
simpl.
subst.
intros; invall; subst.
esplit; repeat (split; [eassumption|]).
split; eauto.
bintro.
sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn0 :: nil)))
         (obj0,
         (array, b, (Class.Inheritance.Repeated, cn :: nil)))
); eauto.
injection e; intros; subst.
refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) (in_or_app _ _ _ _))).
2 : right; right; left; reflexivity.
destruct 1.
destruct (H9 _ _ (refl_equal _) _ (refl_equal _)).
invall.
generalize (refl_equal (length array)).
rewrite H11 at 1.
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
simpl.
intro.
exact (H _ _ _ _ (refl_equal _) H2).

(* 15: Sconstructor Kconstr base *)
destruct l1; simpl; injection 1; intros; try (subst; simpl in *; contradiction).
generalize (H _ _ _ _ (app_cons H4 _) H6).
simpl; intro; invall; subst; esplit; split; eauto.
split; auto.
split; auto.
split; auto.
bintro.
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
         (array, b0, (Class.Inheritance.Repeated, cn :: nil)))
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
simpl; intro; invall; subst; esplit; split; eauto.
split; auto.
split; auto.
split; auto.
bintro.
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
         (array, b0, (Class.Inheritance.Repeated, cn :: nil)))
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
invall; simpl in *.
esplit; split; eauto.
split; auto.
split; auto.
split; auto.
bintro.
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0,
         (array, b, (Class.Inheritance.Repeated, cn :: nil)))
); eauto.
injection e; intros; subst.
generalize (kind Hs1).
unfold state_kind_inv; simpl; intro; invall; subst.
split; intro.
 generalize (H8 _ H7); unfold_ident_in_all; abstract congruence.
generalize (H10 _ H7); unfold_ident_in_all; abstract congruence.

(* 12: constr field scalar no init *)
refine (H _). 

(* 11: Sinitscalar Kconstr field *)
intros. 
exact (H _ _ _ _ (app_cons H5 _) H6).

(* 10: constr_array n Kconstrother field *)
intros until 1.
exact (H _ _ _ _ (app_cons H0 _)).

(* Destruction *)

(* 9: destr array cons *)
destruct l1; simpl; try (intros; discriminate). 
destruct l1; simpl. 
 injection 1; intros until 3; subst; simpl; intros; contradiction.
injection 1; intros; subst.
destruct (H _ _ _ _ (refl_equal _) H9).
simpl in *.
invall; subst.
esplit; split; eauto.
split; auto.
split; auto.
split; auto.
bintro.
sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, j, (Class.Inheritance.Repeated, cn0 :: nil)))
         (obj0,
         (array, b, (Class.Inheritance.Repeated, cn :: nil)))
); eauto.
injection e; intros; subst.
refine (_ (stack_state_wf Hs1 _ _ _ _)). 
2 : simpl; eapply in_or_app; right; right; left; reflexivity.
2 : simpl; reflexivity.
destruct 1; invall.
destruct x0.
 abstract congruence.
generalize (refl_equal (length array)).
rewrite H15 at 1.
rewrite app_length.
simpl; intro; abstract omegaContradiction.

(* 8: destr field cons scalar *)
refine (H _).

(* 7: destr field cons struct *)
destruct l1; simpl; injection 1; intros until 2; subst; simpl; intros; try contradiction. 
exact (H _ _ _ _ (refl_equal _) H2).

(* 6: destr array nil Kdestrother field *)
intros.
exact (H _ _ _ _ (app_cons H0 _) H1).

(* 5: destr field nil *)
intros.
generalize (H _ _ _ _ H3 H4).
simpl.
intro; invall; subst.
esplit; split; eauto.
split; auto.
split; auto.
split; auto.
bintro.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0,
         (array, b, (Class.Inheritance.Repeated, cn :: nil)))
); eauto.
apply False_rect; injection e; intros; invall; subst.
generalize (kind Hs1).
unfold state_kind_inv; simpl; intro; invall; subst.
destruct l1; simpl in H18.
 destruct sf; simpl in H18, H4; try contradiction.
destruct t; simpl in H18; try contradiction.
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
destruct (H18 _ _ (refl_equal _) _ (refl_equal _)).
invall.
destruct x0.
 abstract congruence.
generalize (refl_equal (length array0)).
rewrite H22 at 1.
rewrite app_length.
simpl; intro; abstract omegaContradiction.

(* 4: destr base cons *)
destruct l1; simpl; try (intros; discriminate).
destruct l1; simpl; injection 1; intros until 3; subst; simpl; intros; try contradiction.
generalize (H _ _ _ _ (refl_equal _) H1).
simpl; intro; invall; subst.
esplit; split; eauto.
split; auto.
split; auto.
split; auto.
bintro.
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
         (array, b0, (Class.Inheritance.Repeated, cn :: nil)))
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
intros; invall; subst.
esplit; split; eauto.
split; auto.
split; auto.
split; auto.
bintro.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (t, l)))
         (obj0,
         (array, b0, (Class.Inheritance.Repeated, cn :: nil)))
); eauto.
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
intros; invall; subst.
esplit; split; eauto.
split; auto.
split; auto.
split; auto.
bintro.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0,
         (array, b, (Class.Inheritance.Repeated, cn :: nil)))
); eauto.
intros; apply False_rect; injection e; intros; invall; subst.
refine (_ (stack_state_wf Hs1 _ _ _ _)).
2 : simpl; eapply in_or_app; right; right; left; reflexivity.
2 : simpl; reflexivity.
destruct 1; invall.
generalize (refl_equal (length array)).
rewrite H10 at 1.
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