Load PreservationStack2Header.

Lemma goal : 
  forall t0 obj0 array array_index t l tinit1 init1 body1 k kind0 current1 other1, t0 = StackFrame.Kconstr obj0 array array_index (t, l) tinit1 init1 body1 k kind0 current1 other1 ->    

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
 generalize (kind Hs1).
 unfold state_kind_inv; simpl.
 unfold stackframe_constructor_inv.
 destruct 1.
 destruct H4.
 esplit.
 split.
  eassumption.
 destruct H5.
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
 destruct 1.
 destruct H4.
 esplit.
 split.
  eassumption.
 destruct H5.
 destruct H5.
 esplit.
 split.
  eapply Globals.valid_pointer_new.
  eauto using valid_global.
  eassumption.
  symmetry; eassumption.
 assumption.

(* 20: constr_array < n *)
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
 intros; invall; subst.
 rewrite H5.
 rewrite if_some_commut.
 esplit.
 split.
  reflexivity.
 esplit.
 split.
  eassumption.
 esplit.
 split.
  eassumption.
 esplit.
 split.
  eassumption.
 destruct k; invall; subst.
  (* base *)
  esplit.
  sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0, (array, array_index, (t0, l)))
  ); trivial.
  destruct kind0; invall; subst.
   (* direct non virtual *)
   esplit.
   split.
    eassumption.
   apply and_assoc.
   split.
    bintro.
    sdestruct (
      pointer_eq_dec (A:=A)
          (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
          (obj0, (array, array_index, (t0, l ++ b :: nil)))
    ).
     destruct l.
      discriminate.
     destruct l; discriminate.
    split; eauto.
   intros.
   sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0, (array, array_index, (Class.Inheritance.Shared, b :: nil)))
   ).
    discriminate.
   eauto.
  (* virtual *)
  split.
   trivial.
  split.
   trivial.
  esplit.
  split.
   eassumption.
  apply and_assoc.
  split.
   bintro.
   sdestruct (
pointer_eq_dec (A:=A)
          (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
          (obj0, (array, array_index, (Class.Inheritance.Shared, b :: nil)))
   ).
    discriminate.
   split; eauto.
  intros.
  sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0,
         (array, array_index, (Class.Inheritance.Repeated, x1 :: b :: nil)))
  ).
   discriminate.
  eauto.
 (* field *)
 sdestruct (
 pointer_eq_dec (A:=A)
             (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
             (obj0, (array, array_index, (t0, l)))
 ).
  2 : assumption.
 apply False_rect.
 injection e; intros; subst.
 destruct kind0; invall; subst.
 generalize (kind Hs1). 
 unfold state_kind_inv.
 simpl.
 intros; invall; subst.
 assert (array_index <= array_index < n) by abstract omega.
 generalize (H20 _ H17).
 unfold_ident_in_all; abstract congruence.

(* 18: Sreturn Kconstrothercells *)
intros.
generalize (H _ _ _ _ (app_cons H0 _) H1).
unfold stackframe_constructor_inv.
subst.
refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) (in_or_app _ _ _ _))).
2 : right; right; left; reflexivity.
destruct 1.
generalize (H2 _ _ (refl_equal _)).
simpl; intro.
 assert ((obj, ar) <> (obj0, array)).
  intro.
  injection H4; intros; subst.
  destruct (H3 _ (refl_equal _)).
  destruct H5.
  assert (length array = length (array ++ x)) by abstract congruence.
  rewrite app_length in H7.
  destruct x.
   abstract congruence.
  simpl in H7; abstract omegaContradiction. 
 destruct 1; invall; subst.
 rewrite H6.
 rewrite if_some_commut.
 esplit.
 split.
  reflexivity.
 esplit.
 split.
  eassumption.
 esplit.
 split.
  eassumption.
 esplit.
 split.
  eassumption.
 destruct k; invall; subst; simpl in *.
  (* base *)
  split.
  destruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0, (array, array_index, (t0, l)))
  ); auto.
   abstract congruence.
  destruct kind0; invall; subst.
   (* direct non-virtual *)
   esplit.
   split.
    eassumption.
   apply and_assoc.
   split.
    bintro.
    destruct (
pointer_eq_dec (A:=A)
          (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
          (obj0, (array, array_index, (t0, l ++ b :: nil)))
    ); try abstract congruence.
    split; eauto.
   intros.
   destruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0, (array, array_index, (Class.Inheritance.Shared, b :: nil)))
   ); try abstract congruence.
   eauto.
 (* virtual *)
 split; auto.
 split; auto.
 esplit.
 split.
  eassumption.
 apply and_assoc.
 split.
  bintro.
  destruct (
pointer_eq_dec (A:=A)
          (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
          (obj0, (array, array_index, (Class.Inheritance.Shared, b :: nil)))
  ); try discriminate.
  split; eauto.
 intros.
 destruct (
 pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0,
         (array, array_index, (Class.Inheritance.Repeated, x1 :: b :: nil)))
 ); try discriminate.
 eauto.
 (* field *)
 destruct kind0.
 destruct H10.
 split; try assumption.
 destruct (
 pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0, (array, array_index, (t0, l)))
 ).
  abstract congruence.
 assumption.

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
destruct k.
 exact (H _ _ _ _ (refl_equal _)).
destruct kind0.
intro.
generalize (H _ _ _ _ (refl_equal _) H2).
simpl.
intros; invall; subst.
esplit.
split.
 eassumption.
esplit.
split.
 eassumption.
esplit.
split.
 eassumption.
esplit.
split.
 eassumption.
split.
 trivial.
esplit.
split.
 eassumption.
bintro.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (t, l0), fs)
          (obj0, array, array_index, (t0, l), b0)
).
 2 : split; eauto.
injection e; intros; subst.
generalize (H11 _ (or_introl _ (refl_equal _))).
intro.
apply False_rect.
refine (_ (stack_state_wf Hs1 _ _)).
2 : simpl; eapply in_or_app; right; right; left; reflexivity.
destruct 1.
generalize (H10 _ _ _ (refl_equal _)).
eauto using relptr_gt_irrefl.

(* 15: Sconstructor Kconstr base *)
destruct l1; simpl; injection 1; intros; try (subst; simpl in *; contradiction).
generalize (H _ _ _ _ (app_cons H4 _) H6).
subst.
unfold stackframe_constructor_inv.
simpl.
 intro; invall; subst.
 rewrite H4.
 rewrite if_some_commut.
 esplit.
 split.
  reflexivity.
 esplit.
 split.
  eassumption.
 esplit.
 split.
  eassumption.
 esplit.
 split.
  eassumption.
 destruct k.
  (* base *)
  invall; subst.
  split.
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
  destruct kind0; invall; subst.
   (* direct non-virtual *)
   esplit.
   split.
    eassumption.
   apply and_assoc.
   split.
    bintro.
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
          end))) (obj0, (array, array_index, (t0, l ++ b0 :: nil)))
    ).
     injection e; intros; subst.
     destruct k2.
      assert (l ++ b0 :: nil = p ++ b :: nil) by abstract congruence.
      destruct (list_cons_right_inj H15).
      intros; subst.
      refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) (in_or_app _ _ _ _))).
      2 : right; right; left; reflexivity.
      destruct 1.
      destruct (H16 _ _ _ _ (refl_equal _)).
      apply False_rect.
      generalize (H18 _ _ _ (refl_equal _)).
      eauto using relptr_gt_irrefl.
     destruct l.
      simpl in H9; discriminate.
     destruct l; simpl in e; discriminate.
    split; eauto.
   intros.
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
         end)))
         (obj0, (array, array_index, (Class.Inheritance.Shared, b0 :: nil)))
    ).
     injection e; intros; subst.
    generalize (kind Hs1).
    unfold state_kind_inv.
    simpl.
    intros.
    invall; subst.
    destruct k2.
     destruct p.
      discriminate.
     destruct p0; discriminate.
    invall; subst.
    replace b0 with b in * by abstract congruence.
    generalize (H25 _ (or_introl _ (refl_equal _))).
    generalize (H14 (refl_equal _) _ _ (refl_equal _) _ H16).
    abstract congruence.
   eauto.
  (* virtual *)
  split; auto.
  split; auto.
  esplit.
  split.
   eassumption.
  apply and_assoc.
  split.
   bintro.
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
          end)))
          (obj0, (array, array_index, (Class.Inheritance.Shared, b0 :: nil)))
   ).
    injection e; intros; subst.
    generalize (kind Hs1).
    unfold state_kind_inv.
    simpl.
    intros.
    invall; subst.
    destruct k2.
     destruct p.
      discriminate.
     destruct p0; discriminate.
    invall; subst.
    refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) (in_or_app _ _ _ _))).
    2 : right; right; left; reflexivity.
    destruct 1.
    destruct (H17 _ _ _ _ (refl_equal _)).
    apply False_rect.
    generalize (H25 _ _ _ (refl_equal _)).
    eauto using relptr_gt_min.
   split; eauto.
  intros.
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
         end)))
         (obj0,
         (array, array_index, (Class.Inheritance.Repeated, x1 :: b0 :: nil)))
  ).
   destruct k2; invall; subst.
   injection e; intros; subst.
   destruct p.
    discriminate.
   destruct p0; simpl in H12.
    injection H12; intros; subst.
    refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) (in_or_app _ _ _ _))).
    2 : right; right; left; reflexivity.
    destruct 1.
    destruct (H15 _ _ _ _ (refl_equal _)).
    apply False_rect.
    generalize (H18 _ _ _ (refl_equal _)).
    eauto using relptr_gt_irrefl.
    destruct p1; simpl in e; discriminate.
   discriminate.
  eauto.
 (* field *)
 destruct kind0.
 destruct H11; split; try assumption.
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
 ); try assumption.
 destruct k2.
  injection e; intros; subst.
  rewrite last_complete in H8.
  injection H8; intros; subst.
 generalize (kind Hs1).
 unfold state_kind_inv; simpl.
 intros ; invall; subst.
 generalize (H20 _ (or_introl _ (refl_equal _))).
 generalize H4.
 simpl.
 unfold_ident.
 abstract congruence.
 injection e; intros; subst.
 injection H8; intros; subst.
 generalize (kind Hs1).
 unfold state_kind_inv; simpl.
 intros ; invall; subst.
 generalize (H22 _ (or_introl _ (refl_equal _))).
 generalize H4.
 simpl.
 unfold_ident.
 abstract congruence.

(* 14: Sreturn Kconstrother base *)
generalize (kind Hs1).
unfold state_kind_inv.
simpl.
intro; invall; subst.
intros.
generalize (H _ _ _ _ (app_cons H1 _) H2).
unfold stackframe_constructor_inv; simpl.
simpl.
 intros; invall; subst.
 rewrite H3.
 rewrite if_some_commut.
 esplit.
 split.
  reflexivity.
 esplit.
 split.
  eassumption.
 esplit.
 split.
  eassumption.
 esplit.
 split.
  eassumption.
 destruct k.
  (* base *)
  invall; subst.
  split.
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
   destruct k2;
    injection e; intros; subst;
      unfold_ident_in_all;
    destruct H0; abstract congruence.
  destruct kind0.
   (* direct non-virtual *)
   invall; subst.
   esplit.
   split.
    eassumption.
   apply and_assoc.
   split.
    bintro.
    destruct (pointer_eq_dec (A:=A)
          (obj,
          (ar, i,
          (match k2 with
           | Constructor.direct_non_virtual => h
           | Constructor.virtual => Class.Inheritance.Shared
           end,
          match k2 with
          | Constructor.direct_non_virtual => p ++ b :: nil
          | Constructor.virtual => b :: nil
          end))) (obj0, (array, array_index, (t0, l ++ b0 :: nil)))
    ).
     split; intros; trivial.
     destruct k2; invall; subst.
      injection e; intros; subst.
      assert (last (l ++ b0 :: nil) = last (p ++ b :: nil)) by abstract congruence.
      repeat rewrite last_complete in H14.
      injection H14; intros; subst.
      generalize (app_reg_r H0).
      intros; subst.
      generalize (H8 _ H9).
      abstract congruence.
     destruct l.
      simpl in H6; discriminate.
     destruct l; simpl in e; discriminate.
    split; eauto.
   intros.
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
         end)))
         (obj0, (array, array_index, (Class.Inheritance.Shared, b0 :: nil)))
   ); eauto.
  (* virtual *)
  invall; subst.
  split; auto.
  split; auto.
  esplit.
  split.
   eassumption.
  apply and_assoc.
  split.
   bintro.
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
          end)))
          (obj0, (array, array_index, (Class.Inheritance.Shared, b0 :: nil)))
   ).
    split; auto.
    intros.
    destruct k2; invall; subst.
     destruct p.
      generalize (stack Hs1 (or_introl _ (refl_equal _))).
      simpl; intros; invall; contradiction.
     destruct p; simpl in e; discriminate.
    injection e; intros; subst.
    generalize (H10 _ H1).
    abstract congruence.
   split; eauto.
  intros.
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
         end)))
         (obj0,
         (array, array_index, (Class.Inheritance.Repeated, x1 :: b0 :: nil)))
  ).
   destruct k2.
    injection e; intros; subst.
    destruct H0.
    generalize (H12 _ H1).
    abstract congruence.
   discriminate.
  eauto.
  (* field *)
  destruct kind0.
  split ; try (destruct H8; assumption).
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
  ); try (destruct H8; assumption).
   destruct k2; invall; subst.
    injection e; intros; subst.
    rewrite last_complete in H6.
    injection H6; intros; subst.
    replace x4 with x2 in * by abstract congruence.
    assert (In current1 (Class.fields x2)).
     rewrite H4.
     eauto using in_or_app.
    generalize (H12 _ H0).
    generalize (H10 _ (or_introl _ (refl_equal _))).
    abstract congruence.
   injection e; intros; subst.
   injection H6; intros; subst.
   replace x4 with x2 in * by abstract congruence.
   assert (In current1 (Class.fields x2)).
    rewrite H4.
    eauto using in_or_app.
   generalize (H12 _ H0).
   generalize (H10 _ (or_introl _ (refl_equal _))).
   abstract congruence.

(* 13: constr base direct_non_virtual nil *)
generalize (kind Hs1).
unfold state_kind_inv.
simpl; intro; invall; subst.
rewrite <- app_nil_end in H7; subst.
intros.
generalize (H _ _ _ _ H3 H7).
subst.
unfold stackframe_constructor_inv.
simpl.
 intros; invall; subst.
 rewrite H3.
 rewrite if_some_commut.
 esplit.
 split.
  reflexivity.
 esplit.
 split.
  eassumption.
 repeat (esplit; split; [eassumption |]).
 destruct k.
  (* base *)
  invall; subst.
  split.
   destruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0, (array, array_index, (t0, l)))
   ); auto.
   injection e; intros; subst.
   refine (_ (stack_state_wf Hs1 _ (in_or_app _ _ _ _))).
   2 : right; right; left; reflexivity.
   destruct 1.
   generalize (H11 _ _ _ (refl_equal _)).
   intros.
   destruct (relptr_gt_irrefl hierarchy_wf H18).
  destruct kind0; invall; subst.
   (* direct non-virtual *)
   esplit.
   split.
    eassumption.
   apply and_assoc.
   split.
    bintro.
    destruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
          (obj0, (array, array_index, (t0, l ++ b :: nil)))
    ).
     injection e; intros; subst.
     split.
      intro.
      generalize (H11 _ H18).
      abstract congruence.
     intro.
     generalize (H17 _ H18).
     abstract congruence.
    split; eauto.
   intros.
   destruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0, (array, array_index, (Class.Inheritance.Shared, b :: nil)))
   ); eauto.
   injection e; intros; subst.
   generalize (H19 (refl_equal _) _ _ (refl_equal _) _ H21).
   abstract congruence.
  (* virtual *)
  split; auto.
  split; auto.
  esplit.
  split.
   eassumption.
  apply and_assoc.
  split.
   bintro.
   destruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
          (obj0, (array, array_index, (Class.Inheritance.Shared, b :: nil)))
   ); eauto.
   injection e; intros; subst.
   split; intro.
    generalize (H16 _ H11).
    abstract congruence.
   generalize (H19 _ H11).
   abstract congruence.
  intros.
  destruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0,
         (array, array_index, (Class.Inheritance.Repeated, x4 :: b :: nil)))
  ); eauto.
  injection e; intros; subst.
  generalize (H21 _ H11).
  abstract congruence.
 (* field *)
 destruct kind0.
 destruct H16.
 split ; try assumption.
 destruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0, (array, array_index, (t0, l)))
 ); trivial.

(* 12: constr field scalar no init *)
generalize (kind Hs1).
unfold state_kind_inv.
simpl.
intro; invall; subst.
intros.
generalize (H _ _ _ _ H3 H10).
subst.
 simpl.
intros; invall; subst.
repeat (esplit; split; [eassumption |]).
destruct k; auto.
(* field *)
destruct kind0; invall; subst.
split; auto.
esplit.
split.
 eassumption.
bintro.
destruct (
 aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
          (obj0, array, array_index, (t0, l), b)
); eauto.
injection e; intros; subst.
refine (_ (stack_state_wf Hs1 _ (in_or_app _ _ _ _))).
 2 : right; right; left; reflexivity.
 destruct 1.
 generalize (H12 _ _ _ (refl_equal _)).
 intro.
 destruct (relptr_gt_irrefl hierarchy_wf H20).

(* 11: Sinitscalar Kconstr field *)
generalize (kind Hs1).
unfold state_kind_inv.
simpl.
intro; invall; subst.
intros.
generalize (H _ _ _ _ (app_cons H6 _) H12).
subst.
simpl.
intro; invall; subst.
esplit.
split.
 eassumption.
esplit.
asplit.
 eassumption.
repeat (esplit; split; [eassumption |]).
destruct k; auto.
destruct kind0; invall; subst.
split; auto.
esplit.
split.
 eassumption.
bintro.
sdestruct (
 aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
          (obj0, array, array_index, (t0, l), b)
); eauto.
split; eauto.
injection e; intros; subst.
refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) (in_or_app _ _ _ _))).
2 : right; right; left; reflexivity.
destruct 1.
destruct (H19 _ _ _ _ (refl_equal _)).
generalize (H23 _ _ _ (refl_equal _)).
intro.
destruct (relptr_gt_irrefl hierarchy_wf H25).

(* 10: constr_array n Kconstrother field *)
generalize (kind Hs1).
unfold state_kind_inv.
simpl.
intro; invall; subst.
rewrite last_complete in H3.
invall; subst.
intros.
generalize (H _ _ _ _ (app_cons H2 _) H3).
subst.
simpl.
intros; invall; subst.
repeat (esplit; split; [eassumption |]).
destruct k; auto.
destruct kind0; invall; subst.
split; auto.
esplit; split.
 eassumption.
bintro.
destruct (
aux_constr_state_key_eq_dec (obj', ar', i', (h, p), fs)
          (obj0, array, array_index, (t0, l), b0)
); eauto.
 split; auto.
injection e; intros; subst.
generalize (stack Hs1 (or_introl _ (refl_equal _))).
simpl.
intros; invall; subst.
replace x10 with x6 in * by abstract congruence.
replace x11 with x7 in * by abstract congruence.
generalize (H19 _ H24).
abstract congruence.

(* Destruction *)

(* 9: destr array cons *)
destruct l1; simpl; try (intros; discriminate). 
destruct l1; simpl. 
 injection 1; intros until 3; subst; simpl; intros; contradiction.
injection 1; intros; subst.
destruct (
Z_eq_dec j (-1)
).
 abstract omegaContradiction.
generalize (H _ _ _ _ (refl_equal _) H9).
simpl.
intro; invall; subst.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (array, array_index, (t0, l)))
).
 apply False_rect.
 injection e; intros; subst.
 generalize (kind Hs1).
 unfold state_kind_inv; simpl.
 intro; invall; subst.
 assert (0 <= array_index <= array_index) by abstract omega.
 generalize (H17 _ H16).
 revert H6.
 destruct k; invall; subst; unfold_ident_in_all.
  abstract congruence.
 destruct kind0; invall; subst; unfold_ident_in_all; abstract congruence.
repeat (esplit; split; [eassumption |]). 
destruct k; try assumption.
destruct kind0; invall; subst; split; trivial.
 repeat (esplit; split; [eassumption |]).
 apply and_assoc.
 split.
  bintro.
  sdestruct (
pointer_eq_dec (A:=A)
          (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
          (obj0, (array, array_index, (t0, l ++ b :: nil)))
  ).
   destruct l.
    discriminate.
   destruct l; discriminate.
  split; eauto.
 intros.
 sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0, (array, array_index, (Class.Inheritance.Shared, b :: nil)))
 ).
  discriminate.
 eauto.
split; trivial.
split; trivial.
esplit; split; try eassumption.
apply and_assoc.
split.
 bintro.
 sdestruct (pointer_eq_dec (A:=A)
          (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
          (obj0, (array, array_index, (Class.Inheritance.Shared, b :: nil)))
 ).
  discriminate.
 split; eauto.
intros.
sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0,
         (array, array_index, (Class.Inheritance.Repeated, x1 :: b :: nil)))
).
 discriminate.
eauto.

(* 8: destr field cons scalar *)
destruct k; try refine (H _).
destruct kind0.
intros.
generalize (H _ _ _ _ H1 H2).
simpl; intro; invall; subst.
repeat (esplit; split; [eassumption |]).
split; trivial.
esplit; split; try eassumption. 
bintro.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
          (obj0, array, array_index, (t0, l), b)
).
 2 : split; eauto.
apply False_rect.
injection e; intros; subst.
refine (_ (stack_state_wf Hs1 _ _)).
2 : simpl; eapply in_or_app; right; right; left; reflexivity.
destruct 1.
generalize (H1 _ _ _ (refl_equal _)).
eauto using relptr_gt_irrefl.

(* 7: destr field cons struct *)
destruct l1; simpl; injection 1; intros until 2; subst; simpl; intros; try contradiction. 
destruct k; try refine (H _ _ _ _ (refl_equal _) H2).
destruct kind0.
generalize (H _ _ _ _ (refl_equal _) H2).
simpl; intro; invall; subst.
repeat (esplit; split; [eassumption |]).
split; trivial.
esplit; split; try eassumption. 
bintro.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
          (obj0, array, array_index, (t0, l), b0)
).
 2 : split; eauto.
apply False_rect.
injection e; intros; subst.
refine (_ (stack_state_wf Hs1 _ _)).
2 : simpl; eapply in_or_app; right; right; left; reflexivity.
destruct 1.
generalize (H4 _ _ _ (refl_equal _)).
eauto using relptr_gt_irrefl.

(* 6: destr array nil Kdestrother field *)
intros.
destruct k; try refine (H _ _ _ _ (app_cons H0 _) H1).
destruct kind0.
destruct hp'.
generalize (H _ _ _ _ (app_cons H0 _) H1).
simpl.
intros; invall; subst.
repeat (esplit; split; [eassumption|]).
split; trivial.
esplit; split; [eassumption|].
bintro.
sdestruct (
aux_constr_state_key_eq_dec (obj', ar', i', (t, l3), fs)
          (obj0, array, array_index, (t0, l), b)
).
 2 : split; eauto.
apply False_rect.
injection e; intros; subst.
refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) _)).
2 : eapply in_or_app; right; right; left; reflexivity.
destruct 1.
destruct (H0 _ _ _ _ (refl_equal _)).
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
generalize (H _ _ _ _ H3 H4).
simpl.
destruct k; try tauto.
intro; invall; subst.
repeat (esplit; split; [eassumption |]).
split; trivial.
  generalize (kind Hs1).
  unfold state_kind_inv; simpl.
  intro; invall; subst.
destruct kind0; invall; subst.
 esplit; split; [eassumption|].
 apply and_assoc.
 split.
  bintro.
  sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
          (obj0, (array, array_index, (t0, l ++ b :: nil)))
  ).
   2 : split; eauto.
  injection e; intros; subst.
  split; intros; apply False_rect.
   generalize (H6 _ H19).
   unfold_ident_in_all; abstract congruence. 
  generalize (H17 _ H19).
  unfold_ident_in_all; abstract congruence.
 intros.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0, (array, array_index, (Class.Inheritance.Shared, b :: nil)))
 ).
  2 : eauto.
 apply False_rect.
 injection e; intros; subst.
 generalize (H20 (refl_equal _) _ _ (refl_equal _) _ H22).
 unfold_ident_in_all; abstract congruence.
split; trivial.
split; trivial.
esplit; split; [eassumption|].
apply and_assoc.
split.
 bintro.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
          (obj0, (array, array_index, (Class.Inheritance.Shared, b :: nil)))
 ).
 2 : split; eauto.
 injection e; intros; subst.
 split; intro; apply False_rect.
  generalize (H17 _ H6).
  unfold_ident_in_all; abstract congruence.
 generalize (H20 _ H6).
 unfold_ident_in_all; abstract congruence.
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0,
         (array, array_index, (Class.Inheritance.Repeated, x1 :: b :: nil)))
).
 2 : eauto.
apply False_rect.
injection e; intros; subst.
generalize (H22 _ H6).
unfold_ident_in_all; abstract congruence.

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
           end))) (obj0, (array, array_index, (t0, l)))
).
 apply False_rect.
 injection e; intros; subst.
 generalize (kind Hs1).
 unfold state_kind_inv;
   simpl;
 destruct beta; intros; invall; subst.
 generalize (H19 _ (or_introl _ (refl_equal _))).
 destruct k; invall; subst; unfold_ident_in_all.
  abstract congruence.
 destruct kind0; invall; subst; unfold_ident_in_all; abstract congruence.
generalize (H20 _ (or_introl _ (refl_equal _))).
 destruct k; invall; subst; unfold_ident_in_all.
  abstract congruence.
 destruct kind0; invall; subst; unfold_ident_in_all; abstract congruence.
destruct k; try tauto. 
intros; invall; subst.
repeat (esplit; split; [eassumption|]).
split; trivial.
destruct kind0; invall; subst.
esplit; split; try eassumption.
apply and_assoc.
split.
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
          end))) (obj0, (array, array_index, (t0, l ++ b0 :: nil)))
 ).
  destruct beta.
   injection e; intros; subst.
   destruct (list_cons_right_inj H13).
   subst.
  apply False_rect.
  refine (_ (stack_state_wf Hs1 _ _)).
  2 : simpl; eapply in_or_app; right; right; left; reflexivity.
  destruct 1.
  generalize (H15 _ _ _ (refl_equal _)).
  eauto using relptr_gt_irrefl.
 destruct l.
  discriminate.
 destruct l; discriminate.
eauto.
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
         (obj0, (array, array_index, (Class.Inheritance.Shared, b0 :: nil)))
).
 apply False_rect.
 generalize (kind Hs1).
 unfold state_kind_inv; simpl.
 destruct beta; injection e; intros; invall; subst.
  destruct p.
   discriminate.
  destruct p0; discriminate.
  refine (_ (stack_state_wf Hs1 _ _)).
  2 : simpl; eapply in_or_app; right; right; left; reflexivity.
  intros.
  destruct (x3 _ (refl_equal _)).
  invall.
  destruct x8.
   abstract congruence.
  generalize (refl_equal (length array)).
  rewrite H15 at 1.
  rewrite app_length.
  simpl; intro; abstract omegaContradiction.
 eauto.
split; trivial.
split; trivial.
esplit; split; try eassumption.
apply and_assoc.
split.
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
          (obj0, (array, array_index, (Class.Inheritance.Shared, b0 :: nil)))
 ).
  generalize (kind Hs1).
  unfold state_kind_inv; simpl.
  destruct beta; injection e; intros; invall; subst.
   destruct p.
    discriminate.
   destruct p0; discriminate.
  refine (_ (stack_state_wf Hs1 _ _)).
  2 : simpl; eapply in_or_app; right; right; left; reflexivity.
  intros.
  destruct (x3 _ (refl_equal _)).
  invall.
  destruct x8.
   abstract congruence.
  generalize (refl_equal (length array)).
  rewrite H12 at 1.
  rewrite app_length.
  simpl; intro; abstract omegaContradiction.
 eauto.
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
         (array, array_index, (Class.Inheritance.Repeated, x1 :: b0 :: nil)))
).
 2 : eauto.
destruct beta; try discriminate.
destruct p; try discriminate.
destruct p0.
 simpl in e; injection e; intros; subst.
 generalize (kind Hs1).
 unfold state_kind_inv; simpl.
 intros; invall; subst; unfold_ident_in_all; abstract congruence.
destruct p1; discriminate.

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
generalize (H _ _ _ _ (app_cons H0 _) H1).
simpl.
destruct k; try tauto.
intros; invall; subst.
repeat (esplit; split; [eassumption|]).
split; trivial.
generalize (stack Hs1 (or_introl _ (refl_equal _))).
generalize (kind Hs1).
unfold state_kind_inv.
destruct hp'.
simpl.
destruct kind0; intros until 2; invall; subst.
 esplit; split; try eassumption.
 apply and_assoc.
 split.
  bintro.
  sdestruct (pointer_eq_dec (A:=A) (obj, (ar, i, (t, l0)))
          (obj0, (array, array_index, (t0, l ++ b0 :: nil)))
  ).
   2 : split; eauto.
  injection e; intros; subst.
  destruct beta; invall; subst.
  destruct (list_cons_right_inj H28).
  subst.
  apply False_rect.
  refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) _)).
  2 : eapply in_or_app; right; right; left; reflexivity.
  destruct 1.
  destruct (H3 _ _ _ _ (refl_equal _)).
  generalize (H25 _ _ _ (refl_equal _)).
  eauto using relptr_gt_irrefl.
 destruct l.
  discriminate.
 destruct l; discriminate.
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (t, l0)))
         (obj0, (array, array_index, (Class.Inheritance.Shared, b0 :: nil)))
); eauto.
apply False_rect.
injection e; intros; subst.
destruct beta; invall; subst.
 destruct l3.
  discriminate.
 destruct l3; discriminate.
 generalize (H11 (refl_equal _) _ _ (refl_equal _) _ H24).
 unfold_ident_in_all; abstract congruence.
split; trivial.
split; trivial.
esplit; split; try eassumption.
apply and_assoc.
split.
 bintro.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (t, l0)))
          (obj0, (array, array_index, (Class.Inheritance.Shared, b0 :: nil)))
 ); eauto.
 injection e; intros; subst.
  destruct beta; invall; subst.
   destruct l3.
    discriminate.
   destruct l3; discriminate.
  split; intro; apply False_rect.
   generalize (H23 _ H3).
    unfold_ident_in_all; abstract congruence.
   generalize (H25 _ H3).
   unfold_ident_in_all; abstract congruence.
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (t, l0)))
         (obj0,
         (array, array_index, (Class.Inheritance.Repeated, x1 :: b0 :: nil)))
); eauto.
injection e; intros; subst.
destruct beta; invall; try discriminate; subst.
destruct l3; try discriminate.
destruct l3.
 injection H29; intros; subst.
 injection H19; intros; subst.
 generalize (H27 _ H3).
 unfold_ident_in_all; abstract congruence.
destruct l3; discriminate.

(* 2: destr base virtual nil *)
intros; subst.
generalize (kind Hs1).
unfold state_kind_inv.
simpl.
intro; invall; subst.
generalize (H _ _ _ _ (refl_equal _) H2).
simpl; intro.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, x1 :: nil)))
           (obj0, (array, array_index, (t0, l)))
).
 apply False_rect.
 injection e; intros; subst.
 destruct k; invall; subst; unfold_ident_in_all; try abstract congruence.
 destruct kind0; invall; subst; unfold_ident_in_all; abstract congruence.
destruct k; try assumption.
invall; subst.
repeat (esplit; split; [eassumption|]).
split; trivial.
destruct kind0; invall; subst.
 esplit; split; try eassumption.
 apply and_assoc.
 split.
  bintro.
  sdestruct (
pointer_eq_dec (A:=A)
          (obj, (ar, i, (Class.Inheritance.Repeated, x1 :: nil)))
          (obj0, (array, array_index, (t0, l ++ b :: nil)))
  ).
   destruct l.
    discriminate.
   destruct l; discriminate.
  split; eauto.
 intros.
 sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, x1 :: nil)))
         (obj0, (array, array_index, (Class.Inheritance.Shared, b :: nil)))
 ); eauto.
 discriminate.
split; trivial.
split; trivial.
esplit; split; try eassumption.
apply and_assoc.
split.
bintro.
 sdestruct (
pointer_eq_dec (A:=A)
          (obj, (ar, i, (Class.Inheritance.Repeated, x1 :: nil)))
          (obj0, (array, array_index, (Class.Inheritance.Shared, b :: nil)))
 ).
  discriminate.
 split; eauto.
intros.
sdestruct (
 pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, x1 :: nil)))
         (obj0,
         (array, array_index, (Class.Inheritance.Repeated, x5 :: b :: nil)))
).
 discriminate.
eauto.

(* 1: sdestruct *)
destruct l1; simpl.
 injection 1; intros; subst.
 exact (kind Hs1).
injection 1; intros; subst.
exact (H _ _ _ _ (refl_equal _) H5).


Qed. 

End Preservation.