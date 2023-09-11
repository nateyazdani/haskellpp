Load PreservationStack2Header.

Lemma goal : 
  forall t0 obj0 array array_index t l tinit1 init1 body1 vars1 k kind0 current1 other1, t0 = StackFrame.Kconstrother obj0 array array_index (t, l) tinit1 init1 body1 vars1 k kind0 current1 other1 ->    

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
inversion step; try (clear Heq; subst; simpl in *; exact (H sf2)); try (clear Heq; subst; simpl in *; intros sf1 l1 l2 H'; exact (H _ _ _ _ (app_cons H' _))); subst; simpl in *; try refine (H _); unfold Globals.update in *; simpl in *; subst.


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
(* inductive case *)
 simpl; injection 1; intros until 3; subst.
 exact (H _ _ _ _ (refl_equal _) H6).

(* 20: constr_array < n *)
destruct l1; simpl; injection 1; intros until 2; subst.
 simpl; tauto.
exact (H _ _ _ _ (refl_equal _)).

(* 19: Sconstructor Kconstrarray *)
destruct l1; simpl; injection 1; intros until 2; subst; simpl; try tauto.
intro.
generalize (H _ _ _ _ (app_cons (refl_equal _) _) H4).
unfold stackframe_constructor_inv.
simpl.
refine (_ (stack Hs1 _)).
 2 : simpl; right; eapply in_or_app; right; right; left; reflexivity.
simpl; destruct k; intros; invall; subst.
 destruct kind0; invall; subst.
 split.
  sdestruct (
    pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0, (array, array_index, (t0, l ++ current1 :: nil)))
  ).
   destruct l.
    discriminate.
   destruct l; discriminate.
  eauto.
 eauto.
sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0,
         (array, array_index, (Class.Inheritance.Shared, current1 :: nil)))
); eauto.
discriminate.
destruct kind0; invall; subst.
intros.
sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0,
         (array ++ (array_index, (t0, l), current1) :: nil, j,
         (Class.Inheritance.Repeated, b :: nil)))
); eauto.
apply False_rect.
injection e; intros; subst.
generalize (H5 _ _ H6 _ H13).
generalize (kind Hs1).
unfold state_kind_inv; simpl.
intro; invall; subst.
assert (j <= j < n) by abstract omega.
generalize (H22 _ H13).
unfold_ident.
abstract congruence.

(* 18: Sreturn Kconstrothercells *)
intros.
generalize (H _ _ _ _ (app_cons H0 _) H1).
simpl.
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
 destruct k; intro; invall; subst.
  destruct kind0; invall; subst.
   sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0, (array, array_index, (t0, l ++ current1 :: nil)))
   ); eauto.
   abstract congruence.
  sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0,
         (array, array_index, (Class.Inheritance.Shared, current1 :: nil)))
  ); eauto.
  discriminate.
 (* field *)
 destruct kind0; invall; subst.
 intros.
 sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0,
         (array ++ (array_index, (t0, l), current1) :: nil, j,
         (Class.Inheritance.Repeated, b :: nil)))
 ); eauto.

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
exact (H _ _ _ _ (refl_equal _) H3).

(* 16: constr cons field struct *)
destruct l1; simpl.
 injection 1; intros until 2; subst; simpl; intro; contradiction.
injection 1; intros until 2; subst.
destruct hp.
simpl.
destruct k; try exact (H _ _ _ _ (refl_equal _)).
intro.
generalize (H _ _ _ _ (refl_equal _) H2).
simpl.
destruct kind0; intro; invall; subst.
 split; auto.
 esplit; split; try eassumption.
 intros.
 sdestruct (
 aux_constr_state_key_eq_dec (obj, ar, i, (t, l0), fs)
         (obj0, array, array_index, (t0, l ++ current1 :: nil), fs0)
 ); eauto.
 apply False_rect.
injection e; intros; subst.
generalize (kind Hs1).
unfold state_kind_inv.
simpl.
intros; invall; subst.
generalize (H6 _ H3).
generalize (H16 _ (or_introl _ (refl_equal _))).
simpl; unfold_ident.
abstract congruence.
split; auto.
esplit; split; try eassumption.
intros.
sdestruct (aux_constr_state_key_eq_dec (obj, ar, i, (t, l0), fs)
         (obj0, array, array_index,
         (Class.Inheritance.Shared, current1 :: nil), fs0)
); eauto.
apply False_rect.
injection e; intros; subst.
generalize (kind Hs1).
unfold state_kind_inv.
simpl.
intros; invall; subst.
generalize (H6 _ H3).
generalize (H16 _ (or_introl _ (refl_equal _))).
simpl; unfold_ident.
abstract congruence.

(* 15: Sconstructor Kconstr base *)
destruct l1; simpl; injection 1; intros; try (subst; simpl in *; contradiction).
generalize (H _ _ _ _ (app_cons H4 _) H6).
subst.
simpl.
 intro; invall; subst.
 refine (_ (stack Hs1 _)).
 2 : simpl; right; eapply in_or_app; right; right; left; reflexivity.
 simpl.
 destruct k; intro; invall; subst.
  (* base *)
  destruct kind0; invall; subst.
   (* direct non-virtual *)
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
         end))) (obj0, (array, array_index, (t0, l ++ current1 :: nil)))
    ); eauto.
  apply False_rect.
     injection e; intros; subst.
     destruct k2.
      destruct (list_cons_right_inj H4).
      intros; subst.
      refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) (in_or_app _ _ _ _))).
      2 : right; right; left; reflexivity.
      destruct 1.
      destruct (H16 _ _ _ _ (refl_equal _)).
      generalize (H18 _ _ _ (refl_equal _)).
      eauto using relptr_gt_irrefl.     
     destruct l.
      discriminate.
     destruct l; discriminate.
  (* virtual *)
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
         (array, array_index, (Class.Inheritance.Shared, current1 :: nil)))
    ); eauto.
    apply False_rect.    
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
    injection H4; intros; subst.
    generalize (H25 _ (or_introl _ (refl_equal _))).
    destruct H15; simpl in *; unfold_ident_in_all; abstract congruence.
 (* field *)
 destruct kind0; invall; subst.
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
         (array ++ (array_index, (t0, l), current1) :: nil, j,
         (Class.Inheritance.Repeated, b0 :: nil)))
 ); eauto.
 apply False_rect.
 destruct k2.
  injection e; intros; subst.
 generalize (kind Hs1).
 unfold state_kind_inv; simpl.
 intros ; invall; subst.
 destruct p.
  discriminate.
 destruct p0; discriminate.
discriminate.

(* 14: Sreturn Kconstrother base *)
generalize (kind Hs1).
unfold state_kind_inv.
simpl.
intro; invall; subst.
intros.
generalize (H _ _ _ _ (app_cons H1 _) H2).
unfold stackframe_constructor_inv; simpl.
 destruct k.
  (* base *)
  destruct kind0; intro; invall; subst.
   (* direct non-virtual *)
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
         end))) (obj0, (array, array_index, (t0, l ++ current1 :: nil)))
    ); eauto.
    apply False_rect.
     destruct k2; invall; subst.
      injection e; intros; subst.
      destruct (list_cons_right_inj H0).
      subst.
      refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) _)).
      2 : eapply in_or_app; right; right; left; reflexivity.
      destruct 1.
      destruct (H8 _ _ _ _ (refl_equal _)).
      generalize (H10 _ _ _ (refl_equal _)).
      eauto using relptr_gt_irrefl.
     refine (_ (stack Hs1 _)). 
     2 : simpl; right; eapply in_or_app; right; right; left; reflexivity.
     simpl; intros; invall; subst.
     destruct l.
      discriminate.
     destruct l; discriminate.
  (* virtual *)
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
         (array, array_index, (Class.Inheritance.Shared, current1 :: nil)))
   ); eauto.
   apply False_rect.
   destruct k2.
    generalize (stack Hs1 (or_introl _ (refl_equal _))).
      simpl; intros; invall.
     destruct p.
      discriminate.
     destruct p; discriminate.
    injection e; intros; subst.
    generalize (stack Hs1 (or_introl _ (refl_equal _))).
    simpl; intro; invall; subst.
    refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) _)).
    2 : eapply in_or_app; right; right; left; reflexivity.
    destruct 1.
    destruct (H0 _ _ _ _ (refl_equal _)).
    generalize (H10 _ _ _ (refl_equal _)).
    eauto using relptr_gt_min.
 (* field *)
  destruct kind0; intros; invall; subst.  
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
         (array ++ (array_index, (t0, l), current1) :: nil, j,
         (Class.Inheritance.Repeated, b0 :: nil)))
  ); eauto.

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
 destruct k; intro; invall; subst.
  (* base *)
  destruct kind0; invall; subst.
   (* direct non-virtual *)
    sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0, (array, array_index, (t0, l ++ current1 :: nil)))
    ); eauto.
  (* virtual *)
   sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0,
         (array, array_index, (Class.Inheritance.Shared, current1 :: nil)))
   ); eauto.
 (* field *)
 destruct kind0.
 intros.
 sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0,
         (array ++ (array_index, (t0, l), current1) :: nil, j,
         (Class.Inheritance.Repeated, b :: nil)))
 ); eauto.
 apply False_rect.
 injection e; intros; subst.
generalize (H3 _ _ H11 _ H13).
unfold_ident_in_all; abstract congruence.

(* 12: constr field scalar no init *)
simpl.
destruct k; try refine (H _).
intros.
generalize (H _ _ _ _ H2 H3).
subst.
 simpl.
intros.
destruct kind0; invall; subst.
 (* direct non virtual *)
split; auto.
esplit; split; try eassumption.
intros.
 sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
            (obj0, array, array_index, (t0, l ++ current1 :: nil), fs0)
 ); eauto.
(* virtual *)
split; auto.
esplit; split; try eassumption.
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, array, array_index,
         (Class.Inheritance.Shared, current1 :: nil), fs0)
); eauto.

(* 11: Sinitscalar Kconstr field *)
intros.
generalize (H _ _ _ _ (app_cons H5 _) H6).
simpl.
destruct k; try tauto.
destruct kind0; intros; invall; subst.
(* direct non virtual *)
 split; auto.
 esplit; split; try eassumption.
 intros.
 sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, array, array_index, (t0, l ++ current1 :: nil), fs0)
 ); eauto.
(* virtual *)
split; auto.
esplit; split; try eassumption.
intros.
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, array, array_index,
         (Class.Inheritance.Shared, current1 :: nil), fs0)
); eauto.

(* 10: constr_array n Kconstrother field *)
destruct (Z_eq_dec n n); try abstract congruence.
simpl.
intros.
generalize (H _ _ _ _ (app_cons H0 _) H1).
simpl.
destruct k; try tauto.
destruct kind0; intros; invall; subst.
 (* direct non virtual *)
 split; auto. 
 esplit; split; try eassumption.
 intros.
 sdestruct (
aux_constr_state_key_eq_dec (obj', ar', i', (h, p), fs)
         (obj0, array, array_index, (t0, l ++ current1 :: nil), fs0)
 ); eauto.
(* virtual *)
 split; auto.
 esplit; split; try eassumption.
 intros.
 sdestruct (
 aux_constr_state_key_eq_dec (obj', ar', i', (h, p), fs)
         (obj0, array, array_index,
         (Class.Inheritance.Shared, current1 :: nil), fs0)
 ); eauto.

(* Destruction *)

(* 9: destr array cons *)
destruct l1; simpl; try (intros; discriminate). 
destruct l1; simpl. 
 injection 1; intros until 3; subst; simpl; intros; contradiction.
injection 1; intros; subst.
generalize (H _ _ _ _ (refl_equal _) H9).
simpl.
intro; invall; subst.
refine (_ (stack Hs1 _)).
 2 : simpl; eapply in_or_app; right; right; left; reflexivity.
simpl; intro; destruct k; invall; subst.
 (* base *)
 destruct kind0; invall; subst; split; eauto.
 (* direct non virtual *)
 sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0, (array, array_index, (t0, l ++ current1 :: nil)))
 ); eauto.
 destruct l.
  discriminate.
 destruct l; discriminate.
 (* virtual *)
 sdestruct (
 pointer_eq_dec (A:=A)
         (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0,
         (array, array_index, (Class.Inheritance.Shared, current1 :: nil)))
 ); eauto.
 discriminate.
(* field *)
destruct kind0; invall; subst.
intros.
sdestruct (
 pointer_eq_dec (A:=A)
         (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0,
         (array ++ (array_index, (t0, l), current1) :: nil, j0,
         (Class.Inheritance.Repeated, b :: nil)))
); eauto.
apply False_rect.
injection e; intros; subst.
generalize (kind Hs1).
unfold state_kind_inv; simpl.
intros; invall; subst.
destruct l1.
 simpl in H18.
 destruct sf; simpl in H18, H9; try contradiction.
 destruct c0; try contradiction.
 destruct H18; destruct array; discriminate.
simpl in H18.
destruct t; simpl in H18; try contradiction.
 destruct c0; try contradiction.
 destruct H18; destruct array; discriminate.
destruct inhpath.
destruct k; try contradiction.
destruct kind; invall; subst.
destruct (list_cons_right_inj H29).
injection H18; intros; subst.
refine (_ (stack_wf Hs1 (l1 := nil) (refl_equal _) _)).
2 : eapply in_or_app; right; right; left; reflexivity.
destruct 1.
destruct (H13 _ _ _ _ (refl_equal _)).
generalize (H31 _ _ _ (refl_equal _)).
eauto using relptr_gt_irrefl.

(* 8: destr field cons scalar *)
destruct k; try refine (H _).
intros.
generalize (kind Hs1).
unfold state_kind_inv.
generalize (H _ _ _ _ H1 H2).
destruct kind0; simpl; intros; invall; subst; split; auto; esplit; split; try eassumption; intros.
 (* direct non virtual *)
 sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, array, array_index, (t0, l ++ current1 :: nil), fs0)
 ); eauto.
 apply False_rect.
 injection e; intros; subst.
 unfold_ident_in_all; abstract congruence.
(* virtual *)
sdestruct (
 aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, array, array_index,
         (Class.Inheritance.Shared, current1 :: nil), fs0)
); eauto.
apply False_rect.
injection e; intros; subst.
unfold_ident_in_all; abstract congruence.

(* 7: destr field cons struct *)
destruct l1; simpl; injection 1; intros until 2; subst; simpl; intros; try contradiction. 
destruct k; try refine (H _ _ _ _ (refl_equal _) H2).
generalize (kind Hs1).
unfold state_kind_inv.
simpl.
generalize (H _ _ _ _ (refl_equal _) H2).
destruct kind0; simpl; intros; invall; subst; split; auto; esplit; split; try eassumption; intros.
 (* direct non virtual *)
 sdestruct (
 aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, array, array_index, (t0, l ++ current1 :: nil), fs0)
 ); eauto.
 injection e; intros; subst; unfold_ident_in_all; abstract congruence.
(* virtual *)
sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, array, array_index,
         (Class.Inheritance.Shared, current1 :: nil), fs0)
); eauto.
 injection e; intros; subst; unfold_ident_in_all; abstract congruence.

(* 6: destr array nil Kdestrother field *)
intros.
destruct k; try refine (H _ _ _ _ (app_cons H0 _) H1).
destruct hp'.
generalize (stack Hs1 (or_introl _ (refl_equal _))).
generalize (H _ _ _ _ (app_cons H0 _) H1).
simpl.
destruct kind0; intros; invall; subst; split; auto; esplit; split; try eassumption; intros.
(* direct non virtual *)
 sdestruct (
aux_constr_state_key_eq_dec (obj', ar', i', (t, l3), fs)
         (obj0, array, array_index, (t0, l ++ current1 :: nil), fs0)
 ); eauto.
 injection e; intros; subst.
 unfold_ident_in_all; abstract congruence.
(* virtual *)
sdestruct (
 aux_constr_state_key_eq_dec (obj', ar', i', (t, l3), fs)
         (obj0, array, array_index,
         (Class.Inheritance.Shared, current1 :: nil), fs0)
); eauto.
injection e; intros; subst; unfold_ident_in_all; abstract congruence.

(* 5: destr field nil *)
intros.
generalize (H _ _ _ _ H3 H4).
simpl.
  generalize (kind Hs1).
  unfold state_kind_inv; simpl.
destruct k; intros; invall; subst.
 (* base *)
 destruct kind0; invall; subst; split; eauto.
  (* direct non virtual *)
  sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0, (array, array_index, (t0, l ++ current1 :: nil)))
  ); eauto.
  injection e; intros; subst; unfold_ident_in_all; abstract congruence.
 (* virtual *)
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0,
         (array, array_index, (Class.Inheritance.Shared, current1 :: nil)))
 ); eauto.
 injection e; intros; subst; unfold_ident_in_all; abstract congruence.
(* field *)
destruct kind0; invall; subst; intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0,
         (array ++ (array_index, (t0, l), current1) :: nil, j,
         (Class.Inheritance.Repeated, b :: nil)))
); eauto.
apply False_rect.
injection e; intros; subst.
destruct l1; simpl in H13.
 destruct sf; simpl in H13, H4; try contradiction.
destruct t; simpl in H13; try contradiction.
 destruct inhpath.
 destruct k; try contradiction.
 destruct kind; invall; try discriminate; subst.
 generalize (stack Hs1 (or_introl _ (refl_equal _))).
 simpl; intro; invall; subst.
 destruct l0.
  discriminate.
 destruct l0; discriminate.
invall; subst.
destruct l1; simpl in *.
 destruct (stack2 Hs1 (l1 := nil) (refl_equal _)).
 destruct (H13 (fun x => x)).
 destruct sf; simpl in H14, H4; try contradiction; invall; destruct array; try discriminate;
  destruct c0; try contradiction; invall; discriminate.
destruct (stack2 Hs1 (l1 := nil) (refl_equal _)).
destruct (H13 (fun x => x)).
destruct t1; simpl in H14; try contradiction.
 destruct c0; try contradiction; invall; destruct array; discriminate. 
destruct inhpath.
destruct k; try contradiction.
destruct kind; invall; subst.
destruct (list_cons_right_inj H25).
injection H21; intros; subst.
refine (_ (stack_wf Hs1 (l1 := _ :: nil) (refl_equal _) _)).
2 : eapply in_or_app; right; right; left; reflexivity.
destruct 1.
destruct (H14 _ _ _ _ (refl_equal _)).
generalize (H27 _ _ _ (refl_equal _)).
eauto using relptr_gt_irrefl.

(* 4: destr base cons *)
destruct l1; simpl; try (intros; discriminate).
destruct l1; simpl; injection 1; intros until 3; subst; simpl; intros; try contradiction.
refine (_ (stack Hs1 _)).
2 : simpl; eapply in_or_app; right; right; left; reflexivity.
generalize (kind Hs1).
unfold state_kind_inv.
generalize (H _ _ _ _ (refl_equal _) H1).
simpl.
destruct k; intros; invall; subst. 
 destruct kind0; invall; subst; split; eauto.
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
         end))) (obj0, (array, array_index, (t0, l ++ current1 :: nil)))
  ); eauto.
 destruct beta; invall; subst.
  injection e; intros; subst.
  destruct (list_cons_right_inj H23).
  subst.
  generalize (H22 _ (or_introl _ (refl_equal _))).
  unfold_ident_in_all; abstract congruence.
 destruct l.
  discriminate.
 destruct l; discriminate.
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
         (array, array_index, (Class.Inheritance.Shared, current1 :: nil)))
); eauto.
 destruct beta.
  destruct p.
   discriminate.
  destruct p0; discriminate.
 injection e; intros; subst.
 invall; subst.
 generalize (H23 _ (or_introl _ (refl_equal _))).
 unfold_ident_in_all; abstract congruence.
(* field *)
destruct kind0; invall; subst.
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
         (array ++ (array_index, (t0, l), current1) :: nil, j,
         (Class.Inheritance.Repeated, b0 :: nil)))
); eauto.
destruct beta; try discriminate.
destruct p; try discriminate.
destruct p0; discriminate.

(* 3: destr base direct non virtual nil Kdestrother base *)
destruct hp.
intros.
generalize (kind Hs1).
unfold state_kind_inv.
destruct hp'.
generalize (H _ _ _ _ (app_cons H0 _) H1).
simpl.
destruct k; intros; invall; subst.
 (* base *)
 destruct kind0; invall; subst; split; eauto.
  (* direct non virtual *)
  sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (t, l0)))
         (obj0, (array, array_index, (t0, l ++ current1 :: nil)))
  ); eauto.
  injection e; intros; subst; unfold_ident_in_all; abstract congruence.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (t, l0)))
         (obj0,
         (array, array_index, (Class.Inheritance.Shared, current1 :: nil)))
 ); eauto.
  injection e; intros; subst; unfold_ident_in_all; abstract congruence.
destruct kind0; intros; subst.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (t, l0)))
         (obj0,
         (array ++ (array_index, (t0, l), current1) :: nil, j,
         (Class.Inheritance.Repeated, b0 :: nil)))
); eauto.
injection e; intros; subst.
generalize (H2 _ _ H0 _ H4).
unfold_ident_in_all; abstract congruence.

(* 2: destr base virtual nil *)
intros; subst.
generalize (kind Hs1).
unfold state_kind_inv.
refine (_ (stack Hs1 _)). 
2 : simpl; eapply in_or_app; right; right; left; reflexivity.
generalize (H _ _ _ _ (refl_equal _) H2).
simpl; intros; invall; subst.
destruct k.
 (* base *)
 destruct kind0; invall; subst; split; eauto.
  (* direct non virtual *)
  sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, x5 :: nil)))
         (obj0, (array, array_index, (t0, l ++ current1 :: nil)))
  ); eauto. 
  destruct l.
   discriminate.
  destruct l; discriminate.
 (* virtual *)
 sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, x5 :: nil)))
         (obj0,
         (array, array_index, (Class.Inheritance.Shared, current1 :: nil)))
 ); eauto.
 discriminate.
(* field *)
destruct kind0; invall; subst; intros.
sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, x5 :: nil)))
         (obj0,
         (array ++ (array_index, (t0, l), current1) :: nil, j,
         (Class.Inheritance.Repeated, b :: nil)))
); eauto.
injection e; intros; subst.
generalize (H1 _ _ H4 _ H9).
unfold_ident_in_all; abstract congruence.

(* 1: sdestruct *)
destruct l1; simpl.
 injection 1; intros; subst.
 exact (kind Hs1).
injection 1; intros; subst.
exact (H _ _ _ _ (refl_equal _) H5).

Qed.

End Preservation.