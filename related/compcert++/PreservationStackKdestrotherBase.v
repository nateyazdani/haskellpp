Load PreservationHeader.

Lemma goal :
  forall obj ar i h P k2 current other sf, sf = (StackFrame.Kdestrother obj ar i (h, P) Constructor.base k2 current other) -> forall (Hin: In sf (State.stack s2)), stackframe_weak_inv prog s2 sf.
Proof.
 inversion Hs1.
 Opaque concat cs_le_dec Zminus.
 inversion step; intros; subst; unfold stackframe_weak_inv in *; simpl in *; unfold Globals.update in *; simpl in *; subst; try exact (stack _ Hin); try exact (stack _ (or_intror _ Hin)); try (destruct Hin as [? | Hin2]; [ discriminate | exact (stack _ Hin2) ]).

(* 11: Sblock Some (allocating structure array) *)
symmetry in H1.
destruct Hin as [ | Hin2].
 discriminate.
generalize (stack _ Hin2).
intro; invall; subst.
esplit.
split.
 eassumption.
esplit.
split.
 eapply Globals.valid_pointer_new; simpl; eauto.
eauto 8. 

(* 10: Sconstructor Kconstrarray *)
 destruct Hin as [ | Hin2].
  discriminate.
 generalize (stack _ (or_intror _ Hin2)).
 intro; invall; subst.
 sdestruct (pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (h, P)))
 ).
  apply False_rect.
  injection e; intros; subst.
  revert kind.
  unfold state_kind_inv.
  simpl.
  intros; invall; subst.
  assert (i0 <= i0 < n) by abstract omega.
  generalize (H15 _ H12).
  intro.
  destruct H9; unfold_ident_in_all; abstract congruence.
 destruct k2.
  sdestruct (
    pointer_eq_dec (A:=A)
    (obj,
      (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
    (obj0, (ar0, i0, (h, P ++ current :: nil)))
  ).
   apply False_rect.
   destruct P.
    discriminate.
   destruct P; discriminate.
  eauto 10.
 sdestruct (
pointer_eq_dec (A:=A)
                        (obj,
                        (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
                        (obj0,
                        (ar0, i0, (Class.Inheritance.Shared, current :: nil)))
 ).
  discriminate.
 eauto 10.

(* 9: Sreturn Kconstrothercells *)
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (h, P)))
).
 apply False_rect.
 injection e; intros; subst.
 generalize (stack _ (or_intror _ Hin)).
 intro; invall; subst.
 revert kind.
 unfold state_kind_inv.
 simpl.
 destruct 1; unfold_ident_in_all; abstract congruence.
generalize (stack _ (or_intror _ Hin)).
intro.
destruct k2.
 sdestruct (
pointer_eq_dec (A:=A)
                        (obj,
                        (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
                        (obj0, (ar0, i0, (h, P ++ current :: nil)))
 ).
  apply False_rect.
  invall; subst.
  destruct P.
   discriminate.
  destruct P; discriminate.
 assumption.
sdestruct (
 pointer_eq_dec (A:=A)
                        (obj,
                        (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
                        (obj0,
                        (ar0, i0, (Class.Inheritance.Shared, current :: nil)))
).
 discriminate.
assumption.

(* 8: Sconstructor Kconstr base *)
destruct Hin as [ | Hin2].
 discriminate.
generalize (stack _ (or_intror _ Hin2)).
intro.
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
           end))) (obj0, (ar0, i0, (h0, P)))
).
 apply False_rect.
 injection e; intros; subst.
 revert kind.
 unfold state_kind_inv.
 simpl.
 intro; invall; subst.
 destruct k2; invall; subst.
  generalize (H14 _ (or_introl _ (refl_equal _))).
  intro; unfold_ident_in_all; abstract congruence.
 generalize (H16 _ (or_introl _ (refl_equal _))).
 intro; unfold_ident_in_all; abstract congruence.
destruct k0.
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
                        end))) (obj0, (ar0, i0, (h0, P ++ current :: nil)))
 ).
  2 : assumption.
 apply False_rect.
 destruct k2.
  injection e; intros; subst.
  generalize (last_complete p b).
  rewrite H3.
  rewrite last_complete.
  injection 1; intros; subst.
  generalize (app_reg_r H3).
  intro; subst.
  revert kind.
  unfold state_kind_inv.
  simpl.
  intro; invall; subst.
  unfold_ident_in_all; abstract congruence.
 invall; subst.
 destruct P.
  discriminate.
 destruct P; discriminate.
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
                        (ar0, i0, (Class.Inheritance.Shared, current :: nil)))
).
 2 : assumption.
apply False_rect.
revert kind.
unfold state_kind_inv; simpl.
destruct k2; intro; invall; subst.
 destruct p.
  discriminate.
 destruct p0; discriminate.
injection e; intros; subst.
assert (x2 = x6).
 inversion H14; subst.
 inversion H22; subst.
 inversion H5; subst.
 inversion H29; subst.
 replace o0 with o in * by abstract congruence.
 generalize (valid_array_path_last H18 H3).
 intro; subst.
 generalize (path_last H27).
 injection 1; intros; subst.
 generalize (path_last H17).
 injection 1; intros; subst.
 inversion H17; subst.
 inversion H27; subst.
 abstract congruence.
unfold_ident_in_all; abstract congruence.

(* 7: Sreturn Kconstrother base *)
generalize (stack _ (or_intror _ Hin)).
intro.
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
           end))) (obj0, (ar0, i0, (h0, P)))
).
 apply False_rect.
 injection e; intros; subst.
 generalize (stack _ (or_introl _ (refl_equal _))).
 simpl; intro; destruct k2; invall; subst.
 destruct H12; unfold_ident_in_all; abstract congruence.
 destruct H14; unfold_ident_in_all; abstract congruence.
destruct k0. 
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
                        end))) (obj0, (ar0, i0, (h0, P ++ current :: nil)))
 ).
  2 : assumption.
 apply False_rect.
 invall; subst.
 destruct k2.
  injection e; intros; subst.
  generalize (last_complete p b).
  unfold_ident_in_all.
  rewrite H0.
  rewrite last_complete.
  injection 1; intros; subst.
  generalize (app_reg_r H0).
  intro; subst.
  generalize (stack _ (or_introl _ (refl_equal _))).
  intro; invall; subst; unfold_ident_in_all; abstract congruence.
 destruct P.
  discriminate.
 destruct P; discriminate.
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
                        (ar0, i0, (Class.Inheritance.Shared, current :: nil)))
).
 2 : assumption.
apply False_rect.
generalize (stack _ (or_introl _ (refl_equal _))).
intro; destruct k2; invall; subst.
 destruct p.
  discriminate.
 destruct p; discriminate.
injection e; intros; subst.
 inversion H2; subst.
 inversion H15; subst.
 injection (path_last H13).
 inversion H13; subst.
 inversion H10; subst.
 inversion H26; subst.
 injection (path_last H24).
 inversion H24; subst.
 replace o0 with o in * by abstract congruence.
 generalize (valid_array_path_last H20 H0).
 abstract congruence.

(* 6: constr base direct non virtual nil *)
generalize (stack _ Hin).
intro.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (h0, P)))
).
 apply False_rect.
 injection e; intros; subst.
 invall; subst.
 revert kind.
 unfold state_kind_inv; simpl.
 intros; invall; subst.
 unfold_ident_in_all; abstract congruence.
destruct k2.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
                        (obj0, (ar0, i0, (h0, P ++ current :: nil)))
 ).
  2 : assumption.
 apply False_rect.
 injection e; intros; invall; subst.
 generalize H.
 rewrite last_complete.
 injection 1; intros; subst.
 revert kind.
 unfold state_kind_inv; simpl.
 intros; invall; subst.
 unfold_ident_in_all; destruct H13; abstract congruence.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
                        (obj0,
                        (ar0, i0, (Class.Inheritance.Shared, current :: nil)))
).
 2 : assumption.
apply False_rect.
injection e; intros; invall; subst.
injection H; intros; subst.
revert kind.
unfold state_kind_inv; simpl.
intros; invall; subst.
unfold_ident_in_all; destruct H15; abstract congruence. 

(* Destruction *)

(* 5: destr array *)
destruct Hin as [ | Hin2] .
 discriminate.
destruct Hin2 as [ | Hin ].
 discriminate.
generalize (stack _ (Hin)).
intro.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i, (h, P)))
 ).
 apply False_rect.
 revert kind.
 unfold state_kind_inv.
 simpl; injection e; intros; invall; subst.
 assert (0 <= i <= i) by abstract omega.
 generalize (H20 _ H5).
 unfold_ident_in_all; abstract congruence.
destruct k2.
 sdestruct (
 pointer_eq_dec (A:=A)
                        (obj,
                        (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
                        (obj0, (ar0, i, (h, P ++ current :: nil)))
 ).
  2 : assumption.
 apply False_rect.
 invall; subst.
 destruct P.
  discriminate.
 destruct P; discriminate.
sdestruct (
pointer_eq_dec (A:=A)
                        (obj,
                        (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
                        (obj0,
                        (ar0, i, (Class.Inheritance.Shared, current :: nil)))
).
 discriminate.
assumption.

(* 4: destr field nil *)
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (h0, P)))
).
 apply False_rect.
 injection e; intros; subst.
 generalize (stack_state_wf _ Hin).
 simpl.
 destruct 1.
 generalize (H2 _ _ _ (refl_equal _)).
 apply SubobjectOrdering.relptr_gt_irrefl.
 assumption.
generalize (stack _ Hin).
intro; destruct k2; invall; subst.
 sdestruct (
   pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
   (obj0, (ar0, i0, (h0, P ++ current :: nil)))
 ); eauto 16.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
                        (obj0,
                        (ar0, i0, (Class.Inheritance.Shared, current :: nil)))
); eauto 16.

(* 3: destr base cons *)
destruct Hin as [ | Hin2].
 discriminate.
destruct Hin2 as [Heq | Hin].
 injection Heq. 
 intros; subst.
 generalize (StackFrame.Kdestrother_base_inj Heq).
 intro; invall; subst.
 revert kind.
 unfold state_kind_inv.
 simpl.
 intro; invall; subst.
 sdestruct (
pointer_eq_dec (A:=A)
           (obj0,
           (ar0, i0,
           (match k2 with
            | Constructor.direct_non_virtual => h0
            | Constructor.virtual => Class.Inheritance.Shared
            end,
           match k2 with
           | Constructor.direct_non_virtual => P ++ current :: nil
           | Constructor.virtual => current :: nil
           end))) (obj0, (ar0, i0, (h0, P)))
 ).
  apply False_rect.
  destruct k2; invall; subst.
   injection e.
   intro.
   generalize (refl_equal (length P)).
   rewrite <- H11 at 1.
   rewrite app_length.
   simpl.  
   intro.
   assert ((length P + 1)%nat = length P) by assumption.
   omegaContradiction.
  discriminate.
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
destruct k2; invall; subst.
 sdestruct (
 pointer_eq_dec (A:=A) (obj0, (ar0, i0, (h0, P ++ current :: nil)))
            (obj0, (ar0, i0, (h0, P ++ current :: nil)))
 ).
  esplit.
  split.
   eassumption.
  left; trivial.
 abstract congruence.
sdestruct (
   pointer_eq_dec (A:=A)
            (obj0, (ar0, i0, (Class.Inheritance.Shared, current :: nil)))
            (obj0, (ar0, i0, (Class.Inheritance.Shared, current :: nil)))
).
 eauto 8.
abstract congruence.
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
           end))) (obj0, (ar0, i0, (h0, P)))
).
 apply False_rect.
 destruct beta. 
 injection e; intros; subst.
  destruct (stack_state_wf _ Hin).  
  generalize (H _ _ _ (refl_equal _)).
  inversion 1.
   subst.
   rewrite last_complete in H11.
   injection H11; intro; subst.
   unfold state_kind_inv  in kind.
   simpl in kind.
   invall; subst.
   inversion H8; subst.
   inversion H25; subst.
   rewrite (path_last H23) in H9.
   injection H9; intros; subst.
   assert (In (Class.Inheritance.Repeated, cn) (Class.super x2)).
    eapply in_map_bases_elim.
    eapply in_rev_elim.
    rewrite H15.
   eauto using in_or_app.
  assert (path (Program.hierarchy prog) cn (p ++ cn :: nil) through h0).
    eapply path_concat.
    eassumption.
    eleft with (lf := cn :: nil) (lt := x1 :: nil).
    reflexivity.
    reflexivity.
    simpl.
    rewrite H10.
    sdestruct (
      In_dec super_eq_dec (Class.Inheritance.Repeated, cn) (Class.super x2)
    ).
    rewrite H1.
    trivial.
   contradiction.
  Transparent concat. simpl.
  rewrite (path_last H23).
  destruct (peq x1 x1); unfold_ident_in_all; abstract congruence.
 generalize (path_concat H26 H12 H13).
 intro.
 generalize (path_last H27).
 rewrite (path_last H23).
 injection 1; intros; subst.
 destruct (Plt_irrefl to').
 eapply Ple_Plt_trans.
 eapply Well_formed_hierarchy.path_le.
  eassumption.
  eexact H12.
 eapply Well_formed_hierarchy.well_founded.
 eassumption.
 2 : eassumption.
 assumption.
generalize (refl_equal (length ar0)).
rewrite H8 at 1.
rewrite app_length.
destruct l.
 abstract congruence.
simpl; intro; omegaContradiction.
injection e; intros; subst.
destruct (stack_state_wf _ Hin _ (refl_equal _)).  
invall.
generalize (refl_equal (length ar0)).
rewrite H0 at 1.
destruct x.
 abstract congruence.
rewrite app_length.
simpl; intro; omegaContradiction.
generalize (stack _ Hin).
intro.
destruct k2.
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
                        end))) (obj0, (ar0, i0, (h0, P ++ current :: nil)))
 ).
   invall; subst; eauto 16.
  assumption.
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
                        (ar0, i0, (Class.Inheritance.Shared, current :: nil)))
).
 invall; subst; eauto 16.
assumption.
  
(* 2: destr base direct non virtual nil *)
sdestruct (
 (pointer_eq_dec (A:=A) (obj, (ar, i, hp)) (obj0, (ar0, i0, (h, P)))
)).
 apply False_rect.
 injection e; intros; subst.
 destruct (stack_wf _ nil _ (refl_equal _) _ Hin).
 destruct (H _ _ _ _ (refl_equal _)).
 revert kind.
 unfold state_kind_inv; simpl.
 destruct hp'.
 destruct beta; intro; invall; subst.
  generalize (H1 _ _ _ (refl_equal _)).
  inversion 1.
   subst.
   rewrite last_complete in H17.
   injection H17; intro; subst.
   generalize (concat_last (path_nonempty H18) H19).
   rewrite (path_last H18).
   intro.
   generalize (stack _ (or_introl _ (refl_equal _))).
   simpl.
   intro; invall; subst.
   rewrite last_complete in H6.
   injection H6; intros; subst.
   replace x5 with to' in * by abstract congruence.
   apply (Plt_irrefl to').
   eapply Ple_Plt_trans with x1.
   eauto using Well_formed_hierarchy.path_le.
   eapply Well_formed_hierarchy.well_founded.
   eassumption.
   eassumption.
   eapply in_map_bases_elim.
   eapply in_rev_elim.
   rewrite H23.
   eauto using in_or_app.
  generalize (refl_equal (length ar')).
  rewrite H14 at 1.
  rewrite app_length.
  destruct l0.
   congruence.
  simpl; intro; omegaContradiction.
 generalize (H1 _ _ _ (refl_equal _)).
 inversion 1.
  subst.
  injection H17; intros; subst.
  generalize (concat_last (path_nonempty H18) H19).
  rewrite (path_last H18).
  intro.
  generalize (stack _ (or_introl _ (refl_equal _))).
  simpl.
  intro; invall; subst.
  injection H6; intros; subst.
  injection H10; intros; subst.
  apply (Plt_irrefl to').
   eapply Ple_Plt_trans with x1.
   eauto using Well_formed_hierarchy.path_le.
   eapply Well_formed_hierarchy.is_virtual_base_of_lt.
   eassumption.
   eapply vborder_list_virtual_base.
   eassumption.
   eassumption.
   eauto using in_rev_intro, in_or_app.
  generalize (refl_equal (length ar')).
  rewrite H14 at 1.
  rewrite app_length.
  destruct l0.
   congruence.
  simpl; intro; omegaContradiction.
generalize (stack _ (or_intror _ Hin)).  
intros.
destruct k2.
 sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, hp))
                        (obj0, (ar0, i0, (h, P ++ current :: nil)))
 ).
  2 : assumption.
 apply False_rect.
 injection e; intros; invall; subst.
 revert kind.
 unfold state_kind_inv; simpl.
 destruct beta; intro; invall; subst. 
  destruct hp'; invall; subst.
  generalize (last_complete l b).
  rewrite <- H18.
  rewrite last_complete.
  injection 1; intros; subst.
  generalize (app_reg_r H18).
  intro; subst.
  destruct (stack_wf _ nil _ (refl_equal _) _ Hin).
  destruct (H12 _ _ _ _ (refl_equal _)).
  generalize (H16 _ _ _ (refl_equal _)).
  apply relptr_gt_irrefl.
  assumption.
 destruct hp'; invall; subst.
 destruct P.
  discriminate.
 destruct P; discriminate.
sdestruct( 
pointer_eq_dec (A:=A) (obj, (ar, i, hp))
                        (obj0,
                        (ar0, i0, (Class.Inheritance.Shared, current :: nil)))
).
 2 : assumption.
 apply False_rect.
 injection e; intros; invall; subst.
 revert kind.
 unfold state_kind_inv.
 simpl.
 destruct beta; intro; invall; subst.
  destruct hp'; invall; subst.
  generalize (stack _ (or_introl _ (refl_equal _))).
  simpl.
  intros; invall; subst.
  destruct l.
   discriminate.
  destruct l; discriminate.
 destruct hp'; invall; subst.
 injection H18; intros; subst.
 injection H3; intro; subst.
 generalize (stack _ (or_introl _ (refl_equal _))).
 intro; invall; subst.
 destruct (stack_wf _ nil _ (refl_equal _) _ Hin).
 destruct (H10 _ _ _ _ (refl_equal _)).
 generalize (H21 _ _ _ (refl_equal _)).
 eauto using relptr_gt_min.

(* 1: destr base virtual nil *)
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (h0, P)))
).
 apply False_rect.
 injection e; intros; subst.
 destruct (stack_state_wf _ Hin _ (refl_equal _)).
 invall.
 destruct x.
  congruence.
 generalize (refl_equal (length ar0)).
 rewrite H1 at 1.
 rewrite app_length.
 simpl; intro; omegaContradiction.
generalize (stack _ Hin).
intro.
destruct k2.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
                        (obj0, (ar0, i0, (h0, P ++ current :: nil)))
 ).
  2 : assumption.
apply False_rect.
injection e; intros; invall; subst.
destruct (stack_state_wf _ Hin _ (refl_equal _)).
 invall.
 destruct x.
  congruence.
 generalize (refl_equal (length ar0)).
 rewrite H2 at 1.
 rewrite app_length.
 simpl; intro; omegaContradiction.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
                        (obj0,
                        (ar0, i0, (Class.Inheritance.Shared, current :: nil)))
).
 2 : assumption.
apply False_rect.
injection e; intros; invall; subst.
destruct (stack_state_wf _ Hin _ (refl_equal _)).
 invall.
 destruct x.
  congruence.
 generalize (refl_equal (length ar0)).
 rewrite H2 at 1.
 rewrite app_length.
 simpl; intro; omegaContradiction.

Qed.

End Preservation.
