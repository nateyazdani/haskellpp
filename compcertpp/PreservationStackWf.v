Load PreservationHeader.

Lemma goal : forall sf1 l1 l2, State.stack s2 = l1 ++ sf1 :: l2 -> forall sf2, In sf2 l2 -> ((
    forall obj ar i hp, frame_pointer sf1 = Some (obj, ar, i, hp) -> ((
      forall ar' i' hp', frame_pointer sf2 = Some (obj, ar', i', hp') -> relptr_gt  (ar, i, hp) (ar', i', hp')
    ) /\
    forall ar', frame_array sf2 = Some (obj, ar') -> exists l', ar = ar' ++ l'
    )) /\
  forall obj ar, frame_array sf1 = Some (obj, ar) -> forall ar', frame_array_weak sf2 = Some (obj, ar') -> exists l', ar = ar' ++ l' /\ l' <> nil
)
.
Proof.
inversion Hs1.
  inversion step; subst; simpl in *; try trivial;
    intros ? ? ? K;
    try  (exact (stack_wf _ _ _ (app_cons K _)));
      destruct l1 as [ | ? l1']; simpl in K; injection K; intros until 2; subst; simpl; try exact (stack_wf _ _ _ (refl_equal _)); intros ? J; (split; [((intros; discriminate) || (injection 1; intros; subst; eauto; fail)) | (try (intros; discriminate); injection 1; intros; subst; eauto)]) || (try (split; [| ((intros; discriminate) || (injection 1; intros; subst; eauto; fail))])).

(* 8 Sconstructor Kconstrarray *)
destruct (stack_wf _ nil _ (refl_equal _) _ J).
eauto.

(* 7 Sconstructor Kconstrothercells *)
refine (_ (stack_wf _ _ _ (app_cons _ _))).
2 : reflexivity.
intro.
destruct (x _ J).
tauto.

(* 6 Sconstrucrtor Kconstr base *)
injection 1; intros; subst.
destruct (stack_wf _ nil _ (refl_equal _) _ J).
exact (H3 _ _ _ _ (refl_equal _)).

(* 5 Sconstructor Kconstr base *)
refine (_ (stack_wf _ _ _ (app_cons _ _))).
2 : reflexivity.
intro.
destruct (x _ J).
tauto.

(* Destruction *)

(* 4 destr array cons *)
injection 1; intros; subst.
destruct J.
 subst.
 simpl.
 split.
  intros; discriminate.
 injection 1; intros; subst.
 exists nil ; rewrite <- app_nil_end; trivial.
bintro.
generalize (stack_state_wf _ H5 b).
intros.
split.
intros.
generalize (frame_pointer_frame_array_weak H7).
intro.
destruct (H6 H8).
invall; subst.
eright.
reflexivity.
assumption.
intros.
generalize (frame_array_frame_array_weak H7).
intro.
destruct (H6 H8).
invall; eauto.

(* 3 destr array cons *)
destruct l1'.
 injection H4; intros; subst; simpl.
 split.
  intros; discriminate.
 injection 1; intros; subst.
eauto.
simpl in H4.
injection H4; intros; subst t.
eauto.

(* 2 destr base cons *)
injection 1; intros; subst.
assert (
  relptr_gt
      (ar0, i0,
      (match beta with
       | Constructor.direct_non_virtual => h
       | Constructor.virtual => Class.Inheritance.Shared
       end,
      match beta with
      | Constructor.direct_non_virtual => p ++ b :: nil
      | Constructor.virtual => b :: nil
      end)) (ar0, i0, (h, p))
).
 unfold state_kind_inv in kind.
 simpl in kind.
 destruct beta; invall; subst.
  eleft.
  eassumption.
  eleft with (lt := x1 :: nil) (lf := b :: nil).
  reflexivity.
  simpl. reflexivity.
  simpl.
  rewrite H8.
  sdestruct (
   In_dec super_eq_dec (Class.Inheritance.Repeated, b) (Class.super x2)
  ).
   generalize (Well_formed_hierarchy.complete hierarchy_wf H8 i).
   destruct (hier ! b); abstract congruence.
  destruct n.
  assert (In b (x3 ++ b :: bases)) by eauto using in_or_app.
  revert H0.
  rewrite <- H9.
  intro.
  generalize (let (_, h) := In_rev _ _ in h H0).
  intros.
  destruct (let (h, _) := in_map_iff _ _ _ in h H13).
  destruct x.
  destruct H15; subst.
  generalize (let (h, _) := filter_In _ _ _ in h H16).
  destruct 1.
  destruct t.
   assumption.
  discriminate.
  simpl.
  rewrite H7.
  destruct (peq x1 x1).
   reflexivity.
  destruct n; trivial.
  discriminate.
 assert (is_virtual_base_of hier b x1).
  eapply vborder_list_virtual_base.
  eassumption.
  eassumption.
  eapply In_rev.
  rewrite rev_involutive.
  eauto using in_or_app.
 eleft.
  reflexivity.
 eright.
  eassumption.
 eleft with (lt := nil).
 reflexivity.
 reflexivity.
 simpl.
 generalize (Well_formed_hierarchy.is_virtual_base_of_defined_base hierarchy_wf H0).
 destruct (hier ! b); abstract congruence.
 simpl.
 trivial.
 discriminate.
destruct J.
 subst; simpl.
 split.
 injection 1; intros; subst.
 assumption.
 destruct beta.
  intros; discriminate.
 injection 1; intros; subst.
 exists nil.
 apply app_nil_end.
destruct beta.
 destruct (stack_state_wf _ H5).
 split; auto.
 intros; eauto using relptr_gt_trans.
generalize (stack_state_wf _ H5).
intros.
split.
 intros.
 destruct (H6 _ (frame_pointer_frame_array_weak H7)).
 invall; subst.
 eright.
 reflexivity.
 assumption.
intros.
destruct (H6 _ (frame_array_frame_array_weak H7)).
invall; eauto.

(* 1 destr base cons *)
intros. 
destruct l1'.
 injection H; intros; subst; simpl. 
 destruct beta.
  split; try (intros; discriminate).
  injection 1; intros; subst.
  eauto.
 split.
  injection 1; intros; subst.
   split.
    intros.
    destruct (stack_state_wf _ J _ (frame_pointer_frame_array_weak H5)).
    invall; subst.
    eright.
    reflexivity.
    assumption.
   intros.
    destruct (stack_state_wf _ J _ (frame_array_frame_array_weak H5)).
    invall; subst.
    eauto.
   injection 1; intros; subst; eauto.
simpl in H.
injection H; intros; subst t.
assert (In sf1 stk).
 subst; eauto using in_or_app.
eauto.

Qed.

End Preservation.
