Load PreservationHeader.

Lemma goal :
 match State.kind s2 with
                     | State.constr obj ar i hp _ _ _ _ _ _ _ => forall k, In k (State.stack s2) -> ((forall ar' i' hp', frame_pointer k = Some (obj, ar', i', hp') -> relptr_gt (ar, i, hp) (ar', i', hp')) /\ forall ar', frame_array k = Some (obj, ar') -> exists l', ar = ar' ++ l')
                     | State.constr_array obj ar _ _ _ _ _ => forall k, In k (State.stack s2) -> forall ar', frame_array_weak k = Some (obj, ar') -> exists l', ar = ar' ++ l' /\ l' <> nil
                     | State.destr obj ar _ _ Constructor.base Constructor.virtual _ => forall k, In k (State.stack s2) -> forall ar', frame_array_weak k = Some (obj, ar') -> exists l', ar = ar' ++ l' /\ l' <> nil
                     | State.destr obj ar i hp _ _ _ => forall k, In k (State.stack s2) -> ((forall ar' i' hp', frame_pointer k = Some (obj, ar', i', hp') -> relptr_gt (ar, i, hp) (ar', i', hp')) /\ forall ar', frame_array k = Some (obj, ar') -> exists l', ar = ar' ++ l')
                     | State.destr_array obj ar _ _ => forall k, In k (State.stack s2) -> forall ar', frame_array_weak k = Some (obj, ar') -> exists l', ar = ar' ++ l' /\ l' <> nil
                     | _ => True
                   end
.

Proof.
inversion Hs1.
  Opaque  Zminus.
  inversion step; subst; simpl in *; unfold Globals.update in *; simpl in *; subst; try trivial.

(* 14: Sblock Some: cas impossible (objet inexistant avant construction) *)
  revert H1.
  unfold Globals.new.
  simpl; injection 1; intros until 2; subst.
  generalize (Globals.valid_none valid_global (Ple_refl _)).
  intro.
destruct 1.
 subst; simpl; congruence.
intros.
apply False_rect.
generalize (stack _ H3).
revert H4.
destruct k; simpl; try (intros; discriminate); injection 1; intros; subst.
 (* Kconstr *) 
 destruct (member_extract H3).
 destruct H5.
 revert H5.
 rewrite <- (rev_involutive x).
 destruct (rev x); simpl.
  intro; subst.
  generalize kind.
  unfold state_kind_inv.
  simpl.
  destruct inhpath.
  intros; invall; subst.
  inversion H8; congruence.
 rewrite app_ass.
 simpl; intro; subst.
 destruct (stack2 _ _ _ (refl_equal _)).
 case (is_code_frame_dec t).
  intros.
  generalize (H5 i).
  simpl.
  destruct inhpath.
  intros; invall; subst.
  inversion H10; congruence.
 tauto.
(* Kconstrarray *)
 destruct (member_extract H3).
 destruct H5.
 revert H5.
 rewrite <- (rev_involutive x).
 destruct (rev x); simpl.
  intro; subst.
  generalize kind.
  unfold state_kind_inv.
  simpl.
  intros; invall; congruence.
 rewrite app_ass.
 simpl; intro; subst.
 destruct (stack2 _ _ _ (refl_equal _)).
 case (is_code_frame_dec t).
  intros.
  generalize (H5 i).
  simpl.
  intros; invall; congruence.
 tauto.
(* Kconstrother *)
destruct inhpath.
invall.
inversion H7; congruence.
(* Kconstrothercells *)
invall; congruence.
(* Kdestr *)
destruct (member_extract H3).
revert H5.
rewrite <- (rev_involutive x).
generalize (rev x).
clear x.
destruct l; simpl.
 intros; invall; subst.
 revert kind.
 unfold state_kind_inv.
 simpl.
 destruct inhpath.
 intros; invall; subst.
 inversion H6; abstract congruence.
destruct 1.
revert H5.
rewrite app_ass.
simpl.
intros; subst.
generalize (stack2 _ _ _ (refl_equal _)).
unfold stack2_inv.
simpl.
destruct (is_code_frame_dec t).
 destruct 1.
 destruct inhpath.
 destruct (H5 i).
 invall; subst.
 inversion H9; abstract congruence.
tauto.
(* Kdestrother *)
destruct inhpath.
invall; subst.
inversion H7; abstract congruence.
(* Kdestrcell *)
invall; abstract congruence.

(* 13: Sconstructor Kconstrarray *)
destruct 1.
 (* new stack frame: Kconstrothercells *)
 subst; simpl.
 split.
  intros; discriminate.
 injection 1; intros; subst.
 exists nil.
  rewrite <- app_nil_end.
  trivial.
(* other stack frames *)
destruct (stack_wf _ nil _ (refl_equal _) _ H2).
generalize (H4 _ _ (refl_equal _)).
intros.
split.
 intros.
 destruct (H5 _ (frame_pointer_frame_array_weak H8)).
 invall; subst. 
 eright.
 reflexivity.
 assumption.
intros.
destruct (H5 _ (frame_array_frame_array_weak H8)).
invall; eauto.
 
(* 12: Sreturn Kconstrothercells *)
intros until 1.
destruct (stack_wf _ nil _ (refl_equal _) _ H).
exact (H1 _ _ (refl_equal _)).

(* 11: constr field struct *)
destruct 1.
 subst.
 injection 1; intros; subst.
 esplit.
 split.
  reflexivity.
 congruence.
destruct (stack_state_wf _ H0).
intros.
destruct (frame_array_weak_inv H3).
 invall; subst.
 generalize (H1 _ _ _ H4).
 intros.
 destruct (relptr_gt_array H5).
 subst.
 rewrite app_ass.
 esplit.
 split.
 reflexivity.
 destruct x1; simpl; congruence.
destruct (H2 _ H4).
subst.
rewrite app_ass.
esplit.
split.
 reflexivity.
destruct x; simpl; congruence.

(* 10: Sconstructor Kconstr base *)
assert ( (* This is for the new stack frame, but also for others, to use transitivity *)
 relptr_gt 
     (ar, i,
     (match k2 with
      | Constructor.direct_non_virtual => h
      | Constructor.virtual => Class.Inheritance.Shared
      end,
     match k2 with
     | Constructor.direct_non_virtual => p ++ b :: nil
     | Constructor.virtual => b :: nil
     end)) (ar, i, (h, p))
).
 unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 destruct k2; invall; subst.
  eleft with (p' := (x1 :: nil) ++ b :: nil).
  eassumption.
  eleft.
   simpl.
   reflexivity.
  reflexivity.
  simpl.
  rewrite H6.
  cut (
 (if In_dec super_eq_dec (Class.Inheritance.Repeated, b) (Class.super x2)
    then match hier ! b with
         | Some _ => true
         | None => false
         end
    else false) = true
  ); try tauto.
  destruct (
    In_dec super_eq_dec (Class.Inheritance.Repeated, b) (Class.super x2)
  ).
   generalize (Well_formed_hierarchy.complete hierarchy_wf H6 i0).
   destruct (hier ! b); congruence.
  destruct n.
  assert (In b (x ++ b :: q)) by abstract (eauto using in_or_app).
  unfold_ident_in H7.
  unfold_ident_in H10.
  rewrite <- H7 in H10.
  destruct (map_elim H10).
  destruct H12.
  destruct x3.
  subst.
  destruct (let (J, _) := filter_In _ _ _ in J H12).
  destruct t; try congruence.
  assumption.
 Transparent concat. simpl.
 rewrite H5.
 destruct (peq x1 x1).
  trivial.
 congruence.
 simpl; congruence.
 eleft with (p' := nil ++ b :: nil).
 reflexivity.
 assert (is_virtual_base_of hier b x1) by abstract (
  eapply vborder_list_virtual_base; try eassumption;
  eapply in_or_app; right; left; reflexivity
 ).
 eright.
  eassumption.
 eleft.
 simpl.
 reflexivity.
 reflexivity.
 simpl.
 generalize (Well_formed_hierarchy.is_virtual_base_of_defined_base hierarchy_wf H2).
 destruct (hier ! b); congruence.
 simpl.
 trivial.
 congruence.
destruct 1.
 (* new stack frame: Kconstrother *)
 subst; simpl.
 split; try congruence.
 injection 1; intros; subst.
 assumption.
(* other stack frames *)
destruct (stack_wf _ nil _ (refl_equal _) _ H3).
destruct (H4 _ _ _ _ (refl_equal _)).
split; try assumption.
intros.
eauto using relptr_gt_trans.

(* 9: Sreturn Kconstrother base *)
intros until 1.
destruct (stack_wf _ nil _ (refl_equal _) _ H).
eauto.

(* 8: Sinitscalar Kconstr field *)
intros until 1.
destruct (stack_wf _ nil _ (refl_equal _) _ H4).
eauto.

(* 7: constr_array n Kconstrother field *)
intros until 1.
destruct (stack_wf _ nil _ (refl_equal _) _ H).
eauto.

(* 6: Sreturn Kdestr *)
intros until 1.
destruct (stack_wf _ nil _ (refl_equal _) _ H2).
eauto.

(* 5: destr field cons struct *)
destruct 1.
 subst.
 simpl.
 injection 1; intros; subst.
 esplit.
 split.
  reflexivity.
 discriminate.
intros.
destruct (stack_state_wf _ H0).
destruct (frame_array_weak_inv H1).
 invall; subst.
 generalize (H2 _ _ _ H4).
 inversion 1; subst.
  esplit.
  split.
  reflexivity.
  discriminate.
 rewrite app_ass.
 esplit.
 split.
  reflexivity.
 destruct l0; simpl; discriminate.
destruct (H3 _ H4).
subst.
rewrite app_ass.
esplit.
split.
 reflexivity.
destruct x; simpl; discriminate.

(* 4: destr_array nil Kdestrother field *)
intros until 1.
destruct (stack_wf _ nil _ (refl_equal _) _ H).
eauto.

(* 3: destr base direct non virtual nil Kdestrother base *)
destruct beta; intros until 1;
 destruct (stack_wf _ nil _ (refl_equal _) _ H).
 eauto.
simpl in H1; eauto.

(* 2: destr base direct non virtual nil Kdestrcell *)
intros until 1.
destruct (stack_wf _ nil _ (refl_equal _) _ H1).
simpl in H3.
eauto.

(* 1: requiring destructor : we must show that there is no corresponding stack frame. Added as invariant. *)
intros.
destruct H1.
 subst; simpl in H2; discriminate.
destruct (constructed_stack_objects_no_stackframe _ (or_introl _ (refl_equal _)) _ H1 _ H2).

Qed.

End Preservation.
