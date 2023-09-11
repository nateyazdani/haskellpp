Load PreservationHeader.

Lemma goal :
  forall obj ar i h P current other sf, sf = (StackFrame.Kdestrother obj ar i (h, P) Constructor.field tt current other) -> forall (Hin: In sf (State.stack s2)), stackframe_weak_inv prog s2 sf.
Proof.
 inversion Hs1.
 Opaque  concat cs_le_dec Zminus.
 inversion step; intros; subst; unfold stackframe_weak_inv in *; simpl in *; unfold Globals.update in *; simpl in *; subst; try exact (stack _ Hin); try exact (stack _ (or_intror _ Hin)); try (destruct Hin as [? | Hin2]; [ discriminate | exact (stack _ Hin2) ]).

(* 18: Sblock Some (allocating structure array) *)
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

(* 17: Sconstructor Kconstrarray *)
 destruct Hin as [ | Hin2].
  discriminate.
 generalize (stack _ (or_intror _ Hin2)).
 intro.
 sdestruct (pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (h, P)))
 ).
 2 : assumption.
  apply False_rect.
  injection e; intros; invall; subst.
  revert kind.
  unfold state_kind_inv.
  simpl.
  intros; invall; subst.
  assert (i0 <= i0 < n) by abstract omega.
  generalize (H14 _ H8).
  intro.
  unfold_ident_in_all; abstract congruence.

(* 16: Sreturn Kconstrothercells *)
generalize (stack _ (or_intror _ Hin)).
intro.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (h, P)))
).
 2 : assumption.
 apply False_rect.
 injection e; intros; invall; subst.
 revert kind.
 unfold state_kind_inv.
 simpl.
 destruct 1; unfold_ident_in_all; abstract congruence.

(* 15 : constr field cons struct *)
destruct hp.
simpl.
destruct Hin as [ | Hin].
 discriminate.
sdestruct (
 aux_constr_state_key_eq_dec
                       (obj, ar, i, (t, l), fs)
                       (obj0, ar0, i0, (h, P), current)
).
 apply False_rect.
 destruct (stack_state_wf _ Hin).
 injection e; intros; subst.
 generalize (H0 _ _ _ (refl_equal _)).
 eauto using relptr_gt_irrefl.
exact (stack _ Hin).

(* 14 : Sconstructor Kconstr base *)
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
  generalize (H15 _ (or_introl _ (refl_equal _))).
  intro; unfold_ident_in_all; abstract congruence.
 generalize (H17 _ (or_introl _ (refl_equal _))).
 intro; unfold_ident_in_all; abstract congruence.
assumption.

(* 13 : Sreturn Kconstrother base *)
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
 destruct H13; unfold_ident_in_all; abstract congruence.
 destruct H15; unfold_ident_in_all; abstract congruence.
assumption.

(* 12 : constr base direct non virtual nil *)
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
assumption.

(* 11 : constr field cons scalar *)
simpl.
sdestruct (
 aux_constr_state_key_eq_dec
                       (obj, ar, i, (h, p), fs)
                       (obj0, ar0, i0, (h0, P), current)
).
 apply False_rect.
 injection e; intros; subst.
 destruct (stack_state_wf _ Hin).
 generalize (H1 _ _ _ (refl_equal _)).
 eauto using relptr_gt_irrefl.
exact (stack _ Hin).

(* 10 : Sinitscalar *)
sdestruct (
 aux_constr_state_key_eq_dec
                       (obj, ar, i, (h, p), fs)
                       (obj0, ar0, i0, (h0, P), current)
).
 apply False_rect.
 injection e; intros; subst.
 destruct (stack_wf _ nil _ (refl_equal _) _ Hin).
 destruct (H4 _ _ _ _ (refl_equal _)).
 generalize (H6 _ _ _ (refl_equal _)).
 eauto using relptr_gt_irrefl.
exact (stack _ (or_intror _ Hin)).

(* 9: constr array n Kconstrother field *)
simpl.
sdestruct (
 aux_constr_state_key_eq_dec
                       (obj', ar', i', (h, p), fs)
                       (obj0, ar0, i, (h0, P), current)
).
 apply False_rect.
 injection e; intros; subst.
 destruct (stack_wf _ nil _ (refl_equal _) _ Hin).
 destruct (H _ _ _ _ (refl_equal _)).
 generalize (H1 _ _ _ (refl_equal _)).
 eauto using relptr_gt_irrefl.
exact (stack _ (or_intror _ Hin)).

(* Destruction *)

(* 8: destr array *)
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
 generalize (H21 _ H5).
 unfold_ident_in_all; abstract congruence.
destruct (Z_eq_dec j (-1)).
 omegaContradiction.
assumption.

(* 7: destr field scalar cons *)
sdestruct (
aux_constr_state_key_eq_dec
                       (obj, ar, i, (h, p), fs)
                       (obj0, ar0, i0, (h0, P), current)
).
 apply False_rect.
 injection e; intros; subst.
 destruct (stack_state_wf _ Hin).
 generalize (H0 _ _ _ (refl_equal _)).
 eauto using relptr_gt_irrefl.
exact (stack _ Hin).

(* 6: destr field struct cons *)
simpl.
destruct Hin as [ | Hin].
 injection H0; intros; subst.
 destruct (StackFrame.Kdestrother_field_inj H0); subst.
cut (
exists cs0 : construction_state,
     assoc (pointer_eq_dec (A:=A)) (obj0, (ar0, i0, (h0, P))) cs = Some cs0 /\
     (exists hp : is_some (last P),
        valid_pointer (Program.hierarchy prog) (Globals.heap gl)
          (Value.subobject obj0 ar0 i0 h0 P hp) /\
        (exists cn : ident,
           last P = Some cn /\
           (exists c : Class.t A,
              (Program.hierarchy prog) ! cn = Some c /\
              cs0 = StartedDestructing /\
              (exists l1 : list (FieldSignature.t A),
                 rev (Class.fields c) = l1 ++ current :: other /\
                 (if Cppsem.aux_constr_state_key_eq_dec
                       (obj0, ar0, i0, (h0, P), current)
                       (obj0, ar0, i0, (h0, P), current)
                  then Some StartedDestructing
                  else
                   assoc aux_constr_state_key_eq_dec
                     (obj0, ar0, i0, (h0, P), current) auxcs) =
                 Some StartedDestructing))))
); eauto.
 destruct (
 aux_constr_state_key_eq_dec
                       (obj0, ar0, i0, (h0, P), current)
                       (obj0, ar0, i0, (h0, P), current)
 ).
  revert kind.
  unfold state_kind_inv; simpl.
  intro; invall; eauto 16.
 abstract congruence.
generalize (stack _ Hin).
intro.
sdestruct (
aux_constr_state_key_eq_dec
                       (obj, ar, i, (h, p), fs)
                       (obj0, ar0, i0, (h0, P), current)
).
 invall; eauto 16.
assumption.

(* 5: destr array -1 *)
destruct hp'.
simpl.
sdestruct (
 aux_constr_state_key_eq_dec
                       (obj', ar', i', (t, l0), fs)
                       (obj0, ar0, i, (h, P), current)).
 apply False_rect.
 injection e; intros; subst.
 destruct (stack_wf _ nil _ (refl_equal _) _ Hin).
 destruct (H _ _ _ _ (refl_equal _)).
 generalize (H1 _ _ _ (refl_equal _)).
 eauto using relptr_gt_irrefl.
exact (stack _ (or_intror _ Hin)).

(* 4: destr field nil *)
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (h0, P)))
).
 apply False_rect.
 injection e; intros; subst.
 destruct (stack_state_wf _ Hin).
 generalize (H2 _ _ _ (refl_equal _)).
 apply SubobjectOrdering.relptr_gt_irrefl.
 assumption.
exact (stack _ Hin).

(* 3: destr base cons *)
destruct Hin as [ | Hin2].
 discriminate.
destruct Hin2 as [ | Hin].
 discriminate.
generalize (stack _ Hin).
intro.
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
 invall; eauto 16.
assumption.
  
(* 2: destr base direct non virtual nil Kdestrother base *)
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
destruct hp.
exact (stack _ (or_intror _ Hin)).  

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
exact (stack _ Hin).

Qed.

End Preservation.
