Load PreservationHeader.

Lemma goal :
  forall obj' ar' n' i' cn' ih1 ih2 sf, sf = (StackFrame.Kconstrothercells obj' ar' n' i' cn' ih1 ih2) -> forall (Hin: In sf (State.stack s2)), stackframe_weak_inv prog s2 sf.
Proof.
 inversion Hs1.
 Opaque concat cs_le_dec Zminus.
 inversion step; intros; subst; unfold stackframe_weak_inv in *; simpl in *; unfold Globals.update in *; simpl in *; subst; try exact (stack _ Hin); try exact (stack _ (or_intror _ Hin)); try (destruct Hin as [? | Hin2]; [ discriminate | exact (stack _ Hin2) ]).

(* 11: Sblock Some (allocating structure array) *)
symmetry in H1.
unfold Globals.new in H1.
injection H1; intros; subst; simpl in *.
destruct Hin as [ | Hin2].
 discriminate.
generalize (stack _ Hin2).
intro.
destruct (peq (Globals.next_object gl) obj').
 invall; subst.
 apply False_rect.
 generalize (Globals.valid_none valid_global (Ple_refl (Globals.next_object gl))).
 congruence.
rewrite PTree.gso; eauto.

(* 10: Sconstructor Kconstrarray *)
 destruct Hin as [Heq | Hin2].
  injection Heq; intros; subst.
  sdestruct (
pointer_eq_dec (A:=A)
            (obj', (ar', i', (Class.Inheritance.Repeated, cn' :: nil)))
            (obj', (ar', i', (Class.Inheritance.Repeated, cn' :: nil)))
  ); try abstract congruence.
  unfold state_kind_inv in *; simpl in *; invall; eauto 8.
 generalize (stack _ (or_intror _ Hin2)).
 sdestruct (
pointer_eq_dec (A:=A)
            (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
            (obj', (ar', i', (Class.Inheritance.Repeated, cn' :: nil)))
 ).
  intro; invall; eauto 8.
 intro; assumption.

(* 9: Sreturn Kconstrothercells *)
generalize (stack _ (or_intror _ Hin)).
intro.
sdestruct (
 pointer_eq_dec (A:=A)
            (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
            (obj', (ar', i'0, (Class.Inheritance.Repeated, cn' :: nil)))
); [| assumption].
apply False_rect.
injection e; intros; subst.
destruct (stack_wf _ nil _ (refl_equal _) _ Hin).
simpl in *.
destruct (H1 _ _ (refl_equal _) _ (refl_equal _)).
invall.
generalize (refl_equal (length ar')).
rewrite H5 at 1.
rewrite app_length.
destruct x.
 congruence.
simpl; intro; omegaContradiction.

(* 8 Sconstructor Kconstr base *)
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
            (obj', (ar', i', (Class.Inheritance.Repeated, cn' :: nil)))
).
 apply False_rect.
 revert kind.
 unfold state_kind_inv.
 simpl.
 intro; invall; subst.
 destruct k2; invall; subst.
  destruct p; simpl in *.
   discriminate.
  destruct p0; simpl in *; discriminate.
 discriminate.
destruct Hin as [| Hin2].
 discriminate.
exact (stack _ (or_intror _ Hin2)).

(* 7: Sreturn Kconstrother base *)
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
            (obj', (ar', i', (Class.Inheritance.Repeated, cn' :: nil)))
).
 apply False_rect.
 generalize (stack _ (or_introl _ (refl_equal _))).
 simpl.
 intro; invall; subst.
 destruct k2; invall; subst.
  destruct p; simpl in *.
   discriminate.
  destruct p; simpl in *; discriminate.
 discriminate.
exact (stack _ (or_intror _ Hin)).

(* 6: constr base direct non virtual nil *)
generalize (stack _ Hin).
intro.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
            (obj', (ar', i', (Class.Inheritance.Repeated, cn' :: nil)))
).
 injection e; intros; subst.
 invall; subst.
 eauto 8.
assumption.

(* Destruction *)

(* 5: destr array *)
destruct Hin as [ | Hin2] .
 discriminate.
destruct Hin2 as [ | Hin].
 discriminate.
sdestruct (
 pointer_eq_dec (A:=A)
            (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
            (obj', (ar', i', (Class.Inheritance.Repeated, cn' :: nil)))
).
 injection e; intros; invall; subst.
 apply False_rect.
 destruct (stack_state_wf _ Hin _ (refl_equal _)).
 invall.
 generalize (refl_equal (length ar')).
 rewrite H5 at 1.
 rewrite app_length.
 destruct x.
  congruence.
 simpl; intro; omegaContradiction.
exact (stack _ Hin).

(* 4: destr field nil *)
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
            (obj', (ar', i', (Class.Inheritance.Repeated, cn' :: nil)))
).
 2 : exact (stack _ Hin).
apply False_rect.
injection e; intros; subst.
injection H; intros; subst.
revert kind.
unfold state_kind_inv.
simpl.
intro; invall; subst.
generalize (stack _ Hin).
intro; invall; subst.
destruct H15; unfold_ident_in_all; congruence.

(* 3: destr base cons *)
destruct Hin as [ | Hin2].
 discriminate.
destruct Hin2 as [ | Hin].
 discriminate.
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
            (obj', (ar', i', (Class.Inheritance.Repeated, cn' :: nil)))
).
 2 : exact (stack _ (Hin)).
apply False_rect.
revert kind.
unfold state_kind_inv.
simpl.
intro; invall; subst.
destruct beta; invall; subst.
 destruct p.
  discriminate.
 destruct p0; discriminate.
discriminate.

(* 2: destr base direct non virtual nil *)
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, hp))
            (obj'0, (ar'0, i'0, (Class.Inheritance.Repeated, cn' :: nil)))
).
 2 : exact (stack _ (or_intror _ Hin)).
apply False_rect.
injection e; intros; subst.
revert kind.
unfold state_kind_inv.
simpl.
intros; invall; subst.
generalize (stack _ (or_intror _ Hin)).
intro; invall; subst.
destruct H13; unfold_ident_in_all; congruence.

(* 1: destr base virtual nil *)
sdestruct (pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
            (obj', (ar', i'0, (Class.Inheritance.Repeated, cn' :: nil)))
).
 2 : exact (stack _ (Hin)).
apply False_rect.
revert kind.
unfold state_kind_inv.
simpl.
intro; invall; subst.
injection e; intros; subst.
generalize (stack _ Hin).
intro; invall; subst.
destruct H14; unfold_ident_in_all; congruence.

Qed.

End Preservation.
