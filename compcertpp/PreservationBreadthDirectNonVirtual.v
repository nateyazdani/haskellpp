Load PreservationHeader.

Ltac forward := constructor; simpl; intros; try discriminate; try omegaContradiction.
Ltac fin := forward; reflexivity.

Lemma nodup : forall cn c, hier ! cn = Some c ->
        forall l0 b1 l1 l2, map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b) (filter (fun hb : _ * ident =>
          match hb with
            | (Class.Inheritance.Shared, _) => false
            | _ => true
          end
        ) (Class.super c)) = (l0 ++ b1 :: l1 ++ b1 :: l2) -> False.
Proof.
  intros.
  generalize (NoDup_repeated_bases (Well_formed_hierarchy.bases_no_dup hierarchy_wf H)).
  intro.
  eauto using NoDup_elim.
Qed.

Lemma goal : forall obj ar i h p hp,
    valid_pointer hier (Globals.heap (State.global s2)) (Value.subobject obj ar i h p hp) ->
    forall cn, last p = Some cn ->
      forall c, hier ! cn = Some c ->
        forall l0 b1 l1 b2 l2, map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b) (filter (fun hb : _ * ident =>
          match hb with
            | (Class.Inheritance.Shared, _) => false
            | _ => true
          end
        ) (Class.super c)) = (l0 ++ b1 :: l1 ++ b2 :: l2) ->
        constructed_sibling_before (assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p ++ b1 :: nil))) (State.construction_states s2)) (assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p ++ b2 :: nil))) (State.construction_states s2))
        .
Proof.
 inversion Hs1.
 inversion step; subst; simpl in *; unfold Globals.update in *; simpl in *; subst; try assumption.

(* 11: Sblock Some *)
intros until 1.
symmetry in H1.
unfold Globals.new in H1.
injection H1; intros until 2; subst; simpl in *.
inversion H2; subst; simpl in *.
destruct (peq (obj0) (Globals.next_object gl)).
 rewrite e in H5.
rewrite PTree.gss in H5.
injection H5; intros; subst; simpl in *.
rewrite (construction_states_none _ (Globals.valid_none valid_global (Ple_refl _))).
rewrite (construction_states_none _ (Globals.valid_none valid_global (Ple_refl _))). 
fin.
rewrite PTree.gso in H5.
 2 : assumption.
assert (valid_pointer (Program.hierarchy prog) (Globals.heap gl) (Value.subobject (obj0) ar i h p hp0)).
 econstructor; eauto.
eauto.

(* 10: Sconstructor Kconstrarray *)
intros. 
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (h, p ++ b1 :: nil)))
).
 destruct p.
  discriminate.
 destruct p; discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (h, p ++ b2 :: nil)))
).
 destruct p.
  discriminate.
 destruct p; discriminate.
eauto.

(* 9: Sreturn Kconstrothercells *)
intros.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (h, p ++ b1 :: nil)))
).
 destruct p.
  discriminate.
 destruct p; discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (h, p ++ b2 :: nil)))
).
 destruct p.
  discriminate.
 destruct p; discriminate.
eauto.

(* 8: Sconstructor Kconstr base *)
intros.
destruct k2.
 sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b1 :: nil)))
 ).
  injection e; intros; subst.
  destruct (list_cons_right_inj H6).
  subst.
  sdestruct (
    pointer_eq_dec (A:=A) (obj0, (ar0, i0, (h0, p0 ++ b1 :: nil)))
           (obj0, (ar0, i0, (h0, (p0 ++ b2 :: nil))))
  ).
   injection e0; intros.
   destruct (list_cons_right_inj H7).
   subst.
   apply False_rect; eauto using nodup.
  forward.
 eapply breadth_non_virtual_bases.
 eassumption.
 eassumption.
 eassumption.
 eassumption.
 unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 unfold_ident_in_all.
 rewrite (H16 _ (or_introl _ (refl_equal _))).
 simpl; omega.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b2 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
destruct (list_cons_right_inj H6).
subst.
cut (
 (assoc (pointer_eq_dec (A:=A)) (obj0, (ar0, i0, (h0, p0 ++ b1 :: nil)))
        cs)  = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H7.
 fin.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
apply H13.
assert (l0 ++ b1 :: l1 ++ b2 :: l2 = x3 ++ b2 :: q). 
 unfold_ident_in_all.
 rewrite <- H14.
 rewrite <- H5.
 replace x2 with c0 by congruence.
 trivial.
 generalize (NoDup_repeated_bases (Well_formed_hierarchy.bases_no_dup hierarchy_wf H4)).
 rewrite H5.
 intro.
 replace (l0 ++ b1 :: l1 ++ b2 :: l2) with ((l0 ++ b1 :: l1) ++ b2 :: l2) in H7, H16.
 generalize (NoDup_uniq H16 H7).
 injection 1; intros; subst.
 eauto using in_or_app.
 rewrite app_ass; reflexivity.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b1 :: nil)))
).
 destruct p0.
   discriminate.
 destruct p0; discriminate.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b2 :: nil)))
).
 destruct p0.
   discriminate.
 destruct p0; discriminate.
eauto.

(* 7: Sreturn Kconstrother base *)
intros.
destruct k2.
 sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b1 :: nil)))
 ).
  injection e; intros; subst.
  destruct (list_cons_right_inj H3).
  subst.
  sdestruct (
    pointer_eq_dec (A:=A) (obj0, (ar0, i0, (h0, p0 ++ b1 :: nil)))
           (obj0, (ar0, i0, (h0, (p0 ++ b2 :: nil))))
  ).
   injection e0; intros.
   destruct (list_cons_right_inj H4).
   subst.
   apply False_rect; eauto using nodup.
  forward.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b2 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
destruct (list_cons_right_inj H3).
subst.
cut (
 (assoc (pointer_eq_dec (A:=A)) (obj0, (ar0, i0, (h0, p0 ++ b1 :: nil)))
        cs)  = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H4.
 fin.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
eapply constructed_sibling_before_constructed.
eauto.
unfold_ident_in_all; rewrite H4; simpl; omega.
unfold_ident_in_all; rewrite H4; simpl; omega.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b1 :: nil)))
).
 destruct p0.
  discriminate.
 destruct p0; discriminate.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b2 :: nil)))
).
 destruct p0.
  discriminate.
 destruct p0; discriminate.
eauto.

(* 6: constr base direct non virtual nil *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (h0, p0 ++ b1 :: nil)))
).
 injection e; intros; subst.
 sdestruct (
 pointer_eq_dec (A:=A) (obj0, (ar0, i0, (h0, p0 ++ b1 :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b2 :: nil)))
 ).
  injection e0; intro.
  destruct (list_cons_right_inj H5).
  subst.
  apply False_rect; eauto using nodup.
 forward.
 unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 eapply constructed_sibling_before_none. 
 eauto.
 unfold_ident_in_all; rewrite H7; simpl; omega.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (h0, p0 ++ b2 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
cut (
  (assoc (pointer_eq_dec (A:=A)) (obj0, (ar0, i0, (h0, p0 ++ b1 :: nil)))
        cs) = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H5.
 fin.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
eapply constructed_sibling_before_constructed.
eauto.
unfold_ident_in_all; rewrite H6; simpl; omega.
unfold_ident_in_all; rewrite H6; simpl; omega.

(* Destruction *)

(* 5: destr array cons *)
intros.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i, (h, p ++ b1 :: nil)))
).
 destruct p.
  discriminate.
 destruct p; discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i, (h, p ++ b2 :: nil)))
).
 destruct p.
  discriminate.
 destruct p; discriminate.
eauto.

(* 4: destr field nil *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (h0, p0 ++ b1 :: nil)))
).
 injection e; intros; subst.
 sdestruct (
pointer_eq_dec (A:=A) (obj0, (ar0, i0, (h0, p0 ++ b1 :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b2 :: nil)))
 ).
  injection e0.
  intro.
  destruct (list_cons_right_inj H6).
  subst.
  apply False_rect; eauto using nodup.
 forward.
 unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 eapply constructed_sibling_before_destructed.
 eauto.
 unfold_ident_in_all; rewrite H8; simpl; omega.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (h0, p0 ++ b2 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
cut (
(assoc (pointer_eq_dec (A:=A)) (obj0, (ar0, i0, (h0, p0 ++ b1 :: nil)))
        cs) = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H6.
 fin.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
eapply constructed_sibling_before_constructed.
eauto.
unfold_ident_in_all; rewrite H7; simpl; omega.
unfold_ident_in_all; rewrite H7; simpl; omega.

(* 3: destr *)
intros.
destruct beta.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b1 :: nil)))
 ).
  injection e; intros; subst.
  destruct (list_cons_right_inj H7).
  subst.
  sdestruct (
 pointer_eq_dec (A:=A) (obj0, (ar0, i0, (h0, p0 ++ b1 :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b2 :: nil)))
  ).
   injection e0; intro.
   destruct (list_cons_right_inj H8).
   subst.
   apply False_rect; eauto using nodup.
  unfold state_kind_inv in kind.
  simpl in kind.
  invall; subst.
  unfold_ident_in_all.
  forward.
  apply H14.
  assert (l0 ++ b1 :: l1 ++ b2 :: l2 = rev bases ++ b1 :: rev x3).
   replace (rev bases ++ b1 :: rev x3) with (rev (x3 ++ b1 :: bases)).
   rewrite <- H13.
   rewrite rev_involutive.
   rewrite <- H6.
   replace x2 with c0 by congruence.
   trivial.
  rewrite rev_app.
  simpl.
  rewrite app_ass.
  reflexivity.
 generalize (NoDup_repeated_bases (Well_formed_hierarchy.bases_no_dup hierarchy_wf H5)).
 unfold_ident_in_all.
 rewrite H6.
 intro.
 generalize (NoDup_uniq H19 H17).
 injection 1; intros; subst.
 eapply in_rev_elim.
 rewrite <- H21.
 eauto using in_or_app.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b2 :: nil)))
 ).
 2 : eauto.
 injection e; intros; subst.
 destruct (list_cons_right_inj  H7).
 subst.
 unfold state_kind_inv in kind.
 simpl in kind.
 invall; subst.
 cut (
 assoc (pointer_eq_dec (A:=A)) (obj0, (ar0, i0, (h0, p0 ++ b1 :: nil)))
          cs = Some Constructed
 ).
  unfold_ident.
  intro.
  rewrite H8.
  fin.
 apply H16.
 right.
 assert (l0 ++ b1 :: l1 ++ b2 :: l2 = rev bases ++ b2 :: rev x3).
   replace (rev bases ++ b2 :: rev x3) with (rev (x3 ++ b2 :: bases)).
   unfold_ident_in_all.
   rewrite <- H13.
   rewrite rev_involutive.
   rewrite <- H6.
   replace x2 with c0 by congruence.
   trivial.
  rewrite rev_app.
  simpl.
  rewrite app_ass.
  reflexivity.
 generalize (NoDup_repeated_bases (Well_formed_hierarchy.bases_no_dup hierarchy_wf H5)).
 unfold_ident_in_all.
 rewrite H6.
 intro.
 replace (l0 ++ b1 :: l1 ++ b2 :: l2) with ((l0 ++ b1 :: l1) ++ b2 :: l2) in H8, H17.
 generalize (NoDup_uniq H17 H8).
 injection 1; intros; subst.
 eapply in_rev_elim.
 rewrite <- H21.
 eauto using in_or_app.
 rewrite app_ass.
 reflexivity.
sdestruct (pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b1 :: nil)))
).
 destruct p0.
  discriminate.
 destruct p0; discriminate.
sdestruct (pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (h0, p0 ++ b2 :: nil)))
).
 destruct p0.
  discriminate.
 destruct p0; discriminate.
eauto.

(* 2: destr base direct non virtual nil Kdestrother base *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, hp))
           (obj0, (ar0, i0, (h, p ++ b1 :: nil)))
).
 injection e; intros; subst.
 sdestruct (
 pointer_eq_dec (A:=A) (obj0, (ar0, i0, (h, p ++ b1 :: nil)))
           (obj0, (ar0, i0, (h, p ++ b2 :: nil)))
 ).
  apply False_rect.  
  injection e0.
  intro.
  destruct (list_cons_right_inj H3).
  subst.
  eauto using nodup.
 unfold state_kind_inv in kind; simpl in kind; invall; subst.
 forward.
 eapply constructed_sibling_before_destructed.
 eauto.
 unfold_ident_in_all; rewrite H4; simpl; omega.
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, hp))
           (obj0, (ar0, i0, (h, p ++ b2 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
cut (
   (assoc (pointer_eq_dec (A:=A)) (obj0, (ar0, i0, (h, p ++ b1 :: nil))) cs) = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H3.
 fin.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
eapply constructed_sibling_before_constructed.
eauto.
unfold_ident_in_all; rewrite H4; simpl; omega.
unfold_ident_in_all; rewrite H4; simpl; omega.

(* 1: destr base virtual nil *)
unfold state_kind_inv in kind. 
simpl in kind.
invall; subst.
intros.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, x1 :: nil)))
           (obj0, (ar0, i0, (h, p ++ b1 :: nil)))
).
 destruct p.
  discriminate.
 destruct p; discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, x1 :: nil)))
           (obj0, (ar0, i0, (h, p ++ b2 :: nil)))
).
 destruct p.
  discriminate.
 destruct p; discriminate.
eauto.

Qed.

End Preservation.


 
 

