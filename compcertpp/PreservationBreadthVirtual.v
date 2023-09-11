Load PreservationHeader.

Ltac forward := constructor; simpl; intros; try discriminate; try omegaContradiction.
Ltac fin := forward; reflexivity.

Lemma nodup : forall cn c, (Program.hierarchy prog) ! cn = Some c ->
  forall l0 b1 l1 l2, vborder_list (Program.hierarchy prog) (Class.super c) (l0 ++ b1 :: l1 ++ b1 :: l2) -> False.
Proof.
  intros.
  eapply NoDup_elim.
  eapply vborder_list_no_dup.
  eassumption.
  reflexivity.
Qed.

Lemma goal :  forall obj o,
    (Globals.heap (State.global s2)) ! obj = Some o ->
    forall ar cn n,
      valid_array_path hier cn n (Object.class o) (Object.arraysize o) ar ->
      match last ar with
        | None => n = Object.arraysize o /\ cn = Object.class o
        | Some (_, _, fs) => exists n', n = Zpos n' /\ FieldSignature.type fs = FieldSignature.Struct cn n'
      end ->
      forall i, 0 <= i < n ->
        forall c, hier ! cn = Some c ->
          forall l0 b1 l1 b2 l2, vborder_list hier (Class.super c) (l0 ++ b1 :: l1 ++ b2 :: l2) ->
            constructed_sibling_before (assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b1 :: nil))) (State.construction_states s2)) (assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b2 :: nil))) (State.construction_states s2))
            .
Proof.
 inversion Hs1.
 inversion step; subst; simpl in *; unfold Globals.update in *; simpl in *; subst; try assumption.

(* 11: Sblock Some *)
symmetry in H1.
unfold Globals.new in H1.
injection H1; intros until 2; subst; simpl in *.
intros until 1.
destruct (peq obj (Globals.next_object gl)).
 subst.
 rewrite PTree.gss in H2.
 injection H2; intros; subst; simpl in *.
 rewrite (construction_states_none _ (Globals.valid_none valid_global (Ple_refl _))).
 rewrite (construction_states_none _ (Globals.valid_none valid_global (Ple_refl _))).
 fin.
rewrite PTree.gso in H2; eauto.

(* 10: Sconstructor Kconstrarray *)
intros. 
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil)))
).
 discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b2 :: nil)))
).
 discriminate.
eauto.

(* 9: Sreturn Kconstrothercells *)
intros.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil)))
).
  discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b2 :: nil)))
).
  discriminate.
eauto.

(* 8: Sconstructor Kconstr base *)
intros.
unfold state_kind_inv in kind.
simpl in kind.
destruct k2; invall; subst.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil)))
 ).
  destruct p.
   discriminate.
  destruct p0; discriminate.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b2 :: nil)))
 ).
  destruct p.
   discriminate.
  destruct p0; discriminate.
 eauto.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil)))
).
 injection e; intros; subst.
sdestruct (
pointer_eq_dec (A:=A)
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b2 :: nil)))
).
 apply False_rect.
 injection e0; intros; subst.
 eauto using nodup.
generalize (H18 _ (or_introl _ (refl_equal _))).
intro.
forward.
eapply constructed_sibling_before_none.
eauto.
unfold_ident_in_all.
rewrite H5.
simpl; omega.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b2 :: nil)))
).
 2 : eauto.
cut (
 (assoc (pointer_eq_dec (A:=A))
        (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil))) cs) = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H5.
 forward.
injection e; intros; subst.
inversion H11; subst.
inversion H24; subst.
replace o0 with o in * by abstract congruence.
generalize (valid_array_path_last H3 H5).
intro; subst.
inversion H22; subst.
injection H23; intros; subst.
replace x2 with c0 in * by congruence.
generalize (vborder_list_func H17 H7).
replace (
  l0 ++ b1 :: l1 ++ b2 :: l2
) with (
  (l0 ++ b1 :: l1) ++ b2 :: l2
).
intro.
generalize (NoDup_uniq (vborder_list_no_dup H17) H27).
injection 1; intros; subst.
apply H16.
eauto using in_or_app.
rewrite app_ass.
reflexivity.

(* 7: Sreturn Kconstrother base *)
intros.
generalize (stack _ (or_introl _ (refl_equal _))).
simpl.
intro.
destruct k2;  invall; subst.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil)))
 ).
  destruct p.
   discriminate.
  destruct p; discriminate.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b2 :: nil)))
 ).
  destruct p.
   discriminate.
  destruct p; discriminate.
 eauto.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil)))
).
 forward.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b2 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
cut (
 (assoc (pointer_eq_dec (A:=A))
        (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil))) cs) = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H2.
 forward.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
eapply constructed_sibling_before_constructed.
eauto.
unfold_ident_in_all; rewrite H2; simpl; omega.
unfold_ident_in_all; rewrite H2; simpl; omega.

(* 6: constr base direct non virtual nil *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil)))
).
 injection e; intros; subst.
 sdestruct (
 pointer_eq_dec (A:=A)
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b2 :: nil)))
 ).
  injection e0; intros; subst.
  apply False_rect.
  eauto using nodup.
 forward.
 unfold state_kind_inv in kind.
 simpl in kind.
 intros; invall; subst.
 eapply constructed_sibling_before_none.
 eauto.
 unfold_ident_in_all; rewrite H9; simpl; omega.
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b2 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
cut (
 (assoc (pointer_eq_dec (A:=A))
        (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil))) cs) = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H7.
 forward.
unfold state_kind_inv in kind.
simpl in kind.
invall; subst.
eapply constructed_sibling_before_constructed.
eauto.
unfold_ident_in_all; rewrite H8; simpl; omega.
unfold_ident_in_all; rewrite H8; simpl; omega.

(* Destruction *)

(* 5: destr array cons *)
intros.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i, (Class.Inheritance.Shared, b1 :: nil)))
).
 discriminate.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
           (obj0, (ar0, i, (Class.Inheritance.Shared, b2 :: nil)))
).
 discriminate.
eauto.

(* 4: destr field nil *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil)))
).
 injection e; intros; subst.
 sdestruct (
   pointer_eq_dec (A:=A)
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b2 :: nil)))
 ).
  injection e0; intros; subst.
  apply False_rect.
  eauto using nodup.
 forward.
 unfold state_kind_inv in kind.
 simpl in kind; invall; subst.
 eapply constructed_sibling_before_destructed.
 eauto.
 unfold_ident_in_all; rewrite H10; simpl; omega.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b2 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
cut (
(assoc (pointer_eq_dec (A:=A))
        (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil))) cs) = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H8.
 forward.
unfold state_kind_inv in kind.
simpl in kind; invall; subst.
eapply constructed_sibling_before_constructed.
eauto.
unfold_ident_in_all; rewrite H9; simpl; omega.
unfold_ident_in_all; rewrite H9; simpl; omega.

(* 3: destr *)
unfold state_kind_inv in kind.
simpl in kind.
destruct beta; intros; invall; subst. 
 sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil)))
 ).
  destruct p.
   discriminate.
  destruct p0; discriminate.
 sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b2 :: nil)))
 ).
  destruct p.
   discriminate.
  destruct p0; discriminate.
 eauto.
sdestruct (
pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil)))
).
 injection e; intros; subst.
 sdestruct (
pointer_eq_dec (A:=A)
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b2 :: nil)))
 ).
  injection e0; intros; subst.
  apply False_rect.
  eauto using nodup.
 forward.
 inversion H11; subst.
 inversion H26; subst.
 replace o0 with o in * by abstract congruence.
 generalize (valid_array_path_last H9 H0).
 intro; subst.
 inversion H24; subst.
 injection H25; intros; subst.
 replace x2 with c0 in * by abstract congruence.
 generalize (vborder_list_func H8 H15).
 rewrite rev_app.
 simpl.
 rewrite app_ass.
 simpl.
 intro.
 generalize (NoDup_uniq (vborder_no_dup H8) H29).
 injection 1; intros; subst.
 apply H16.
 apply in_rev_elim.
 rewrite <- H31.
 eauto using in_or_app.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b2 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
cut (
 (assoc (pointer_eq_dec (A:=A))
        (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil))) cs) = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H6.
 forward.
apply H18.
right.
 inversion H11; subst.
 inversion H25; subst.
 replace o0 with o in * by abstract congruence.
 generalize (valid_array_path_last H6 H0).
 intro; subst.
 inversion H23; subst.
 injection H24; intros; subst.
 replace x2 with c0 in * by abstract congruence.
 generalize (vborder_list_func H8 H15).
 rewrite rev_app.
 simpl.
 rewrite app_ass.
 simpl.
 revert H8.
 replace 
   (l0 ++ b1 :: l1 ++ b2 :: l2)
   with 
     ((l0 ++ b1 :: l1) ++ b2 :: l2)
     .
 intros.
 generalize (NoDup_uniq (vborder_no_dup H8) H28).
 injection 1; intros; subst.
 apply in_rev_elim.
 rewrite <- H31.
 eauto using in_or_app.
 rewrite app_ass.
 reflexivity.

(* 2: destr base direct non virtual nil Kdestrother base *)
intros.
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, hp))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil)))
).
 injection e; intros; subst.
 sdestruct (
 pointer_eq_dec (A:=A)
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b2 :: nil)))
 ).
  injection e0; intros; subst.
  apply False_rect.
  eauto using nodup.
forward.
revert kind.
unfold state_kind_inv; simpl.
intros; invall; subst.
eapply constructed_sibling_before_destructed.
eauto.
unfold_ident_in_all.
rewrite H7.
simpl; omega.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, hp))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b2 :: nil)))
).
 2 : eauto.
injection e; intros; subst.
cut (
(assoc (pointer_eq_dec (A:=A))
        (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil))) cs) = Some Constructed
).
 unfold_ident.
 intro.
 rewrite H5.
 forward.
revert kind.
unfold state_kind_inv; simpl.
intros; invall; subst.
eapply constructed_sibling_before_constructed.
eauto.
unfold_ident_in_all;rewrite H6;simpl; omega.
unfold_ident_in_all;rewrite H6;simpl; omega.

(* 1: destr base virtual nil *)
unfold state_kind_inv in kind. 
simpl in kind.
invall; subst.
intros.
sdestruct (pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, x1 :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b1 :: nil)))
).
 discriminate.
sdestruct (pointer_eq_dec (A:=A)
           (obj, (ar, i, (Class.Inheritance.Repeated, x1 :: nil)))
           (obj0, (ar0, i0, (Class.Inheritance.Shared, b2 :: nil)))
).
 discriminate.
eauto.

Qed.

End Preservation.


 
 

