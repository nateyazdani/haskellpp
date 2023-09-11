Load PreservationHeader.

Lemma goal :
  state_kind_inv prog s2 (* aux_constr_state2 *).
Proof.
 inversion Hs1.
 Opaque Globals.get_field Globals.put_field concat cs_le_dec Zminus.
 inversion step; subst; unfold state_kind_inv in *; unfold Globals.update in *; simpl in *; subst; try abstract tauto.

 (* 28 Kreturnfromcall *)
 destruct stk; try tauto.
 destruct (stack2 _ nil _ (refl_equal _)). 
 generalize (H0 I).
 destruct t; simpl; tauto.

 (* 27 Sblock Some: allocate new object *)
split; auto.
 generalize H1.
 unfold Globals.new.
 injection 1; intros; subst; simpl in *.
 rewrite PTree.gss.
 esplit.
 split.
  reflexivity.
 simpl.
 split.
  constructor; omega.
 split.
  auto.
 split.
  omega.
 split.
  intros; omegaContradiction.
 intros.
 eapply construction_states_none.
 eapply Globals.valid_none.
 assumption.
 apply Ple_refl.

 (* 26 constr_array nil *)
 destruct stk; try tauto.
 destruct (stack2 _ nil _ (refl_equal _)).
 generalize (H I).
destruct t; simpl; tauto.

 (* 25 constr_array cons *)
destruct kind.
destruct H0.
destruct H0.
esplit.
split.
 eassumption.
destruct H2.
split.
 assumption.
destruct H3.
split.
 assumption.
destruct H4.
split.
 omega.
assumption.

(* 24 Sconstructor Kconstrarray *)
 sdestruct (pointer_eq_dec (A:=A)
   (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
   (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
 ); try congruence.
 esplit.
 split.
  reflexivity.
 exists I.
 invall; subst.
 asplit.
 econstructor.
  eassumption.
  econstructor.
   eassumption. 
  assumption.
  assumption.
  eapply path_trivial.
  congruence.
 esplit.
 split.
  reflexivity.
 esplit.
 split.
  eassumption.
 split.
  trivial.
 split; auto.
 exists nil.
 split.
  simpl.
  assumption.
 split.
  simpl; tauto.
 split.
  intros.
  sdestruct (pointer_eq_dec (A:=A)  
    (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
    (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
  ); try congruence.
  assert (is_virtual_base_of hier b cn) by abstract (eauto using vborder_list_virtual_base).
  eapply construction_states_virtual_bases.
  eassumption.
  eassumption.
  assumption.
  omega.
  assumption.
  eapply H10.
  omega.
  intros.
  sdestruct (
    pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: b :: nil)))
  ); try congruence.
  change (cn :: b :: nil) with ((cn :: nil) ++ b :: nil).
  eapply construction_states_direct_non_virtual_bases.
  eassumption.
  reflexivity.
  eassumption.
  assumption.
  eapply H10.
  omega.

(* 23 Kconstrothercells *) 
split.
destruct (stack _ (or_introl _ (refl_equal _))).
simpl in H.
destruct H.
esplit.
split.
 eassumption.
destruct H0.
split.
 assumption.
destruct H1.
split.
 assumption.
destruct H2.
split.
 omega.
bintro.
sdestruct (
 pointer_eq_dec (A:=A)
          (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
          (obj, (ar, b, (Class.Inheritance.Repeated, cn :: nil)))
).
 split; try tauto.
 replace b with i in * by abstract congruence.
 intros; abstract omegaContradiction.
assert (i <> b) by abstract congruence.
split; intros. 
inversion H5.
assert (b < i) by abstract omega.
assert (i < i + 1) by abstract omega.
eapply constructed_sibling_before_constructed.
eapply breadth_arrays.
eassumption.
eassumption.
assumption.
assumption.
eassumption.
omega.
destruct H3; rewrite H3; simpl; omega.
destruct H3; rewrite H3; simpl; omega.
inversion H5.
inversion H2.
assert (i < b) by abstract omega.
eapply breadth_arrays.
eassumption.
eassumption.
assumption.
eassumption.
eassumption.
omega.
unfold_ident_in_all; destruct H3; rewrite H3; simpl; omega.
destruct (stack2 _ nil _ (refl_equal _)).
generalize (H0 (fun x => x)).
destruct stk; tauto.

(* 22 constr cons *)
destruct hp.
invall; subst.
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
destruct k; invall; subst; simpl in *.
 (* base *)
 split.
  trivial.
 destruct k2.
  tauto.
 destruct stk; try tauto.
 destruct t0; simpl in *; try tauto;
 invall; subst; simpl in *; injection H4; intros; subst; eauto 7.
(* field *)
destruct k2.
invall; subst.
revert H.
case_eq (FieldSignature.type b); try (intros; contradiction).
eauto.

(* 21 constr field struct *)
destruct hp.
invall; subst.
split; eauto 8.
inversion H2; subst.
esplit.
split.
 eassumption.
inversion H14; subst.
generalize (path_last H12).
intros.
replace x1 with to in * by abstract congruence.
split.
eapply valid_array_path_concat.
 eassumption.
econstructor.
assumption.
assumption.
eassumption.
eassumption.
rewrite H5.
eauto using in_or_app.
eassumption.
econstructor.
compute; congruence.
omega.
split.
 rewrite last_complete.
 eauto.
split.
split.
 omega.
compute; congruence.
split.
 intros; omegaContradiction.
intros.
eapply construction_states_structure_fields.
 eassumption.
 eassumption.
 eassumption.
 rewrite H5.
 eauto using in_or_app.
 eassumption.
 assumption.
 eauto.

(* 20 Kconstr base *)
invall.
subst.
sdestruct (
  (pointer_eq_dec (A:=A)
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
)); try abstract congruence.
clear e.
esplit.
split.
 reflexivity.
destruct k2; invall.
(* case non-virtual *)
assert (is_some (last (p ++ b :: nil))).
 rewrite last_complete.
 exact I.
exists H10.
 assert (In (Class.Inheritance.Repeated, b) (Class.super x2)). 
 eapply in_map_bases_elim.
 rewrite H7.
 eauto using in_or_app.
 asplit.
 inversion H4; subst.
 inversion H19; subst.
 econstructor.
 eassumption.
 trivial.
 econstructor.
 eassumption.
 assumption.
 assumption.
 generalize (path_last H17).
 intros.
 replace to with x1 in * by abstract congruence.
 eapply path_concat with (p1 := p) (p2 := x1 :: b :: nil).
 eassumption.
 eleft.
 reflexivity.
 change (x1 :: b :: nil) with ((x1 :: nil) ++ b :: nil).
 reflexivity.
 simpl.
 rewrite H6.
 sdestruct (
   In_dec super_eq_dec (Class.Inheritance.Repeated, b) (Class.super x2)
 ).
  rewrite H8.
  trivial.
 contradiction.
 Transparent concat. simpl. Opaque concat.
 rewrite H18.
 destruct (peq x1 x1).
  trivial.
 congruence.
esplit.
split.
eapply last_complete.
esplit.
split.
eassumption.
split; auto.
split; auto.
exists nil.
split.
 reflexivity.
split.
 simpl; tauto.
split.
 intros.
 sdestruct (
   pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
   (obj, (ar, i, (h, (p ++ b :: nil) ++ b0 :: nil)))
 ).
  injection e.
  intros.
  assert (length ( p ++ b :: nil) = length ((p ++ b :: nil) ++ b0 :: nil)) by abstract congruence.
  repeat rewrite app_length in H16.
  simpl in H16.
  omegaContradiction.
 eapply construction_states_direct_non_virtual_bases.
 eassumption.
 eapply last_complete.
 eassumption.
 eauto using in_map_bases_elim.
 eauto.
 intros; subst.
 sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (Class.Inheritance.Repeated, p ++ b :: nil)))
         (obj, (ar, i, (Class.Inheritance.Shared, b0 :: nil)))
); try abstract congruence.
 inversion H13; subst.
 inversion H22; subst.
 inversion H20; subst.
 rewrite H15 in H21.
 injection H21; intros; subst.
 destruct p.
  contradiction.
 injection H15.
 intros; subst.
 eauto.
(* case virtual *)
subst.
inversion H4; subst.
inversion H17; subst.
generalize (path_last H15).
injection 1.
intro; subst.
inversion H15; subst.
injection H18; intros; subst.
exists I.
asplit.
 econstructor. 
 eassumption.
 trivial.
 econstructor.
  eassumption.
 assumption.
 assumption.
 econstructor.
 eapply vborder_list_virtual_base.
 eassumption.
 eassumption.
 eapply in_or_app.
 eright.
 eleft.
 reflexivity.
 eleft with (lt := nil).
 reflexivity.
 reflexivity.
 simpl.
 rewrite H8.
 trivial.
esplit.
split.
 reflexivity.
esplit.
split.
 eassumption.
split.
 trivial.
split; eauto.
exists nil.
split.
 reflexivity.
split.
 simpl; intros; contradiction.
split.
 simpl; intros.
 sdestruct (
 pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
         (obj,
         (ar, i, (Class.Inheritance.Shared, b :: b0 :: nil)))
 ).
  discriminate.
 change (b :: b0 :: nil) with ((b :: nil) ++ b0 :: nil).
 eapply construction_states_direct_non_virtual_bases.
 eassumption.
 reflexivity.
 eassumption.
 eauto using in_map_bases_elim.
 eauto.
 intro; discriminate.
  
(* 19 Kconstrother base *)
destruct k2.
(* case non-virtual *)
destruct (
@pointer_eq_dec A
               (@pair ident
                  (prod (prod (array_path A) Z)
                     (prod Class.Inheritance.t (list ident))) obj
                  (@pair (prod (array_path A) Z)
                     (prod Class.Inheritance.t (list ident))
                     (@pair (array_path A) Z ar i)
                     (@pair Class.Inheritance.t (list ident) h
                        (@app ident p (@cons ident b (@nil ident))))))
               (@pair ident
                  (prod (prod (array_path A) Z)
                     (prod Class.Inheritance.t (list ident))) obj
                  (@pair (prod (array_path A) Z)
                     (prod Class.Inheritance.t (list ident))
                     (@pair (array_path A) Z ar i)
                     (@pair Class.Inheritance.t (list ident) h p)))
).
 apply False_rect.
 injection e; intros.
 assert (length (p ++ b :: nil) = length p) by abstract congruence.
 rewrite app_length in H0.
 simpl in H0.
 omegaContradiction.
invall; subst.
generalize (stack _ (or_introl _ (refl_equal _))).
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
split; auto.
exists (x4 ++ b :: nil).
split.
rewrite app_ass.
simpl.
assumption.
split.
intros.
destruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
         (obj, (ar, i, (h, p ++ b0 :: nil)))
); try trivial.
destruct (in_app_or _ _ _ H3).
 destruct (In_split _ _ H7).
 destruct H10.
 subst.
 rewrite app_ass in H8.
 simpl in H8.
 eapply constructed_sibling_before_constructed.
 eapply breadth_non_virtual_bases.
 eassumption.
 eassumption.
 eassumption.
 eassumption.
 destruct H9; rewrite H9; simpl; abstract omega.
 destruct H9; rewrite H9; simpl; abstract omega.
destruct H7.
 congruence.
contradiction.
split.
intros.
destruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
         (obj, (ar, i, (h, p ++ b0 :: nil)))
).
 assert (last (p ++ b0 :: nil) = last (p ++ b :: nil)) by abstract congruence.
 repeat rewrite last_complete in H7.
 injection H7; intros; subst.
 apply False_rect.
 assert (NoDup ((x4 ++ b :: nil) ++ q)) by abstract (
  rewrite app_ass;
  simpl;
  rewrite <- H8;
  eapply NoDup_repeated_bases;
  eauto using Well_formed_hierarchy.bases_no_dup
 ).
 eapply NoDup_app.
 eassumption.
 2 : eassumption.
 eauto using in_or_app.
destruct (In_split _ _ H3).
destruct H7.
subst.
eapply constructed_sibling_before_none.
eapply breadth_non_virtual_bases.
eassumption.
eassumption.
eassumption.
eassumption.
destruct H9; rewrite H7; simpl; abstract omega.
intros.
destruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p ++ b :: nil)))
         (obj, (ar, i, (Class.Inheritance.Shared, b0 :: nil)))
).
 trivial.
subst.
assert (is_some (last (cn' :: P' ++ b :: nil))).
 change (cn' :: P' ++ b :: nil) with ((cn' :: P') ++ b :: nil).
 rewrite last_complete.
 exact I.
inversion H4; subst.
inversion H16; subst.
generalize (path_last H14).
intro.
replace x2 with to in * by abstract congruence.
assert (
 valid_pointer (Program.hierarchy prog) (Globals.heap gl)
         (Value.subobject (obj) ar i Class.Inheritance.Repeated (cn' :: P' ++ b :: nil) H3)
).
 econstructor.
  eassumption.
  trivial.
 econstructor.
  eassumption.
  assumption.
  assumption.
 eapply path_concat.
 eassumption.
 eleft with (lf := b :: nil) (lt := to :: nil).
 reflexivity.
 simpl ; reflexivity.
 simpl.
 rewrite H6.
 sdestruct (
In_dec super_eq_dec (Class.Inheritance.Repeated, b) (Class.super x3)
 ).
  generalize (Well_formed_hierarchy.complete hierarchy_wf H6 i0).
  destruct ((Program.hierarchy prog) ! b); abstract congruence.
 destruct n1.
 eapply in_map_bases_elim.
 rewrite H8.
 eauto using in_or_app.
 change (cn' :: P' ++ b :: nil) with ((cn' :: P') ++ b :: nil).
 eapply last_concat.
 assumption.
 eapply constructed_sibling_before_constructed.
 eapply breadth_virtual_nonempty_non_virtual_bases.
 eassumption.
 simpl; reflexivity.
 eassumption.
 reflexivity.
 assumption.
 simpl in H9; destruct H9; rewrite H9; simpl; omega.
 simpl in H9; destruct H9; rewrite H9; simpl; omega.
generalize (stack2 _ nil _ (refl_equal _)).
unfold stack2_inv.
simpl.
destruct 1.
generalize (H7  (fun x => x)).
destruct stk; tauto.
(* case virtual *)
generalize (stack _ (or_introl _ (refl_equal _))).
simpl.
intros; invall; subst.
generalize (stack2 _ nil _ (refl_equal _)).
unfold stack2_inv.
simpl.
destruct 1.
generalize (H4 (fun x => x)).
intro.
destruct stk.
 tauto.
destruct H5.
sdestruct (
pointer_eq_dec (A:=A)
           (obj,
           (ar, i, (Class.Inheritance.Shared, b :: nil)))
           (obj,
           (ar, i, (Class.Inheritance.Repeated, x1 :: nil)))
).
 discriminate.
esplit.
split.
eassumption.
esplit.
split.
 eassumption.
esplit.
split.
 reflexivity.
simpl in *.
esplit.
split.
 eassumption.
split; auto.
split; auto.
exists (x3 ++ b :: nil).
split.
 rewrite app_ass.
 simpl.
 assumption.
inversion H1; subst.
inversion H18; subst.
generalize (maximize_array_path H12).
destruct 1.
destruct H17.
destruct H19.
inversion H16; subst.
injection H21; intros; subst.
generalize (path_last H16).
injection 1; intro; subst.
split.
intros.
sdestruct (
 pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
         (obj,
         (ar, i, (Class.Inheritance.Shared, b0 :: nil)))
).
 trivial.
destruct (in_app_or _ _ _ H25). 
 destruct (In_split _ _ H26).
 destruct H27.
 subst.
 eapply constructed_sibling_before_constructed.
 eapply breadth_virtual_bases. 
 eassumption.
 eassumption.
 assumption.
 abstract omega.
 eassumption.
 rewrite app_ass in H7.
 simpl in H7.
 eassumption.
 rewrite H6.
 simpl; abstract omega.
 rewrite H6; simpl; abstract omega.
destruct H26.
 congruence.
contradiction.
split.
 intros.
 sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
         (obj,
         (ar, i, (Class.Inheritance.Shared, b0 :: nil)))
 ).
 apply False_rect.
 replace b0 with b in * by abstract congruence.
 assert (NoDup ((x3 ++ b :: nil) ++ q)) by abstract (
  rewrite app_ass;
  simpl;
  eauto using vborder_no_dup
 ).
 eapply NoDup_app.
 eassumption.
 2 : eassumption.
 eauto using in_or_app.
 destruct (In_split _ _ H25).
 destruct H26.
 subst.
 eapply breadth_virtual_bases. 
 eassumption.
 eassumption.
 assumption.
 abstract omega.
 eassumption.
 eassumption.
 unfold_ident_in_all; rewrite H6.
 simpl; abstract omega.
intros.
sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
         (obj,
         (ar, i,
         (Class.Inheritance.Repeated, to :: b0 :: nil)))
); try congruence.
eapply breadth_virtual_non_virtual_bases.
eassumption.
eassumption.
assumption.
abstract omega.
eapply vborder_list_virtual_base.
eassumption.
eassumption.
eapply in_or_app; right; left; trivial.
eassumption.
assumption.
unfold_ident_in_all.
rewrite H6.
simpl; abstract omega.

(* 18 constr_virtual_bases nil *)
invall; subst.
destruct stk; try tauto.
assert (h = Class.Inheritance.Repeated /\ p = x1 :: nil).
 destruct t; simpl in *; try tauto;
 invall; subst;
 simpl in *; replace class with x1 by abstract congruence; auto.
invall; subst.
esplit.
split.
 eassumption.
esplit.
split.
 eassumption.
injection H.
intros; subst.
replace x2 with c in * by abstract congruence.
esplit.
split.
 reflexivity.
esplit.
split.
 eassumption.
split; auto.
split.
(* construction states *)
exists nil.
split.
 reflexivity.
split.
 simpl; tauto.
split.
 intros.
 simpl.
 eapply H11.
 eauto using in_map_bases_elim.
injection 2; intros; subst.
eapply H7.
rewrite app_nil_end.
eapply virtual_base_vborder_list.
eassumption.
eassumption.
assumption.
(* chaining *)
destruct t; simpl in *; tauto.

(* 17 constr_non_virtual_bases nil *)
sdestruct (pointer_eq_dec (A:=A) (obj, (ar, i, (h, p))) (obj, (ar, i, (h, p)))
).
 2 : congruence.
esplit.
split.
reflexivity.
invall; subst.
assert (last p = Some cn) by assumption.
assert (last p = Some x1) by assumption.
replace x1 with cn in * by abstract congruence.
replace x2 with c in * by abstract congruence.
esplit.
split.
 eassumption.
esplit.
split.
 eassumption.
esplit.
split.
 eassumption.
split; auto.
split; auto.
exists nil.
split.
 reflexivity.
split.
 simpl; tauto.
intros.
eapply construction_states_fields.
eassumption.
eassumption.
eassumption.
assumption.
rewrite H2.
apply cs_le_refl.

(* 16 constr_fields, scalar no init *)
invall; subst.
simpl.
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
split; auto.
exists (x3 ++ fs :: nil).
split.
 rewrite app_ass.
 simpl.
 assumption.
split.
 intros.
 destruct (
 aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj, ar, i, (h, p), fs0)
 ).
  trivial.
 destruct (in_app_or _ _ _ H1).
  eauto.
 destruct H9.
  congruence.
 contradiction.
intros.
destruct (
 aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj, ar, i, (h, p), fs0)
).
 replace fs0 with fs in * by abstract congruence.
 apply False_rect.
 assert (NoDup ((x3 ++ fs :: nil) ++ q)) by abstract (
  rewrite app_ass;
  simpl;
  rewrite <- H6;
  eapply Well_formed_hierarchy.fields_no_dup;
  eassumption
 ).
 eapply NoDup_app.
 eassumption.
 eapply in_or_app.
 right.
 left.
 reflexivity.
 assumption.
eauto.

(* 15 Sinitscalar Kconstrfield *)
invall; subst.
esplit.
split.
 eassumption.
esplit.
asplit.
 eassumption.
esplit.
split.
 eassumption.
esplit.
split.
 eassumption.
split; auto.
split.
replace x1 with cn in * by abstract congruence.
exists (x3 ++ fs :: nil).
split.
 rewrite app_ass.
 simpl.
 assumption.
split.
intros.
cut (
 (if aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj, ar, i, (h, p), fs0)
    then Some Constructed
    else
     assoc aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs0)
       auxcs) = Some Constructed
); try tauto.
destruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj, ar, i, (h, p), fs0)
); try tauto.
destruct (in_app_or _ _ _ H11).
 eauto.
destruct H13.
 congruence.
contradiction.
intros.
cut (
 (if aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj, ar, i, (h, p), fs0)
    then Some Constructed
    else
     assoc aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs0)
       auxcs) = None
); try tauto.
destruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj, ar, i, (h, p), fs0)
).
 apply False_rect.
 replace fs0 with fs in * by abstract congruence.
 assert (NoDup ((x3 ++ fs :: nil) ++ q)) by abstract (
  rewrite app_ass;
  simpl;
  rewrite <- H10;
  eauto using Well_formed_hierarchy.fields_no_dup
 ).
 eauto using NoDup_app, in_or_app.
eauto.
destruct (stack2 _ nil _ (refl_equal _)). 
generalize (H13 (fun x => x)).
destruct stk; tauto.

(* 14 constr_array n n Kconstrotherfields *)
generalize (stack _ (or_introl _ (refl_equal _))).
simpl.
destruct 1.
invall; subst.
replace x5 with x1 in * by abstract congruence.
replace x6 with x2 in * by abstract congruence.
assert (x7 = x3) by abstract (
 apply app_reg_r with (fs :: q);
 congruence
).
subst.
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
split; auto.
split.
 destruct (Z_eq_dec n n); try congruence.
 clear e.
 simpl.
 exists (x3 ++ fs :: nil).
 asplit.
  rewrite app_ass.
  simpl.
  assumption.
 split.
 intros.
  sdestruct (
aux_constr_state_key_eq_dec (obj', ar', i', (h, p), fs)
         (obj', ar', i', (h, p), fs0)
  ); try congruence.
  destruct (in_app_or _ _ _ H7).
   destruct (In_split _ _ H10).
   destruct H18.
   subst.
   rewrite app_ass in H17.
   eapply constructed_sibling_before_constructed.
   eapply breadth_fields.
   eassumption.
   eassumption.
   eassumption.
   eassumption.
   rewrite H6.
   simpl; abstract omega.
   rewrite H6; simpl; abstract omega.
  destruct H10.
   congruence.
  contradiction.
 intros.
 sdestruct (
 aux_constr_state_key_eq_dec (obj', ar', i', (h, p), fs)
         (obj', ar', i', (h, p), fs0)
 ).
  replace fs0 with fs in * by abstract congruence.
  assert (NoDup ((x3 ++ fs :: nil) ++ q)) by abstract (
   rewrite <- H;
   eauto using Well_formed_hierarchy.fields_no_dup
  ).
  edestruct NoDup_app.
   eassumption.
  2 : eassumption.
  eauto using in_or_app.
 rewrite app_ass in H.
 destruct (In_split _ _ H7).
 destruct H10; subst.
 simpl in H.
 eapply breadth_fields.
 eassumption.
 eassumption.
 eassumption.
 eassumption.
 rewrite H6; simpl; abstract omega.
rewrite last_complete in H9.
invall; subst.
generalize (stack2 _ nil _ (refl_equal _)).
unfold stack2_inv.
simpl.
destruct 1.
generalize (H7 (fun x => x)).
destruct stk; tauto.

(* 13 constr_fields_nil : on arrive au corps du constructeur *)
destruct stk ; try tauto.
invall; subst.
rewrite <- app_nil_end in H4.
subst.
generalize (stack _ (or_introl _ (refl_equal _))).
generalize (stack_state _ _ (refl_equal _)).
revert H6.
destruct t; simpl; try tauto.
(* two subcases *) 
 destruct inhpath.
 intros; invall; subst.
 destruct k; try tauto.
 invall; subst.
 destruct kind; invall; subst.
 split.
  assumption.
 rewrite last_complete in H2.
 injection H2; intros; subst.
 eauto.
split.
assumption.
injection H2; intros; subst.
eauto.
intros; invall; subst.
injection H2; intros; subst.
eauto.

(* Destruction *)

(* 12 destr_array *)
split.
sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
         (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
).
  trivial.
 destruct n.
  trivial.
 destruct kind.
 destruct H4.
 destruct H4.
 destruct H4.
 destruct H6. 
 destruct H7.
 destruct H8.
 inversion H8.
 exists hp.
 generalize (valid_object_classes _ _ H4).
 intro.
 generalize (Well_formed_hierarchy.array_path_valid hierarchy_wf H6 H12).
 intro.
 case_eq (hier ! cn); try abstract congruence.
 intros.
 asplit.
  eright.
  eassumption.
  esplit.
   eassumption.
   assumption.
   assumption.
  eleft with (lt := nil).
  reflexivity.
  reflexivity.
  simpl.
  rewrite H14.
  trivial.
 esplit.
 split.
  reflexivity.
 esplit.
 split.
  eassumption.
 destruct (Z_eq_dec j (-1)).
  abstract omegaContradiction.
 destruct H9.
 assert (0 <= j <= j)%Z by abstract omega.
 generalize (H9 _ H17).
  intros.
  eapply construction_states_fields.
  eassumption.
  reflexivity.
  eassumption.
  eassumption.
  assumption.

(* 11 : Sreturn Kdestr (back from destructor) *)
destruct kind.
esplit.
split.
 eassumption.
invall.
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
unfold_ident_in_all.
replace x0 with cn in * by abstract congruence.
replace x1 with c in * by abstract congruence.
split.
 exists nil.
 simpl.
 split.
 rewrite H1.
 rewrite rev_involutive.
 trivial.
split.
 intros; contradiction.
intros.
destruct (In_rev l fs).
generalize (H8 H4).
rewrite <- H1.
eauto.
generalize (stack2 _ nil _ (refl_equal _)).
unfold stack2_inv.
simpl.
destruct 1.
generalize (H8 (fun x => x)).
destruct stk.
 intro; assumption.
destruct 1; assumption.

(* 10 : scalar field destruction *)
invall; subst.
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
rewrite H5.
split.
 exists (x3 ++ fs :: nil).
 split.
 rewrite app_ass; reflexivity.
 split.
 intros.
 sdestruct (
aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj, ar, i, (h, p), fs0)
 ).
  trivial.
 destruct (in_app_or _ _ _ H0).
  eauto.
 inversion H8; try abstract congruence; contradiction.
 intros.
 sdestruct (
 aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj, ar, i, (h, p), fs0)
 ).
  apply False_rect.
  injection e; intros; subst.
  generalize (NoDup_rev (Well_formed_hierarchy.fields_no_dup hierarchy_wf H4)).
  rewrite H5.
  intro.
  generalize (NoDup_app_right H8).
  inversion 1.
   contradiction.
 eauto.
assumption.

(* 9 structure array field destruction *)
invall; subst.
inversion H2; subst.
inversion H14; subst.
generalize (path_last H12).
intro.
replace x1 with to in * by abstract congruence.
assert (In fs (Class.fields x2)).
 rewrite <- rev_involutive.
 rewrite H5.
 destruct (In_rev (x3 ++ fs :: l) fs).
 eauto using in_or_app.
asplit.
esplit.
esplit.
split.
 eassumption.
asplit.
 eapply valid_array_path_concat.
 eassumption.
 econstructor.
 assumption.
 assumption.
 eassumption.
 eassumption.
 assumption.
 eassumption.
 econstructor.
 2 : eapply Zle_refl.
 compute.
 congruence.
rewrite last_complete.
split.
 esplit.
 split.
  reflexivity.
 assumption.
split.
 cut (0 <= Zpos n)%Z.
  Transparent Zminus. unfold Zminus.  abstract omega.
  compute; congruence.
 generalize (H9 _ (or_introl _ (refl_equal _))).
 intros.
 generalize (construction_states_structure_fields _ _ _ _ _ _ H2 _ H3 _ H4 _ H15 _ _ H).
 intro.
 unfold Zminus.
 split.
  intros.
  assert (0 <= j < Zpos n)%Z by abstract omega.
  eauto using constructed_field_array_cell_constructed.
 intros.
 abstract omegaContradiction.
eauto 8.

(* 8 Kdestrother field *)
destruct hp'.
invall; subst.
generalize (stack _ (or_introl _ (refl_equal _))).
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
split.
 exists (x8 ++ fs :: nil).
 split.
  rewrite app_ass.
  assumption.
 split.
  intros.
  sdestruct (
 aux_constr_state_key_eq_dec (obj', ar', i', (t, l0), fs)
         (obj', ar', i', (t, l0), fs0)
  ).
   trivial.
  destruct (in_app_or _ _ _ H3).
   destruct (In_split _ _ H14).
   destruct H17.
   subst.
   assert (Class.fields x7 = rev l ++ fs :: rev x9 ++ fs0 :: rev x4).
    rewrite <- (rev_involutive (Class.fields x7)).
    rewrite H15.
    repeat (rewrite rev_app;  simpl).    
    repeat (rewrite app_ass;  simpl).
    reflexivity.
   eapply breadth_fields.
   eassumption.
   eassumption.
   eassumption.
   eassumption.
   rewrite H16.
   simpl; abstract omega.
  inversion H14; try abstract congruence; contradiction.
 intros.
 sdestruct (
aux_constr_state_key_eq_dec (obj', ar', i', (t, l0), fs)
         (obj', ar', i', (t, l0), fs0)
 ).
  apply False_rect.
  injection e; intros; subst.
  generalize (Well_formed_hierarchy.fields_no_dup hierarchy_wf H13).
  intros.
  generalize (NoDup_rev H14).
  rewrite H15.
  intros.
  generalize (NoDup_app_right H17).
  inversion 1; abstract congruence.
 destruct (In_split _ _ H3).
 destruct H14; subst.
 assert (
   Class.fields x7 = rev x9 ++ fs0 :: rev x4 ++ fs :: rev x8
 ).
  rewrite <- (rev_involutive (Class.fields x7)).
  rewrite H15.
  repeat (rewrite rev_app;  simpl).    
  repeat (rewrite app_ass;  simpl).
  reflexivity.  
 eapply constructed_sibling_before_constructed.
 eapply breadth_fields.
 eassumption.
 eassumption.
 eassumption.
 eassumption.
 rewrite H16.
 simpl; abstract omega.
 rewrite H16.
 simpl; abstract omega.
generalize (stack2 _ nil _ (refl_equal _)).
unfold stack2_inv.
simpl.
destruct 1.
 generalize (H14 (fun x => x)).
destruct stk.
 intro; assumption.
destruct 1; assumption.

(* 7 : destr field nil *)
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p))) (obj, (ar, i, (h, p)))
).
 2 : abstract congruence.
invall; subst.
replace x1 with cn in * by abstract (unfold_ident_in_all; congruence).
replace x2 with c in * by abstract congruence.
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
split.
 trivial.
split; try assumption.
exists nil.
simpl.
split.
rewrite <- (rev_involutive bases).
rewrite H1.
trivial.
split.
 intros; contradiction.
split.
 intros.
 sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj, (ar, i, (h, p ++ b :: nil)))
 ).
  injection e0.
  intro.
  generalize (refl_equal (length p)).
  rewrite H10 at 1.
  rewrite app_length.
  simpl.
  intro.
  abstract omegaContradiction.
 eapply construction_states_direct_non_virtual_bases.
 eassumption.
 eassumption.
 eassumption.
 eapply in_map_bases_elim.
 rewrite <- H1.
 eapply in_rev_intro.
 assumption.
 rewrite H3. simpl; abstract omega.
 rewrite H3; apply cs_le_refl.
intros; subst.
sdestruct (
 pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn' :: p')))
         (obj, (ar, i, (Class.Inheritance.Shared, b :: nil)))
).
 discriminate.
inversion H4; subst.
inversion H17; subst.
destruct (maximize_array_path H2); invall; subst.
inversion H15; subst.
injection H19; intros; subst.
destruct lt.
 injection H21; intros; subst.
 unfold_ident_in_all.
 eapply construction_states_virtual_bases.
 eassumption.
 eassumption.
 assumption.
 abstract omega.
 assumption.
 rewrite H3. simpl. abstract omega.
 rewrite H3. simpl. abstract omega.
injection H21; intros; subst.
eapply constructed_sibling_before_constructed.
eapply breadth_virtual_nonempty_non_virtual_bases. 
eassumption.
simpl; reflexivity.
eassumption.
reflexivity.
assumption.
unfold_ident_in_all; rewrite H3; simpl; abstract omega.
unfold_ident_in_all; rewrite H3; simpl; abstract omega.

(* 6 : destr base : entering destructor *)
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
).
 2 : abstract congruence.
split.
 trivial.
invall; subst.
inversion H5; subst.
inversion H14; subst.
generalize (path_last H12).
intros.
replace x1 with to in * by abstract congruence.
exists hp'.
asplit.
 econstructor.
 eassumption.
 trivial.
 eapply valid_relative_pointer_intro with (pto := b) (ato := through). 
 eassumption.
 assumption.
 assumption.
 destruct beta; invall; subst.
  (* case direct non virtual *)
  eapply path_concat with (p2 := to :: b :: nil).
  eassumption.
  eleft with (lt := to :: nil).
   reflexivity.
   reflexivity.
   simpl.
   rewrite H7.
   rewrite H1.
   sdestruct (
     In_dec super_eq_dec (Class.Inheritance.Repeated, b) (Class.super x2)
   ).
    trivial.
   destruct n.
   eapply in_map_bases_elim.
   eapply in_rev_elim.
   rewrite H15.
   eauto using in_or_app.
  Transparent concat. simpl. rewrite H6. destruct (peq to to). trivial. destruct n. trivial. 
 (* case virtual *)
 assert (In b (rev (x ++ b :: bases))).
 eapply In_rev.
 rewrite rev_involutive.
 eauto using in_or_app. 
 generalize (vborder_list_virtual_base H7 H9 H15).
 intros.
 eapply path_concat with (p2 := b :: nil).
  eassumption.
 eright.
 eassumption.
 eleft with (lt := nil).
 reflexivity.
 reflexivity.
 simpl.
 rewrite H1.
 trivial.
 simpl.
 trivial.
inversion H15; intros; subst.
replace o0 with o in * by abstract congruence.
inversion H22; subst.
generalize (valid_array_path_last H16 H).
intro; subst.
generalize (path_last H20).
intros.
assert (to0 = b).
 destruct beta.
  rewrite last_complete in H21; abstract congruence.
 simpl in H21; abstract congruence.
subst.
esplit.
split.
 eassumption.
esplit.
split.
 eassumption.
intros.
eapply construction_states_fields.
eassumption.
eassumption.
eassumption.
assumption.
destruct beta; invall; subst; eauto.

(* 5 : destr base nonvirtual nil Kdestrother base *)
destruct hp.
invall; subst.
destruct hp'.
generalize (stack _ (or_introl _ (refl_equal _))).
simpl.
intros.
invall; subst.
destruct beta.
 (* direct non virtual *)
 invall; subst. 
 destruct (
pointer_eq_dec (A:=A) (obj', (ar', i', (t0, l0 ++ b :: nil)))
           (obj', (ar', i', (t0, l0)))
 ).
 apply False_rect.
 assert (length l0 = length (l0 ++ b :: nil)) by abstract congruence.
 revert H6. 
 rewrite app_length.
 simpl.
 intro; abstract omegaContradiction.
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
 split.
  exists (x ++ b :: nil).
  split.
   rewrite H13.
   rewrite app_ass.
   reflexivity.
  split.
   intros.
   sdestruct (
 pointer_eq_dec (A:=A) (obj', (ar', i', (t0, l0 ++ b :: nil)))
         (obj', (ar', i', (t0, l0 ++ b0 :: nil)))
   ).
    trivial.
   destruct (in_app_or _ _ _ H6).
    destruct (In_split _ _ H8).
    invall; subst.
    assert (map
         (fun hp' : Class.Inheritance.t * ident =>
              let (_, p') := hp' in p')
             (filter
                (fun hp' : Class.Inheritance.t * ident =>
                 let (y, _) := hp' in
                 match y with
                 | Class.Inheritance.Repeated => true
                 | Class.Inheritance.Shared => false
                 end) (Class.super x6))
      = rev bases' ++ b :: rev x8 ++ b0 :: rev x7).
     rewrite <- (rev_involutive (map _ _)).
     rewrite H13.
     repeat (rewrite rev_app; simpl).
     repeat (rewrite app_ass; simpl).
     reflexivity.
    eapply breadth_non_virtual_bases.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    rewrite H0.
    simpl; abstract omega.
   inversion H8; try abstract congruence; contradiction.
  split.
  intros.
   destruct (
pointer_eq_dec (A:=A) (obj', (ar', i', (t0, l0 ++ b :: nil)))
         (obj', (ar', i', (t0, l0 ++ b0 :: nil)))
   ).
    assert (last (l0 ++ b0 :: nil) = last (l0 ++ b :: nil)) by abstract congruence.
    revert H8.
    repeat rewrite last_complete.
    injection 1; intros; subst.
    apply False_rect.
    generalize (NoDup_rev (NoDup_repeated_bases (Well_formed_hierarchy.bases_no_dup hierarchy_wf H12))).
    rewrite H13.
    intros.
    generalize (NoDup_app_right H15).
    inversion 1; abstract congruence.
   destruct (In_split _ _ H6).
   invall; subst.
   assert (map
         (fun hp' : Class.Inheritance.t * ident =>
              let (_, p') := hp' in p')
             (filter
                (fun hp' : Class.Inheritance.t * ident =>
                 let (y, _) := hp' in
                 match y with
                 | Class.Inheritance.Repeated => true
                 | Class.Inheritance.Shared => false
                 end) (Class.super x6))
      = rev x8 ++ b0 :: rev x7 ++ b :: rev x).
     rewrite <- (rev_involutive (map _ _)).
     rewrite H13.
     repeat (rewrite rev_app; simpl).
     repeat (rewrite app_ass; simpl).
     reflexivity.
   eapply constructed_sibling_before_constructed.
   eapply breadth_non_virtual_bases.
   eassumption.
   eassumption.
   eassumption.
   eassumption.
   rewrite H0.
   simpl; abstract omega.
   rewrite H0.
   simpl; abstract omega.
 intros; subst.
 simpl.
 sdestruct (
 pointer_eq_dec (A:=A)
         (obj',
         (ar', i', (Class.Inheritance.Repeated, (cn' :: p') ++ b :: nil)))
         (obj', (ar', i', (Class.Inheritance.Shared, b0 :: nil)))
  ); try (intros; discriminate).
 simpl in H9; eauto.
 generalize (stack2 _ nil _ (refl_equal _)).
  unfold stack2_inv.
  simpl.
  destruct 1.
  generalize (H8 (fun x => x)).
  destruct stk.
   intro; assumption.
  destruct 1; assumption.
(* virtual *)
invall; subst.
sdestruct (
 pointer_eq_dec (A:=A)
           (obj', (ar', i', (Class.Inheritance.Shared, b :: nil)))
           (obj', (ar', i', (Class.Inheritance.Repeated, x5 :: nil)))
).
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
split.
 auto.
injection H2; intros; subst.
inversion H10; subst.
inversion H19; subst.
inversion H17; subst.
injection H18; intros; subst.
generalize (path_last H17).
injection 1; intros; subst.
destruct (maximize_array_path H6).
invall; subst.
split.
exists (x ++ x1 :: nil).
split.
 rewrite app_ass.
 assumption.
split.
 intros.
 sdestruct (
 pointer_eq_dec (A:=A)
         (obj', (ar', i', (Class.Inheritance.Shared, x1 :: nil)))
         (obj', (ar', i', (Class.Inheritance.Shared, b :: nil)))
 ).
 trivial.
 destruct (in_app_or _ _ _ H25).
  destruct (In_split _ _ H27).
  invall; subst.
  assert (rev ((x7 ++ b :: x8) ++ x1 :: bases') = rev bases' ++ x1 :: rev x8 ++ b :: rev x7).
   repeat (rewrite rev_app; simpl).
   repeat (rewrite app_ass; simpl).
   reflexivity.
  unfold_ident_in_all.
  rewrite H28 in H15.
  eapply breadth_virtual_bases.
  eassumption.
  eassumption.
  assumption.
  abstract omega.
  eassumption.
  eassumption.
  rewrite H0.
  simpl; abstract omega.
 inversion H27; try abstract congruence; contradiction.
split.
 intros.
 sdestruct (
 pointer_eq_dec (A:=A)
         (obj', (ar', i', (Class.Inheritance.Shared, x1 :: nil)))
         (obj', (ar', i', (Class.Inheritance.Shared, b :: nil)))
 ).
  injection e; intros; subst.
  apply False_rect.
  generalize (NoDup_app_right (rev_NoDup (vborder_no_dup H15))).
  inversion 1.
  subst.
  contradiction.
 destruct (In_split _ _ H25).
 invall; subst.
 assert (rev (x ++ x1 :: x7 ++ b :: x8) = rev x8 ++ b :: rev x7 ++ x1 :: rev x).
  repeat (rewrite rev_app; simpl).
  repeat (rewrite app_ass; simpl).
  reflexivity.
 rewrite H27 in H15.
 eapply constructed_sibling_before_constructed.
 eapply breadth_virtual_bases.
 eassumption.
 eassumption.
 assumption.
 abstract omega.
 eassumption.
 eassumption.
 rewrite H0; simpl; abstract omega.
 rewrite H0; simpl; abstract omega.
intros.
sdestruct (
 pointer_eq_dec (A:=A)
         (obj', (ar', i', (Class.Inheritance.Shared, x1 :: nil)))
         (obj',
         (ar', i', (Class.Inheritance.Repeated, to :: b :: nil)))
).
 discriminate.
eapply breadth_virtual_non_virtual_bases.
eassumption.
eassumption.
assumption.
abstract omega.
eapply vborder_list_virtual_base.
eassumption.
eassumption.
eapply In_rev.
rewrite rev_involutive.
eapply in_or_app.
right.
left.
reflexivity.
eassumption.
assumption.
unfold_ident_in_all. rewrite H0. simpl. abstract omega. 
  generalize (stack2 _ nil _ (refl_equal _)).
  unfold stack2_inv.
  simpl.
  destruct 1.
  generalize (H27 (fun x => x)).
  destruct stk.
   intro; assumption.
  intro; invall; assumption. 

(* 4 : destr base non-virtual nil Kdestrcell (start destructing virtual bases) *)
destruct hp.
invall; subst.
injection H4; intros; subst.
replace x2 with c in * by abstract congruence.
esplit.
split.
 eassumption.
esplit.
split.
 eassumption.
esplit.
split.
 reflexivity.
esplit.
split.
 eassumption.
split.
 trivial.
split.
split; trivial.
split.
exists nil.
simpl.
split.
 assumption.
split.
 intro; contradiction.
split.
 intros.
 eapply H11.
 trivial.
 reflexivity.
 eapply vborder_list_virtual_base.
 eassumption.
 eassumption.
 eapply In_rev.
 rewrite rev_involutive.
 assumption.
intros.
simpl in H7.
apply H7.
rewrite <- app_nil_end in H6.
subst.
eapply In_rev.
rewrite rev_involutive.
eapply in_map_bases_intro.
assumption.
generalize (stack2 _ nil _ (refl_equal _)).
unfold stack2_inv.
simpl.
destruct 1.
generalize (H8 (fun x => x)).
destruct stk.
 intro; assumption.
destruct 1; assumption.

(* 3 : destr base virtual nil : destruct next cell *)
invall; subst.
injection H; intros; subst.
rewrite <- app_nil_end in H6.
inversion H2; subst.
inversion H15; subst.
inversion H13; subst.
injection H14; intros; subst.
generalize (path_last H13).
injection 1; intros; subst.
generalize (maximize_array_path H0).
intros; invall; subst.
split.
esplit.
esplit.
split.
 eassumption.
split.
 eassumption.
split.
 eassumption.
split.
 abstract omega.
bintro.
sdestruct (
pointer_eq_dec (A:=A)
          (obj, (ar, i, (Class.Inheritance.Repeated, to :: nil)))
          (obj, (ar, b, (Class.Inheritance.Repeated, to :: nil)))
).
 injection e; intros; subst.
 split; intros.
  abstract omegaContradiction.
 trivial.
split; intros.
 eapply constructed_sibling_before_constructed.
 eapply breadth_arrays with (i2 := i).
 eassumption.
 eassumption.
 assumption.
 abstract omega.
 abstract omega.
 abstract omega.
 unfold_ident_in_all; rewrite H1; simpl; abstract omega. 
 unfold_ident_in_all; rewrite H1; simpl; abstract omega.
eapply constructed_sibling_before_destructed.
eapply breadth_arrays with (i1 := i).
 eassumption.
 eassumption.
 assumption.
 abstract omega.
 assert (b <> i) by abstract congruence.
 abstract omega.
 abstract omega.
 unfold_ident_in_all; rewrite H1; simpl; abstract omega. 
assumption.

(* 2 exiting from block, requires destruct *)
split; auto.
esplit.
esplit.
split.
 eassumption.
split.
econstructor.
2 : eapply Zle_refl.
eauto.
split.
auto.
split.
assert (0 <= Object.arraysize o)%Z by eauto.
abstract omega.
split.
intros.
 assert (0 <= j < Object.arraysize o)%Z by abstract omega.
 eauto.
intros.
abstract omegaContradiction.

(* 1 destr_array nil Kcontinue (return from destruction) *)
generalize (stack2 _ nil _ (refl_equal _)).
unfold stack2_inv.
simpl.
destruct 1.
generalize (H I).
destruct stk.
 trivial.
unfold stackframe_constructor_inv.
intro; assumption.

Qed.

End Preservation.
