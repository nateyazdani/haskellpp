Load IncludeHeader.


 (** * POPL 2012 submission: Theorem 4 *)

 (** Constructed scalar fields *)


Section ScalarFields.

Variable A : ATOM.t.
Variable nativeop : Type.

Variable prog : Program.t A nativeop.
Notation hier := (Program.hierarchy prog) (only parsing).

Hypothesis hierarchy_wf : Well_formed_hierarchy.prop (Program.hierarchy prog).

Variable cppsem : cppsemparam.
Variable sem : semparam A nativeop.
  
Definition scalar_fields_some_constructed (s : _ _ nativeop) :=
  forall obj ar i h p hp, valid_pointer hier (Globals.heap (State.global s)) (Value.subobject obj ar i h p hp) ->
    forall cn, last p = Some cn ->
      forall c, hier ! cn = Some c ->
        forall fs, In fs (Class.fields c) ->
          forall ty, FieldSignature.type fs = FieldSignature.Scalar ty ->
            forall v, Globals.get_field (Globals.field_values (State.global s)) (obj, ar, i, (h, p), fs) = Some v ->
              assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, (h, p), fs) (State.field_construction_states s) = Some Constructed
              .
  
Definition scalar_fields_some_constructed_recip (s : _ _ nativeop) :=
  enable_uninitialized_scalar_fields cppsem = false ->
  forall obj ar i h p hp, valid_pointer hier (Globals.heap (State.global s)) (Value.subobject obj ar i h p hp) ->
    forall cn, last p = Some cn ->
      forall c, hier ! cn = Some c ->
        forall fs, In fs (Class.fields c) ->
          forall ty, FieldSignature.type fs = FieldSignature.Scalar ty ->
            assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, (h, p), fs) (State.field_construction_states s) = Some Constructed ->
            exists v, Globals.get_field (Globals.field_values (State.global s)) (obj, ar, i, (h, p), fs) = Some v
              .

Variables s1 : State.t A nativeop.

Lemma init_scalar_fields_some_constructed : 
  initial_state prog s1 ->
  scalar_fields_some_constructed s1.
Proof.
  inversion 1; subst.
  unfold scalar_fields_some_constructed.
  simpl.
  inversion 1; subst.
  rewrite PTree.gempty in H3.
  discriminate.
Qed. 

Lemma init_scalar_fields_some_constructed_recip : 
  initial_state prog s1 ->
  scalar_fields_some_constructed_recip s1.
Proof.
  inversion 1; subst.
  unfold scalar_fields_some_constructed_recip.
  simpl.
  inversion 2; subst.
  rewrite PTree.gempty in H4.
  discriminate.
Qed. 

Hypothesis Hs1 : invariant prog s1.

Variable s2 : State.t A nativeop.
Variable t : trace (evtr sem).

Hypothesis step : step prog cppsem s1 t s2.

Section Straight.

Hypothesis Hs1fields : scalar_fields_some_constructed s1.

Lemma  preservation_scalar_fields_some_constructed : 
  scalar_fields_some_constructed s2.
Proof.
  unfold scalar_fields_some_constructed in *.
  Opaque Globals.get_field Globals.put_field.
  inversion step; subst; simpl in *; try assumption.

  (* 9 putfield *)
  intros.
  destruct (aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs) (obj0, ar0, i0, (h0, p0), fs0)).
   injection e; intros; subst; assumption.   
   unfold_ident_in_all.
   rewrite (Globals.get_put_field_other H2 n) in H8.
   eauto.

  (* 8 Sblock Some *)
  intros until 1.
  destruct (peq obj  obj0).
   subst.
   injection H1; intros until 2; subst; simpl in *.
   generalize (Globals.valid_none (valid_global Hs1) (Ple_refl _)).
   intros.
   rewrite (unconstructed_scalar_fields Hs1 H3 H7) in H8.
   discriminate.
  injection H1; intros until 2; subst; simpl in *.
  inversion H2; subst.
  rewrite PTree.gso in H5; eauto.
  eapply Hs1fields with (hp := hp2).
  econstructor; eauto.

  (* 7 constr field cons struct *)
  intros.
  sdestruct (
Cppsem.aux_constr_state_key_eq_dec (obj, ar, i, hp, fs)
         (obj0, ar0, i0, (h, p), fs0)
  ); eauto.
  unfold_ident_in_all; abstract congruence.

  (* 6 constr field scalar no init *)
  intros.
  sdestruct (
Cppsem.aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, ar0, i0, (h0, p0), fs0)
  ); eauto.

  (* 5 Sinitscalar *)
  intros.
  sdestruct (
Cppsem.aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, ar0, i0, (h0, p0), fs0)
  ); eauto.
  unfold_ident_in_all.
  rewrite (Globals.get_put_field_other H3 n) in H9.
  eauto.

  (* 4 constr array n Kconstrother field *)
  intros.
  sdestruct (
Cppsem.aux_constr_state_key_eq_dec (obj', ar', i', (h, p), fs)
         (obj0, ar0, i, (h0, p0), fs0)
  ); eauto.

  (* 3 destr field cons scalar *)
  intros.
  sdestruct (
 Cppsem.aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, ar0, i0, (h0, p0), fs0)
  ); eauto.
   injection e; intros; subst.
   Transparent Globals.get_field. simpl in *.
   rewrite H in H5.
   rewrite find_remove_field_same in H5.
   discriminate.
  assert (
Globals.get_field
         (remove_field (obj, ar, i, (h, p), fs) (Globals.field_values gl))
         (obj0, ar0, i0, (h0, p0), fs0) = Globals.get_field
         ( (Globals.field_values gl))
         (obj0, ar0, i0, (h0, p0), fs0) 
  ).
   simpl.
   rewrite H4.
   rewrite (find_remove_field_other n).
   reflexivity.
  rewrite H6 in H5.
  eauto.

 (* 2 destr field cons struct *)
  intros.
  sdestruct (
Cppsem.aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, ar0, i0, (h0, p0), fs0)
  ); eauto.
  unfold_ident_in_all; abstract congruence.

  (* 1 destr array nil Kdestrother field *)
  intros.
  sdestruct (
Cppsem.aux_constr_state_key_eq_dec (obj', ar', i', hp', fs)
         (obj0, ar0, i, (h, p), fs0)
  ); eauto.
  generalize (kind Hs1).
  intro.
  unfold state_kind_inv in *; simpl in *; destruct hp'; invall; subst.
  rewrite (last_complete) in H8.
  invall; subst.
  unfold_ident_in_all; abstract congruence.

Qed.   

End Straight.

Section Recip.

Hypothesis Hs1fields : scalar_fields_some_constructed_recip s1.

Lemma  preservation_scalar_fields_some_constructed_recip : 
  scalar_fields_some_constructed_recip s2.
Proof.
  unfold scalar_fields_some_constructed_recip in *.
  Opaque Globals.get_field Globals.put_field.
  inversion step; subst; simpl in *; try assumption.

  (* 9 putfield *)
  intros.
  destruct (aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs) (obj0, ar0, i0, (h0, p0), fs0)).
   injection e; intros; subst.
   erewrite Globals.get_put_field_same.
   2 : eassumption.
   eauto.
  erewrite Globals.get_put_field_other.
  2 : eassumption.
  eauto.
  assumption.

  (* 8 Sblock Some *)
  intros until 2.
  destruct (peq obj  obj0).
   subst.
   injection H1; intros until 2; subst; simpl in *.
   generalize (Globals.valid_none (valid_global Hs1) (Ple_refl _)).
   intros.
   rewrite (construction_states_fields_none Hs1 H4) in H9.
   discriminate.
  injection H1; intros until 2; subst; simpl in *.
  inversion H3; subst.
  rewrite PTree.gso in H6; eauto.
  eapply Hs1fields with (hp := hp2).
  assumption.
  econstructor; eauto.

  (* 7 constr field cons struct *)
  intros until 6.
  sdestruct (
Cppsem.aux_constr_state_key_eq_dec (obj, ar, i, hp, fs)
         (obj0, ar0, i0, (h, p), fs0)
  ); eauto.
  intro; discriminate.

  (* 6 constr field scalar no init *)
  intro.
  congruence. (** rule disabled *)

  (* 5 Sinitscalar *)
  intros until 6.
  sdestruct (
Cppsem.aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, ar0, i0, (h0, p0), fs0)
  ).
   injection e; intros; subst.
   erewrite Globals.get_put_field_same.
   2 : eassumption.
   eauto.
  erewrite Globals.get_put_field_other.
  2 : eassumption.
  eauto.
  assumption.

  (* 4 constr array n Kconstrother field *)
  intros until 6.
  sdestruct (
Cppsem.aux_constr_state_key_eq_dec (obj', ar', i', (h, p), fs)
         (obj0, ar0, i, (h0, p0), fs0)
  ); eauto.
  generalize (kind Hs1).
  unfold state_kind_inv; simpl.
  intro; invall; subst.
  rewrite last_complete in H8.
  invall; subst.
  congruence.

  (* 3 destr field cons scalar *)
  intros until 6.
  sdestruct (
 Cppsem.aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, ar0, i0, (h0, p0), fs0)
  ).
   intro; discriminate.
  assert (
Globals.get_field
         (remove_field (obj, ar, i, (h, p), fs) (Globals.field_values gl))
         (obj0, ar0, i0, (h0, p0), fs0) = Globals.get_field
         ( (Globals.field_values gl))
         (obj0, ar0, i0, (h0, p0), fs0) 
  ).
  Transparent Globals.get_field.
   simpl.
   rewrite H5.
   rewrite (find_remove_field_other n).
   reflexivity.
  unfold_ident_in_all.
  rewrite H6.
  eauto.

 (* 2 destr field cons struct *)
  intros until 6.
  sdestruct (
Cppsem.aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, ar0, i0, (h0, p0), fs0)
  ); eauto.
  unfold_ident_in_all; abstract congruence.

  (* 1 destr array nil Kdestrother field *)
  intros until 6.
  sdestruct (
Cppsem.aux_constr_state_key_eq_dec (obj', ar', i', hp', fs)
         (obj0, ar0, i, (h, p), fs0)
  ); eauto.
  intro; discriminate.

Qed.   

End Recip.

End ScalarFields.

End Preservation.
