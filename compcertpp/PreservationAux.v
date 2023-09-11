
Load PreservationHeader.

Lemma stack_objects_sorted :
  sorted (fun x y => Plt y x) (stack_objects s2).
Proof.
  inversion Hs1.
  inversion step; subst; simpl in *; eauto.

 (* new *)
 eapply sorted2_sorted.
 simpl.
 split.
  intros.
  destruct (Z_lt_le_dec (Zpos i) (Zpos obj)).
   assumption.
  apply False_rect.
  injection H1; intros; subst.
  generalize (Globals.valid_none valid_global z).
  generalize (stack_objects_exist _ H2).
  intros; contradiction.
  eauto using sorted_sorted2, Plt_trans.

(* delete *)
 eauto using sorted_tail.
Qed.
  

Lemma unconstructed_scalar_fields : forall obj, (Globals.heap (State.global s2)) ! obj = None -> forall fs ty, FieldSignature.type fs = FieldSignature.Scalar ty -> forall ar i hp, Globals.get_field (Globals.field_values (State.global s2)) (obj, ar, i, hp, fs) = None.
Proof.
  inversion Hs1.
  Opaque Globals.get_field Globals.put_field.
  inversion step; subst; simpl in *; eauto.  

  (* putfield *)
  intros.
  destruct (aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs) (obj0, ar0, i0, hp0, fs0)).
   injection e; intros; subst.
   inversion H0; abstract congruence.
   rewrite (Globals.get_put_field_other H2 n); eauto.  

   (* sblock some *)
   injection H1; intros until 2; subst; simpl in *.
   intro.
   destruct (peq (Globals.next_object gl) obj).
    subst.
    rewrite PTree.gss.
    intro; discriminate.
   rewrite PTree.gso; eauto.

   (* Sinitscalar *)
  intros.
  destruct (aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs) (obj0, ar0, i0, hp, fs0)).
   injection e; intros; subst.
   unfold state_kind_inv in *; simpl in *; invall; subst.
   inversion H8; abstract congruence.
   rewrite (Globals.get_put_field_other H3 n); eauto.  

  (* destr field scalar *)
  intros.
  destruct (aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs) (obj0, ar0, i0, hp, fs0)).
   injection e; intros; subst.
   unfold state_kind_inv in *; simpl in *; invall; subst.
   inversion H4; abstract congruence.
   eapply trans_equal with (Globals.get_field (Globals.field_values gl) (obj0, ar0, i0, hp, fs0)).
   Transparent Globals.get_field.
   simpl.
   destruct hp.
   rewrite H1.
   rewrite (find_remove_field_other n).
   reflexivity.
   eauto.
Qed.   


Lemma stack_or_deallocated :  forall obj,  (Globals.heap (State.global s2)) ! obj <> None -> In obj (stack_objects s2) \/ In obj (State.deallocated_objects s2).
Proof.
  inversion Hs1.
  inversion step; subst; simpl in *; eauto.  

  injection H1; intros until 2; subst; simpl in *.
  intro.
  destruct (peq obj (Globals.next_object gl)).
   auto.
  rewrite PTree.gso; eauto.
  intros;  destruct (stack_or_deallocated _ H2); eauto.

  intros.
  unfold state_kind_inv in *; simpl in *; invall; subst.
  destruct (stack_or_deallocated _ H); eauto.
  destruct H1; eauto.
Qed.


  
  

Lemma deallocated_objects_destructed : forall obj, In obj (State.deallocated_objects s2) -> forall o, (Globals.heap (State.global s2)) ! obj = Some o -> forall i, 0 <= i < Object.arraysize o -> assoc (@pointer_eq_dec _) (obj, (nil, i, (Class.Inheritance.Repeated, Object.class o :: nil))) (State.construction_states s2) = Some Destructed.
Proof.
  inversion Hs1.
  inversion step; subst; simpl in *; eauto.  

(* 12 Sblock Some *)
revert H1.
unfold Globals.new.
injection 1; intros until 2; subst; simpl in *.
intro.
destruct (peq (Globals.next_object gl) obj ).
 subst.
 generalize (Globals.valid_none valid_global (Ple_refl _)).
 intros until 2.
 generalize (deallocated_objects_exist _ H3).
 intro; contradiction.
rewrite PTree.gso; eauto.

(* 11 Sconstructor Kconstrarray *)
intros.
sdestruct (
 pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0,
         (nil, i0, (Class.Inheritance.Repeated, Object.class o :: nil)))
    
); eauto.
injection e; intros; subst.
generalize (deallocated_objects_destructed _ H2 _ H3 _ H4).
unfold state_kind_inv in kind; simpl in *; invall.
assert (i0 <= i0 < n) by abstract omega.
generalize (H13 _ H4).
unfold_ident.
intros; abstract congruence.

(* 10 Sreturn Kconstrothercells *)
intros.
sdestruct (
 pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0,
         (nil, i0, (Class.Inheritance.Repeated, Object.class o :: nil)))
); eauto.
injection e; intros; subst.
generalize (deallocated_objects_destructed _ H _ H0 _ H1).
generalize (stack _ (or_introl _ (refl_equal _))); simpl.
unfold_ident ;intro; invall.
destruct H7; abstract congruence.


(* 9 Sconstructor Kconstr base *)
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
         (nil, i0, (Class.Inheritance.Repeated, Object.class o :: nil)))
); eauto.
apply False_rect.
destruct k2; try discriminate.
unfold state_kind_inv in kind; simpl in *; invall.
destruct p. 
 discriminate.
destruct p0; discriminate.

(* 8 Sreturn Kconstrother base *)
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
         (nil, i0, (Class.Inheritance.Repeated, Object.class o :: nil)))
); eauto.
apply False_rect.
destruct k2; try discriminate.
generalize (stack _ (or_introl _ (refl_equal _))); simpl; intro; invall.
destruct p. 
 discriminate.
destruct p; discriminate.

(* 7 constr base direct non virtual nil *)
intros.
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0,
         (nil, i0, (Class.Inheritance.Repeated, Object.class o :: nil)))
    
); eauto.
injection e; intros; subst.
generalize (deallocated_objects_destructed _ H1 _ H2 _ H3).
unfold state_kind_inv in kind; simpl in *; invall; subst.
unfold_ident_in_all; intros; abstract congruence.

(* 6 destr array i *)
intros.
sdestruct (
  pointer_eq_dec (A:=A)
  (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
  (obj0,
    (nil, i, (Class.Inheritance.Repeated, Object.class o :: nil)))
); eauto.
injection e; intros; subst.
apply False_rect.
generalize (deallocated_objects_destructed _ H4 _ H5 _ H6).
unfold state_kind_inv in kind; simpl in *; invall; subst.
assert (0 <= i <= i) by abstract omega.
generalize (H12 _ H6).
unfold_ident; intros; abstract congruence.

(* 5 destr fields nil *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0,
         (nil, i0, (Class.Inheritance.Repeated, Object.class o :: nil)))
); eauto.
injection e; intros; subst.
generalize (deallocated_objects_destructed _ H2 _ H3 _ H4).
unfold state_kind_inv in kind; simpl in *; invall; subst.
unfold_ident_in_all; intros; abstract congruence.

(* 4 destr base cons *)
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
         (nil, i0, (Class.Inheritance.Repeated, Object.class o :: nil)))
); eauto.
destruct beta; try discriminate.
unfold state_kind_inv in kind; simpl in *; invall.
destruct p.
 discriminate.
destruct p0; discriminate.

(* 3 destr base direct non virtual nil Kdestrother bases *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, hp))
         (obj0,
         (nil, i0, (Class.Inheritance.Repeated, Object.class o :: nil)))
); eauto.

(* 2 destr base virtual nil *)
intros.
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0,
         (nil, i0, (Class.Inheritance.Repeated, Object.class o :: nil)))
); eauto.

(* 1 requires destruct *)
destruct 1; eauto.
subst.
unfold state_kind_inv in kind; simpl in *; invall; subst.
intros.
replace x0 with o in * by abstract congruence.
apply H6.
abstract omega.

Qed.



Lemma deallocated_objects_not_in_stack : forall obj, In obj (stack_objects s2) -> In obj (State.deallocated_objects s2) -> False.
Proof.
  inversion Hs1.
  inversion step; subst; simpl in *; eauto.

  destruct 1; eauto.
  subst.
  intro.
  generalize (deallocated_objects_exist _ H2).
  injection H1; intros; subst; simpl in *.
 generalize (Globals.valid_none valid_global (Ple_refl _)).
  assumption.

  destruct 2; eauto.
  subst.
  inversion stack_objects_no_dup; subst.
  unfold state_kind_inv in *; simpl in *; invall; subst; contradiction.
Qed.
  

Lemma  deallocated_objects_exist :  forall obj, In obj (State.deallocated_objects s2) -> (Globals.heap (State.global s2)) ! obj <> None.
Proof.
  inversion Hs1.
  inversion step; subst; simpl in *; eauto.

  intros.
  revert H1.
  unfold Globals.new.
  injection 1; intros; subst; simpl.
destruct (peq (Globals.next_object gl) obj0 ).
subst; rewrite PTree.gss; abstract congruence.
rewrite PTree.gso; eauto.

destruct 1; eauto.
subst.
unfold state_kind_inv in *; simpl in *; invall; abstract congruence.

Qed.


Lemma  kind_object_in_construction : forall obj, kind_object (State.kind s2) = Some obj -> exists l', stack_objects s2 = obj :: l'.
Proof.
  inversion Hs1.
  inversion step; subst; simpl in *; try (intros; discriminate); injection 1; intros; subst; eauto; exact (stack_objects_in_construction nil _ _ (refl_equal _) _ _ (refl_equal _)).
Qed.


Lemma  stack_objects_in_construction : forall l1 sf l2
  (Hstack : State.stack s2 = l1 ++ sf :: l2)
  obj ar
  (Hframe : frame_array_weak sf = Some (obj, ar)), exists l', stackframe_objects l2 = obj :: l'.
Proof.
  inversion Hs1.
  inversion step; subst; simpl in *; eauto;
    intros until 1; try exact (stack_objects_in_construction _ _ _ (app_cons Hstack _)); destruct l1; injection Hstack; intros; eauto; subst; simpl in *; try (intros; discriminate); injection Hframe; intros; subst; eauto; try exact (stack_objects_in_construction nil _ _ (refl_equal _) _ _ (refl_equal _)); try exact (stack_objects_in_construction (_ :: _) _ _ (refl_equal _) _ _ Hframe).

  destruct l1.
   injection H4; intros; subst; injection Hframe; intros; subst; eauto.
  injection H4; eauto.

  destruct l1.
   injection H; intros; subst; injection Hframe; intros; subst; eauto.
  injection H; eauto.

Qed.  


Lemma constructed_stack_objects_no_kind : forall obj (Hin : In obj (constructed_stack_objects s2)), kind_object (State.kind s2) = Some obj -> False.
Proof.
  generalize (constructed_stack_objects_incl (s := s1)).
  intro Hincl.
  inversion Hs1.
  intros until 1.
  inversion step; subst; simpl in *; try (intros; discriminate); injection 1; intros; subst; eauto; try exact (constructed_stack_objects_no_stackframe _ Hin _ (or_introl _ (refl_equal _)) _ (refl_equal _)).

  (* 2 Sblock Some *)
  generalize (stack_objects_exist _ (Hincl _ Hin)).
  intros.
  destruct H3.
  eapply Globals.valid_none.
  assumption.
  revert H1.
  unfold Globals.new.
  injection 1; intros; subst.
  eapply Ple_refl.

  (* 1 requires destruct *)
  inversion stack_objects_no_dup.
  subst.
  destruct H4.
  apply in_or_app.
  destruct (in_app_or _ _ _ Hin).
   auto.
  right.
  eapply constructed_stackframe_objects_incl.
  assumption.

Qed.
 

Lemma constructed_stack_objects_no_stackframe : forall obj, In obj (constructed_stack_objects s2) -> forall sf, In sf (State.stack s2) -> forall ar, frame_array_weak sf = Some (obj, ar) -> False.
Proof.
  inversion Hs1.
  inversion step; subst; simpl in *; eauto.

  (* 13 Scall *)
  destruct 2; eauto.
  subst; simpl; intro; abstract congruence.

  (* 12 Sinvoke *)
  destruct 2; eauto.
  subst; simpl; intro; abstract congruence.

  (* 11 Sblock Some *)
  destruct 2; eauto.
  subst; simpl; intro; abstract congruence.

  (* 10 constr array nil Kcontinue *)
  destruct 1; eauto.
  subst; intros.
  unfold state_kind_inv in *; simpl in *; invall; subst; simpl in *; invall; subst.  
  generalize (stack_state_wf _ (or_intror _ H) _ H0).
  intros; invall.
  destruct ar0; try discriminate.
  destruct x0; try discriminate.
  destruct H5; trivial.
   
  (* 9 constr array cons *)
  destruct 2; eauto.
  subst; injection 1; intros; subst; eauto.

  (* 8 Sconstructor Kconstrarray *)
  destruct 2; eauto.
  subst; injection 1; intros; subst.
  eauto.

  (* 7 constr cons *)
  destruct 2; eauto.
  subst; injection 1; intros; subst; eauto.

  (* 6 constr cons field struct *)
  destruct 2; eauto.
  subst; injection 1; intros; subst; eauto.

  (* 5 Sconstructor Kconstr base *)
  destruct 2; eauto.
  subst; injection 1; intros; subst; eauto.

  (* 4 destr array cons *)
  destruct 2.  
   subst; injection 1; intros; subst; eauto.
  destruct H5; eauto.
  subst; injection 1; intros; subst; eauto.

  (* 3 destr field cons *)
  destruct 2; eauto.
  subst; injection 1; intros; subst; eauto.

  (* 2 destr base cons *)
  destruct 2.
   subst; injection 1; intros; subst; eauto.
  destruct H0; eauto.
  subst; injection 1; intros; subst; eauto.

  (* 1 destr array nil Kcontinue *)
  destruct 2; eauto.
  subst; simpl; intros; discriminate.

Qed.
   
Lemma constructed_stack_objects_correct : forall obj, In obj (constructed_stack_objects s2) -> forall o, (Globals.heap (State.global s2)) ! obj = Some o -> forall i, 0 <= i < Object.arraysize o -> assoc (@pointer_eq_dec _) (obj, (nil, i, (Class.Inheritance.Repeated, Object.class o :: nil))) (State.construction_states s2) = Some Constructed.
Proof.
  generalize (constructed_stack_objects_incl (s := s1)).
  intro Hincl.
  generalize (fun x H => stack_objects_exist Hs1 (Hincl x H)).
  intro Hex.
  inversion Hs1.
  inversion step; subst; simpl in *; try trivial.

(* 13 Sblock Some *)
revert H1.
unfold Globals.new.
injection 1; intros until 2; subst; simpl in *.
intro.
destruct (peq (Globals.next_object gl) obj ).
 subst.
 generalize (Globals.valid_none valid_global (Ple_refl _)).
 intros until 2.
 generalize (Hex _ H3).
 intro; contradiction.
rewrite PTree.gso; eauto.

(* 12 constr array nil Kcontinue *)
destruct 1; eauto.
subst.
unfold state_kind_inv in kind; simpl in *; invall; subst; simpl in *; invall; subst.
intros.
replace o with x in * by abstract congruence.
eauto.

(* 11 Sconstructor Kconstrarray *)
intros.
sdestruct (
 pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0,
         (nil, i0, (Class.Inheritance.Repeated, Object.class o :: nil)))
    
); eauto.
injection e; intros; subst.
generalize (constructed_stack_objects_correct _ H2 _ H3 _ H4).
unfold state_kind_inv in kind; simpl in *; invall.
assert (i0 <= i0 < n) by abstract omega.
generalize (H13 _ H4).
unfold_ident.
intros; abstract congruence.

(* 10 Sreturn Kconstrothercells *)
intros.
sdestruct (
 pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj0,
         (nil, i0, (Class.Inheritance.Repeated, Object.class o :: nil)))
); eauto.

(* 9 Sconstructor Kconstr base *)
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
         (nil, i0, (Class.Inheritance.Repeated, Object.class o :: nil)))
); eauto.
apply False_rect.
destruct k2; try discriminate.
unfold state_kind_inv in kind; simpl in *; invall.
destruct p. 
 discriminate.
destruct p0; discriminate.

(* 8 Sreturn Kconstrother base *)
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
         (nil, i0, (Class.Inheritance.Repeated, Object.class o :: nil)))
); eauto.

(* 7 constr base direct non virtual nil *)
intros.
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0,
         (nil, i0, (Class.Inheritance.Repeated, Object.class o :: nil)))
    
); eauto.
injection e; intros; subst.
generalize (constructed_stack_objects_correct _ H1 _ H2 _ H3).
unfold state_kind_inv in kind; simpl in *; invall; subst.
unfold_ident_in_all; intros; abstract congruence.

(* 6 destr array i *)
intros.
sdestruct (
  pointer_eq_dec (A:=A)
  (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil)))
  (obj0,
    (nil, i, (Class.Inheritance.Repeated, Object.class o :: nil)))
); eauto.
injection e; intros; subst.
apply False_rect.
unfold state_kind_inv in kind; simpl in *; invall; subst.
destruct stk; try contradiction.
destruct t; try contradiction.
 simpl in H8.
 destruct c0; try contradiction.
 invall; subst; simpl in *.
 inversion stack_objects_no_dup.
 subst.
 destruct H18.
 apply in_or_app.
 destruct (in_app_or _ _ _ H4).
  auto.
 right.
 eapply constructed_stackframe_objects_incl.
 assumption.
simpl in H8. 
destruct inhpath.
destruct k; try contradiction.
destruct kind; invall; subst.
destruct array; discriminate.

(* 5 destr fields nil *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0,
         (nil, i0, (Class.Inheritance.Repeated, Object.class o :: nil)))
); eauto.
injection e; intros; subst.
generalize (constructed_stack_objects_correct _ H2 _ H3 _ H4).
unfold state_kind_inv in kind; simpl in *; invall; subst.
unfold_ident_in_all; intros; abstract congruence.

(* 4 destr base cons *)
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
         (nil, i0, (Class.Inheritance.Repeated, Object.class o :: nil)))
); eauto.
destruct beta; try discriminate.
unfold state_kind_inv in kind; simpl in *; invall.
destruct p.
 discriminate.
destruct p0; discriminate.

(* 3 destr base direct non virtual nil Kdestrother bases *)
intros.
sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, hp))
         (obj0,
         (nil, i0, (Class.Inheritance.Repeated, Object.class o :: nil)))
); eauto.
injection e; intros; subst.
generalize (constructed_stack_objects_correct _ H _ H0 _ H1).
unfold state_kind_inv in kind; simpl in *; invall; subst.
unfold_ident_in_all; intros; abstract congruence.

(* 2 destr base virtual nil *)
intros.
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p)))
         (obj0,
         (nil, i0, (Class.Inheritance.Repeated, Object.class o :: nil)))
); eauto.
injection e; intros; subst.
generalize (constructed_stack_objects_correct _ H0 _ H1 _ H2).
unfold state_kind_inv in kind; simpl in *; invall.
unfold_ident_in_all; abstract congruence.

(* 1 requires destruct *)
intros; eauto.

Qed.
  


Lemma  construction_states_fields_none : forall obj, (Globals.heap (State.global s2)) ! obj = None -> forall ar i hp fs, assoc (aux_constr_state_key_eq_dec ) (obj, ar, i, hp, fs) (State.field_construction_states s2) = None.
Proof.
  inversion Hs1.
  inversion step; subst; simpl in *; try trivial.

(* 8 Sblock Some *)
revert H1.
unfold Globals.new.
injection 1; intros until 2; subst; simpl in *.
intro.
destruct (peq (Globals.next_object gl) obj ).
 subst; rewrite PTree.gss; abstract congruence.
rewrite PTree.gso; eauto.

(* 7 constr field cons *)
intros.
sdestruct (
Cppsem.aux_constr_state_key_eq_dec (obj, ar, i, hp, fs)
         (obj0, ar0, i0, hp0, fs0)
); eauto.
destruct hp; unfold state_kind_inv in kind; simpl in *; invall.
inversion H3; abstract congruence.

(* 6 constr field cons scalar no init *)
intros.
sdestruct (
Cppsem.aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, ar0, i0, hp, fs0)
); eauto.
unfold state_kind_inv in kind; simpl in *; invall.
inversion H4; abstract congruence.

(* 5 Sinitscalar Kconstr field *)
intros.
sdestruct (
Cppsem.aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, ar0, i0, hp, fs0)
); eauto.
unfold state_kind_inv in kind; simpl in *; invall.
inversion H7; abstract congruence.

(* 4 constr array n Kconstrother field *)
intros.
sdestruct (
Cppsem.aux_constr_state_key_eq_dec (obj', ar', i', (h, p), fs)
         (obj0, ar0, i, hp, fs0)
); eauto.
destruct hp; generalize (stack _ (or_introl _ (refl_equal _))); simpl; intro; invall.
inversion H2; abstract congruence.

(* 3 destr field cons scalar *)
intros.
sdestruct (
Cppsem.aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, ar0, i0, hp, fs0)
); eauto.
destruct hp; unfold state_kind_inv in kind; simpl in *; invall.
inversion H3; abstract congruence.

(* 2 destr field cons struct *)
intros.
sdestruct (
Cppsem.aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs)
         (obj0, ar0, i0, hp, fs0)
); eauto.
destruct hp; unfold state_kind_inv in kind; simpl in *; invall.
inversion H3; abstract congruence.

(* 1 destr array nil Kdestrother field *)
intros.
sdestruct (
Cppsem.aux_constr_state_key_eq_dec (obj', ar', i', hp', fs)
         (obj0, ar0, i, hp, fs0)
); eauto.
destruct hp'; generalize (stack _ (or_introl _ (refl_equal _))); simpl; intro; invall.
inversion H2; abstract congruence.

Qed.

Lemma stack_objects_no_dup : NoDup (stack_objects s2).
Proof.
  inversion Hs1.
  inversion step; subst; simpl in *; try trivial.

(* 1/2 Sblock Some *)
econstructor.
 2 : assumption.
 intro.
 generalize (stack_objects_exist _ H2).
 intros.
 apply H3.
 eapply Globals.valid_none.
 assumption.
 revert H1.
 unfold Globals.new.
 injection 1; intros; subst.
 apply Ple_refl.

(* requires destruct *)
inversion stack_objects_no_dup ; assumption.

Qed.

Lemma stack_objects_exist :
  forall obj, In obj (stack_objects s2) -> (Globals.heap (State.global s2)) ! obj <> None.
Proof.
  inversion Hs1.
  inversion step; subst; simpl in *; try trivial.

(* Sblock Some *)
revert H1.
unfold Globals.new.
injection 1; intros; subst; simpl in *.
destruct (peq (Globals.next_object gl) obj0 ).
 subst; rewrite PTree.gss; abstract congruence.
destruct H4.
 contradiction.
rewrite PTree.gso; eauto.

(* requires destruct *)
eauto.

Qed.

Lemma valid_global : Globals.valid (State.global s2).
Proof.
  inversion Hs1.
  inversion valid_global.
  constructor.
  inversion step; subst; unfold Globals.update in *; simpl in *; try abstract trivial.

  (* new *)
  eapply Globals.valid_new.
  eassumption.
  symmetry; eassumption.

Qed.

Lemma valid_object_classes : forall obj o, (Globals.heap (State.global s2)) ! obj = Some o -> hier ! (Object.class o) <> None.
Proof.
  inversion Hs1.
  inversion step; subst; simpl in *; try abstract trivial.

  (* new *)
  intros ? ?.
  generalize H1.
  unfold Globals.new.
  injection 1; intros until 2; subst; simpl.
  destruct (peq  (Globals.next_object gl) obj0).
   subst.
   rewrite PTree.gss.
   injection 1; intros; subst; simpl.
   assumption.
  rewrite PTree.gso; eauto.

Qed.  


Lemma object_arraysizes_nonnegative : forall obj o, (Globals.heap (State.global s2)) ! obj = Some o -> (0 <= Object.arraysize o)%Z.
Proof.
  inversion Hs1.
  inversion step; subst; simpl in *; trivial.

  (* new *)
  intros ? ?.
  generalize H1.
  unfold Globals.new.
  injection 1; intros until 2; subst; simpl.
  destruct (peq (Globals.next_object gl)  obj0).
   subst.
   rewrite PTree.gss.
   injection 1; intros; subst; simpl.
   abstract omega.
  rewrite PTree.gso; eauto.

Qed.  

Lemma stack_state : forall sf l, State.stack s2 = sf :: l -> frame_requires_code sf -> is_code_state (State.kind s2).
Proof.
  inversion Hs1.
  inversion step; subst; simpl in *; trivial;
try (injection 1; intros; subst; simpl in *; tauto);
try (intros; subst; refine (_ (stack2 _ nil _ (refl_equal _))); unfold stack2_inv; simpl; tauto).
Qed.

Lemma construction_states_none : forall obj, (Globals.heap (State.global s2)) ! obj = None -> forall rptr, assoc (@pointer_eq_dec _) (obj, rptr) (State.construction_states s2) = None.
Proof.
  inversion Hs1.
  inversion step; subst; simpl in *; try trivial.

(* 11 Sblock Some *)
revert H1.
unfold Globals.new.
injection 1; intros until 2; subst; simpl in *.
intro.
destruct (peq (Globals.next_object gl) obj ).
 subst; rewrite PTree.gss; abstract congruence.
rewrite PTree.gso; eauto.

(* 10 Sconstructor Kconstrarray *)
intros.
sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil))) 
         (obj0, rptr)
); eauto.
unfold state_kind_inv in kind; simpl in *; invall; congruence.

(* 9 Sreturn Kconstrothercells *)
intros.
sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil))) 
         (obj0, rptr)
); eauto.
generalize (stack _ (or_introl _ (refl_equal _))).
simpl; intro; invall; abstract congruence.

(* 8 Sconstructor Kconstr base *)
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
         end))) (obj0, rptr)
); eauto.
unfold state_kind_inv in kind; simpl in *; invall.
inversion H5; abstract congruence.

(* 7 Sreturn Kconstrother base *)
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
         end))) (obj0, rptr)
); eauto.
generalize (stack _ (or_introl _ (refl_equal _))).
simpl; intro; invall.
inversion H2; abstract congruence.

(* 6 constr base direct non virtual nil *)
intros.
sdestruct (
  pointer_eq_dec (A:=A) (obj, (ar, i, (h, p))) (obj0, rptr)
); eauto.
unfold state_kind_inv in kind; simpl in *; invall.
inversion H4; abstract congruence.

(* 5 destr array i *)
intros.
sdestruct (
 pointer_eq_dec (A:=A)
         (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil))) 
         (obj0, rptr)
); eauto.
unfold state_kind_inv in kind; simpl in *; invall; abstract congruence.

(* 4 destr fields nil *)
intros.
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p))) (obj0, rptr)
); eauto.
unfold state_kind_inv in kind; simpl in *; invall.
inversion H5; abstract congruence.

(* 3 destr base cons *)
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
         end))) (obj0, rptr)
); eauto.
unfold state_kind_inv in kind; simpl in *; invall.
inversion H6; abstract congruence.

(* 2 destr base direct non virtual nil Kdestrother bases *)
intros.
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, hp)) (obj0, rptr)
); eauto.
destruct hp; unfold state_kind_inv in kind; simpl in *; invall.
inversion H2; abstract congruence.

(* 1 destr base virtual nil *)
intros.
sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h, p))) (obj0, rptr)
); eauto.
unfold state_kind_inv in kind; simpl in *; invall.
inversion H3; abstract congruence.

Qed.




End Preservation.