Require Import Relations.
Require Import Coqlib.
Require Import LibPos.
Require Import Maps.
Require Import LibLists.
Require Import Cppsem.
Require Import Cplusconcepts.
Require Import CplusWf.
Require Import Events.
Require Import Smallstep.
Require Import Wellfounded.
Require Import CplusWf.
Load Param.
Open Scope nat_scope.

Section Progress.

Variable A : ATOM.t.
Variable nativeop : Type.

Variable prog : Program.t A nativeop.
Notation hier := (Program.hierarchy prog).

Hypothesis hierarchy_wf : Well_formed_hierarchy.prop hier. (* needed for vbase_order_list *)



(* Hypotheses about destructors *)

Inductive has_trivial_destructor : ident -> Prop :=
| has_trivial_destructor_intro : forall cn hc,
  hier ! cn = Some hc ->      
  (forall b, In (Class.Inheritance.Repeated, b) (Class.super hc) -> has_trivial_destructor b)  ->
  (forall b, is_virtual_base_of hier b cn -> has_trivial_destructor b)  ->
  (forall fs, In fs (Class.fields hc) -> forall b n, FieldSignature.type fs = FieldSignature.Struct b n -> has_trivial_destructor b) ->
  forall lc, (Program.hierarchy prog) ! cn = Some lc ->
    forall m,
      Method.find (Program.destructor_sig prog) (Class.methods lc) = Some m ->
      forall mcode,
        Method.kind m = Method.concrete mcode ->
        forall mb,
          (Program.methods prog) ! mcode = Some mb ->
          Method_body.code mb = Sreturn None ->
          has_trivial_destructor cn.

Variable cppsem : cppsemparam.
Variable sem : semparam A nativeop.

Definition goal_destr cn := ( forall s1,
  match State.kind s1 with
    |  State.destr obj ar i (h, p) k1 k2 l =>
      last p = Some cn -> 
      forall c, hier ! cn = Some c ->
        (
          match k1 as k return Constructor.init_key_secondary k -> list (Constructor.init_key_item A k) -> Prop with
            | Constructor.base =>
              fun k2' l' => forall x, In x l' ->
                match k2' with
                  | Constructor.direct_non_virtual => In (Class.Inheritance.Repeated, x) (Class.super c)
                  | _ => is_virtual_base_of hier x cn
                end
            | Constructor.field => fun _ l' => forall x, In x l' -> In x (Class.fields c)
          end
        ) k2 l ->     
        exists s2,
          star _ (step prog cppsem (sem := sem)) s1 E0 s2 /\
          State.kind s2 = State.destr obj ar i (h, p) k1 k2 nil /\
          State.deallocated_objects s2 = State.deallocated_objects s1 /\
          State.stack s2 = State.stack s1
    | _ => True
  end) /\ (forall s1,
  match State.kind s1 with
    | State.destr_array obj ar i cn' =>
      cn = cn' ->
      (-1 <= i)%Z ->
      exists s2,
        star _ (step prog cppsem (sem := sem)) s1 E0 s2 /\
        State.kind s2 = State.destr_array obj ar (-1) cn /\
        State.deallocated_objects s2 = State.deallocated_objects s1 /\
        State.stack s2 = State.stack s1      
    | _ => True
  end).


Lemma progress'_destr : forall cn, has_trivial_destructor cn -> goal_destr cn.
Proof.
  induction 1.
  unfold goal_destr.
  asplit.

  (* destr *)
  destruct s1.
  destruct kind; simpl; intros; subst; trivial.
  destruct inhpath.
  intros.
  replace lc with hc in * by congruence.
  replace hc with c in * by congruence.
  subst.
  revert construction_states field_construction_states deallocated_objects global.
  induction bases.
   simpl.
   intros.
   esplit.
   esplit.
   eleft.
   simpl.
   eauto.
   destruct k.

    (* base *)
    intros.
    generalize (H13 _ (or_introl _ (refl_equal _))).
    intros.
    assert (has_trivial_destructor a).
     destruct kind; eauto.
    assert (goal_destr a).
     destruct kind; eauto.
    inversion H15; subst.
    assert (Hlast : (last match kind with
                  | Constructor.direct_non_virtual => l ++ a :: nil
                  | Constructor.virtual => a :: nil
                end) = Some a).
     destruct kind.
      rewrite last_complete.
      reflexivity.
     reflexivity.     
    assert (hp' : is_some (last match kind with
                  | Constructor.direct_non_virtual => l ++ a :: nil
                  | Constructor.virtual => a :: nil
                end)).
     rewrite Hlast.
     exact I.
    refine (_ (_ : step prog cppsem (sem := sem)
      (State.make
        (State.destr obj array array_index (t, l)
          Constructor.base kind
          (a :: bases)) stack global construction_states
        field_construction_states deallocated_objects) _ _)).
    Focus 2.
     eapply step_destr_base_cons with (hp' := hp').
     reflexivity.
     reflexivity.
     eassumption.
     eassumption.
     eassumption.
     eassumption.
     reflexivity.
     symmetry.
     eassumption.
    intro.
    refine (_ (_ : step prog cppsem (sem := sem)
      (State.make (State.codepoint (
         (PTree.set (Method_body.this mb0)
                 (Value.ptr
                    (Value.subobject obj array array_index
                       match kind with
                       | Constructor.direct_non_virtual => t
                       | Constructor.virtual => Class.Inheritance.Shared
                       end
                       match kind with
                       | Constructor.direct_non_virtual => l ++ a :: nil
                       | Constructor.virtual => a :: nil
                       end hp')) (PTree.empty (Value.t A))) 
      ) (Sreturn None) nil nil)
       (StackFrame.Kdestr obj array array_index
              (match kind with
               | Constructor.direct_non_virtual => t
               | Constructor.virtual => Class.Inheritance.Shared
               end,
              match kind with
              | Constructor.direct_non_virtual => l ++ a :: nil
              | Constructor.virtual => a :: nil
              end) ::
              StackFrame.Kdestrother obj array array_index 
              (t, l)
              Constructor.base kind a bases
              :: stack) global  
          ((obj,
           (array, array_index,
           (match kind with
            | Constructor.direct_non_virtual => t
            | Constructor.virtual => Class.Inheritance.Shared
            end,
           match kind with
           | Constructor.direct_non_virtual => l ++ a :: nil
           | Constructor.virtual => a :: nil
           end)), StartedDestructing) :: construction_states)
 field_construction_states
       deallocated_objects) E0
      (
        State.make
   (State.destr obj array array_index
             (match kind with
              | Constructor.direct_non_virtual => t
              | Constructor.virtual => Class.Inheritance.Shared
              end,
             match kind with
             | Constructor.direct_non_virtual => l ++ a :: nil
             | Constructor.virtual => a :: nil
             end)
             Constructor.field tt (rev (Class.fields _)))
          (StackFrame.Kdestrother obj array array_index 
             (t, l)
             Constructor.base kind a bases :: stack) global
          ((obj,
           (array, array_index,
           (match kind with
            | Constructor.direct_non_virtual => t
            | Constructor.virtual => Class.Inheritance.Shared
            end,
           match kind with
           | Constructor.direct_non_virtual => l ++ a :: nil
           | Constructor.virtual => a :: nil
           end)), StartedDestructing) :: construction_states)
          field_construction_states deallocated_objects
      ))).
     Focus 2.
     eapply (@step_Kdestr_return _ _ _ _ _).
     eassumption.
     eassumption.
     rewrite rev_involutive.
     reflexivity.
   intro.
   inversion H16 as [HH21a _].
   match goal with
     x0 : step _ _ _ _ ?s |- _ =>  generalize (HH21a s) 
   end.
   simpl.
   intro.
   refine (_ (H26 Hlast _ _ _)).
   2 : eassumption.
   Focus 2.
    intros.
    eapply In_rev.
    assumption.
   simpl; intros; invall; subst.
   destruct x2; simpl in *; subst; simpl in *.  
  refine (_ (_ : step prog cppsem (sem := sem)
 (State.make
             (State.destr obj array array_index
                (match kind with
                 | Constructor.direct_non_virtual => t
                 | Constructor.virtual => Class.Inheritance.Shared
                 end,
                match kind with
                | Constructor.direct_non_virtual => l ++ a :: nil
                | Constructor.virtual => a :: nil
                end)
                Constructor.field tt nil)
             (StackFrame.Kdestrother obj array array_index 
                (t, l)
                Constructor.base kind a bases :: stack) global0
             construction_states0 field_construction_states0 deallocated_objects)
 _ (
   State.make
   (State.destr obj array array_index
     (match kind with
        | Constructor.direct_non_virtual => t
        | Constructor.virtual => Class.Inheritance.Shared
      end,
     match kind with
       | Constructor.direct_non_virtual => l ++ a :: nil
       | Constructor.virtual => a :: nil
     end)
     Constructor.base Constructor.direct_non_virtual
     (rev (map
       (fun hb : Class.Inheritance.t * ident =>
         let (_, b) := hb in b)
       (filter
              (fun hb : Class.Inheritance.t * ident =>
                let (y, _) := hb in
                  match y with
                    | Class.Inheritance.Repeated => true
                    | Class.Inheritance.Shared => false
                  end) (Class.super _)))))
        (StackFrame.Kdestrother obj array array_index 
          (t, l)
          Constructor.base kind a bases :: stack) global0
        ((obj,
          (array, array_index,
            (match kind with
               | Constructor.direct_non_virtual => t
               | Constructor.virtual => Class.Inheritance.Shared
             end,
            match kind with
              | Constructor.direct_non_virtual => l ++ a :: nil
              | Constructor.virtual => a :: nil
            end)), DestructingBases) :: construction_states0)
        field_construction_states0 deallocated_objects
))).
  Focus 2.
  econstructor.
   eassumption.
   eassumption.
   rewrite rev_involutive.
   reflexivity.
  intro.
  match goal with
    x2 : step _ _ _ _ ?s |- _ =>  generalize (HH21a s) 
  end.
  simpl.
  intros; invall; subst.
  refine (_ (H27 _ _ _ _)).
  2 : assumption.
  2 : eassumption.
  Focus 2.
   intros.
   eapply in_map_bases_elim.
   eapply In_rev.
   eassumption.
  intro; invall; subst.
  destruct x3; simpl in *; subst; simpl in *.
  refine (_ (_ : step prog cppsem (sem := sem)
    (State.make
      (State.destr obj array array_index
        (match kind with
           | Constructor.direct_non_virtual => t
           | Constructor.virtual => Class.Inheritance.Shared
         end,
        match kind with
          | Constructor.direct_non_virtual => l ++ a :: nil
          | Constructor.virtual => a :: nil
        end)
        Constructor.base Constructor.direct_non_virtual nil)
      (StackFrame.Kdestrother obj array array_index 
        (t, l)
        Constructor.base kind a bases :: stack) global1
      construction_states1 field_construction_states1 deallocated_objects)
    _ _
  )).
   Focus 2.
   econstructor.
  intros.
 generalize (IHbases (fun x Hx => H13 _ (or_intror _ Hx)) ((obj,
             (array, array_index,
             (match kind with
              | Constructor.direct_non_virtual => t
              | Constructor.virtual => Class.Inheritance.Shared
              end,
             match kind with
             | Constructor.direct_non_virtual => l ++ a :: nil
             | Constructor.virtual => a :: nil
             end)), Destructed) :: construction_states1) field_construction_states1 deallocated_objects global1).
 intros; invall; subst.
 esplit.
 esplit.
 eapply star_left.
 eassumption.
 eapply star_left.
 eassumption.
 eapply star_trans.
 eapply evtr_sem.
 eassumption.
 eapply star_left.
 eassumption.
 eapply star_trans.
 eapply evtr_sem.
 eassumption.
 eapply star_left.
 eassumption.
 eassumption.
 reflexivity.
 reflexivity.
 reflexivity.
 reflexivity.
 reflexivity.
 repeat rewrite E0_left; eauto using evtr_sem.
 eauto.

 (* field *)
 intros.
 destruct kind.
 case_eq (FieldSignature.type a).
  (* scalar *)
  intros.
   refine (_ (_ :
(step prog cppsem (sem := sem))
           (State.make
              (State.destr obj array array_index (t, l)
                Constructor.field tt (a :: bases)) stack global
              construction_states field_construction_states deallocated_objects) _ _
   )).
    Focus 2.
    eapply step_destr_field_scalar.
    reflexivity.
    eassumption.
   intro.
   generalize (IHbases (fun x y => H13 _ (or_intror _ y)) construction_states ((obj, array, array_index, (t, l), a, Destructed)
             :: field_construction_states)  deallocated_objects  (Globals.update global (remove_field (obj, array, array_index, (t, l), a) (Globals.field_values global)))).
   intros; invall; subst.
   esplit.
   esplit.
   eapply star_left.
   eassumption.
   eassumption.
   rewrite E0_left; eauto using evtr_sem.
   eauto.

  (* struct *)
  intros. 
  generalize (H13 _ (or_introl _ (refl_equal _))).
  intro.
  generalize (H5 _ H15 _ _ H14).
  destruct 1 as [_ ?].
  refine (_ (_ :
 (step prog cppsem (sem := sem))
           (State.make
              (State.destr obj array array_index (t, l)
                 Constructor.field tt (a :: bases)) stack global
              construction_states field_construction_states deallocated_objects) _ _
  )).
   Focus 2.
   eapply step_destr_field_struct.
   eassumption.
   reflexivity.
   reflexivity.
  intro.
  match goal with
    x : step _ _ _ _ ?s |- _ => generalize (H16 s (refl_equal _))
  end.
  Opaque Zminus. simpl.
  intros.
  assert (-1 <= Zpos arraysize - 1)%Z.
   Transparent Zminus.
   compute.
   destruct arraysize; intros; discriminate.
  generalize (H17 H18).
  intros; invall; subst.
  Opaque Zminus.
  destruct x0; simpl in *; subst; simpl in *.
  refine (_ (_ :  (step prog cppsem (sem := sem))
 (State.make
             (State.destr_array obj
                (array ++ (array_index, (t, l), a) :: nil) 
                (-1) struct)
             (StackFrame.Kdestrother obj array array_index 
                (t, l)
                Constructor.field tt a bases :: stack) global0
             construction_states0 field_construction_states0 deallocated_objects) _ _
  )).
   Focus 2.
   eapply step_destr_array_nil_fields.
   reflexivity.
  intros.
   generalize (IHbases (fun x y => H13 _ (or_intror _ y)) construction_states0 ((obj, array, array_index, (t, l), a, Destructed)
             :: field_construction_states0)  deallocated_objects  ( global0)).
   intros; invall; subst.
   esplit.
   esplit.   
    eapply star_left.
    eassumption.
    eapply star_trans.
    apply evtr_sem.
    eassumption.
    eapply star_left.
    eassumption.
    eassumption.
   reflexivity.
   reflexivity.
   repeat rewrite E0_left; eauto using evtr_sem.
   eauto.

(* array *)
destruct s1.
destruct kind; simpl in *; trivial.
intro; subst.
revert array_index global construction_states field_construction_states deallocated_objects.
cut (
forall n array_index,  Z_of_nat n = (array_index + 1)%Z -> forall global construction_states field_construction_states deallocated_objects,
  exists s2 : State.t A nativeop,
    star (evtr sem) (step prog cppsem (sem := sem))
    (State.make
      (State.destr_array obj array array_index class) stack global construction_states
      field_construction_states deallocated_objects) E0 s2 /\
    State.kind s2 =
    State.destr_array obj array (-1) class /\
    State.deallocated_objects s2 = deallocated_objects /\
    State.stack s2 = stack  
).
 intros.
 assert (0 <= array_index + 1)%Z by abstract omega.
 generalize (Z_of_nat_complete _ H14).
 intros; invall; subst; eauto.
induction n.
 (* 0 *)
 simpl.
 intros.
 assert (array_index = (-1))%Z by abstract omega.
 subst.
 esplit.
 esplit.
 eapply star_refl.
 simpl; eauto.
(* S *)
rewrite inj_S.
unfold Zsucc.
generalize (Zle_0_nat n).
intros.
Transparent Zminus.
Require Import ROmega.
 assert (Z_of_nat n = (array_index - 1 + 1))%Z by abstract romega.
 rewrite H14 in H12.
 refine (_ (_ : step prog cppsem (sem := sem)
   (State.make (State.destr_array obj array array_index class) stack
               global construction_states field_construction_states
               deallocated_objects) E0 _
 )).
  Focus 2.
  eapply step_destr_array with (hp := I).
  romega.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  reflexivity.
  symmetry. eassumption.
 intro.
 refine (_ (_ : step prog cppsem (sem := sem)
   (State.make (State.codepoint (
     (PTree.set (Method_body.this mb)
       (Value.ptr
         (Value.subobject obj array array_index Class.Inheritance.Repeated (class :: nil) I)) (PTree.empty (Value.t A))) 
      ) (Sreturn None) nil nil)
       (StackFrame.Kdestr obj array array_index
              (Class.Inheritance.Repeated,
                class :: nil
              ) ::
              StackFrame.Kdestrcell obj array array_index 
              class
              :: stack) global  
          ((obj,
           (array, array_index,
             (Class.Inheritance.Repeated
               ,
           class :: nil
           )), StartedDestructing) :: construction_states)
 field_construction_states
       deallocated_objects) E0
      (
        State.make
   (State.destr obj array array_index
             (Class.Inheritance.Repeated
              ,
              class :: nil
             )
             Constructor.field tt (rev (Class.fields _)))
          (StackFrame.Kdestrcell obj array array_index 
            class
            :: stack) global
          ((obj,
           (array, array_index,
           (Class.Inheritance.Repeated,
           class :: nil
           )), StartedDestructing) :: construction_states)
          field_construction_states deallocated_objects
      ))).
     Focus 2.
     eapply (@step_Kdestr_return _ _ _ _ _).
     reflexivity.
     eassumption.
     rewrite rev_involutive.
     reflexivity.
   intro.
   match goal with
     x0 : step _ _ _ _ ?s |- _ =>  generalize (H11 s (refl_equal _)) 
   end.
   simpl.
   intro.
   refine (_ (H15 _ _ _)).
   2 : eassumption.
   Focus 2.
    intros.
    eapply In_rev.
    assumption.
   simpl; intros; invall; subst.
   destruct x2; simpl in *; subst; simpl in *.  
  refine (_ (_ : step prog cppsem (sem := sem)
 (State.make
             (State.destr obj array array_index
                (Class.Inheritance.Repeated
                 ,
                class :: nil
                )
                Constructor.field tt nil)
             (StackFrame.Kdestrcell obj array array_index 
                class
                :: stack) global0
             construction_states0 field_construction_states0 deallocated_objects)
 _ (
   State.make
   (State.destr obj array array_index
     (Class.Inheritance.Repeated
       ,
       class :: nil
     )
     Constructor.base Constructor.direct_non_virtual
     (rev (map
       (fun hb : Class.Inheritance.t * ident =>
         let (_, b) := hb in b)
       (filter
              (fun hb : Class.Inheritance.t * ident =>
                let (y, _) := hb in
                  match y with
                    | Class.Inheritance.Repeated => true
                    | Class.Inheritance.Shared => false
                  end) (Class.super _)))))
        (StackFrame.Kdestrcell obj array array_index 
          class :: stack) global0
        ((obj,
          (array, array_index,
            (Class.Inheritance.Repeated
             ,
              class :: nil
            )), DestructingBases) :: construction_states0)
        field_construction_states0 deallocated_objects
))).
  Focus 2.
  econstructor.
   reflexivity.
   eassumption.
   rewrite rev_involutive.
   reflexivity.
  intro.
  match goal with
    x2 : step _ _ _ _ ?s |- _ =>  generalize (H11 s (refl_equal _)) 
  end.
  simpl.
  intros; invall; subst.
  refine (_ (H16 _ _ _)).
  2 : eassumption.
  Focus 2.
   intros.
   eapply in_map_bases_elim.
   eapply In_rev.
   eassumption.
  intro; invall; subst.
  destruct x3; simpl in *; subst; simpl in *.
generalize (Well_formed_hierarchy.vborder_list_exists hierarchy_wf H).
destruct 1.
rewrite <- (rev_involutive x2) in v.
  refine (_ (_ : step prog cppsem (sem := sem)    
    (State.make
      (State.destr obj array array_index
        (Class.Inheritance.Repeated
          ,
          class :: nil
        )
        Constructor.base Constructor.direct_non_virtual nil)
      (StackFrame.Kdestrcell obj array array_index 
        class
        :: stack) global1
      construction_states1 field_construction_states1 deallocated_objects)
    E0 
    ((State.make (State.destr obj array array_index (Class.Inheritance.Repeated, class :: nil) Constructor.base Constructor.virtual (rev x2)) stack global1 construction_states1 field_construction_states1 deallocated_objects))
  )).
   Focus 2.
   eapply step_destr_base_non_virtual_nil_cell.
   eassumption.
   congruence.
 intro.
  match goal with
    x2 : step _ _ _ _ ?s |- _ =>  generalize (H11 s (refl_equal _)) 
  end.
  simpl.
  intros; invall; subst.
  refine (_ (H18 _ _ _)).
  2 : eassumption.
  2 : intros; eapply vborder_list_virtual_base.
  3 : eassumption.
  2 : assumption.
  2 : eapply In_rev.
  2 : rewrite rev_involutive.
  2 : assumption.
  intro; invall; subst.
destruct x5; simpl in *; subst; simpl in *.
refine (_ (_ :
step prog cppsem (sem := sem)
 (State.make
             (State.destr obj array array_index
                (Class.Inheritance.Repeated, class :: nil) Constructor.base
                Constructor.virtual nil) stack global2 construction_states2
             field_construction_states2 deallocated_objects) E0 _
)).
  2 : eapply step_destr_base_virtual_nil.
  2 : reflexivity.
  2 : reflexivity.
intro.
generalize (
IHn _ H14 global2  ((obj,
             (array, array_index, (Class.Inheritance.Repeated, class :: nil)),
             Destructed) :: construction_states2) field_construction_states2 deallocated_objects
).
destruct 1; invall; subst.
esplit.
esplit.
eapply star_left.
eassumption.
eapply star_left.
eassumption.
eapply star_trans.
apply evtr_sem.
eassumption.
eapply star_left.
eassumption.
eapply star_trans.
apply evtr_sem.
eassumption.
eapply star_left.
eassumption.
eapply star_trans.
apply evtr_sem.
eassumption.
eapply star_left.
eassumption.
eassumption.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
eauto.

Qed.

Corollary progress_destr : forall gl obj o,
    (Globals.heap gl) ! obj = Some o ->
    has_trivial_destructor (Object.class o) ->
    (0 <= Object.arraysize o)%Z ->
    forall sdestruct sdestruct',
      exit_succ sdestruct = Some sdestruct' ->      
      forall vars stl0 stl bl stk cs auxcs f,
        exists gl', exists cs', exists auxcs',
          star _ (step prog cppsem (sem := sem))
          (State.make (State.codepoint vars sdestruct stl0 (BlockPoint.make stl (Some obj) :: bl)) stk gl cs auxcs f) E0
          (State.make (State.codepoint vars sdestruct' stl bl) stk gl' cs' auxcs' (obj :: f)).
Proof.
  intros.
  refine (_ (_ : step prog cppsem (sem := sem)
    (State.make  (State.codepoint vars sdestruct stl0 (BlockPoint.make stl (Some obj) :: bl)) stk gl cs auxcs f) E0 _)).
  Focus 2.
  econstructor.
  eapply exit_succ_requires_destruct.
  congruence.
  eassumption.
  reflexivity.
  reflexivity.
 intro.
 destruct (progress'_destr H0).
 assert (-1 <= Object.arraysize o - 1)%Z by romega.
 match goal with
   _ : step _ _ _ _ ?s |- _ =>  generalize (H4 s (refl_equal _) H5)
 end.
 Opaque Zminus. simpl; intros; invall; subst.
 destruct x0; simpl in *; subst; simpl in *.
 refine (_ (_ :
   step prog cppsem (sem := sem)
   (State.make (State.destr_array obj nil (-1) (Object.class o))
            (StackFrame.Kcontinue (StackFrame.continue_destr (A:=A) vars)
               sdestruct obj stl bl :: stk) global construction_states
            field_construction_states deallocated_objects)
   E0 _
 )).
 Focus 2.
 eapply step_destr_array_nil_continue.
 reflexivity.
 reflexivity.
 eassumption.
 reflexivity.
intro.            
esplit.
esplit.
esplit.
eapply star_left.
eassumption.
eapply star_trans.
eapply evtr_sem.
eassumption.
eapply star_left.
eassumption.
eleft.
reflexivity.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
Qed.

(* Hypotheses about constructors *)

Inductive has_nearly_trivial_constructor : ident -> Prop :=
| has_nearly_trivial_constructors_intro : forall cn hc,
  hier ! cn = Some hc ->      
  (forall b, In (Class.Inheritance.Repeated, b) (Class.super hc) -> has_nearly_trivial_constructor b)  ->
  (forall b, is_virtual_base_of hier b cn -> has_nearly_trivial_constructor b)  ->
  (forall fs, In fs (Class.fields hc) -> forall b n, FieldSignature.type fs = FieldSignature.Struct b n -> has_nearly_trivial_constructor b) ->
  forall lc, (Program.constructors prog) ! cn = Some lc ->
    forall c, 
      assoc (@Program.constructor_key_eq_dec A) nil lc = Some c ->
      (forall b, In (Class.Inheritance.Repeated, b) (Class.super hc) -> assoc (@Constructor.initializer_key_eq_dec A) (existT _ Constructor.base (Constructor.direct_non_virtual, b)) (Constructor.initializers c) = Some (Sconstructor b nil)) ->
      (forall b, is_virtual_base_of hier b cn ->
        assoc (@Constructor.initializer_key_eq_dec A) (existT _ Constructor.base (Constructor.virtual, b)) (Constructor.initializers c) = Some (Sconstructor b nil)) ->
      (forall fs, In fs (Class.fields hc) ->
        forall b n, FieldSignature.type fs = FieldSignature.Struct b n ->
          assoc (@FieldSignature.eq_dec _) fs (Constructor.struct_field_initializers c) = None) ->
      (forall fs, In fs (Class.fields hc) ->
        forall ty, FieldSignature.type fs = FieldSignature.Scalar ty -> (
          (enable_uninitialized_scalar_fields cppsem = false -> assoc (@Constructor.initializer_key_eq_dec A) (existT _ Constructor.field (tt, fs)) (Constructor.initializers c) <> None) /\ forall st, assoc (@Constructor.initializer_key_eq_dec A) (existT _ Constructor.field (tt, fs)) (Constructor.initializers c) = Some st ->
            exists aty, ty = Typ.atom aty /\
              exists op, (exists tr, exists va, nativeop_sem (s := sem) op nil (Some (existT _ aty va)) tr) /\
                exists v, st = Sseq (Snative op nil (Some v)) (Sinitscalar v))) ->
      Constructor.body c = Sreturn None ->
      has_nearly_trivial_constructor cn.

Definition goal cn := ( forall s1,
  match State.kind s1 with
    |  State.constr obj ar i (h, p) tinit init body vars k1 k2 l =>
      last p = Some cn -> 
      forall c, hier ! cn = Some c ->
        (
          match k1 as k return Constructor.init_key_secondary k -> list (Constructor.init_key_item A k) -> Prop with
            | Constructor.base =>
              fun k2' l' => forall x, In x l' ->
                match k2' with
                  | Constructor.direct_non_virtual => In (Class.Inheritance.Repeated, x) (Class.super c)
                  | _ => is_virtual_base_of hier x cn
                end
            | Constructor.field => fun _ l' => forall x, In x l' -> In x (Class.fields c)
          end
        ) k2 l ->     
        forall lc, (Program.constructors prog) ! cn = Some lc ->
          forall c, assoc (@Program.constructor_key_eq_dec A) nil lc = Some c ->
            tinit = Constructor.struct_field_initializers c ->
            init = Constructor.initializers c ->
            body = Constructor.body c ->
            exists tr, exists s2, exists vars',
              star _ (step prog cppsem (sem := sem)) s1 tr s2 /\
              (Globals.heap (State.global s2)) ! obj = (Globals.heap (State.global s1)) ! obj /\
              State.kind s2 = State.constr obj ar i (h, p) tinit init body vars' k1 k2 nil /\
              State.deallocated_objects s2 = State.deallocated_objects s1 /\
              State.stack s2 = State.stack s1              
    | _ => True
  end) /\ (forall s1,
  match State.kind s1 with
    | State.constr_array obj ar n i cn' tinit vars =>
      cn = cn' ->
      tinit = (fun _ => Sconstructor cn' nil) ->
      (0 <= i <= n)%Z ->
      exists tr, exists s2,
        star _ (step prog cppsem (sem := sem)) s1 tr s2 /\
        (Globals.heap (State.global s2)) ! obj = (Globals.heap (State.global s1)) ! obj /\
        State.kind s2 = State.constr_array obj ar n n cn tinit vars /\
        State.deallocated_objects s2 = State.deallocated_objects s1 /\
              State.stack s2 = State.stack s1
    | _ => True
  end).

Lemma progress' : forall cn, has_nearly_trivial_constructor cn -> goal cn.
Proof.
  induction 1.
  unfold goal.
  asplit.

  (* constr *)
  destruct s1.
  destruct kind; simpl; intros; subst; trivial.
  destruct inhpath.
  intros.
  subst.
  replace c0 with hc in * by abstract congruence.
  replace lc0 with lc in * by abstract congruence.
  replace c1 with c in * by abstract congruence.
  revert vars construction_states field_construction_states deallocated_objects global.
  induction bases.
   simpl.
   intros.
   esplit.
   esplit.
   esplit.
   split.
   eleft.
   simpl.
   split; eauto.
   destruct k.

    (* base *)
    intros.
    generalize (H15 _ (or_introl _ (refl_equal _))).
    intros.
    assert (assoc (Constructor.initializer_key_eq_dec (A:=A))
         (existT (Constructor.init_subkey A) Constructor.base
           (kind, a)) (Constructor.initializers c) = Some (Sconstructor a nil)).
     destruct kind; eauto.
    assert (has_nearly_trivial_constructor a).
     destruct kind; eauto.
    assert (goal a).
     destruct kind; eauto.
    inversion H20; subst.
    refine (_ (_ : step prog cppsem (sem := sem)
      (State.make
        (State.constr obj array array_index (t, l)
          (Constructor.struct_field_initializers c)
          (Constructor.initializers c) (Constructor.body c) vars
          Constructor.base kind
          (a :: bases)) stack global construction_states
        field_construction_states deallocated_objects) _ _)).
    Focus 2.
     eapply step_constr_cons.
     trivial.
     symmetry.
     simpl in *.
     rewrite H19.
     reflexivity.
    intro.
    assert (Hlast : (last match kind with
                  | Constructor.direct_non_virtual => l ++ a :: nil
                  | Constructor.virtual => a :: nil
                end) = Some a).
     destruct kind.
      rewrite last_complete.
      reflexivity.
     reflexivity.     
    assert (hp' : is_some (last match kind with
                  | Constructor.direct_non_virtual => l ++ a :: nil
                  | Constructor.virtual => a :: nil
                end)).
     rewrite Hlast.
     exact I.
    refine (_ (_ : step prog cppsem (sem := sem)
      (State.make (State.codepoint vars (Sconstructor a nil) nil nil)
        (StackFrame.Kconstr obj array array_index 
          (t, l) (Constructor.struct_field_initializers c)
          (Constructor.initializers c) (Constructor.body c)
          Constructor.base kind a bases
          :: stack) global construction_states field_construction_states
        deallocated_objects) _ 
      (
        State.make
        (State.constr obj array array_index
          (match kind with
             | Constructor.direct_non_virtual => t
             | Constructor.virtual => Class.Inheritance.Shared
           end,
          match kind with
            | Constructor.direct_non_virtual => l ++ a :: nil
            | Constructor.virtual => a :: nil
          end) (Constructor.struct_field_initializers _)
          (Constructor.initializers _) (Constructor.body _)
          (set_params
            (Value.ptr
              (Value.subobject obj array array_index
                match kind with
                  | Constructor.direct_non_virtual => t
                  | Constructor.virtual => Class.Inheritance.Shared
                end
                match kind with
                  | Constructor.direct_non_virtual => l ++ a :: nil
                  | Constructor.virtual => a :: nil
                end hp') :: nil)
            (Constructor.this _ :: Constructor.args _))
          Constructor.base Constructor.direct_non_virtual
          (map
            (fun hb : Class.Inheritance.t * ident =>
              let (_, b) := hb in b)
            (filter
              (fun hb : Class.Inheritance.t * ident =>
                let (y, _) := hb in
                  match y with
                    | Class.Inheritance.Repeated => true
                    | Class.Inheritance.Shared => false
                  end) (Class.super _))))
        (StackFrame.Kconstrother obj array array_index 
          (t, l) (Constructor.struct_field_initializers c)
          (Constructor.initializers c) (Constructor.body c) vars
          Constructor.base kind a bases :: stack) global
        ((obj,
          (array, array_index,
            (match kind with
               | Constructor.direct_non_virtual => t
               | Constructor.virtual => Class.Inheritance.Shared
             end,
            match kind with
              | Constructor.direct_non_virtual => l ++ a :: nil
              | Constructor.virtual => a :: nil
            end)), StartedConstructing) :: construction_states)
        field_construction_states deallocated_objects
      ))).
     Focus 2.
     eapply (@step_Kconstr_base _ _ _ _ _ nil).
     reflexivity.
     eassumption.
     eassumption.
     reflexivity.
     reflexivity.
     reflexivity.
     reflexivity.
     reflexivity.
     reflexivity.
     eassumption.
     reflexivity.
   intro.
   inversion H21 as [HH21a _].
   match goal with
     x0 : step _ _ _ _ ?s |- _ =>  generalize (HH21a s) 
   end.
   simpl.
   intro.
   generalize (H33 Hlast _ H22 (@in_map_bases_elim _) _ H26 _ H27 (refl_equal _) (refl_equal _) (refl_equal _)).
   simpl; intros; invall; subst.
   destruct x2; simpl in *; subst; simpl in *.  
   rename H35 into Hglobalobj1.
  refine (_ (_ : step prog cppsem (sem := sem)
 (State.make
             (State.constr obj array array_index
                (match kind with
                 | Constructor.direct_non_virtual => t
                 | Constructor.virtual => Class.Inheritance.Shared
                 end,
                match kind with
                | Constructor.direct_non_virtual => l ++ a :: nil
                | Constructor.virtual => a :: nil
                end) (Constructor.struct_field_initializers c2)
                (Constructor.initializers c2) (Constructor.body c2) x3
                Constructor.base Constructor.direct_non_virtual nil)
             (StackFrame.Kconstrother obj array array_index 
                (t, l) (Constructor.struct_field_initializers c)
                (Constructor.initializers c) (Constructor.body c) vars
                Constructor.base kind a bases :: stack) global0
             construction_states0 field_construction_states0 deallocated_objects)
 _ (
   State.make
   (State.constr obj array array_index
             (match kind with
              | Constructor.direct_non_virtual => t
              | Constructor.virtual => Class.Inheritance.Shared
              end,
             match kind with
             | Constructor.direct_non_virtual => l ++ a :: nil
             | Constructor.virtual => a :: nil
             end) (Constructor.struct_field_initializers c2)
             (Constructor.initializers c2) (Constructor.body c2) x3
             Constructor.field tt (Class.fields _))
          (StackFrame.Kconstrother obj array array_index 
             (t, l) (Constructor.struct_field_initializers c)
             (Constructor.initializers c) (Constructor.body c) vars
             Constructor.base kind a bases :: stack) global0
          ((obj,
           (array, array_index,
           (match kind with
            | Constructor.direct_non_virtual => t
            | Constructor.virtual => Class.Inheritance.Shared
            end,
           match kind with
           | Constructor.direct_non_virtual => l ++ a :: nil
           | Constructor.virtual => a :: nil
           end)), BasesConstructed) :: construction_states0)
          field_construction_states0 deallocated_objects
))).
  Focus 2.
   econstructor.
   eassumption.
   eassumption.
   reflexivity.
  intro.
  match goal with
    x2 : step _ _ _ _ ?s |- _ =>  generalize (HH21a s) 
  end.
  simpl.
  intros; invall; subst.
  generalize (H35 Hlast _ H22 (fun x y => y) _ H26 _ H27 (refl_equal _) (refl_equal _) (refl_equal _)).
  intro; invall; subst.
  destruct x5; simpl in *; subst; simpl in *.
  rename H37 into Hglobalobj2.
  refine (_ (_ : step prog cppsem (sem := sem)
    (State.make
      (State.constr obj array array_index
        (match kind with
           | Constructor.direct_non_virtual => t
           | Constructor.virtual => Class.Inheritance.Shared
         end,
        match kind with
          | Constructor.direct_non_virtual => l ++ a :: nil
          | Constructor.virtual => a :: nil
        end) (Constructor.struct_field_initializers c2)
        (Constructor.initializers c2) (Constructor.body c2) x6
        Constructor.field tt nil)
      (StackFrame.Kconstrother obj array array_index 
        (t, l) (Constructor.struct_field_initializers c)
        (Constructor.initializers c) (Constructor.body c) vars
        Constructor.base kind a bases :: stack) global1
      construction_states1 field_construction_states1 deallocated_objects)
    _ _
  )).
   Focus 2.
   econstructor.
  intros.
  refine (_ (_ : step prog cppsem (sem := sem)
(State.make (State.codepoint x6 (Constructor.body c2) nil nil)
            (StackFrame.Kconstrother obj array array_index 
               (t, l) (Constructor.struct_field_initializers c)
               (Constructor.initializers c) (Constructor.body c) vars
               Constructor.base kind a bases :: stack) global1
            construction_states1 field_construction_states1 deallocated_objects)
_ _)).
  Focus 2.
  rewrite H32.
  econstructor.
  reflexivity.
  reflexivity.
 intro.
 generalize (IHbases (fun x Hx => H15 _ (or_intror _ Hx)) vars ((obj,
             (array, array_index,
             (match kind with
              | Constructor.direct_non_virtual => t
              | Constructor.virtual => Class.Inheritance.Shared
              end,
             match kind with
             | Constructor.direct_non_virtual => l ++ a :: nil
             | Constructor.virtual => a :: nil
             end)), Constructed) :: construction_states1) field_construction_states1 deallocated_objects global1).
 intros; invall; subst.
 esplit.
 esplit.
 esplit.
 split.
 eapply star_left.
 eassumption.
 eapply star_left.
 eassumption.
 eapply star_trans.
 eapply evtr_sem.
 eassumption.
 eapply star_left.
 eassumption.
 eapply star_trans.
 eapply evtr_sem.
 eassumption.
 eapply star_left.
 eassumption.
 eapply star_left.
 eassumption.
 eassumption.
 reflexivity.
 reflexivity.
 reflexivity.
 reflexivity.
 reflexivity.
 reflexivity.
 reflexivity.
 split.
 repeat (eapply trans_equal; [eassumption |]).
 trivial.
 eauto.

 (* field *)
 intros.
 destruct kind.
 generalize (H15 _ (or_introl _ (refl_equal _))).
 intros.
 case_eq (FieldSignature.type a).
  (* scalar *)
  intros.
  destruct (H11 _ H18 _ H19).
  case_eq (
    assoc (Constructor.initializer_key_eq_dec (A:=A))
    (existT (Constructor.init_subkey A) Constructor.field (tt, a))
    (Constructor.initializers c)
  ).
   (* some init *)
   intros.
   generalize (H21 _ H22).
   intros; invall; subst.
   refine (_ (_ :
     (step prog cppsem (sem := sem))
     (State.make
       (State.constr obj array array_index (t, l)
         (Constructor.struct_field_initializers c)
         (Constructor.initializers c) (Constructor.body c) vars
         Constructor.field tt (a :: bases)) stack global
       construction_states field_construction_states deallocated_objects) _ _     
   )).
    Focus 2.
    eapply step_constr_cons.
    rewrite H19; trivial.
    eassumption.
   intros.
   refine (_ (_ :
     (step prog cppsem (sem := sem))     
     (State.make
            (State.codepoint vars
               (Sseq (Snative x0 nil (Some x1)) (Sinitscalar x1)) nil nil)
            (StackFrame.Kconstr obj array array_index 
               (t, l) (Constructor.struct_field_initializers c)
               (Constructor.initializers c) (Constructor.body c)
               Constructor.field tt a bases :: stack) global
            construction_states field_construction_states deallocated_objects) _ _
   )).
    Focus 2.
     econstructor.
   intro.
   refine (_ (_ :
     (step prog cppsem (sem := sem))
 (State.make
            (State.codepoint vars (Snative x0 nil (Some x1))
               (Sinitscalar x1 :: nil) nil)
            (StackFrame.Kconstr obj array array_index 
               (t, l) (Constructor.struct_field_initializers c)
               (Constructor.initializers c) (Constructor.body c)
               Constructor.field tt a bases :: stack) global
            construction_states field_construction_states deallocated_objects) _ _
   )).
    Focus 2.
    eapply (@step_Snative _ _ _ _ _ nil).
    reflexivity.
    eassumption.
    eauto.
   intro.
   refine (_ (_ :
     (step prog cppsem (sem := sem))
     (State.make
       (State.codepoint (PTree.set x1 (Value.atom x x3) vars) Sskip
         (Sinitscalar x1 :: nil) nil)
       (StackFrame.Kconstr obj array array_index 
         (t, l) (Constructor.struct_field_initializers c)
         (Constructor.initializers c) (Constructor.body c)
         Constructor.field tt a bases :: stack) global
       construction_states field_construction_states deallocated_objects) _ _
   )).
    Focus 2.
    econstructor.
   intros.
   refine (_ (_ :
     (step prog cppsem (sem := sem))
     (State.make
            (State.codepoint (PTree.set x1 (Value.atom x x3) vars)
               (Sinitscalar x1) nil nil)
            (StackFrame.Kconstr obj array array_index 
               (t, l) (Constructor.struct_field_initializers c)
               (Constructor.initializers c) (Constructor.body c)
               Constructor.field tt a bases :: stack) global
            construction_states field_construction_states deallocated_objects) _ _
   )).
    Focus 2.
    econstructor.
    eassumption.
    rewrite PTree.gss.
    reflexivity.
    eassumption.
    exact I.
   unfold Globals.put_field. 
   rewrite H19.
   simpl.
   destruct (
     ATOM.ty_eq_dec (t:=A) x x
   ).
    reflexivity.
   destruct n; trivial.
   reflexivity.
  intros.
  generalize (IHbases (fun x y => H15 _ (or_intror _ y)) (PTree.set x1 (Value.atom x x3) vars) construction_states ((obj, array, array_index, (t, l), a, Constructed)
             :: field_construction_states)  deallocated_objects  (Globals.update global
               (update_field (obj, array, array_index, (t, l), a)
                  (Value.atom x x3) (Globals.field_values global)))).
  intros; invall; subst.
  esplit.
  esplit.
  esplit.
  split.
  eapply star_left.
  eassumption.
  eapply star_left.
  eassumption.
  eapply star_left.
  eassumption.
  eapply star_left.
  eassumption.
  eapply star_left.
  eassumption.
  eassumption.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  simpl.
 split.
 repeat (eapply trans_equal; [eassumption |]).
 destruct global; reflexivity.
 eauto.

  (* no init *)
  case_eq (enable_uninitialized_scalar_fields cppsem).
   intros.
   refine (_ (_ :
(step prog cppsem (sem := sem))
           (State.make
              (State.constr obj array array_index (t, l)
                 (Constructor.struct_field_initializers c)
                 (Constructor.initializers c) (Constructor.body c) vars
                 Constructor.field tt (a :: bases)) stack global
              construction_states field_construction_states deallocated_objects) _ _
   )).
    Focus 2.
    eapply step_constr_fields_cons_scalar_no_init.
    assumption.
    eassumption.
    assumption.
   intro.
   generalize (IHbases (fun x y => H15 _ (or_intror _ y)) ( vars) construction_states ((obj, array, array_index, (t, l), a, Constructed)
             :: field_construction_states)  deallocated_objects  ( global)).
   intros; invall; subst.
   esplit.
   esplit.
   esplit.
   split.
   eapply star_left.
   eassumption.
   eassumption.
   reflexivity.
   eauto.
  intro.
  generalize (H20 H22).
  intro; simpl in *; abstract congruence.

  (* struct *)
  intros. 
  generalize (H10 _ H18 _ _ H19).
  intros.
  generalize (H5 _ H18 _ _ H19).
  destruct 1 as [_ ?].
  refine (_ (_ :
 (step prog cppsem (sem := sem))
           (State.make
              (State.constr obj array array_index (t, l)
                 (Constructor.struct_field_initializers c)
                 (Constructor.initializers c) (Constructor.body c) vars
                 Constructor.field tt (a :: bases)) stack global
              construction_states field_construction_states deallocated_objects) _ _
  )).
   Focus 2.
   eapply step_constr_cons_field_struct.
   eassumption.
   rewrite H20. reflexivity.
   reflexivity.
  intro.
  match goal with
    x : step _ _ _ _ ?s |- _ => generalize (H21 s)
  end.
  simpl.
  intros.
  assert (0 <= 0 <= Zpos arraysize)%Z.
   compute.
   split; intros; discriminate.
  generalize (H22 (refl_equal _) (refl_equal _) H23).
  intros; invall; subst.
  destruct x1; simpl in *; subst; simpl in *.
  refine (_ (_ :  (step prog cppsem (sem := sem))
 (State.make
             (State.constr_array obj
                (array ++ (array_index, (t, l), a) :: nil) 
                (Zpos arraysize) (Zpos arraysize) struct (fun _ => Sconstructor struct nil) vars)
             (StackFrame.Kconstrother obj array array_index 
                (t, l) (Constructor.struct_field_initializers c)
                (Constructor.initializers c) (Constructor.body c) vars
                Constructor.field tt a bases :: stack) global0
             construction_states0 field_construction_states0 deallocated_objects) _ _
  )).
   Focus 2.
   eapply step_Kconstrother_fields.
  intros.
   generalize (IHbases (fun x y => H15 _ (or_intror _ y)) ( vars) construction_states0 ((obj, array, array_index, (t, l), a, Constructed)
             :: field_construction_states0)  deallocated_objects  ( global0)).
   intros; invall; subst.
   esplit.
   esplit.
   esplit.
   split.
    eapply star_left.
    eassumption.
    eapply star_trans.
    apply evtr_sem.
    eassumption.
    eapply star_left.
    eassumption.
    eassumption.
   reflexivity.
   reflexivity.
   reflexivity.
 split.
 repeat (eapply trans_equal; [eassumption |]).
 trivial.
 eauto.

(* array *)
destruct s1.
destruct kind; simpl in *; trivial.
intros until 2; subst.
revert array_index vars global construction_states field_construction_states deallocated_objects.
cut (
forall n array_index,  Z_of_nat n = (array_size - array_index)%Z -> forall vars global construction_states field_construction_states deallocated_objects,
   exists tr : trace (evtr sem),
     exists s2 : State.t A nativeop,
         star (evtr sem) (step prog cppsem (sem := sem))
           (State.make
              (State.constr_array obj array array_size array_index class (fun _ => Sconstructor class nil)
                 vars) stack global construction_states
              field_construction_states deallocated_objects) tr s2 /\
(Globals.heap (State.global s2)) ! obj =
             (Globals.heap (global)) ! obj /\
         State.kind s2 =
         State.constr_array obj array array_size array_size class (fun _ => Sconstructor class nil) vars /\
         State.deallocated_objects s2 = deallocated_objects /\
         State.stack s2 = stack  
).
 intros.
 assert (0 <= array_size - array_index)%Z by abstract romega.
 generalize (Z_of_nat_complete _ H16).
 intros; invall; subst; eauto.
induction n.
 (* 0 *)
 simpl.
 intros.
 assert (array_index = array_size) by abstract romega.
 subst.
 esplit.
 esplit.
 esplit.
 eapply star_refl.
 simpl; eauto.
(* S *)
rewrite inj_S.
unfold Zsucc.
generalize (Zle_0_nat n).
intros.
assert (array_index < array_size)%Z by abstract romega.
assert (Z_of_nat n = (array_size - (array_index + 1)))%Z by abstract romega.
generalize (Well_formed_hierarchy.vborder_list_exists hierarchy_wf H).
destruct 1.
refine (_ (_ :
 (step prog cppsem (sem := sem))
           (State.make
              (State.constr_array obj array array_size array_index class (fun _ => Sconstructor class nil)
                 vars) stack global construction_states
              field_construction_states deallocated_objects) _ _
)).
 Focus 2.
 eapply step_constr_array_cons.
 assumption.
 simpl.
 reflexivity.
intro.
refine (_ (_ :
step prog cppsem (sem := sem)
  (State.make (State.codepoint vars (Sconstructor class nil) nil nil)
            (StackFrame.Kconstrarray obj array array_size array_index class
               (fun _ => Sconstructor class nil) :: stack) global construction_states
            field_construction_states deallocated_objects) _ 
(
State.make
          (State.constr obj array array_index
             (Class.Inheritance.Repeated, class :: nil)
             (Constructor.struct_field_initializers _)
             (Constructor.initializers _) (Constructor.body _)
             (set_params
                (Value.ptr
                   (Value.subobject obj array array_index
                      Class.Inheritance.Repeated (class :: nil) I) :: nil)
                (Constructor.this _ :: Constructor.args _))
             Constructor.base Constructor.virtual _)
          (StackFrame.Kconstrothercells obj array array_size array_index
             class (fun _ => Sconstructor class nil) vars :: stack) global
          ((obj,
           (array, array_index, (Class.Inheritance.Repeated, class :: nil)),
           StartedConstructing) :: construction_states)
          field_construction_states deallocated_objects
))).
 Focus 2.
 eapply (@step_constructor_Kconstrarray _ _ _ _ _ nil).
 eassumption.
 eassumption.
 reflexivity.
 reflexivity.
 reflexivity.
 reflexivity.
 reflexivity.
 eassumption.
 eassumption.
 trivial.
intro.
generalize (H13 (
 (State.make
            (State.constr obj array array_index
               (Class.Inheritance.Repeated, class :: nil)
               (Constructor.struct_field_initializers c)
               (Constructor.initializers c) (Constructor.body c)
               (set_params
                  (Value.ptr
                     (Value.subobject obj array array_index
                        Class.Inheritance.Repeated 
                        (class :: nil) I) :: nil)
                  (Constructor.this c :: Constructor.args c))
               Constructor.base Constructor.virtual x)
            (StackFrame.Kconstrothercells obj array array_size array_index
               class (fun _ => Sconstructor class nil) vars :: stack) global
            ((obj,
             (array, array_index, (Class.Inheritance.Repeated, class :: nil)),
             StartedConstructing) :: construction_states)
            field_construction_states deallocated_objects)
) (refl_equal _) _ H (vborder_list_virtual_base H v) _ H6 _ H7 (refl_equal _) (refl_equal _) (refl_equal _)).
intros; invall; subst.
destruct x3; simpl in *; subst; simpl in *.
rename H19 into Hglobalobj1.
refine (_ (_ :
 (step prog cppsem (sem := sem))
  (State.make
             (State.constr obj array array_index
                (Class.Inheritance.Repeated, class :: nil)
                (Constructor.struct_field_initializers c)
                (Constructor.initializers c) (Constructor.body c) x4
                Constructor.base Constructor.virtual nil)
             (StackFrame.Kconstrothercells obj array array_size array_index
                class (fun _ => Sconstructor class nil) vars :: stack) global0 construction_states0
             field_construction_states0 deallocated_objects) _ 
(
State.make
          (State.constr obj array array_index
             (Class.Inheritance.Repeated, class :: nil)
             (Constructor.struct_field_initializers c)
             (Constructor.initializers c) (Constructor.body c) x4
             Constructor.base Constructor.direct_non_virtual
             (map
                (fun hb : Class.Inheritance.t * ident =>
                 let (_, b) := hb in b)
                (filter
                   (fun hb : Class.Inheritance.t * ident =>
                    let (y, _) := hb in
                    match y with
                    | Class.Inheritance.Repeated => true
                    | Class.Inheritance.Shared => false
                    end) (Class.super _))))
          (StackFrame.Kconstrothercells obj array array_size array_index
             class (fun _ => Sconstructor class nil) vars :: stack) global0 construction_states0
          field_construction_states0 deallocated_objects
))).
 Focus 2.
 eapply step_constr_virtual_bases_nil.
 reflexivity.
 eassumption.
 reflexivity.
intro.
generalize (H13
(State.make
            (State.constr obj array array_index
               (Class.Inheritance.Repeated, class :: nil)
               (Constructor.struct_field_initializers c)
               (Constructor.initializers c) (Constructor.body c) x4
               Constructor.base Constructor.direct_non_virtual
               (map
                  (fun hb : Class.Inheritance.t * ident =>
                   let (_, b) := hb in b)
                  (filter
                     (fun hb : Class.Inheritance.t * ident =>
                      let (y, _) := hb in
                      match y with
                      | Class.Inheritance.Repeated => true
                      | Class.Inheritance.Shared => false
                      end) (Class.super hc))))
            (StackFrame.Kconstrothercells obj array array_size array_index
               class (fun _ => Sconstructor class nil) vars :: stack) global0 construction_states0
            field_construction_states0 deallocated_objects)
(refl_equal _) _ H (@in_map_bases_elim _) _ H6 _ H7 (refl_equal _) (refl_equal _) (refl_equal _)).
simpl; intro; invall; subst.
destruct x6; simpl in *; subst; simpl in *.
rename H20 into Hglobalobj2.
refine (_ (_ :
(step prog cppsem (sem := sem))
  (State.make
             (State.constr obj array array_index
                (Class.Inheritance.Repeated, class :: nil)
                (Constructor.struct_field_initializers c)
                (Constructor.initializers c) (Constructor.body c) x7
                Constructor.base Constructor.direct_non_virtual nil)
             (StackFrame.Kconstrothercells obj array array_size array_index
                class (fun _ => Sconstructor class nil) vars :: stack) global1 construction_states1
             field_construction_states1 deallocated_objects) _ 
  (
    State.make
    (State.constr obj array array_index
      (Class.Inheritance.Repeated, class :: nil)
      (Constructor.struct_field_initializers c)
      (Constructor.initializers c) (Constructor.body c) x7
      Constructor.field tt (Class.fields _))
    (StackFrame.Kconstrothercells obj array array_size array_index
      class (fun _ => Sconstructor class nil) vars :: stack) global1
    ((obj,
      (array, array_index, (Class.Inheritance.Repeated, class :: nil)),
      BasesConstructed) :: construction_states1)
    field_construction_states1 deallocated_objects
  ))).
 Focus 2.
 eapply step_constr_non_virtual_bases_nil.
 reflexivity.
 eassumption.
 reflexivity.
intros.
generalize (H13
 (State.make
            (State.constr obj array array_index
               (Class.Inheritance.Repeated, class :: nil)
               (Constructor.struct_field_initializers c)
               (Constructor.initializers c) (Constructor.body c) x7
               Constructor.field tt (Class.fields hc))
            (StackFrame.Kconstrothercells obj array array_size array_index
               class (fun _ => Sconstructor class nil) vars :: stack) global1
            ((obj,
             (array, array_index, (Class.Inheritance.Repeated, class :: nil)),
             BasesConstructed) :: construction_states1)
            field_construction_states1 deallocated_objects)
(refl_equal _) _ H (fun x y => y) _ H6 _ H7 (refl_equal _) (refl_equal _) (refl_equal _)).
simpl; intros; invall; subst.
destruct x9; simpl in *; subst; simpl in *.
rename H21 into Hglobalobj3.
refine (_ (_ :
 (step prog cppsem (sem := sem))
 (State.make
             (State.constr obj array array_index
                (Class.Inheritance.Repeated, class :: nil)
                (Constructor.struct_field_initializers c)
                (Constructor.initializers c) (Constructor.body c) x10
                Constructor.field tt nil)
             (StackFrame.Kconstrothercells obj array array_size array_index
                class (fun _ => Sconstructor class nil) vars :: stack) global2 construction_states2
             field_construction_states2 deallocated_objects) _ 
(
State.make (State.codepoint x10 (Constructor.body c) nil nil)
          (StackFrame.Kconstrothercells obj array array_size array_index
             class (fun _ => Sconstructor class nil) vars :: stack) global2 construction_states2
          field_construction_states2 deallocated_objects
))).
 Focus 2.
 eapply step_constr_fields_nil.
intro.
refine (_ (_ :
step prog cppsem (sem := sem)
(State.make (State.codepoint x10 (Constructor.body c) nil nil)
            (StackFrame.Kconstrothercells obj array array_size array_index
               class (fun _ => Sconstructor class nil) vars :: stack) global2 construction_states2
            field_construction_states2 deallocated_objects) _ _
)).
 Focus 2.
 rewrite H12.
 econstructor.
 reflexivity.
intros.
generalize (IHn _ H17 vars global2  ((obj,
              (array, array_index,
              (Class.Inheritance.Repeated, class :: nil)), Constructed)
              :: construction_states2) field_construction_states2 deallocated_objects).
intros; invall; subst.
esplit.
esplit.
esplit.
eapply star_left.
eassumption.
eapply star_left.
eassumption.
eapply star_trans.
apply evtr_sem.
eassumption.
eapply star_left.
eassumption.
eapply star_trans.
apply evtr_sem.
eassumption.
eapply star_left.
eassumption.
eapply star_trans.
apply evtr_sem.
eassumption.
eapply star_left.
eassumption.
eapply star_left.
eassumption.
eassumption.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
split.
repeat (eapply trans_equal; [eassumption |]).
trivial.
eauto.

Qed.

Corollary progress : forall cn,
  has_nearly_trivial_constructor cn ->
  forall num,  (0 < num)%Z ->    
    forall vlocstruct stm vars stl bl stk gl cs auxcs f,
      exists hp, exists obj, exists gl1,
        (obj, gl1) =  Globals.new gl cn num  /\
        exists t, exists vars', exists gl', exists cs', exists auxcs',
          star _ (step prog cppsem (sem := sem))
          (State.make (State.codepoint vars (Sblock (Some (vlocstruct, cn, num)) (fun _ => Sconstructor cn nil) stm) stl bl) stk gl cs auxcs f) t
          (State.make (State.codepoint vars' stm nil (BlockPoint.make stl (Some obj) :: bl)) stk gl' cs' auxcs' f) /\
          vars' = PTree.set vlocstruct (Value.ptr (Value.subobject obj nil 0 Class.Inheritance.Repeated (cn :: nil) hp)) vars /\
            (Globals.heap gl') ! obj = (Globals.heap gl1) ! obj /\
            exists o, (Globals.heap gl1) ! obj = Some o /\
              Object.class o = cn /\
              Object.arraysize o = num
              .
Proof.
  intros.
  inversion H; subst.
  case_eq (Globals.new gl cn num).
  intros.
  symmetry in H12.
  refine (_ (_ : step prog cppsem (sem := sem)    
    (State.make (State.codepoint vars (Sblock (Some (vlocstruct, cn, num)) (fun _ => Sconstructor cn nil) stm) stl bl) stk gl cs auxcs f) E0 _)).
   Focus 2.
   eapply step_Sblock_some with (hp := I).
   congruence.
   assumption.
   eassumption.
   reflexivity.
   reflexivity.
  destruct (progress' H).
  intro.
  assert (0 <= 0 <= num)%Z by romega.
  match goal with 
    _ : step _ _ _ _ ?s |- _ =>
      generalize (H14 s (refl_equal _) (refl_equal _) H15)
  end.
  intro; invall; subst.
  destruct x1; simpl in *; subst; simpl in *.
  refine (_ (_ : step prog cppsem (sem := sem)
  (State.make
             (State.constr_array p nil num num cn
                (fun _ : Z => Sconstructor cn nil)
                (PTree.set vlocstruct
                   (Value.ptr
                      (Value.subobject p nil 0 Class.Inheritance.Repeated
                         (cn :: nil) I)) vars))
             (StackFrame.Kcontinue (StackFrame.continue_constr A) stm p stl
                bl :: stk) global construction_states
             field_construction_states f)
  E0 _
  )).
  Focus 2.
  eapply step_constr_array_nil_Kcontinue.
  reflexivity.
  reflexivity.
 intro.
 esplit.
 esplit.
 esplit.
 split.
  reflexivity.
 esplit.
 esplit.
 esplit.
 esplit.
 esplit.
 split.
 eapply star_left.
 eassumption.
 eapply star_trans.
 eapply evtr_sem.
 eassumption.
 eapply star_left.
 eassumption.
eleft.
reflexivity.
reflexivity.
reflexivity.
split.
reflexivity.
split.
assumption.
injection H12; intros; subst.
simpl.
rewrite PTree.gss.
esplit.
split.
reflexivity.
simpl; eauto.

Qed.


End Progress.

