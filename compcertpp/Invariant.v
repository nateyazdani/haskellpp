Require Import Relations.
Require Import Coqlib.
Require Import LibPos.
Require Import Maps.
Require Import LibLists.
Require Import Cppsem.
Require Import Cplusconcepts.
Require Import Events.
Require Import SubobjectOrdering.
Load Param.


Ltac sdestruct z :=
  let Y := fresh "Y" in (
    pose (Y := z);
      simpl in Y; unfold_ident_in Y; unfold_ident; fold Y; destruct Y
  ).


Lemma cs_le_dec : forall o1 o2,
  {(o1 =< o2)} + {~ (o1 =< o2) }.
Proof.
  intros; eauto using Z_le_dec.
Defined. (* transparence is necessary for the following lemma *)

Lemma cs_le_dec_2 : forall o1 o2,
  {(o1 =< o2)} + {(o2 << o1)}.
Proof.
  intros; eauto using Z_lt_le_dec.
Qed.

Lemma decidable_solve : forall (A : Type) (P : A -> A -> Prop) (P_dec : forall a1 a2, {P a1 a2} + {~ P a1 a2})
  a1 a2, (if P_dec a1 a2 then True else False) -> P a1 a2.
Proof.
  intros.
  destruct (P_dec a1 a2).
   assumption.
  contradiction.
Qed.

Implicit Arguments decidable_solve [A P].

Open Scope nat_scope.

Open Scope Z_scope.

Section Invar.

Variable A : ATOM.t.
Variable nativeop : Type.
Variable sem : semparam A nativeop.
Let evtr := evtr sem.
Let trace := trace evtr.


Variable prog : Program.t A nativeop.
Notation hier := (Program.hierarchy prog).


 Lemma NoDup_repeated_bases : forall l, NoDup l -> NoDup (map (fun hp' : Class.Inheritance.t * ident => let (_, p') := hp' in p')
            ((filter (fun hp' : _ * ident =>
              match hp' with
                | (Class.Inheritance.Repeated, _) => true
                | _ => false
              end) l))).
Proof.
  intros.
  apply norepet_NoDup.
  apply list_map_norepet.
  apply NoDup_norepet.
  apply NoDup_filter_compat.
  assumption.
  intros until 1.
  destruct (filter_In  (fun hp' : Class.Inheritance.t * ident =>
             let (y, _) := hp' in
             match y with
             | Class.Inheritance.Repeated => true
             | Class.Inheritance.Shared => false
             end) x l).
  destruct (H1 H0).
  destruct x.
  destruct t; try congruence.
  intros until 1.
  destruct  (filter_In  (fun hp' : Class.Inheritance.t * ident =>
             let (y, _) := hp' in
             match y with
             | Class.Inheritance.Repeated => true
             | Class.Inheritance.Shared => false
             end) y l).
  destruct (H6 H5).
  destruct y.
  destruct t; congruence.
Qed.

Function is_code_frame (k : StackFrame.t A nativeop) : Prop :=
  match k with
    | StackFrame.Kcontinue _ _ _ _ _ => True
    | StackFrame.Kreturnfromcall _ _ _ _ => True
    | _ => False
  end.

Remark is_code_frame_dec : forall f : _ A nativeop,
{is_code_frame f} + {~ is_code_frame f}.
Proof.
  destruct f; simpl; (left; exact I) || (right; exact (fun x => x)).
Qed.


Function is_code_state (k : State.state_kind A nativeop) : Prop :=
  match k with
    | State.codepoint _ _ _ _ => True
    | _ => False
  end.

Function frame_requires_code (k : StackFrame.t A nativeop) : Prop :=
  match k with
    | StackFrame.Kconstr _ _ _ _ _ _ _ _ _ _ _ => True
    | StackFrame.Kconstrarray _ _ _ _ _ _ => True
    | StackFrame.Kdestr _ _ _ _ => True
    | _ => False
  end.

(* Enchainements *)

(* L'invariant suivant est necessaire pour faire s'enchainer correctement, dans une classe C, la construction d'un champ tableau de structures avec la construction des autres champs de C *)

Function stackframe_array_fields_inv (obj : ident) (ar : array_path A) (fr : StackFrame.t A nativeop) {struct fr} : Prop :=
  match fr with
    | StackFrame.Kconstrother obj' ar' i' (h', p') _ _ _ _ Constructor.field tt field other_fields' =>
      obj = obj' /\
      exists cn, last p' = Some cn /\
        exists c, hier ! cn = Some c /\
          exists l1, Class.fields c = l1 ++ field :: other_fields' /\
            ar = ar' ++ (i', (h', p'), field) :: nil
    | StackFrame.Kcontinue (StackFrame.continue_constr) _ obj' _ _ => ar = nil /\ obj' = obj
    | _ => False
  end.

Function stackframe_array_fields_inv_destr (obj : ident) (ar : array_path A) (fr : StackFrame.t A nativeop) {struct fr} : Prop :=
  match fr with
    | StackFrame.Kdestrother obj' ar' i' (h', p') Constructor.field tt field other_fields' =>
      obj = obj' /\
      exists cn, last p' = Some cn /\
        exists c, hier ! cn = Some c /\
          exists l1, rev (Class.fields c) = l1 ++ field :: other_fields' /\
            ar = ar' ++ (i', (h', p'), field) :: nil
    | StackFrame.Kcontinue (StackFrame.continue_destr _) _ obj' _ _ => ar = nil /\ obj' = obj
    | _ => False
  end.


(* L'invariant suivant est necessaire pour faire s'enchainer correctement, dans une classe C, la construction du dernier champ d'une base de C, avec la construction des autres bases de C *)

Function stackframe_field_base_inv (obj : ident) (ar : array_path A) (i : Z) (h : Class.Inheritance.t) (p : list ident) (fr : StackFrame.t A nativeop) {struct fr} : Prop :=
  match fr with
    | StackFrame.Kconstrother obj' ar' i' (h', p') _ _ _ _ Constructor.base Constructor.direct_non_virtual b _ =>
      obj = obj' /\ ar = ar' /\ i = i' /\ h = h' /\ p = p' ++ b :: nil
    | StackFrame.Kconstrother obj' ar' i' _ _ _ _ _ Constructor.base Constructor.virtual b _ =>
      obj = obj' /\ ar = ar' /\ i = i' /\ h = Class.Inheritance.Shared /\ p = b :: nil
    | StackFrame.Kconstrothercells obj' ar' _ i' cn' _ _ =>
      obj = obj' /\ ar = ar' /\ i = i' /\ h = Class.Inheritance.Repeated /\ p = cn' :: nil
    | _ => False
  end.

Function stackframe_field_base_inv_destr (obj : ident) (ar : array_path A) (i : Z) (h : Class.Inheritance.t) (p : list ident) (fr : StackFrame.t A nativeop) {struct fr} : Prop :=
  match fr with
    | StackFrame.Kdestrother obj' ar' i' (h', p') Constructor.base Constructor.direct_non_virtual b _ => obj = obj' /\ ar = ar' /\ i = i' /\ h = h' /\ p = p' ++ b :: nil
    | StackFrame.Kdestrother obj' ar' i' _ Constructor.base Constructor.virtual b _ => obj = obj' /\ ar = ar' /\ i = i' /\ h = Class.Inheritance.Shared /\ p = b :: nil

    | StackFrame.Kdestrcell obj' ar' i' cn' =>
      obj = obj' /\ ar = ar' /\ i = i' /\ h = Class.Inheritance.Repeated /\ p = cn' :: nil
    | _ => False
  end.


(* L'invariant suivant est necessaire pour faire s'enchainer correctement la construction d'un objet complet de type C et la construction d'autres cellules d'un tableau de C *)

Function stackframe_vbase_cell_inv (obj : ident) (ar : array_path A) (i : Z) (h : Class.Inheritance.t) (p : list ident) (sf2 : StackFrame.t A nativeop) {struct sf2} : Prop :=
  match sf2 with
    | StackFrame.Kconstrothercells obj' ar' _ i' cn' _ _ =>
      obj = obj' /\ ar = ar' /\ i = i' /\ h = Class.Inheritance.Repeated /\ p = cn' :: nil
    | _ => False
  end.

Function stackframe_chaining (sf1 sf2 : StackFrame.t A nativeop) {struct sf1} : Prop :=
  match sf1 with
    | StackFrame.Kconstrothercells obj ar _ _ _ _ _ => stackframe_array_fields_inv obj ar sf2
    | StackFrame.Kconstr obj ar i (h, p) _ _ _ Constructor.base Constructor.virtual _ _ => stackframe_vbase_cell_inv obj ar i h p sf2
    | StackFrame.Kconstrarray obj ar _ _ _ _ => stackframe_array_fields_inv obj ar sf2
    | StackFrame.Kconstrother obj ar i (h, p) _ _ _ _ Constructor.base Constructor.virtual _ _ => stackframe_vbase_cell_inv obj ar i h p sf2
    | StackFrame.Kconstr obj ar i (h, p) _ _ _ _ _ _ _ => stackframe_field_base_inv obj ar i h p sf2
    | StackFrame.Kconstrother obj ar i (h, p) _ _ _ _ _ _ _ _ => stackframe_field_base_inv obj ar i h p sf2
    | StackFrame.Kdestrcell obj ar _ _ => stackframe_array_fields_inv_destr obj ar sf2
    | StackFrame.Kdestr obj ar i (h, p) => stackframe_field_base_inv_destr obj ar i h p sf2
    | StackFrame.Kdestrother obj ar i (h, p) Constructor.base Constructor.virtual _ _ => stackframe_array_fields_inv_destr obj ar sf2 /\ h = Class.Inheritance.Repeated /\ exists cn, p = cn :: nil
(* this is no longer true : stackframe_vbase_cell_inv obj ar i h p sf2, as we have no more cell stack frame when destructing virtual base *)
    | StackFrame.Kdestrother obj ar i (h, p) Constructor.base Constructor.direct_non_virtual _ _ => stackframe_field_base_inv_destr obj ar i h p sf2
    | StackFrame.Kdestrother obj ar i (h, p) Constructor.field _ _ _ => stackframe_field_base_inv_destr obj ar i h p sf2
    | _ => True
  end.

Section Invariant.

Variable s : State.t A nativeop.

(* Invariant valable dans les corps de constructeurs ou initialiseurs uniquement *)

Definition stackframe_constructor_inv (fr : StackFrame.t A nativeop) : Prop :=
  match fr with

    | StackFrame.Kconstr obj ar i (h, P) _ _ _ k k2 current other => exists cs,
      assoc (@pointer_eq_dec _) (obj, (ar, i, (h, P))) (State.construction_states s) = Some cs /\
      exists hp,
        valid_pointer hier (Globals.heap (State.global s)) (Value.subobject obj ar i h P hp) /\
        exists cn, last P = Some cn /\
          exists c, hier ! cn = Some c /\
            match (existT (fun t => (Constructor.init_subkey _ t * list (Constructor.init_key_item _ t))%type) k (k2, current, other)) with

              | existT Constructor.base (bk2, base, other_bases) =>
                cs = StartedConstructing /\
                match bk2 with

                  | Constructor.direct_non_virtual =>
                    exists l1, map (fun hp' : Class.Inheritance.t * ident => let (_, p') := hp' in p')
                      ((filter (fun hp' : _ * ident =>
                        match hp' with
                          | (Class.Inheritance.Repeated, _) => true
                          | _ => false
                        end) (Class.super c))) = l1 ++ base :: other_bases /\
                      (forall b, In b l1 -> assoc (@pointer_eq_dec _) (obj, (ar, i, (h, P ++ b :: nil))) (State.construction_states s) = Some Constructed) /\
                      (forall b, In b (base :: other_bases) -> assoc (@pointer_eq_dec _) (obj, (ar, i, (h, P ++ b :: nil))) (State.construction_states s) = None) /\
                      (h = Class.Inheritance.Repeated -> forall cn' p', P = cn' :: p' -> forall b, is_virtual_base_of hier b cn' -> assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b :: nil))) (State.construction_states s) = Some Constructed)
                        
                  | Constructor.virtual =>
                    h = Class.Inheritance.Repeated /\ P = cn :: nil /\
                      exists l1, vborder_list hier (Class.super c) (l1 ++ base :: other_bases) /\
                        (forall b, In b l1 -> assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b :: nil))) (State.construction_states s) = Some Constructed) /\
                        (forall b, In b (base :: other_bases) -> assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b :: nil))) (State.construction_states s) = None) /\
                        forall b, In (Class.Inheritance.Repeated, b) (Class.super c) -> assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Repeated, cn :: b :: nil))) (State.construction_states s) = None

                end
                
              | existT Constructor.field (tt, field, other_fields) =>
                cs = BasesConstructed /\
                exists l1, Class.fields c = l1 ++ field :: other_fields /\
                  (forall fs, In fs l1 ->
                    assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, (h, P), fs) (State.field_construction_states s) = Some Constructed) /\
                  forall fs, In fs (field :: other_fields) -> assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, (h, P), fs) (State.field_construction_states s) = None

            end

    | StackFrame.Kconstrarray obj ar n i cn _ => (exists o,
      (Globals.heap (State.global s)) ! obj = Some o /\      
      valid_array_path hier cn n (Object.class o) (Object.arraysize o) ar /\
      (* hier ! cn <> None /\ *)
      match last ar with
        | None => n = Object.arraysize o /\ cn = Object.class o
        | Some (_, _, fs) => exists n', n = Zpos n' /\ FieldSignature.type fs = FieldSignature.Struct cn n'
      end /\
      0 <= i < n /\
      (forall j, 0 <= j < i -> assoc (@pointer_eq_dec _) (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s) = Some Constructed) /\
      forall j, i <= j < n -> assoc (@pointer_eq_dec _) (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s) = None)
            
    | StackFrame.Kconstrother obj ar i (h, p) _ _ _ _ Constructor.base Constructor.direct_non_virtual base _ =>
      assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p ++ base :: nil))) (State.construction_states s) =
      Some BasesConstructed /\
      exists c, hier ! base = Some c /\ 
        forall fs, In fs (Class.fields c) ->
          assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, (h, p ++ base :: nil), fs) (State.field_construction_states s) = Some Constructed

    | StackFrame.Kconstrother obj ar i _ _ _ _ _ Constructor.base Constructor.virtual base _ =>
      assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, base :: nil))) (State.construction_states s) = Some BasesConstructed /\
      exists c, hier ! base = Some c /\
        forall fs, In fs (Class.fields c) ->
          assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, (Class.Inheritance.Shared, base :: nil), fs) (State.field_construction_states s) = Some Constructed

    | StackFrame.Kconstrother obj ar i (h, p) _ _ _ _ Constructor.field tt field _ =>
      forall b n, FieldSignature.type field = FieldSignature.Struct b n -> forall j, 0 <= j < Zpos n -> assoc (@pointer_eq_dec _) (obj, (ar ++ (i, (h, p), field) :: nil, j, (Class.Inheritance.Repeated, b :: nil))) (State.construction_states s) = Some Constructed

    | StackFrame.Kconstrothercells obj ar _ i cn _ _ =>
      assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s) = Some BasesConstructed /\ exists c, hier ! cn = Some c /\
        forall fs, In fs (Class.fields c) ->
          assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, (Class.Inheritance.Repeated, cn :: nil), fs) (State.field_construction_states s) = Some Constructed
            
    | StackFrame.Kdestr obj ar i (h, P) =>
      assoc (@pointer_eq_dec _) (obj, (ar, i, (h, P))) (State.construction_states s) =
      Some StartedDestructing /\
      exists hp,
        valid_pointer hier (Globals.heap (State.global s)) (Value.subobject obj ar i h P hp) /\
        exists cn, last P = Some cn /\
          exists c, hier ! cn = Some c /\
            (forall fs, In fs (Class.fields c) ->
              assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, (h, P), fs) (State.field_construction_states s) = Some Constructed)

    |  _ => True
end.

(* Invariants valables partout *)

Definition state_kind_inv : Prop :=
  match State.kind s with

    | State.constr obj ar i (h, P) _ _ _ _ k k2 ls =>
      exists cs,
        assoc (@pointer_eq_dec _) (obj, (ar, i, (h, P))) (State.construction_states s) = Some cs /\
        exists hp,
          valid_pointer hier (Globals.heap (State.global s)) (Value.subobject obj ar i h P hp) /\
          exists cn, last P = Some cn /\
            exists c, hier ! cn = Some c /\
              match existT (fun t => (Constructor.init_key_secondary t * list (Constructor.init_key_item _ t))%type) k (k2, ls) with
                
                | existT Constructor.base (bk2, bases) =>
                  cs = StartedConstructing /\
                  match bk2 with

                    | Constructor.direct_non_virtual =>
                      (
                        exists l1, map (fun hp' : Class.Inheritance.t * ident => let (_, p') := hp' in p')
                          ((filter (fun hp' : _ * ident =>
                            match hp' with
                              | (Class.Inheritance.Repeated, _) => true
                              | _ => false
                            end) (Class.super c))) = l1 ++ bases /\
                          (forall b, In b l1 -> assoc (@pointer_eq_dec _) (obj, (ar, i, (h, P ++ b :: nil))) (State.construction_states s) = Some Constructed) /\
                          (forall b, In b bases -> assoc (@pointer_eq_dec _) (obj, (ar, i, (h, P ++ b :: nil))) (State.construction_states s) = None) /\
                          (h = Class.Inheritance.Repeated -> forall cn' P', P = cn' :: P' -> forall b, is_virtual_base_of hier b cn' -> assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b :: nil))) (State.construction_states s) = Some Constructed)
                      ) /\
                      match State.stack s with (* enchainement avec KconstrotherNVbases, KconstrotherVbases *)
                        | k' :: _ => stackframe_field_base_inv obj ar i h P k'
                        | _ => False
                      end

                    | Constructor.virtual =>
                      (
                        exists l1, vborder_list hier (Class.super c) (l1 ++ bases) /\
                          (forall b, In b l1 -> assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b :: nil))) (State.construction_states s) = Some Constructed) /\
                          (forall b, In b bases -> assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b :: nil))) (State.construction_states s) = None) /\
                          (forall b, In (Class.Inheritance.Repeated, b) (Class.super c) -> assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Repeated, cn :: b :: nil))) (State.construction_states s) = None)
                      ) /\
                      match State.stack s with (* enchainement avec Kconstrothercells *)
                        | k' :: _ => stackframe_vbase_cell_inv obj ar i h P k'
                        | _ => False
                      end
                      
                  end

                | existT Constructor.field (tt, fields) =>
                  cs = BasesConstructed /\ (
                    exists l1, Class.fields c = l1 ++ fields /\
                      (forall fs, In fs l1 -> assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, (h, P), fs) (State.field_construction_states s) = Some Constructed) /\
                      (forall fs, In fs fields -> assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, (h, P), fs) (State.field_construction_states s) = None)
                  ) /\
                  match State.stack s with (* enchainement avec KconstrotherNVbases, KconstrotherVbases *)
                    | k' :: _ => stackframe_field_base_inv obj ar i h P k'
                    | _ => False
                  end

              end

    | State.constr_array obj ar n i cn _ _ => (exists o,
      (Globals.heap (State.global s)) ! obj = Some o /\      
      valid_array_path hier cn n (Object.class o) (Object.arraysize o) ar /\
      (* hier ! cn <> None /\ *)
      match last ar with
        | None => n = Object.arraysize o /\ cn = Object.class o
        | Some (_, _, fs) => exists n', n = Zpos n' /\ FieldSignature.type fs = FieldSignature.Struct cn n'
      end /\
      0 <= i <= n /\
      (forall j, 0 <= j < i -> assoc (@pointer_eq_dec _) (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s) = Some Constructed) /\
      forall j, i <= j < n -> assoc (@pointer_eq_dec _) (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s) = None) /\
    match State.stack s with (* enchainement avec Kconstrotherfields *)
      | k' :: _ => stackframe_array_fields_inv obj ar k'
      | _ => False
    end

(* Destruction *)

    | State.destr obj ar i (h, P) k k2 ls =>
      exists cs,
        assoc (@pointer_eq_dec _) (obj, (ar, i, (h, P))) (State.construction_states s) = Some cs /\
        exists hp,
          valid_pointer hier (Globals.heap (State.global s)) (Value.subobject obj ar i h P hp) /\
          exists cn, last P = Some cn /\
            exists c, hier ! cn = Some c /\
              match existT (fun t => (Constructor.init_key_secondary t * list (Constructor.init_key_item _ t))%type) k (k2, ls) with
                
                | existT Constructor.base (bk2, bases) =>
                  cs = DestructingBases /\
                  match bk2 with

                    | Constructor.direct_non_virtual =>
                      (
                        exists l1, rev (map (fun hp' : Class.Inheritance.t * ident => let (_, p') := hp' in p')
                          ((filter (fun hp' : _ * ident =>
                            match hp' with
                              | (Class.Inheritance.Repeated, _) => true
                              | _ => false
                            end) (Class.super c)))) = l1 ++ bases /\
                          (forall b, In b l1 -> assoc (@pointer_eq_dec _) (obj, (ar, i, (h, P ++ b :: nil))) (State.construction_states s) = Some Destructed) /\
                          (forall b, In b bases -> assoc (@pointer_eq_dec _) (obj, (ar, i, (h, P ++ b :: nil))) (State.construction_states s) = Some Constructed) /\
                          (h = Class.Inheritance.Repeated -> forall cn' p', P = cn' :: p' -> forall b, is_virtual_base_of hier b cn' -> assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b :: nil))) (State.construction_states s) = Some Constructed)
                      ) /\
                      match State.stack s with (* enchainement avec KconstrotherNVbases, KconstrotherVbases *)
                        | k' :: _ => stackframe_field_base_inv_destr obj ar i h P k'
                        | _ => False
                      end

                    | Constructor.virtual => (h = Class.Inheritance.Repeated /\ P = cn :: nil) /\
                      (
                        exists l1, vborder_list hier (Class.super c) (rev (l1 ++ bases)) /\
                          (forall b, In b l1 -> assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b :: nil))) (State.construction_states s) = Some Destructed) /\
                          (forall b, In b bases -> assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b :: nil))) (State.construction_states s) = Some Constructed) /\
                          (forall b, In (Class.Inheritance.Repeated, b) (Class.super c) -> assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Repeated, cn :: b :: nil))) (State.construction_states s) = Some Destructed)
                      ) /\ (*
                        (exists n, match last ar with
                                     | None => exists o, (Globals.heap (State.global s)) ! obj = Some o /\ n = Object.arraysize o
                                     | Some (_, _, fs) => exists n', n = Zpos n' /\ FieldSignature.type fs = FieldSignature.Struct cn n'
                                   end
                        /\
                        (forall j, 0 <= j < i -> assoc (@pointer_eq_dec _) (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s) = Some Constructed) /\
                        (forall j, i < j < n -> assoc (@pointer_eq_dec _) (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s) = Some Destructed) ) /\ *)
                      match State.stack s with (* enchainement avec Kconstrothercells *)
                        | k' :: _ => stackframe_array_fields_inv_destr obj ar k'
(* this is no longer true : stackframe_vbase_cell_inv obj ar i h P k', as we have no more cell stack frame when destructing virtual base *)
                          
                        | _ => False
                      end
                      
                  end

                | existT Constructor.field (tt, fields) =>
                  cs = StartedDestructing /\ (
                    exists l1, rev (Class.fields c) = l1 ++ fields /\
                      (forall fs, In fs l1 -> assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, (h, P), fs) (State.field_construction_states s) = Some Destructed) /\
                      (forall fs, In fs fields -> assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, (h, P), fs) (State.field_construction_states s) = Some Constructed)
                  ) /\
                  match State.stack s with (* enchainement avec KconstrotherNVbases, KconstrotherVbases *)
                    | k' :: _ => stackframe_field_base_inv_destr obj ar i h P k'
                    | _ => False
                  end

              end

    | State.destr_array obj ar i cn => (exists n, exists o,
      (Globals.heap (State.global s)) ! obj = Some o /\      
      valid_array_path hier cn n (Object.class o) (Object.arraysize o) ar /\
      (* hier ! cn <> None /\ *)
      match last ar with
        | None => n = Object.arraysize o /\ cn = Object.class o
        | Some (_, _, fs) => exists n', n = Zpos n' /\ FieldSignature.type fs = FieldSignature.Struct cn n'
      end /\
      -1 <= i < n /\
      (forall j, 0 <= j <= i -> assoc (@pointer_eq_dec _) (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s) = Some Constructed) /\
      forall j, i < j < n -> assoc (@pointer_eq_dec _) (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s) = Some Destructed) /\
    match State.stack s with (* enchainement avec Kconstrotherfields *)
      | k' :: _ => stackframe_array_fields_inv_destr obj ar k'
      | _ => False
    end

    
    | State.codepoint _ _ _ _ =>
      match State.stack s with
        | k' :: _ => stackframe_constructor_inv k'
        | nil => True
      end

  end.

Definition stackframe_weak_inv (fr : StackFrame.t A nativeop) : Prop :=
  match fr with

    | StackFrame.Kconstrother obj ar i (h, P) _ _ _ _ k k2 current other => 
      exists cs,
        assoc (@pointer_eq_dec _) (obj, (ar, i, (h, P))) (State.construction_states s) = Some cs /\
        exists hp,
          valid_pointer hier (Globals.heap (State.global s)) (Value.subobject obj ar i h P hp) /\
          exists cn, last P = Some cn /\
            exists c, hier ! cn = Some c /\

              match existT (fun t => (Constructor.init_key_secondary t * Constructor.init_key_item _ t * list (Constructor.init_key_item _ t))%type) k (k2, current, other) with
                
                | existT Constructor.base (bk2, base, other_bases) =>
                  cs = StartedConstructing /\
                  match bk2 with

                    | Constructor.direct_non_virtual =>
                      exists l1, map (fun hp' : Class.Inheritance.t * ident => let (_, p') := hp' in p')
                        ((filter (fun hp' : _ * ident =>
                          match hp' with
                            | (Class.Inheritance.Repeated, _) => true
                            | _ => false
                          end) (Class.super c))) = l1 ++ base :: other_bases /\
                        (* (forall b, In b l1 -> assoc (@pointer_eq_dec _) (obj, (ar, i, (h, P ++ b :: nil))) (State.construction_states s) = Some Constructed) /\
                        (forall b, In b other_bases -> assoc (@pointer_eq_dec _) (obj, (ar, i, (h, P ++ b :: nil))) (State.construction_states s) = None) /\
                        (forall b, is_virtual_base_of hier b cn -> assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b :: nil))) (State.construction_states s) = Some Constructed) /\ *)
                        let cs := assoc (@pointer_eq_dec _) (obj, (ar, i, (h, P ++ base :: nil))) (State.construction_states s) in
                          cs = Some StartedConstructing \/ cs = Some BasesConstructed

                    | Constructor.virtual =>
                      h = Class.Inheritance.Repeated /\ P = cn :: nil /\
                      exists l1, vborder_list hier (Class.super c) (l1 ++ base :: other_bases) /\
                        (* (forall b, In b l1 -> assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b :: nil))) (State.construction_states s) = Some Constructed) /\
                        (forall b, In b other_bases -> assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b :: nil))) (State.construction_states s) = None) /\
                        (forall b, In (Class.Inheritance.Repeated, b) (Class.super c) -> assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Repeated, cn :: b :: nil))) (State.construction_states s) = None)
                        /\ *)
                        let cs := assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, base :: nil))) (State.construction_states s) in
                          cs = Some StartedConstructing \/ cs = Some BasesConstructed

                  end

                | existT Constructor.field (tt, field, other_fields) =>
                  cs = BasesConstructed /\
                  exists l1, Class.fields c = l1 ++ field :: other_fields /\ (*
                    (forall fs, In fs l1 -> assoc aux_constr_state_key_eq_dec (obj, ar, i, (h, P), fs) aux_constr_state = Some Constructed) /\
                    (forall fs, In fs other_fields ->  assoc aux_constr_state_key_eq_dec (obj, ar, i, (h, P), fs) aux_constr_state = None) /\ *)
                    assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, (h, P), field) (State.field_construction_states s) = Some StartedConstructing

              end

    | StackFrame.Kconstrothercells obj ar n i cn _ _ => exists o,
      (Globals.heap (State.global s)) ! obj = Some o /\      
      valid_array_path hier cn n (Object.class o) (Object.arraysize o) ar /\
      match last ar with
        | None => n = Object.arraysize o /\ cn = Object.class o
        | Some (_, _, fs) => exists n', n = Zpos n' /\ FieldSignature.type fs = FieldSignature.Struct cn n'
      end /\
      0 <= i < n /\ (*
      (forall j, 0 <= j < i -> assoc (@pointer_eq_dec _) (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s) = Some Constructed) /\
      (forall j, i < j < n -> assoc (@pointer_eq_dec _) (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s) = None) /\ *)
      let cs := assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s) in cs = Some StartedConstructing \/ cs = Some BasesConstructed

(* Destruction *)

    | StackFrame.Kdestrother obj ar i (h, P) k k2 current other => 
      exists cs,
        assoc (@pointer_eq_dec _) (obj, (ar, i, (h, P))) (State.construction_states s) = Some cs /\
        exists hp,
          valid_pointer hier (Globals.heap (State.global s)) (Value.subobject obj ar i h P hp) /\
          exists cn, last P = Some cn /\
            exists c, hier ! cn = Some c /\

              match existT (fun t => (Constructor.init_key_secondary t * Constructor.init_key_item _ t * list (Constructor.init_key_item _ t))%type) k (k2, current, other) with
                
                | existT Constructor.base (bk2, base, other_bases) =>
                  cs = DestructingBases /\
                  match bk2 with

                    | Constructor.direct_non_virtual =>
                      exists l1, rev (map (fun hp' : Class.Inheritance.t * ident => let (_, p') := hp' in p')
                        ((filter (fun hp' : _ * ident =>
                          match hp' with
                            | (Class.Inheritance.Repeated, _) => true
                            | _ => false
                          end) (Class.super c)))) = l1 ++ base :: other_bases /\
                      (* (forall b, In b l1 -> assoc (@pointer_eq_dec _) (obj, (ar, i, (h, P ++ b :: nil))) (State.construction_states s) = Some Destructed) /\
                         (forall b, In b other_bases -> assoc (@pointer_eq_dec _) (obj, (ar, i, (h, P ++ b :: nil))) (State.construction_states s) = Some Constructed) /\
                         (forall b, is_virtual_base_of hier b cn -> assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b :: nil))) (State.construction_states s) = Some Constructed) /\ *)
                      let cs := assoc (@pointer_eq_dec _) (obj, (ar, i, (h, P ++ base :: nil))) (State.construction_states s) in
                        cs = Some StartedDestructing \/ cs = Some DestructingBases

                    | Constructor.virtual =>
                      h = Class.Inheritance.Repeated /\ P = cn :: nil /\
                      exists l1, vborder_list hier (Class.super c) (rev (l1 ++ base :: other_bases)) /\
                        (* (forall b, In b l1 -> assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b :: nil))) (State.construction_states s) = Some Destructed) /\
                        (forall b, In b other_bases -> assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b :: nil))) (State.construction_states s) = Some Constructed) /\
                        (forall b, In (Class.Inheritance.Repeated, b) (Class.super c) -> assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Repeated, cn :: b :: nil))) (State.construction_states s) = Some Destructed)
                        /\ *)
                        (let cs := assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, base :: nil))) (State.construction_states s) in
                          cs = Some StartedDestructing \/ cs = Some DestructingBases) (* /\
                        (exists n, match last ar with
                                     | None => exists o, (Globals.heap (State.global s)) ! obj = Some o /\ n = Object.arraysize o
                                     | Some (_, _, fs) => exists n', n = Zpos n' /\ FieldSignature.type fs = FieldSignature.Struct cn n'
                                   end
                        /\
                        (forall j, 0 <= j < i -> assoc (@pointer_eq_dec _) (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s) = Some Constructed) /\
                        (forall j, i < j < n -> assoc (@pointer_eq_dec _) (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s) = Some Destructed) ) *)
                          

                  end

                | existT Constructor.field (tt, field, other_fields) =>
                  cs = StartedDestructing /\
                  exists l1, rev (Class.fields c) = l1 ++ field :: other_fields /\
                    (* (forall fs, In fs l1 -> assoc aux_constr_state_key_eq_dec (obj, ar, i, (h, P), fs) aux_constr_state = Some Destructed) /\
                    (forall fs, In fs other_fields ->  assoc aux_constr_state_key_eq_dec (obj, ar, i, (h, P), fs) aux_constr_state = Some Constructed) /\ *)
                    assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, (h, P), field) (State.field_construction_states s) = Some StartedDestructing

              end

    | StackFrame.Kdestrcell obj ar i cn => exists n, exists o,
      (Globals.heap (State.global s)) ! obj = Some o /\      
      valid_array_path hier cn n (Object.class o) (Object.arraysize o) ar /\
      match last ar with
        | None => n = Object.arraysize o /\ cn = Object.class o
        | Some (_, _, fs) => exists n', n = Zpos n' /\ FieldSignature.type fs = FieldSignature.Struct cn n'
      end /\
      0 <= i < n /\
      (* (forall j, 0 <= j < i -> assoc (@pointer_eq_dec _) (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s) = Some Constructed) /\
      (forall j, i < j < n -> assoc (@pointer_eq_dec _) (obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s) = Some Destructed) /\ *)
      let cs := assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s) in cs = Some StartedDestructing \/ cs = Some DestructingBases



    | _ => True (* en particulier, les KconstrNVbase, KconstrVbase, etc. n'ont pas a etre traites ici. Ils ne peuvent etre surmontes que d'un point de code (correspondant a l'initialiseur avant construction). *)
      
  end.

(* Resume *)

Definition stack2_inv (sf1 : StackFrame.t A nativeop) (l2 : list (StackFrame.t A nativeop)) : Prop :=
  (is_code_frame sf1 -> match l2 with
                         | nil => True
                         | sf2 :: _ => stackframe_constructor_inv sf2
                       end) /\
  ((~ is_code_frame sf1) -> match l2 with
                           | nil => False
                           | sf2 :: _ => stackframe_chaining sf1 sf2 /\ (frame_requires_code sf2 -> False)
                         end).

Function frame_array_weak (sf : StackFrame.t A nativeop) : option (ident * array_path A) :=
  match sf with
    | StackFrame.Kconstrothercells obj ar _ _ _ _ _ => Some (obj, ar)
    | StackFrame.Kconstr obj ar _ _ _ _ _ _ _ _ _ => Some (obj, ar)
    | StackFrame.Kconstrarray obj ar _ _ _ _ => Some (obj, ar)
    | StackFrame.Kconstrother obj ar _ _ _ _ _ _ _ _ _ _ => Some (obj, ar)
    | StackFrame.Kdestrcell obj ar _ _ => Some (obj, ar)
    | StackFrame.Kdestr obj ar _ _ => Some (obj, ar)
    | StackFrame.Kdestrother obj ar _ _ _ _ _ _ => Some (obj, ar)
    | _ => None
  end.

Function frame_array (sf : StackFrame.t A nativeop) : option (ident * array_path A) :=
  match sf with
    | StackFrame.Kconstrothercells obj ar _ _ _ _ _ => Some (obj, ar)
    | StackFrame.Kconstrarray obj ar _ _ _ _ => Some (obj, ar)
    | StackFrame.Kdestrcell obj ar _ _ => Some (obj, ar)
    | StackFrame.Kdestrother obj ar _ _ Constructor.base Constructor.virtual _ _ => Some (obj, ar)
    | _ => None
  end.

Function frame_pointer (sf : StackFrame.t A nativeop) : option (ident * array_path A * Z * (Class.Inheritance.t * list ident)) :=
  match sf with
    | StackFrame.Kconstr obj ar i hp _ _ _ _ _ _ _ => Some (obj, ar, i, hp)
    | StackFrame.Kconstrother obj ar i hp _ _ _ _ _ _ _ _ => Some (obj, ar, i, hp)
    | StackFrame.Kdestr obj ar i hp => Some (obj, ar, i, hp)
    | StackFrame.Kdestrother obj ar i hp _ _ _ _ => Some (obj, ar, i, hp)
    | _ => None
  end.

Function kind_object (k : State.state_kind A nativeop) : option ident :=
  match k with
    | State.constr obj _ _ _ _ _ _ _ _ _ _ => Some obj
    | State.constr_array obj _ _ _ _ _ _ => Some obj
    | State.destr obj _ _ _ _ _ _ => Some obj
    | State.destr_array obj _ _ _ => Some obj
    | _ => None
  end.

Lemma frame_pointer_frame_array_weak : forall k obj ar' i' hp',
  frame_pointer k = Some (obj, ar', i', hp') ->
  frame_array_weak k = Some (obj, ar').
Proof.
  destruct k; simpl; congruence.
Qed.

Lemma frame_array_frame_array_weak : forall k obj ar',
  frame_array k = Some (obj, ar') ->
  frame_array_weak k = Some (obj, ar').
Proof.
  destruct k; simpl; try congruence.
  destruct k; try congruence.
  destruct kind; congruence.
Qed.

Lemma frame_array_weak_inv : forall k obj ar',
  frame_array_weak k = Some (obj, ar') ->
  (exists i', exists hp', frame_pointer k = Some (obj, ar', i', hp')) \/ frame_array k = Some (obj, ar').
Proof.
  destruct k; simpl; try congruence; injection 1; intros; subst; eauto.
Qed.  

Function block_objects (bl : list (BlockPoint.t A nativeop)) : list ident :=
  match bl with
    | nil => nil
    | BlockPoint.make _ sobj :: q =>
      match sobj with
        | None => nil
        | Some obj => obj :: nil
      end ++ block_objects q
  end.

Lemma block_objects_app : forall bl1 bl2, block_objects (bl1 ++ bl2) = block_objects bl1 ++ block_objects bl2.
Proof.
 induction bl1; simpl.
 trivial.
 intro.
 rewrite IHbl1.
 destruct a.
 rewrite app_ass.
 trivial.
Qed.


Function stackframe_objects (sf : list (StackFrame.t A nativeop)) : list ident :=
  match sf with
    | nil => nil
    | fr :: q =>
      match fr with
        | StackFrame.Kcontinue _ _ obj ostl bl => 
          (*match ostl with
            | Some _ => obj :: nil
            | _ => nil
          end ++ *) obj :: block_objects bl
        | StackFrame.Kreturnfromcall _ _ _ bl => block_objects bl
        | _ => nil
      end ++ stackframe_objects q
  end.

Function constructed_stackframe_objects (sf : list (StackFrame.t A nativeop)) : list ident :=
  match sf with
    | nil => nil
    | fr :: q =>
      match fr with
        | StackFrame.Kcontinue _ _ _ _ bl => block_objects bl
        | StackFrame.Kreturnfromcall _ _ _ bl => block_objects bl
        | _ => nil
      end ++ constructed_stackframe_objects q
  end.

Lemma constructed_stackframe_objects_incl : forall sf x, In x (constructed_stackframe_objects sf) -> In x (stackframe_objects sf).
Proof.
  induction sf; simpl.
   intros; assumption.
  intros.
  apply in_or_app.
  destruct (in_app_or _ _ _ H).
   left.
   destruct a; try assumption.
(*   apply in_or_app; *) auto.
  eauto.
Qed.

Definition stack_objects :=
  match s with
    | State.make sk stk _ _ _ _ =>
      match sk with
        | State.codepoint _ _ _ bl => block_objects bl
        | _ => nil
      end  ++ stackframe_objects stk
  end.

Definition constructed_stack_objects :=
  match s with
    | State.make sk stk _ _ _ _ =>
      match sk with
        | State.codepoint _ _ _ bl => block_objects bl
        |  _ => nil
      end ++ constructed_stackframe_objects stk
  end.

Lemma constructed_stack_objects_incl : forall x, In x (constructed_stack_objects) -> In x (stack_objects).
Proof.
  unfold stack_objects, constructed_stack_objects.
  destruct s.
  intros.
  apply in_or_app.
  destruct (in_app_or _ _ _ H); eauto using constructed_stackframe_objects_incl.
Qed.

Record constructed_base_child_of (cs' cs : option construction_state) : Prop  := construction_base_child_of_intro {
  constructed_base_child_of_none : (cs = None -> cs' = None);
  constructed_base_child_of_started_constructing : (cs = Some StartedConstructing -> (cs' =< Some Constructed));
  constructed_base_child_of_constructed : ((Some BasesConstructed =< cs) -> (cs =< (Some StartedDestructing)) -> cs' = Some Constructed);
  constructed_base_child_of_destructing_bases : (cs = Some DestructingBases -> (Some Constructed =< cs'));
  constructed_base_child_of_destructed : (cs = Some Destructed -> cs' = Some Destructed)
}.

Record constructed_field_child_of (cs' cs : option construction_state) : Prop := constructed_field_child_of_intro {
  constructed_field_child_of_none : ((cs =< Some StartedConstructing) -> cs' = None);
  constructed_field_child_of_bases_constructed : (cs = Some BasesConstructed -> cs' = None \/ cs' = Some StartedConstructing \/ cs' = Some Constructed);
  constructed_field_child_of_constructed : (cs = Some Constructed -> cs' = Some Constructed);
  constructed_field_child_of_started_destructing : (cs = Some StartedDestructing -> cs' = Some Constructed \/ cs' = Some StartedDestructing \/ cs' = Some Destructed);
  constructed_field_child_of_destructed : ((Some DestructingBases =< cs) -> cs' = Some Destructed)
}.

Record constructed_field_array_cell (cs cs' : option construction_state) : Prop := constructed_field_array_cell_intro {
  constructed_field_array_cell_none : cs = None -> cs' = None;
  constructed_field_array_cell_started_constructing : cs = Some StartedConstructing -> (cs' =< Some Constructed);
  constructed_field_array_cell_bases_constructed : cs = Some BasesConstructed -> False;
  constructed_field_array_cell_constructed : cs = Some Constructed -> cs' = Some Constructed;
  constructed_field_array_cell_started_destructing : cs = Some StartedDestructing -> (Some Constructed =< cs');
  constructed_field_array_cell_destructing_bases : cs = Some DestructingBases -> False;
  constructed_field_array_cell_destructed : cs = Some Destructed -> cs' = Some Destructed
}.

Record constructed_sibling_before (cs cs' : option construction_state) : Prop := constructed_sibling_before_intro {
  constructed_sibling_before_none : ((cs << Some Constructed) -> cs' = None);
  constructed_sibling_before_destructed : ((Some Constructed << cs) -> cs' = Some Destructed)
}.
    
Record invariant : Prop := invariant_intro {
  valid_global : Globals.valid (State.global s);
  construction_states_none : forall obj, (Globals.heap (State.global s)) ! obj = None -> forall rptr, assoc (@pointer_eq_dec _) (obj, rptr) (State.construction_states s) = None;
  construction_states_fields_none : forall obj, (Globals.heap (State.global s)) ! obj = None -> forall ar i hp fs, assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, hp, fs) (State.field_construction_states s) = None;
  valid_object_classes : forall obj o, (Globals.heap (State.global s)) ! obj = Some o -> hier ! (Object.class o) <> None;
  object_arraysizes_nonnegative : forall obj o, (Globals.heap (State.global s)) ! obj = Some o -> (0 <= Object.arraysize o)%Z;
  kind :  state_kind_inv;
  stack : forall sf, In sf (State.stack s) -> stackframe_weak_inv sf;
  stack2 : forall sf1 l1 l2, State.stack s = l1 ++ sf1 :: l2 -> stack2_inv sf1 l2;
  stack_state : forall sf l, State.stack s = sf :: l -> frame_requires_code sf -> is_code_state (State.kind s);
  stack_state_wf : match State.kind s with
                     | State.constr obj ar i hp _ _ _ _ _ _ _ => forall k, In k (State.stack s) -> ((forall ar' i' hp', frame_pointer k = Some (obj, ar', i', hp') -> relptr_gt hier (ar, i, hp) (ar', i', hp')) /\ forall ar', frame_array k = Some (obj, ar') -> exists l', ar = ar' ++ l')
                     | State.constr_array obj ar _ _ _ _ _ => forall k, In k (State.stack s) -> forall ar', frame_array_weak k = Some (obj, ar') -> exists l', ar = ar' ++ l' /\ l' <> nil
                     | State.destr obj ar _ _ Constructor.base Constructor.virtual _ => forall k, In k (State.stack s) -> forall ar', frame_array_weak k = Some (obj, ar') -> exists l', ar = ar' ++ l' /\ l' <> nil
                     | State.destr obj ar i hp _ _ _ => forall k, In k (State.stack s) -> ((forall ar' i' hp', frame_pointer k = Some (obj, ar', i', hp') -> relptr_gt hier (ar, i, hp) (ar', i', hp')) /\ forall ar', frame_array k = Some (obj, ar') -> exists l', ar = ar' ++ l')
                     | State.destr_array obj ar _ _ => forall k, In k (State.stack s) -> forall ar', frame_array_weak k = Some (obj, ar') -> exists l', ar = ar' ++ l' /\ l' <> nil
                     | _ => True
                   end
  ;
  stack_wf : forall sf1 l1 l2, State.stack s = l1 ++ sf1 :: l2 -> forall sf2, In sf2 l2 -> ((
    forall obj ar i hp, frame_pointer sf1 = Some (obj, ar, i, hp) -> ((
      forall ar' i' hp', frame_pointer sf2 = Some (obj, ar', i', hp') -> relptr_gt hier (ar, i, hp) (ar', i', hp')
    ) /\
    forall ar', frame_array sf2 = Some (obj, ar') -> exists l', ar = ar' ++ l'
    )) /\
  forall obj ar, frame_array sf1 = Some (obj, ar) -> forall ar', frame_array_weak sf2 = Some (obj, ar') -> exists l', ar = ar' ++ l' /\ l' <> nil
  )
  ;

 (** Depth (subobject inclusion) *)

  construction_states_direct_non_virtual_bases : forall obj ar i h p hp,
    valid_pointer hier (Globals.heap (State.global s)) (Value.subobject obj ar i h p hp) ->
      forall cn, last p = Some cn ->
        forall c, hier ! cn = Some c ->
          forall b, In (Class.Inheritance.Repeated, b) (Class.super c) ->
            constructed_base_child_of (assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p ++ b :: nil))) (State.construction_states s)) (assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states s))
            ;

  construction_states_virtual_bases : forall obj o,
    (Globals.heap (State.global s)) ! obj = Some o ->
    forall ar cn n,
      valid_array_path hier cn n (Object.class o) (Object.arraysize o) ar ->
      match last ar with
        | None => n = Object.arraysize o /\ cn = Object.class o
        | Some (_, _, fs) => exists n', n = Zpos n' /\ FieldSignature.type fs = FieldSignature.Struct cn n'
      end ->
      forall i, 0 <= i < n ->
        forall b, is_virtual_base_of hier b cn ->
          constructed_base_child_of (assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b :: nil))) (State.construction_states s)) (assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s))
          ;

  construction_states_fields : forall obj ar i h p hp,
    valid_pointer hier (Globals.heap (State.global s)) (Value.subobject obj ar i h p hp) ->
    forall cn, last p = Some cn ->
      forall c, hier ! cn = Some c ->
      forall fs, In fs (Class.fields c) ->
        constructed_field_child_of (assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, (h, p), fs) (State.field_construction_states s)) (assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states s))
        ;

  construction_states_structure_fields : forall obj ar i h p hp,
    valid_pointer hier (Globals.heap (State.global s)) (Value.subobject obj ar i h p hp) ->
    forall cn, last p = Some cn ->
      forall c, hier ! cn = Some c ->
        forall fs, In fs (Class.fields c) ->
          forall b n, FieldSignature.type fs = FieldSignature.Struct b n ->
            forall j, 0 <= j < Zpos n ->
              constructed_field_array_cell (assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, (h, p), fs) (State.field_construction_states s)) (assoc (@pointer_eq_dec _) (obj, ((ar ++ (i, (h, p), fs) :: nil), j, (Class.Inheritance.Repeated, b :: nil))) (State.construction_states s))
              ;

(** Breadth (occurs before) *)

 breadth_virtual_bases : forall obj o,
    (Globals.heap (State.global s)) ! obj = Some o ->
    forall ar cn n,
      valid_array_path hier cn n (Object.class o) (Object.arraysize o) ar ->
      match last ar with
        | None => n = Object.arraysize o /\ cn = Object.class o
        | Some (_, _, fs) => exists n', n = Zpos n' /\ FieldSignature.type fs = FieldSignature.Struct cn n'
      end ->
      forall i, 0 <= i < n ->
        forall c, hier ! cn = Some c ->
          forall l0 b1 l1 b2 l2, vborder_list hier (Class.super c) (l0 ++ b1 :: l1 ++ b2 :: l2) ->
            constructed_sibling_before (assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b1 :: nil))) (State.construction_states s)) (assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, b2 :: nil))) (State.construction_states s))
            ;

 breadth_virtual_non_virtual_bases : forall obj o,
    (Globals.heap (State.global s)) ! obj = Some o ->
    forall ar cn n,
      valid_array_path hier cn n (Object.class o) (Object.arraysize o) ar ->
      match last ar with
        | None => n = Object.arraysize o /\ cn = Object.class o
        | Some (_, _, fs) => exists n', n = Zpos n' /\ FieldSignature.type fs = FieldSignature.Struct cn n'
      end ->
      forall i, 0 <= i < n ->
        forall vb, is_virtual_base_of hier vb cn ->
        forall c, hier ! cn = Some c ->
          forall nvb, In (Class.Inheritance.Repeated, nvb) (Class.super c) ->
            constructed_sibling_before (assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Shared, vb :: nil))) (State.construction_states s)) (assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nvb :: nil))) (State.construction_states s))
            ;
  
  breadth_non_virtual_bases : forall obj ar i h p hp,
    valid_pointer hier (Globals.heap (State.global s)) (Value.subobject obj ar i h p hp) ->
    forall cn, last p = Some cn ->
      forall c, hier ! cn = Some c ->
        forall l0 b1 l1 b2 l2, map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b) (filter (fun hb : _ * ident =>
          match hb with
            | (Class.Inheritance.Shared, _) => false
            | _ => true
          end
        ) (Class.super c)) = (l0 ++ b1 :: l1 ++ b2 :: l2) ->
        constructed_sibling_before (assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p ++ b1 :: nil))) (State.construction_states s)) (assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p ++ b2 :: nil))) (State.construction_states s))
        ;

  breadth_fields : forall obj ar i h p hp,
    valid_pointer hier (Globals.heap (State.global s)) (Value.subobject obj ar i h p hp) ->
    forall cn, last p = Some cn ->
      forall c, hier ! cn = Some c ->
        forall l0 b1 l1 b2 l2, Class.fields c = (l0 ++ b1 :: l1 ++ b2 :: l2) ->
          constructed_sibling_before (assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, (h, p), b1) (State.field_construction_states s)) (assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, (h, p), b2) (State.field_construction_states s))
          ;

 breadth_arrays : forall obj o,
    (Globals.heap (State.global s)) ! obj = Some o ->
    forall ar cn n,
      valid_array_path hier cn n (Object.class o) (Object.arraysize o) ar ->
      match last ar with
        | None => n = Object.arraysize o /\ cn = Object.class o
        | Some (_, _, fs) => exists n', n = Zpos n' /\ FieldSignature.type fs = FieldSignature.Struct cn n'
      end ->
      forall i1 i2, 0 <= i1 -> i1 < i2 -> i2 < n ->
        constructed_sibling_before (assoc (@pointer_eq_dec _) (obj, (ar, i1, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s)) (assoc (@pointer_eq_dec _) (obj, (ar, i2, (Class.Inheritance.Repeated, cn :: nil))) (State.construction_states s))
        ;

(** Stack objects *)
  
  stack_objects_no_dup : NoDup stack_objects
    ;
  stack_objects_exist : forall obj, In obj stack_objects -> (Globals.heap (State.global s)) ! obj <> None
    ;
  constructed_stack_objects_correct : forall obj, In obj constructed_stack_objects -> forall o, (Globals.heap (State.global s)) ! obj = Some o -> forall i, 0 <= i < Object.arraysize o -> assoc (@pointer_eq_dec _) (obj, (nil, i, (Class.Inheritance.Repeated, Object.class o :: nil))) (State.construction_states s) = Some Constructed
    ;
  constructed_stack_objects_no_kind : forall obj, In obj constructed_stack_objects -> kind_object (State.kind s) = Some obj -> False
    ;
  constructed_stack_objects_no_stackframe : forall obj, In obj constructed_stack_objects -> forall sf, In sf (State.stack s) -> forall ar, frame_array_weak sf = Some (obj, ar) -> False
    ;
  stack_objects_in_construction : forall l1 sf l2, State.stack s = l1 ++ sf :: l2 -> forall obj ar, frame_array_weak sf = Some (obj, ar) -> exists l', stackframe_objects l2 = obj :: l'
    ;

  stack_objects_sorted : sorted (fun x y => Plt y x) stack_objects
    ;

  kind_object_in_construction : forall obj, kind_object (State.kind s) = Some obj -> exists l', stack_objects = obj :: l'

    ;
(** Deallocated objects *)

  deallocated_objects_exist :  forall obj, In obj (State.deallocated_objects s) -> (Globals.heap (State.global s)) ! obj <> None
    ;

  deallocated_objects_not_in_stack : forall obj, In obj stack_objects -> In obj (State.deallocated_objects s) -> False
    ;

  deallocated_objects_destructed : forall obj, In obj (State.deallocated_objects s) -> forall o, (Globals.heap (State.global s)) ! obj = Some o -> forall i, 0 <= i < Object.arraysize o -> assoc (@pointer_eq_dec _) (obj, (nil, i, (Class.Inheritance.Repeated, Object.class o :: nil))) (State.construction_states s) = Some Destructed
    ;

  stack_or_deallocated :  forall obj,  (Globals.heap (State.global s)) ! obj <> None -> In obj stack_objects \/ In obj (State.deallocated_objects s)

    ;

 (** Unconstructed scalar fields *)

  unconstructed_scalar_fields : forall obj, (Globals.heap (State.global s)) ! obj = None -> forall fs ty, FieldSignature.type fs = FieldSignature.Scalar ty -> forall ar i hp, Globals.get_field (Globals.field_values (State.global s)) (obj, ar, i, hp, fs) = None
   
               
               
}.

End Invariant.

End Invar.

Ltac solve_cs_order := simpl; omega.
