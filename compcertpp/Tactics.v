Load Param.

Ltac changeall v f P :=
match P with
| v => f
| forall x : ?T, ?b => let T2 := changeall v f T with b2 := changeall v f b in
  constr:(forall x : T2, b2)
| exists x : ?T, ?b => let T2 := changeall v f T with b2 := changeall v f b in
  constr:(exists x : T2, b2)
| (fun x : ?T => ?b) => let T2 := changeall v f T with b2 := changeall v f b in
  constr:(fun x : T2 => b2)
| (?a ?b) => let a2 := changeall v f a with b2 := changeall v f b in
  constr:(a2 b2)
| (?a -> ?b) => let a2 := changeall v f a with b2 := changeall v f b in
  constr:(a2 -> b2)
| _ => P
end.

Ltac setvar v f H :=
match goal with
| [|- ?P] =>
  let P2 := changeall f v P in
  cut (forall v, f = v -> P2) ;
  [intro H ; apply (H (f) (refl_equal _)) | intros v H ]
end.

Ltac var1 v f :=
 let H := fresh "H" in
 setvar v f H
.

Ltac var0 f :=
 let v := fresh "v" in
 let H := fresh "H" in
 setvar v f H
.

Ltac var f :=
 let v := fresh "v" in
 let H := fresh "H" in
 setvar v f H ; (rewrite H || idtac)
.

Ltac genclear H := generalize H ; clear H.

Ltac econtr := eapply False_rect ; eauto.

Ltac invert_all :=
match goal with
| [ |- ?Q ] =>
 match type of Q with
  | Prop => match goal with
    | [ H : exists x, _ |- _ ] => inversion_clear H
    end
 | _ =>
  match goal with
    | [ H : _ /\ _ |- _ ] => inversion_clear H
    | [ H : _ <-> _ |- _ ] => inversion_clear H
    | [ H : { x : _ & _ } |- _ ] => inversion_clear H
    | [ H : { x : _ | _ } |- _ ] => inversion_clear H
  end
 end
end.

Ltac invall := repeat invert_all.

Ltac discr :=
match goal with
| [ H1 : ?k = _ , H2 : ?k = _ |- _ ] => rewrite H2 in H1 ; clear H2 ; discr
| [ H1 : ?k = _ , H2 : _ = ?k |- _ ] => rewrite <- H2 in H1 ; clear H2 ; discr
| _ => discriminate
end.

(*
Goal forall (A : Set) (a b c : A) (H1 : a = b) (H2 : a = c), True.
intros.
discr || eauto.
Save.

Goal forall a, a = true -> a = false -> False.
intros.
discr.
Save.
*)

Ltac contreq :=
match goal with
| [ H1 : ?a <> ?a |- _ ] => contradiction (refl_equal a)
| [ H1 : ?a <> ?b , H2 : ?b = ?c |- _ ] => rewrite H2 in H1 ; clear H2 ; contreq
| [ H1 : ?a <> ?b , H2 : ?c = ?b |- _ ] => rewrite <- H2 in H1 ; clear H2 ; contreq
| [ H1 : ?a = ?b -> False, H2 : ?b = ?c |- _ ] => rewrite H2 in H1 ; clear H2 ; contreq
| [ H1 : ?a = ?a -> False |- _  ] => contradiction (refl_equal a)
| [ H1 : ?a = ?b -> False, H2 : ?c = ?b |- _ ] => rewrite <- H2 in H1 ; clear H2 ; contreq
end.

(*
Goal forall (A : Set) (a : A), (a <> a) -> False.
intros.
contreq.
Save.
*)

Ltac introvars :=
match goal with
| [ |- ?P -> ?Q ] => idtac
| [ |- forall _, _ ] => intro ; introvars
| _ => idtac
end.

(*
Goal forall (x y : Type), x = y -> True.
introvars.
auto.
Save.
*)

Ltac dup H := generalize H; intro.
(*
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive sigT => "pi" [ "" ].
Extract Inductive prod => "pi" [ "" ].

Extract Inductive sumor => "option" [ "Some" "None" ].
*)
(* Extract Inductive sig => "" [ "" ]. *)

Lemma ex_set_prop : forall (A : Type) P,
{a : A | P a} -> exists a, P a.
Proof.
intros ? ? [a Ha]; exists a; auto.
Qed.

Lemma option_inj : forall A (a : A) b, Some a = Some b -> a = b.
Proof.
injection 1; auto.
Qed.

Lemma conj_step : forall (A B : Prop), A -> (A -> B) -> A /\ B.
Proof.
tauto.
Qed.


Ltac asplit :=
  match goal with
    | |- ?A /\ ?B =>
      cut (A /\ (A -> B)) ; [ tauto | split ; [ | intro ] ]
    | |- (?A * ?B)%type =>
      cut (A * (A -> B)) ; [ tauto | split ; [ | intro ] ]
  end.

Ltac bsplit :=
  match goal with
    | |- ?B /\ ?A =>
      cut (A /\ (A -> B)) ; [ tauto | split ; [ | intro ] ]
    | |- (?B * ?A)%type =>
      cut (A * (A -> B)) ; [ tauto | split ; [ | intro ] ]
  end.


Ltac use h := 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ _ )) || 
refine (_ (h _ _ _ _ )) || 
refine (_ (h _ _ _ )) || 
refine (_ (h _ _ )) || 
refine (_ (h _ )) || 
fail 1 "Pas assez d'arguments".

Ltac invoke h := use h ; try eassumption ; intro ; try invall.

Ltac invoke' h := use h ; try eassumption.

Remark if_some_commut : forall (U V : Prop) (d : {U} + {V}) (X : Type) (x1 x2 : X), (if d then Some x1 else Some x2) = Some (if d then x1 else x2).
Proof.
 intros; destruct d; trivial.
Qed.


Ltac bintro := refine ((fun F => conj (fun b => proj1 (F b)) (fun b => proj2 (F b))) (fun b => _)).

Remark and_assoc : forall A B C : Prop, (A /\ B) /\ C -> A /\ B /\ C.
Proof. tauto. Qed.


  Ltac try_dependent_revert i :=
    match goal with
      | h: ?P |- _ => 
        match P with
          | context [ i ] => revert h
        end
    end.
  Ltac dependent_revert i := 
    repeat try_dependent_revert i;
      revert i.

