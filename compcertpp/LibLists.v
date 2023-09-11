
Require Export List.
Require Export Tactics.
Require Export Coqlib.
Require Import Wf_nat.
Require Import Recdef.

Load Param.

Hint Resolve in_eq in_cons.

Lemma list_inj : forall A (a : A) a' b b', a::b = a'::b' -> (a=a' /\ b=b').
Proof.
injection 1; auto.
Qed.

Lemma list_cons_right_inj : forall (A : Type) l1 (a1: A) l2 a2, l1 ++ a1 :: nil = l2 ++ a2 :: nil -> l1 = l2 /\ a1 = a2.
Proof.
 induction l1.
  simpl.
  destruct l2; simpl.
  intros; split; congruence.
  destruct l2; simpl; intros; discriminate.
 simpl.
 destruct l2.
  destruct l1; simpl; intros; discriminate.
 simpl.
 injection 1; intros; subst.
 destruct (IHl1 _ _ _ H0).
 subst; split; trivial.
Qed.

Remark list_cons_inj : forall (T : Type) (a1 a2 : T) q1 q2,
  a1 :: q1 = a2 :: q2 ->
  a1 = a2 /\ q1 = q2.
Proof.
  intros; split; congruence.
Qed.


Open Scope nat_scope.

Section List_addons.

Variable A : Type.

(** *** List membership. *)

Lemma member_nil : forall (x : A), In x nil -> False.
Proof.
inversion 1.
Qed.

Hint Resolve member_nil.

Lemma member_step : forall (x : A) a, x <> a ->
forall l, In x (a::l) -> In x l.
Proof.
intros until 1.
inversion 1 ; subst ; eauto.
congruence.
Qed.

Fixpoint find_in_list (l : list A) (n : nat) {struct n} : option A :=
  match l with
    | nil => None
    | a' :: l' =>
      match n with
        | O => Some a'
        | S n' => find_in_list l' n'
      end
  end.

Lemma find_in_list_member : forall n l a,
find_in_list l n = Some a -> In a l.
Proof.
induction n; destruct l; simpl; intros; try discriminate.
 left; congruence.
 right; eauto.
Qed.

Lemma member_find_in_list : forall l a, In a l ->
  exists n, find_in_list l n = Some a.
Proof.
induction l; inversion 1; subst.
exists O.
reflexivity.
generalize (IHl _ H0).
intros [n ?].
exists (S n).
auto.
Qed.


Section Member_dec.
Hypothesis eq_A_dec : forall x y : A, {x = y} + {x <> y}.

Lemma member_dec : 
forall (x : A) l, {In x l} + {In x l -> False}.
Proof.
 exact (In_dec eq_A_dec).
Qed.

Lemma member_which_dec :
forall (a : A) l x, In x (a::l) -> {x = a} + {In x l}.
Proof.
intros a l x.
destruct (eq_A_dec x a).
auto.
intros Hx.
right.
inversion Hx.
congruence.
eauto.
Defined.

Definition member_rect : forall (e : A) (P : list A -> Type),
 (forall l : list A, P (e :: l)) ->
       (forall l : list A, In e l -> P l -> forall a : A, P (a :: l)) ->
       forall l : list A, In e l -> P l.
Proof.
intros e P Hhead Htail.
induction l.
intro Hmem.
apply False_rect.
inversion Hmem.
intro Hmem.
destruct (member_which_dec Hmem).
subst.
apply Hhead.
apply Htail.
trivial.
auto.
Defined.

Definition find_in_list_constr : forall l e, In e l -> 
{n | find_in_list l n = Some e}.
Proof.
intros.
eapply (@member_rect e (fun l => {n : nat | find_in_list l n = Some e})).
intros.
exists O.
reflexivity.
intros ? ? [n ?] ?.
exists (S n).
auto.
auto.
Defined.

End Member_dec.

(** *** Universal property on all items of a list. *)

Section List_forall.

Variable P : A -> Prop.

Fixpoint list_forall (l : list A) {struct l} : Prop :=
  match l with
    | nil => True
    | a' :: l' => P a' /\ list_forall l'
  end.

(*
Inductive list_forall : list A -> Prop :=
| list_forall_nil : list_forall nil
| list_forall_cons
   (a : A)
   (l : list A) 
   (_ : P a)
   (_ : list_forall l) :
  list_forall (a::l)
.

Hint Constructors list_forall.
*)

Theorem list_forall_correct : forall l,
list_forall l -> forall x, In x l -> P x.
Proof.
induction l ; inversion 1 ; inversion 1; auto; congruence.
Qed.

Theorem list_forall_complete : forall l,
(forall x, In x l -> P x) -> list_forall l.
Proof.
induction l ; simpl; auto.
Qed.

End List_forall.

(** *** No duplicates

 A list not containing twice the same item. *)

(* Fixpoint repeat n (a : A) := match n with O => nil | S n' => a::(@repeat n' a) end. *)

End List_addons.

Ltac automem :=
match goal with
| [ H: In _ nil |- _ ] => apply False_rect ; inversion H
| _ => idtac
end.



Lemma member_map : forall (A : Type) l x, In x l -> forall (B : Type) (f : A -> B),
In (f x) (map f l).
Proof.
induction l ; inversion 1; simpl ; auto; intros; left; congruence.
Qed.

Lemma map_intro : forall (A : Type) l x, In x l -> forall (B : Type) (f : A -> B) y,
  y = f x -> In y (map f l).
Proof.
  intros ; subst ; auto using member_map.
Qed.

Lemma map_elim : forall (A : Type) (B : Type) (f : A -> B) l y, In y (map f l) ->
  exists x, In x l /\ f x = y.
Proof.
  induction l.
   inversion 1.
  inversion 1.
  repeat esplit.
  left.
  reflexivity.
  assumption.
 destruct (IHl _ H0).
 destruct H1.
 esplit.
 split.
 2 : eassumption.
 auto.
Qed.


Lemma map_length : forall (A B : Type) (f : A -> B) l, length l = length (map f l).
Proof.
induction l ; simpl ; auto.
Qed.

Remark map_some_inj : forall (T : Type) l1 l2,
  map (@Some T) l1 = map (@Some _) l2 ->
  l1 = l2.
Proof.
  induction l1; destruct l2; simpl; try congruence.
  injection 1; intros; subst.
  f_equal.
  eauto.
Qed.


(* Equations with ++ (app) *)

Section App_facts.
Variable A : Type.

Require Import Arith.

Lemma app_fix_left : forall (l l0 : list A), l = l ++ l0 -> l0 = nil.
Proof.
induction l.
simpl.
auto.
simpl.
intros l0 H.
injection H.
intros.
auto.
Qed.

Lemma app_fix_right : forall (l l0 : list A), l = l0 ++ l -> l0 = nil.
Proof.
intros l l0 Hll0.
generalize (app_length l0 l).
rewrite <- Hll0.
rewrite plus_comm.
pattern (length l) at 1.
rewrite <- (plus_0_r (length l)).
intro Hlength.
generalize (plus_reg_l _ _ _ Hlength).
case l0.
auto.
simpl.
discriminate 1.
Qed.

Lemma app_reg_l : forall l l1 l2 : list A, l ++ l1 = l ++ l2 -> l1 = l2.
Proof.
induction l.
simpl.
auto.
simpl.
injection 1.
auto.
Qed.

Lemma rev_inj : forall l1 l2 : list A, rev l1 = rev l2 -> l1 = l2.
Proof.
intros.
rewrite <- (rev_involutive l1).
rewrite <- (rev_involutive l2).
f_equal.
auto.
Qed.

Lemma app_reg_r : forall l l1 l2 : list A, l1 ++ l = l2 ++ l -> l1 = l2.
Proof.
introvars.
rewrite <- (rev_involutive (l1 ++ l)).
rewrite <- (rev_involutive (l2 ++ l)).
rewrite distr_rev.
rewrite (distr_rev l2).
intro H.
generalize (rev_inj H).
intros.
apply rev_inj.
eapply app_reg_l.
eauto.
Qed.

Lemma rev_app : forall l1 l2 : _ A, rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
 induction l1.
 simpl.
 intros. apply app_nil_end.
 simpl.
 intros. 
 rewrite IHl1.
 apply app_ass.
Qed.

Remark app_cons : forall (A : Type) (sf : A) l l1 l2,
  l = l1 ++ sf :: l2 ->
  forall a,
    a :: l = (a :: l1) ++ sf :: l2.
Proof.
  intros; simpl; congruence.
Qed.

Remark app_ass2 : forall (A : Type) (sf1 sf2 : A) l1 l2,
l1 ++ sf1 :: sf2 :: l2 = (l1 ++ sf1 :: nil) ++ sf2 :: l2.
Proof.
  intros.
  rewrite app_ass.
  reflexivity.
Qed.

Lemma no_self_append_no_nil : forall (A : Type) (l : _ A),
  (exists l', l = l ++ l' /\ l' <> nil) -> False.
Proof.
  intros; invall.
  destruct x.
   congruence.
  generalize (refl_equal (length l)).
  rewrite H at 1.
  rewrite app_length.
  simpl.
  intros.
  omegaContradiction.
Qed.




Lemma member_or : forall l1 l2 (b : A), In b (l1 ++ l2) -> In b l1 \/ In b l2.
Proof.
 intros; apply in_app_or; auto.
Qed.

Lemma member_app_left : forall l1 (b : A), In b l1 -> forall l2, In b (l1 ++ l2).
Proof.
induction l1;simpl; inversion 1; auto.
Qed.

Lemma member_app_right : forall l1 l2 (b : A), In b l2 -> In b (l1 ++ l2).
Proof.
induction l1; simpl; auto.
Qed.

Lemma no_duplicates_no_member_app : forall l1 l2, NoDup (l1 ++ l2) -> forall x : A, In x l1 -> In x l2 -> False.
Proof.
induction l1; simpl.
 inversion 2.
inversion 1.
subst.
inversion 1.
 subst.
 intros.
 apply H2.
 apply member_app_right.
 assumption.
subst.
eauto.
Qed.

Lemma member_extract : forall l (b : A), In b l -> exists l1, exists l2, l = l1 ++ (b :: l2).
Proof.
intros; apply In_split; auto.
Qed.

Fixpoint flatten l :=
  match l with
    | nil => nil (A := A)
    | a::b => a ++ flatten b
  end.

Lemma member_flatten_elim : forall l a, In a (flatten l) ->
  exists l0, In l0 l /\ In a l0.
Proof.
induction l; simpl.
 inversion 1.
intros a0 Ha0.
generalize (member_or Ha0).
simple inversion 1.
 intros.
 esplit.
 split.
  left; reflexivity.
 assumption.
intro HIH.
generalize (IHl _ HIH).
intros [l0 [Hl0 Ha0l0]].
esplit.
split.
 right.
 eassumption.
assumption.
Qed.

Lemma member_flatten_intro : forall l l0,
  In l0 l -> forall a, In a l0 -> In a (flatten l).
Proof.
induction l; simpl; inversion 1.
 intros; subst.
 eapply member_app_left; eauto.
 intros.
eapply member_app_right; eauto.
Qed.

Hypothesis eq_A_dec : forall a b : A, {a = b} + {a <> b}.

Let md := member_rect eq_A_dec.

Lemma member_flatten_elim_type : forall l a, In a (flatten l) ->
  {l0 | In l0 l /\ In a l0}.
Proof.
induction l; simpl.
 inversion 1.
intros a0 Ha0.
generalize (member_or Ha0).
intros.
destruct (In_dec eq_A_dec a0 a).
 esplit.
 split.
  left; reflexivity.
 assumption.
assert (
  In a0 (flatten l)
) as HIH by tauto.
generalize (IHl _ HIH).
intros [l0 [Hl0 Ha0l0]].
esplit.
split.
 right.
 eassumption.
assumption.
Qed.

Lemma member_extract_dec :
forall l (b : A), In b l -> {l1 : _ & {l2 | l = l1 ++ (b :: l2)}}.
Proof.
induction l.
intros b Hb; apply False_rect; inversion Hb.
intros b Hb.
destruct (member_which_dec eq_A_dec Hb).
subst.
exists (@nil A).
simpl.
exists l.
trivial.
destruct (IHl _ i) as [l1 [l2 Hl]].
exists (a::l1).
exists (l2).
simpl.
congruence.
Defined.

Lemma member_map_recip_type :
  forall (B : Type) (f : B -> A) l a,
    In a (map f l) ->
    {b | f b = a /\ In b l}.
Proof.
induction l.
simpl.
intros.
contradiction.
 simpl.
intros b.
destruct (eq_A_dec (f a) b).
 intros.
exists a.
auto.
intros.
assert (In b (map f l)).
inversion H ; tauto.
destruct (IHl _ H0).
destruct a0.
exists x.
auto.
Qed.
   

End App_facts.

Section Sorted.
Variable A : Type.
Variable ord : A -> A -> Prop.

Inductive sorted : list A -> Prop := 
| sorted_O: sorted nil
| sorted_1: forall x, sorted (cons x nil)
| sorted_S: forall x y, ord x y -> forall l, sorted (cons y l) -> sorted (cons x (cons y l)).

Hint Constructors sorted.

Lemma sorted_tail : forall a l, sorted (a::l) -> sorted l.
Proof.
 inversion 1.
  auto.
 auto.
Qed.

Hypothesis eq_A_dec : forall a b : A, {a = b} + {a <> b}.

Fixpoint occur a l {struct l} := match l with
| nil => O
| cons b m => match eq_A_dec a b with
  | left _ => S (@occur a m)
  | right _ => @occur a m
  end
end.

Lemma occur_member : forall l a n, occur a l = S n -> In a l.
Proof.
induction l.
simpl.
discriminate 2.
simpl.
intros a0 n.
destruct (eq_A_dec a0 a); subst; eauto.
Qed.

Lemma occur_not_member : forall l a, occur a l = O -> In a l -> False.
Proof.
induction l.
inversion 2.
simpl.
intros a0.
destruct (eq_A_dec a0 a).
discriminate 1.
inversion 2.
congruence.
subst; eauto.
Qed.

Definition sameocc l1 l2 := forall a, occur a l1 = occur a l2.

Lemma sameocc_member l1 l2 : sameocc l1 l2 -> forall c, In c l1 -> In c l2.
Proof.
unfold sameocc.
intros l1 l2 Hbis.
intros c Hc.
case_eq (occur c l1).
intros Ho.
destruct (occur_not_member Ho Hc).
rewrite Hbis.
apply occur_member.
Qed.

Hypothesis ord_dec : forall a b, {ord a b} + {ord a b -> False}.

Hypothesis ord_total : forall a b, ord a b \/ ord b a.

Hypothesis ord_trans : forall a b, ord a b -> forall c, ord b c -> ord a c.

Lemma head_minimal : forall l, sorted l -> forall c l', l = c::l' -> forall d, In d l' -> ord c d.
Proof.
induction 1.
discriminate 1.
injection 1.
intros until 2.
subst.
inversion 1.
injection 1.
intros until 2.
subst.
inversion 1. 
subst; auto.
eapply ord_trans; eauto.
Qed.


Fixpoint sorted2 (l : list A) : Prop :=
  match l with
    | nil => True
    | a' :: l' => (forall i, In i l' -> ord a' i) /\ sorted2 l'
  end.

Lemma sorted_sorted2 : forall l, sorted l -> sorted2 l.
Proof.
induction 1.
 simpl; tauto.
 simpl. split. inversion 1. tauto.
 simpl in *.
 invall.
 intuition.
 congruence.
 eauto.
Qed.

Lemma sorted2_sorted : forall l, sorted2 l -> sorted l.
Proof.
induction l.
 intros; auto.
 simpl.
 inversion 1.
destruct l.
 auto.
simpl in *.
inversion H1.
apply sorted_S.
apply H0.
auto.
auto.
Qed.

Lemma sorted_app : forall l1 l2, sorted (l1 ++ l2) -> forall a1, In a1 l1 ->
forall a2, In a2 l2 -> ord a1 a2.
Proof.
induction l1.
 inversion 2.
simpl.
inversion 2.
 subst.
 intros.
 eapply head_minimal.
  eexact H.
 reflexivity.
 apply member_app_right.
 assumption.
subst.
apply IHl1.
eapply sorted_tail.
eassumption.
assumption.
Qed.

Lemma sorted_app_left : forall l1 l2, sorted (l1 ++ l2) -> sorted l1.
Proof.
induction l1.
auto.
simpl.
inversion 1.
subst.
replace l1 with (@nil A).
apply sorted_1.
destruct l1; auto; simpl in H2; discriminate.
subst.
destruct l1; auto.
simpl in *.
apply sorted_S.
 congruence.
eapply IHl1.
rewrite H1 in H3.
eassumption.
Qed.

Lemma sorted_app_right : forall l1 l2, sorted (l1 ++ l2) -> sorted l2.
Proof.
induction l1; auto.
simpl.
 inversion 1.
 replace l2 with (@nil A).
 auto.
 destruct l2; auto; destruct l1; simpl in H2; discriminate.
subst.
rewrite H1 in H3.
eauto.
Qed.

Lemma sorted_app_intro : forall l1,
  sorted l1 ->
  forall l2,
    sorted l2 ->
    (forall i1, In i1 l1 -> forall i2, In i2 l2 -> ord i1 i2) ->
    sorted (l1 ++ l2)
.
Proof.
  intros.
  apply sorted2_sorted.
  generalize (sorted_sorted2 H).
  clear H.
  intro.
  generalize (sorted_sorted2 H0).
  clear H0.
  intro.
  revert H l2 H0 H1.
  induction l1 ; simpl.
   tauto.
  destruct 1.
  intros.
  split.
   intros.
   destruct (in_app_or _ _ _ H3) ; eauto.
  eauto.
Qed.
 

Definition sort_insert l : sorted l -> forall b, {l' | sorted l' /\ sameocc l' (b::l)}.
Proof.
induction l.
intros.
exists (cons b nil).
unfold sameocc; auto.
intros Hal b.
case (ord_dec b a).
intros Hba.
exists (b::a::l).
unfold sameocc; auto.
intros.
assert (sorted l) as Hl.
 inversion Hal; auto.
destruct (IHl Hl b) as [l' Hl'].
exists (a::l').
inversion Hl' as [Hl'sorted Hl'bis].
split.
case_eq l'.
auto.
intros a0 l'0 ?.
subst.
apply sorted_S.
destruct (eq_A_dec a0 b).
subst.
destruct (ord_total a b).
auto.
contradiction.
eapply head_minimal.
apply Hal.
reflexivity.
eapply member_step.
eauto.
eapply sameocc_member.
apply Hl'bis.
left; auto.
auto.
unfold sameocc in *.
intro a0.
simpl.
destruct (eq_A_dec a0 a).
subst.
rewrite Hl'bis.
simpl.
destruct (eq_A_dec a b); auto.
rewrite Hl'bis.
simpl.
auto.
Defined.

Definition sort l : {l' | sorted l' /\ sameocc l' l}.
Proof.
induction l.
exists (@nil A).
unfold sameocc; auto.
destruct IHl as [l' Hl'].
assert (sorted l') as Hl'2.
 inversion Hl'; auto.
destruct (sort_insert Hl'2 a) as [l'0 Hl'0].
exists l'0.
inversion Hl'0 as [Hl'1 Hl'3].
unfold sameocc in *.
split.
auto.
inversion_clear Hl' as [_ Hl'4].
intros a0.
rewrite Hl'3.
simpl.
destruct (eq_A_dec a0 a); auto.
Defined.

End Sorted.
Hint Constructors sorted.

Lemma imp_sorted_weak : 
  forall (A : Type) (P Q : A -> A -> Prop) (l : list A),
    (forall a b, In a l -> In b l -> P a b -> Q a b) ->
    sorted P l -> sorted Q l.
Proof.
induction l.
intros ; constructor.
destruct l.
intros ; constructor.
intros.
inversion H0.
subst.
constructor.
auto.
auto.
Qed.

Corollary imp_sorted :
  forall (A : Type) (P Q : A -> A -> Prop), (forall a b : A, P a b -> Q a b) ->
    forall l, sorted P l -> sorted Q l.
Proof.
intros.
revert H0.
apply imp_sorted_weak.
auto.
Qed.

Fixpoint repeat (A : Type) (a : A) (n : nat) {struct n} : list A :=
  match n with
    | O => nil
    | S n' => a :: (repeat a n')
  end.


Section Minimum_partial_order.

Variable A : Type.

Variable le : A -> A -> Prop.

Hypothesis le_antisym : forall a b,
  le a b -> le b a -> a = b.

Hypothesis le_trans : forall a b,
le a b -> forall c, le b c -> le a c.

Hypothesis le_dec : forall a b,
{le a b} + {~ le a b}.


Theorem minimum_partial_order : forall l 
(le_refl : forall a, In a l -> le a a ) ,
{a | In a l /\ forall b, In b l -> le a b} +
{forall a, In a l -> (forall b, In b l -> le a b) -> False}.
Proof.
 induction l using (well_founded_induction_type (well_founded_ltof _ (@length A))).
 unfold ltof in *.
 rename X into IHn.
 intro.
 destruct l.
  right.
  inversion 1.
 destruct l.
  left.
  esplit.
  split.
   left.
   reflexivity.
  inversion 1.
   subst.
   auto.
  contradiction.
 destruct (le_dec a a0).
  destruct (IHn (a :: l)).
     simpl.
     omega.
    simpl in le_refl.
    simpl.
    intros.
    destruct H ; auto.
   destruct s.
   destruct a1.
   left.
   exists x.
   split.
   simpl.
   simpl in H.
   tauto.
   inversion 1.
   subst.
   apply H0.
   simpl ; auto.
   inversion H2.
    subst.
    eapply le_trans.
    2 : eassumption.
     apply H0.
     simpl ; auto.
   apply H0.
   simpl ; auto.

  right.
  inversion 1.
   subst.
   intros.
   eapply f.
   Focus 2.
    intros.
    eapply H0.
    inversion H1 ; simpl ; auto.
   simpl ; auto.
  intros.
  inversion H0.
   subst.
   assert (le a1 a).
    apply H1.
    simpl ; tauto.
   generalize (le_antisym l0 H2).
   intros ; subst.
   eapply f.
   Focus 2.
    intros.
    eapply H1.
    simpl ; tauto.
   simpl ; auto.
  eapply f.
  right.
  eassumption.
  intros.
  eapply H1.
  inversion H3 ; simpl ; auto.

 destruct (IHn (a0 :: l)).
  simpl.
  omega.
  simpl in le_refl.
  auto.
  destruct s.
  destruct a1.
  destruct (le_dec x a). 
   left.
   exists x.
   split.
   simpl  in * ; auto.
   inversion 1 ; subst.
    assumption.
   auto.
  right.
  inversion 1 ; intros ; subst.
   destruct n.
   apply H3.
   simpl ; auto.
  destruct n0.
  replace x with a1.
  simpl in * ; auto.
  apply le_antisym.
  simpl in * ; auto.
  simpl in * ; auto.
 right.
 inversion 1 ; intros ; subst.
  destruct n.
  apply H1.
  simpl ; auto.
 eapply f.
 simpl ; eassumption.
 simpl in * ; auto.
Qed.

End Minimum_partial_order.

Section Minimals.

Variable A : Type.

Variable le : A -> A -> Prop.

Hypothesis le_antisym : forall a b,
  le a b -> le b a -> a = b.

Hypothesis le_trans : forall a b,
le a b -> forall c, le b c -> le a c.

Hypothesis le_dec : forall a b,
{le a b} + {~ le a b}.

Lemma is_minimal : forall i
  (le_refl_i : le i i)
  l
  (le_refl_l : forall j, In j l -> le j j) ,
  {j | In j l /\ le j i /\ j <> i} + {forall j, In j l -> le j i -> j = i}.
Proof.
  induction l ; simpl.
   right.
   tauto.
  intros.
  destruct (le_dec a i).
   destruct (le_dec i a).
    generalize (le_antisym l0 l1).
    intros ; subst.
    destruct IHl.
     auto.
    left.
    destruct s.
    exists x.
    tauto.
   right.
   inversion 1.
    auto.
   auto.
   left.
   exists a.
   split.
   auto.
   split.
   assumption.
   intro.
   subst.
   contradiction.
   destruct IHl.
   auto.
   destruct s.
   left.
   exists x.
   tauto.
   right.
   inversion 1.
    subst.
    intros.
    contradiction.
   auto.
 Qed.  

Lemma minimals_aux : forall l accu m
  (le_refl_accu_l : forall i, In i (accu ++ l) -> le i i)
  (le_refl_m : forall i, In i m -> le i i)
  (hyp : forall j, In j accu -> forall k, In k m -> le k j -> k = j),
  {n | forall j, In j n <-> (In j (accu ++ l) /\ forall k, In k m -> le k j -> k = j)}.
Proof.
 induction l ; simpl ; intros.
 rewrite <- app_nil_end.
 exists accu.
 intros.
 split.
  split.
   assumption.
   auto.
  tauto.
 assert (le a a) as le_refl_a.
  apply le_refl_accu_l.
  apply in_or_app.
  simpl.
  tauto.
 destruct (is_minimal le_refl_a le_refl_m).
  destruct s.
  invall.
  destruct (IHl accu m).
   intros.
   apply le_refl_accu_l.
   apply in_or_app.
   simpl.
   generalize (in_app_or _ _ _ H0).
   tauto.
  assumption. 
  assumption.
  exists x0.
  intro.
  destruct (i j).
  split.
   intros.
   destruct (H0 H4).
   generalize (in_app_or _ _ _ H5).
   intros.
   split.
   apply in_or_app.  
   simpl.
   tauto.
   assumption.
  destruct 1.
  destruct (in_app_or _ _ _ H4).
   apply H3.
   split.
   apply in_or_app.
   tauto.
   assumption.
  inversion H6.
   subst.
   destruct H2.
   auto.
  apply H3.
  split.
   apply in_or_app.
   tauto.
   assumption.
 destruct (IHl (a :: accu) m).
  simpl.
  inversion 1.
   congruence.
  destruct (in_app_or _ _ _ H0).
   apply le_refl_accu_l.
   apply in_or_app.
   tauto.
   apply le_refl_accu_l.
   apply in_or_app.
   simpl.
   tauto.
  assumption.
  inversion 1.
   subst.
   assumption.
  auto.
 exists x.
 intro.
 destruct (i j).
 split.
  intros.
  destruct (H H1).
  simpl in H2.
  split ; auto.
  apply in_or_app.
  simpl.
  inversion H2.
   tauto.
  generalize (in_app_or _ _ _ H4) ; tauto.
 destruct 1.
 apply H0.
 split ; auto.
 simpl.
 destruct (in_app_or _ _ _ H1).
  right ; apply in_or_app ; tauto.
 inversion H3 ; try tauto.
 right ; apply in_or_app ; tauto.
Qed.

Theorem minimals : forall l
  (le_refl_l : forall j, In j l -> le j j) ,
  {n | forall j, In j n <-> (In j l /\ forall k, In k l -> le k j -> k = j)}.
Proof.
  intros.
  apply (@minimals_aux l nil l).  
   simpl ; assumption.
   assumption.
   simpl ; tauto.
Qed.

End Minimals.



Section List_product.

  Variable A B : Type.

  Variable P : A -> B -> Prop.

  Hypothesis P_dec : forall a b, {P a b} + {~ P a b}.

  Lemma list_product : forall la lb,
    {lab | forall a b,
      In (a, b) lab <->
      (In a la /\ In b lb /\ P a b)}.
  Proof.
    intros.
    exists (
      flatten
      (List.map (fun a =>
        List.map (fun b =>
          (a, b)
        ) (
          List.filter
          (fun b => if P_dec a b then true else false)
          lb
        )
      )
      la)
    ).
    intros.
    split.
     intros.
     destruct (member_flatten_elim H).
     destruct H0.
     destruct (map_elim H0).
     destruct H2.
     subst.
     destruct (map_elim H1).
     destruct H3.
     injection H4 ; intros ; subst.
     destruct (filter_In (fun b => if P_dec a b then true else false) b lb).
     destruct (H5 H3).
     destruct (P_dec a b) ; try discriminate.
     auto.
    destruct 1.
    destruct H0.
    eapply member_flatten_intro.
    eapply map_intro.
    eassumption.
    reflexivity.
    eapply map_intro.
    2 : reflexivity.
    destruct (filter_In (fun b => if P_dec a b then true else false) b lb).
    apply H3.
    split.
    trivial.
    destruct (P_dec a b) ; congruence.
  Qed.

End  List_product.

Section At_most_list.
  Variable A : Type.
  Hypothesis eq_dec : forall a b : A, {a = b} + {a <> b}.

  Lemma at_most_list : forall l,
    {i : A & {j | In i l /\ In j l /\ i <> j}} +
    {forall i, In i l -> forall j, In j l -> i = j}.
  Proof.
    induction l ; simpl.
     right.
     tauto.
    destruct l ; simpl in *.
     simpl.
     right.
     simpl.
     inversion 1 ; try contradiction.
     inversion 1 ; try contradiction.
     congruence.
    destruct (eq_dec a a0).
     subst.
     destruct IHl.
      destruct s.
      destruct s.
      destruct a.
      destruct H0.
      left.
      repeat esplit.
      3 : eassumption.
      right ; eassumption.
      right ;  eassumption.
     right.
     intros.
     eapply e.
     inversion H as [? | [? | ?]] ; eauto.
     inversion H0 as [? | [? | ?]] ; eauto.
    left.
    exists a.
    exists a0.
    auto.
Qed.
    
End At_most_list.

Section Assoc.

  Variable key : Type.
  Hypothesis key_eq_dec : forall a b : key, {a = b} + {a <> b}.
  Variable value : Type.

  Function assoc (to_find : key) (l : list (key * value)) {struct l} : option value := 
    match l with
      | nil => None
      | (k, v) :: q =>
        if key_eq_dec k to_find
          then Some v
          else assoc to_find q
    end.

  Lemma assoc_In : forall to_find l val,
    assoc to_find l = Some val ->
    In (to_find, val) l.
  Proof.
    intros until val.
    functional induction (assoc to_find l) ; simpl.
     congruence.
    intros ; left ; congruence.
    intros ; right ; auto.
  Qed.

  Lemma assoc_not_In : forall to_find l,
    assoc to_find l = None ->
    forall val, ~ In (to_find, val) l.
  Proof.
    intros until l.
    functional induction (assoc to_find l) ; simpl.
     tauto.
     congruence.
    intros.
    intro.
    inversion H0.
    congruence.
    unfold not in * ; eauto.
  Qed.

  Lemma assoc_app_some : forall l1 to_find v,
    assoc to_find l1 = Some v ->
    forall l2,
    assoc to_find (l1 ++ l2) = Some v
    .
  Proof.
    intros until  v.
    functional induction (assoc to_find l1) ; simpl.
    congruence.
    rewrite e0.
    tauto.
    rewrite e0.
    assumption.
  Qed.

  Lemma assoc_app_none : forall l1 to_find,
    assoc to_find l1 = None ->
    forall l2,
    assoc to_find (l1 ++ l2) = assoc to_find l2.
  Proof.
    intros.
    functional induction (assoc to_find l1); simpl.
     tauto.
    congruence.
    rewrite e0.
    auto.
  Qed.

End Assoc.

Section Assoc_map.

  Variable key : Type.
  Hypothesis key_eq_dec : forall a b : key, {a = b} + {a <> b}.
  Variables value1 value2 : Type.

Section Assoc_map_aux.

  Variable f : key -> value1 -> option value2.

  Function assoc_map_aux (accu : list (key * value2))  (l : list (key * value1)) {struct l} : list (key * value2) :=
    match l with
      | nil => accu
      | (a, va) :: l' =>
        match f a va with
          | None =>         assoc_map_aux accu l'
          | Some vb =>
            match assoc key_eq_dec a accu with
              | None =>  assoc_map_aux ((a, vb) :: accu) l'
              | _ => assoc_map_aux accu l'
            end
        end
    end.

  Lemma assoc_map_aux_cons_right : forall l accu a,
    assoc_map_aux accu (l ++ a :: nil) = assoc_map_aux (assoc_map_aux accu l) (a :: nil).
  Proof.
    induction l ; simpl.
    trivial.
    intros.
    replace
      (let (a1, va) := a in
        match f a1 va with
          | Some vb =>
            match assoc key_eq_dec a1 accu with
              | Some _ => assoc_map_aux accu (l ++ a0 :: nil)
              | None => assoc_map_aux ((a1, vb) :: accu) (l ++ a0 :: nil)
            end
          | None => assoc_map_aux accu (l ++ a0 :: nil)
        end)
      with (assoc_map_aux (let (a1, va) := a in
        match f a1 va with
          | Some vb =>           
            match assoc key_eq_dec a1 accu with
              | Some _ => accu
              | None =>  ((a1, vb) :: accu)
            end
          | None => accu
        end)  (l ++ a0 :: nil))
      .    
    rewrite IHl.
    Opaque assoc.
    simpl.
    destruct a0.
    case_eq (f k v).
    destruct a.
    case_eq (f k0 v0).
    case_eq (assoc key_eq_dec k0 accu).
    trivial.
    trivial.
    trivial.
    destruct a.
    case_eq (f k0 v0).
    case_eq (assoc key_eq_dec k0 accu).
    trivial.
    trivial.
    trivial.
    destruct a.
    case_eq (f k v).
    case_eq (assoc key_eq_dec k accu).
    trivial.
    trivial.
    trivial.
  Qed.

  Corollary assoc_map_aux_app : forall l accu l1,
    assoc_map_aux accu (l1 ++ l) = assoc_map_aux (assoc_map_aux accu l1) l.
  Proof.
    induction l.
    intros.
    rewrite <- app_nil_end.
    reflexivity.
    intros.
    replace (l1 ++ a :: l) with ((l1 ++ a :: nil) ++ l) by (rewrite app_ass ; reflexivity).
    rewrite IHl.
    rewrite assoc_map_aux_cons_right.
    simpl.
    destruct a.
    destruct (f k v).
    destruct (assoc key_eq_dec k (assoc_map_aux accu l1)).
    trivial.
    trivial.
    trivial.
  Qed.

   (*
  Lemma assoc_map_aux_In : forall l l1 accu,
    (forall a vb, In (a, vb) (assoc_map_aux accu l1) <-> exists va, assoc key_eq_dec a l1 = Some va /\ f a va = Some vb) ->
    forall a vb, In (a, vb) (assoc_map_aux accu (l1 ++ l)) <-> exists va, assoc key_eq_dec a (l1 ++ l) = Some va /\ f a va = Some vb.
  Proof.
   induction l.
   intros.
   rewrite <- app_nil_end.
   auto.
   intros.
   replace (l1 ++ a :: l) with ((l1 ++ a :: nil) ++ l) by (rewrite app_ass ; reflexivity).
   apply IHl ; clear IHl.
   rewrite assoc_map_aux_app.
   simpl.
   destruct a.
   case_eq (f k v).
   case_eq (assoc key_eq_dec k (assoc_map_aux accu l1)).
   intros.
   generalize (H a vb0).
   destruct 1.
   split.
    intros.
    generalize (H2 H4).
    destruct 1.
    destruct H5.
    rewrite (assoc_app_some H5).
    repeat esplit.
    assumption.
   destruct 1.
   destruct H4.
   case_eq (assoc key_eq_dec a l1).
    intros.
    rewrite (assoc_app_some H6) in H4.
    apply H3.
    esplit.
    split.
    eassumption.
    congruence.
    intros.
    rewrite (assoc_app_none H6) in H4.
    functional inversion H4.
    clear H12.
    subst.
    generalize (assoc_In H0).
    intros.
    generalize (H a v0).
    destruct 1.
    generalize (H8 H7).
    destruct 1.
    destruct H10.
    congruence.
   clear H12.
   subst.
   functional inversion X.
  intro.
  

  intros.
  generalize (assoc_not_In H0).
  intro.
  split.
  inversion 1 ; subst.
  injection H4 ; intros ; subst.
   case_eq (assoc key_eq_dec a l1).
    intros.
    generalize (H a vb0).
    destruct 1.
    destruct (H2 vb0).
    apply H7.
    esplit.
    split.
    eassumption.
*)  
    

End Assoc_map_aux.

Variable f : value1 -> value2.


  Function map_snd (xy : key * value1) : key * value2 :=
    let (x, y) := xy in (x, f y).

  Lemma assoc_map_none : forall l x,
    assoc key_eq_dec x l = None ->
    assoc key_eq_dec x (map map_snd l) = None.
  Proof.
    induction l ; subst ; simpl.
     tauto.
     destruct a.
     simpl.
     intro x.
     destruct (key_eq_dec k x).
      congruence.
     auto.
  Qed.

  Lemma assoc_map_none_recip : forall l x,
    assoc key_eq_dec x (map map_snd l) = None ->
    assoc key_eq_dec x l = None.
  Proof.
    induction l ; subst ; simpl.
     tauto.
    destruct a ; simpl ; intro x ; destruct (key_eq_dec k x) ; try congruence; auto.
  Qed.

  Lemma assoc_map_some : forall l x y,
    assoc key_eq_dec x l = Some y ->
    assoc key_eq_dec x (map map_snd l) = Some (f y).
  Proof.
    induction l ; subst ; simpl.
     congruence.
    destruct a ; simpl.
    intro x.
    destruct (key_eq_dec k x).
     congruence.
    auto.
  Qed.

  Lemma assoc_map_some_recip : forall l x y2,
    assoc key_eq_dec x (map map_snd l) = Some y2 ->
    exists y1, assoc key_eq_dec x l = Some y1 /\ f y1 = y2.
  Proof.
    intros.
    case_eq (assoc key_eq_dec x l).
     intros v Hv.
      generalize (assoc_map_some Hv).
      intros.
    esplit.
    split.
     reflexivity.
     congruence.
    intro Hnone.
    generalize (assoc_map_none Hnone).
    congruence.
  Qed.

End Assoc_map.

(* Appending sorted lists with no duplicates (for efficiency) *)

Section Merge_sort.

Variable ident : Type.

Hypothesis peq : forall t1 t2 : ident, {t1 = t2} + {t1 <> t2}.

Variable Plt : ident -> ident -> Prop.

Hypothesis plt : forall t1 t2, {Plt t1 t2} + {~ Plt t1 t2}.

Function merge_aux
  (accu : list ident)
  (x : list ident * list ident)
  {measure
    (fun x0 : list ident * list ident => let (l1, l2) := x0 in length l1 + length l2)%nat
    x
  } : list ident :=
  let (l1, l2) := x in
    match l1 with
      | nil => rev' accu ++ l2
      | a1 :: q1 =>
        match l2 with
          | nil => rev' accu ++ l1
          | a2 :: q2 =>
            if peq a1 a2
              then merge_aux (a1 :: accu) (q1, q2)
              else if plt a1 a2
                then merge_aux (a1 :: accu) (q1, l2)
                else
                  merge_aux (a2 :: accu) (l1, q2)
        end
    end.
Proof.
  (intros; simpl; omega).
  (intros; simpl; omega).
  (intros; simpl; omega).
Qed.

Lemma merge_aux_prop : forall accu x l1 l2,
  x = (l1, l2) ->
  forall i, In i (accu ++ l1 ++ l2) <-> In i (merge_aux accu x)
.
Proof.
  intros accu x.
  functional induction (merge_aux accu x).
   injection 1 ; intros ; subst.
   simpl.
   unfold rev'.
   rewrite <- rev_alt.
   destruct (In_rev accu i).   
   split.
   intros.
   apply in_or_app.
   destruct (in_app_or _ _ _ H2).
   auto.
   tauto.
   intros.
   apply in_or_app.
   destruct (in_app_or _ _ _ H2).
   auto.
   tauto.

   injection 1 ; intros ; subst.
   rewrite <- app_nil_end.
   simpl.
   unfold rev'.
   rewrite <- rev_alt.
   destruct (In_rev accu i).   
   split.
   intros.
   apply in_or_app.
   destruct (in_app_or _ _ _ H2).
   auto.
   tauto.
   intros.
   apply in_or_app.
   destruct (in_app_or _ _ _ H2).
   auto.
   tauto.

   injection 1 ; intros.
   subst l2.
   subst l1.
   clear e2.
   subst.
   destruct (IHl _ _ (refl_equal _) i).
   split.
   intros.
   apply H0.
   simpl.
   destruct (in_app_or _ _ _ H2).
    right.
    apply in_or_app.
    tauto.
   destruct (in_app_or _ _ _ H3).
    destruct H4.
     tauto.
    right.
    apply in_or_app.
    right.
    apply in_or_app.
    tauto.
   destruct H4.
    tauto.
   right.
   apply in_or_app.
   right.
   apply in_or_app.
   tauto.
   intros.
   generalize (H1 H2).
   intros.
   simpl in H3.
   apply in_or_app.
   simpl.
   inversion H3.
    tauto.
   destruct (in_app_or _ _ _ H4).
    tauto.
   right.
   right.
   apply in_or_app.
   simpl.
   generalize (in_app_or _ _ _ H5).
   tauto.

   injection 1 ; intros ; subst.
   destruct (IHl _ _ (refl_equal _) i).
   simpl.
   split.
   intros.
   apply H0.
   simpl.
   destruct (in_app_or _ _ _ H2).
    right.
    apply in_or_app.
    tauto.
   destruct H3.
    tauto.
   right.
   apply in_or_app.
   tauto.
   intros.
   apply in_or_app.
   simpl.
   generalize (H1 H2).   
   simpl.
   destruct 1.
    tauto.
   destruct (in_app_or _ _ _ H3).
    tauto.
   tauto.

  injection 1 ; intros ; subst.
  destruct (IHl _ _ (refl_equal _) i).
  split.
  intros.
  apply H0.
  change 
    ((a2 :: accu) ++ (a1 :: q1) ++ q2)
    with
      (a2 :: (accu ++ (a1 :: q1) ++ q2))
      .
  rewrite <- app_ass.
  simpl.
  rewrite <- app_ass in H2.
  destruct (in_app_or _ _ _ H2).
  right.
  apply in_or_app.
  tauto.
  inversion H3.
   tauto.
  right.
  apply in_or_app.
  tauto.
  intros.
  generalize (H1 H2).
   change 
    ((a2 :: accu) ++ (a1 :: q1) ++ q2)
    with
      (a2 :: (accu ++ (a1 :: q1) ++ q2))
      .
   rewrite <- app_ass.
   rewrite <- app_ass.
   inversion 1.
    apply in_or_app.
    simpl.
    tauto.
   apply in_or_app.
   simpl.
   destruct (in_app_or _ _ _ H4).
    tauto.
   tauto.
 Qed.
   
Definition merge l1 l2 := merge_aux nil (l1, l2).

Lemma merge_prop : forall l1 l2,
  forall i, In i (l1 ++ l2) <-> In i (merge l1 l2)
.
Proof.
  unfold merge.
  intros.
  change (l1 ++ l2) with (nil ++ l1 ++ l2).
  apply merge_aux_prop.
  trivial.
Qed.

Lemma merge_intro : forall l1 l2,
  forall i, In i (l1 ++ l2) -> In i (merge l1 l2)
.
Proof.
  intros.
  destruct (merge_prop l1 l2 i).
  tauto.
Qed.

Lemma merge_elim : forall l1 l2,
  forall i, In i (merge l1 l2) -> In i (l1 ++ l2)
.
Proof.
  intros.
  destruct (merge_prop l1 l2 i).
  tauto.
Qed.

Function flatten_merge (l : list (list ident)) : list ident :=
  match l with
    | nil => nil
    | a::b => merge a (flatten_merge b)
  end.

Lemma flatten_merge_prop : forall l i,
  In i (flatten l) <-> In i (flatten_merge l)
.
Proof.
  induction l ; simpl.
   tauto.
  intro.
  destruct (IHl i).
  split.
  intros.
  apply merge_intro.
  apply in_or_app.
  generalize (in_app_or _ _ _ H1).
  destruct 1.
   tauto.
  auto.
  intros.
  apply in_or_app.
  destruct (in_app_or _ _ _  (merge_elim H1)).
   tauto.
  auto.
Qed.

Definition flatten_merge_intro l i :=
  let (h, _) := @flatten_merge_prop l i in h.


Definition flatten_merge_elim l i :=
  let (_, h) := @flatten_merge_prop l i in h.
 
Function split_aux (accu1 accu2 l : list ident) {struct l} : list ident * list ident :=
  match l with
    | nil => (accu1, accu2)
    | a :: nil => (a :: accu1, accu2)
    | a :: b :: q => split_aux (a :: accu1) (b :: accu2) q
  end.

Lemma split_aux_length_left : (forall l,
  length l >= 2 ->
  forall accu1 accu2 l1 l2,
    split_aux accu1 accu2 l = (l1, l2) ->
    length l1 < length l + length accu1)%nat.
Proof.
  induction l using (well_founded_ind (Wf_nat.well_founded_ltof _ (@length ident))).
   unfold Wf_nat.ltof in H.
  destruct l.
   simpl.
   intros.
   omegaContradiction.
  destruct l.
  simpl.
   intros.
   omegaContradiction.
  destruct l.
  simpl.
  intros.
  injection H1.
  intros ; subst.
  simpl.
  omega.
 intros.
 simpl.
 change (split_aux accu1 accu2 (i :: i0 :: i1 :: l))
   with (split_aux (i :: accu1) (i0 :: accu2) (i1 :: l))
 in H1.
 destruct l.
 simpl in H1.
 injection H1.
 intros ; subst.
 simpl.
 omega.
 assert (length (i1 :: i2 :: l) < length (i :: i0 :: i1 :: i2 :: l))%nat.
  simpl.
  omega.
 assert (length (i1 :: i2 :: l) >= 2)%nat.
  simpl.
  omega.
 generalize (H _ H2 H3 _ _ _ _ H1).
 simpl.
 omega.
Qed.


Lemma split_aux_length_right : (forall l,
  length l >= 2 ->
  forall accu1 accu2 l1 l2,
    split_aux accu1 accu2 l = (l1, l2) ->
    length l2 < length l + length accu2)%nat.
Proof.
  induction l using (well_founded_ind (Wf_nat.well_founded_ltof _ (@length ident))).
   unfold Wf_nat.ltof in H.
  destruct l.
   simpl.
   intros.
   omegaContradiction.
  destruct l.
  simpl.
   intros.
   omegaContradiction.
  destruct l.
  simpl.
  intros.
  injection H1.
  intros ; subst.
  simpl.
  omega.
 intros.
 simpl.
 change (split_aux accu1 accu2 (i :: i0 :: i1 :: l))
   with (split_aux (i :: accu1) (i0 :: accu2) (i1 :: l))
 in H1.
 destruct l.
 simpl in H1.
 injection H1.
 intros ; subst.
 simpl.
 omega.
 assert (length (i1 :: i2 :: l) < length (i :: i0 :: i1 :: i2 :: l))%nat.
  simpl.
  omega.
 assert (length (i1 :: i2 :: l) >= 2)%nat.
  simpl.
  omega.
 generalize (H _ H2 H3 _ _ _ _ H1).
 simpl.
 omega.
Qed.

Lemma split_aux_prop : forall l accu1 accu2 l1 l2,
  split_aux accu1 accu2 l = (l1, l2) ->
  forall i,
    In i (l1 ++ l2) <-> In i (accu1 ++ accu2 ++ l)
    .
Proof.
  induction l using (well_founded_ind (Wf_nat.well_founded_ltof _ (@length ident))).
  unfold Wf_nat.ltof in H.
  destruct l.
   simpl.
   injection 1 ; intros ; subst.
   rewrite <- app_nil_end.
   tauto.
  destruct l.
  simpl.
  injection 1 ; intros ; subst.
  simpl.
  rewrite <- app_ass.
  split.
  intros.
  apply in_or_app.
  simpl.
  tauto.
  intros.
  generalize (in_app_or _ _ _ H1).
  simpl.
  tauto.
  intros.
  change (
    split_aux accu1 accu2 (i :: i0 :: l) 
  ) with (
    split_aux (i :: accu1) (i0 :: accu2) l 
  ) in H0.
  assert (length l  < length (i :: i0 :: l))%nat.
  simpl.
  omega.
  destruct (H _ H1 _ _ _ _ H0 i1).
  split.
  intros.
  apply in_or_app.  
  generalize (H2 H4).
  simpl.
  destruct 1.
   subst.
   right.
   apply in_or_app.
   auto.
  destruct (in_app_or _ _ _ H5).
   tauto.
  right.
  apply in_or_app.
  simpl.
  destruct H6.
   tauto.
  generalize (in_app_or _ _ _ H6).
  tauto.
 intros.
 apply H3.
 apply in_or_app.
 simpl.
 destruct (in_app_or _ _ _ H4).
  tauto.
 destruct (in_app_or _ _ _ H5).
 right.
 right.
 apply in_or_app.
 tauto.
 destruct H6.
 tauto.
 destruct H6.
 tauto.
 right.
 right.
 apply in_or_app.
 tauto.
Qed. 

Function merge_sort (l : list ident) {measure length l} : list ident :=
  match l with
    | nil => nil
    | a :: nil => a :: nil
    | a :: b :: q =>
      let (l1, l2) := split_aux nil nil l in
        merge (merge_sort l1) (merge_sort l2)
  end.
Proof.
  intros.
  assert (length (a :: b :: q) >= 2)%nat.
   simpl.
   omega.
  generalize (split_aux_length_right H teq1).
  simpl.
  omega.
 intros.
  assert (length (a :: b :: q) >= 2)%nat.
   simpl.
   omega.
  generalize (split_aux_length_left H teq1).
  simpl.
  omega.
Qed.

Lemma merge_sort_prop : forall l i,
  In i l <-> In i (merge_sort l)
.
Proof.
  intro l.
  functional induction (merge_sort l).
   tauto.
   tauto.
   intros.
   generalize (split_aux_prop e0 i).
   intros.
   change (nil ++ nil ++ a :: b :: q) with (a :: b :: q) in H.
   destruct H.
   destruct (merge_prop (merge_sort l1) (merge_sort l2) i).
   destruct (in_app i (merge_sort l1) (merge_sort l2)).
   destruct (in_app i l1 l2).
   destruct (IHl0 i).
   destruct (IHl1 i).
   split ; tauto.
Qed.

Definition merge_sort_intro l i :=
  let (h, _) := merge_sort_prop l i in h.

Definition merge_sort_elim l i :=
  let (_, h) := merge_sort_prop l i in h.


Hypothesis Plt_strict : forall a, ~ Plt a a.

Implicit Arguments Plt_strict [].

Lemma sorted_decomp_unique : forall l,
  (forall l1 a l2 b l3, l = l1 ++ a :: l2 ++ b :: l3 -> Plt b a) ->
  forall l1 a l1',
    l = l1 ++ a :: l1' ->
    forall l2 l2',
      l = l2 ++ a :: l2' ->
      (l1, l1') = (l2, l2').
Proof.
  induction l.
   destruct l1 ; simpl ; congruence.
  intros.
  destruct l1.
   simpl in *.
   injection H0 ; intros ; subst.
   destruct l2.
    simpl in *.
    congruence.
   simpl in *.
   generalize (H (@nil _) _ _ _ _ H1).
   intros.
   injection H1 ; intros ; subst.
   destruct (Plt_strict i).
   assumption.
  destruct l2.
   simpl in *.
   injection H1 ; intros ; subst.
   generalize (H (@nil _) _ _ _ _ H0).
   intros.
   injection H0 ; intros ; subst.
   destruct (Plt_strict i).
   assumption.
  simpl in *.
  injection H0 ; intros ; subst.
  injection H1 ; intros ; subst.
  cut ((l1, l1') = (l2, l2')).
   congruence.
  eapply IHl.
  2 : reflexivity.
  2 : eexact H2.
  intros.
  eapply H.
  rewrite H3.
  change (i0 :: l0 ++ a :: l3 ++ b :: l4) with ((i0 :: l0) ++ a :: l3 ++ b :: l4).
  reflexivity.
Qed.

Lemma sorted_intro : forall l,
  (forall l1 a l2 b l3, l = l1 ++ a :: l2 ++ b :: l3 -> Plt b a) ->
  sorted (fun a b => Plt b a) l.
Proof.
  induction l.
   intros ; constructor.
  destruct l.
   intros ; constructor.
  intros.
  generalize (H (@nil _) _ (@nil _) _ l (refl_equal _)).
  intros.
  econstructor.
  assumption.
  apply IHl.
  intros.
  eapply H.
  rewrite H1.
  change (a :: l1 ++ a0 :: l2 ++ b :: l3) with ((a :: l1) ++ a0 :: l2 ++ b :: l3).
  reflexivity.
Qed.

Hypothesis  Plt_trans:
  forall (x y z: ident), Plt x y -> Plt y z -> Plt x z.

Implicit Arguments Plt_trans [].


Lemma sorted_elim : forall l,
  sorted (fun a b => Plt b a) l ->  
  (forall l1 a l2 b l3, l = l1 ++ a :: l2 ++ b :: l3 -> Plt b a)
.
Proof.
  induction 1.
   destruct l1 ; simpl ; congruence.
   destruct l1 ; try destruct l1 ; simpl ; try congruence.
   destruct l2 ; simpl ; try congruence.
  destruct l1 ; simpl.
   injection 1 ; intros ; subst.
   destruct l2 ; simpl in *.
    congruence.
   generalize (IHsorted (@nil _) _ _ _ _ H2).
   intros.
   injection H2 ; intros ; subst.
   eauto using Plt_trans.
  injection 1 ; intros ; eauto.
Qed.

Lemma sorted_join_common : forall l1 a l2,
  sorted (fun a b => Plt b a) (l1 ++ a :: nil) ->
  sorted (fun a b => Plt b a) (a :: l2) ->
  sorted (fun a b => Plt b a) (l1 ++ a :: l2)
.
Proof.
  induction l1 ; inversion 1 ; simpl.
    tauto.
   destruct l1 ; discriminate.
  destruct l1 ; simpl in *.
  injection H1 ; intros ; subst.
  constructor.
  assumption.
  assumption.
 injection H1 ; intros ; subst.
 constructor.
 assumption.
 auto.
Qed.

End Merge_sort.

Section Tag_list.

Variable A : Type.

Variable P : A -> Type.

Lemma tag_list : forall l, (forall a, In a l -> P a) -> {l' : list (sigT P) | forall a, In a l <-> exists p, In (existT _ a p) l'}.
Proof.
 induction l ; simpl.
 intros.
 exists nil ; simpl.
 split ; simpl.
  tauto.
 inversion 1.
 assumption.
 intro H.
 generalize (IHl (fun a h => H _ (or_intror _ h))).
 destruct 1 as [l' Hl'].
 generalize (H _ (or_introl _ (refl_equal _))).
 intro h.
 exists (existT _ _ h :: l').
 simpl.
 split ; simpl.
 inversion 1 as [ | Hin].
  subst ; simpl.
  exists h.
  tauto.
 destruct (Hl' a0) as [Hex _].
 destruct (Hex Hin) as [p ?].
 exists p ; eauto.
 inversion 1 as [p Hp].
 inversion Hp as [? | Hinl'].
  left ; congruence.
 generalize (Hl' a0).
 intros [_ Hin'].
 generalize (Hin' (ex_intro _ p Hinl')).
 tauto.
Qed.

End Tag_list.
  
Lemma In_dec_recip : forall (T : Type) (in_dec : forall (t : T) l, {In t l} + {~ In t l})
  (t1 t2 : T), {t1 = t2} + {t1 <> t2}.
Proof.
 intros.
 destruct (in_dec t2 (t1 :: nil)) ; simpl in * ; tauto.
Qed.

Section NoDup.

Variable A : Type.

Lemma NoDup_elim :
  forall l : _ A, NoDup l -> forall l1 x l2 l3, l = l1 ++ x :: l2 ++ x :: l3 -> False.
Proof.
  induction 1 ; simpl.
  destruct l1 ; simpl ; congruence.
  destruct l1 ; simpl.
   injection 1 ; intros ; subst.
   destruct H.
   apply in_or_app.
   simpl.
   auto.
  injection 1 ; intros ; subst.
  eauto.
Qed.

Lemma NoDup_intro : forall l : _ A,
  (forall l1 x l2 l3, l = l1 ++ x :: l2 ++ x :: l3 -> False) ->
  NoDup l.
Proof.
 induction l ; simpl.
  intros ; constructor.
 intros.
 constructor.
 intro Habs.
 destruct (In_split _ _ Habs).
 destruct H0.
 subst.
 exact (H (@nil _) _ _ _ (refl_equal _)).
 apply IHl.
 intros.
 subst.
 exact (H (_ :: _) _ _ _ (refl_equal _)).
Qed.

Lemma NoDup_app : forall l1 l2,
  NoDup (l1 ++ l2) ->
  forall x : A, In x l1 -> In x l2 -> False.
Proof.
 intros.
 destruct (In_split _ _ H0).
 destruct H2.
 subst.
 destruct (In_split _ _ H1).
 destruct H2.
 subst.
 rewrite app_ass in H.
 simpl in H.
 rewrite <- app_ass in H.
 eauto using NoDup_elim.
Qed.

Lemma NoDup_app_recip : forall l,
  (forall l1 l2, l = l1 ++ l2 -> forall x : A, In x l1 -> In x l2 -> False) ->
  NoDup l.
Proof.
  intros.
  apply NoDup_intro.
  intros ? ? ? ?.
  change (x :: l2 ++ x :: l3) with ((x :: l2) ++ x :: l3).
  rewrite <- app_ass.
  intros.
  subst.
  eapply H.
  reflexivity.
  apply in_or_app.
  right.
  simpl.
  left.
  reflexivity.
  auto.
Qed.

Lemma NoDup_norepet : forall l : _ A, NoDup l -> list_norepet l.
Proof.
 induction 1; constructor; auto.
Qed.

Lemma norepet_NoDup : forall l : _ A, list_norepet l -> NoDup l.
Proof.
  induction 1; constructor; auto.
Qed.

  
End NoDup.

Section Discr.
Variable A : Type.
Variable P : A -> Type.

Lemma in_app_discr : forall l1,
  (forall x, In x l1 -> P x -> False) ->
  forall a,
  P a ->
  forall l1',
    (forall x, In x l1' -> P x -> False) ->
    forall a', P a' ->
      forall l2 l2',
    l1 ++ a :: l2 = l1' ++ a' :: l2' ->
    (l1, a, l2) = (l1', a', l2').
Proof.
 induction l1 ; simpl.
 destruct l1' ; simpl.
  congruence.
 injection 3 ; intros ; subst.
 destruct (H0 a0).
  tauto.
  assumption.
 destruct l1' ; simpl.
  injection 3 ; intros ; subst.
  destruct (H a').
  tauto.
  assumption.
 intros.
 injection H1 ; intros ; subst.
 assert ((l1, a0, l2) = (l1', a', l2')).
  eapply IHl1. 
   eauto.
   eassumption.
   eauto.
   assumption.
   assumption.
  congruence.
Qed.

End Discr.

Section Left_include.

Variable A : Type.

Lemma left_include : forall l1' a' l2',
  (forall x : A, In x l1' -> x = a' -> False) ->
  forall l1, (In a' l1 -> False) ->
    forall l2,
      l1 ++ l2 = l1' ++ a' :: l2' ->
    exists l0, l1' = l1 ++ l0.
Proof.
 induction l1' ; simpl.
  intros ? ? _ ? ? ?.
  destruct l1 ; simpl.
  intros _ ; esplit ; reflexivity.
  injection 1 ; intros ; subst ; simpl in *.
  destruct H.
  auto.
  destruct l1 ; simpl.
   intros ; esplit ; reflexivity.
  injection 2 ; intros ; subst.
  assert (forall x, In x l1' -> x = a' -> False) by eauto.
  assert (In a' l1 -> False) by eauto.
  destruct (IHl1' _ _ H3 _ H4 _ H2).
  subst.
  esplit.
  reflexivity.
Qed.

End Left_include.

(** List ordering *)
Section List_ordering.
 Variable A : Type.

 Lemma NoDup_uniq : forall l1 (a : A) l2,
   NoDup (l1 ++ a :: l2) ->
   forall l3 l4,
     l1 ++ a :: l2 = l3 ++ a :: l4 ->
     (l1, l2) = (l3, l4).
 Proof.
   induction l1; simpl.
   inversion 1; subst.
   destruct l3; simpl.
    congruence.
   injection 1; intros; subst.
   destruct H2.
   apply in_or_app.
   auto.
   inversion 1; subst.
   destruct l3; simpl.
    injection 1; intros; subst.
    destruct H2.
    apply in_or_app.
    auto.
   injection 1; intros; subst.
   generalize (IHl1 _ _ H3 _ _ H1).
   congruence.
 Qed.


Lemma nodup_right : forall l, NoDup l ->
  forall l1 (obj : A) l1', l = l1 ++ obj :: l1' ->
  forall l2 l2', l = l2 ++ obj :: l2' ->
    l1' = l2'.
Proof.
  intros.
  subst.
  generalize (NoDup_uniq H H1).
  congruence.
Qed.

 Lemma NoDup_uniq_recip : forall l,
   (forall (a : A) l1 l2, l = l1 ++ a :: l2 -> forall l3 l4, l = l3 ++ a :: l4 -> (l1, l2) = (l3, l4)) ->
   NoDup l.
 Proof.
   induction l.
    intros; constructor.
   intros.
   constructor.
   intro.
   destruct (member_extract H0).
   destruct H1.
   subst.
   generalize (H a nil (x ++ a :: x0) (refl_equal _) (a :: x) x0 (refl_equal _)).
   congruence.
   apply IHl.
   intros.
   assert (a :: l = (a :: l1) ++ a0 :: l2).
    rewrite H0.
    reflexivity.
   assert (a :: l = (a :: l3) ++ a0 :: l4).
    rewrite H1.
    reflexivity.
   generalize (H _ _ _ H2 _ _ H3).
   congruence.
 Qed.   

 Lemma NoDup_filter : forall (f : A -> _) l a l', NoDup (l ++ a :: l') ->
   forall l2, filter f (l ++ a :: l') = a :: l2 ->
     forall x, In x l -> f x = false.
 Proof.
   induction l; simpl.
    tauto.
   inversion 1; subst.
   case_eq (f a).
    injection 2; intros until 2; subst.
    destruct H2.
    apply in_or_app.
    auto.
   inversion 3.
    congruence.
   eauto.
 Qed.  

 Definition list_lt (l : list A) (a b : A) : Prop :=
   exists l1, exists l2, exists l3,
     l = l1 ++ a :: l2 ++ b :: l3.

 Lemma list_lt_trans : forall l, NoDup l -> forall a b,
   list_lt l a b -> forall c,
     list_lt l b c ->
     list_lt l a c.
 Proof.
   destruct 2.
   destruct H0.
   destruct H0.
   destruct 1.
   destruct H1.
   destruct H1.
   subst.
   revert H H1.
   replace (x ++ a :: x0 ++ b :: x1) with ((x ++ a :: x0) ++ b :: x1).
   intros.
   generalize (NoDup_uniq H H1).
   injection 1; intros; subst.
   exists x.
   exists (x0 ++ b :: x3).
   exists x4.
   rewrite app_ass.
   rewrite app_ass.
   reflexivity.
   rewrite app_ass.
   reflexivity.
 Qed.
   
 Lemma list_lt_irrefl : forall l, NoDup l -> forall a,
   list_lt l a a -> False.
 Proof.
   destruct 2.
   destruct H0.
   destruct H0.
   subst.
   eauto using NoDup_elim.
 Qed.

 Lemma list_lt_In_left : forall l a b, list_lt l a b ->
   In a l.
 Proof.
   destruct 1.
   destruct H.
   destruct H.
   subst.
   apply in_or_app.
   auto.
 Qed.

 Lemma list_lt_In_right : forall l a b, list_lt l a b ->
   In b l.
 Proof.
   destruct 1.
   destruct H.
   destruct H.
   subst.
   apply in_or_app.
   right.
   right.
   apply in_or_app.
   auto.
 Qed.

 Lemma list_lt_app_reg_l : forall l a b,
   list_lt l a b -> forall l', list_lt (l' ++ l) a b.
 Proof.
   destruct 1.
   destruct H.
   destruct H.
   subst.
   intros.
   exists (l' ++ x).
   exists x0.
   exists x1.
   rewrite app_ass.
   reflexivity.
 Qed.

   Lemma list_lt_app_reg_r : forall l a b,
   list_lt l a b -> forall l', list_lt (l ++ l') a b.
   Proof.
     destruct 1.
     invall.
     subst.
     exists x.
     exists x0.
     exists (x1 ++ l').
     rewrite app_ass.
     simpl.
     rewrite app_ass.
     reflexivity.
   Qed.
     
   Lemma list_lt_app : forall l a,
     In a l -> forall l' a', In a' l' -> list_lt (l ++ l') a a'.
   Proof.
     intros.
     destruct (member_extract H).
     invall.
     subst.
     destruct (member_extract H0).
     invall.
     subst.
     exists x.
     exists (x0 ++ x1).
     exists x2.
     rewrite app_ass.
     rewrite app_ass.
     reflexivity.
   Qed.
       

 Hypothesis eq_dec : forall a b : A, {a = b} + {a <> b}.

 Lemma list_lt_total : forall l a, In a l -> forall b, In b l ->
   {list_lt l a b} + {list_lt l b a} + {a = b}.
 Proof.
  intros.
  destruct (eq_dec a b).
   auto.
  left.
  destruct (member_extract_dec eq_dec H).
  destruct s.
  destruct (In_dec eq_dec b x).
   right.
   destruct (member_extract i).
   destruct H1.
   exists x1.
   exists x2.
   exists x0.
   subst.
   repeat rewrite app_ass; reflexivity.
  left.
  assert (i : In b x0).
   subst.
   generalize (in_app_or _ _ _ H0).
   simpl.
   tauto.
  destruct (member_extract i).
  destruct H1.
  subst.
  exists x.
  exists x1.
  exists x2.
  reflexivity.
Qed.  

End  List_ordering.

Lemma NoDup_filter_compat : forall (A : Type) (l : _ A),
  NoDup l ->
  forall f, NoDup (filter f l).
Proof.
  induction 1; simpl.
   intros; constructor.
  intros.
  destruct (f x).
   constructor.
   intro.
   generalize (filter_In f x l).
    tauto.
   eauto.
  eauto.
Qed.

Lemma NoDup_app_intro : forall (A : Type) (l1 : _ A),
  NoDup l1 ->
  forall l2, NoDup l2 ->
    (forall x, In x l1 -> In x l2 -> False) ->
    NoDup (l1 ++ l2).
Proof.
  induction 1; subst; simpl.
   tauto.
  intros.
  constructor.
   intro.
   destruct (in_app_or _ _ _ H3).
    contradiction.
   eauto.
  eauto.
Qed.
   
Lemma NoDup_rev : forall (A : Type) (l : _ A),
  NoDup l ->
  NoDup (rev l).
Proof.
 induction 1; simpl.
  constructor.
 apply NoDup_app_intro.
 assumption.
 constructor.
  auto.
 constructor.
 simpl.
 destruct 2; try contradiction; subst.
 destruct H.
 destruct (In_rev l x0).
 auto.
Qed.

Corollary rev_NoDup : forall (A : Type) (l : _ A),
 NoDup (rev l) ->
 NoDup l.
Proof.
  intros.
  rewrite <- rev_involutive.
  eauto using NoDup_rev.
Qed.

Definition in_rev_intro := (fun (A : Type) l x => let (h, _) := In_rev (A := A) l x in h).

Definition in_rev_elim := (fun (A : Type) l x => let (_, h) := In_rev (A := A) l x in h).

Lemma NoDup_app_left : forall (A : Type) (l1 l2 : _ A),
 NoDup (l1 ++ l2) ->
 NoDup l1
.
Proof.
 intros; eauto using NoDup_norepet, list_norepet_append_left, norepet_NoDup.
Qed.

Lemma NoDup_app_right : forall (A : Type) (l1 l2 : _ A),
 NoDup (l1 ++ l2) ->
 NoDup l2
.
Proof.
 intros; eauto using NoDup_norepet, list_norepet_append_right, norepet_NoDup.
Qed.


Lemma filter_app : forall (A : Type) (l1 l2 : _ A) f,
  filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
 induction l1; simpl.
  trivial.
 intros.
 destruct (f a).
  simpl.
  f_equal.
  eauto.
 eauto.
Qed.

Lemma filter_app_recip : forall (A : Type) l (f : A -> _) l'1 l'2,
  filter f l = l'1 ++ l'2 -> exists l1, exists l2, l = l1 ++ l2 /\ filter f l1 = l'1 /\ filter f l2 = l'2.
Proof.
  induction l; simpl.
  intros.
  symmetry in H.
  destruct (app_eq_nil _ _ H).
  subst.
  exists nil.
  exists nil.
  repeat split; reflexivity.
  intros.
  case_eq (f a); intro Heq; rewrite Heq in *.
  destruct l'1.
   simpl in H; subst.
   exists nil.
   exists (a :: l).
   split.
    reflexivity.
    split.
     reflexivity.
    simpl.
    rewrite Heq.
    reflexivity.
   simpl in H.
   injection H; intros; subst.
   destruct (IHl _ _ _ H0).
   destruct H1.
   destruct H1.
   destruct H2.
   exists (a0 :: x).
   exists x0.
   subst.
   split.
   reflexivity.
   split.
   simpl.
   rewrite Heq.
   reflexivity.
   reflexivity.
  destruct (IHl _ _ _ H).
  destruct H0.
  destruct H0.
  destruct H1.
  subst.
  exists (a :: x).
  exists x0.
  split.
  reflexivity.
  split.
  simpl.
  rewrite Heq.
  reflexivity.
  reflexivity.
Qed.  

Lemma filter_commut : forall (A : Type) f1 f2 (l : _ A),
  filter f1 (filter f2 l) = filter f2 (filter f1 l).
Proof.
 induction l; simpl.
  trivial.
 case_eq (f1 a); intro Heq1; simpl; case_eq (f2 a); intro Heq2; simpl; try rewrite Heq1; try rewrite Heq2; try assumption.
 f_equal; assumption.
Qed.

Lemma filter_idem : forall (A : Type) f (l : _ A),
  filter f (filter f l) = filter f l.
Proof.
  induction l; simpl.
   trivial.
  case_eq (f a); intros; simpl.
   rewrite H.
   f_equal; assumption.
  assumption.
Qed.   

Lemma list_lt_filter_recip : forall (A : Type) (f : A -> _) l a b, list_lt (filter f l) a b -> list_lt l a b.
Proof.
 destruct 1.
 destruct H.
 destruct H.
 destruct (filter_app_recip H).
 destruct H0.
 invall.
 subst.
 change (a :: x0 ++ b :: x1) with ((a :: x0) ++ b :: x1) in H3.
 destruct (filter_app_recip H3).
 destruct H0.
 destruct H0.
 destruct H1.
 subst.
 assert (In a (filter f x)).
  rewrite H1; auto.
 assert (In b (filter f x4)).
  rewrite H2; auto.
 destruct (filter_In f a x).
 destruct (H5 H0).
 destruct (filter_In f b x4).
 destruct (H9 H4).
 destruct (member_extract H7).
 destruct H13.
 subst.
 destruct (member_extract H11).
 destruct H13.
 subst.
 exists (x2 ++ x3).
 exists (x5 ++ x).
 exists x6.
 rewrite app_ass.
 rewrite app_ass.
 rewrite app_ass.
 reflexivity.
Qed. 

Lemma list_lt_filter_aux : forall (A : Type) l a b, list_lt l a b -> forall (f : A -> _), f a = true -> f b = true -> list_lt (filter f l) a b.
Proof.
 destruct 1.
 destruct H.
 destruct H.
 intros.
 subst.
 rewrite filter_app.
 simpl.
 rewrite H0.
 rewrite filter_app.
 simpl.
 rewrite H1.
 exists (filter f x).
 exists (filter f x0).
 exists (filter f x1).
 reflexivity.
Qed.

Corollary list_lt_filter : forall (A : Type) l a b, list_lt l a b -> forall  (f : A -> _), In a (filter f l) -> In b (filter f l) -> list_lt (filter f l) a b.
Proof.
 intros.
 destruct (filter_In f a l).
 destruct (filter_In f b l).
 destruct (H2 H0).
 destruct (H4 H1).
 eauto using list_lt_filter_aux.
Qed.


(** The last element of a list *)

Section Last.

Variable A : Type.

Function (* Fixpoint *) last (l : list A) {struct l} : option A :=
  match l with
    | nil => None
    | a :: l' =>
      match l' with
        | nil => Some a
        | _ => last l'
      end
  end.

Lemma last_correct : forall l s, last l = Some s ->
  {l' | l = l' ++ s :: nil}.
Proof.
 intros l.
 functional induction (last l).
  congruence.
 injection 1 ; intros ; subst.
 exists (@nil A).
  reflexivity.
 intros.
 destruct (IHo _ H).
 subst.
 exists (a :: x).
 reflexivity.
Qed.

Lemma last_complete : forall l a, last (l ++ a :: nil) = Some a.
Proof.
 induction l ; simpl.
  trivial.
 intro.
 case_eq (l ++ a0 :: nil).
   destruct l ; simpl ; congruence.
 intros.
 rewrite <- H.
 eauto.
Qed.

Lemma last_app_left : forall l1, l1 <> nil -> forall l2,
  last (l2 ++ l1) = last l1.
Proof.
 intro.
 rewrite <- (rev_involutive l1).
 destruct (rev l1) ; simpl.
  congruence.
 intros.
 rewrite <- app_ass.
 rewrite last_complete.
 rewrite last_complete.
 reflexivity.
Qed.

Lemma last_nonempty : forall l, l <> nil -> last l <> None.
Proof.
 intro l.
 functional induction (last l) ; simpl.
  congruence.
 congruence.
 intros.
 destruct l'.
  contradiction.
 apply IHo.
 congruence.
Qed.


End Last.


(*
Extract Inductive list => "list" [ "[]" "( :: )" ].
*)

(* Recursive Extraction member_strong_list.
 this gives the identity on lists, written in a particular way *)


(* Recursive Extraction sort. *)

