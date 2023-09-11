Require Import ZArith.
Require Import List.
Load Param.

Section Injection_with_decode.

Variables A B : Type.
Hypothesis encode : A -> B.
Hypothesis decode : B -> A.
Hypothesis decode_encode_id : forall a : A, decode (encode a) = a.

Lemma encode_inj_with_decode : forall a1 a2, encode a1 = encode a2 -> a1 = a2.
Proof.
 intros.
 rewrite <- (decode_encode_id a1).
 rewrite <- (decode_encode_id a2).
 congruence.
Qed.

End Injection_with_decode.

Lemma inj_comp : forall (A B : Type) (fab : A -> B) (fab_inj : forall a1 a2, fab a1 = fab a2 -> a1 = a2) (C : Type) (fbc : B -> C) (fbc_inj : forall b1 b2, fbc b1 = fbc b2 -> b1 = b2) a1 a2, fbc (fab a1) = fbc (fab a2) -> a1 = a2.
Proof.
  intros; eauto.
Qed.
  
Function bits_of_pos (p : positive) {struct p} : list bool :=
  match p with
    | xH => nil
    | xO p' => false :: bits_of_pos p'
    | xI p' => true :: bits_of_pos p'
  end.

Function pos_of_bits (l : list bool) {struct l} : positive :=
  match l with
    | nil => xH
    | false :: l' => xO (pos_of_bits l')
    | true :: l' => xI (pos_of_bits l')
  end.

Lemma bits_of_pos_of_bits : forall l, bits_of_pos (pos_of_bits l) = l.
Proof.
  induction l; simpl; trivial.
  destruct a; simpl; rewrite IHl; trivial.
Qed.

Lemma pos_of_bits_of_pos : forall p, pos_of_bits (bits_of_pos p) = p.
Proof.
  induction p; simpl; trivial; rewrite IHp; trivial.
Qed.

Function encode_couple_bool_aux (l1 l2 : list bool) {struct l1} : list bool :=
  match l1 with
    | nil => false :: true :: l2
    | b1 :: l1' =>
      match l2 with
        | nil => false :: false :: l1
        | b2 :: l2' => true :: b1 :: b2 :: encode_couple_bool_aux l1' l2'
      end
  end.

Definition encode_couple_bool (c : list bool * list bool) :=
  let (l1, l2) := c in encode_couple_bool_aux l1 l2.

Function decode_couple_bool (l : list bool) {struct l} : list bool * list bool :=
  match l with
    | true :: b1 :: b2 :: l' =>
      let (l1, l2) := decode_couple_bool l' in
        (b1 :: l1, b2 :: l2)
    | false :: false :: l1 => (l1, nil)
    | false :: true :: l2 => (nil, l2)
    | _ => (nil, nil) (** garbage *)
  end.

Lemma decode_encode_couple_bool : forall c, decode_couple_bool (encode_couple_bool c) = c.
Proof.
destruct c.
revert l0.
unfold encode_couple_bool.
induction l; simpl; trivial.
destruct l0; simpl; trivial.
rewrite IHl; trivial. 
Qed.

Definition encode_couple_pos (c : _ * _) :=
  let (l1, l2) := c in
    pos_of_bits (encode_couple_bool (bits_of_pos l1, bits_of_pos l2)).

Lemma encode_couple_pos_inj : forall c1 c2, encode_couple_pos c1 = encode_couple_pos c2 ->
  c1 = c2.
Proof.
  unfold encode_couple_pos.
  destruct c1.
  destruct c2.
  intros.
  generalize (encode_inj_with_decode bits_of_pos_of_bits H).
  intros.
  generalize (encode_inj_with_decode decode_encode_couple_bool H0).
  injection 1; intros.
  rewrite (encode_inj_with_decode pos_of_bits_of_pos H2).
  rewrite (encode_inj_with_decode pos_of_bits_of_pos H3).
  trivial.
Qed.

Lemma encode_couple_pos_never_xH : forall c, encode_couple_pos c <> xH.
Proof.
  destruct c.
  unfold encode_couple_pos.
  destruct p; simpl; try congruence;
   destruct p0; simpl; congruence.
Qed.

Section Encode_couple.

  Variable A : Type.
  Variable encodeA : A -> positive.
  Hypothesis encodeA_inj : forall a1 a2, encodeA a1 = encodeA a2 -> a1 = a2.
  Variable B : Type.
  Variable encodeB : B -> positive.
  Hypothesis encodeB_inj : forall b1 b2, encodeB b1 = encodeB b2 -> b1 = b2.

  Definition encode_couple (c : _ * _) :=
    let (a, b) := c in
      encode_couple_pos (encodeA a, encodeB b).

  Lemma encode_couple_inj : forall c1 c2, encode_couple c1 = encode_couple c2 -> c1 = c2.
  Proof.
    unfold encode_couple.
    destruct c1.
    destruct c2.
    intros.
    generalize (encode_couple_pos_inj H).
    injection 1; intros.
    rewrite (encodeA_inj H2).
    rewrite (encodeB_inj H1).
    trivial.
  Qed.

End Encode_couple.

Section Encode_list.

  Variable A : Type.
  Variable encode : A -> positive.

Function encode_list (l : list A) {struct l} : positive :=
  match l with
    | nil => xH
    | p :: l' => encode_couple_pos (encode p, encode_list l')
  end.

Hypothesis encode_inj : forall a1 a2, encode a1 = encode a2 -> a1 = a2.

Lemma encode_list_inj : forall l1 l2,
  encode_list l1 = encode_list l2 ->
  l1 = l2.
Proof.
  Opaque encode_couple_pos.
  induction l1; simpl.
   destruct l2; simpl; trivial.
   intros.
   symmetry in H.
   destruct (encode_couple_pos_never_xH H).
  destruct l2; simpl.
   intro.
   destruct (encode_couple_pos_never_xH H).
  intro.
  generalize (encode_couple_pos_inj H).
  injection 1; intros; subst.
  rewrite (encode_inj H2).
  rewrite (IHl1 _ H1).
  trivial.
Qed.

End Encode_list.

Section Identity.
Variable A : Type.
Definition id (a : A) := a.
Lemma id_inj : forall a1 a2, id a1 = id a2 -> a1 = a2.
Proof.
unfold id; tauto.
Qed.
End Identity.


