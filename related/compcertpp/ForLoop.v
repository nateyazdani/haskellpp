Require Import Coqlib.
Require Import ZArith.
Require Import Wf_Z.
Open Scope Z_scope.
Load Param.

Section ForLoop.

Variable T : Type.
Variable nop : T.

Section Up.

Variable f : Z -> T -> T.

Variable to : Z.

Inductive forup_sem : Z -> T -> Prop :=
| forup_sem_ge : forall i, to <= i -> forup_sem i nop
| forup_sem_lt : forall i, i < to -> forall y, forup_sem (i + 1) y -> forup_sem i (f i y).

Lemma forup_func : forall i y1, forup_sem i y1 -> forall y2, forup_sem i y2 -> y1 = y2.
Proof.
  induction 1; inversion 1; trivial; try omegaContradiction.
  rewrite (IHforup_sem _ H3).
  trivial.
Qed.

Definition forup_def : forall i,  {y | forup_sem i y}.
Proof.
  cut (forall j, {y | forup_sem (to - j) y}).
   intros.
   destruct (X (to - i)).
   exists x.
   replace i with (to - (to - i)) by omega.
   assumption.
  intro.
  destruct (Z_lt_le_dec j 0).
   esplit.
   eleft.
   omega.
  revert j z.
  eapply Z_lt_rec.
  intros.
  destruct (Z_lt_le_dec (x-1) 0).
   esplit.
   eleft.
   omega.
  assert (0 <= x-1 < x) by omega.
  destruct (X _ H).
  replace (to - (x - 1)) with (to - x + 1) in f0 by omega.
   esplit.
   eright.
   omega.
   eassumption.
Qed.

Definition forup z := let (x, _) := forup_def z in x.

Lemma forup_ge : forall z, to <= z -> forup z = nop.
Proof.
  unfold forup.
  intro.
  destruct forup_def.
  inversion f0.
  trivial.
  intros; omegaContradiction.
Qed.

Lemma forup_lt : forall z, z < to -> forup z = f z (forup (z+1)).
Proof.
  unfold forup.
  intros until 1.
  destruct (forup_def z).
  inversion f0; try omegaContradiction.
  destruct (forup_def (z+1)).
  generalize (forup_func H1 f1).
  congruence.
Qed.

End Up.

Section Down.

Variable f : Z -> T -> T.
Variable to : Z.

Definition fordown z := forup (fun j => f (- j)) (- to) (- z).

Lemma fordown_le : forall z, z <= to -> fordown z = nop.
Proof.
  unfold fordown.
  intros.
  assert (-to <= -z) by omega.
  eauto using forup_ge.
Qed.

Lemma fordown_gt : forall z, to < z -> fordown z = f z (fordown (z-1)).
Proof.
  unfold fordown.
  intros.
  assert (-z < -to) by omega.
  rewrite (forup_lt _ H0).
  replace (- - z) with z by omega.
  replace (- (z-1)) with ((-z) + 1) by omega.
  trivial.
Qed.


End Down.

End ForLoop. 

Opaque forup fordown.
