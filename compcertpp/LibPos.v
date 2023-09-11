Require Export Coqlib.
Require Export ZArith.
Require Import Tactics.
Load Param.

Lemma Plt_rev_trans :forall a b,
  Plt b a ->
  forall c, Plt c b -> Plt c a.
Proof.
  intros ; eauto using Plt_trans.
Qed.

Lemma Ple_Plt_trans:
  forall (p q r: positive), Ple p q -> Plt q r -> Plt p r.
Proof.
  unfold Plt, Ple; intros; omega.
Qed.

Lemma Ple_antisym : forall p q, Ple p q -> Ple q p -> p = q.
Proof.
  unfold Ple.
  intros.
  assert (Zpos p = Zpos q) by omega.
  congruence.
Qed.



Section Bounded_gt.

Variable p : positive.

Inductive bounded_gt : positive -> positive -> Prop :=
| bounded_gt_intro : forall a b,
  Plt b a -> Plt a p -> bounded_gt a b.

Function bound_gt (q : positive) : nat :=
  match (Zpos p - Zpos q)%Z with
    | Zpos r => nat_of_P r
    | _ => O
  end.

Theorem bounded_gt_wf : well_founded bounded_gt.
Proof.
 unfold well_founded.
 cut (forall n q, bound_gt q = n -> Acc bounded_gt q).
 intros.
 eauto.
 induction n using (well_founded_ind Wf_nat.lt_wf).
 intros.
 subst.
 revert H.
 unfold bound_gt.
 case_eq (Zpos p - Zpos q)%Z.
  intros.
  assert (Zpos p = Zpos q) by omega.
  injection H1.
  intros ; subst q.
  constructor.
  inversion 1.
  subst.
  apply False_rect.
  destruct (Plt_strict p).
  eauto using Plt_trans.
 intros.
 constructor.
 inversion 1.
 subst.
 unfold Plt in *.
 assert (Zpos p > Zpos q)%Z.
 cut (Zpos p - Zpos q > 0)%Z.
 omega.
 rewrite H.
 compute.
 trivial.
 clear H4.
 assert (Zpos p - Zpos y < Zpos p - Zpos q)%Z by omega.
 assert (Zpos p - Zpos y > 0)%Z by omega.
 generalize (H5).
 case_eq (Zpos p - Zpos y)%Z ; intros until 1 ; compute ; try congruence.
 intros _.
 generalize (fun y0 Hq Hy => H0 y0 Hy y Hq).
 rewrite H6.
 intros.
 eapply H7.
 reflexivity.
apply nat_of_P_lt_Lt_compare_morphism.
 rewrite H in H4.
 rewrite H6 in H4.
 unfold Zlt in H4.
 simpl in H4.
 assumption.
 intros.
 assert (Zpos p < Zpos q)%Z.
 cut (Zpos p - Zpos q < 0)%Z.
  omega.
 rewrite H.
 compute.
 trivial.
 assert (Plt p q).
  assumption.
 constructor.
 inversion 1.
 subst.
 destruct (Plt_strict p).
 eauto using Plt_trans.
Qed.
 
End Bounded_gt.


Section Bounded_exists.
 Variable p : positive -> bool.

 Lemma bounded_exists : forall n,
   {j | Plt j n /\ p j = true} + {forall j, Plt j n -> p j = false}.
 Proof.
  intros.
  induction n using Prec.
  compute.
   right.
   destruct j ; simpl ; congruence.
  case_eq (p n).
   left.
   exists n.
   split.
   apply Plt_succ.
   assumption.
  intros.
  destruct IHn as [ [j [Hlt Hp]] | Hlt].
   left.
   exists j.
   split.
   eauto using Plt_succ, Plt_trans.
   assumption.
  right.
  intros j Hlt_succ.
  destruct (Plt_succ_inv _ _ Hlt_succ).
   eauto.
  congruence.
Qed.

End Bounded_exists. 


(* LCM *)

Definition lcm a b := a * (b / Zgcd a b).

Lemma lcm_positive : forall a, 0 < a -> forall b, 0 < b -> 0 < lcm a b.
Proof.
  intros.
  unfold lcm.
  replace 0 with (a * 0) by ring.
  apply Zmult_lt_compat_l.
   assumption.
  generalize (Zgcd_is_gcd a b).
  inversion 1.
  destruct H3.
  clear H1 H2 H4.
  assert (Zgcd a b = 0 -> False).
   intro.
   generalize (Zgcd_inv_0_r _ _ H1).
   omega.
   pattern b at 1.
  rewrite H3.
  rewrite Z_div_mult_full.
  generalize (Zgcd_is_pos a b).
  intros.
  rewrite H3 in H0.
  assert (0 < Zgcd a b) by omega.
  eauto using Zmult_lt_0_reg_r.
  assumption.
Qed.

Theorem lcm_prop : forall a, 0 < a -> forall b, 0 < b -> forall q,
  (a | q) -> (b | q) -> (lcm a b | q).
Proof.
  destruct 3; subst.
  destruct 1; subst.
  unfold lcm.
  generalize (Zgcd_is_gcd a b).
  inversion 1.
  clear H5.
  destruct H3.
  destruct H4.  
  generalize (Zgcd_is_pos a b).
  intros.
  assert (0 < Zgcd a b).
   cut (Zgcd a b = 0 -> False).
    intros.
    omega.
   intros.
   generalize (Zgcd_inv_0_l _ _ H6).
   omega.
  assert (b > 0) by omega.
  assert (Zgcd a b >= 0) by omega.
  generalize (Zis_gcd_rel_prime _ _ _ H7 H8 H2).
  revert H6 H4 H3.
  clear H2 H5 H7 H8.  
  generalize (Zgcd a b).
  intros.
  subst.
  assert (z <> 0) by omega.
  revert H2.
  replace (q2 * z / z) with q2.
  replace (q1 * z / z) with q1.
  intros.
  revert H1.
  rewrite Zmult_assoc.
  rewrite Zmult_assoc.
  intros.
  generalize (Zmult_reg_r  _ _ _ H3 H1).
  intros.
  assert (q2 | q0).
   apply Gauss with q1.
   exists q.
   rewrite Zmult_comm.
   congruence.
   apply rel_prime_sym.
   assumption.
  destruct H5. 
  subst.
  exists q3.
  ring.
  rewrite Z_div_mult_full; trivial.
  rewrite Z_div_mult_full; trivial.
Qed. 

Lemma lcm_divides_left : forall a b, (a | lcm a b).
Proof.
  unfold lcm.
  intros.
  exists (b / Zgcd a b).
  rewrite Zmult_comm.
  trivial.
Qed.

Lemma lcm_divides_right : forall a b, 0 < b -> (b | lcm a b).
Proof.
  unfold lcm.
  intros.
  assert (Zgcd a b = 0 -> False).
   intro.
   generalize (Zgcd_inv_0_r _ _ H0).
   omega.
  generalize (Zgcd_is_pos a b).
  intros.
  assert (0 < Zgcd a b) by omega.
  rewrite <- (Zgcd_div_swap0 _ _ H2 H).
  exists (a / Zgcd a b).
  trivial.
Qed. 

Lemma incr_align : forall a, (0 < a) -> forall p, {q | p <= q /\ (a | q)}.
Proof.
 intros.
 assert (J : a > 0) by omega.
 generalize (Z_div_mod p _ J).
 destruct (Zdiv_eucl p a).
 destruct 1.
 destruct (Z_eq_dec z0 0).
  exists p.
  subst.
  split.
   omega.
  exists z.
  rewrite Zmult_comm.
  omega.
 exists (p + a - z0).
 split.
  omega.
 exists (z + 1).
 subst.
 rewrite Zmult_plus_distr_l.
 rewrite Zmult_comm.
 replace (1 * a) with a by omega.
 omega.
Qed.
  
  
(* The following algorithm computes the lowest offset starting from low_bound, aligned to align, such that, if this offset is lower than high_bound, then it verifies some predicate f. *)
           
           Section Bounded.

             Variable align : Z.
             Hypothesis align_pos : 0 < align.

             Variable low_bound high_bound : Z.

             Variable f : Z -> bool.

             Definition bounded_offset : {z | low_bound <= z /\ (align | z) /\ (high_bound <= z \/ f z = true)}.
             Proof.
               cut (forall j, 0 <= j -> forall z, (align | z) -> high_bound - z = j -> {z' | z <= z' /\ (align | z') /\ (high_bound <= z' \/ f z' = true)}).
               intros.
                destruct (incr_align align_pos low_bound).
                destruct a.
                destruct (Z_le_dec 0 (high_bound - x)).
                 destruct (H _ z _ H1 (refl_equal _)).
                 destruct a.                 
                 exists x0.
                 split.
                 omega.
                 assumption.
                exists x.
                split.
                 assumption.
                split.
                 assumption.
                left.
                omega.
              intros until 1.
              pattern j.
              eapply Z_lt_rec; try eassumption.
              intros.
              clear j H.
              subst.
              case_eq (f z).
               intros.
               exists z.
               split.
               omega.
               split.
               assumption.
               auto.
              intros _.
              assert (align | z + align) by eauto using Zdivide_plus_r, Zdivide_refl.
              destruct (Z_le_dec (high_bound) (z + align)).
               exists (z + align).
               split.
               omega.              
               split.
               assumption.
               auto.
              assert (0 <= high_bound - (z + align) < high_bound - z) by omega.
              destruct (H0 _ H2 _ H (refl_equal _)).
              destruct a.
              exists x.
              split.
               omega.
              assumption.
            Qed.

          End Bounded.
