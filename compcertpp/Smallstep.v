(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Tools for small-step operational semantics *)

(** This module defines generic operations and theorems over
  the one-step transition relations that are used to specify
  operational semantics in small-step style. *)

Require Import Wf.
Require Import Wf_nat.
Require Import Classical.
Require Import Coqlib.
Require Import Events.

Set Implicit Arguments.

(** * Closures of transitions relations *)

Section SmallStep.

Variable ev : tr.

Notation trace := (trace ev).
Notation traceinf := (traceinf ev).
Notation outcome := (outcome ev).

Hypothesis evsem : trsem ev.

Section CLOSURES.

Variable state: Type.

(** A one-step transition relation has the following signature.
  It is parameterized by a global environment, which does not
  change during the transition.  It relates the initial state
  of the transition with its final state.  The [trace] parameter
  captures the observable events possibly generated during the
  transition. *)

Variable step: state -> trace -> state -> Prop.

(** No transitions: stuck state *)

Definition nostep (s: state) : Prop :=
  forall t s', ~(step s t s').

(** Zero, one or several transitions.  Also known as Kleene closure,
    or reflexive transitive closure. *)

Inductive star : state -> trace -> state -> Prop :=
  | star_refl: forall s,
      star s E0 s
  | star_step: forall s1 t1 s2 t2 s3 t,
      step s1 t1 s2 -> star s2 t2 s3 -> t = t1 ** t2 ->
      star s1 t s3.

Lemma star_one:
  forall s1 t s2, step  s1 t s2 -> star  s1 t s2.
Proof.
  intros. eapply star_step; eauto. apply star_refl. rewrite E0_right; auto.
Qed.

Lemma star_trans:
  forall  s1 t1 s2, star  s1 t1 s2 ->
  forall t2 s3 t, star s2 t2 s3 -> t = t1 ** t2 -> star s1 t s3.
Proof.
  induction 1; intros.  
  rewrite H0. rewrite E0_left; auto.
  eapply star_step; eauto. rewrite <- Eapp_assoc. congruence. assumption.
Qed.

Lemma star_left:
  forall s1 t1 s2 t2 s3 t,
  step s1 t1 s2 -> star  s2 t2 s3 -> t = t1 ** t2 ->
  star  s1 t s3.
Proof star_step.

Lemma star_right:
  forall  s1 t1 s2 t2 s3 t,
  star  s1 t1 s2 -> step  s2 t2 s3 -> t = t1 ** t2 ->
  star  s1 t s3.
Proof.
  intros. eapply star_trans. eauto. apply star_one. eauto. auto.
Qed.

Section Invariant.

Variable P : state -> Prop.

Hypothesis HP : forall  s, P  s -> forall t s', step  s t s' -> P  s'.

Lemma star_invariant : forall  s, P  s -> forall t s', star  s t s' -> P  s'.
Proof.
  intros.
  revert H.
  induction H0; eauto.
Qed.

End Invariant.

(** One or several transitions.  Also known as the transitive closure. *)

Inductive plus: state -> trace -> state -> Prop :=
  | plus_left: forall s1 t1 s2 t2 s3 t,
      step  s1 t1 s2 -> star s2 t2 s3 -> t = t1 ** t2 ->
      plus s1 t s3.

Lemma plus_one:
  forall s1 t s2,
  step s1 t s2 -> plus s1 t s2.
Proof.
  intros. econstructor; eauto. apply star_refl. rewrite E0_right; auto.
Qed.

Lemma plus_star:
  forall s1 t s2, plus s1 t s2 -> star s1 t s2.
Proof.
  intros. inversion H; subst.
  eapply star_step; eauto. 
Qed.

Lemma plus_right:
  forall s1 t1 s2 t2 s3 t,
  star s1 t1 s2 -> step s2 t2 s3 -> t = t1 ** t2 ->
  plus s1 t s3.
Proof.
  intros. inversion H; subst. rewrite E0_left; auto. apply plus_one. auto.
  rewrite Eapp_assoc; auto. eapply plus_left; eauto.
  eapply star_right; eauto. 
Qed.

Lemma plus_left':
  forall s1 t1 s2 t2 s3 t,
  step s1 t1 s2 -> plus s2 t2 s3 -> t = t1 ** t2 ->
  plus s1 t s3.
Proof.
  intros. eapply plus_left; eauto. apply plus_star; auto.
Qed.

Lemma plus_right':
  forall s1 t1 s2 t2 s3 t,
  plus s1 t1 s2 -> step s2 t2 s3 -> t = t1 ** t2 ->
  plus s1 t s3.
Proof.
  intros. eapply plus_right; eauto. apply plus_star; auto.
Qed.

Lemma plus_star_trans:
  forall s1 t1 s2 t2 s3 t,
  plus s1 t1 s2 -> star s2 t2 s3 -> t = t1 ** t2 -> plus s1 t s3.
Proof.
  intros. inversion H; subst. 
  econstructor; eauto. eapply star_trans; eauto.
  rewrite Eapp_assoc; auto.
Qed.

Lemma star_plus_trans:
  forall s1 t1 s2 t2 s3 t,
  star s1 t1 s2 -> plus s2 t2 s3 -> t = t1 ** t2 -> plus s1 t s3.
Proof.
  intros. inversion H; subst.
  rewrite E0_left; auto.
  rewrite Eapp_assoc; auto.
  econstructor. eauto. eapply star_trans. eauto. 
  apply plus_star. eauto. eauto. auto.
Qed.

Lemma plus_trans:
  forall s1 t1 s2 t2 s3 t,
  plus s1 t1 s2 -> plus s2 t2 s3 -> t = t1 ** t2 -> plus s1 t s3.
Proof.
  intros. eapply plus_star_trans. eauto. apply plus_star. eauto. auto.
Qed.

Lemma plus_inv:
  forall s1 t s2, 
  plus s1 t s2 ->
  step s1 t s2 \/ exists s', exists t1, exists t2, step s1 t1 s' /\ plus s' t2 s2 /\ t = t1 ** t2.
Proof.
  intros. inversion H; subst. inversion H1; subst.
  left. rewrite E0_right; auto.
  right. exists s3; exists t1; exists (t0 ** t3); split. auto.
  split. econstructor; eauto. auto.
Qed.

Lemma star_inv:
  forall s1 t s2,
  star s1 t s2 ->
  (s2 = s1 /\ t = E0) \/ plus s1 t s2.
Proof.
  intros. inv H. left; auto. right; econstructor; eauto.
Qed.

(** Infinitely many transitions *)

CoInductive forever : state -> traceinf -> Prop :=
  | forever_intro: forall s1 t s2 T,
      step s1 t s2 -> forever s2 T ->
      forever s1 (t *** T).

Lemma star_forever:
  forall s1 t s2, star s1 t s2 ->
  forall T, forever s2 T ->
  forever s1 (t *** T).
Proof.
  induction 1; intros. rewrite E0_left_inf; auto.
  subst t. rewrite Eappinf_assoc; auto.
  econstructor; eauto.
Qed.  

(** An alternate, equivalent definition of [forever] that is useful
    for coinductive reasoning. *)

Variable A: Type.
Variable order: A -> A -> Prop.

CoInductive forever_N  : A -> state -> traceinf -> Prop :=
  | forever_N_star: forall s1 t s2 a1 a2 T1 T2,
      star s1 t s2 -> 
      order a2 a1 ->
      forever_N a2 s2 T2 ->
      T1 = t *** T2 ->
      forever_N a1 s1 T1
  | forever_N_plus: forall s1 t s2 a1 a2 T1 T2,
      plus s1 t s2 ->
      forever_N a2 s2 T2 ->
      T1 = t *** T2 ->
      forever_N a1 s1 T1.

Hypothesis order_wf: well_founded order.

Lemma forever_N_inv:
  forall a s T,
  forever_N a s T ->
  exists t, exists s', exists a', exists T',
  step s t s' /\ forever_N a' s' T' /\ T = t *** T'.
Proof.
  intros a0. pattern a0. apply (well_founded_ind order_wf).
  intros. inv H0.
  (* star case *)
  inv H1.
  (* no transition *)
  rewrite E0_left_inf; auto.
  apply H with a2. auto. auto. 
  (* at least one transition *)
  exists t1; exists s0; exists x; exists (t2 *** T2).
  split. auto. split. eapply forever_N_star; eauto.
  apply Eappinf_assoc; auto.
  (* plus case *)
  inv H1.
  exists t1; exists s0; exists a2; exists (t2 *** T2).
  split. auto.
  split. inv H3. rewrite E0_left_inf; auto.  
  eapply forever_N_plus. econstructor; eauto. eauto. auto.
  apply Eappinf_assoc; auto.
Qed.

Lemma forever_N_forever:
  forall a s T, forever_N a s T -> forever s T.
Proof.
  cofix COINDHYP; intros.
  destruct (forever_N_inv H) as [t [s' [a' [T' [P [Q R]]]]]].
  rewrite R. apply forever_intro with s'. auto. 
  apply COINDHYP with a'; auto.
Qed.

(** Yet another alternative definition of [forever]. *)

CoInductive forever_plus  : state -> traceinf -> Prop :=
  | forever_plus_intro: forall s1 t s2 T1 T2,
      plus s1 t s2 -> 
      forever_plus s2 T2 ->
      T1 = t *** T2 ->
      forever_plus s1 T1.

Lemma forever_plus_inv:
  forall s T,
  forever_plus s T ->
  exists s', exists t, exists T',
  step s t s' /\ forever_plus s' T' /\ T = t *** T'.
Proof.
  intros. inv H. inv H0. exists s0; exists t1; exists (t2 *** T2).
  split. auto.
  split. exploit star_inv; eauto. intros [[P Q] | R]. 
    subst. rewrite E0_left_inf; auto. econstructor; eauto. 
  apply Eappinf_assoc; auto.
Qed.

Lemma forever_plus_forever:
  forall s T, forever_plus s T -> forever s T.
Proof.
  cofix COINDHYP; intros.
  destruct (forever_plus_inv H) as [s' [t [T' [P [Q R]]]]].
  subst. econstructor; eauto.
Qed.

(** Infinitely many silent transitions *)

CoInductive forever_silent : state -> Prop :=
  | forever_silent_intro: forall s1 s2,
      step s1 E0 s2 -> forever_silent s2 ->
      forever_silent s1.

(** An alternate definition. *)

CoInductive forever_silent_N  : A -> state -> Prop :=
  | forever_silent_N_star: forall s1 s2 a1 a2,
      star s1 E0 s2 -> 
      order a2 a1 ->
      forever_silent_N a2 s2 ->
      forever_silent_N a1 s1
  | forever_silent_N_plus: forall s1 s2 a1 a2,
      plus s1 E0 s2 ->
      forever_silent_N a2 s2 ->
      forever_silent_N a1 s1.

Lemma forever_silent_N_inv:
  forall a s,
  forever_silent_N a s ->
  exists s', exists a',
  step s E0 s' /\ forever_silent_N a' s'.
Proof.
  intros a0. pattern a0. apply (well_founded_ind order_wf).
  intros. inv H0.
  (* star case *)
  inv H1.
  (* no transition *)
  apply H with a2. auto. auto. 
  (* at least one transition *)
  exploit Eapp_E0_inv; eauto. intros [P Q]. subst. 
  exists s0; exists x.
  split. auto. eapply forever_silent_N_star; eauto.
  (* plus case *)
  inv H1. exploit Eapp_E0_inv; eauto. intros [P Q]. subst. 
  exists s0; exists a2.
  split. auto. inv H3. auto.  
  eapply forever_silent_N_plus. econstructor; eauto. eauto.
Qed.

Lemma forever_silent_N_forever:
  forall a s, forever_silent_N a s -> forever_silent s.
Proof.
  cofix COINDHYP; intros.
  destruct (forever_silent_N_inv H) as [s' [a' [P Q]]].
  apply forever_silent_intro with s'. auto. 
  apply COINDHYP with a'; auto.
Qed.

(** Infinitely many non-silent transitions *)

CoInductive forever_reactive : state -> traceinf -> Prop :=
  | forever_reactive_intro: forall s1 s2 t T,
      star s1 t s2 -> t <> E0 -> forever_reactive s2 T ->
      forever_reactive s1 (t *** T).

Lemma star_forever_reactive:
  forall s1 t s2 T,
  star s1 t s2 -> forever_reactive s2 T ->
  forever_reactive s1 (t *** T).
Proof.
  intros. inv H0. rewrite <- Eappinf_assoc. econstructor. 
  eapply star_trans; eauto. 
  red; intro. exploit Eapp_E0_inv; eauto. intros [P Q]. contradiction.
  auto. auto.
Qed.

(** * Outcomes for program executions *)

(** The four possible outcomes for the execution of a program:
- Termination, with a finite trace of observable events
  and an integer value that stands for the process exit code
  (the return value of the main function).
- Divergence with a finite trace of observable events.
  (At some point, the program runs forever without doing any I/O.)
- Reactive divergence with an infinite trace of observable events.
  (The program performs infinitely many I/O operations separated
   by finite amounts of internal computations.)
- Going wrong, with a finite trace of observable events
  performed before the program gets stuck.
*)

Inductive program_behavior: Type :=
  | Terminates: trace -> outcome -> program_behavior
  | Diverges: trace -> program_behavior
  | Reacts: traceinf -> program_behavior
  | Goes_wrong: trace -> program_behavior.

Definition not_wrong (beh: program_behavior) : Prop :=
  match beh with
  | Terminates _ _ => True
  | Diverges _ => True
  | Reacts _ => True
  | Goes_wrong _ => False
  end.

(** Given a characterization of initial states and final states,
  [program_behaves] relates a program behaviour with the 
  sequences of transitions that can be taken from an initial state
  to a final state. *)

Variable initial_state: state -> Prop.
Variable final_state: state -> outcome -> Prop.

Inductive program_behaves : program_behavior -> Prop :=
  | program_terminates: forall s t s' r,
      initial_state s ->
      star s t s' ->
      final_state s' r ->
      program_behaves (Terminates t r)
  | program_diverges: forall s t s',
      initial_state s ->
      star s t s' -> forever_silent s' ->
      program_behaves (Diverges t)
  | program_reacts: forall s T,
      initial_state s ->
      forever_reactive s T ->
      program_behaves (Reacts T)
  | program_goes_wrong: forall s t s',
      initial_state s ->
      star s t s' ->
      nostep s' ->
      (forall r, ~final_state s' r) ->
      program_behaves (Goes_wrong t)
  | program_goes_initially_wrong:
      (forall s, ~initial_state s) ->
      program_behaves (Goes_wrong E0).

End CLOSURES.

(** * Simulations between two small-step semantics. *)

(** In this section, we show that if two transition relations 
  satisfy certain simulation diagrams, then every program behaviour
  generated by the first transition relation can also occur
  with the second transition relation. *)

Section SIMULATION.

(** The first small-step semantics is axiomatized as follows. *)

Variable state1: Type.
Variable step1: state1 -> trace -> state1 -> Prop.
Variable initial_state1: state1 -> Prop.
Variable final_state1: state1 -> outcome -> Prop.

(** The second small-step semantics is also axiomatized. *)

Variable state2: Type.
Variable step2: state2 -> trace -> state2 -> Prop.
Variable initial_state2: state2 -> Prop.
Variable final_state2: state2 -> outcome -> Prop.

(** We assume given a matching relation between states of both semantics.
  This matching relation must be compatible with initial states
  and with final states. *)

Variable match_states: state1 -> state2 -> Prop.

(** More generalized hypotheses than in CompCert *)

Hypothesis match_initial_states : forall st1, initial_state1 st1 ->
  exists st2, initial_state2 st2 /\
    exists st2', star step2 st2 E0 st2' /\
      match_states st1 st2'.

Hypothesis match_final_states:
  forall st1 st2 r,
  match_states st1 st2 ->
  final_state1 st1 r ->
  exists st2', star step2 st2 E0 st2' /\
    final_state2 st2' r.


(** Simulation when one transition in the first program
    corresponds to zero, one or several transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_STAR_WF.

(** [order] is a well-founded ordering associated with states
  of the first semantics.  Stuttering steps must correspond
  to states that decrease w.r.t. [order]. *)

Variable order: state1 -> state1 -> Prop.
Hypothesis order_wf: well_founded order.

Hypothesis simulation:
  forall st1 t st1', step1 st1 t st1' ->
  forall st2, match_states st1 st2 ->
  exists st2',
  (plus step2 st2 t st2' \/ (star step2 st2 t st2' /\ order st1' st1))
  /\ match_states st1' st2'.

Lemma simulation_star_star:
  forall st1 t st1', star step1 st1 t st1' ->
  forall st2, match_states st1 st2 ->
  exists st2', star step2 st2 t st2' /\ match_states st1' st2'.
Proof.
  induction 1; intros.
  exists st2; split. apply star_refl. auto.
  destruct (simulation H H2) as [st2' [A B]].
  destruct (IHstar _ B) as [st3' [C D]].
  exists st3'; split; auto.
  apply star_trans with t1 st2' t2; auto. 
  destruct A as [F | [F G]].
  apply plus_star; auto.
  auto.
Qed.

Lemma simulation_star_forever_silent:
  forall st1 st2,
  forever_silent step1 st1 -> match_states st1 st2 ->
  forever_silent step2 st2.
Proof.
  assert (forall st1 st2,
    forever_silent step1 st1 -> match_states st1 st2 ->
    forever_silent_N step2 order st1 st2).
  cofix COINDHYP; intros.
  inversion H; subst.
  destruct (simulation H1 H0) as [st2' [A B]].
  destruct A as [C | [C D]].
  apply forever_silent_N_plus with st2' s2.
  auto. apply COINDHYP. assumption. assumption.
  apply forever_silent_N_star with st2' s2.
  auto. auto. apply COINDHYP. assumption. auto.
  intros. eapply forever_silent_N_forever; eauto.
Qed.

Lemma simulation_star_forever_reactive:
  forall st1 st2 T,
  forever_reactive step1 st1 T -> match_states st1 st2 ->
  forever_reactive step2 st2 T.
Proof.
  cofix COINDHYP; intros.
  inv H. 
  destruct (simulation_star_star H1 H0) as [st2' [A B]].
  econstructor. eexact A. auto. 
  eapply COINDHYP. eauto. auto. 
Qed.

Lemma simulation_star_wf_preservation:
  forall beh,
  not_wrong beh ->
  program_behaves step1 initial_state1 final_state1 beh ->
  program_behaves step2 initial_state2 final_state2 beh.
Proof.
  intros. inv H0; simpl in H. 
  destruct (match_initial_states H1) as [s2i [A [s2 [B' B]]]].
  destruct (simulation_star_star H2 B) as [s2'f [C D]].
  destruct (match_final_states D H3) as [s2' [D'1 D'2]].
  econstructor.
   eassumption.
   eapply star_trans.
   eassumption.
   eapply star_trans.
   eassumption.
   eassumption.
   reflexivity.
   rewrite E0_left; auto.
   rewrite E0_right; auto.
   assumption.
  destruct (match_initial_states H1) as [s2i [A [s2 [B' B]]]].
  destruct (simulation_star_star H2 B) as [s2' [C D]].
  econstructor.
   eassumption.
   eapply star_trans.
   eassumption.
   eassumption.
   rewrite E0_left; auto.
  eapply simulation_star_forever_silent; eauto.
  destruct (match_initial_states H1) as [s2i [A [s2 [B' B]]]].
  econstructor.
   eassumption.
   replace T with (E0 *** T).
   eapply star_forever_reactive.
   eassumption.
   eapply simulation_star_forever_reactive; eauto.
  rewrite E0_left_inf; auto.
  contradiction.
  contradiction.
Qed.

End SIMULATION_STAR_WF.

Section SIMULATION_STAR.

(** We now consider the case where we have a nonnegative integer measure
  associated with states of the first semantics.  It must decrease when we take 
  a stuttering step. *)

Variable measure: state1 -> nat.

Hypothesis simulation:
  forall st1 t st1', step1 st1 t st1' ->
  forall st2, match_states st1 st2 ->
  (exists st2', plus step2 st2 t st2' /\ match_states st1' st2')
  \/ (measure st1' < measure st1 /\ t = E0 /\ match_states st1' st2)%nat.

Lemma simulation_star_preservation:
  forall beh,
  not_wrong beh ->
  program_behaves step1 initial_state1 final_state1 beh ->
  program_behaves step2 initial_state2 final_state2 beh.
Proof.
  intros.
  apply simulation_star_wf_preservation with (ltof _ measure).
  apply well_founded_ltof. intros.
  destruct (simulation H1 H2) as [[st2' [A B]] | [A [B C]]].
  exists st2'; auto.
  exists st2; split. right; split. rewrite B. apply star_refl. auto. auto.
  auto. auto.
Qed.

End SIMULATION_STAR.

(** Lock-step simulation: each transition in the first semantics
    corresponds to exactly one transition in the second semantics. *)

Section SIMULATION_STEP.

Hypothesis simulation:
  forall st1 t st1', step1 st1 t st1' ->
  forall st2, match_states st1 st2 ->
  exists st2', step2 st2 t st2' /\ match_states st1' st2'.

Lemma simulation_step_preservation:
  forall beh,
  not_wrong beh ->
  program_behaves step1 initial_state1 final_state1 beh ->
  program_behaves step2 initial_state2 final_state2 beh.
Proof.
  intros.
  pose (measure := fun (st: state1) => 0%nat).
  assert (simulation':
  forall st1 t st1', step1 st1 t st1' ->
  forall st2, match_states st1 st2 ->
  (exists st2', plus step2 st2 t st2' /\ match_states st1' st2')
  \/ (measure st1' < measure st1 /\ t = E0 /\ match_states st1' st2)%nat).
  intros. destruct (simulation H1 H2) as [st2' [A B]].
  left; exists st2'; split. apply plus_one; auto. auto.
  eapply simulation_star_preservation; eauto.
Qed.

End SIMULATION_STEP.

(** Simulation when one transition in the first program corresponds
    to one or several transitions in the second program. *)

Section SIMULATION_PLUS.

Hypothesis simulation:
  forall st1 t st1', step1 st1 t st1' ->
  forall st2, match_states st1 st2 ->
  exists st2', plus step2 st2 t st2' /\ match_states st1' st2'.

Lemma simulation_plus_preservation:
  forall beh,
  not_wrong beh ->
  program_behaves step1 initial_state1 final_state1 beh ->
  program_behaves step2 initial_state2 final_state2 beh.
Proof.
  intros.
  pose (measure := fun (st: state1) => 0%nat).
  assert (simulation':
  forall st1 t st1', step1 st1 t st1' ->
  forall st2, match_states st1 st2 ->
  (exists st2', plus step2 st2 t st2' /\ match_states st1' st2')
  \/ (measure st1' < measure st1 /\ t = E0 /\ match_states st1' st2)%nat).
  intros. destruct (simulation H1 H2) as [st2' [A B]].
  left; exists st2'; auto.
  eapply simulation_star_preservation; eauto.
Qed.

End SIMULATION_PLUS.

(** Simulation when one transition in the first program
    corresponds to zero or one transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_OPT.

Variable measure: state1 -> nat.

Hypothesis simulation:
  forall st1 t st1', step1 st1 t st1' ->
  forall st2, match_states st1 st2 ->
  (exists st2', step2 st2 t st2' /\ match_states st1' st2')
  \/ (measure st1' < measure st1 /\ t = E0 /\ match_states st1' st2)%nat.

Lemma simulation_opt_preservation:
  forall beh,
  not_wrong beh ->
  program_behaves step1 initial_state1 final_state1 beh ->
  program_behaves step2 initial_state2 final_state2 beh.
Proof.
  assert (simulation':
    forall st1 t st1', step1 st1 t st1' ->
    forall st2, match_states st1 st2 ->
    (exists st2', plus step2 st2 t st2' /\ match_states st1' st2')
    \/ (measure st1' < measure st1 /\ t = E0 /\ match_states st1' st2)%nat).
  intros. elim (simulation H H0). 
  intros [st2' [A B]]. left. exists st2'; split. apply plus_one; auto. auto.
  intros [A [B C]]. right. intuition.
  intros. eapply simulation_star_preservation; eauto.
Qed.

End SIMULATION_OPT.

End SIMULATION.

(** * Additional results about infinite reduction sequences *)

(** We now show that any infinite sequence of reductions is either of
  the "reactive" kind or of the "silent" kind (after a finite number
  of non-silent transitions).  The proof necessitates the axiom of
  excluded middle.  This result is used in [Csem] and [Cminor] to
  relate the coinductive big-step semantics for divergence with the
  small-step notions of divergence. *)

Require Import Classical.
Unset Implicit Arguments.

Section INF_SEQ_DECOMP.

Variable state: Type.
Variable step: state -> trace -> state -> Prop.

Inductive State: Type :=
  ST: forall (s: state) (T: traceinf), forever step s T -> State.

Definition state_of_State (S: State): state :=
  match S with ST s T F => s end.
Definition traceinf_of_State (S: State) : traceinf :=
  match S with ST s T F => T end.

Inductive Step: trace -> State -> State -> Prop :=
  | Step_intro: forall s1 t T s2 S F,
      Step t (ST s1 (t *** T) (@forever_intro state step s1 t s2 T S F))
             (ST s2 T F).

Inductive Steps: State -> State -> Prop :=
  | Steps_refl: forall S, Steps S S
  | Steps_left: forall t S1 S2 S3, Step t S1 S2 -> Steps S2 S3 -> Steps S1 S3.

Remark Steps_trans:
  forall S1 S2, Steps S1 S2 -> forall S3, Steps S2 S3 -> Steps S1 S3.
Proof.
  induction 1; intros. auto. econstructor; eauto.
Qed.

Let Reactive (S: State) : Prop :=
  forall S1, 
  Steps S S1 ->
  exists S2, exists S3, exists t, Steps S1 S2 /\ Step t S2 S3 /\ t <> E0.

Let Silent (S: State) : Prop :=
  forall S1 t S2, Steps S S1 -> Step t S1 S2 -> t = E0.

Lemma Reactive_or_Silent:
  forall S, Reactive S \/ (exists S', Steps S S' /\ Silent S').
Proof.
  intros. destruct (classic (exists S', Steps S S' /\ Silent S')).
  auto.
  left. red; intros. 
  generalize (not_ex_all_not _ _ H S1). intros.
  destruct (not_and_or _ _ H1). contradiction. 
  unfold Silent in H2. 
  generalize (not_all_ex_not _ _ H2). intros [S2 A].
  generalize (not_all_ex_not _ _ A). intros [t B].
  generalize (not_all_ex_not _ _ B). intros [S3 C].
  generalize (imply_to_and _ _ C). intros [D F].
  generalize (imply_to_and _ _ F). intros [G J].
  exists S2; exists S3; exists t. auto.  
Qed.

Lemma Steps_star:
  forall S1 S2, Steps S1 S2 ->
  exists t, star step (state_of_State S1) t (state_of_State S2)
         /\ traceinf_of_State S1 = t *** traceinf_of_State S2.
Proof.
  induction 1.
  exists E0; split. apply star_refl. rewrite E0_left_inf; auto.
  inv H. destruct IHSteps as [t' [A B]].
  exists (t ** t'); split.
  simpl; eapply star_left; eauto.
  simpl in *. subst T. rewrite Eappinf_assoc; auto.
Qed.

Lemma Silent_forever_silent:
  forall S,
  Silent S -> forever_silent step (state_of_State S).
Proof.
  cofix COINDHYP; intro S. case S. intros until f. simpl. case f. intros.
  assert (Step t (ST s1 (t *** T0) (forever_intro s1 t s0 f0))
                 (ST s2 T0 f0)). 
    constructor.
  assert (t = E0). 
    red in H. eapply H; eauto. apply Steps_refl.
  apply forever_silent_intro with (state_of_State (ST s2 T0 f0)).
  rewrite <- H1. assumption. 
  apply COINDHYP. 
  red; intros. eapply H. eapply Steps_left; eauto. eauto. 
Qed.

Lemma Reactive_forever_reactive:
  forall S,
  Reactive S -> forever_reactive step (state_of_State S) (traceinf_of_State S).
Proof.
  cofix COINDHYP; intros.
  destruct (H S) as [S1 [S2 [t [A [B C]]]]]. apply Steps_refl. 
  destruct (Steps_star _ _ A) as [t' [P Q]].
  inv B. simpl in *. rewrite Q. rewrite <- Eappinf_assoc. 
  apply forever_reactive_intro with s2. 
  eapply star_right; eauto. 
  red; intros. destruct (Eapp_E0_inv evsem H0). contradiction.
  change (forever_reactive step (state_of_State (ST s2 T F)) (traceinf_of_State (ST s2 T F))).
  apply COINDHYP. 
  red; intros. apply H.
  eapply Steps_trans. eauto.
  eapply Steps_left. constructor. eauto.
  auto.
Qed.

Theorem forever_silent_or_reactive:
  forall s T,
  forever step s T ->
  forever_reactive step s T \/
  exists t, exists s', exists T',
  star step s t s' /\ forever_silent step s' /\ T = t *** T'.
Proof.
  intros. 
  destruct (Reactive_or_Silent (ST s T H)).
  left. 
  change (forever_reactive step (state_of_State (ST s T H)) (traceinf_of_State (ST s T H))).
  apply Reactive_forever_reactive. auto.
  destruct H0 as [S' [A B]].
  exploit Steps_star; eauto. intros [t [C D]]. simpl in *.
  right. exists t; exists (state_of_State S'); exists (traceinf_of_State S').
  split. auto. 
  split. apply Silent_forever_silent. auto.
  auto.
Qed.

End INF_SEQ_DECOMP.



End SmallStep.