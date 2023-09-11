Load PreservationHeader.

Lemma goal : forall sf (Hin: In sf (State.stack s2)), stackframe_weak_inv prog s2 sf.
Proof.
 destruct sf; intros; try exact I.
 destruct inhpath; destruct k.
  Require Import PreservationStackKconstrotherBase.
  eauto using goal.
  Require Import PreservationStackKconstrotherField.
  destruct kind; eauto using goal.
 Require Import PreservationStackKconstrothercells.
 eauto using goal.
 destruct inhpath; destruct k.
  Require Import PreservationStackKdestrotherBase.
  eauto using goal.
  Require Import PreservationStackKdestrotherField.
  destruct kind; eauto using goal.
 Require Import PreservationStackKdestrcell.
 eauto using goal.
Qed.

End Preservation.

  
 
 