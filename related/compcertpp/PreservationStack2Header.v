Load PreservationHeader.

Lemma stack2_2 : forall (sf2 sf1 : StackFrame.t A nativeop)
    (l1 l2 : list (StackFrame.t A nativeop)),
    State.stack s1 = l1 ++ sf1 :: sf2 :: l2 ->
    is_code_frame sf1 ->
    stackframe_constructor_inv prog s1 sf2
.
Proof.
 intros.
 destruct (stack2 Hs1 (sf1 := sf1) (l1 := l1) (l2 := sf2 :: l2) H).
 eauto.
Qed.

Set Printing Depth 1048576.
