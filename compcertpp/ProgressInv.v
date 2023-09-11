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
Require Import Progress.
Require Import Invariant.
Require Import Preservation.
Require Import Constrorder.
Load Param.
Open Scope Z_scope.

(** More progress properties needing the Invariant. *)

(** * POPL 2012 submission: Theorem 3 *)

Section Progress.

Variable A : ATOM.t.
Variable nativeop : Type.

Variable prog : Program.t A nativeop.
Notation hier := (Program.hierarchy prog).

Hypothesis hierarchy_wf : Well_formed_hierarchy.prop hier. (** needed for [vbase_order_list] *)

Variable cppsem : cppsemparam.
Variable sem : semparam A nativeop.

Corollary progress : forall cn,
  has_nearly_trivial_constructor prog cppsem sem cn ->
  forall num,  (0 < num)%Z ->
    forall s vlocstruct stm vars stl bl stk gl cs auxcs f,
      s = (State.make (State.codepoint vars (Sblock (Some (vlocstruct, cn, num)) (fun _ => Sconstructor cn nil) stm) stl bl) stk gl cs auxcs f) ->
      invariant prog s ->
      exists hp, exists obj, exists gl1,
        (obj, gl1) =  Globals.new gl cn num  /\
        exists t, exists vars', exists gl', exists cs', exists auxcs',
          star _  (step prog cppsem (sem := sem)) s t
          (State.make (State.codepoint vars' stm nil (BlockPoint.make stl (Some obj) :: bl)) stk gl' cs' auxcs' f) /\
          vars' = PTree.set vlocstruct (Value.ptr (Value.subobject obj nil 0 Class.Inheritance.Repeated (cn :: nil) hp)) vars /\
            (Globals.heap gl') ! obj = (Globals.heap gl1) ! obj /\
            exists o, (Globals.heap gl1) ! obj = Some o /\
              Object.class o = cn /\
              Object.arraysize o = num
              /\
              forall i, 0 <= i < num ->
                assoc (@pointer_eq_dec _) (obj, (nil, i, (Class.Inheritance.Repeated, cn :: nil))) cs' = Some Constructed.
Proof.
 intros.
 subst.
 generalize (progress hierarchy_wf H H0 vlocstruct stm vars stl bl stk gl cs auxcs f).
 intro; invall; subst.
 generalize (star_invariant _ (Preservation.goal  hierarchy_wf) H2 H4).
 intro.
 esplit.
 esplit.
 esplit.
 split.
 eassumption.
 esplit.
 esplit.
 esplit.
 esplit.
 esplit.
 split.
 eassumption.
 split.
 reflexivity.
 split.
 assumption.
esplit.
split.
eassumption.
split.
trivial.
split.
trivial.
refine (_ (constructed_stack_objects_correct H3 _)).
2 : simpl; left; reflexivity.
simpl.
rewrite H5.
rewrite H7.
eauto.
Qed.

Corollary progress_destr : forall s,
  invariant prog s -> forall gl obj,
    (forall o, (Globals.heap gl) ! obj = Some o -> has_trivial_destructor prog (Object.class o)) ->
    forall sdestruct sdestruct',
      exit_succ sdestruct = Some sdestruct' ->      
      forall vars stl0 stl bl stk cs auxcs f,
        s = (State.make (State.codepoint vars sdestruct stl0 (BlockPoint.make stl (Some obj) :: bl)) stk gl cs auxcs f) ->
        exists gl', exists cs', exists auxcs',
          star _ (step prog cppsem (sem := sem))
          s E0
          (State.make (State.codepoint vars sdestruct' stl bl) stk gl' cs' auxcs' (obj :: f)) /\             (Globals.heap gl') ! obj = (Globals.heap gl) ! obj /\
          exists o, 
            (Globals.heap gl) ! obj = Some o /\
            forall i, 0 <= i < Object.arraysize o ->
              assoc (@pointer_eq_dec _) (obj, (nil, i, (Class.Inheritance.Repeated, Object.class o :: nil))) cs' = Some Destructed.             
Proof.
 intros; subst.
 generalize (stack_objects_exist H (or_introl _ (refl_equal _))). 
 simpl.
 case_eq ((Globals.heap gl) ! obj); try congruence.
 intros until 1.
 intros _.
 generalize (object_arraysizes_nonnegative H H2).
 intro.
 generalize (H0 _ H2).
 intro.
 generalize (progress_destr hierarchy_wf cppsem sem H2 H4 H3 H1 vars stl0 stl bl stk cs auxcs f).
 intros; invall; subst.
 generalize (star_invariant _ (Preservation.goal  hierarchy_wf) H H6).
 intro.
 esplit.
 esplit.
 esplit.
 split.
 eassumption.
 generalize (star_object hierarchy_wf H6 H H2).
 simpl.
 intro.
 split; auto.
 esplit.
 split.
 reflexivity.
 exact (deallocated_objects_destructed H5 (or_introl _ (refl_equal _)) H7).
Qed.
 
End Progress.