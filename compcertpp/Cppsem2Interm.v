Require Import Coqlib.
Require Import Cplusconcepts.
Require Import CplusWf.
Require Import LibLists.
Require Import Tactics.
Require Import LibMaps.
Require Import Events.
Require Import Smallstep.
Require Import Cppsem.
Require Import Interm.
Require Import Cppsem2IntermAux.
Load Param.
Open Scope Z_scope.

Section Compiler.

Variable A : ATOM.t.

Variable nativeop : Type.


Function compile_var (n : newvar) {struct n} : ident :=
  match n with
    | Oldvar x => xO x
    | Newvar x => xI x
  end.

(** * Name mangling *)

Require Import Mangle.

Lemma compile_var_inj : forall v1 v2 : newvar, compile_var v1 = compile_var v2 -> v1 = v2.
Proof.
 intros ? ?;
 functional induction (compile_var v1);
   functional induction (compile_var v2);
     intros;
       congruence.
Qed.

Function compile_static (n : newstatic) {struct n} : ident :=
  match n with
    | Oldstatic x => xO x
    | Newstatic x => xI x
  end.

Lemma compile_static_inj : forall v1 v2, compile_static v1 = compile_static v2 -> v1 = v2.
Proof.
  intros ? ?;
    functional induction (compile_static v1);
      functional induction (compile_static v2);
        intros;
          congruence.
Qed.

Variable compile_atom_type : ATOM.ty A -> ident.

Hypothesis compile_atom_type_inj : forall a1 a2, compile_atom_type a1 = compile_atom_type a2 -> a1 = a2.

Function compile_type (ty : Typ.t A) {struct ty} : ident :=
  match ty with
    | Typ.atom a => xO (compile_atom_type a)
    | Typ.class cl => xI cl
  end.

Lemma compile_type_inj : forall ty1 ty2, compile_type ty1 = compile_type ty2 -> ty1 = ty2.
Proof.
  intros ? ?.
  functional induction (compile_type ty1); functional induction (compile_type ty2); intros; try congruence.
  f_equal.
  apply compile_atom_type_inj.
  congruence.
Qed.

Function compile_constrdestr_aux (cd : constrdestr A) {struct cd} : ident :=
  match cd with
    | StaticDestructor => xH
    | StaticConstructor l => Psucc (encode_list compile_type l)
  end.

Lemma Psucc_not_xH : forall id, Psucc id <> xH.
Proof.
  destruct id; simpl; congruence.
Qed.

Lemma compile_constrdestr_aux_inj : forall cd1 cd2,
  compile_constrdestr_aux cd1 = compile_constrdestr_aux cd2 -> cd1 = cd2.
Proof.
  destruct cd1;
    destruct cd2;
      simpl;
        try congruence.
  intro.
  generalize (Psucc_inj _ _ H).
  intro.
  generalize (encode_list_inj compile_type_inj H0).
  congruence.
intro; edestruct Psucc_not_xH; eauto.
intro H; symmetry in H; edestruct Psucc_not_xH; eauto.
Qed.

Definition compile_constrdestr_naive (i : ident) (cd : constrdestr A) (b : bool) :=
  (if b then xI else xO) (encode_couple_pos (i, (compile_constrdestr_aux cd)))
.

Remark bool_eq_dec : forall b1 b2 : bool, {b1 = b2} + {b1 <> b2}.
Proof.
  decide equality.
Qed.

Lemma compile_constrdestr_naive_inj : forall i1 cd1 b1 i2 cd2 b2,
  compile_constrdestr_naive i1 cd1 b1 = compile_constrdestr_naive i2 cd2 b2 ->
   (i1, cd1, b1) = (i2, cd2, b2).
Proof.
  unfold compile_constrdestr_naive.
  intros.
  destruct (bool_eq_dec b1 b2).
  2 : destruct b1; destruct b2; congruence.
  subst.
  f_equal.
  cut ((i1, compile_constrdestr_aux cd1) = (i2, compile_constrdestr_aux cd2)).
   injection 1.
   intro.
   generalize (compile_constrdestr_aux_inj H1). 
   congruence.
  eapply encode_couple_pos_inj.
  destruct b2; congruence.
Qed.

Variable prog : Program.t A nativeop.

Hypothesis hierarchy_wf : Well_formed_hierarchy.prop (Program.hierarchy prog).

Definition vborder_list_ex2 class :=
  match vborder_list_ex hierarchy_wf class with
    | inleft (exist (_ :: _) _) => true
    | _ => false
  end.


Definition compile_constrdestr (i : ident) (cd : constrdestr A) (b : bool) :=
  match cd with
    | StaticConstructor _ =>
      compile_constrdestr_naive i cd
      (if b then true else
        if vborder_list_ex2 i then false else true (** use unique *constructor* for classes with no virtual bases *)
      )
    | _ => compile_constrdestr_naive i cd b
  end
.

(** * Compilation of static functions, constructors and destructors *)

Section Fold_to_ptree.

  Variables K U V : Type.

  Variable f : ident -> K -> U -> option (ident * V).

  Function fold_assoc_to_ptree (l : list (ident * list (K * U))) (t : PTree.t V) {struct l} : PTree.t V :=
    match l with
      | nil => t
      | (class, lconstr) :: l' => assoc_to_ptree (f class) lconstr (fold_assoc_to_ptree l' t)
    end. 

  Hypothesis f_inj : forall i1 k1 u1 i v1,
    f i1 k1 u1 = Some (i, v1) ->
    forall i2 k2 u2 v2, f i2 k2 u2 = Some (i, v2) ->
      (i1, k1) = (i2, k2).

  Let f_inj' : forall class k1 u1 i v1,
    f class k1 u1 = Some (i, v1) ->
    forall k2 u2 v2,
      f class k2 u2 = Some (i, v2) ->
      k1 = k2 \/ v1 = v2.
  Proof.
   intros.
   generalize (f_inj H H0).
   injection 1; auto.
  Qed.

  Hypothesis K_eq_dec : forall k1 k2 : K, {k1 = k2} + {k1 <> k2}.

  Lemma fold_assoc_to_ptree_some : forall l class lk,
    assoc peq class l = Some lk ->
    forall k u, assoc K_eq_dec k lk = Some u ->
      forall i v, f class k u = Some (i, v) ->
        forall t, (fold_assoc_to_ptree l t) ! i = Some v.
  Proof.
   induction l; simpl.
    intros; discriminate.
   destruct a.
   intros ? ?.
   destruct (peq p class).
    subst.
    injection 1; intro; subst; eauto using assoc_to_ptree_some, f_inj'.
   intros.
   erewrite (assoc_to_ptree_other).
   eauto.    
   intros.
   intro.
   injection (f_inj H2 H1).
   congruence.
 Qed.

 Lemma fold_assoc_to_ptree_other : forall l i,
   (forall class k u v, f class k u <> Some (i, v)) ->
   forall t,
     (fold_assoc_to_ptree l t) ! i = t ! i.
 Proof.
   induction l; simpl; trivial.
   intros.
   destruct a.
   erewrite assoc_to_ptree_other;
   eauto.
 Qed.

 Definition fold_ptree_to_ptree tu tv := fold_assoc_to_ptree (PTree.elements tu) tv.

 Lemma fold_ptree_to_ptree_some : forall tu class lk,
    tu ! class = Some lk ->
    forall k u, assoc K_eq_dec k lk = Some u ->
      forall i v, f class k u = Some (i, v) ->
        forall t, (fold_ptree_to_ptree tu t) ! i = Some v.
 Proof.
  intros until 1.
  generalize (ptree_assoc H).
  unfold fold_ptree_to_ptree; intros; eauto using fold_assoc_to_ptree_some.
 Qed.

 Lemma fold_ptree_to_ptree_other : forall l i,
   (forall class k u v, f class k u <> Some (i, v)) ->
   forall t,
     (fold_ptree_to_ptree l t) ! i = t ! i.
 Proof.
  unfold fold_ptree_to_ptree; eauto using fold_assoc_to_ptree_other.
 Qed.

End Fold_to_ptree.

Variable semparam : semparam A nativeop.

Function f_constructor_mostderived (class : ident) (ctype : list (Typ.t A)) (ctor : Constructor.t A nativeop) : option (ident * static_fun A (nativeop)) :=
  match (Program.constructors prog) ! class with
    | None => None
    | Some lk =>
      match assoc (@Program.constructor_key_eq_dec _) ctype lk with
        | Some _ => Some (compile_static (Newstatic (compile_constrdestr_naive class (StaticConstructor ctype) true)), compile_constructor semparam compile_var compile_static compile_constrdestr hierarchy_wf class ctor true)
        | _ => None
      end
  end.

Lemma tilde_1_inj : forall p1 p2, ((p1)~1)%positive = ((p2)~1)%positive -> p1 = p2.
Proof.
  intros; congruence.
Qed.

Lemma tilde_0_inj : forall p1 p2, ((p1)~0)%positive = ((p2)~0)%positive -> p1 = p2.
Proof.
  intros; congruence.
Qed.

Lemma f_constructor_mostderived_inj : forall i1 k1 u1 i v1,
    f_constructor_mostderived i1 k1 u1 = Some (i, v1) ->
    forall i2 k2 u2 v2, f_constructor_mostderived i2 k2 u2 = Some (i, v2) ->
      (i1, k1) = (i2, k2).
Proof.
  intros.
  functional induction (f_constructor_mostderived i1 k1 u1); try discriminate;
  functional induction (f_constructor_mostderived i2 k2 u2); try discriminate.
  Opaque compile_constrdestr_naive.
  injection H; injection H0; intros; subst.
  generalize (compile_constrdestr_naive_inj (tilde_1_inj H4)).
  congruence.
Qed.

Function f_constructor_not_mostderived (class : ident) (ctype : list (Typ.t A)) (ctor : Constructor.t A nativeop) : option (ident * static_fun A (nativeop)) :=
  match (Program.constructors prog) ! class with
    | None => None
    | Some lk =>
      match assoc (@Program.constructor_key_eq_dec _) ctype lk with
        | Some _ => 
          if vborder_list_ex2 class 
            then
              Some (compile_static (Newstatic (compile_constrdestr_naive class (StaticConstructor ctype) false)), compile_constructor semparam compile_var compile_static compile_constrdestr hierarchy_wf class ctor false)
            else None (** do not compile subobject constructor if class has no virtual bases *)
        | _ => None
      end
  end.

Lemma pair_inj : forall A B : Type, forall a1 a2 : A, forall b1 b2 : B,
  (a1, b1) = (a2, b2) -> (a1 = a2 /\ b1 = b2).
Proof.
  intros; split; congruence.
Qed.

Lemma newstatic_inj : forall i1 i2, Newstatic i1 = Newstatic i2 -> i1 = i2.
Proof.
  congruence.
Qed.

Lemma f_constructor_not_mostderived_inj : forall i1 k1 u1 i v1,
    f_constructor_not_mostderived i1 k1 u1 = Some (i, v1) ->
    forall i2 k2 u2 v2, f_constructor_not_mostderived i2 k2 u2 = Some (i, v2) ->
      (i1, k1) = (i2, k2).
Proof.
  intros.
  functional induction (f_constructor_not_mostderived i1 k1 u1); try discriminate.
  functional induction (f_constructor_not_mostderived i2 k2 u2); try discriminate.
  destruct (pair_inj (option_inj H0)); subst.
  destruct (pair_inj (option_inj H)); subst.
  generalize (compile_constrdestr_naive_inj (newstatic_inj (compile_static_inj H1))).
  congruence.
Qed.

Function f_destructor (b : bool) (class : ident) (_unused : Class.t A) : option (ident * static_fun A (nativeop)) :=
  match (Program.hierarchy prog) ! class with
    | Some _ => Some (compile_static (Newstatic (compile_constrdestr_naive class (StaticDestructor A) b)), compile_destructor semparam compile_var compile_static compile_constrdestr hierarchy_wf class b)
    | _ => None
  end.

Lemma f_destructor_inj : forall b i1 u1 i v1,
    f_destructor b i1 u1 = Some (i, v1) ->
    forall i2 u2 v2, f_destructor b i2 u2 = Some (i, v2) ->
      i1 = i2.
Proof.
  unfold f_destructor.
  intros.
  destruct ((Program.hierarchy prog) ! i1); try discriminate.
  destruct ((Program.hierarchy prog) ! i2); try discriminate.
  destruct (pair_inj (option_inj H)); subst.
  destruct (pair_inj (option_inj H0)); subst.
  generalize (compile_constrdestr_naive_inj (newstatic_inj (compile_static_inj H1))).
  congruence.
Qed.

Definition f_static (stid : ident) (m : Static_method.t A nativeop) : option (ident * static_fun A (nativeop)) :=
  Some
  (compile_static (Oldstatic stid),
    Static_fun
    (map (fun v : ident => compile_var (Oldvar v))
      (Static_method.args m))
    (compile' semparam (prog:=prog) compile_var
      compile_static compile_constrdestr hierarchy_wf
      (Context 1 None nil 0 false) (Static_method.code m))).


Lemma f_static_inj :
forall (k : positive) (u : Static_method.t A nativeop)
     (i0 : positive) (v : static_fun A (nativeop)),
   f_static k u = Some (i0, v) ->
   forall (k' : positive) (u' : Static_method.t A nativeop)
     (v' : static_fun A (nativeop)),
   f_static k' u' = Some (i0, v') -> k = k'
.
Proof.
  unfold f_static; simpl.
  injection 1; intros until 2; subst.
  injection 1; intros; subst.
  auto.
Qed.

Definition statics' :=
  ptree_to_ptree f_static (Program.static_methods prog)
  (ptree_to_ptree (f_destructor true) (Program.hierarchy prog)
    (ptree_to_ptree (f_destructor false) (Program.hierarchy prog)
      (fold_ptree_to_ptree f_constructor_not_mostderived (Program.constructors prog)
        (fold_ptree_to_ptree f_constructor_mostderived (Program.constructors prog)
          (PTree.empty _)
        )
      )
    )
  ).

Lemma prog'_statics : 
  forall (i : positive) (m : Static_method.t A nativeop),
    (Program.static_methods prog) ! i = Some m ->
    (statics') ! (compile_static (Oldstatic i)) =
    Some
    (Static_fun
      (map (fun v : ident => compile_var (Oldvar v))
        (Static_method.args m))
      (compile' semparam (prog:=prog) compile_var
        compile_static compile_constrdestr hierarchy_wf
        (Context 1 None nil 0 false) (Static_method.code m)))
    .
Proof.
  unfold statics'.
  intros.
  eapply ptree_to_ptree_some.
  eauto using f_static_inj.
  eassumption.
  reflexivity.
Qed.

Lemma prog'_destructors : forall cn : positive,
        (Program.hierarchy prog) ! cn <> None ->
        forall b : bool,
        (statics')
        ! (compile_static
             (Newstatic (compile_constrdestr cn (StaticDestructor A) b))) =
        Some
          (compile_destructor semparam (prog:=prog) compile_var
             compile_static compile_constrdestr hierarchy_wf cn b).
Proof.
  unfold statics'.
  intros.
  case_eq ((Program.hierarchy prog) ! cn); try congruence.
  intros.
  erewrite ptree_to_ptree_other.
  destruct b.
   eapply ptree_to_ptree_some.
   eauto using f_destructor_inj.
   eassumption.
   unfold f_destructor.
   rewrite H0.
   reflexivity.
  erewrite ptree_to_ptree_other.
  eapply ptree_to_ptree_some.
   eauto using f_destructor_inj.
   eassumption.
   unfold f_destructor.
   rewrite H0.
   reflexivity.
  unfold f_destructor.   
  intros.
  destruct ((Program.hierarchy prog) ! k); simpl; try congruence.
  intro.
  discriminate.
 unfold f_static.
 intros.
 intro.
 discriminate.
Qed.

Lemma prog'_constructors_mostderived :
  (forall (cn : positive)
          (c : list (list (Typ.t A) * Constructor.t A nativeop)),
        (Program.constructors prog) ! cn = Some c ->
        forall (ty : list (Typ.t A)) (co : Constructor.t A nativeop),
        assoc (@Program.constructor_key_eq_dec _) ty c = Some co ->
        (statics')
        ! (compile_static
             (Newstatic (compile_constrdestr cn (StaticConstructor ty) true))) =
        Some
          (compile_constructor semparam (prog:=prog) compile_var
             compile_static compile_constrdestr hierarchy_wf cn co true))
.
Proof.
  unfold statics'.
  intros.
  erewrite ptree_to_ptree_other.
  erewrite ptree_to_ptree_other.
  erewrite ptree_to_ptree_other.
  erewrite fold_ptree_to_ptree_other.
  eapply fold_ptree_to_ptree_some.
  eauto using f_constructor_mostderived_inj.
  eassumption.
  eassumption.
  unfold f_constructor_mostderived.
  rewrite H.
  rewrite H0.
  reflexivity.
 intros.
 unfold compile_constrdestr.
 functional induction (f_constructor_not_mostderived class k u); try congruence.
 intro.
 discriminate.
 intros.
 unfold compile_constrdestr.
 unfold f_destructor.
 destruct ((Program.hierarchy prog) ! k);  discriminate.
 unfold f_destructor.
 intro.
 destruct ((Program.hierarchy prog) ! k);  try discriminate.
 unfold compile_constrdestr.
 simpl.
 intros.
 intro.
 generalize (option_inj H1).
 intro.
 generalize (pair_inj H2).
 destruct 1.
 generalize (tilde_1_inj H3).
 intro.
 generalize (compile_constrdestr_naive_inj H5).
 intro; discriminate.
 congruence.
 unfold f_static.
 unfold compile_constrdestr.
 intros.
 intro.
 generalize (pair_inj (option_inj H1)).
 destruct 1.
 generalize (compile_static_inj H2).
 intro; discriminate.
Qed.

Lemma prog'_constructors :
  (forall (cn : positive)
          (c : list (list (Typ.t A) * Constructor.t A nativeop)),
        (Program.constructors prog) ! cn = Some c ->
        forall (ty : list (Typ.t A)) (co : Constructor.t A nativeop),
        assoc (@Program.constructor_key_eq_dec _) ty c = Some co ->
        forall b : bool,
        (statics')
        ! (compile_static
             (Newstatic (compile_constrdestr cn (StaticConstructor ty) b))) =
        Some
          (compile_constructor semparam (prog:=prog) compile_var
             compile_static compile_constrdestr hierarchy_wf cn co b))
.
Proof.
  unfold compile_constrdestr at 1.
  destruct b.
   eapply prog'_constructors_mostderived.
   eassumption.
   assumption.
  case_eq (vborder_list_ex2 cn).
   unfold statics'.
  erewrite ptree_to_ptree_other.
  erewrite ptree_to_ptree_other.
  erewrite ptree_to_ptree_other.
  intro.
  eapply fold_ptree_to_ptree_some.
  eauto using f_constructor_not_mostderived_inj.
  eassumption.
  eassumption.
  unfold f_constructor_not_mostderived.
  rewrite H.
  rewrite H0.
  rewrite H1.
  reflexivity.
 intros.
 functional induction (f_destructor false k u); try congruence.
 intro.
 destruct (pair_inj (option_inj H1)).
 generalize (compile_constrdestr_naive_inj (newstatic_inj (compile_static_inj H2))).
 congruence.
 intros.
 functional induction (f_destructor true k u); try congruence.
 intro.
 destruct (pair_inj (option_inj H1)).
 generalize (compile_constrdestr_naive_inj (newstatic_inj (compile_static_inj H2))).
 congruence. 
 unfold f_static.
 intros.
 intro.
 destruct (pair_inj (option_inj H1)).
 generalize (compile_static_inj H2); congruence.
intro.
 erewrite <- compile_constructor_eq_with_no_virtual_bases. (** if constructors were duplicated, then the same code would have been produced for both of them, in this case where class has no virtual bases *) 
 eapply prog'_constructors_mostderived.
 eassumption.
 assumption.
unfold vborder_list_ex2 in *.
destruct (vborder_list_ex hierarchy_wf cn).
 destruct s.
 destruct x; try congruence.
 invall.
 intros.
 exact (virtual_base_vborder_list H2 H3 H4).
intros.
exact (is_virtual_base_of_defined H2 e).
Qed.

Definition methods' :=
  PTree.map 
  (fun i m =>
    (Interm.Method_body (compile_var (Oldvar (Method_body.this m)))
      (map (fun v : ident => compile_var (Oldvar v))
        (Method_body.args m))
      (compile' semparam (prog:=prog) compile_var
        compile_static compile_constrdestr hierarchy_wf
        (Context 1 None nil 0 false) (Method_body.code m)))
  ) (Program.methods prog).

Lemma prog'_methods :
  forall (i : positive) (m : Method_body.t A nativeop),
    (Program.methods prog) ! i = Some m ->
    (methods') ! i =
    Some
    (Interm.Method_body (compile_var (Oldvar (Method_body.this m)))
      (map (fun v : ident => compile_var (Oldvar v))
        (Method_body.args m))
      (compile' semparam (prog:=prog) compile_var
        compile_static compile_constrdestr hierarchy_wf
        (Context 1 None nil 0 false) (Method_body.code m))).
Proof.
  intros.
  unfold methods'.
  rewrite PTree.gmap. 
  unfold option_map.
  rewrite H.
  reflexivity.
Qed.

Definition prog' :=
  Program (Program.hierarchy prog) methods' statics' (compile' semparam (prog:=prog) compile_var compile_static
    compile_constrdestr hierarchy_wf (Context 1 None nil 0 false)
    (Program.main prog)).



Theorem simulation : forall cppsem is_primary_path  beh,
  not_wrong beh ->
  program_behaves (Cppsem.step prog cppsem (sem := semparam)) (Cppsem.initial_state prog) (@Cppsem.final_state A nativeop semparam) beh ->
  program_behaves (Interm.step prog' (sem := semparam) is_primary_path) (Interm.initial_state prog') (@Interm.final_state A (nativeop) (semparam)) beh.
Proof.
 intro.
 intro.
 apply simulation_plus_preservation with (match_states := invariant semparam compile_var compile_static compile_constrdestr hierarchy_wf).
 eauto using evtr_sem.
 eauto using init.
 eauto using fin.
 intros.
 eapply preservation.
 exact compile_var_inj.
 reflexivity.
 exact prog'_constructors.
 exact prog'_destructors.
 exact prog'_statics.
 exact prog'_methods.
 eassumption.
 assumption.
Qed.


End Compiler.

Check simulation.  