Require Import Coqlib.
Require Import Tactics.
Require Import LibLists.
Require Import LibMaps.
Require Import Cplusconcepts.
Require Import CplusWf.
Require Import LayoutConstraints.
Require Import Dynamic.
Require Import DynamicWf.
Require Import CPP.
Require Memory.
Require Import Events.
Require Import Smallstep.
Require Import Target.
Require Import Vtables.
Open Scope Z_scope.
Load Param.

Notation OldVar := (xO) (only parsing).
Notation NewVar := (xI) (only parsing).

Section Common.

  Variable A : ATOM.t.

  Variable hierarchy : PTree.t (Class.t A).

  Hypothesis Hhier : Well_formed_hierarchy.prop hierarchy.


Notation is_dynamic := (Dynamic.is_dynamic).

Variable COP : CPPOPTIM A.

Variable vop' : valop' A Z.

Hypothesis vop'_pos : forall k t, 0 < vop' k t.     

  Variable offsets : PTree.t (LayoutConstraints.t A).


    Lemma reduce_path_trivial : forall rr,
      reduce_path (A:=A) offsets (rr :: nil) = rr :: nil.
    Proof.
      unfold reduce_path.
      destruct (reduce_path_aux offsets).
      intros.
      assert (rr :: nil <> nil) by congruence.
      generalize (y _ H).
      simpl.
      destruct 1.
      destruct H0.
      destruct H0.
      congruence.
    Qed.

      
      Hypothesis intro : forall ci o, offsets ! ci = Some o -> class_level_prop (OP COP) (PF vop'_pos) offsets hierarchy ci o.
      
      Hypothesis guard : forall ci, offsets ! ci <> None -> hierarchy ! ci <> None.

      Hypothesis exis: forall ci, hierarchy ! ci <> None -> offsets ! ci <> None. 

      Hypothesis empty_prop : forall (ci : positive) (oc : LayoutConstraints.t A),
        offsets ! ci = Some oc ->
        disjoint_empty_base_offsets (OP COP) offsets hierarchy ci oc.

   

Variable mblock : Type.

        Variables memblocks memvalues : Type.

        Variable memop : Memory.op (val A (romty A) mblock)  memblocks memvalues mblock.

        Hypothesis memprop : Memory.prop memop (valop (romty A)  mblock vop').
   
        Variable (compile_method_name : ident -> MethodSignature.t A -> ident).

        Variable nativeop : Type.

   Variable ovObj : ident.
   Variable ovVTT : ident.   

   Variable nvcap : ident.

   Variable real : ident.

   Function compile_set_vptr_case (h : Class.Inheritance.t) (ismostderived : bool) : bool :=
     match h with
       | Class.Inheritance.Repeated => true
       | _ => ismostderived
     end.
   
   Function compile_set_vptr (h : Class.Inheritance.t) (p : list ident) (ismostderived : bool) : stmt nativeop (romty A) :=
     if compile_set_vptr_case h ismostderived
       then
         match subobject_offset offsets real p with
           | None =>
             skip _ _
           | Some o =>
             seq
             (romop _ (Some (OldVar ovVTT)) (Target.vtable (romty := romty A) real (h, p)) (NewVar (Psucc nvcap)))
             (store _ _ (vop' Size (tyVptr _)) (OldVar ovObj) o (NewVar (Psucc nvcap)))
         end
       else
       match p with
         | nil => skip _ _
         | v :: _ =>
           match non_virtual_subobject_offset offsets 0 p with
             | None => skip _ _
             | Some o =>
               seq
               (romop _ (Some (NewVar nvcap)) (Target.vbase_offset (romty := romty A) real v) (NewVar (Psucc (Psucc nvcap))))
               (
                 seq
                 (ptrshiftmult _ _ (OldVar ovObj) (NewVar (Psucc (Psucc nvcap))) 1 (NewVar (Psucc (Psucc nvcap))))
                 (
                   seq                     
                   (romop _ (Some (OldVar ovVTT)) (Target.vtable (romty := romty A) real (h, p)) (NewVar (Psucc nvcap)))
                   (store _ _ (vop' Size (tyVptr _)) (NewVar (Psucc (Psucc nvcap))) o (NewVar (Psucc nvcap)))
                 )
               )
           end
       end
       .
   
   Function compile_set_vptr_list (l : list (Class.Inheritance.t * list ident)) (ismostderived : bool) {struct l} : stmt nativeop (romty A) :=
     match l with
       | nil => skip _ _
       | (h, p) :: l' =>
         seq
         (compile_set_vptr_list l' ismostderived)
         (compile_set_vptr h p ismostderived)
     end.


    Lemma array_path_valid_from :
      forall (via : array_path A) (to : ident) (to_n : Z) 
        (from : ident) (from_n : Z),
        valid_array_path (A:=A) hierarchy to to_n from from_n via ->
       hierarchy ! to <> None -> hierarchy ! from <> None
       .
    Proof.
      induction 1; simpl; intros; eauto using path_defined_from.
    Qed.      

    Variables  (hr : Class.Inheritance.t) (pr : list ident) (hyperreal : ident).

Section Path.

Hypothesis Hpath : path hierarchy real pr hyperreal hr.

Lemma primary_path_prefix : forall l1 l2,
  (List.length l1 <= List.length l2)%nat ->
  forall a, is_primary_path offsets (a :: l1) = true ->
    is_primary_path offsets (a :: l2) = true ->
    exists l, l2 = l1 ++ l.
Proof.
  intros.
  revert H0 l2 H H1.
  var (a :: l1).
  intro.
  revert a l1 H.
  functional induction (is_primary_path offsets v); try discriminate.
   injection 1; intros; subst.
   simpl; eauto.
  injection 1; intros; subst.
  simpl.
  simpl in H2.
  functional inversion H3; subst.
   simpl in *; omegaContradiction.
  simpl in H2.
  assert (length _x <= length _x1)%nat by omega.
  replace a'0 with a' in * by congruence.
  destruct (IHb x _ _ (refl_equal _) _ H0 X).
  esplit.
  f_equal.
  2 : eassumption.
  congruence.
Qed.    

Lemma reduce_path_location_reduce_path_contents : forall p1 h1 to1, path hierarchy to1 p1 real h1 ->
  forall h'1 p'1, (h'1, p'1) = concat (hr, pr) (h1, p1) ->
    forall to2 p2 h2, path hierarchy to2 p2 real h2 ->
      forall h'2 p'2, (h'2, p'2) = concat (hr, pr) (h2, p2) ->
        reduce_path offsets p'1 = reduce_path offsets p'2 ->
        reduce_path offsets p1 = reduce_path offsets p2.
Proof.
 intros.
 generalize (reduce_path_prefix offsets Hhier (path_concat Hpath H H0)).
 generalize (reduce_path_prefix offsets Hhier (path_concat Hpath H1 H2)).
 intros; invall.
 revert to1 to2 p1 h1 H h'1 p'1 H0 p2 h2 H1 h'2 p'2 H2 H3 x x0 x1 x2 H6 H4 H7 H9 H8 H5 H10 H12.
 cut (
forall (to1 to2 : ident) (p1 : list ident) (h1 : Class.Inheritance.t),
   path (A:=A) hierarchy to1 p1 real h1 ->
   forall (h'1 : Class.Inheritance.t) (p'1 : list ident),
   (h'1, p'1) = concat (hr, pr) (h1, p1) ->
   forall (p2 : list ident) (h2 : Class.Inheritance.t),
   path (A:=A) hierarchy to2 p2 real h2 ->
   forall (h'2 : Class.Inheritance.t) (p'2 : list ident),
   (h'2, p'2) = concat (hr, pr) (h2, p2) ->
   reduce_path (A:=A) offsets p'1 = reduce_path (A:=A) offsets p'2 ->
   forall (x : ident) (x0 : list ident) (x1 : ident) (x2 : list ident),
   path (A:=A) hierarchy x1 (reduce_path (A:=A) offsets p'2) hyperreal h'2 ->
   path (A:=A) hierarchy to2 (x1 :: x2) x1 Class.Inheritance.Repeated ->
   p'2 = reduce_path (A:=A) offsets p'2 ++ x2 ->
   is_primary_path (A:=A) offsets (x1 :: x2) = true ->
   path (A:=A) hierarchy x (reduce_path (A:=A) offsets p'1) hyperreal h'1 ->
   path (A:=A) hierarchy to1 (x :: x0) x Class.Inheritance.Repeated ->
   p'1 = reduce_path (A:=A) offsets p'1 ++ x0 ->
   is_primary_path (A:=A) offsets (x :: x0) = true ->
   (length x0 <= length x2)%nat ->
   reduce_path (A:=A) offsets p1 = reduce_path (A:=A) offsets p2
 ).
  intros.
  destruct (le_lt_dec (length x0) (length x2)).
  eauto.
  assert (length x2 <= length x0)%nat by omega.
  generalize (sym_equal H4).
  intro.
  symmetry.
  eauto.
 intros.
 generalize (path_last H4).
 rewrite <- H3.
 rewrite (path_last H8).
 injection 1; intros; subst x1.
 destruct (primary_path_prefix H12 H11 H7).
 subst x2.
 assert ((h'1, p'1) = concat (h'1, reduce_path offsets p'1) (Class.Inheritance.Repeated, x :: x0)).
 simpl.
 rewrite (path_last H8).
 destruct (peq x x); congruence.
 assert (x :: x0 <> nil) by congruence.
 assert (h'2 = h'1).
  rewrite H3 in H8.
  eauto using Well_formed_hierarchy.path_eq_hierarchy_eq. 
 subst h'2.  
 assert ((h'1, p'2) = concat (h'1, reduce_path offsets p'2) (concat (Class.Inheritance.Repeated, x :: x0) (Class.Inheritance.Repeated, to1 :: x1))).
 Opaque last.
  simpl.
  rewrite (path_last H9).
  destruct (peq to1 to1); try congruence.
  rewrite H6 at 1.
  simpl.
  rewrite (path_last H4).
  destruct (peq x x); congruence.
 rewrite <- concat_assoc in H16.
 rewrite <- H3 in H16.
 rewrite <- H14 in H16.
 rewrite H0 in H16.
 rewrite H2 in H16.
 rewrite concat_assoc in H16.
 case_eq (concat (h1, p1) (Class.Inheritance.Repeated, to1 :: x1)).
 intros.
 symmetry in H17. 
 generalize (last_correct (path_last H9)).
 destruct 1.
 assert (
   path hierarchy to2 (to1 :: x1) to1 Class.Inheritance.Repeated
 ).
  replace (x :: x0 ++ x1) with ((x :: x0) ++ x1) in H5 by reflexivity.
  rewrite e in H5.
  rewrite app_ass in H5.
  simpl in H5.
  assert (to1 :: x1 <> nil) by congruence.
  generalize (last_app_left H18 x2).
  rewrite (path_last H5).
  intros.
  symmetry in H19.
  destruct (last_correct H19).
  clear H10 H6.
  inversion H5.
  econstructor; eauto using is_valid_repeated_subobject_split_right.
  rewrite <- H17 in H16.
 generalize (Well_formed_hierarchy.concat_path_unique Hhier
H1 (path_concat H H18 H17)  Hpath H16).
 clear H10 H6.
 injection 1; intros; subst.
 simpl in H17.
 rewrite (path_last H) in H17.
 destruct (peq to1 to1); try congruence.
 injection H17; intros; subst.
 replace (x :: x0 ++ x1) with ((x :: x0) ++ x1) in H7 by reflexivity.
 rewrite e in H7.
 rewrite app_ass in H7.
 simpl in H7.
 generalize (primary_path_split_right Hhier H7).
 intro.
 generalize (path_path1 H).
  inversion 1; subst.
  erewrite reduce_path_primary_right.
  reflexivity.
  eassumption.
  eassumption.
  assumption.
 erewrite reduce_path_primary_right.
 reflexivity.
 eassumption.
 eassumption.
 assumption.
Qed.

Lemma reduce_path_location_reduce_path_contents' : forall p1 h1 to1, path hierarchy to1 p1 real h1 ->
  forall to2 p2 h2, path hierarchy to2 p2 real h2 ->
    reduce_path offsets p1 <> reduce_path offsets p2 ->
    forall h'1 p'1, (h'1, p'1) = concat (hr, pr) (h1, p1) ->
      forall h'2 p'2, (h'2, p'2) = concat (hr, pr) (h2, p2) ->
        reduce_path offsets p'1 <> reduce_path offsets p'2.
Proof.
 intros.
 generalize (reduce_path_location_reduce_path_contents H H2 H0 H3).
 tauto.
Qed.


End Path.


   Variables (ar : array_path A) (afrom : ident) (zfrom : Z) (i : Z)
   (Hptr : valid_relative_pointer hierarchy afrom zfrom ar hyperreal i hr pr real)
   (bl : mblock)
   (mbl : memblocks)
   (Hbl_valid : Memory.valid_block memop mbl bl)
   (oa : t A)
   (Hoa : offsets ! afrom = Some oa)
   (Hbsz : zfrom * size oa <= Memory.block_size memop mbl bl)
   (off : Z)
   (Hoff : relative_pointer_offset offsets afrom hyperreal ar i pr = Some off)
   (stack : list (frame A nativeop (romty A) mblock))
   (ismostderived : bool)
   (prog : program nativeop (romty A))
   (Hprog : Target.rom prog = rom Hhier intro guard exis compile_method_name)
   (tsp : targetsemparam)
   (sem : semparam A nativeop)
   (env0 : PTree.t (val A (romty A) mblock))
   (sm_obj : env0 ! (OldVar ovObj) = Some (Ptr _ _ (Some (bl, off)))).

Section Is_dynamic.

Variable  (sm_vtt : env0 ! (OldVar ovVTT) = Some (VTTptr (romty := romty A) _ _ (hyperreal, (hr, pr))))
   .

   Record small_invariant (env : PTree.t (val A (romty A) mblock)) : Prop := small_invariant_intro {
     sm_vptr : is_dynamic hierarchy real -> env ! (NewVar nvcap) = Some (Vptr (romty := romty A) _ _ (hyperreal, (hr, pr), (Class.Inheritance.Repeated, real :: nil)))
       ;
     sm_other : forall v, (forall n, v = NewVar n -> Plt n nvcap) -> env ! v = env0 ! v
   }.

   Section Step.

    Variable (to : ident) (Hto : is_dynamic hierarchy to) (h : Class.Inheritance.t) (p : list ident)
      (Hp : path hierarchy to p real h)
      (Hp_red : p = reduce_path offsets p)
      (env : PTree.t (val A (romty A) mblock))
      (oz : Z)
      (h' : Class.Inheritance.t) (p' : list ident)
      (Hhp' : (h', p') = concat (hr, pr) (h, p))
      (Hoz : relative_pointer_offset offsets afrom hyperreal ar i p' = Some oz)
      (Hismd : ismostderived = true -> ((hr, pr) = (Class.Inheritance.Repeated, hyperreal :: nil) \/ h = Class.Inheritance.Repeated))
      (Hinv : small_invariant env)
      (stl : list (stmt nativeop (romty A)))
      (mva : memvalues)   
      .

    Lemma step_prop : exists env', exists mva',
      star _ (step (sem := sem) vop' memop prog tsp)
      (State (compile_set_vptr (h) (p) (ismostderived)) stl env stack (Mem mbl mva))
      E0
      (State (skip _ _) stl env'  stack (Mem mbl mva')) /\
      small_invariant env' /\
      Memory.load memop (vop' Size (tyVptr _)) mbl mva' (bl, oz) = Some (Vptr (romty := romty A) _ _ (hyperreal, (hr, pr), (h, p)))
      /\
      (
        forall bl' o s, bl' <> bl \/ (oz + vop' Size (tyVptr _) <= o \/ o + s <= oz) ->
          Memory.load memop s mbl mva' (bl', o) =
          Memory.load memop s mbl mva (bl', o)
      ).
    Proof.
      assert (sm_obj0 : env ! (OldVar ovObj) = Some (Ptr _ _ (Some (bl, off)))).
       rewrite <- sm_obj.
       eapply sm_other.
       assumption.
       intros; congruence.
      assert (sm_vtt0 : env ! (OldVar ovVTT) = Some (VTTptr (romty := romty A) _ _ (hyperreal, (hr, pr)))).
       rewrite <- sm_vtt.
       eapply sm_other.
       assumption.
       intros; congruence.       
     unfold compile_set_vptr.
     functional inversion Hoff.
     subst off.
     generalize Hoz.
     unfold relative_pointer_offset.
     rewrite H0.
     rewrite H1.
     case_eq (subobject_offset offsets hyperreal p'); try congruence.
     intros until 1.
     injection 1; intro; subst oz.
     functional inversion H.
     subst l p'.
     inversion Hptr.     
     inversion Hinv.
     assert (Hdyn : is_dynamic hierarchy real) by eauto using is_dynamic_path, path_concat.
     generalize (sm_vptr0 Hdyn).
     clear sm_vptr0.
     intro sm_vptr0.     
     case_eq (compile_set_vptr_case h ismostderived).
      intros.      
      assert ((hr, pr) = (Class.Inheritance.Repeated, hyperreal :: nil) \/ h = Class.Inheritance.Repeated).
       functional inversion H10; auto.
      destruct H11.

      (** subobject of the true most-derived object *)
       injection H11; intros; subst hr pr.
       generalize (path_last H9).
       injection 1; intro; subst real.       
       erewrite concat_trivial_left in Hhp'.
       2 : eassumption.
       injection Hhp'; intros; subst h p.
       rewrite H.
       unfold subobject_offset in H2.
       rewrite H4 in H2.
       rewrite (virtual_base_offsets_self (intro H4)) in H2.
       simpl in H2.
       injection H2; intro; subst z2.
       assert (
         valid_relative_pointer (A:=A) hierarchy afrom zfrom ar hyperreal i 
         h' (b :: _x) to
       ).
        econstructor.
        eassumption.
        assumption.
        assumption.
        assumption.
       assert (offsets ! to <> None) by eauto using path_defined_to.       
       destruct (dynamic_align Hhier intro H16 Hoz Hoa H17 Hto).
       case_eq (offsets ! to); try congruence.
       intros.
       generalize (own_fields_offset_dynamic_low_bound (intro H20) Hto).
       simpl.
       intro.
       generalize (non_virtual_data_size_own_fields_offset (intro H20)). 
       intro.
       destruct (relative_pointer_data_incl intro H16 (dynamic_nonempty (c := COP) Hto) Hoz).
       generalize (H24 _ Hoa _ H20).
       intro.
       generalize (data_size_high_bound (intro Hoa)).
       intro.
       assert ((zfrom - 1) * size oa + size oa = zfrom * size oa) by ring.
       simpl in H18, H19.
       refine (_ (Memory.store_some (mv := (Vptr A (romty:=romty A) mblock
            (hyperreal, (Class.Inheritance.Repeated, hyperreal :: nil),
            (h', b :: _x)))
       ) memprop H19 Hbl_valid _ _ (memv := mva))).
       2 : omega.
       2 : simpl.
       2 : unfold valdata.
       2 : unfold type_of_value.
       2 : omega.
       case_eq (
Memory.store memop
     (Memory.valsize (valop (A:=A) (romty A) mblock vop')
        (Vptr A (romty:=romty A) mblock
           (hyperreal, (Class.Inheritance.Repeated, hyperreal :: nil),
           (h', b :: _x)))) mbl mva (bl, z1 + i * size ofto + z)
     (Vptr A (romty:=romty A) mblock
        (hyperreal, (Class.Inheritance.Repeated, hyperreal :: nil),
        (h', b :: _x)))
       ).
        2 : congruence.
       intros until 1.
       intros _.
       esplit.
       esplit.
       split.
       eright.
       econstructor.
       eright.
       econstructor.
       eauto.
       rewrite sm_vtt0.
       econstructor.
       rewrite Hprog.
       simpl.
       eapply map_all_pvtt_complete.
       eassumption.
       eauto using is_dynamic_path.
       rewrite Hprog.
       Opaque pvtables. simpl.
       eapply pvtables_complete.
       eassumption.
       2 : eassumption.
       assumption.
       assumption.
       rewrite Hprog.
       reflexivity.
       reflexivity.
      eright.
      econstructor.
      eright.
      econstructor.
      rewrite PTree.gso.
      eassumption.
      congruence.
      rewrite PTree.gss.
      reflexivity.
      reflexivity.
      replace (
        z1 + i * size ofto + 0 + z
      ) with (
        z1 + i * size ofto + z
      ) by omega.
      eassumption.
     eleft.
     reflexivity.
     reflexivity.
     reflexivity.
     repeat rewrite E0_left; eauto using evtr_sem.
     split.
     split.
     rewrite PTree.gso.
     subst hr.
     subst pr.
     subst real.
     auto.
     intro.
     injection H29.
     intro.
     generalize (Plt_succ nvcap).
     rewrite H30 at 1.
     apply Plt_irrefl.
    intros.
    rewrite PTree.gso.
    eauto.
    destruct v; try congruence.
    intro.
    generalize (H29 _ H30).
    intro.
    destruct (Plt_irrefl _ (Plt_trans _ _ _ (Plt_succ _) H31)).
    split.
    erewrite Memory.load_store_same.
    reflexivity.
    eassumption.
    eassumption.
   intros.
   eapply Memory.load_store_other.
   eassumption.
   eassumption.
   simpl.
   unfold valdata.
   unfold type_of_value.
   tauto.

(** non-virtual subobject *)
subst h.        
inversion Hp.
rewrite H11 in  *.
subst from.
unfold subobject_offset at 1.
assert (offsets ! real <> None) by eauto using path_defined_from.
case_eq (offsets ! real); try congruence.
intros.
rewrite (virtual_base_offsets_self (intro H15)).
generalize Hhp'.
intro.
simpl in Hhp'0.
rewrite (path_last H9) in Hhp'0.
destruct (peq real real); try congruence.
injection Hhp'0.
intros.
subst h'.
destruct (LibLists.last_correct (path_last H9)).
subst pr.
rewrite app_ass in H16.
simpl in H16.
rewrite H16 in H3.
generalize (non_virtual_subobject_offset_app_recip H3).
destruct 1.
destruct H17.
rewrite (non_virtual_subobject_offset_rewrite H18).
assert (
 valid_relative_pointer (A:=A) hierarchy afrom zfrom ar hyperreal i hr
   (b :: _x) to
).
 econstructor.
 eassumption.
 assumption.
 assumption.
 eapply path_concat.
 eassumption.
 eassumption.
 assumption.
 assert (offsets ! to <> None) by eauto using path_defined_to.
 destruct (dynamic_align Hhier intro H19 Hoz Hoa H20 Hto).
 simpl in H21, H22.
       case_eq (offsets ! to); try congruence.
       intros.
       generalize (own_fields_offset_dynamic_low_bound (intro H23) Hto).
       simpl.
       intro.
       generalize (non_virtual_data_size_own_fields_offset (intro H23)). 
       intro.
       destruct (relative_pointer_data_incl intro H19 (dynamic_nonempty (c := COP) Hto) Hoz).
       generalize (H27 _ Hoa _ H23).
       intro.
       generalize (data_size_high_bound (intro Hoa)).
       intro.
       assert ((zfrom - 1) * size oa + size oa = zfrom * size oa) by ring.
refine (_ (Memory.store_some (mv :=  (Vptr A (romty:=romty A) mblock
    (hyperreal, (hr, x ++ real :: nil),
      (Class.Inheritance.Repeated, real :: lf)))) memprop _ Hbl_valid _ _ (memv := mva))).
2 : eassumption.
2 : omega.
2 : simpl.
2 : unfold valdata.
2 : unfold type_of_value.
2 : omega.
case_eq (
   Memory.store memop
     (Memory.valsize (valop (A:=A) (romty A) mblock vop')
        (Vptr A (romty:=romty A) mblock
           (hyperreal, (hr, x ++ real :: nil),
           (Class.Inheritance.Repeated, real :: lf)))) mbl mva
     (bl, z1 + i * size ofto + z)
     (Vptr A (romty:=romty A) mblock
        (hyperreal, (hr, x ++ real :: nil),
        (Class.Inheritance.Repeated, real :: lf)))
); try congruence.
intros until 1.
intros _.
functional inversion H2.
assert (b0 = b).
 destruct x; simpl in *; congruence.
subst b0.
replace o0 with ofto in * by congruence.
replace o with ofto in * by congruence.
replace of0 with of in * by congruence.
replace x0 with z2 in * by congruence.
esplit.
esplit.
split.
eright.
econstructor.
eright.
econstructor.
eauto.
rewrite sm_vtt0.
econstructor.
rewrite Hprog.
simpl.
eapply map_all_pvtt_complete.
eassumption.
eauto using is_dynamic_path.
rewrite Hprog.
simpl.
eapply pvtables_complete.
eassumption.
2 : eassumption.
eassumption.
assumption.
rewrite Hprog.
simpl.
eapply LibLists.last_complete.
reflexivity.
eright.
econstructor.
eright.
econstructor.
rewrite PTree.gso.
eassumption.
congruence.
rewrite PTree.gss.
reflexivity.
reflexivity.
replace (
  z1 + i * size ofto + z2 + (z + 0 - z2)
) with (
  z1 + i * size ofto + z
) by omega.
eassumption.
eleft.
reflexivity.
reflexivity.
reflexivity.
     repeat rewrite E0_left; eauto using evtr_sem.
     split.
     split.
      rewrite PTree.gso.
      rewrite sm_vptr0.
      rewrite e0.
      reflexivity.
     intro.
     injection H37.
     intro.
     generalize (Plt_succ nvcap).
     rewrite H38 at 1.
     apply Plt_irrefl.
    intros.
    rewrite PTree.gso.
    eauto.
    destruct v; try congruence.
    intro.
    generalize (H37 _ H38).
    intro.
    destruct (Plt_irrefl _ (Plt_trans _ _ _ (Plt_succ _) H39)).
    split.
    erewrite Memory.load_store_same.
    reflexivity.
    eassumption.
    rewrite H32.
    eassumption.
   intros.
   eapply Memory.load_store_other.
   eassumption.
   eassumption.
   simpl.
   unfold valdata.
   unfold type_of_value.
   tauto.

(** virtual subobject: read into the VTable *)
functional inversion 1.
destruct h; try contradiction.
generalize Hhp'.
simpl.
injection 1; intros.
rewrite <- H16.
rewrite (non_virtual_subobject_offset_rewrite H3).
assert (
 path hierarchy real (real :: nil) real Class.Inheritance.Repeated
).
 eleft with (lt:= nil).
 reflexivity.
 reflexivity.
 simpl.
 case_eq (hierarchy ! real); auto.
 generalize (path_defined_to H9).
 intros; contradiction.
 generalize (concat_trivial_right H9).
 intro.
 symmetry in H19.
generalize (path_path1 Hp).
rewrite <- H16.
inversion 1; subst.
inversion H22; subst.
injection H11; intros; subst.
destruct (vboffsets_l_complete Hhier
intro exis H9 H18 H19 H2 H21).
destruct H15.
destruct H16.
destruct H16.
replace x with o in * by congruence.
replace o with ofto in * by congruence.
replace x0 with of in * by congruence.
case_eq (Zsem sem (of - z2)).
intros.
 assert (offsets ! to <> None) by eauto using path_defined_to.
 assert (valid_relative_pointer hierarchy afrom zfrom ar hyperreal i Class.Inheritance.Shared (base :: lf) to).
 econstructor.
 eassumption.
 assumption.
 assumption.
 eapply path_concat.
 eassumption.
 eassumption.
 reflexivity. 
 destruct (dynamic_align Hhier intro H25 Hoz Hoa H24 Hto).
 simpl in H26, H27.
       case_eq (offsets ! to); try congruence.
       intros.
       generalize (own_fields_offset_dynamic_low_bound (intro H28) Hto).
       simpl.
       intro.
       generalize (non_virtual_data_size_own_fields_offset (intro H28)). 
       intro.
       destruct (relative_pointer_data_incl intro H25 (dynamic_nonempty (c := COP) Hto) Hoz).
       generalize (H32 _ Hoa _ H28).
       intro.
       generalize (data_size_high_bound (intro Hoa)).
       intro.
       assert ((zfrom - 1) * size oa + size oa = zfrom * size oa) by ring.
refine (_ (Memory.store_some (val := val A (romty A) mblock)
(o := memop)
(v := valop (romty A) mblock vop')
_
(i := z1 + i * size ofto + z2 + (of - z2) + (z + 0 - of))
(mv := (Vptr A (romty:=romty A) mblock
    (hyperreal, (hr, pr), (Class.Inheritance.Shared, base :: lf))))
_
(memb := mbl)
(b := bl)
_
_
_
(memv := mva)
)).
simpl.
unfold valdata.
unfold type_of_value.
simpl.
intro.
match type of x2 with ?x <> None => case_eq x ; try congruence end.
clear x2.
intros.
2 : assumption.
2 : replace (
 z1 + i * size ofto + z2 + (of - z2) + (z + 0 - of)
) with (
  z1 + i * size ofto + z
) by omega.
2 : assumption.
2 : assumption.
2 : omega.
2 : simpl.
2 : unfold valdata, type_of_value; omega.

esplit.
esplit.
split.
eright.
econstructor.
eright.
econstructor.
eauto.
rewrite (sm_vptr0).
econstructor.
rewrite Hprog.
simpl.
eapply map_all_pvtable_complete.
eassumption.
eleft with (lt := nil).
reflexivity.
reflexivity.
simpl.
case_eq (hierarchy ! real); auto.
generalize (path_defined_to H9).
intros; contradiction.
rewrite reduce_path_trivial.
reflexivity.
eauto using is_dynamic_path.
rewrite Hprog.
Opaque vboffsets_l.
simpl.
rewrite reduce_path_trivial in H17.
eassumption.
eassumption.
rewrite Hprog.
simpl.
reflexivity.
rewrite Hprog.
simpl.
eapply Relations.Relation_Operators.rt_refl.
rewrite Hprog.
simpl.
unfold vtable_access_VBase.
destruct (vborder_list_ex Hhier real).
 destruct s.
 destruct e.
 destruct H37.
 eauto using virtual_base_vborder_list, path_is_virtual_base_of.
 edestruct (path_defined_to H9).
 assumption.
reflexivity.
eright.
econstructor.
eright.
econstructor.
eright.
econstructor.
rewrite PTree.gso.
eassumption.
congruence.
rewrite PTree.gss.
reflexivity.
eapply Zsem_semZ.
eassumption.
replace (z1 + i * size ofto + z2 + (of - z2) * 1
) with (z1 + i * size ofto + z2 + (of - z2)
) by ring.
reflexivity.
eright.
econstructor.
eright.
econstructor.
eright.
econstructor.
rewrite PTree.gso.
rewrite PTree.gso.
eauto.
congruence.
congruence.
rewrite sm_vtt0.
econstructor.
rewrite Hprog.
simpl.
eapply map_all_pvtt_complete.
eassumption.
eauto using is_dynamic_path.
rewrite Hprog.
simpl.
eapply pvtables_complete.
eassumption.
2 : eassumption.
assumption.
assumption.
rewrite Hprog. 
simpl.
eauto using path_last.
reflexivity.
eright.
econstructor.
eright.
econstructor.
rewrite PTree.gso.
rewrite PTree.gss.
reflexivity.
intro.
injection H37.
intro.
generalize (Plt_succ (Psucc nvcap)).
rewrite H38.
apply Plt_irrefl.
rewrite PTree.gss.
reflexivity.
reflexivity.
eassumption.
eleft.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
     repeat rewrite E0_left; eauto using evtr_sem.
     split.
     split.
     rewrite PTree.gso.
     rewrite PTree.gso.
     rewrite PTree.gso.
     auto.
     intro.
     injection H37.
     intro.
     destruct (Plt_irrefl nvcap).     
     rewrite H38 at 2.
     eapply Plt_trans.
     eapply Plt_succ.
     eapply Plt_succ.
     intro.
     injection H37.
     intro.
     destruct (Plt_irrefl nvcap).     
     rewrite H38 at 2.
     eapply Plt_trans.
     eapply Plt_succ.
     eapply Plt_succ.
     intro.
     injection H37.
     intro.
     destruct (Plt_irrefl nvcap).     
     rewrite H38 at 2.
     eapply Plt_succ.
    intros.
    rewrite PTree.gso.
    rewrite PTree.gso.
    rewrite PTree.gso.
    eauto.
    destruct v0; try congruence.
    intro.
    generalize (H37 _ H38).
    intro.
    destruct (Plt_irrefl nvcap).
    eapply Plt_trans.
    eapply Plt_succ.
    eapply Plt_trans.
    eapply Plt_succ.
    assumption.
    destruct v0; try congruence.
    intro.
    generalize (H37 _ H38).
    intro.
    destruct (Plt_irrefl nvcap).
    eapply Plt_trans.
    eapply Plt_succ.
    eapply Plt_trans.
    eapply Plt_succ.
    assumption.
    destruct v0; try congruence.
    intro.
    generalize (H37 _ H38).
    intro.
    destruct (Plt_irrefl nvcap).
    eapply Plt_trans.
    eapply Plt_succ.
    assumption.     
    split.
    erewrite Memory.load_store_same.
    reflexivity.
    eassumption.
    replace (
      z1 + i * size ofto + z
    ) with ( z1 + i * size ofto + z2 + (of - z2) + (z + 0 - of)
    ) by omega.
    eassumption.
   intros.
   eapply Memory.load_store_other.
   eassumption.
   eassumption.
    replace ( z1 + i * size ofto + z2 + (of - z2) + (z + 0 - of)
    ) with (      z1 + i * size ofto + z
    ) by omega.
   simpl.
   tauto.

Qed.

End Step.

  Lemma star_prop : forall l
    (Hl : forall h p, In (h, p) l ->
      p = reduce_path offsets p /\
      exists to, path hierarchy to p real h /\
        is_dynamic hierarchy to)   
    (env : PTree.t (val A (romty A) mblock))
    (Hismd : ismostderived = true -> ((hr, pr) = (Class.Inheritance.Repeated, hyperreal :: nil) \/ forall h p, In (h, p) l -> h = Class.Inheritance.Repeated))
    (Hinv : small_invariant env)
    (stl : list (stmt nativeop (romty A)))
    (mva : memvalues),
    exists env', exists mva',
      star _ (step (sem := sem) vop' memop prog tsp)
      (State (compile_set_vptr_list l (ismostderived)) stl env stack (Mem mbl mva))
      E0
      (State (skip _ _) stl env'  stack (Mem mbl mva')) /\
      small_invariant env' /\ (
      forall h p, In (h, p) l ->
        forall h' p'
          (Hhp' : (h', p') = concat (hr, pr) (h, p))
          oz
          (Hoz : relative_pointer_offset offsets afrom hyperreal ar i p' = Some oz),
          Memory.load memop (vop' Size (tyVptr _)) mbl mva' (bl, oz) = Some (Vptr (romty := romty A) _ _ (hyperreal, (hr, pr), (h, p)))
      ) /\
      (
        forall bl' o s, (bl' <> bl \/ (forall h p, In (h, p) l ->
          forall h' p'
            (Hhp' : (h', p') = concat (hr, pr) (h, p))
            oz
            (Hoz : relative_pointer_offset offsets afrom hyperreal ar i p' = Some oz),
            oz + vop' Size (tyVptr _) <= o \/ o + s <= oz
        )) ->
        Memory.load memop s mbl mva' (bl', o) =
          Memory.load memop s mbl mva (bl', o)
      )
      .
  Proof.
    induction l.

    (** nil *)
    intros.
    esplit.
    esplit.
    split.
    eleft.
    split; trivial.
    split.
     simpl; tauto.
    trivial.
    
    (** cons *)
    intros.
    rewrite compile_set_vptr_list_equation.
    destruct a.
    refine (_ (IHl _ _ _ _ (compile_set_vptr t l0 ismostderived :: stl) mva)).
    4 : eassumption.
    2 : auto.
    2 : intro; destruct (Hismd H); simpl in *; eauto.
    destruct 1.
    destruct H.
    destruct H.
    destruct H0.
    destruct H1.
    inversion Hptr; subst.
    generalize (Hl _ _ (or_introl _ (refl_equal _))).
    destruct 1.
    destruct H8.
    destruct H8.
    case_eq (concat (hr, pr) (t, l0)).
    intros.
    symmetry in H10.
    assert (
      valid_relative_pointer hierarchy afrom zfrom ar hyperreal i t0 l1 x1
    ).
     econstructor; eauto using path_concat.
    generalize (relative_pointer_offset_exist
Hhier intro guard (fun _ _ H => exis H) (Plt_succ _) H11).
    intro.
    match type of H12 with ?x <> None => case_eq x ; try congruence end.
    clear H12.
    intros.
    refine (_ (step_prop H9 H8 H7 H10 H12 _ H0 stl x0)).
    destruct 1.
    destruct H13.
    destruct H13.
    destruct H14.
    destruct H15.
    esplit.
    esplit.
    split.
    eright.
    econstructor.
    eapply star_trans.
    eapply evtr_sem.
    eassumption.
    eright.
    econstructor.
    eassumption.
    reflexivity.
    reflexivity.
    repeat rewrite E0_right; eauto using evtr_sem.
    split; trivial.
    split.
    intros.
    destruct (path_eq_dec (h, p) (t, l0)).
     congruence.
    inversion H17.
     congruence.
    eapply trans_equal.
    2 : eapply H1; eauto.
    apply H16.
    right.
    (** POPL 2011 theorem *)
    generalize (Hl _ _ (or_intror _ H18)).
    destruct 1.
    destruct H20.
    destruct H20.
    destruct (list_eq_dec peq p l0).
     subst p.
     generalize (Well_formed_hierarchy.path_eq_hierarchy_eq Hhier H8 H20).
     congruence.
    assert (reduce_path offsets p <> reduce_path offsets l0) by congruence.
    generalize (reduce_path_location_reduce_path_contents' H6 H20 H8 H22 Hhp' H10). (** KEY to use POPL'11 thm *)
    intros.
    assert (
     valid_relative_pointer hierarchy afrom zfrom ar hyperreal i h' p' x4
    ) by (econstructor; eauto using path_concat).
    assert (offsets ! x4 <> None) by eauto using path_defined_to.
    assert (offsets ! x1 <> None) by eauto using path_defined_to.
    generalize (
      reduce_path_dynamic_type_disjoint
      Hhier intro H24 H11 (or_intror _ H23) H25 H26 H21 H9 Hoz H12
    ).
    simpl; tauto.
   intros.
   eapply trans_equal.
   eapply H16.
   destruct H17; eauto.
  eapply H2.
  destruct H17; eauto.
 intro.
 destruct (Hismd H13); eauto.
Qed.

End Is_dynamic.



Definition compile_set_dynamic_type :=
  if is_dynamic_dec Hhier real
    then 
      seq 
      (
        (romop _ (Some (OldVar ovVTT)) (Target.vtable (romty := romty A) real (Class.Inheritance.Repeated, real :: nil)) (NewVar nvcap))
      )
      (
        compile_set_vptr_list (reduced_dynamic_paths Hhier offsets real) ismostderived
      )
    else
      exit _ _ O (** similar to NOP but a step is required. *)
      .

Variable  (sm_vtt : is_dynamic hierarchy real -> env0 ! (OldVar ovVTT) = Some (VTTptr (romty := romty A) _ _ (hyperreal, (hr, pr))))
   .

Variable Hismd : ismostderived = true -> ((hr, pr) = (Class.Inheritance.Repeated, hyperreal :: nil) \/ (forall b, is_virtual_base_of hierarchy b real -> False)).

Theorem compile_set_dynamic_type_correct : forall stl
      (mva : memvalues),
      exists env', exists mva',
        plus _ (step (sem := sem) vop' memop prog tsp)
        (State (compile_set_dynamic_type) stl env0 stack (Mem mbl mva))
        E0
        (State (skip _ _) stl env'  stack (Mem mbl mva')) /\
        small_invariant env' /\ (
          forall to, is_dynamic hierarchy to ->
            forall h p, path hierarchy to p real h ->
              forall h' p'
                (Hhp' : (h', p') = concat (hr, pr) (h, p))
                oz
                (Hoz : relative_pointer_offset offsets afrom hyperreal ar i p' = Some oz),
                Memory.load memop (vop' Size (tyVptr _)) mbl mva' (bl, oz) = Some (Vptr (romty := romty A) _ _ (hyperreal, (hr, pr), (h, reduce_path offsets p)))
        ) /\
        (
          forall bl' o s, (bl' <> bl \/ (forall to, is_dynamic hierarchy to ->
            forall h p, path hierarchy to p real h ->
              forall h' p'
                (Hhp' : (h', p') = concat (hr, pr) (h, p))
                oz
                (Hoz : relative_pointer_offset offsets afrom hyperreal ar i p' = Some oz),
                oz + vop' Size (tyVptr _) <= o \/ o + s <= oz
          )) ->
          Memory.load memop s mbl mva' (bl', o) =
            Memory.load memop s mbl mva (bl', o)
      )
      .
Proof.
  unfold compile_set_dynamic_type.
  destruct (is_dynamic_dec Hhier real).

  Focus 2.
  esplit.
  esplit.
  split.
  eapply plus_left.
  econstructor.
 eleft.
 repeat rewrite E0_left; eauto using evtr_sem.
 split.
  split.
  tauto.
  trivial.
 split.
  intros.
  destruct n.
  eauto using is_dynamic_path.
  trivial.

  inversion Hptr.
  subst.
  intros.
  refine (_ (star_prop
    (sm_vtt i0)
      (l := (reduced_dynamic_paths Hhier offsets real))
      (env := PTree.set (NewVar nvcap) (Vptr (romty := romty A) _ _ (hyperreal, (hr, pr), (Class.Inheritance.Repeated, real :: nil))) env0)
      _
      _
      _
      stl
      mva
    ))
    .
  destruct 1.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H5.
  esplit.
  esplit.
  split.
  eapply plus_left.
  econstructor.
  eright.
  econstructor.
  eauto.
  econstructor.
  rewrite Hprog.
  simpl.
  eapply map_all_pvtt_complete.
  eassumption.
  assumption.
  rewrite Hprog.
  Opaque pvtables.
  simpl.
  eapply pvtables_complete.
  eassumption.
  eassumption.
  eleft with (lt := nil).
  reflexivity.
  reflexivity.
  simpl.
  case_eq (hierarchy ! real).
  trivial.
  intros.
  edestruct path_defined_to.
  2 : eassumption.
  eassumption.
  rewrite reduce_path_trivial.
  reflexivity.
  rewrite Hprog.
  simpl.
  eauto using path_last.
  reflexivity.
 eright.
 econstructor.
 eassumption.
 reflexivity.
 reflexivity.
 repeat rewrite E0_left; eauto using evtr_sem.
 split; trivial.
 split.
  intros.
  functional inversion Hoz; subst.
  destruct (reduce_path_prefix offsets Hhier H8).
  destruct H9.
  destruct H9.
  destruct H13.
  destruct H14.
  case_eq (concat (hr, pr) (h, reduce_path offsets p)).
  intros.
  symmetry in H16.
  rewrite H14 in Hhp'.
  generalize (primary_subobject_offset_recip
    intro H15 H16 (path_last H9) Hhp' H12).
  intro.
  eapply H5.
  eapply reduced_dynamic_paths_complete.
  2 : erewrite (reduce_path_idem).
  2 : reflexivity.
  2 : eassumption.
  2 : eauto using path_nonempty.
  2 : eassumption.
  eauto using is_dynamic_path.
  eassumption.
  unfold relative_pointer_offset.
  rewrite H10.
  rewrite H11.
  rewrite H17.
  reflexivity.
 intros.
 destruct H7; eauto.
 eapply H6.
 right.
 intros.
 generalize (reduced_dynamic_paths_correct H8).
 destruct 1.
 destruct H9.
 destruct H10.
 eauto.
intros.
destruct (reduced_dynamic_paths_correct H3).
destruct H4.
destruct H5.
eauto.
intros.
destruct (Hismd H3); auto.
right.
intros.
destruct (reduced_dynamic_paths_correct H5).
destruct H6.
generalize (path_path1 H6).
inversion 1; subst.
 trivial.
edestruct H4; eauto.
split.
rewrite PTree.gss.
reflexivity.
intros.
rewrite PTree.gso.
reflexivity.
destruct v; try congruence.
intro.
injection H4; intro; subst.
generalize (H3 _ (refl_equal _)).
apply Plt_irrefl.
Qed.

End Common.

