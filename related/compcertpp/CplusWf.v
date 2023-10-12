(** CplusWf.v: Copyright 2010 Tahina Ramananandro *)

Require Import LibLists.
Require Export Cplusconcepts.
Require Import Coqlib.
Require Import Relations.
Require Import LibMaps.
Require Import Wellfounded.
Load Param.

(** A hierarchy is well-formed if, and only if, all the following conditions hold:
   - it is well-founded, i.e. for any classes B and C, if B is directly reachable from C (direct base, or type of scalar array field), then B < C
   - it is complete, i.e. for any classes B and C, if C is defined and if B is directly reachable from C, then B is defined

This module presents useful consequences of the well-formedness of a hierarchy
*)


Module Well_formed_hierarchy.  
  Section HH.
    Variable A : ATOM.t.
    Variable hierarchy : PTree.t (Class.t A).

    Record prop : Prop := intro {
      well_founded : forall ci c,
        PTree.get ci hierarchy = Some c ->
        forall h cisuper, In (h, cisuper) (Class.super c) -> 
          Plt cisuper ci 
          ;
      well_founded_struct : forall ci c,
        PTree.get ci hierarchy = Some c ->
        forall fi, In fi (Class.fields c) ->
          forall cl z, 
            FieldSignature.type fi = FieldSignature.Struct cl z ->
            Plt cl ci
            ;
      complete : forall ci c,
        PTree.get ci hierarchy = Some c ->
        forall h cisuper, In (h, cisuper) (Class.super c) ->
          PTree.get cisuper hierarchy <> None
          ;
      complete_struct : forall ci c,
        PTree.get ci hierarchy = Some c ->
        forall fi, In fi (Class.fields c) ->
          forall cl z, FieldSignature.type fi = FieldSignature.Struct cl z ->
            hierarchy ! cl <> None
            ;
    (** necessary for construction *)
      bases_no_dup : forall ci c,
        PTree.get ci hierarchy = Some c ->
        NoDup (Class.super c)
        ;
      fields_no_dup : forall ci c,
        PTree.get ci hierarchy = Some c ->
        NoDup (Class.fields c)
    }.

    Hint Resolve well_founded complete.

    Hypothesis hyp : prop.

(** * Well-foundedness properties *)
    
    Lemma is_virtual_base_of_defined_base :
      forall vb ci,
        is_virtual_base_of hierarchy vb ci ->
        hierarchy ! vb <> None.
    Proof.
      induction 1.
      eapply complete.
      auto.
      eassumption.
      eassumption.
      assumption.
    Qed.

    Lemma is_virtual_base_of_lt : 
      forall vb ci,
        is_virtual_base_of hierarchy vb ci ->
        Plt vb ci.
    Proof.
      destruct hyp.
      induction 1.
       eauto.
      eauto using Plt_trans.
    Qed.

    Corollary no_self_virtual_base : 
      forall ci, ~ is_virtual_base_of hierarchy ci ci.
    Proof.
      intros.
      intro.
      destruct (Plt_strict ci).
      eauto using is_virtual_base_of_lt.
    Qed.

    Lemma is_valid_repeated_subobject_le : 
      forall l a l',
        l = a :: l' ->
        forall z, LibLists.last l = Some z ->
          is_valid_repeated_subobject hierarchy l = true ->
          Ple z a.
    Proof.
      destruct hyp.
      induction l.
       congruence.
      injection 1 ; intros ; subst.
      revert H3.
      simpl.
      case_eq (hierarchy ! a0) ; try congruence.
      intros until 1.
      remember l' as l''.
      pattern l'' at 1.
      rewrite Heql''.
      destruct l'.
       subst ; simpl in *.
       intros.
       unfold Ple.
       injection H2 ; intros ; subst ; omega.
      destruct (
        In_dec super_eq_dec (Class.Inheritance.Repeated, i) (Class.super t)
      ); try congruence.
      intros.
      subst.
      replace (LibLists.last (a0 :: i :: l')) with (LibLists.last (i :: l')) in H2.
      apply Plt_Ple.
      eauto using Ple_Plt_trans.
      change (a0 :: i :: l') with ((a0 :: nil) ++ i :: l').
      rewrite last_app_left.
      trivial.
      congruence.
    Qed.             

    Corollary path_le :  
      forall to k from p,
        path hierarchy to k from p ->
        Ple to from.
    Proof.
     intros.
     generalize (path_path0 H).
     inversion 1.
      subst.
      symmetry in H2.
      eapply is_valid_repeated_subobject_le.
      eexact H2.
      apply last_complete.
      congruence.
     subst.
     symmetry in H3.
     apply Plt_Ple.
     eapply Ple_Plt_trans.
      eapply is_valid_repeated_subobject_le.
      eexact H3.
      apply last_complete.
      congruence.
     eauto using is_virtual_base_of_lt.
   Qed. 

   Corollary path_base_le : forall to k from a p,
        path hierarchy to (a :: k) from p ->
        Ple to a.
    Proof.
      intros.
      generalize (path_path1 H).
      inversion 1; subst.
       injection H1; intros; subst; eauto using path_le.
      inversion H2; subst.
      injection H3; intros; subst; eauto using path_le.
    Qed.

   Lemma self_path_trivial : forall from k p,
     path hierarchy from p from k ->
     (k, p) = (Class.Inheritance.Repeated, from :: nil).
   Proof.
     intros.
     generalize (path_path2 H).
     inversion 1.
      trivial.
     generalize (well_founded hyp H1 H2).
     intros.
     generalize (path_le (path2_path H3)).
     intros.
     destruct (Plt_strict interm).
     eauto using Plt_Ple_trans.
     generalize (well_founded hyp H1 H2).
     intros.
     generalize (path_le (path2_path H3)).
     intros.
     destruct (Plt_strict interm).
     eauto using Plt_Ple_trans.
     generalize (well_founded hyp H1 H2).
     intros.
     generalize (path_le (path2_path H3)).
     intros.
     destruct (Plt_strict interm).
     eauto using Plt_Ple_trans.
   Qed.
     

Lemma categorize_paths :
  forall to via from,
  forall kind, path hierarchy to via from kind ->
  forall h q, via = h :: q ->
    (h = from <-> kind = Class.Inheritance.Repeated).
Proof.
  intros until h.
  revert h.
  generalize (path_path2 H).
  clear H.
  induction 1.
   injection 1 ; intros ; subst.
   tauto.
  injection 1 ; intros ; subst.
  tauto.
  intros.
  subst.
  split.
   intros.
   subst.
   generalize (IHpath2 _ _ (refl_equal _)).
   destruct 1.
   destruct h.
   generalize (H3 (refl_equal _)).
   intros ; subst.
   destruct (@no_self_virtual_base interm).
   eleft.
   eassumption.
   assumption.
   generalize (path_path0 (path2_path H1)).
   inversion 1.
    subst.
   injection H6 ; intros ; subst.
   destruct (@no_self_virtual_base base).
   eapply is_virtual_base_of_trans.
   eleft.
   eassumption.
   eassumption.
   assumption.
  intros ; discriminate.
  intros ; subst.
  split ; intros ; try discriminate.
  subst.
  generalize (IHpath2 _ _ (refl_equal _)).
  destruct 1.
  generalize (path_path0 (path2_path H1)).
   inversion 1.
    subst.
   injection H6 ; intros ; subst.
   destruct (@no_self_virtual_base base).
   eright.
   eassumption.
   eassumption.
   assumption.
Qed.

Corollary path_eq_hierarchy_eq : forall p h1 from to1,
  path hierarchy to1 p from h1 ->
  forall to2 h2, path hierarchy to2 p from h2 ->
    h1 = h2.
Proof.
  intros.
  generalize (path_last H).
  destruct p; simpl; try congruence.
  intros _.
  generalize (categorize_paths H (refl_equal _)).
  destruct 1.
  generalize (categorize_paths H0 (refl_equal _)).
  destruct 1.
  destruct h1; destruct h2; eauto; symmetry; eauto.
Qed.

Lemma is_valid_repeated_subobject_sorted : forall l,
  is_valid_repeated_subobject hierarchy l = true ->
  LibLists.sorted (fun a b => Plt b a) l.
Proof.
  induction l ; simpl.
   congruence.
  case_eq (hierarchy ! a) ; try congruence.
  intros until 1.
  remember l as m.
  pattern m at 2.
  rewrite Heqm.
  destruct m ; simpl.
   intros ; constructor.
  destruct (
    In_dec super_eq_dec (Class.Inheritance.Repeated, i) (Class.super t)
  ) ; try congruence.
  intros.
  generalize (well_founded hyp H i0).
  intros.
  constructor.
  assumption.
  subst.
  auto.
Qed.
 
Lemma array_path_le : forall via to to_n from from_n,
  valid_array_path hierarchy to to_n from from_n via ->
  Ple to from.
Proof.
  induction 1.
   apply Ple_refl.
  eapply Ple_trans.
  eassumption.
  eapply Plt_Ple.
  eapply Plt_Ple_trans.
  eauto using well_founded_struct.
  eauto using path_le.
Qed.

Lemma array_path_valid : forall via to to_n from from_n,
  valid_array_path hierarchy to to_n from from_n via ->
  hierarchy ! from <> None ->
  hierarchy ! to <> None.
Proof.
  induction 1; eauto using complete_struct.
Qed.  

(** * Construction of the list of (direct or indirect) virtual bases *)
 
Function primary_virtual_bases (l : list (Class.Inheritance.t * ident)) : list ident :=
match l with
  | nil => nil
  | (Class.Inheritance.Shared, ci) :: q =>
    ci :: primary_virtual_bases q
  | _ :: q => primary_virtual_bases q
end.


Lemma primary_virtual_bases_correct : forall b l,
  In b (primary_virtual_bases l) -> In (Class.Inheritance.Shared, b) l.
Proof.
  induction l ; simpl.
  tauto.
  destruct a.
  destruct t.
  eauto.
  simpl.
  inversion 1.
   subst.
   eauto.
   eauto.
Qed.

Lemma primary_virtual_bases_complete : forall l b,
  In (Class.Inheritance.Shared, b) l -> In b (primary_virtual_bases l).
Proof.
  induction l; simpl; eauto.
  inversion 1 ; subst; eauto.
  destruct a ; simpl.
  destruct t ; simpl ; eauto.
Qed.

Lemma virtual_bases_step : forall n t,
  (forall i, Plt i n -> t ! i <> None) ->
  (forall i l, t ! i = Some l -> forall j, In j l <-> is_virtual_base_of hierarchy j i) ->
  {l : _ & forall j, In j l <-> is_virtual_base_of hierarchy j n}.
Proof.
 intros.
 case_eq (t ! n).
  intros.
  exists l.
  auto.
 intros _.
 case_eq (hierarchy ! n).
 Focus 2.
  intros.
  exists (@nil ident).
  simpl.
  split.
   tauto.
  inversion 1 ; congruence.
 intros.
 exists (
   merge
   peq
   plt
   (merge_sort peq plt (primary_virtual_bases (Class.super t0)))
   (flatten_merge 
     peq
     plt
     (List.map
       (fun i : _ * _ =>
         let (_, j) := i in
         match t ! j with
           | None => nil
           | Some l => l
         end)
       (Class.super t0)
     )
   )
 ).
 intros.
 split.
  intros.
  destruct (in_app_or _ _ _ (merge_elim H2)).
   eleft.
   eassumption.
   apply primary_virtual_bases_correct.
   apply (merge_sort_elim (peq := peq) (plt := plt)).
   assumption.
  destruct (LibLists.member_flatten_elim (flatten_merge_elim H3)).
  destruct H4.
  destruct (LibLists.map_elim H4).
  clear H4.
  destruct H6.
  subst.
  destruct x0.
  case_eq (t ! p).
   Focus 2.
   intros.
   rewrite H6 in *.
   inversion H5.
  intros.
  rewrite H6 in *.
  destruct (H0 _ _ H6 j).
  eright.
  eassumption.
  eassumption.
  auto.
 intros.
 apply merge_intro.
 apply in_or_app.
 inversion H2.
  subst.
  left.
  apply merge_sort_intro.
  apply primary_virtual_bases_complete.
  congruence.
 right.
 replace t0 with c in * by congruence.
 subst.
 generalize (well_founded hyp H1 H4).
 intros.
 generalize (H _ H6).
 intros.
 case_eq (t ! bi') ; try congruence.
 intros.
 destruct (H0 _ _ H8 j).
 generalize (H10 H5).
 intros.
 apply flatten_merge_intro.
 eapply LibLists.member_flatten_intro.
 2 : eassumption.
 eapply LibLists.map_intro.
 eassumption.
 simpl.
 rewrite H8.
 trivial.
Qed.

Theorem virtual_bases :
  {t |
    (forall cn,
      hierarchy ! cn <> None -> t ! cn <> None) /\
    forall cn l, t ! cn = Some l ->
      forall i, (In i l <-> is_virtual_base_of hierarchy i cn)
  }.
Proof.
  generalize (max_index hierarchy).
  destruct 1.
  destruct (progressive virtual_bases_step x).
  destruct p0.
  exists x0.
  eauto.
Qed.

(** * Construction of the list of all paths reachable from classes *)

Section Path_to.

Variable to : ident.

Lemma path_to_step : forall n t, (forall i, Plt i n -> t ! i <> None) ->
  (forall i l, t ! i = Some l -> forall kp : _ * _, In kp l <-> let (k, p) := kp in path hierarchy to p i k) ->
  {l : _ & forall kp : _ * _, In kp l <-> let (k, p) := kp in path hierarchy to p n k}.
Proof.
 intros.
 case_eq (hierarchy ! n).
  intros.
  destruct (peq n to).
   subst.
   exists ((Class.Inheritance.Repeated, (to :: nil)) :: nil).
   intros.
   split.
   simpl.
   inversion 1 ; try tauto.
   subst.
   apply path2_path.
   constructor.
   congruence.
   intros.
   destruct kp.
   generalize (path_path2 H2).
   inversion 1.
    auto.
   generalize (path2_path H6).
   intros.   
   generalize (well_founded hyp H4 H5).
   intros.
   generalize (path_le H10).
   intros.
   destruct (Plt_strict interm).
   eauto using Plt_Ple_trans.
   subst.
   generalize (path2_path H6).
   intros.   
   generalize (well_founded hyp H4 H5).
   intros.
   generalize (path_le H7).
   intros.
   destruct (Plt_strict interm).
   eauto using Plt_Ple_trans.
   subst.
   generalize (path2_path H6).
   intros.   
   generalize (well_founded hyp H4 H5).
   intros.
   generalize (path_le H7).
   intros.
   destruct (Plt_strict interm).
   eauto using Plt_Ple_trans.
  (* n <> to *)   
   exists (LibLists.flatten 
     (List.map
       (fun kc : _ * _ =>
         let (k, c) := kc in
           List.map
           (concat (k, match k with
                         | Class.Inheritance.Repeated => (n :: c :: nil)
                         | Class.Inheritance.Shared => c :: nil
                       end
           ))
           (match t ! c with
              | Some l => l
              | _ => nil
            end)
       )
       (Class.super t0)
     )
   ).
   intros.
   destruct kp.
   simpl.
   split.
   intros.
   generalize (LibLists.member_flatten_elim H2).
   clear H2.
   destruct 1.
   destruct H2.
   destruct (in_map_iff    (fun kc : Class.Inheritance.t * positive =>
             let (k, c) := kc in
             map
               (concat
                  (k,
                  match k with
                  | Class.Inheritance.Repeated => n :: c :: nil
                  | Class.Inheritance.Shared => c :: nil
                  end))
               match t ! c with
               | Some l => l
               | None => nil (A:=Class.Inheritance.t * list ident)
               end) (Class.super t0) x).
   clear H5.
   destruct (H4 H2).
   clear H4 H2.
   destruct x0.
   destruct H5.
   subst.
   generalize (well_founded hyp H1 H4).
   intros.
   generalize (H _ H2).
   intros.
   case_eq (t ! p) ; try congruence.
   intros.
   rewrite H6 in H3.
   destruct (in_map_iff
       (concat
               (t2,
               match t2 with
               | Class.Inheritance.Repeated => n :: p :: nil
               | Class.Inheritance.Shared => p :: nil
               end))         
       l0 (t1, l)
   ).
   clear H8.
   generalize (H7 H3).
   clear H7 H3.
   destruct 1.
   destruct H3.
   eapply path2_path.
   cut (let (t1', l') :=  (
      concat
         (t2,
         match t2 with
         | Class.Inheritance.Repeated => n :: p :: nil
         | Class.Inheritance.Shared => p :: nil
         end) x 
   )
 in path2 hierarchy to l' n t1').
   rewrite H3.
   tauto.
   destruct x.
   eapply path2_concat.
   eapply path_path2.
   eapply path_elem.
   eassumption.
   assumption.
   eauto using complete.
   destruct (H0 _ _ H6 (t3, l1)).
   apply path_path2.
   auto.

 (* reciprocally *)
 intros.
 generalize (path_path2 H2).
 intros.
 destruct (
   path2_concat_recip H3
 ).
  destruct H4 ; contradiction.
 generalize (H4 _ H1).
 clear H4.
 destruct 1.
 destruct H4.
 destruct H4.
 destruct H4.
 destruct H4.
 destruct H5.
 generalize (well_founded hyp H1 H4).
 intros.
 generalize (H _ H7).
 intros.
 case_eq (t ! x) ; try congruence.
 intros.
 destruct (H0 _ _ H9 (x1, x2)).
 clear H10.
 generalize (H11 (path2_path H5)).
 intros.
 rewrite H6. 
 eapply LibLists.member_flatten_intro.
 Focus 2.
  eapply (in_map
    (concat
        (x0,
        match x0 with
        | Class.Inheritance.Repeated => n :: x :: nil
        | Class.Inheritance.Shared => x :: nil
        end)
    )
  ).
  eassumption.
  replace l0 with (match t ! x with Some l1 => l1 | None => nil end).
  remember (x0, x) as kc.
  replace (
    (map
        (concat
           (x0,
           match x0 with
           | Class.Inheritance.Repeated => n :: x :: nil
           | Class.Inheritance.Shared => x :: nil
           end))
        match t ! x with
        | Some l1 => l1
        | None => nil (A:=Class.Inheritance.t * list ident)
        end)
  ) with (
    let (x0, x) := kc in
    (map
        (concat
           (x0,
           match x0 with
           | Class.Inheritance.Repeated => n :: x :: nil
           | Class.Inheritance.Shared => x :: nil
           end))
        match t ! x with
        | Some l1 => l1
        | None => nil (A:=Class.Inheritance.t * list ident)
        end)
  ).
 eapply (in_map  (fun kc : Class.Inheritance.t * positive =>
         let (k, c) := kc in
         map
           (concat
              (k,
              match k with
              | Class.Inheritance.Repeated => n :: c :: nil
              | Class.Inheritance.Shared => c :: nil
              end))
           match t ! c with
           | Some l1 => l1
           | None => nil (A:=Class.Inheritance.t * list ident)
           end) ).
  subst.
  assumption.
  subst.
  reflexivity.
  rewrite H9.
  reflexivity.

(* hierarchy = none *)
intros.
exists (@nil (Class.Inheritance.t * list ident)).
simpl.
intros.
split.
tauto.
destruct kp.
intros.
generalize (path_path2 H2).
 inversion 1 ; congruence.
Qed.

Theorem path_to :
  {t |
    (forall cn,
      hierarchy ! cn <> None -> t ! cn <> None) /\
    forall cn l, t ! cn = Some l ->
      forall i : _ * _, (In i l <-> let (k, p) := i in path hierarchy to p cn k)
  }.
Proof.
  generalize(max_index hierarchy).
  destruct 1.
  destruct (progressive path_to_step x).
  destruct p0.
  exists x0.
  eauto.
Qed.

End Path_to.

Theorem paths :
  {T | (forall cn0,
    hierarchy ! cn0 <> None -> T ! cn0 <> None) /\
    forall cn0 t, T ! cn0 = Some t ->
      (forall cn,
        hierarchy ! cn <> None -> t ! cn <> None) /\
      forall cn l, t ! cn = Some l ->
        forall i : _ * _, (In i l <-> let (k, p) := i in path hierarchy cn0 p cn k)
  }.
Proof.
  generalize(max_index hierarchy).
  destruct 1.
  destruct (progressive (fun n _ _ _ => let (o, h) := path_to n in existT _ o h) x).
  destruct p0.
  exists x0.
  eauto.
Qed.


Lemma path_eq_dec : forall kp1 kp2 : Class.Inheritance.t * list ident,
  {kp1 = kp2} + {kp1 <> kp2}.
Proof.
  repeat decide equality.
Qed.

Lemma concat_path_unique : forall to via from by,
  path hierarchy to via from by ->
  forall to' via' by',
    path hierarchy to' via' from by' ->
    forall h p ofrom, path hierarchy from p ofrom h ->
      forall h, concat (h, p) (by, via) = concat (h, p) (by', via') ->
        (by, via) = (by', via').
Proof.
  intros until 1.
  generalize (path_path1 H).
  inversion 1; subst.
   intros until 1.
   generalize (path_path1 H1).
   inversion 1; subst; intros until 1; simpl.
    rewrite (path_last H5).
    destruct (peq from from); try congruence.
    injection 1; intros; subst.
    rewrite (app_reg_l H9).
    trivial.
   rewrite (path_last H7).
   destruct (peq from from); try congruence.
   inversion H6; subst.
   destruct p.
    generalize (path_nonempty H7); congruence.
   injection 1; intros; subst.
   destruct (Plt_irrefl base).
   eapply Plt_Ple_trans.
   eauto using is_virtual_base_of_lt.
   eauto using path_base_le.
  intros until 1.
  generalize (path_path1 H3).
  inversion 1; subst; intros until 1; simpl.
   rewrite (path_last H5).
   destruct (peq from from); try congruence.
   inversion H2; subst.
   destruct p.
    generalize (path_nonempty H5); congruence.
   injection 1; intros; subst.
   destruct (Plt_irrefl i).
   eapply Plt_Ple_trans.
   eauto using is_virtual_base_of_lt.
   eauto using path_base_le.
  tauto.
Qed.

Lemma path_is_base_dec : forall to via from by,
  path hierarchy to via from by ->
  forall to' via' by',
    path hierarchy to' via' from by' ->
    {via1 : _ & {by1 | path hierarchy to' via1 to by1 /\ (by', via') = concat (by, via) (by1, via1)}} + {
      forall via1 by1, path hierarchy to' via1 to by1 -> (by', via') <> concat (by, via) (by1, via1)
    }.
Proof.
  intros.
  destruct (path_to to').
  destruct a.  
  case_eq (x ! to).
   intros.
   case_eq (filter (fun hp => if path_eq_dec (by', via') (concat (by, via) hp) then true else false) l).
    intros.
    right.
    intros.
    intro.
    change False with (In (by1, via1) nil).
    rewrite <- H4.
    eapply filter_In.
    split.
    eapply H2.
    eassumption.
    assumption.
    destruct (
      path_eq_dec (by', via') (concat (by, via) (by1, via1))
    ); try contradiction.
    trivial.
   intros.
   assert (In p (p :: l0)) by auto.
   rewrite <- H4 in H5.
   destruct (let (J, _) := filter_In _ _ _ in J H5).
   destruct (
path_eq_dec (by', via') (concat (by, via) p)
   ); try discriminate.   
   destruct p.
   left.
   esplit.
   esplit.
   split.
   generalize (let (J, _) := H2 _ _ H3 _ in J H6).
   intro.
   eassumption.
   assumption.
 intro.
 apply False_rect.
 generalize (H1 _ (path_defined_to H)).
 intro; contradiction.
Qed.


(** * Dynamic cast *)

Lemma dynamic_cast_unique : forall real rk rp from to k1 p1,
  dynamic_cast hierarchy real rk rp from to k1 p1 ->
  forall k2 p2,
    dynamic_cast hierarchy real rk rp from to k2 p2 ->
    (k1, p1) = (k2, p2)
.
Proof.
  intros real rk rp from to.
  cut (forall k1 p1 n1,
    dynamic_cast_aux hierarchy real rk rp from to k1 p1 n1 ->
    forall k2 p2 n2,
      dynamic_cast_aux hierarchy real rk rp from to k2 p2 n2 ->
      (n1 <= n2)%nat ->
      (k1, p1) = (k2, p2)      
  ).
  intros.
  destruct (dynamic_cast_dynamic_cast_aux H0).
  destruct (dynamic_cast_dynamic_cast_aux H1).
  destruct (le_lt_dec x x0).
   eauto.
  assert (x0 <= x)%nat by omega.
  symmetry.
  eauto.

  inversion 1 ; subst ; simpl ;
  inversion 1 ; subst ; simpl ;
    intros ; try omegaContradiction.

  generalize (H2 _ _ H6).
  congruence.

  generalize (path_le H1).
  intros.
  generalize (path_le H6).
  intros.
  generalize (Ple_antisym H9 H10).
  intros ; subst.
  generalize (self_path_trivial H1).
  injection 1 ; intros ; subst.
  generalize (self_path_trivial H6).
  injection 1 ; intros ; subst.
  rewrite H7 in H3.
  rewrite concat_assoc in H3.
  simpl in H3.
  destruct (peq from from) ; try congruence.
  injection H3 ; intros ; subst.
  generalize (path_last H5).
  intros.
  rewrite H13.
  destruct (peq from from) ; try congruence.
  rewrite <- app_nil_end.
  trivial.

  generalize (path_concat H0 H1 H3).
  intros.
  eauto.

  rewrite H6 in H2.
  simpl in H2.
  injection H2 ; intros ; subst.
  simpl in H6.
  injection H6 ; intros ; subst.
  generalize (path_last H4).
  intros.
  inversion H5.
  subst.
  unfold plus in *.
  rewrite H9 in *.
  destruct (peq to to) ; try congruence.
  generalize (path_last H0).
  intros.
  rewrite H10 in *.
  inversion H1.
  subst.
  destruct (peq to to) ; try congruence.
  generalize (path_path0 H0).
  generalize (path_path0 H4).
  inversion 1.
   subst.
   inversion 1.
   subst.
   rewrite H17 in H8.
   rewrite H20 in H8.
   rewrite app_ass in H8.
   rewrite app_ass in H8.
   simpl in H8.
  generalize (is_valid_repeated_subobject_sorted H18).
  intro.
  rewrite H17 in H19.
  generalize (is_valid_repeated_subobject_sorted H12).
  intro.
  generalize (sorted_join_common H19 H22).
  intros.
  generalize (sorted_elim Plt_trans H23).
  intros.
  generalize (sorted_decomp_unique Plt_strict H24 (refl_equal _) H8).
  injection 1 ; intros ; subst.
  congruence.

  subst.
  inversion 1 ; intros ; subst.
  simpl in H8.
  injection H8 ; intros ; subst.
  change (base0 :: lf1 ++ lf) with ((base0 :: lf1) ++ lf) in H8.
  change (base0 :: lf2 ++ lf0) with ((base0 :: lf2) ++ lf0) in H8.
  rewrite H18 in H8.
  rewrite H22 in H8.
  rewrite app_ass in H8.
  rewrite app_ass in H8.
  simpl in H8.
  generalize (is_valid_repeated_subobject_sorted H19).
  intros.
  rewrite H18 in H24. 
  generalize (is_valid_repeated_subobject_sorted H12).
  intros.
  generalize (sorted_join_common H24 H25).
  intros.
  generalize (sorted_elim Plt_trans H26).
  intros.
  generalize (sorted_decomp_unique Plt_strict H27 (refl_equal _) H8).
  congruence.

  auto.

  auto.

Qed.


Lemma dynamic_cast_dec : forall real real_inheritance real_path from cast,
  {cast_inheritance : _ & {cast_path | dynamic_cast hierarchy real real_inheritance real_path from cast cast_inheritance cast_path}} +
  {forall cast_inheritance cast_path, dynamic_cast hierarchy real real_inheritance real_path from cast cast_inheritance cast_path -> False}.
Proof.
  intros.

  case_eq (hierarchy ! real).
  Focus 2.
   intros.
   right.
   inversion 1.
    generalize (path_defined_from H1).
    congruence.
    generalize (path_defined_from H1).
    congruence.
    generalize (path_defined_from H1).
    congruence.
  intros.
  case_eq (hierarchy ! cast).
  Focus 2.
   intros.
   right.
   inversion 1.
    generalize (path_defined_to H3).
    congruence.
    generalize (path_defined_to H2).
    congruence.
    generalize (path_defined_to H3).
    congruence.
  intros.
  assert (hierarchy ! cast <> None) by congruence.
  assert (hierarchy ! real <> None) by congruence.
  destruct paths.
  destruct a.
  generalize (H3 _ H1).
  intros.
  case_eq (x ! cast) ; try congruence.
  intros.
  destruct (H4 _ _ H6).
  generalize (H7 _ H2).
  intros.
  case_eq (t1 ! real) ; try congruence.
  intros.
  case_eq (hierarchy ! from).
  Focus 2.
   intros.
   right.
   inversion 1.
    generalize (path_defined_to H13).
    congruence.
    generalize (path_defined_to H14).
    congruence.
    generalize (path_defined_to H13).
    congruence.
  intros.
  assert (hierarchy ! from <> None) by congruence.
  generalize (H3 _ H12).
  intros.
  case_eq (x ! from) ; try congruence.
  intros.
  destruct (H4 _ _ H14).  
  generalize (H15 _ H2).
  intros.
  case_eq (t3 ! real) ; try congruence.
  intros.
  generalize (H16 _ _ H18).
  intros.
  destruct (H19 (real_inheritance, real_path)).
  destruct (In_dec path_eq_dec (real_inheritance, real_path) l0).
   Focus 2.
   intros.
   right.
   inversion 1.
    generalize (H21 H23).
    assumption.
    generalize (path_concat H23 H24 H25).
    intros.
    generalize (H21 H26).
    assumption.
    generalize (H21 H23).
    assumption.
  generalize (H20 i).
  intros.
  destruct (at_most_list path_eq_dec l).
   assert (
     forall a b, {
        (real_inheritance, real_path) = concat a b /\ exists c, b = (Class.Inheritance.Repeated, c)
     } + { ~  (
       (real_inheritance, real_path) = concat a b /\ exists c, b = (Class.Inheritance.Repeated, c)
     ) }
   ).
   destruct b.
    destruct t4.
    destruct (path_eq_dec (real_inheritance, real_path) (concat a (Class.Inheritance.Repeated, l1)) ).
    left.
    split.
    assumption.
    esplit.
    reflexivity.
    right.
    intro.
    destruct H23.
    contradiction.
    right.
    intro.
    destruct H23.
    destruct H24.
    discriminate.
   generalize (H15 _ H1).
   intros.
   case_eq (t3 ! cast) ; try congruence.
   intros.
   generalize (H16 _ _ H25).
   intros.
   destruct (
     list_product H23 l l1
   ).
   destruct x0.
    simpl in *.
     intros.
     generalize (H7 _ H12).
     intros.
     case_eq (t1 ! from) ; try congruence.
     intros.
     generalize (H8 _ _ H28).
     intros.
     destruct l2.
      simpl in *.
      right.
      inversion 1.
       destruct (H29 (k, p)).
       contradiction.
       destruct (H26 (Class.Inheritance.Repeated, p)).
       generalize (H35 H32).
       intros.
       generalize (H8 _ _ H10).
       intros.
       destruct (H37 (cast_inheritance, cast_path)).
       generalize (H39 H31).
       intros.
       destruct (i0 (cast_inheritance, cast_path) (Class.Inheritance.Repeated, p)).
       apply H42.
       split ; try assumption.
       split ; try assumption.
       split ; try assumption.
       esplit ; reflexivity.
       destruct s.
       destruct s.
       destruct a.
       destruct H35.
       destruct H36.
       generalize (H8 _ _ H10).
       intros.
       destruct (H36 x0).
       destruct (H36 x1).
       destruct x0.
       destruct x1.
       transitivity (cast_inheritance, cast_path).
       eauto.
       symmetry.
       eauto.
     destruct (at_most_list path_eq_dec (p :: l2)).
      right.
      inversion 1.
      destruct s0.
      destruct s0.
      destruct a.
      destruct H36.
      destruct (H29 x0).
      destruct (H29 x1).
      destruct x0.
      destruct x1.
      destruct H37.
      transitivity (k, p0).
      symmetry.
      eauto.
      eauto.
       destruct (H26 (Class.Inheritance.Repeated, p0)).
       generalize (H35 H32).
       intros.
       generalize (H8 _ _ H10).
       intros.
       destruct (H37 (cast_inheritance, cast_path)).
       generalize (H39 H31).
       intros.
       destruct (i0 (cast_inheritance, cast_path) (Class.Inheritance.Repeated, p0)).
       apply H42.
       split ; try assumption.
       split ; try assumption.
       split ; try assumption.
       esplit ; reflexivity.
       destruct s.
       destruct s.
       destruct a.
       destruct H35.
       destruct H36.
       generalize (H8 _ _ H10).
       intros.
       destruct (H36 x0).
       destruct (H36 x1).
       destruct x0.
       destruct x1.
       transitivity (cast_inheritance, cast_path).
       eauto.
       symmetry.
       eauto.
     destruct p.
     destruct (H29 (t4, l3)).
     simpl in H30.
     generalize (H30 (or_introl _ (refl_equal _))).
     intros.
     case_eq (concat (real_inheritance, real_path) (t4, l3)).
      intros.
      symmetry in H33.    
     left.
     exists t5.
     exists l4.
     eapply dynamic_cast_upcast.
     assumption.
     eassumption.
     intros.
     apply e.
     simpl ; auto.
     destruct (H29 (k', p')).
     auto.
     assumption.
  destruct p.
  simpl in *.
  destruct (i0 p p0).
  destruct (H27 (or_introl _ (refl_equal _))).
  destruct H30.
  destruct H31.
  destruct p0.
  destruct t4.
   Focus 2.
   apply False_rect.
   destruct H32.
   discriminate.
  destruct p.
  generalize (H8 _ _ H10).
  intros.
  destruct (H33 (t4, l3)).
  destruct (H26 (Class.Inheritance.Repeated, l2)).
  left.
  exists t4.
  exists l3.
  eapply dynamic_cast_downcast.
  eauto.
  eauto.
  assumption.
 generalize (H8 _ _ H10).
 intros.
 destruct l.
  simpl in *.
  right.
  inversion 1.
   generalize (path_concat H25 H26 H28).
   intros.
   destruct (H23 (cast_inheritance, cast_path)).
   eauto.
   destruct (H23 (cast_inheritance, cast_path)).
   eauto.
   destruct (H23 (cast_inheritance, cast_path)).
   eauto.
 destruct p.
 simpl in *.
 destruct (H23 (t4, l1)).
 generalize (H24 (or_introl _ (refl_equal _))).
 intros.
 left.
 exists t4.
 exists l1.
 eapply dynamic_cast_crosscast.
 assumption.
 assumption.
 intros.
 apply e.
 destruct (H23 (k, p)).
 eauto.
 auto.
Qed.


Lemma dynamic_cast_base_static_cast : forall real rh rp from cast ch cp, dynamic_cast hierarchy real rh rp from cast ch cp ->
  forall h' p', path hierarchy cast p' from h' ->
    static_cast  hierarchy real rh rp from cast ch cp.
Proof.
  inversion 1; subst.
  intros; eleft.
  assumption.
  eexact H1.
  assumption.
  assumption.
 intros.
 generalize (path_le H3).
 intro.
 generalize (path_le H1).
 intro.
 generalize (Ple_antisym H4 H5).
 intros; subst.
 generalize (self_path_trivial H1).
 injection 1; intros; subst.
 simpl in H2.
 rewrite (path_last H0) in H2.
 destruct (peq from from); try congruence.
 rewrite <- app_nil_end in H2.
 injection H2; intros; subst.
 eleft.
 assumption.
 eexact H1.
 intros.
 generalize (self_path_trivial H7).
 congruence.
 simpl.
 rewrite <- app_nil_end.
 rewrite (path_last H0).
 destruct (peq from from); congruence.
intros.
generalize (path_concat H0 H3).
case_eq (concat (rh, rp) (h', p')).
intros.
generalize (H2 _ _ (H5 _ _ (refl_equal _))).
injection 1; intros; subst.
symmetry in H4.
eleft.
assumption.
eassumption.
2 : assumption.
intros.
generalize (path_concat H0 H7).
case_eq (concat (rh, rp) (k', p'0)).
intros.
symmetry in H8.
generalize (H2 _ _ (H9 _ _ (refl_equal _))).
injection 1; intros; subst.
clear H2 H5 H6 H9 H10.
revert h' p' H3 H4 k' p'0 H7 H8 .
cut (
forall (h' : Class.Inheritance.t) (p' : list ident),
   path (A:=A) hierarchy cast p' from h' ->
   (ch, cp) = concat (rh, rp) (h', p') ->
   forall (k' : Class.Inheritance.t) (p'0 : list ident), (k' = Class.Inheritance.Shared -> h' = Class.Inheritance.Shared) ->
   path (A:=A) hierarchy cast p'0 from k' ->
   (ch, cp) = concat (rh, rp) (k', p'0) -> (h', p') = (k', p'0)
).
 intros.
 destruct h'; destruct k'; eauto; symmetry; eauto.
intros. 
generalize (path_path1 H2).
generalize (path_path1 H5).
inversion 1; subst.
 simpl in H6.
 rewrite (path_last H0) in H6.
 destruct (peq from from); try congruence.
 inversion 1; subst.
  simpl in H3.
  rewrite (path_last H0) in H3.
  destruct (peq from from); try congruence.
  injection H6; intros; subst.
  injection H3; intro.
  generalize (app_reg_l H11).
  congruence.
 simpl in H3.
 injection H3; intros; subst.
 injection H6; intros; subst.
 generalize (path_path1 H0).
 inversion 1; subst.
 inversion H15; subst.
 simpl in H12; inversion H12; subst.
 injection H16; intros; subst.
 destruct (Plt_irrefl base).
 eapply Plt_Ple_trans.
 eapply is_virtual_base_of_lt.
 eapply H11.
 eauto using path_le.
generalize (H4 (refl_equal _)).
intros; subst.
simpl in H3.
simpl in H6.
congruence.
Qed.

Lemma ambiguous_base_no_static_cast : forall from cast h1 p1,
  path hierarchy cast p1 from h1 ->
  forall p2 h2,   path hierarchy cast p2 from h2 ->
    (h1, p1) <> (h2, p2) ->
    forall real rh rp ch cp, static_cast hierarchy real rh rp from cast ch cp ->  False.
Proof.
  intros.
  inversion H2; subst.
   generalize (H5 _ _ H).
   generalize (H5 _ _ H0).
   congruence.
  generalize (path_le H).
  intro.
  generalize (path_le H4).
  intro.
  generalize (Ple_antisym H7 H8).
  intros; subst.
  generalize (self_path_trivial H).
  generalize (self_path_trivial H0).
  congruence.
Qed.
  

(* Paths *)

Function non_virtual_bases (l : list (Class.Inheritance.t * ident)) : list ident :=
match l with
  | nil => nil
  | (Class.Inheritance.Repeated, ci) :: q =>
    ci :: non_virtual_bases q
  | _ :: q => non_virtual_bases q
end.

Lemma non_virtual_bases_correct : forall l b,
  In b (non_virtual_bases l) -> In (Class.Inheritance.Repeated, b) l.
Proof.
  induction l ; simpl.
  tauto.
  destruct a.
  destruct t.
  simpl.
  inversion 1.
   subst.
   eauto.
   eauto.
 eauto.
Qed.

Lemma non_virtual_bases_complete : forall l b,
  In (Class.Inheritance.Repeated, b) l -> In b (non_virtual_bases l).
Proof.
  induction l; simpl; eauto.
  inversion 1 ; subst; eauto.
  destruct a ; simpl.
  destruct t ; simpl ; eauto.
Qed.



Section Filtered_paths.

Variable P : ident -> Prop.

Hypothesis P_dec : forall i, {P i} + {~ P i}.

  Lemma filtered_repeated_paths_step : forall n t, (forall i, Plt i n -> t ! i <> None) ->
    (forall i l, t ! i = Some l -> (forall p, In p l <-> 
      exists l', p = i :: l' /\ is_valid_repeated_subobject hierarchy p = true /\
        forall j, LibLists.last p = Some j -> P j)) ->
  {l : _ &  (forall p, In p l <-> 
      exists l', p = n :: l' /\ is_valid_repeated_subobject hierarchy p = true /\
        forall j, LibLists.last p = Some j -> P j)
}.
  Proof.
   intros.
   case_eq (t ! n).
    intros.
    exists l.
    auto.
   intros _.
   case_eq (hierarchy ! n).
    intros.
    exists (      
      ((if P_dec n then (n :: nil) :: nil else nil) ++ LibLists.flatten (
       List.map 
       (fun ci =>
         match t ! ci with
           | Some l =>
             List.map (cons n) l
           | _ => nil
         end
         )
       (non_virtual_bases (Class.super t0))
     )
     )
   ).
  intros.
  split.
  intro.
  destruct (in_app_or _ _ _ H2).
   destruct (P_dec n).
    inversion H3 ; try contradiction.
    subst.
    simpl.
    rewrite H1. 
    repeat esplit.  
    congruence.
   inversion H3.
  clear H2.
  destruct (LibLists.member_flatten_elim H3).
  clear H3.
  destruct H2.
  destruct (in_map_iff 
    (fun ci : positive =>
      match t ! ci with
        | Some l => map (cons n) l
        | None => nil (A:=list positive)
      end)
    (non_virtual_bases (Class.super t0))
    x
  ).
  clear H5.
  destruct (H4 H2).
  clear H4 H2.
  destruct H5.
  generalize (non_virtual_bases_correct H4).
  intros.
  generalize (well_founded hyp H1 H5).
  intros.
  generalize (H _ H6).
  intros.
  case_eq (t ! x0) ; try congruence.
  intros.
  rewrite H8 in H2.
  subst.
  destruct (in_map_iff (cons n) l p).
  clear H9.
  destruct (H2 H3).
  clear H2 H3.
  destruct H9.
  subst.
  simpl.
  exists x.
  split.
  reflexivity.
  rewrite H1.
  destruct (H0 _ _ H8 (x)).
  clear H9.
  destruct (H2 H3).
  clear H2 H3.
  destruct H9.
  destruct H3.
  pattern x at 1.
  rewrite H2.
  rewrite H3.
  split.
  assert (
    (if In_dec super_eq_dec (Class.Inheritance.Repeated, x0) (Class.super t0)
    then true
    else false) = true
  ).
  destruct (
    In_dec super_eq_dec (Class.Inheritance.Repeated, x0) (Class.super t0)
  ).
  trivial.
  contradiction.
  exact H10.
  rewrite H2.
  rewrite <- H2.
  assumption.

  destruct 1.
  destruct H2.
  subst.
  simpl in H3.
  rewrite H1 in H3.
  destruct H3.
  destruct x.
   generalize (H3 _ (refl_equal _)).
   intros.
   destruct (P_dec n) ; try contradiction.
   apply in_or_app.
   simpl.
   tauto.
  apply in_or_app.
  right.
  assert (
    (if In_dec super_eq_dec (Class.Inheritance.Repeated, p)
             (Class.super t0)
        then is_valid_repeated_subobject hierarchy (p :: x)
        else false) = true ->
    In (Class.Inheritance.Repeated, p) (Class.super t0) /\
    is_valid_repeated_subobject hierarchy (p :: x) = true
  ).
  destruct (
    In_dec super_eq_dec (Class.Inheritance.Repeated, p)
    (Class.super t0)
  ).
   tauto.
  congruence.
  destruct (H4 H2).
  clear H2 H4.
  remember 
  (fun ci : positive =>
            match t ! ci with
            | Some l => map (cons n) l
            | None => nil (A:=list positive)
            end)
  as f.
  eapply LibLists.member_flatten_intro with (l0 := f p). 
  eapply LibLists.member_map.
  apply non_virtual_bases_complete.
  assumption.
  subst.
  generalize (well_founded hyp H1 H5).
  intros.
  generalize (H _ H2).
  intros.
  case_eq (t ! p) ; try congruence.
  intros.
  destruct (H0 _ _ H7 (p :: x)).
  clear H8.
  apply LibLists.member_map.
  apply H9.
  esplit.
  split.
  reflexivity.
  split.
  assumption.
  assumption.

  intros.
  exists (@nil (list positive)).
  intros.
  simpl.
  split.
  tauto.
  destruct 1.
  destruct H2.
  subst.
  simpl in H3.
  rewrite H1 in H3.
  destruct H3.
  discriminate.
Qed.

Theorem filtered_paths_aux :
  {t | 
    (forall cn,
      hierarchy ! cn <> None -> t ! cn <> None) /\
    forall cn l, t ! cn = Some l ->
      forall i, (In i l <-> 
        exists i', i = cn :: i' /\
          is_valid_repeated_subobject hierarchy i = true /\
          forall j, LibLists.last i = Some j -> P j
)
  } ->
  forall from,
    {l |
      forall k p, 
        (In (k, p) l <-> 
          exists to,
            path hierarchy to p from k /\
            P to
        )
    }
    .
Proof.
 destruct 1.
 destruct a.
 intros.
 case_eq (hierarchy ! from).
  intros.
  assert (hierarchy ! from <> None) by congruence.
  generalize (H _ H2).
  intros.
  case_eq (x ! from) ; try congruence.
  intros.
  generalize (H0 _ _ H4).
  intros.
  destruct (virtual_bases).
  destruct a.
  generalize (H6 _ H2).
  intros.
  case_eq (x0 ! from) ; try congruence.
  intros.
  generalize (H7 _ _ H9).
  clear H3 H7 H8.
  intros.
  exists (
    List.map (fun p => (Class.Inheritance.Repeated, p)) l
    ++
    LibLists.flatten
    (List.map
      (fun b =>
        match x ! b with
          | None => nil
          | Some lb => List.map  (fun p => (Class.Inheritance.Shared, p)) lb
        end)
      l0
    )
  ).
  split.
   intro.
   destruct (in_app_or _ _ _ H7).
    clear H7.
    destruct (LibLists.map_elim H8).
    clear H8.
    destruct H7.
    injection H8 ; clear H8 ; intros ; subst.
    destruct (H5 p).
    clear H10.
    destruct (H8 H7).
    destruct H10.
    subst.
    clear H8 H7.
    destruct H11.
    clear H3.
    assert (from :: x1 <> nil) by congruence.
    generalize (last_nonempty H3).
    intros.
    case_eq (LibLists.last (from :: x1)) ; try congruence.
    intros.
    destruct (last_correct H11).
    esplit.
    asplit.
    eapply path0_path.
    econstructor.
    reflexivity.
    eassumption.
    assumption.
    apply H8.
    assumption.
   destruct (LibLists.member_flatten_elim H8).
   destruct H10.
   clear H8.
   clear H7.
   destruct (LibLists.map_elim H10).
   clear H10.
   destruct H7.
   subst.
   destruct (H3 x2).
   clear H10.
   generalize (H8 H7).
   clear H8 H7.
   intros.
   generalize (is_virtual_base_of_defined_base H7).
   intros.
   generalize (H _ H8).
   intros.
   case_eq (x ! x2) ; try congruence.
   intros.
   clear H10.
   rewrite H12 in H11.
   destruct (LibLists.map_elim H11).
   clear H11.
   destruct H10.
   injection H11.
   clear H11.
   intros ; subst.
   destruct (H0 _ _ H12 p).
   clear H13.
   destruct (H11 H10).
   clear H11 H10.
   destruct H13.
   subst.
   destruct H11.
   assert (x2 :: x1 <> nil) by congruence.
   generalize (last_nonempty H13).
   intros.
   case_eq (LibLists.last (x2 :: x1)) ; try congruence.
   intros.
   destruct (last_correct H15).
   rewrite H15 in H11.
   esplit.
   split.
   eapply path0_path.
   econstructor.
   eassumption.
   reflexivity.
   eassumption.
   assumption.
   auto.

  destruct 1.
  destruct H7.
  generalize (path_path0 H7).
  clear H7.
  intro.
  apply in_or_app.
  inversion H7.   
   subst.
   left.
   eapply LibLists.map_intro.
   2 : reflexivity.
   destruct (H5 (from :: lf)).
   clear H10.
   apply H13.
   esplit.
   split.
   reflexivity.
   split.
   assumption.
   rewrite (H11).
   rewrite last_complete.
   intros.
   congruence.
  subst.
  right.
  destruct (H3 base).
  clear H11.
  generalize (H14 H10).
  clear H14.
  intros.
  clear H4 H5.
  generalize (is_virtual_base_of_defined_base H10).
  intros.
  generalize (H _ H4).
  intros.
  case_eq (x ! base) ; try congruence.
  intros.
  destruct (H0 _ _ H14 (base :: lf)).
  clear H15.   
  eapply LibLists.member_flatten_intro.
   eapply LibLists.map_intro.
   eassumption.
   rewrite H14.
   reflexivity.
  eapply LibLists.map_intro.
   eapply H16.
   esplit.
   split.
   reflexivity.
   split.
   assumption.
   rewrite H12.
   rewrite last_complete.
   congruence.
  trivial.
 intros.
 exists (@nil (Class.Inheritance.t * list ident)).
 simpl.
 split.
  tauto.
 destruct 1.
 destruct H2.
 generalize (path_path2 H2).
 inversion 1 ; congruence.
Qed.

Lemma filtered_repeated_paths :
  {t | 
    (forall cn,
      hierarchy ! cn <> None -> t ! cn <> None) /\
    forall cn l, t ! cn = Some l ->
      forall i, (In i l <-> 
        exists i', i = cn :: i' /\
          is_valid_repeated_subobject hierarchy i = true /\
          forall j, LibLists.last i = Some j -> P j
)
  }.
Proof.
  generalize(max_index hierarchy).
  destruct 1.
  destruct (progressive filtered_repeated_paths_step x).
  destruct p0.
  exists x0.
  eauto.
Qed.

Theorem filtered_paths : 
  {t |
    (forall cn,
      hierarchy ! cn <> None -> t ! cn <> None) /\
    forall from l, t ! from = Some l ->
      forall k p, 
        (In (k, p) l <-> 
          exists to,
            path hierarchy to p from k /\
            P to
        )
  }
  .
Proof.
  generalize filtered_repeated_paths.
  intro.
  generalize(max_index hierarchy).
  destruct 1.
  destruct (progressive (fun n _ _ _ => let (o, h) := filtered_paths_aux H n in existT _ o h) x).
  destruct p0.
  exists x0.
  eauto.  
Qed.

End Filtered_paths.    
  
(** * Domination *)

   Lemma dominates_antisym : forall from kp1 kp2,
     dominates hierarchy from kp1 kp2 ->
     dominates hierarchy from kp2 kp1 ->
     kp1 = kp2.
   Proof.
     inversion 1.
     subst.
     inversion 1.
     subst.
     generalize (path_last H1).
     intros.
     generalize (path_last H2).
     intros.
     generalize (path_concat H1 H2 (sym_equal H3)).
     intros.
     generalize (path_last H9).
     intros.
     generalize (path_last H4).
     intros.
     replace to0 with to2 in * by congruence.
     generalize (path_last H5).
     intros.
     rewrite H3 in H6.
     generalize (path_concat H4 H5 H6).
     intros.
     generalize (path_last (H13)).
     intros.
     replace to3 with to1 in * by congruence.
     clear to0 to3.
     case_eq (concat (k, p) (k2, p2)).
     intros.
     generalize (path_concat H2 H5 (sym_equal H15)).
     intros.
     generalize (self_path_trivial (H16)).
     injection 1 ; intros ; subst.
     pattern (k1, p1) at 1.
     rewrite H6.
     rewrite <- H3.
     rewrite concat_assoc.
     rewrite H15.
     f_equal.
     symmetry.
     generalize (path_le H2).
     intros.
     generalize (path_le H5).
     intros.
     generalize (Ple_antisym H18 H19).
     intros ; subst.
     apply self_path_trivial.
     assumption.
   Qed.


Lemma dominates_dec_aux_accu : forall kp1 kp2 l accu,
  (forall kp, In kp (rev accu) -> kp2 <> concat kp1 kp) ->
  {kp | In kp (rev accu ++ l) /\ kp2 = concat kp1 kp} +
  {forall kp, In kp (rev accu ++ l) -> kp2 <> concat kp1 kp}.
Proof.
  induction l.
  intros.
  rewrite <- app_nil_end.
  tauto.
 intros.
 destruct (path_eq_dec kp2 (concat kp1 a)).
  left.
  esplit.
  split.
  2 : eassumption.
  apply in_or_app.
  simpl.
  tauto.
 change (a :: l) with ((a :: nil) ++ l).
 rewrite <- app_ass.
 change (rev accu ++ a :: nil) with (rev (a :: accu)).
 apply IHl.
 simpl.
 intros.
 destruct (in_app_or _ _ _ H0).
  auto.
 inversion H1.
 congruence.
 contradiction.
Qed.

Corollary dominates_dec_aux : forall kp1 kp2 l,
  {kp | In kp (l) /\ kp2 = concat kp1 kp} +
  {forall kp, In kp (l) -> kp2 <> concat kp1 kp}.
Proof.
  intros.
  change l with (rev nil ++ l).
  apply dominates_dec_aux_accu.
  simpl.
  tauto.
Qed. 

Theorem dominates_dec : forall from kp1 kp2,
  {dominates hierarchy from kp1 kp2} + {~ dominates hierarchy from kp1 kp2}.
Proof.
 intro from.
 case_eq (hierarchy ! from).
 Focus 2.
  intros.
  right.
  intro Habs.
  destruct Habs.
  subst.
  generalize (path_path2 H1).
  inversion 1 ; subst ; congruence.
 intros cfrom Hcfrom.
 destruct kp1 as [k1 p1].
 case_eq (LibLists.last p1).
  Focus 2.   
  destruct p1.
   intros.
   right.
   intro Habs.
   destruct Habs.
   injection H0 ; intros ; subst.
   generalize (path_path0 H1).
   inversion 1 ; discriminate.
  intros.
  assert (i :: p1 <> nil) by congruence.
  generalize (last_nonempty H0).
  intros.
  contradiction.
 intros to1 Hlast1.
 case_eq (hierarchy ! to1).
  Focus 2.
  intros.
  right.
  intro Habs.
  destruct Habs.
  injection H0 ; intros ; subst.
  generalize (path_last H1).
  intros.
  replace to0 with to1 in * by congruence.
  destruct (last_correct Hlast1).
  subst.
  assert (In to1 (x ++ to1 :: nil)).
   apply in_or_app.
   simpl.
   tauto.
  generalize (path_path0 H1).
  inversion 1 ; subst.
   exact (is_valid_repeated_subobject_defined H8 H4 H). 
  exact (is_valid_repeated_subobject_defined H9 H4 H).
 intros cto1 Hcto1.
 assert (hierarchy ! to1 <> None) by congruence.
 destruct kp2 as (k2, p2).
 case_eq (LibLists.last p2).
  Focus 2.
  intros.
  destruct p2.
   right.
   intros Habs.
   inversion Habs.
   injection H1 ; intros ; subst.
   generalize (path_last H2).
   intros.
   replace to0 with to1 in * by congruence.
   generalize (path_concat ( H2) ( H3) H4).
   intros.
   generalize (path_path0 H6).
   inversion 1 ; discriminate.
  assert (i :: p2 <> nil) by congruence.
  generalize (last_nonempty H1).
  intros.
  contradiction.
 intros to2 Hlast2.
 case_eq (hierarchy ! to2).
  Focus 2.
  intros.
  right.
  intro Habs.
  inversion Habs.
  injection H1 ; intros ;subst.
  generalize (path_last H2).
  intros.
  replace to0 with to1 in * by congruence.
  generalize (path_concat ( H2) ( H3) H4).
  intros.
  destruct (last_correct Hlast2).
  subst.
  assert (In to2 (x ++ to2 :: nil)).
   apply in_or_app.
   simpl.
   tauto.
  generalize (path_path0 ( H6)).
  inversion 1 ; subst.
   exact (is_valid_repeated_subobject_defined H11 H7 H0).
  exact (is_valid_repeated_subobject_defined H12 H7 H0).  
 intros cto2 Hcto2.   
 destruct paths as [T [HT H1]].
 generalize (HT _ H).
 intros.
 case_eq (T ! to1) ; try congruence.
 intros.
 destruct (H1 _ _ H2).
 assert (hierarchy ! from <> None) by congruence.
 generalize (H3 _ H5).
 intros.
 case_eq (t ! from) ; try congruence.
 intros.
 destruct (H4 _ _ H7 (k1, p1)).
 destruct (In_dec path_eq_dec (k1, p1) l).
  Focus 2.
  right.
  intro Habs.
  inversion Habs.
  injection H10 ; intros ; subst.
  generalize (path_last H11).
  intros.
  replace to0 with to1 in * by congruence.
  eauto.
 generalize (H8 i).
 intros.
 assert (hierarchy ! to2 <> None) by congruence.
 generalize (HT _ H11). 
 intros.
 case_eq (T ! to2) ; try congruence.
 intros.
 generalize (H1 _ _ H13).
 destruct 1.
 generalize (H14 _ H).
 intros.
 case_eq (t0 ! to1) ; try congruence.
 intros.
 destruct (
   dominates_dec_aux (k1, p1) (k2, p2) l0
 ).
  destruct s.
  destruct x.
  destruct a.
  destruct (H15 _ _ H17 (t1, l1)).
  generalize (H20 H18).
  intros.
  left.
  econstructor.
  reflexivity.
  eassumption.
  eassumption.
  assumption.
 right.
 intro Habs.
 destruct Habs.
 injection H18 ; intros ; subst.
 generalize (path_last H19).
 intros.
 replace to0 with to1 in * by congruence.
 generalize (path_concat ( H10) ( H20) H21).
 intro.
 generalize (path_last H23).
 intros.
 replace to3 with to2 in * by congruence.
 destruct (H15 _ _ H17 (k, p)).
 generalize (H26 H20).
 intros.
 exact (n _ H27 H21).
Qed.

(** * Method dispatch *)

Theorem final_overrider_dominates : forall ms ac1 rc rck1 rcp1 rk1 rp1,
  final_overrider hierarchy ms ac1 rc rck1 rcp1 rk1 rp1 ->
  forall ac2 k12 p12,
    path hierarchy ac2 p12 ac1 k12 ->
    forall ak2 ap2 am2,
      path hierarchy am2 ap2 ac2 ak2 ->
      forall amc2,
        hierarchy ! am2 = Some amc2 ->
        Method.find ms (Class.methods amc2) <> None ->
        (forall to k p,
          path hierarchy to p ac2 k ->
          forall c, hierarchy ! to = Some c ->
            Method.find ms (Class.methods c) <> None ->
            dominates hierarchy ac2 (ak2, ap2) (k, p)
        ) ->
        forall rck2 rcp2,
          (rck2, rcp2) = concat (rck1, rcp1) (k12, p12) ->
          final_overrider hierarchy ms ac2 rc rck2 rcp2 rk1 rp1
        .
Proof.
  inversion 1.
  inversion H7.
  injection H11 ; clear H11 ; intros until 2 ; subst.
  intros.
  generalize (path_concat H0 H11 H19).
  intros.
  case_eq (concat (rck2, rcp2) (ak2, ap2)).
  intros.
  symmetry in H21.
  generalize H21.
  intros.
  rewrite H19 in H22.
  rewrite concat_assoc in H22. 
  case_eq (concat (k12, p12) (ak2, ap2)).
  intros.
  rewrite H23 in H22.
  symmetry in H23. 

  econstructor.
  assumption.
  eassumption.
  eassumption.
  assumption.
  assumption.
  eassumption.
  eassumption.
  eapply dominates_trans.
   eassumption.
   eapply (dominates_concat_left H0 H5 H22).
   eapply H4.
   eapply path_concat.
   eassumption.
   eassumption.
   assumption.
   eassumption.
   assumption.
  eassumption.
  assumption.
  assumption.
Qed.


Theorem final_overrider_list : forall 
 (ms : MethodSignature.t A) (apparent_class : ident) (real_class : ident) (real_class_inheritance : Class.Inheritance.t) (real_class_path : list ident) ,
 { l | forall (real_inheritance:  Class.Inheritance.t) (real_path : list ident),
   In (real_inheritance, real_path) l <->
   final_overrider hierarchy ms apparent_class real_class real_class_inheritance real_class_path real_inheritance real_path }.
Proof.
intros.
case_eq (hierarchy ! apparent_class) ; intros.
 Focus 2.
 exists (@nil (Class.Inheritance.t * list ident)) ; simpl ; split ; try tauto.
 inversion 1.
 generalize (path_defined_to H1).
 congruence.
intros.
case_eq (hierarchy ! real_class) ; intros.
 Focus 2.
 exists (@nil (Class.Inheritance.t * list ident)) ; simpl ; split ; try tauto.
 inversion 1.
 generalize (path_defined_from H2).
 congruence.
destruct (paths).
destruct a.
assert (hierarchy ! apparent_class <> None) as H' by congruence.
generalize (H1 _ H').
intros H'0.
case_eq (x ! apparent_class) ; try congruence.
intros.
destruct (H2 _ _ H3).
assert (hierarchy ! real_class <> None) by congruence.
generalize (H4 _ H6).
intros.
case_eq (t1 ! real_class) ; try congruence.
intros.
destruct (H5 _ _ H8 (real_class_inheritance, real_class_path)).
destruct (In_dec path_eq_dec (real_class_inheritance, real_class_path) l).
 Focus 2.
 exists (@nil (Class.Inheritance.t * list ident)).
 simpl.
 split ; try tauto.
 inversion 1.
 generalize (H10 H12).
 assumption.
generalize (H9 i).
intros.
assert (
  forall cn, 
    {exists c, hierarchy ! cn = Some c /\ Method.find ms (Class.methods c) <> None} +
    {~ exists c, hierarchy ! cn = Some c /\ Method.find ms (Class.methods c) <> None}
).
 intros.
 destruct (hierarchy ! cn).
  case_eq (Method.find ms (Class.methods t2)).
   intros.
   left.
   esplit.
   split.
   reflexivity.
   congruence.
  right.
  intro.
  invall.
  congruence.
 right.
 intro.
 invall.
 discriminate.
destruct (filtered_paths H12).
destruct a.
assert (hierarchy ! apparent_class <> None) by congruence.
generalize (H13 _ H15).
intros.
case_eq (x0 ! apparent_class) ; try congruence.
intros.
generalize (H14 _ _ H17).
intros.
destruct (@LibLists.minimum_partial_order _ _ (@dominates_antisym apparent_class) (@dominates_trans _ hierarchy apparent_class) (@dominates_dec apparent_class) l0).
  intros.
  destruct a.
  destruct (H18 t2 l1).
  destruct (H20 H19).
  invall.
  eauto using dominates_refl_weak.
 Focus 2. (* pas de minimum *)
 exists (@nil (Class.Inheritance.t * list ident)).
 simpl.
 split ; try tauto.
 inversion 1.
 apply f with (apparent_method_inheritance, apparent_method_path).
  destruct (H18 apparent_method_inheritance apparent_method_path).
  apply H32.
  esplit.
  split.
  eassumption.
  esplit.
  split.
  eassumption.
  assumption.
  intros.
 destruct b.
 destruct (H18 t2 l1).
 destruct (H32 H31).
 invall.
 eauto.
(* minimum existe *)
destruct s.
invall.
destruct x1.
case_eq (concat (real_class_inheritance, real_class_path) (t2, l1)).
intros.
symmetry in H21.
generalize (H13 _ H6).
intros.
case_eq (x0 ! real_class) ; try congruence.
intros.
generalize (H14 _ _ H23).
intros.
generalize (fun x => @filter_In _ (fun b => if dominates_dec real_class b (t3, l2) then true else false) x l3).
generalize (
  (filter
         (fun b : Class.Inheritance.t * list ident =>
          if dominates_dec real_class b (t3, l2) then true else false) l3)
).
intros.
destruct (@LibLists.minimals _ _ (@dominates_antisym real_class) (dominates_dec real_class) l4).
 intros.
 destruct (H25 j).
 destruct (H27 H26).
 destruct j.
 destruct (H24 t4 l5).
 destruct (H31 H29).
 invall.
 eauto using dominates_refl_weak.
destruct (H18 t2 l1).
generalize (H26 H19).
intros.
exists x1.
invall.
split.
 intros.
 destruct (i0 (real_inheritance, real_path)).
 destruct (H32 H29).
 generalize (H35 _ H34).
 intros.
 destruct (H25 (real_inheritance, real_path)).
 destruct (H37 H34).
 destruct (H24 real_inheritance real_path).
 destruct (H41 H39).
 invall.
 econstructor.
 assumption.
 eassumption.
 eassumption.
 assumption.
  intros.
  apply H20.
  destruct (H18 k p).
  apply H50.
  esplit.
  split.
  eassumption.
  esplit.
  split.
  eassumption.
  assumption.
 eassumption.
 eassumption.
 destruct ( dominates_dec real_class (real_inheritance, real_path) (t3, l2)
 ) ; try congruence.
 eassumption.
 assumption.
 intros.
 apply H35 ; auto.
 destruct (H25 (k, p)).
 apply H51.
 split.
 destruct (H24 k p).
 apply H53.
 esplit.
 split.
 eassumption.
 esplit.
 split.
 eassumption.
 assumption.
 destruct (
   dominates_dec real_class (k, p) (t3, l2) 
 ) ; try congruence.
 destruct n.
 destruct (
   dominates_dec real_class (real_inheritance, real_path) (t3, l2)
 ); try congruence.
 eauto using dominates_trans.
inversion 1.
destruct (i0 (real_inheritance, real_path)).
apply H44.
split.
 destruct (H25 (real_inheritance, real_path)).
 apply H46.
 split.
  destruct (H24 real_inheritance real_path).
  apply H48.
  esplit.
  split.
  eassumption.
  esplit.
  split.
  eassumption.
  assumption.
 destruct ( dominates_dec real_class (real_inheritance, real_path) (t3, l2)
 ) ; try congruence.
 destruct n.
 eapply dominates_trans.
 eassumption.
 eapply dominates_concat_left.
 2 : eassumption.
 eassumption.
 eassumption.
 eapply H36.
 eassumption.
 eassumption.
 assumption.
invall.
intros.
destruct (H25 k).
destruct (H47 H45).
destruct k.
destruct (H24 t4 l5).
destruct (H51 H49).
invall.
eauto.
Qed.


Lemma vborder_list_exists : forall a c, (hierarchy) ! a = Some c -> {y | vborder_list (hierarchy) (Class.super c) y}.
Proof.
 cut (forall al, match al with
              | existS a l =>
                forall c, (hierarchy) ! a = Some c ->
                  forall l', Class.super c = l' ++ l ->
                    {y | vborder_list (hierarchy) l y}
            end).
 intros.
 refine (X (existS _ a (Class.super c)) _ _ nil _).
  eassumption.
  reflexivity.
 pose (lstlt := ltof  _ (@length (Class.Inheritance.t * ident))).
 induction al using (well_founded_induction_type (wf_lexprod _ _ _ _ Plt_wf (fun _ => well_founded_ltof _ (@length (Class.Inheritance.t * ident))))).
  destruct al.
   destruct l.
   intros.
   esplit.
   econstructor.
  assert (lexprod _ _ Plt (fun _ => lstlt) (existT _ x l) (existT _ x (p :: l))) by abstract (
   right;
   unfold lstlt, ltof;
   simpl;
   omega
  ).
  intros.
  assert (Class.super c = (l' ++ p :: nil) ++ l) by abstract (
   rewrite app_ass;
   simpl;
   assumption
  ).
  destruct (X _ H _ H0 _ H2).
  clear H.
  case_eq p.
  intros.
  subst.
  assert (In (t, i) (Class.super c)) by abstract (
   rewrite H1; eauto using in_or_app
  ).
  assert ((hierarchy) ! i <> None)
 by abstract (eauto using complete).  
  case_eq ((hierarchy) ! i); try congruence.
  intros.  
  assert (lexprod _ _ Plt (fun _ => lstlt) (existT _ i (Class.super t0)) (existT _ x ((t, i) :: l))) by abstract (
   left;
   eauto using well_founded
  ).
  destruct (X _ H5 _ H4 nil (refl_equal _)).
  esplit.
  econstructor.
   eassumption.
   eassumption.
   eassumption.
  reflexivity.
  reflexivity.
Qed.


End HH.

  End Well_formed_hierarchy.


