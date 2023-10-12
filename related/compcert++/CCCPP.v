(** CCCPP.v: Copyright 2010 Tahina Ramananandro *)

Require Import LibLists.
Require Import Cplusconcepts.
Require Import Coqlib.
Require Import Tactics.
Require Import CplusWf.
Require Import LibMaps.
Require Import LayoutConstraints.
Require Import LibPos.
Require Import CPP.
Require Import Dynamic.
Require Import DynamicWf.

Load Param.

(** The proof of correctness of a layout algorithm optimized for empty base tail padding (POPL 2011, Section 6.2) *)

Section Compcert.
Variable (A : ATOM.t).

(** * Empty classes *)

(** A class is empty if, and only if, all the following conditions hold:
   - it has no scalar fields
   - all its structure fields are of an empty class type
   - it has no virtual methods
   - it has no virtual bases
   - all its direct non-virtual bases are empty
*)

Section Is_empty.

Variable hierarchy : PTree.t (Class.t A).

Inductive is_empty : ident -> Prop :=
| is_empty_intro : forall ci c
  (H_ci_c : hierarchy ! ci = Some c)
  (H_fields_struct : forall f, In f (Class.fields c) -> exists e, exists he, FieldSignature.type f = FieldSignature.Struct e he)
  (H_fields_struct_empty : forall f, In f (Class.fields c) -> forall e he,  FieldSignature.type f = FieldSignature.Struct e he -> is_empty e)
  (H_no_virtual_methods : forall m, In m (Class.methods c) -> Method.virtual m = true -> False)
  (H_no_virtual_bases : forall b, In (Class.Inheritance.Shared, b) (Class.super c) -> False)
  (H_bases_empty : forall b, In (Class.Inheritance.Repeated, b) (Class.super c) -> is_empty b),
  is_empty ci
.

(** This definition meets the constraints for empty classes stated in 4.3 *)

Lemma is_empty_prop : Is_empty.prop hierarchy is_empty.
Proof.
  constructor.
  inversion 1; congruence.
  inversion 1. intros until 1. replace c0 with c in * by congruence. assumption.
  inversion 1. intros until 1. replace c0 with c in * by congruence. assumption.
  inversion 1; intros; subst. replace c0 with c in * by congruence.
   destruct h.
    eauto.
    destruct (H_no_virtual_bases b).
    assumption.
Qed.

Lemma dynamic_nonempty : forall i,
  is_dynamic hierarchy i -> is_empty i -> False.
Proof.
  induction 1 ; inversion 1 ; subst ;   replace c0 with c in * by congruence.
  destruct H_methods.
  destruct H0.
  eauto.
  eauto.
  destruct h ; eauto.
Qed.

Hypothesis hierarchy_wf : Well_formed_hierarchy.prop hierarchy.


Lemma no_virtual_bases : forall ci,
  is_empty ci ->
  forall vb, is_virtual_base_of hierarchy vb ci -> False.
Proof.
  intros.
  revert H.
  induction H0.
   inversion 1; subst.
   replace c0 with c in * by congruence.
   eauto.
   intros.
   apply IHis_virtual_base_of.
   inversion H2.
   subst.
   replace c0 with c in * by congruence.
   destruct h'.
    eauto.
   apply False_rect.
   eauto.
Qed.


Definition is_empty_dec : forall i, {is_empty i} + {~ is_empty i}.
Proof.
 induction i using  (well_founded_induction Plt_wf).
 rename H into IHi.
 case_eq (hierarchy ! i).
  intros c Hc.
  pose (e := fun f : _ A =>
    match FieldSignature.type f with
      | FieldSignature.Struct s _ =>
        match plt s i with
          | left Hlt =>
            if IHi _ Hlt then false else true
          | _ => true
        end
      | _ => true
    end
  ).
  case_eq (List.filter e (Class.fields c)).
   intros.
   case_eq (List.filter (Method.virtual (A := A)) (Class.methods c)).
   intros.
   pose (f := fun (x : _ * ident) =>
     match x with
       | (Class.Inheritance.Shared, _) => true
       | (Class.Inheritance.Repeated, j) =>
         match plt j i with
           | left Hlt =>
             if IHi _ Hlt then false else true
           | _ => false
         end
     end
   ).
   case_eq (filter f (Class.super c)).
    intros Hnil.
    left.
    econstructor.
    eassumption.
    intros.
    case_eq (e f0).
     intros.
     generalize (filter_In e f0 (Class.fields c)).
     intros [_ R].
     rewrite H in R.
     destruct R.
     tauto.
    unfold e.
    case_eq (FieldSignature.type f0); try congruence.
    intros until 1.
    destruct (plt struct i) ; try congruence.
    destruct (IHi _ p) ; try congruence.
    intros ; repeat esplit.
    intros.
    case_eq (e f0).
     intros.
     generalize (filter_In e f0 (Class.fields c)).
     intros [_ R].
     rewrite H in R.
     destruct R.
     tauto.
    unfold e.
    rewrite H2.
    destruct (plt e0 i) ; try congruence.
    destruct (IHi e0 p) ; congruence.

    intros.
    generalize (filter_In (Method.virtual (A := A)) m (Class.methods c)).
    rewrite H0.
    simpl.
    tauto.

    intros b Hb.
    generalize (filter_In f (Class.Inheritance.Shared, b) (Class.super c)).
    intros [_ Hb_abs].
    rewrite Hnil in Hb_abs.
    simpl in Hb_abs.
    apply Hb_abs.
    tauto.
    intros b Hb.
    generalize (filter_In f (Class.Inheritance.Repeated, b) (Class.super c)).
    intros [_ Hb_empty].
    rewrite Hnil in Hb_empty.
    simpl in Hb_empty.
    destruct (plt b i).
    destruct (IHi b p).
     assumption.
    destruct Hb_empty.
    tauto.
    destruct n.
    eauto using Well_formed_hierarchy.well_founded.
   intros p l Hp_aux.
   assert (In p (filter f (Class.super c))) as Hp.
   rewrite Hp_aux.
   auto.
   destruct p as (h, j).
   generalize (filter_In f (h, j) (Class.super c)).
   intros [Hp_destr _].
   generalize (Hp_destr Hp).
   intros [Hp_c Hp_f].
   right.
   intro Habs.
   inversion Habs.
   replace c0 with c in * by congruence.
   unfold f in Hp_f.
   destruct h.
    destruct (plt j i).
     destruct (IHi j p).
      discriminate.
     destruct n.
     eauto.
    discriminate.
   eauto.

  intros.
  right.
  intro Habs.
  generalize (filter_In (Method.virtual (A := A)) t (Class.methods c)).
  rewrite H0.
  simpl.
  inversion Habs.
  replace c0 with c in * by congruence.
  generalize (H_no_virtual_methods t).
  tauto.

  intros.
  assert (In t (filter e (Class.fields c))).
   rewrite H.
   auto.
  generalize (filter_In e t (Class.fields c)).
  intros [L _].
  destruct (L H0).
  right.
  intro.
  inversion H3.
  replace c0 with c in * by congruence.
  generalize (H_fields_struct _ H1).
  destruct 1.
  destruct H5.
  revert H2.
  unfold e.
  rewrite H5.
  destruct (plt x i).
   destruct (IHi x p) ; try congruence.
   destruct n ; eauto.
  destruct n ; eauto using Well_formed_hierarchy.well_founded_struct.
 right ; intro Habs ; inversion Habs ; congruence.
Qed.

End Is_empty.

Definition Optim := CPP.Optim (CppOptim is_empty_prop dynamic_nonempty).

Variable (PF : PLATFORM A).

 Section LD.


(** * Overview of the layout algorithm *)

(** ** Computed values *)

(** Apart from the values expected in 4.1 and computed in [offsets], this algorithm computes the [ebo] and [nvebo] sets of empty base offsets and non-virtual empty base offsets, incrementally as in 4.5.5. [cilimit] is the identifier of the class being laid out. *)


     Record LD : Type := Ld {
       offsets : PTree.t (LayoutConstraints.t A);
       cilimit : ident;
       ebo : PTree.t (list (ident * Z));
       nvebo : PTree.t (list (ident * Z))
     }.

     Section prop.

       Variable hierarchy : PTree.t (Class.t A).

       Variable o : LD.


(** ** Invariant *)

(**
- Guard conditions: [offsets], [ebo] and [nvebo] are defined for all classes with an identifier less than [cilimit]:
- Soundness condition: for all such classes, the conditions stated in 4.5 hold
- specification of the sets [ebo], [nvebo] of (non-virtual) empty base offsets
*)
       
       Record prop : Prop := intro {
         (** Guard *)
         offsets_guard : forall ci, (offsets o) ! ci <> None -> hierarchy ! ci <> None;
         (** Section 4 *)
         offsets_intro : forall ci of, (offsets o) ! ci = Some of -> class_level_prop Optim PF (offsets o) hierarchy ci of
           ;
         (** Guard *)
         offsets_guard2 : forall ci, (offsets o) ! ci <> None -> Plt ci (cilimit o);
         offsets_exist : forall ci, Plt ci (cilimit o) -> hierarchy ! ci <> None -> (offsets o) ! ci <> None
           ;
         (** 4.5.5 for empty bases *)
         disjoint_ebo : forall ci o', (offsets o) ! ci = Some o' -> disjoint_empty_base_offsets Optim (offsets o) hierarchy ci o'
           ;
         (** Specification and guard conditions for [ebo], [nvebo] the sets of (non-virtual) empty base offsets *)
         ebo_prop : forall ci e, (ebo o) ! ci = Some e -> forall b o', (In (b, o') e <-> empty_base_offset Optim (offsets o) hierarchy ci b o')
           ;
         ebo_exist : forall ci, Plt ci (cilimit o) -> (ebo o) ! ci <> None
           ;
         ebo_guard : forall ci, (ebo o) ! ci <> None -> Plt ci (cilimit o)
           ;
         nvebo_prop : forall ci e, (nvebo o) ! ci = Some e -> forall b o', (In (b, o') e <-> non_virtual_empty_base_offset Optim (offsets o) hierarchy ci b o')
           ;
         nvebo_exist : forall ci, Plt ci (cilimit o) -> (nvebo o) ! ci <> None;
         nvebo_guard : forall ci, (nvebo o) ! ci <> None  ->  Plt ci (cilimit o)
       }.

   End prop.


End LD.

       Hint Resolve offsets_guard offsets_intro  offsets_exist disjoint_ebo ebo_prop ebo_exist nvebo_prop nvebo_exist.

Section Layout.   
       
       Variable hierarchy : PTree.t (Class.t A).
       
       Hypothesis hierarchy_wf : Well_formed_hierarchy.prop hierarchy.
              
       Let virtual_bases := let (t, _) := Well_formed_hierarchy.virtual_bases hierarchy_wf in t.

       Let virtual_bases_prop : (forall cn,
         hierarchy ! cn <> None -> virtual_bases ! cn <> None) /\
       forall cn l, virtual_bases ! cn = Some l ->
         forall i, (In i l <-> is_virtual_base_of hierarchy i cn)
           .
       Proof.
         unfold virtual_bases.
         destruct Well_formed_hierarchy.virtual_bases.
         assumption.
       Qed.

   
(** * Incremental layout *)

(** The identifier of the class being laid out is [LD.cilimit ld]. All classes with an identifier less that [LD.cilimit ld] are assumed to be already laid out. *)


    Section Step.

       Variable ld : LD.

       Hypothesis Hld : prop hierarchy ld.
       
       Section Def.

       Variable h : Class.t A.

       Hypothesis Hh : hierarchy ! (cilimit ld) = Some h.


(** ** Layout of non-virtual direct bases *)

       Section Non_virtual_direct_base_layout.

(** 
- [nvl_todo]: the list of non-virtual direct bases to which an offset has not yet been assigned
- [nvl_offsets]: the mapping between non-virtual direct bases and offsets
- [nvl_nvebo]: the set of non-virtual empty base offsets reachable through a direct non-virtual base that has already been assigned an offset
- [nvl_nvds]: the non-virtual data size so far. This is also the field boundary so far (because fields will be laid out no sooner than after the last non-virtual direct base).
- [nvl_nvsize]: the non-virtual size so far.
- [nvl_pbase]: the primary base, if any
- [nvl_align]: the non-virtual alignment so far
*)


         Record nvl : Set := make_nvl {
           nvl_todo : list ident;
           nvl_offsets : PTree.t Z;
           nvl_nvebo : list (ident * Z);
           nvl_nvds : Z;
           nvl_nvsize : Z;
           nvl_pbase : option ident;
           nvl_align : Z
         }.

         Section prop.

           Variable nvldata : nvl.

           Record nvl_prop : Prop := nvl_intro {
             (** Guard *)
             nvl_exist : forall ci, (In (Class.Inheritance.Repeated, ci) (Class.super h) <->  ((nvl_offsets nvldata) ! ci <> None \/ In ci (nvl_todo nvldata)));
             (** C21 *)
             nvl_primary_base : forall ci, nvl_pbase nvldata = Some ci -> (nvl_offsets nvldata) ! ci = Some 0;
             (** 4.3 *)
             nvl_primary_base_dynamic : forall ci, nvl_pbase nvldata = Some ci -> is_dynamic hierarchy ci;
             (** Guard *)
             nvl_data_low_bound : 0 <= nvl_nvds nvldata;
             (** C19 *)
             nvl_data_dynamic_low_bound : is_dynamic hierarchy (cilimit ld) -> dynamic_type_data_size PF <= nvl_nvds nvldata;
             (** C5 *)
             nvl_size_pos : 0 < nvl_nvsize nvldata;
             (** Guard *)
             nvl_low_bound : forall ci of, (nvl_offsets nvldata) ! ci = Some of -> 0 <= of;
             (** C20 *)
             nvl_dynamic_no_primary_low_bound : is_dynamic hierarchy (cilimit ld) -> nvl_pbase nvldata = None -> forall ci, (is_empty hierarchy ci -> False) -> forall of, (nvl_offsets nvldata) ! ci = Some of -> dynamic_type_data_size PF <= of;
             (** C6 *)
             nvl_nonempty_non_overlap : forall ci1 o1, (nvl_offsets nvldata) ! ci1 = Some o1 -> (is_empty hierarchy ci1 -> False) -> forall ci2 o2, (nvl_offsets nvldata) ! ci2 = Some o2 -> (is_empty hierarchy ci2 -> False) -> ci1 <> ci2 -> forall of1, (offsets ld) ! ci1 = Some of1 -> forall of2, (offsets ld) ! ci2 = Some of2 -> o1 + non_virtual_data_size of1 <= o2 \/ o2 + non_virtual_data_size of2 <= o1;
             (** C23 *)
             nvl_disjoint_empty_bases : forall ci1 o1, (nvl_offsets nvldata) ! ci1 = Some o1 -> forall ci2 o2, (nvl_offsets nvldata) ! ci2 = Some o2 -> ci1 <> ci2 -> forall b bo1, non_virtual_empty_base_offset Optim (offsets ld) hierarchy ci1 b bo1 -> forall bo2, non_virtual_empty_base_offset Optim (offsets ld) hierarchy ci2 b bo2 -> o1 + bo1 <> o2 + bo2;
             (** C7 *)
             nvl_nonempty_high_bound : forall ci, (is_empty hierarchy ci -> False) -> forall of, (nvl_offsets nvldata) ! ci = Some of -> forall o', (offsets ld) ! ci = Some o' -> of + non_virtual_data_size o' <= nvl_nvds nvldata;
             (** C1 *)
             nvl_high_bound : forall ci, forall of, (nvl_offsets nvldata) ! ci = Some of -> forall o', (offsets ld) ! ci = Some o' -> of + non_virtual_size o' <= nvl_nvsize nvldata;
             (** Guard *)
             nvl_align_pos : 0 < nvl_align nvldata;
             (** C16 *)
             nvl_align_dynamic : is_dynamic hierarchy (cilimit ld) -> (dynamic_type_data_align PF | nvl_align nvldata);
             (** C15 *)
             nvl_align_prop : forall ci, (nvl_offsets nvldata) ! ci <> None -> forall of, (offsets ld) ! ci = Some of -> (non_virtual_align of | nvl_align nvldata);
             nvl_offset_align :  forall ci of, (nvl_offsets nvldata) ! ci = Some of -> forall co, (offsets ld) ! ci = Some co -> (non_virtual_align co | of);
             (** Specification of [nvl_nvebo] non-virtual empty base offsets *)
             nvl_nvebo_prop : forall b o, (In (b, o) (nvl_nvebo nvldata) <-> exists ci, exists of, (nvl_offsets nvldata) ! ci = Some of /\ non_virtual_empty_base_offset Optim (offsets ld) hierarchy ci b (o - of))
           }.

           End prop.

           Section Step. 

             Variable nvldata : nvl.

           Hypothesis prop : nvl_prop nvldata.

(** Trying to assign an offset to the non-virtual direct base [a] of [cilimit ld] *)

           Variable a : ident.

           Variable q : list ident.

           Hypothesis Htodo : nvl_todo nvldata = a :: q.

           Hypothesis undef: (nvl_offsets nvldata) ! a = None.

           Let son : In (Class.Inheritance.Repeated, a) (Class.super h).
           Proof.
             destruct (nvl_exist prop a).
             apply H0.
             rewrite Htodo.
             auto.
           Qed.

           Let Hlt : (Plt a (cilimit ld)). 
           Proof.
             eauto using Well_formed_hierarchy.well_founded.
           Qed.

           Let orig_offset : {o' | (offsets ld) ! a = Some o'}.
           Proof.
             assert ((offsets ld) ! a <> None) by eauto using offsets_exist, Well_formed_hierarchy.complete.
             case_eq ((offsets ld) ! a); try congruence.
             intros.
             repeat esplit.
           Qed.

           Let o' := let (o', _) := orig_offset in o'.

           Let Ho' : (offsets ld) ! a = Some o'.
           Proof.
             unfold o'.
             destruct orig_offset.
             assumption.
           Qed.

           Let e0 : {e | (nvebo ld) ! a = Some e}.
           Proof.
             generalize (nvebo_exist ( Hld) Hlt).
             case_eq ((nvebo ld) ! a); try congruence.
             intros.
             repeat esplit.
           Qed.

           Let e := let (e, _) := e0 in e.

           Let He :  (nvebo ld) ! a = Some e.
           Proof.
             unfold e.
             destruct e0.
             assumption.
           Qed.

(** 
   The offset [nv_offset] assigned to [a] is computed as follows:
   - starting from 0 if [a] is empty, from [nvl_nvds nvldata] (the non-virtual data size so far) otherwise
   - find the least offset [o] multiple of the non-virtual alignment of [a], and such that the set [e] of non-virtual empty base offsets reachable from [a] is disjoint from [nvl_nvebo] the offsets of non-virtual empty base offsets so far, knowing that there will be no conflict if [o >= nvl_nvsize nvldata]
   See [LibPos] for a definition of [bounded_offset].
*)

           Let em := is_empty_dec hierarchy_wf a.

           Let f z (x : _ * _) :=
             let (b, o) := x in
               if In_dec (prod_eq_dec peq Z_eq_dec) (b, z + o) (nvl_nvebo nvldata) then true else false.

           Let align_pos : 0 < non_virtual_align o'.
           Proof.
             exact (non_virtual_align_low_bound (offsets_intro Hld Ho')).
           Qed.
           
           Let f' z :=
             match List.filter (f z) e with
               | nil => true
               | _ => false
             end.

           Definition nv_offset :=
             let (z, _) := bounded_offset align_pos (if em then 0 else nvl_nvds nvldata)  (nvl_nvsize nvldata)  f' in z.

            Lemma nv_offsets_non_overlap : forall ci co, (nvl_offsets nvldata) ! ci = Some co -> forall b bo, non_virtual_empty_base_offset Optim (offsets ld) hierarchy ci b bo -> forall bo', non_virtual_empty_base_offset Optim (offsets ld) hierarchy a b bo' -> co + bo <> nv_offset + bo'.
            Proof.
              intros.
              unfold nv_offset.
              destruct (bounded_offset align_pos  (if em then 0 else nvl_nvds nvldata) (nvl_nvsize nvldata) f').
              destruct a0.
              destruct H3.
              assert (Plt ci (cilimit ld)).
               destruct (nvl_exist prop ci).                
               eapply Well_formed_hierarchy.well_founded.
               eauto.
               eauto.
               eapply H6.
               left.
               congruence.
              destruct (non_virtual_empty_base_offset_wf 
               hierarchy_wf (offsets_intro ( Hld)) (offsets_guard ( Hld)) H0).
              assert ((offsets ld) ! b <> None).
               eapply offsets_exist.
               eauto.
               eauto using Ple_Plt_trans.
               assumption.
              case_eq ((offsets ld) ! b) ; try congruence.
              intros.               
              generalize (non_virtual_empty_base_offset_incl
                 hierarchy_wf (offsets_intro ( Hld)) (offsets_guard ( Hld))
                 H1 H8 Ho').
              intros.
              assert (hierarchy ! ci <> None).
               destruct (nvl_exist prop ci).
               eapply Well_formed_hierarchy.complete.
               eauto.
               eassumption.
               eapply H12.
               left.
               congruence.
              assert ((offsets ld) ! ci <> None) by eauto using offsets_exist.
              case_eq ((offsets ld) ! ci); try congruence.
              intros.
              generalize (non_virtual_empty_base_offset_incl
                 hierarchy_wf (offsets_intro ( Hld)) (offsets_guard ( Hld))                 
                 H0 H8 H13).
              intros.
              destruct H4.
               (* case away *)
               generalize (nvl_high_bound prop H H13).
               omega.
              (* case not away *)
              revert H4.
              unfold f'.
              case_eq (filter (f x) e); try congruence.
              intros.
              generalize (filter_In (f x) (b, bo') e).
              rewrite H4.
               simpl.
               destruct 1.
               intro Habs.
               apply H17.
               split.
               generalize (nvebo_prop Hld He b (bo')).
               tauto.
               rewrite <- Habs.
               assert ((if In_dec (prod_eq_dec peq Z_eq_dec) (b, co + bo) (nvl_nvebo nvldata)
    then true
    else false) = true).
               case (In_dec (prod_eq_dec peq Z_eq_dec) (b, co + bo) (nvl_nvebo nvldata)).
                trivial.
               intros.
               destruct n.
               destruct (nvl_nvebo_prop prop b (co + bo)).
               apply H19.
               esplit.
               esplit.
               split.
               eassumption.
               replace (co + bo - co) with bo by omega.
               assumption.
              assumption.
            Qed.

            Lemma nv_offset_low_bound : 0 <= nv_offset.
            Proof.
              unfold nv_offset.
              destruct (bounded_offset align_pos  (if em then 0 else nvl_nvds nvldata) (nvl_nvsize nvldata) f').
               destruct a0.
               revert H.
               case em.
                tauto.               
              generalize (nvl_data_low_bound prop).
              intros; omega.
            Qed.

            Lemma nv_offset_align : (non_virtual_align o' | nv_offset).
            Proof.
              unfold nv_offset.
              destruct (bounded_offset align_pos  (if em then 0 else nvl_nvds nvldata) (nvl_nvsize nvldata) f').
              tauto.
            Qed.

            Lemma nv_offset_nonempty_low_bound : (is_empty hierarchy a -> False) -> nvl_nvds nvldata <= nv_offset.
            Proof.
              unfold nv_offset.
              destruct (bounded_offset align_pos  (if em then 0 else nvl_nvds nvldata) (nvl_nvsize nvldata) f').
              revert a0.
              case em.
               contradiction.
              tauto.
            Qed.

         Let g := map_snd (key := ident) (fun o => nv_offset + o).

(** Update the data to assign [nv_offset] to the non-virtual base. *)
               
         Definition non_virtual_direct_base_layout_step : {
           nvldata' | nvl_prop nvldata' /\ nvl_todo nvldata' = q
         }.
           exists (
             make_nvl
             (** remove [a] from [nvl_todo = a :: q] *) q
             (** assign [nv_offset] to [a] *) (PTree.set a nv_offset (nvl_offsets nvldata))
             (** add non-virtual empty base offsets of [a] to [nvl_nvebo] *) (List.map g e ++ nvl_nvebo nvldata)
             (** update data size if [a] is not empty *) (if em then nvl_nvds nvldata else (nv_offset + non_virtual_data_size o'))
             (** update size to the max *) (if Z_le_dec (nv_offset + non_virtual_size o') (nvl_nvsize nvldata) then (nvl_nvsize nvldata) else  (nv_offset + non_virtual_size o'))
             (** keep the same primary base *) (nvl_pbase nvldata)
             (** update alignment to the least common multiple *) (lcm (nvl_align nvldata) (non_virtual_align o'))
           ).
         Proof.
           split.
            inversion prop.
            constructor; simpl; try assumption.

            intro.
            destruct (nvl_exist0 ci).
            rewrite Htodo in H, H0.
            simpl in H, H0.            
             destruct (peq ci a).
             subst.
             rewrite PTree.gss.
             split.
             intros.
             left; congruence.
             intros.
             assumption.
            rewrite PTree.gso.
            assert (a = ci -> False) by congruence.
            split; tauto.
           assumption.

            intros.
            rewrite PTree.gso.
            eauto.
            generalize (nvl_primary_base0 _ H).
            intros.
            congruence.

            case em; intro.
             assumption.
            generalize (non_virtual_data_size_own_fields_offset (offsets_intro ( Hld) Ho')).
            generalize (own_fields_offset_low_bound (offsets_intro ( Hld) Ho')).
            generalize (nv_offset_low_bound).
            omega.

            intros.
            case em.
             eauto.
            intro.
            apply Zle_trans with (nvl_nvds nvldata).
             eauto.
            generalize (nv_offset_nonempty_low_bound n).
            generalize (non_virtual_data_size_own_fields_offset (offsets_intro ( Hld) Ho')).
            generalize (own_fields_offset_low_bound (offsets_intro ( Hld) Ho')).
            omega.

            destruct (Z_le_dec (nv_offset + non_virtual_size o') (nvl_nvsize nvldata)).
             assumption.
            apply Zlt_trans with (nvl_nvsize nvldata).
             assumption.
            omega.

            intros ? ?.
            destruct (peq ci a).
             subst.
             rewrite PTree.gss.
             injection 1; intros; subst of.
             exact nv_offset_low_bound.
            rewrite PTree.gso.
            eauto.
            assumption.

            intros ? ? ? ?.
            destruct (peq ci a).
             subst.
             rewrite PTree.gss.
             injection 1; intros; subst of.
             generalize (nv_offset_nonempty_low_bound H1).
             intros.
             apply Zle_trans with (nvl_nvds nvldata).
              eauto.
             assumption.            
            rewrite PTree.gso; eauto.

          intros ? ?.
          destruct (peq ci1 a).
           subst.
           rewrite PTree.gss.
           injection 1; intro; subst o1.
           intros.
           rewrite PTree.gso in H1.
           generalize (nvl_nonempty_high_bound prop H2 H1 H5).
           generalize (nv_offset_nonempty_low_bound H0).
           omega.
           congruence.
          rewrite PTree.gso.
          intros ? ? ? ?.
          destruct (peq ci2 a).
           subst.
           rewrite PTree.gss.
           injection 1; intros; subst o2.
           generalize (nvl_nonempty_high_bound prop H0 H H5).
           generalize (nv_offset_nonempty_low_bound H3).
           omega.
           rewrite PTree.gso.
           eauto.
           assumption.
          assumption.

          intros ? ?.
          destruct (peq ci1 a).
           subst.
           rewrite PTree.gss.
           injection 1; intro; subst o1.
           intros.
           rewrite PTree.gso in H0.
           cut (o2 + bo2 <> nv_offset + bo1).
            congruence.
            eauto using nv_offsets_non_overlap.
           congruence.
          rewrite PTree.gso.
          intros ? ? ?.
          destruct (peq ci2 a).
           subst.
           rewrite PTree.gss.
           injection 1; intros; subst o2.
           eauto using nv_offsets_non_overlap.
          rewrite PTree.gso.
          eauto.
          assumption.
          assumption.

          intros ? ? ?.
          destruct (peq ci a).
           subst ci.
           rewrite PTree.gss.
           injection 1; intro; subst of.
           rewrite Ho'.
           injection 1; intro; subst o'0.
           case em.
            contradiction.
           intro; omega.
          rewrite PTree.gso.
          intros.
          eapply Zle_trans with (nvl_nvds nvldata).
          eauto.
          case em.
           intros; omega.
          intros.
          generalize (nv_offset_nonempty_low_bound n0).
          generalize (non_virtual_data_size_own_fields_offset (offsets_intro ( Hld) Ho')).
          generalize (own_fields_offset_low_bound (offsets_intro ( Hld) Ho')).
          omega.
          assumption.

          intros ? ?.
          destruct (peq ci a).
           subst.
           rewrite PTree.gss.
           injection 1; intros; subst of.
           destruct ( Z_le_dec (nv_offset + non_virtual_size o') (nvl_nvsize nvldata)).
            congruence.
           replace o'0 with o' by congruence.
           omega.
          rewrite PTree.gso.
          intros.
          destruct ( Z_le_dec (nv_offset + non_virtual_size o') (nvl_nvsize nvldata)).    
           eauto.
          apply Zle_trans with (nvl_nvsize nvldata).
           eauto.
          omega.
         assumption.

         apply lcm_positive.
         assumption.
         eauto using non_virtual_align_low_bound.

         intro.
         apply Zdivide_trans with (nvl_align nvldata).
         eauto.
         apply lcm_divides_left.                 

         intro.
         destruct (peq ci a).
          subst.
          intros.
          replace of with o' by congruence.
          apply lcm_divides_right.
          eauto using non_virtual_align_low_bound.
         rewrite PTree.gso.
         intros.
         apply Zdivides_trans with (nvl_align nvldata).
          eauto.
         apply lcm_divides_left.
         assumption.

         intros ? ?.
         destruct (peq ci a).
          subst.
          rewrite PTree.gss.
          injection 1; intro; subst of.
          rewrite Ho'.
          injection 1; intros; subst co.
          exact nv_offset_align.
         rewrite PTree.gso; eauto.

         intros.
         split.
         intros.
         destruct (in_app_or _ _ _ H).
          destruct (list_in_map_inv _ _ _ H0).
          destruct H1.
          unfold g in H1.
          unfold map_snd in H1.
          destruct x.
          injection H1; intros; subst.
          destruct (nvebo_prop ( Hld) He i z).
          exists a.
          exists nv_offset.
          rewrite PTree.gss.
          split.
          trivial.
          replace (nv_offset + z - nv_offset) with z by omega.
          auto.
         destruct (nvl_nvebo_prop0 b o).
         destruct (H1 H0).
         destruct H3.
         destruct H3.
         exists x.
         exists x0.
         rewrite PTree.gso.
         eauto.
         congruence.
        destruct 1.
        destruct H.
        destruct H.
        destruct (peq x a).
         subst.
         rewrite PTree.gss in H.
         injection H; intro; subst x0.
         apply in_or_app.
         left.
         replace (b, o) with (g (b, o - nv_offset)).
         apply in_map.
         destruct (nvebo_prop ( Hld) He b (o - nv_offset)).
         auto.
         simpl.
         f_equal.
         omega.
        rewrite PTree.gso in H.
        apply in_or_app.
        right.
        destruct (nvl_nvebo_prop0 b o).
         apply H2.
         eauto.
        assumption.

        simpl.
        trivial.

      Qed.

    End Step.

(** Finalization: if at some point, some direct non-virtual bases have already been assigned an offset, then the following lemma tells how to deal with all the remaining direct non-virtual bases *)

    Definition non_virtual_direct_base_layout_end :
      forall nvldata, nvl_prop nvldata -> {
        nvldata' | nvl_prop nvldata' /\ nvl_todo nvldata' = nil
      }.
    Proof.
      intro.
      var (nvl_todo nvldata).
      revert v nvldata H.
      induction v.
       intros.
       exists nvldata.
       split.
       assumption.
       assumption.
      intros.
      case_eq ((nvl_offsets nvldata) ! a).
       intros.
       apply (IHv (
         make_nvl
         v
         (nvl_offsets nvldata)
         (nvl_nvebo nvldata)
         (nvl_nvds nvldata)
         (nvl_nvsize nvldata)
         (nvl_pbase nvldata)
         (nvl_align nvldata)
       )).
        reflexivity.
        inversion x.
        constructor; simpl; try trivial.
        intros.
        rewrite H in nvl_exist0.
        simpl in nvl_exist0.
        destruct (nvl_exist0 ci).
        split.
         destruct (peq a ci).
          subst.
          intros.
          left.
          congruence.
          tauto.
         tauto.

         intros.
        destruct (non_virtual_direct_base_layout_step x H).
         assumption.
        destruct a0.
        eauto.
      Qed.


(** Initialization. *)
    
    Section Init.

      Let f (x : _ * ident) :=
        match x with
          | (Class.Inheritance.Repeated, b) => b :: nil
          | _ => nil
        end.

      Let nvbases := flatten (map f (Class.super h)).

      Let g b := 
        if is_dynamic_dec hierarchy_wf b then true else false
          .

      Let dynbases := filter g nvbases.

(** There is a direct non-virtual primary base [a] of [cilimit ld]: choose it as the primary base *)
      
     Section Primary_base.

      Variable a : ident.

      Variable q : list ident.

      Hypothesis some_dynbase : dynbases = a :: q.

      Lemma nveb_inh : In (Class.Inheritance.Repeated, a) (Class.super h).
      Proof.
        destruct (filter_In g a nvbases).
        unfold dynbases in some_dynbase.
        rewrite some_dynbase in H.
        destruct (H (or_introl _ (refl_equal _))).
        destruct (member_flatten_elim H1).
        destruct H3.
        destruct (list_in_map_inv _ _ _ H3).
        destruct H5.
        destruct x0.
        subst.
        destruct t; simpl in H4; try contradiction.
        inversion H4; try contradiction.
        subst.
        assumption.
      Qed.

      Let inh := nveb_inh.

      Lemma nveb_dyn : is_dynamic hierarchy a.
      Proof.
        destruct (filter_In g a nvbases).
        unfold dynbases in some_dynbase.
        rewrite some_dynbase in H.
        destruct (H (or_introl _ (refl_equal _))).
        unfold g in H2.
        destruct (is_dynamic_dec hierarchy_wf a).
         assumption.
        discriminate.
      Qed.

      Let dyn := nveb_dyn.
 
      Let Hlt : Plt a (cilimit ld).
      Proof.
        eauto using Well_formed_hierarchy.well_founded.
      Qed.

      Let of'0 : {of' | (offsets ld) ! a = Some of'}.
      Proof.
        assert ((offsets ld) ! a <> None) by eauto using offsets_exist, Well_formed_hierarchy.complete.
        case_eq ((offsets ld) ! a).
         intros.
         repeat esplit.
        contradiction.
      Qed.

      Let of' := let (of', _) := of'0 in of'.

      Let Hof' : (offsets ld) ! a = Some of'.
      Proof.
        unfold of'.
        destruct of'0.
        assumption.
      Qed.


           Let e0 : {e | (nvebo ld) ! a = Some e}.
           Proof.
             generalize (nvebo_exist ( Hld) Hlt).
             case_eq ((nvebo ld) ! a); try congruence.
             intros.
             repeat esplit.
           Qed.

           Let e := let (e, _) := e0 in e.

           Let He :  (nvebo ld) ! a = Some e.
           Proof.
             unfold e.
             destruct e0.
             assumption.
           Qed.

           Let ne : is_empty hierarchy a -> False.
           Proof.
             eauto using dynamic_nonempty.
           Qed.

      Definition nvl_init_some_primary_base : {
        nv | nvl_prop nv
      }.
       exists (
         make_nvl
         nvbases
         (PTree.set a 0 (PTree.empty _))
         e
         (non_virtual_data_size of')
         (non_virtual_size of')
         (Some a)
         (non_virtual_align of')
       ).
    Proof.
     constructor; simpl.

     split.
     intros.
     right.
     unfold nvbases.     
     eapply member_flatten_intro with (f (Class.Inheritance.Repeated, ci)).
     eapply in_map.
     assumption.
     simpl.
     auto.
     inversion 1.
      destruct (peq ci a).
       subst ci.
       assumption.
      rewrite PTree.gso in H0.
      rewrite PTree.gempty in H0.
      congruence.
      assumption.
      unfold nvbases in H0.
      destruct (member_flatten_elim H0).
      destruct H1.
      destruct (list_in_map_inv _ _ _ H1).
      destruct H3.
      subst x.
      destruct x0.
      destruct t; simpl in H2.
       inversion H2; try contradiction.
       congruence.
      contradiction.

      injection 1; intros; subst ci.
      rewrite PTree.gss.
      trivial.

      congruence.

      generalize (non_virtual_data_size_own_fields_offset (offsets_intro ( Hld) Hof')).
      generalize (own_fields_offset_low_bound (offsets_intro ( Hld) Hof')).
      omega.

      intros.
      generalize (own_fields_offset_dynamic_low_bound (offsets_intro ( Hld) Hof' ) dyn).
      generalize (non_virtual_data_size_own_fields_offset (offsets_intro ( Hld) Hof')).
      omega.

      exact (non_virtual_size_positive (offsets_intro ( Hld) Hof' )).

      intros ? ?.
      destruct (peq ci a).
       subst ci.
       rewrite PTree.gss.
       injection 1; intros; subst of; omega.
       rewrite PTree.gso.
       rewrite PTree.gempty.
       congruence.
       assumption.

     congruence.

     intros ? ?.
     destruct (peq ci1 a).
      subst ci1.
      intros.
      rewrite PTree.gso in H1.
      rewrite PTree.gempty in H1.
      discriminate.
      congruence.
     rewrite PTree.gso.
     rewrite PTree.gempty.
     congruence.
     assumption.

     intros ? ?.
     destruct (peq ci1 a).
      subst ci1.
      intros.
      rewrite PTree.gso in H0.
      rewrite PTree.gempty in H0.
      discriminate.
      congruence.
     rewrite PTree.gso.
     rewrite PTree.gempty.
     congruence.
     assumption.

     intros ? ? ?.
     destruct (peq ci a).
      subst ci.
      rewrite PTree.gss.
      injection 1; intros; subst of.
      replace o' with of' by congruence.
      omega.
      rewrite PTree.gso.
      rewrite PTree.gempty.
      congruence.
      assumption.

      intros ? ?.
      destruct (peq ci a).
      subst ci.
      rewrite PTree.gss.
      injection 1; intros; subst of.
      replace o' with of' by congruence.
      omega.
      rewrite PTree.gso.
      rewrite PTree.gempty.
      congruence.
      assumption.

      exact (non_virtual_align_low_bound (offsets_intro ( Hld) Hof' )).

      intros.
      eapply non_virtual_align_dynamic.
      eapply offsets_intro.
      eauto.
      eauto.
      eauto.

      intro.
      destruct (peq ci a).
       subst ci.
       intros.
       replace of with of' by congruence.
       apply Zdivide_refl.       
       rewrite PTree.gso.
       rewrite PTree.gempty.
       congruence.
       assumption.

      intros ? ?.
      destruct (peq ci a).
       subst ci.
       rewrite PTree.gss.
       injection 1; intros; subst of.
       exists 0.
       omega.
      rewrite PTree.gso.
      rewrite PTree.gempty.
      congruence.
      assumption.      

      intros.
      destruct (nvebo_prop ( Hld) He b o).
      split.
      intros.
      exists a.
      exists 0.
      split.
       rewrite PTree.gss.
       trivial.
     replace (o - 0) with o by omega.
     auto.
     destruct 1.
     destruct H1.
     destruct H1.
     apply H0.
     destruct (peq x a).
      subst x.
      rewrite PTree.gss in H1.
      injection H1; intros; subst x0.
     replace o with (o - 0) by omega.
     assumption.
     rewrite PTree.gso in H1.
     rewrite PTree.gempty in H1.
     discriminate.
     assumption.
   Qed.

   End Primary_base.

(** The class is dynamic, but has no primary base *)

   Section No_primary_base.

     Section Dynamic.

       Hypothesis dyn : is_dynamic hierarchy (cilimit ld).

     Definition nvl_init_dynamic_no_primary_base : {
        nv | nvl_prop nv
      }.
       exists (
         make_nvl
         nvbases
         (PTree.empty _)
         nil        
         (dynamic_type_data_size PF)
         (dynamic_type_data_size PF)
         None
         (dynamic_type_data_align PF)
       ).
      Proof.
     constructor; simpl; try rewrite PTree.gempty; try congruence.

     split.
     intros.
     right.
     unfold nvbases.     
     eapply member_flatten_intro with (f (Class.Inheritance.Repeated, ci)).
     eapply in_map.
     assumption.
     simpl.
     auto.
     rewrite PTree.gempty.
     inversion 1.
      congruence.
      unfold nvbases in H0.
      destruct (member_flatten_elim H0).
      destruct H1.
      destruct (list_in_map_inv _ _ _ H1).
      destruct H3.
      subst.
      destruct x0.
      destruct t; simpl in H2.
       inversion H2; try contradiction.
       congruence.
      contradiction.

      generalize (dynamic_type_data_size_low_bound PF).
      omega.
      
      omega.

      apply dynamic_type_data_size_low_bound.

      intros ? ?.
      rewrite PTree.gempty.
      congruence.

      intros until 3.
      intros ?.
      rewrite PTree.gempty.
      congruence.

      intros ? ?.
      rewrite PTree.gempty.
      congruence.

      intros ? ?.
      rewrite PTree.gempty.
      congruence.

      intros ? ? ?.
      rewrite PTree.gempty.
      congruence.

      intros ? ?.
      rewrite PTree.gempty.
      congruence.

      apply dynamic_type_data_align_low_bound.

      intros; apply Zdivide_refl.

      intros ?.
      rewrite PTree.gempty.
      congruence.

      intros ? ?.
      rewrite PTree.gempty.
      congruence.

      split.
       tauto.
      destruct 1.
      destruct H.
      destruct H.
      rewrite PTree.gempty in H.
      discriminate.
    Qed.

  End Dynamic.


(** The class is not dynamic *)

  Section Non_dynamic.

       Hypothesis dyn : is_dynamic hierarchy (cilimit ld) -> False.

     Definition nvl_init_non_dynamic : {
        nv | nvl_prop nv
      }.
       exists (
         make_nvl
         nvbases
         (PTree.empty _)
         nil
         0
         1
         None
         1
       ).
      Proof.
     constructor; simpl; try rewrite PTree.gempty; try congruence; try omega.

     split.
     intros.
     right.
     unfold nvbases.     
     eapply member_flatten_intro with (f (Class.Inheritance.Repeated, ci)).
     eapply in_map.
     assumption.
     simpl.
     auto.
     rewrite PTree.gempty.
     inversion 1.
      congruence.
      unfold nvbases in H0.
      destruct (member_flatten_elim H0).
      destruct H1.
      destruct (list_in_map_inv _ _ _ H1).
      destruct H3.
      subst.
      destruct x0.
      destruct t; simpl in H2.
       inversion H2; try contradiction.
       congruence.
      contradiction.

      intros ? ?.
      rewrite PTree.gempty.
      congruence.

      intros ? ?.
      rewrite PTree.gempty.
      congruence.

      intros ? ?.
      rewrite PTree.gempty.
      congruence.

      intros ? ? ?.
      rewrite PTree.gempty.
      congruence.

      intros ? ?.
      rewrite PTree.gempty.
      congruence.
      
      intros ?.
      rewrite PTree.gempty.
      congruence.

      intros ? ?.
      rewrite PTree.gempty.
      congruence.


      split.
       tauto.
      destruct 1.
      destruct H.
      destruct H.
      rewrite PTree.gempty in H.
      discriminate.
    Qed.

  End Non_dynamic.
     
  End No_primary_base.


(** Finally, pack all together *)

  Definition non_virtual_direct_base_layout : {
    nvldata | nvl_prop nvldata /\ nvl_todo nvldata = nil
  }.
  Proof.
   case_eq dynbases.
    intros.
    destruct (is_dynamic_dec hierarchy_wf (cilimit ld)).
     destruct (nvl_init_dynamic_no_primary_base).
     eauto using non_virtual_direct_base_layout_end. 
    destruct (nvl_init_non_dynamic).
     assumption.
    eauto using non_virtual_direct_base_layout_end.
    intros.
    destruct (nvl_init_some_primary_base H).
    eauto using non_virtual_direct_base_layout_end.
  Qed.

End Init.

End Non_virtual_direct_base_layout.

(** Let [nvldata] be the layout of direct non-virtual bases. Then, [nvl_nvdsize nvldata], the data size so far before laying out fields, is the field boundary. *)

Let nvldata := let (k, _) := non_virtual_direct_base_layout in k.

Let H_nvldata : nvl_prop nvldata.
Proof.
  unfold nvldata.
  destruct non_virtual_direct_base_layout.
  tauto.
Qed.

Let H_nvldata_2 : nvl_todo nvldata = nil.
Proof.
  unfold nvldata.
  destruct non_virtual_direct_base_layout.
  tauto.
Qed.

(** ** Layout of fields *)

Section Field_layout.

(** 
- [fl_todo]: the list of fields to which an offset has not yet been assigned
- [fl_offsets]: the mapping between fields and offsets
- [fl_ebo]: the set of empty base offsets reachable through a field that has already been assigned an offset
- [fl_nvds]: the non-virtual data size so far.
- [fl_nvsize]: the non-virtual size so far.
- [fl_align]: the non-virtual alignment so far.
 *)


         Record fl : Type := make_fl {
           fl_todo : list (FieldSignature.t A);
           fl_offsets : list (FieldSignature.t A * Z);
           fl_ebo : list (ident * Z);
           fl_nvds : Z;
           fl_nvsize : Z;
           fl_align : Z
         }.

         Section prop.

           Variable fldata : fl.

           Record fl_prop : Prop := fl_intro {             
             (** Guard *)
             fl_exist : forall fs, (In fs (Class.fields h) <->  (assoc (FieldSignature.eq_dec (A := A)) fs (fl_offsets fldata) <> None \/ In fs (fl_todo fldata)));
             (** C11 *)
             fl_data_low_bound : nvl_nvds nvldata <= fl_nvds fldata;
             (** Helper for C1 *)
             fl_size_low_bound : nvl_nvsize nvldata <= fl_nvsize fldata;
             (** Guard *)
             fl_low_bound : forall fs of, assoc (FieldSignature.eq_dec (A := A)) fs (fl_offsets fldata) = Some of -> 0 <= of;
             (** C8 *)
fl_nonempty_low_bound : forall fs of, assoc (FieldSignature.eq_dec (A := A)) fs (fl_offsets fldata) = Some of -> (forall ty n, FieldSignature.type fs = FieldSignature.Struct ty n -> is_empty hierarchy ty -> False) ->  nvl_nvds nvldata <= of;
             (** C9 *)
             fl_non_overlap : forall fs1 o1, assoc (FieldSignature.eq_dec (A := A)) fs1 (fl_offsets fldata)  = Some o1 ->  (forall ty n, FieldSignature.type fs1 = FieldSignature.Struct ty n -> is_empty hierarchy ty -> False) -> forall fs2 o2, assoc (FieldSignature.eq_dec (A := A)) fs2 (fl_offsets fldata) = Some o2 -> fs1 <> fs2 ->  (forall ty n, FieldSignature.type fs2 = FieldSignature.Struct ty n -> is_empty hierarchy ty -> False) -> forall s1, field_data_size PF (offsets ld) fs1 = Some s1 -> forall s2, field_data_size PF (offsets ld) fs2 = Some s2 -> o1 + s1 <= o2 \/ o2 + s2 <= o1;
             (** C24 *)
             fl_disjoint_empty_bases : forall fs1 o1, assoc (FieldSignature.eq_dec (A := A)) fs1 (fl_offsets fldata) = Some o1 -> forall ci1 p1, FieldSignature.type fs1 = FieldSignature.Struct ci1 p1 -> forall z1, 0 <= z1 -> z1 < Zpos p1 -> forall so1, (offsets ld) ! ci1 = Some so1 -> forall b bo1, empty_base_offset Optim (offsets ld) hierarchy ci1 b bo1 -> forall ci2 o2, (nvl_offsets nvldata) ! ci2 = Some o2 -> forall bo2, non_virtual_empty_base_offset Optim (offsets ld) hierarchy ci2 b bo2 -> o1 + z1 * size so1 + bo1 <> o2 + bo2;
             (** C25 *)
             fl_disjoint_empty_bases_fields : forall fs1 o1, assoc (FieldSignature.eq_dec (A := A)) fs1 (fl_offsets fldata) = Some o1 -> forall ci1 p1, FieldSignature.type fs1 = FieldSignature.Struct ci1 p1 -> forall z1, 0 <= z1 -> z1 < Zpos p1 -> forall so1, (offsets ld) ! ci1 = Some so1 -> forall b bo1, empty_base_offset Optim (offsets ld) hierarchy ci1 b bo1 -> forall fs2 o2, assoc (FieldSignature.eq_dec (A := A)) fs2 (fl_offsets fldata) = Some o2 -> forall ci2 p2, FieldSignature.type fs2 = FieldSignature.Struct ci2 p2 -> forall z2, 0 <= z2 -> z2 < Zpos p2 -> forall so2, (offsets ld) ! ci2 = Some so2 -> forall bo2, empty_base_offset Optim (offsets ld) hierarchy ci2 b bo2 -> fs1 <> fs2 -> 
               o1 + z1 * size so1 + bo1 <> o2 + z2 * size so2 + bo2;
             (** C10 *)
             fl_nonempty_high_bound : forall fs of, assoc (FieldSignature.eq_dec (A := A)) fs (fl_offsets fldata) = Some of ->  (forall ty n, FieldSignature.type fs = FieldSignature.Struct ty n -> is_empty hierarchy ty -> False) -> forall s, field_data_size PF (offsets ld) fs = Some s -> of + s <= fl_nvds fldata;
             (** C2 *)
             fl_high_bound : forall fs of, assoc (FieldSignature.eq_dec (A := A)) fs (fl_offsets fldata) = Some of -> forall s, field_size PF (offsets ld) fs = Some s -> of + s <= fl_nvsize fldata;
             (** Guard *)
             fl_align_pos : 0 < fl_align fldata;
             (** Helper for C15 and C16 *)
             fl_align_nvl : (nvl_align nvldata | fl_align fldata);
             (** C14 *)
             fl_align_prop : forall fs, assoc (FieldSignature.eq_dec (A := A)) fs (fl_offsets fldata) <> None -> forall al, field_align PF (offsets ld) fs = Some al -> (al | fl_align fldata);
             fl_offset_align : forall fs fo, assoc (FieldSignature.eq_dec (A := A)) fs (fl_offsets fldata) = Some fo -> forall al, field_align PF (offsets ld) fs = Some al -> (al | fo);
             (** Specification of [fl_ebo], the set of the empty base offsets reachable through a field of [cilimit ld] *)
             fl_ebo_prop : forall b o, (In (b, o) (fl_ebo fldata) <-> exists fs, exists of, assoc (FieldSignature.eq_dec (A := A)) fs (fl_offsets fldata) = Some of /\ exists ci, exists n, FieldSignature.type fs = FieldSignature.Struct ci n /\ exists i, 0 <= i /\ i < Zpos n /\ exists oo, (offsets ld) ! ci = Some oo /\ empty_base_offset Optim (offsets ld) hierarchy ci b (o - of - i * size oo))
           }.

           End prop.

           Section Step.


             Variable fldata : fl.

           Hypothesis prop : fl_prop fldata.

(** Trying to assign an offset to the field [fs0] of [cilimit ld] *)

           Variable fs0 : FieldSignature.t A.

           Variable q : list (FieldSignature.t A).

           Hypothesis Htodo : fl_todo fldata = fs0 :: q.

           Hypothesis undef: assoc (FieldSignature.eq_dec (A := A))  fs0 (fl_offsets fldata)  = None.

             Let son : In fs0 (Class.fields h).
             Proof.
               destruct (fl_exist prop fs0).
               apply H0.
               rewrite Htodo.
               auto.
             Qed.


(** [fs0] is a structure array field of type [a] *)

           Section Struct.

             Variable a : ident.

             Variable na : positive.

             Hypothesis Hstruct : FieldSignature.type fs0 = FieldSignature.Struct a na.

           Let Hlt : (Plt a (cilimit ld)). 
           Proof.
             eauto using Well_formed_hierarchy.well_founded_struct.
           Qed.

           Definition fstruct_orig_offset : {o' | (offsets ld) ! a = Some o'}.
           Proof.
             assert ((offsets ld) ! a <> None) by eauto using offsets_exist, Well_formed_hierarchy.complete_struct.
             case_eq ((offsets ld) ! a); try congruence.
             intros.
             repeat esplit.
           Qed.

           Let o' := let (o', _) := fstruct_orig_offset in o'.

           Let Ho' : (offsets ld) ! a = Some o'.
           Proof.
             unfold o'.
             destruct fstruct_orig_offset.
             assumption.
           Qed.

           Definition fstruct_e0 : {e | (ebo ld) ! a = Some e}.
           Proof.
             generalize (ebo_exist ( Hld) Hlt).
             case_eq ((ebo ld) ! a); try congruence.
             intros.
             repeat esplit.
           Qed.

           Let e := let (e, _) := fstruct_e0 in e.

           Let He :  (ebo ld) ! a = Some e.
           Proof.
             unfold e.
             destruct fstruct_e0.
             assumption.
           Qed.

(** [fstruct_e'0_aux] constructs the union of all << j * sizeof(a) + ebo(a) >> for each j such that 0 <= j < n *)

           Definition fstruct_e'0_aux : forall k, 0 <= k -> 0 <= k <= Zpos na ->
             forall l, (forall b o, In (b, o) l <-> exists j, 0 <= j /\ j < Zpos na - k /\ In (b, o - j * size o') e) ->
               {l | forall b o, In (b, o) l <-> exists j, 0 <= j /\ j < Zpos na /\ In (b, o - j * size o') e}.
           Proof.
             intros until 1.
             pattern k.
             eapply Z_lt_rec; try eassumption.
             intros.
             clear k H.
             destruct (Z_eq_dec x 0).
              subst.
              replace (Zpos na - 0) with (Zpos na) in H2 by omega.
              exists l; assumption.
             assert (0 <= x - 1 <= Zpos na) by omega.
             assert (0 <= x - 1 < x) by omega.
             apply (H0 _ H3 H (map (map_snd (fun o => o + (Zpos na - x) * size o')) e ++ l)).
             intros.
             assert (forall A B C : Prop, (A <-> B) -> (B <-> C) -> (A <-> C)) by tauto.
             refine (H4 _ _ _ (in_app (b, o) _ _) _).             
             split.
              destruct 1.
               destruct (list_in_map_inv _ _ _ H5).
               destruct H6.
               destruct x0.
               Opaque Zmult Zplus Zminus. simpl in H6.
               injection H6; intros; subst.
               exists (Zpos na - x).
                split.
                Transparent Zminus. omega.
                split.
                 omega.
                replace (z + (Zpos na - x) * size o' - (Zpos na - x) * size o') with z by omega.
                assumption.
               destruct (H2 b o).
               destruct (H6 H5).
               destruct H8.
               destruct H9.
               exists x0.
               split.
                omega.
               split.
                omega.
               assumption.
              destruct 1.
              destruct H5.
              destruct H6.
              pattern (b, o) at 1.
              replace (b, o) with (map_snd (fun o0 => o0 + (Zpos na - x) * size o') (b, o - (Zpos na - x) * size o')).
              destruct (Z_eq_dec x0 (Zpos na - x)).
               subst.
               left.
               apply in_map.
               assumption.
              right.
              destruct (H2 b o).
              apply H9.
              exists x0.
              split.
               omega.
              split.
               omega.
              assumption.
             Opaque Zminus. simpl.
             f_equal.
             Transparent Zminus. omega.
           Qed.

           Definition fstruct_e'0 :
             {l | forall b o, In (b, o) l <-> exists j, 0 <= j /\ j < Zpos na /\ In (b, o - j * size o') e}.
           Proof.
             refine (@fstruct_e'0_aux (Zpos na) _ _ nil _).
             generalize (Zpos_positive na).
             omega.
             generalize (Zpos_positive na).
             omega.
             Opaque Zminus. simpl.
             split.
              tauto.
             destruct 1.
             Transparent Zminus. omega.
           Qed.

           Let e' := let (e', _) := fstruct_e'0 in e'.

           Let He' :  forall b o, In (b, o) e' <-> exists j, 0 <= j /\ j < Zpos na /\ In (b, o - j * size o') e.
           Proof.
             unfold e'.
             destruct fstruct_e'0.
             assumption.
           Qed.

(** 
   The offset [fl_offset] assigned to [fs0] is computed as follows:
   - starting from 0 if [fs0] is empty, from [fl_nvds fldata] (the non-virtual data size so far) otherwise
   - find the least offset [o] multiple of the alignment of [a], and such that the set [e'] of empty base offsets reachable from any cell of the array of [a] is disjoint from [nvl_nvebo] the offsets of non-virtual empty base offsets so far, and from [fl_ebo] the empty base offsets reachable from other fields so far, knowing that there will be no conflict if [o >= fl_nvsize fldata]
   See [LibPos] for a definition of [bounded_offset].
*)


           Let em := is_empty_dec hierarchy_wf a.
           
           Let f z (x : _ * _) :=
             let (b, o) := x in
               if In_dec (prod_eq_dec peq Z_eq_dec) (b, z + o) (nvl_nvebo nvldata) then true else
                 if In_dec (prod_eq_dec peq Z_eq_dec) (b, z + o) (fl_ebo fldata) then true else
 false.

             Definition fstruct_off0 : {z | (if em then 0 else fl_nvds fldata) <= z /\ (align o' | z) /\ (fl_nvsize fldata <= z \/ List.filter (f z) e' = nil)}.
             Proof.
               destruct (bounded_offset (align_low_bound (offsets_intro ( Hld) Ho')) (if em then 0 else fl_nvds fldata) (fl_nvsize fldata) (fun z => match List.filter (f z) e' with nil => true | _ => false end)).
               destruct a0.
               destruct H0.
               esplit.
               split.
               eassumption.
               split.
               assumption.
               destruct H1.
                tauto.
               destruct (filter (f x) e'); try discriminate.
               auto.
             Qed.

            Definition fl_offset := let (z, _) := fstruct_off0 in z.

            Lemma fl_offset_prop : (if em then 0 else fl_nvds fldata) <= fl_offset /\ (align o' | fl_offset) /\ (fl_nvsize fldata <= fl_offset \/ List.filter (f fl_offset) e' = nil).
            Proof.
              unfold fl_offset.
              destruct fstruct_off0.
              assumption.
            Qed.

            Lemma fl_offsets_non_overlap : forall ci co, (nvl_offsets nvldata) ! ci = Some co -> forall b bo, non_virtual_empty_base_offset Optim (offsets ld) hierarchy ci b bo -> forall i, 0 <= i -> i < Zpos na -> forall bo', empty_base_offset Optim (offsets ld) hierarchy a b bo' -> co + bo <> fl_offset + i * size o' + bo'.
            Proof.
              intros.
              destruct fl_offset_prop.
              destruct H5.
              generalize (fl_size_low_bound prop).
              intro.
              assert (Plt ci (cilimit ld)).
               destruct (nvl_exist H_nvldata ci).
               eapply Well_formed_hierarchy.well_founded.
               eauto.
               eauto.
               eapply H9.
               left.
               congruence.
              destruct (non_virtual_empty_base_offset_wf 
                 hierarchy_wf (offsets_intro ( Hld)) (offsets_guard ( Hld))  H0).
              assert ((offsets ld) ! b <> None).
               eapply offsets_exist.
                eauto.
                eauto using Ple_Plt_trans.
                assumption.
               case_eq ((offsets ld) ! b) ; try congruence.
               intros.               
               generalize (empty_base_offset_incl hierarchy_wf
                 (offsets_intro ( Hld)) (offsets_guard ( Hld))
                 H3 H11 Ho').
               intros.
               assert (hierarchy ! ci <> None).
                destruct (nvl_exist H_nvldata ci).
                eapply Well_formed_hierarchy.complete.
                eauto.
                eassumption.
                eapply H15.
                left.
                congruence.
               assert ((offsets ld) ! ci <> None) by eauto using offsets_exist.
               case_eq ((offsets ld) ! ci); try congruence.
               intros.
               generalize (non_virtual_empty_base_offset_incl hierarchy_wf
                 (offsets_intro ( Hld)) (offsets_guard ( Hld))  
                 H0 H11 H16).
               intros.
               generalize (nvl_high_bound H_nvldata H H16).
               intros.
               assert (0 <= size o') by omega.
               generalize (Zmult_ge H1 H19).
               intros.
              inversion H6.
               (* case away *)
               omega.
              (* case disjoint_offset *)
               destruct (ebo_prop ( Hld) He b bo').
               generalize (H23 H3).
               intros.
               intro Habs.
               destruct (filter_In (f fl_offset) (b, i * size o' + bo') e').
               rewrite H21 in H26.
               simpl in H26.
               apply H26.
               split.
                destruct (He' b (i * size o' + bo')).
                apply H28.
                exists i.
                split.
                 assumption.
                split.
                 assumption.
                replace ( i * size o' + bo' - i * size o') with bo' by omega.
                assumption.
               rewrite Zplus_assoc.
               rewrite <- Habs.
               assert (
                 (if In_dec (prod_eq_dec peq Z_eq_dec) (b, co + bo) (nvl_nvebo nvldata)
                   then true
                   else
                     if In_dec (prod_eq_dec peq Z_eq_dec) (b, co + bo) (fl_ebo fldata)
                       then true
                       else false) = true
               ).
               case (In_dec (prod_eq_dec peq Z_eq_dec) (b, co + bo) (nvl_nvebo nvldata)  ).
                tauto.
               intros.
               destruct n.
               destruct (nvl_nvebo_prop H_nvldata b (co + bo)).
               apply H28.
               esplit.
               esplit.
               split.
               eassumption.
               replace (co + bo - co) with bo by omega.
               assumption.
              assumption.
           Qed.

           Lemma fl_disjoint_field_empty_bases :  forall z1, 0 <= z1 -> z1 < Zpos na -> forall b bo1, empty_base_offset Optim (offsets ld) hierarchy a b bo1 -> 
             forall fs2 o2, assoc (FieldSignature.eq_dec (A := A)) fs2 (fl_offsets fldata) = Some o2 -> forall ci2 p2, FieldSignature.type fs2 = FieldSignature.Struct ci2 p2 -> forall z2, 0 <= z2 -> z2 < Zpos p2 -> forall so2, (offsets ld) ! ci2 = Some so2 -> forall bo2, empty_base_offset Optim (offsets ld) hierarchy ci2 b bo2 -> 
               fl_offset + z1 * size o' + bo1 <> o2 + z2 * size so2 + bo2.
           Proof.
              intros.
              destruct fl_offset_prop.
              destruct H9.
              intro.
              assert (Plt ci2 (cilimit ld)).
               destruct (fl_exist prop fs2).
               eapply Well_formed_hierarchy.well_founded_struct.
               eauto.
               eauto.
               eapply H13.
               left.
               congruence.
               eassumption.
              destruct (empty_base_offset_wf 
                 hierarchy_wf (offsets_intro ( Hld)) (offsets_guard ( Hld))  H7).
              assert ((offsets ld) ! b <> None).
               eapply offsets_exist.
                eauto.
                eauto using Ple_Plt_trans.
                assumption.
               case_eq ((offsets ld) ! b) ; try congruence.
               intros.               
               generalize (empty_base_offset_incl hierarchy_wf
                 (offsets_intro ( Hld)) (offsets_guard ( Hld))
                 H1 H15 Ho').
               intros.
               generalize (empty_base_offset_incl hierarchy_wf
                 (offsets_intro ( Hld)) (offsets_guard ( Hld))  
                 H7 H15 H6).
               intros.
               generalize (fl_high_bound prop H2).
                unfold field_size.
                rewrite H3.
                rewrite H6.
                intro.
               generalize (H19 _ (refl_equal _)).
               intros.
               assert (z2 <= (Zpos p2 - 1)) by omega.
               generalize (size_positive (offsets_intro Hld) H6).
               intros.
               assert (0 <= size so2) by omega.
               generalize (Zmult_le_compat_r _ _ _ H21 H23).               
               intros.
               assert (0 <= size o') by omega.
               generalize (Zmult_ge H H25).
               intros.
               generalize (Zmult_ge H4 H23).
               intros.
              inversion H10.
              (* case away *)
               omega.
              (* case disjoint_offset *)
               destruct (ebo_prop ( Hld) He b bo1).
               generalize (H30 H1).
               intros.
               destruct (filter_In (f fl_offset) (b, z1 * size o' + bo1) e').
               rewrite H28 in H33.
               simpl in H33.
               apply H33.
               split.
                destruct (He' b (z1 * size o' + bo1)).
                apply H35.
                exists z1.
                split.
                 assumption.
                split.
                 assumption.
                replace ( z1 * size o' + bo1 - z1 * size o') with bo1 by omega.
                assumption.
               rewrite Zplus_assoc.
               rewrite H11.
               assert (
                 (if In_dec (prod_eq_dec peq Z_eq_dec) (b, o2 + z2 * size so2 + bo2)
                   (nvl_nvebo nvldata)
                   then true
                   else
                     if In_dec (prod_eq_dec peq Z_eq_dec) (b, o2 + z2 * size so2 + bo2)
                       (fl_ebo fldata)
                       then true
                       else false) = true
               ).
               case (In_dec (prod_eq_dec peq Z_eq_dec) (b, o2 + z2 * size so2 + bo2)
                       (fl_ebo fldata)).
                destruct (
                  In_dec (prod_eq_dec peq Z_eq_dec) (b, o2 + z2 * size so2 + bo2)
         (nvl_nvebo nvldata)
                ); trivial.
               intros.
               destruct n.
               destruct (fl_ebo_prop prop b (o2 + z2 * size so2 + bo2)).
               apply H35.
               esplit.
               esplit.
               split.
               eassumption.
               esplit.
               esplit.
               split.
                eassumption.
               esplit.
               split.
               2 : split.
               2 : eassumption.
               assumption.
               esplit.
               split.
               eassumption.
               replace (o2 + z2 * size so2 + bo2 - o2 - z2 * size so2) with bo2 by omega.
               assumption.
              assumption.
            Qed.


           Let g := map_snd (key := ident) (fun o => fl_offset + o).
           
           Definition field_layout_step_struct : {
             fldata' | fl_prop fldata' /\ fl_todo fldata' = q
           }.
           exists (
             make_fl
             (** remove [fs0] from [fl_todo fldata = fs0 :: q] *) q
             (** assign [fl_offset] to [fs0] *) ((fs0, fl_offset) :: (fl_offsets fldata))
             (** add the empty base offsets reachable from [fs0] *) (List.map g e' ++ fl_ebo fldata)
             (** update the data size if [a] is not empty *) (if em then fl_nvds fldata else fl_offset + (Zpos na - 1) * size o' + data_size o')
             (** update the size to the max *) (if Z_le_dec (fl_offset + Zpos na * size o') (fl_nvsize fldata) then (fl_nvsize fldata) else  (fl_offset + Zpos na * size o'))
             (** update the alignment to the least common multiple *) (lcm (fl_align fldata) (align o'))
           ).
          Proof.
           Opaque Zminus.
           split; simpl; try trivial.
            inversion prop.
            constructor; simpl; try assumption.

            intro.
            destruct (fl_exist0 fs).
            rewrite Htodo in H, H0.
            simpl in H, H0.            
             destruct ((FieldSignature.eq_dec (A := A)) fs0 fs).
             subst fs.
             split.
             intros.
             left; congruence.
             intros.
             assumption.
            assert (fs0 = fs -> False) by congruence.
            split; tauto.

            destruct (fl_offset_prop).
            revert H.
            destruct em.
             eauto.
            intros.
            apply Zle_trans with (fl_nvds fldata).
             eauto.
            assert (0 < size o') by eauto using size_positive, offsets_intro.
            assert (0 < Zpos na) by eauto using Zpos_positive.
            Transparent Zminus.
            assert (0 <= Zpos na - 1) by omega.
            assert (0 <= size o') by omega.            
            assert (0 <= data_size o').
             generalize (non_virtual_data_size_own_fields_offset (offsets_intro Hld Ho')).
             generalize (own_fields_offset_low_bound (offsets_intro Hld Ho')).
             generalize (virtual_base_offsets_data_size (offsets_intro Hld Ho') (virtual_base_offsets_self (offsets_intro Hld Ho')) n Ho').
             omega.
            generalize (Zmult_ge H3 H4).
            omega.

            destruct (Z_le_dec (fl_offset + Zpos na * size o') (fl_nvsize fldata)); omega.

            intros ? ?.
            destruct ((FieldSignature.eq_dec (A := A)) fs0 fs).
             injection 1; intro; subst of.
             destruct fl_offset_prop.
             revert H0.
             destruct em.
              tauto.
             intros.
             generalize (nvl_data_low_bound H_nvldata).
             omega.
            eauto.

            intros ? ?.
            destruct ((FieldSignature.eq_dec (A := A)) fs0 fs).
             subst fs.
             injection 1; intro; subst of.
             rewrite Hstruct.
             intros.
             destruct fl_offset_prop.
             revert H1.
             destruct em.
              destruct (H0 _ _ (refl_equal _)).
              assumption.
             intros.
             generalize (fl_data_low_bound prop).
             omega.
            eauto.

            intros ? ?.
            destruct ((FieldSignature.eq_dec (A := A)) fs0 fs1).
             subst fs1.
             injection 1; intro; subst o1.
             rewrite Hstruct.
             intros ? ? ?.
             destruct ((FieldSignature.eq_dec (A := A)) fs0 fs2).
              subst fs2.
              congruence.
             unfold field_data_size at 1.
             rewrite Hstruct.
             rewrite Ho'.
             intros.
             Opaque Zminus.
             injection H4.
             intros; subst s1.
             right.             
             apply Zle_trans with (fl_nvds fldata).
              eauto.
             destruct fl_offset_prop.
             revert H6.
             destruct em.
              destruct (H0 _ _ (refl_equal _)).
              assumption.
             tauto.
             intros ? ? ?.
             destruct ((FieldSignature.eq_dec (A := A)) fs0 fs2).
             subst fs2.
              injection 1; intro; subst o2.
              unfold field_data_size at 2.
              rewrite Hstruct.
              rewrite Ho'.
              injection 3; intros; subst.
              left.
              apply Zle_trans with (fl_nvds fldata).
              eauto.
              destruct fl_offset_prop.
              revert H7.
              destruct em.
               destruct (H3 _ _ (refl_equal _)).
               assumption.
              tauto.
             eauto.

             intros ? ?.
             destruct ((FieldSignature.eq_dec (A := A)) fs0 fs1).
              subst fs1.
              injection 1; intro; subst o1.
              rewrite Hstruct.
              injection 1; intros until 2; subst ci1 p1.
              rewrite Ho'.
              injection 3; intros; subst so1.
              intros.
              cut (o2 + bo2 <> fl_offset + z1 * size o' + bo1).
               congruence.
              eauto using fl_offsets_non_overlap.
             eauto.

            intros ? ?.
            destruct ((FieldSignature.eq_dec (A := A)) fs0 fs1).
             subst fs1.
             injection 1; intro; subst o1.
             rewrite Hstruct.
             injection 1; intros until 2; subst ci1 p1.
             rewrite Ho'.
             injection 3; intro; subst so1.
             intros ? ? ? ? ?.
             destruct ((FieldSignature.eq_dec (A := A)) fs0 fs2).
              subst fs2.
              congruence.
              intros; eauto using fl_disjoint_field_empty_bases.
             intros until 6.
             intros ? ?.
             destruct ((FieldSignature.eq_dec (A := A)) fs0 fs2).
             subst fs2.
              injection 1; intro; subst o2.
              rewrite Hstruct.
              injection 1; intros until 2; subst ci2 p2.
              rewrite Ho'.
              injection 3; intro; subst so2.
              intros.
              cut ( fl_offset + z2 * size o' + bo2 <>  o1 + z1 * size so1 + bo1).
               congruence.
              eauto using fl_disjoint_field_empty_bases.
             eauto.

             intros ? ?.
             destruct ((FieldSignature.eq_dec (A := A)) fs0 fs).
              subst fs.
              injection 1; intro; subst of.
              unfold field_data_size.
              rewrite Hstruct.
              rewrite Ho'.
              injection 2; intros; subst.
              destruct em.
               destruct (H0 _ _ (refl_equal _)).
               assumption.
              omega.
             intros.
             apply Zle_trans with (fl_nvds fldata).
              eauto.
             destruct fl_offset_prop.
             revert H2.
             destruct em; intros.
              omega.
            assert (0 < size o') by eauto using size_positive, offsets_intro.
            assert (0 < Zpos na) by eauto using Zpos_positive.
            Transparent Zminus.
            assert (0 <= Zpos na - 1) by omega.
            assert (0 <= size o') by omega.
            generalize (Zmult_ge H6 H7).
            generalize (non_virtual_data_size_own_fields_offset (offsets_intro Hld Ho')).
            generalize (own_fields_offset_low_bound (offsets_intro Hld Ho')).
            generalize (virtual_base_offsets_data_size (offsets_intro Hld Ho') (virtual_base_offsets_self (offsets_intro Hld Ho')) n0 Ho').
            omega.

             intros ? ?.
             destruct ((FieldSignature.eq_dec (A := A)) fs0 fs).
              subst fs.
              injection 1; intro; subst of.
              unfold field_size.
              rewrite Hstruct.
              rewrite Ho'.
              Opaque Zminus.
              injection 1; intros; subst.
              pattern (size o') at 2.
              replace (size o') with (1 * size o') by omega.
              rewrite <- Zmult_plus_distr_l.
              replace (Zpos na - 1 + 1) with (Zpos na).
              destruct (
 Z_le_dec (fl_offset + Zpos na * size o') (fl_nvsize fldata)
              ); omega.
              Transparent Zminus. omega.
             intros.
             apply Zle_trans with (fl_nvsize fldata).
              eauto.
              destruct (Z_le_dec (fl_offset + Zpos na * size o') (fl_nvsize fldata)); omega.
           
         apply lcm_positive.
         assumption.
         eauto using align_low_bound, offsets_intro.
         
         apply Zdivide_trans with (fl_align fldata).
         eauto.
         apply lcm_divides_left.                 

         intro.
         destruct ((FieldSignature.eq_dec (A := A)) fs0 fs).
          subst fs.
          intros _ ?.
          unfold field_align.
          rewrite Hstruct.
          rewrite Ho'.
          injection 1; intro; subst al.
          apply lcm_divides_right.
          eauto using align_low_bound, offsets_intro.
         intros.
         apply Zdivides_trans with (fl_align fldata).
          eauto.
         apply lcm_divides_left.

         intros ? ?.
         destruct ((FieldSignature.eq_dec (A := A)) fs0 fs).
          subst fs.
          injection 1; intro; subst fo.
          destruct fl_offset_prop.
          destruct H1.
          unfold field_align.
          rewrite Hstruct.
          rewrite Ho'.
          congruence.
         eauto.

         intros.
         split.
         intros.
         destruct (in_app_or _ _ _ H).
          destruct (list_in_map_inv _ _ _ H0).
          destruct H1.
          unfold g in H1.
          unfold map_snd in H1.
          destruct x.
          injection H1; intros; subst.
          destruct (He' i z).
          destruct (H3 H2).
          destruct H5.
          destruct H6.
          destruct (ebo_prop ( Hld) He i (z - x * size o')).
          exists fs0.
          exists fl_offset.
          destruct ((FieldSignature.eq_dec (A := A)) fs0 fs0); try congruence.
          split.
           trivial.
          exists a.
          exists na.
          split.
          assumption.
          exists x.
          split.
           assumption.
          split.
           assumption.
          exists o'.
          split.
           assumption.
          replace (fl_offset + z - fl_offset - x * size o') with (z - x * size o') by omega.
          auto.
         destruct (fl_ebo_prop0 b o).
         destruct (H1 H0).
         destruct H3.
         destruct H3.
         exists x.
         exists x0.
         destruct ((FieldSignature.eq_dec (A := A)) fs0 x).
          congruence.
         eauto.
        destruct 1.
        destruct H.
        destruct H.
        destruct ((FieldSignature.eq_dec (A := A)) fs0 x).
         subst x.
         replace x0 with fl_offset in * by congruence.
         apply in_or_app.
         left.
         destruct H0.
         destruct H0.
         destruct H0.
         rewrite Hstruct in H0.
         injection H0; intros; subst x x1.
         destruct H1.
         destruct H1.
         destruct H2.
         destruct H3.
         destruct H3.
         rewrite Ho' in H3.
         injection H3; intros; subst x1.
         replace (b, o) with (g (b, o - fl_offset)).
         apply in_map.
         destruct (He' b (o - fl_offset)).
         apply H6.
         exists x.
         split.
          assumption.
         split.
          assumption.
         destruct (ebo_prop ( Hld) He b (o - fl_offset - x * size o')).
         auto.
         simpl.
         f_equal.
         omega.
        apply in_or_app.
        right.
        destruct (fl_ebo_prop0 b o).
         apply H2.
         eauto.
       Qed.

    End Struct.

(** General case *)

    Definition field_layout_step : {
      fldata' | fl_prop fldata' /\ fl_todo fldata' = q
    }.
     (** case struct: use the results of section Struct above. *)
      case_eq (FieldSignature.type fs0); eauto using field_layout_step_struct.      
     (** only case scalar is left *)
      intros.
      destruct (incr_align (typ_align_positive PF t) (fl_nvds fldata)).
      destruct a.      
      exists (
        make_fl
        q
        ((fs0, x) :: fl_offsets fldata)
        (fl_ebo fldata)
        (x + typ_size PF (t))
        (if Z_le_dec (x + typ_size PF ( t)) (fl_nvsize fldata) then (fl_nvsize fldata) else (x + typ_size PF ( t)))
        (lcm (typ_align PF t) (fl_align fldata))
      ).
    Proof.
      split; simpl; try trivial.
      inversion prop.
      constructor; simpl; try assumption.

            intro.
            destruct (fl_exist0 fs).
            rewrite Htodo in H2, H3.
            simpl in H2, H3.            
             destruct ((FieldSignature.eq_dec (A := A)) fs0 fs).
             subst fs.
             split.
             intros.
             left; congruence.
             intros.
             assumption.
            assert (fs0 = fs -> False) by congruence.
            split; tauto.

            apply Zle_trans with (fl_nvds fldata).
             eauto.
            generalize (typ_size_positive PF ( t)).
            omega.

            destruct ( Z_le_dec (x + typ_size PF ( t))
         (fl_nvsize fldata)); omega.

            intros ? ?.
            destruct ((FieldSignature.eq_dec (A := A)) fs0 fs).
             subst fs.
             injection 1; intro; subst of.
             generalize (nvl_data_low_bound H_nvldata).
             omega.
            eauto.

            intros ? ?.
            destruct ((FieldSignature.eq_dec (A := A)) fs0 fs).
             subst fs.
             injection 1; intro; subst of.
              intros; omega.
            eauto.

            intros ? ?.
            destruct ((FieldSignature.eq_dec (A := A)) fs0 fs1).
             subst fs1.
             injection 1; intro; subst o1.
             intros _ ? ?.
             destruct ((FieldSignature.eq_dec (A := A)) fs0 fs2).
              subst fs2.
              congruence.
             unfold field_data_size at 1.
             rewrite H.             
             intros.
             injection H6.
             intros; subst s1.
             right.             
             apply Zle_trans with (fl_nvds fldata).
              eauto.
             assumption.
             intros ? ? ? ?.
             destruct ((FieldSignature.eq_dec (A := A)) fs0 fs2).
             subst fs2.
              injection 1; intro; subst o2.
              unfold field_data_size at 2.
              rewrite H.
              injection 3; intros; subst.
              left.
              apply Zle_trans with (fl_nvds fldata).
              eauto.
              assumption.
             eauto.

             intros ? ?.
             destruct ((FieldSignature.eq_dec (A := A)) fs0 fs1).
              intros; congruence.
             eauto.

             intros ? ?.
             destruct ((FieldSignature.eq_dec (A := A)) fs0 fs1).
              intros; congruence.
             intros until 6.
             intros ? ?.
             destruct ((FieldSignature.eq_dec (A := A)) fs0 fs2).
              intros; congruence.
             eauto.

             intros ? ?.
             destruct ((FieldSignature.eq_dec (A := A)) fs0 fs).
              subst fs.
              injection 1; intro; subst of.
              unfold field_data_size.
              rewrite H.
              injection 2; intros; subst.
              omega.
             intros.
             apply Zle_trans with (fl_nvds fldata).
              eauto.
              generalize (typ_size_positive PF ( t)).
              omega.           

             intros ? ?.
             destruct ((FieldSignature.eq_dec (A := A)) fs0 fs).
              subst fs.
              injection 1; intro; subst of.
              unfold field_size.
              rewrite H.
              injection 1; intros; subst.
              destruct ( Z_le_dec (x + typ_size PF ( t))
         (fl_nvsize fldata)); omega.
             intros.
             apply Zle_trans with (fl_nvsize fldata).
              eauto.
              destruct ( Z_le_dec (x + typ_size PF ( t))
         (fl_nvsize fldata)); omega.

         apply lcm_positive.
         apply typ_align_positive.
         assumption.
         
         apply Zdivide_trans with (fl_align fldata).
         eauto.
         apply lcm_divides_right.
         auto.

         intro.
         destruct ((FieldSignature.eq_dec (A := A)) fs0 fs).
          subst fs.
          intros _ ?.
          unfold field_align.
          rewrite H.
          injection 1; intro; subst al.
          apply lcm_divides_left.
         intros.
         apply Zdivides_trans with (fl_align fldata).
          eauto.
         apply lcm_divides_right.
         auto.

         intros ? ?.
         destruct ((FieldSignature.eq_dec (A := A)) fs0 fs).
          subst fs.
          injection 1; intro; subst fo.
          unfold field_align.
          rewrite H.
          congruence.
         eauto.

         intros.
         destruct (fl_ebo_prop0 b o).
         split.       
          intros.
          destruct (H2 H4).
          exists x0.
          destruct ((FieldSignature.eq_dec (A := A)) fs0 x0).
           destruct H5.
           destruct H5.
           destruct H6.
           destruct H6.
           destruct H6.
           congruence.
          assumption.
         destruct 1.
         destruct H4.
         destruct ((FieldSignature.eq_dec (A := A)) fs0 x0).
          destruct H4.
          destruct H5.
          destruct H5.
          destruct H5.
          congruence.
         eauto.
       Qed.
     
    End Step.

    Definition field_layout : {
      fldata' | fl_prop fldata' /\ fl_todo fldata' = nil
    }.
    Proof.
      cut (forall l fldata, fl_todo fldata = l -> fl_prop fldata -> {fldata' | fl_prop fldata' /\ fl_todo fldata' = nil}).
     intros.
   refine (X (Class.fields h) (
     make_fl
     (Class.fields h)
     nil
     nil
     (nvl_nvds nvldata)
     (nvl_nvsize nvldata)
     (nvl_align nvldata)
   ) (refl_equal _) _).
   constructor; simpl; try congruence.
    tauto.
    omega.
    omega.
    eauto using nvl_align_pos.
    apply Zdivide_refl.
    split.
     tauto.
    destruct 1.
    destruct H.
    destruct H.
    discriminate.

  induction l.
  intros.
  exists fldata.
  split; assumption.

  intros.
  case_eq (assoc (FieldSignature.eq_dec (A := A)) a (fl_offsets fldata)).
   intros.
   destruct (IHl (
     make_fl
     l
     (fl_offsets fldata)
     (fl_ebo fldata)
     (fl_nvds fldata)
     (fl_nvsize fldata)
     (fl_align fldata)
   )).
    reflexivity.
   inversion H0.
   constructor; simpl; try assumption.
   assert (assoc (FieldSignature.eq_dec (A := A)) a (fl_offsets fldata) <> None) by congruence.
   intros.
   generalize (fl_exist0 fs).
   rewrite H.
   simpl.
   destruct ((FieldSignature.eq_dec (A := A)) a fs).
    rewrite e in H2.
    tauto.
   tauto.
  exists x; assumption.

  intros.
  destruct (field_layout_step H0 H H1).
  destruct a0.
  eauto.
Qed.


End Field_layout.
      
  Let fldata := (let (f, _) := field_layout in f).

  Let H_fldata : fl_prop fldata.
  Proof.
    unfold fldata.
    destruct field_layout.
    tauto.
  Qed.

  Let H_fldata_2 : fl_todo fldata = nil.
  Proof.
    unfold fldata.
    destruct field_layout.
    tauto.
  Qed.

(** At this point, all non-virtual layout is done. The field boundary is [nvl_nvdsize nvldata], whereas all other non-virtual values are defined in [fldata]. *)

(** [nvebo0] is the set of all non-virtual empty base offsets, except the offset of [cilimit ld] itself. *)

  Let nvebo0 := nvl_nvebo nvldata ++ fl_ebo fldata.

  Lemma nvebo0_incl : forall b o,
    In (b, o) nvebo0 -> 0 <= o < fl_nvsize fldata.
  Proof.
    unfold nvebo0.
    intros.
    destruct (in_app_or _ _ _ H).
     (* direct base *)
     cut (0 <= o < nvl_nvsize nvldata).
      generalize (fl_size_low_bound H_fldata).
      omega.
     destruct (nvl_nvebo_prop H_nvldata b o).
     destruct (H1 H0).
     destruct H3.
     destruct H3.
     assert ((nvl_offsets nvldata) ! x <> None) by congruence.
     destruct (nvl_exist H_nvldata x).
     generalize (H7 (or_introl _ H5)).
     intros.
     assert (Plt x (cilimit ld)) by eauto using Well_formed_hierarchy.well_founded.
     assert (hierarchy ! x <> None) by eauto using Well_formed_hierarchy.complete.
     assert ((offsets ld) ! x <> None) by eauto using offsets_exist.
     case_eq ((offsets ld) ! x); try congruence.
     intros.
     destruct (non_virtual_empty_base_offset_wf 
       hierarchy_wf (offsets_intro ( Hld)) (offsets_guard ( Hld)) H4).
     assert (Plt b (cilimit ld)) by eauto using Ple_Plt_trans.
     assert ((offsets ld) ! b <> None) by eauto using offsets_exist.
     destruct (non_virtual_empty_base_offset_incl hierarchy_wf
       (offsets_intro ( Hld)) (offsets_guard ( Hld))
       H4 H16 H12).
     generalize (nvl_low_bound H_nvldata H3).
     generalize (nvl_high_bound H_nvldata H3 H12).
     omega.
    (* field *)
    destruct (fl_ebo_prop H_fldata b o).
    destruct (H1 H0).
    destruct H3.
    destruct H3.
    destruct H4.
    destruct H4.
    destruct H4.
    destruct H5.
    destruct H5.
    destruct H6.
    destruct H7.
    destruct H7.
    generalize (size_positive (offsets_intro Hld) H7).
    intros.
    assert (0 <= size x4) by omega.
    generalize (Zmult_ge H5 H10).
    intros.
    assert (x3 <= Zpos x2 - 1) by omega.
    generalize (Zmult_le_compat_r _ _ _ H12 H10).
    rewrite Zmult_minus_distr_r.
    replace (1 * size x4) with (size x4) by omega.
    intros.
    destruct (empty_base_offset_wf hierarchy_wf (offsets_intro Hld) (offsets_guard Hld) H8).
    assert (
      assoc (FieldSignature.eq_dec (A := A)) x (fl_offsets fldata) <> None
    ) by congruence.
    generalize (fl_exist H_fldata x).
    rewrite H_fldata_2.
    simpl.
    destruct 1.    
    assert ((offsets ld) ! b <> None). 
     eapply offsets_exist.
     eauto.
     eauto using Ple_Plt_trans, Well_formed_hierarchy.well_founded_struct.
     assumption.
    generalize (empty_base_offset_incl hierarchy_wf (offsets_intro Hld) (offsets_guard Hld) H8 H19 H7).
    intros.
    generalize (fl_low_bound H_fldata H3).
    generalize (fl_high_bound H_fldata H3).
    unfold field_size.
    rewrite H4.
    rewrite H7.
    intros.
    generalize (H21 _ (refl_equal _)).
    rewrite Zmult_minus_distr_r.
    rewrite Zmult_1_l.
    omega.    
  Qed.

(** [nvebo] is the set of all non-virtual empty base offsets, including the offset of [cilimit ld] itself if it is empty. *)

  Let Nvebo := (if is_empty_dec hierarchy_wf (cilimit ld) then (cons (cilimit ld, 0) nil) else nil) ++ nvebo0.  

(** ** Virtual base layout *)

(** In this algorithm, we do not consider generalized virtual bases, but only virtual bases. Indeed, the non-virtual parts of the virtual bases of [cilimit ld] make the conditions of 4.5 hold, which is not yet known for [cilimit ld] itself. So we have to treat the non-virtual part of the class differently from the non-virtual parts of its virtual bases. *)

  Section Virtual_base_layout.

(** 
- [vl_todo]: the list of virtual bases to which an offset has not yet been assigned
- [vl_offsets]: the mapping between virtual bases and offsets
- [vl_nvebo]: the set of non-virtual empty base offsets reachable through a virtual base that has already been assigned an offset
- [vl_ds]: the data size so far.
- [vl_size]: the size so far.
- [vl_align]: the alignment so far.
 *)

         Record vl : Set := make_vl {
           vl_todo : list ident;
           vl_offsets : PTree.t Z;
           vl_nvebo : list (ident * Z);
           vl_ds : Z;
           vl_size : Z;
           vl_align : Z
         }.

         Section prop.

           Variable vldata : vl.

           Record vl_prop : Prop := vl_intro {             
             (** Guard *)
             vl_exist : forall ci, (is_virtual_base_of hierarchy ci (cilimit ld) <-> ((vl_offsets vldata) ! ci <> None \/ In ci (vl_todo vldata)));
             (** C13 for the class itself *)
             vl_data_low_bound : fl_nvds fldata <= vl_ds vldata;
             (** C3 for the class itself *)
             vl_size_low_bound : fl_nvsize fldata <= vl_size vldata;
             (** Guard *)
             vl_low_bound : forall ci of, (vl_offsets vldata) ! ci = Some of -> 0 <= of;
             (** C12 between the class itself and one of its virtual bases *)
             vl_nonempty_low_bound : forall ci, (is_empty hierarchy ci -> False) -> forall of, (vl_offsets vldata) ! ci = Some of -> fl_nvds fldata <= of;
             (** C12 between two virtual bases *)
             vl_nonempty_non_overlap : forall ci1 o1, (vl_offsets vldata) ! ci1 = Some o1 -> (is_empty hierarchy ci1 -> False) -> forall ci2 o2, (vl_offsets vldata) ! ci2 = Some o2 -> (is_empty hierarchy ci2 -> False) -> ci1 <> ci2 -> forall of1, (offsets ld) ! ci1 = Some of1 -> forall of2, (offsets ld) ! ci2 = Some of2 -> o1 + non_virtual_data_size of1 <= o2 \/ o2 + non_virtual_data_size of2 <= o1;
             (** C26 between two virtual bases *)
             vl_disjoint_empty_bases : forall ci1 o1, (vl_offsets vldata) ! ci1 = Some o1 -> forall ci2 o2, (vl_offsets vldata) ! ci2 = Some o2 -> ci1 <> ci2 -> forall b bo1, non_virtual_empty_base_offset Optim (offsets ld) hierarchy ci1 b bo1 -> forall bo2, non_virtual_empty_base_offset Optim (offsets ld) hierarchy ci2 b bo2 -> o1 + bo1 <> o2 + bo2;
             (** C26 between the class itself and one of its virtual bases *)
             vl_disjoint_empty_bases_main : forall ci o, (vl_offsets vldata) ! ci = Some o -> forall b bo, non_virtual_empty_base_offset Optim (offsets ld) hierarchy ci b bo -> In (b, o + bo) Nvebo -> False;
             (** C13 for a virtual base *)
             vl_nonempty_high_bound : forall ci, (is_empty hierarchy ci -> False) -> forall of, (vl_offsets vldata) ! ci = Some of -> forall o', (offsets ld) ! ci = Some o' -> of + non_virtual_data_size o' <= vl_ds vldata;
             (** C3 for a virtual base *)
             vl_high_bound : forall ci, forall of, (vl_offsets vldata) ! ci = Some of -> forall o', (offsets ld) ! ci = Some o' -> of + non_virtual_size o' <= vl_size vldata;
             (** Guard *)
             vl_align_pos : 0 < vl_align vldata;
             (** C17 for the class itself *)
             vl_align_field : (fl_align fldata | vl_align vldata);
             (** C17 for a virtual base *)
             vl_align_prop : forall ci, (vl_offsets vldata) ! ci <> None -> forall of, (offsets ld) ! ci = Some of -> (non_virtual_align of | vl_align vldata);
             vl_offset_align : forall ci of, (vl_offsets vldata) ! ci = Some of -> forall co, (offsets ld) ! ci = Some co -> (non_virtual_align co | of);
             (** Specification of the set [vl_nvebo] of non-virtual empty base offsets accessible from some virtual base. *)
             vl_nvebo_prop : forall b o, (In (b, o) (vl_nvebo vldata) <-> exists ci, exists of, (vl_offsets vldata) ! ci = Some of /\ non_virtual_empty_base_offset Optim (offsets ld) hierarchy ci b (o - of))
           }.

           End prop.


           Section Step. 

             Variable vldata : vl.

           Hypothesis prop : vl_prop vldata.

(** Trying to assign an offset to the virtual base [a] of [cilimit ld] *)

           Variable a : ident.

           Variable q : list ident.

           Hypothesis Htodo : vl_todo vldata = a :: q.

           Hypothesis undef: (vl_offsets vldata) ! a = None.

           Let son : is_virtual_base_of hierarchy a (cilimit ld).
           Proof.
             destruct (vl_exist prop a).
             apply H0.
             rewrite Htodo.
             auto.
           Qed.

           Let Hlt : (Plt a (cilimit ld)). 
           Proof.
             eauto using Well_formed_hierarchy.is_virtual_base_of_lt.
           Qed.

           Definition v_orig_offset : {o' | (offsets ld) ! a = Some o'}.
           Proof.
             assert ((offsets ld) ! a <> None) by eauto using offsets_exist, Well_formed_hierarchy.is_virtual_base_of_defined_base.
             case_eq ((offsets ld) ! a); try congruence.
             intros.
             repeat esplit.
           Qed.

           Let o' := let (o', _) := v_orig_offset in o'.

           Let Ho' : (offsets ld) ! a = Some o'.
           Proof.
             unfold o'.
             destruct v_orig_offset.
             assumption.
           Qed.

           Let e0 : {e | (nvebo ld) ! a = Some e}.
           Proof.
             generalize (nvebo_exist ( Hld) Hlt).
             case_eq ((nvebo ld) ! a); try congruence.
             intros.
             repeat esplit.
           Qed.

           Let e := let (e, _) := e0 in e.

           Let He :  (nvebo ld) ! a = Some e.
           Proof.
             unfold e.
             destruct e0.
             assumption.
           Qed.

           Let cilimit_nonempty : is_empty hierarchy (cilimit ld) -> False.
           Proof.
             intros; eauto using no_virtual_bases.
           Qed.

           Corollary nvebo_eq_nvebo0 : Nvebo = nvebo0.
           Proof.
             unfold Nvebo.
             case (is_empty_dec hierarchy_wf (cilimit ld)); try contradiction; reflexivity.
           Qed.
           
           Let em := is_empty_dec hierarchy_wf a.

(** 
   The offset [v_offset] assigned to [a] is computed as follows:
   - starting from 0 if [a] is empty, from [vl_ds fldata] (the data size so far) otherwise
   - find the least offset [o] multiple of the non-virtual alignment of [a], and such that the set [e] of non-virtual empty base offsets reachable from [a] is disjoint from [nvl_nvebo] the offsets of non-virtual empty base offsets so far, and from [fl_ebo] the empty base offsets reachable from other fields so far, and from [vl_nvebo] the offsets of non-virtual empty base offsets reachable through virtual bases so far, knowing that there will be no conflict if [o >= vl_size fldata]
   See [LibPos] for a definition of [bounded_offset].
*)

           Let f z (x : _ * _) :=
             let (b, o) := x in
               if In_dec (prod_eq_dec peq Z_eq_dec) (b, z + o) (nvebo0)
                 then true
                 else if In_dec (prod_eq_dec peq Z_eq_dec) (b, z + o) (vl_nvebo vldata)
                   then true
                   else false.

           Let f' z :=
             match List.filter (f z) e with
               | nil => true
               | _ => false
             end.

           Let align_pos : 0 < non_virtual_align o'.
           Proof.
             exact (non_virtual_align_low_bound (offsets_intro Hld Ho')).
           Qed.
           
           Definition v_offset :=
             let (z, _) := bounded_offset align_pos (if em then 0 else vl_ds vldata) (vl_size vldata) f' in z.
           

            Lemma v_offsets_non_overlap : forall ci co, (vl_offsets vldata) ! ci = Some co -> forall b bo, non_virtual_empty_base_offset Optim (offsets ld) hierarchy ci b bo -> forall bo', non_virtual_empty_base_offset Optim (offsets ld) hierarchy a b bo' -> co + bo <> v_offset + bo'.
            Proof.
              intros.
              unfold v_offset.
              destruct (bounded_offset align_pos (if em then 0 else vl_ds vldata) (vl_size vldata) f').
              destruct a0.
              destruct H3.
              assert (Plt ci (cilimit ld)).
               destruct (vl_exist prop ci).                
               eapply Well_formed_hierarchy.is_virtual_base_of_lt.
               eauto.               
               eapply H6.
               left.
               congruence.
              destruct (non_virtual_empty_base_offset_wf 
               hierarchy_wf (offsets_intro ( Hld)) (offsets_guard ( Hld)) H0).
              assert ((offsets ld) ! b <> None).
               eapply offsets_exist.
               eauto.
               eauto using Ple_Plt_trans.
               assumption.
              case_eq ((offsets ld) ! b) ; try congruence.
              intros.               
              generalize (non_virtual_empty_base_offset_incl hierarchy_wf
                 (offsets_intro ( Hld)) (offsets_guard ( Hld))
                 H1 H8 Ho').
              intros.
              assert (hierarchy ! ci <> None).
               destruct (vl_exist prop ci).
               eapply Well_formed_hierarchy.is_virtual_base_of_defined_base.
               eauto.
               eapply H12.
               left.
               congruence.
              assert ((offsets ld) ! ci <> None) by eauto using offsets_exist.
              case_eq ((offsets ld) ! ci); try congruence.
              intros.
              generalize (non_virtual_empty_base_offset_incl hierarchy_wf
                 (offsets_intro ( Hld)) (offsets_guard ( Hld))                 
                 H0 H8 H13).
              intros.
              destruct H4.
               (* case away *)
               generalize (vl_high_bound prop H H13).
               omega.
              (* case not away *)
               revert H4.
               unfold f'.
               case_eq (filter (f x) e); try congruence.
               intros.
               intro Habs.
               generalize (filter_In (f x) (b, bo') e).
               rewrite H4.
               simpl.
               destruct 1.
               apply H17.
               split.
               generalize (nvebo_prop Hld He b bo').
               tauto.
               rewrite <- Habs.
               assert (
  (if In_dec (prod_eq_dec peq Z_eq_dec) (b, co + bo) (nvebo0)
    then true
    else
      if In_dec (prod_eq_dec peq Z_eq_dec) (b, co + bo) (vl_nvebo vldata)
      then true
      else false) = true
               ).
               destruct (In_dec (prod_eq_dec peq Z_eq_dec) (b, co + bo) (vl_nvebo vldata)).
                 destruct ( In_dec (prod_eq_dec peq Z_eq_dec) (b, co + bo) (nvebo0)); try trivial.
                destruct n.
                generalize (vl_nvebo_prop prop b (co + bo)).
                destruct 1.
                apply H19.
                esplit.
                esplit.
                split.
                eassumption.
                replace (co + bo - co) with bo by omega.
                assumption.
               assumption.
            Qed.

            Lemma v_offsets_non_overlap_main : forall b bo', non_virtual_empty_base_offset Optim (offsets ld) hierarchy a b bo' -> In (b, v_offset + bo') Nvebo -> False.
            Proof.
              rewrite nvebo_eq_nvebo0.
              intros until 1.
              generalize (non_virtual_empty_base_offset_wf hierarchy_wf (offsets_intro Hld) (offsets_guard Hld) H).
              destruct 1.
              assert ((offsets ld) ! b <> None) by eauto using offsets_exist, Ple_Plt_trans.
              generalize (non_virtual_empty_base_offset_incl hierarchy_wf (offsets_intro Hld) (offsets_guard Hld) H H2 Ho').
              intro.
              unfold v_offset.
              destruct (bounded_offset align_pos (if em then 0 else vl_ds vldata) (vl_size vldata)).
              destruct a0.
              destruct H5.
              intro.
              destruct H6.
               generalize (nvebo0_incl H7).
               generalize (vl_size_low_bound prop).
              omega.
             revert H6.
             unfold f'.
             case_eq (filter (f x) e); try congruence.
             intros.
             generalize (filter_In (f x) (b, bo') e).
             rewrite H6.
             simpl.
             destruct 1.
             apply H10.
             split.
              generalize (nvebo_prop Hld He b bo').
              tauto.
             assert (
   (if In_dec (prod_eq_dec peq Z_eq_dec) (b, x + bo') (nvebo0 )
    then true
    else
      if In_dec (prod_eq_dec peq Z_eq_dec) (b, x + bo') (vl_nvebo vldata)
      then true
      else false) = true           ).
             case ( In_dec (prod_eq_dec peq Z_eq_dec) (b, x + bo') (nvebo0)).
              trivial.
             contradiction.
            assumption.
          Qed.

            Lemma v_offset_low_bound : 0 <= v_offset.
            Proof.
              unfold v_offset.
              destruct (bounded_offset align_pos (if em then 0 else vl_ds vldata) (vl_size vldata) f').
              destruct a0.
              revert H.
              destruct em.
               tauto.
              generalize (vl_data_low_bound prop).
              generalize (fl_data_low_bound H_fldata).
              generalize (nvl_data_low_bound H_nvldata).
              intros; omega.
            Qed.

            Lemma v_offset_align : (non_virtual_align o' | v_offset).
            Proof.
              unfold v_offset.
              destruct (bounded_offset align_pos (if em then 0 else vl_ds vldata) (vl_size vldata) f').
              tauto.
            Qed.

            Lemma v_offset_nonempty_low_bound : (is_empty hierarchy a -> False) -> vl_ds vldata <= v_offset.
            Proof.
              unfold v_offset.
              destruct (bounded_offset align_pos (if em then 0 else vl_ds vldata) (vl_size vldata) f').
              destruct em; tauto.
            Qed.

         Let g := map_snd (key := ident) (fun o => v_offset + o).
               
         Definition virtual_base_layout_step : {
           vldata' | vl_prop vldata' /\ vl_todo vldata' = q
         }.
           exists (
             make_vl
             (** remove [a] from [vl_todo vldata = a :: q] *) q
             (** assign [v_offset] to [a] *) (PTree.set a v_offset (vl_offsets vldata))
             (** add the non-virtual empty base offsets of [a] to the empty base offsets of [cilimit ld] *) (List.map g e ++ vl_nvebo vldata)
             (** update the data size if [a] is not empty *) (if em then vl_ds vldata else (v_offset + non_virtual_data_size o'))
             (** update the size to the max *) (if Z_le_dec (v_offset + non_virtual_size o') (vl_size vldata) then (vl_size vldata) else  (v_offset + non_virtual_size o'))
             (** update the alignment to the least common multiple *) (lcm (vl_align vldata) (non_virtual_align o'))
           ).
         Proof.
           split; simpl; try trivial.
            inversion prop.
            constructor; simpl; try assumption.

            intro.
            destruct (vl_exist0 ci).
            rewrite Htodo in H, H0.
            simpl in H, H0.            
             destruct (peq ci a).
             subst.
             rewrite PTree.gss.
             split.
             intros.
             left; congruence.
             intros.
             assumption.
            rewrite PTree.gso.
            assert (a = ci -> False) by congruence.
            split; tauto.
           assumption.

            case em; intro.
             assumption.
            apply Zle_trans with (vl_ds vldata).
             assumption.
            generalize (v_offset_nonempty_low_bound n).
            generalize (non_virtual_data_size_own_fields_offset (offsets_intro ( Hld) Ho')).
            generalize (own_fields_offset_low_bound (offsets_intro ( Hld) Ho')).
            omega.

            apply Zle_trans with (vl_size vldata).
            assumption.
            destruct (Z_le_dec (v_offset + non_virtual_size o') (vl_size vldata));
             omega.

            intros ? ?.
            destruct (peq ci a).
             subst.
             rewrite PTree.gss.
             injection 1; intros; subst of.
             exact (v_offset_low_bound).
            rewrite PTree.gso.
            eauto.
            assumption.

            intros ? ? ?.
            destruct (peq ci a).
             subst.
             rewrite PTree.gss.
             injection 1; intros; subst of.
             generalize (v_offset_nonempty_low_bound H).
             omega.
            rewrite PTree.gso; eauto.

          intros ? ?.
          destruct (peq ci1 a).
           subst.
           rewrite PTree.gss.
           injection 1; intro; subst o1.
           intros.
           rewrite PTree.gso in H1.
           generalize (vl_nonempty_high_bound prop H2 H1 H5).
           generalize (v_offset_nonempty_low_bound H0).
           omega.
           congruence.
          rewrite PTree.gso.
          intros ? ? ? ?.
          destruct (peq ci2 a).
           subst.
           rewrite PTree.gss.
           injection 1; intros; subst o2.
           generalize (vl_nonempty_high_bound prop H0 H H5).
           generalize (v_offset_nonempty_low_bound H3).
           omega.
           rewrite PTree.gso.
           eauto.
           assumption.
          assumption.

          intros ? ?.
          destruct (peq ci1 a).
           subst.
           rewrite PTree.gss.
           injection 1; intro; subst o1.
           intros.
           rewrite PTree.gso in H0.
           cut (o2 + bo2 <> v_offset + bo1).
            congruence.
           eauto using v_offsets_non_overlap.
           congruence.
          rewrite PTree.gso.
          intros ? ? ?.
          destruct (peq ci2 a).
           subst.
           rewrite PTree.gss.
           injection 1; intros; subst o2.
           eauto using v_offsets_non_overlap.
          rewrite PTree.gso.
          eauto.
          assumption.
          assumption.

          intros ? ?.
          destruct (peq ci a).
           subst.
           rewrite PTree.gss.
           injection 1; intro; subst o.
           intros; eauto using v_offsets_non_overlap_main.
          rewrite PTree.gso; eauto.

          case em.
           intros ? ? ?.
           rewrite PTree.gso.
           eauto.
           intro.
           subst ci.
           contradiction.
          intros ? ? ?.
          destruct (peq ci a).
           subst.
           rewrite PTree.gss.
           injection 1; intros; subst of.
           replace o'0 with o' in * by congruence.
           omega.
          rewrite PTree.gso.
          intros.
          eapply Zle_trans with (vl_ds vldata).
          eauto.
          generalize (v_offset_nonempty_low_bound n).
          generalize (non_virtual_data_size_own_fields_offset (offsets_intro ( Hld) Ho')).
          generalize (own_fields_offset_low_bound (offsets_intro ( Hld) Ho')).
          omega.
          assumption.

          intros ? ?.
          destruct (peq ci a).
           subst.
           rewrite PTree.gss.
           injection 1; intros; subst of.
           destruct ( Z_le_dec (v_offset + non_virtual_size o') (vl_size vldata)).
            congruence.
           replace o'0 with o' by congruence.
           omega.
          rewrite PTree.gso.
          intros.
          destruct ( Z_le_dec (v_offset + non_virtual_size o') (vl_size vldata)).    
           eauto.
          apply Zle_trans with (vl_size vldata).
           eauto.
          omega.
         assumption.

         apply lcm_positive.
         assumption.
         eauto using non_virtual_align_low_bound.
         
         apply Zdivide_trans with (vl_align vldata).
         eauto.
         apply lcm_divides_left.                 

         intro.
         destruct (peq ci a).
          subst.
          intros.
          replace of with o' by congruence.
          apply lcm_divides_right.
          eauto using non_virtual_align_low_bound.
         rewrite PTree.gso.
         intros.
         apply Zdivides_trans with (vl_align vldata).
          eauto.
         apply lcm_divides_left.
         assumption.

         intros ? ?.
         destruct (peq ci a).
          subst ci.
          rewrite PTree.gss.
          injection 1; intro; subst of.
          rewrite Ho'.
          injection 1; intros; subst co.
          exact v_offset_align.
         rewrite PTree.gso; eauto.

         intros.
         split.
         intros.
         destruct (in_app_or _ _ _ H).
          destruct (list_in_map_inv _ _ _ H0).
          destruct H1.
          unfold g in H1.
          unfold map_snd in H1.
          destruct x.
          injection H1; intros; subst.
          destruct (nvebo_prop ( Hld) He i z).
          exists a.
          exists v_offset.
          rewrite PTree.gss.
          split.
          trivial.
          replace (v_offset + z - v_offset) with z by omega.
          auto.
         destruct (vl_nvebo_prop0 b o).
         destruct (H1 H0).
         destruct H3.
         destruct H3.
         exists x.
         exists x0.
         rewrite PTree.gso.
         eauto.
         congruence.
        destruct 1.
        destruct H.
        destruct H.
        destruct (peq x a).
         subst.
         rewrite PTree.gss in H.
         injection H; intro; subst x0.
         apply in_or_app.
         left.
         replace (b, o) with (g (b, o - v_offset)).
         apply in_map.
         destruct (nvebo_prop ( Hld) He b (o - v_offset)).
         auto.
         simpl.
         f_equal.
         omega.
        rewrite PTree.gso in H.
        apply in_or_app.
        right.
        destruct (vl_nvebo_prop0 b o).
         apply H2.
         eauto.
        assumption.
      Qed.

    End Step.

(** Finally, lay out all the virtual bases *)

    Definition vbases_aux : {l | forall x, In x l <-> is_virtual_base_of hierarchy x (cilimit ld)}.
    Proof.
      case_eq (virtual_bases ! (cilimit ld)).
       intros.
       exists l.
       destruct (virtual_bases_prop).
       eauto.
      intros.
      apply False_rect.
      destruct (virtual_bases_prop).
      eapply H0.
      2 : eassumption.
      congruence.
    Qed.

    Let vbases := let (v, _) := vbases_aux in v.

    Let H_vbases :  forall x, In x vbases <-> is_virtual_base_of hierarchy x (cilimit ld).
    Proof.
      unfold vbases.
      destruct vbases_aux.
      assumption.
    Qed.

  Definition virtual_base_layout : {
    vldata | vl_prop vldata /\ vl_todo vldata = nil
  }.
  Proof.
   cut (forall l vl, vl_todo vl = l -> vl_prop vl -> {
     vldata | vl_prop vldata /\ vl_todo vldata = nil
   }).
    intros.
    refine (H _ (make_vl
      vbases
      (@PTree.empty _)
      nil
      (fl_nvds fldata)
      (fl_nvsize fldata)
      (fl_align fldata)
    ) _ _).
     reflexivity.
    constructor; simpl; try (intros; rewrite PTree.gempty in *;  congruence).
    intro.
    rewrite PTree.gempty.
    generalize (H_vbases ci).
    tauto.
    omega.
    omega.
    eauto using fl_align_pos.
    apply Zdivide_refl.
    split.
     tauto.
    destruct 1.
    destruct H0.
    destruct H0.
    rewrite PTree.gempty in *; congruence.

   induction l.
   intros.
   esplit.
   split.
    eassumption.
   assumption.

   intros.
   case_eq ((vl_offsets vl0) ! a).
    intros.
    apply IHl with (make_vl
      l
      (vl_offsets vl0)
      (vl_nvebo vl0)
      (vl_ds vl0)
      (vl_size vl0)
      (vl_align vl0)
    ).
     reflexivity.
    inversion H0.
    constructor; simpl; try assumption.
    intro.
    generalize (vl_exist0 ci).
    rewrite H.
    simpl.
    destruct (peq a ci).
     subst.
     rewrite H1.
     assert (forall A B C: Prop, (B <-> C) -> (A <-> B) -> (A <-> C)) by tauto.
     apply H2.
     split; left; congruence.
    tauto.

    intros.
    destruct (virtual_base_layout_step H0 H H1).
    destruct a0.
    eauto.
  Qed.


  End Virtual_base_layout.

  Let vldata := let (v, _) := virtual_base_layout in v.

  Let H_vldata : vl_prop vldata.
  Proof.
    unfold vldata.
    destruct virtual_base_layout.
    tauto.
  Qed.

  Let H_vldata_2 : vl_todo vldata = nil.
  Proof.
    unfold vldata.
    destruct virtual_base_layout.
    tauto.
  Qed.

(** ** Finalization and proof of correctness *)

(** Now, round the size up to max(size, dsize), then up to the nearest multiple of the alignment. *)

  Let size0 := incr_align (vl_align_pos H_vldata) (if Z_le_dec (vl_size vldata) (vl_ds vldata) then vl_ds vldata else vl_size vldata).

  Let size := let (s, _) := size0 in s.

  Let H_size : vl_size vldata <= size.
  Proof.
    unfold size.
    destruct size0.
    destruct (Z_le_dec (vl_size vldata) (vl_ds vldata)); omega.
  Qed.

  Let H_data_size : vl_ds vldata <= size.
  Proof.
    unfold size.
    destruct size0.
    destruct (Z_le_dec (vl_size vldata) (vl_ds vldata)); omega.
  Qed.

  Let H_size_2 : (vl_align vldata | size).
  Proof.
    unfold size.
    destruct size0.
    tauto.
  Qed. 

(** Construction of the layout data as expected in 4.2 *)

  Let o' :=  (LayoutConstraints.make
    (nvl_pbase nvldata)
    (nvl_offsets nvldata)
    (nvl_nvds nvldata)
    (fl_offsets fldata)
    (fl_nvds fldata)
    (fl_nvsize fldata)
    (fl_align fldata)
    (PTree.set (cilimit ld) 0 (vl_offsets vldata))
    (vl_ds vldata)
    size
    (vl_align vldata)    
  ).

  Definition offsets' := PTree.set (cilimit ld) o' (offsets ld).

  Lemma offsets'_eq : forall ci', Plt ci' (cilimit ld) ->
    offsets' ! ci' = (offsets ld) ! ci'.
  Proof.
    unfold offsets'.
    intros.
    rewrite PTree.gso.
    trivial.
    intro; subst.
    eapply Plt_irrefl; eauto.
  Qed.

  Lemma offsets_preserve_old : forall ci,
    Plt ci (cilimit ld) ->
    forall o, offsets' ! ci = Some o ->
      class_level_prop Optim PF offsets' hierarchy ci o.
  Proof.
    intros.
    assert (ci <> cilimit ld).
     intro.
     subst.
     eapply Plt_irrefl.
     eassumption.     
    generalize H0.
     unfold offsets' at 1.
     rewrite PTree.gso.
     intros.
    eapply class_level_prop_eq with (offsets1 := offsets ld) (cilimit := cilimit ld).
     eauto.
     intros; symmetry; eauto using offsets'_eq.
    eauto using offsets_guard.
    assumption.
    eassumption.
    eauto using offsets_intro.
    assumption.
    assumption.
  Qed.

  Lemma offsets'_defined : offsets' ! (cilimit ld) = Some o'.
  Proof.
   unfold offsets'.
   rewrite PTree.gss.
   trivial.
  Qed.

  Lemma nvl_offsets_lt : forall bi of,
    (nvl_offsets nvldata) ! bi = Some of ->
    Plt bi (cilimit ld).
  Proof.
    intros.
    assert ((nvl_offsets nvldata) ! bi <> None) by congruence.
    destruct (nvl_exist H_nvldata bi).
    generalize (H2 (or_introl _ H0)).
    intros.
    eauto using Well_formed_hierarchy.well_founded.
  Qed.

  Lemma nvl_offsets_offsets' : forall bi of,
    (nvl_offsets nvldata) ! bi = Some of ->
    offsets' ! bi = (offsets ld) ! bi.
  Proof.
    intros.
    assert ((nvl_offsets nvldata) ! bi <> None) by congruence.
    destruct (nvl_exist H_nvldata bi).
    generalize (H2 (or_introl _ H0)).
    intros.
    assert (Plt bi (cilimit ld)) by eauto using Well_formed_hierarchy.well_founded.
    eauto using offsets'_eq.
  Qed.

  Lemma fl_offsets_offsets' : forall f of,
    assoc (FieldSignature.eq_dec (A := A)) f (fl_offsets fldata) = Some of ->
    forall ci n, FieldSignature.type f = FieldSignature.Struct ci n ->
      offsets' ! ci = (offsets ld) ! ci.
  Proof.
    intros.
    assert (assoc (FieldSignature.eq_dec (A := A)) f (fl_offsets fldata) <> None) by congruence.
    destruct (fl_exist H_fldata f).
    generalize (H3 (or_introl _ H1)).
    intros.
    assert (Plt ci (cilimit ld)) by eauto using Well_formed_hierarchy.well_founded_struct.
    eauto using offsets'_eq.
  Qed.

  Lemma vl_offsets_offsets' : forall bi of,
    (vl_offsets vldata) ! bi = Some of ->
    offsets' ! bi = (offsets ld) ! bi.
  Proof.
    intros.
    assert ((vl_offsets vldata) ! bi <> None) by congruence.
    destruct (vl_exist H_vldata bi).
    generalize (H2 (or_introl _ H0)).
    intros.
    assert (Plt bi (cilimit ld)) by eauto using Well_formed_hierarchy.is_virtual_base_of_lt.
    eauto using offsets'_eq.
  Qed.
    
(** The proof that the new offsets computed for the current class satisfy the soundness conditions *)

  Lemma offsets'_preserve :
    class_level_prop Optim PF offsets' hierarchy (cilimit ld) o'.
  Proof.
    constructor; unfold o'; simpl.

    intros.
    eapply nvl_primary_base_dynamic.
    eauto.
    assumption.
    
    intros.
    generalize (nvl_primary_base H_nvldata H).
    intros.
    assert ((nvl_offsets nvldata) ! b <> None) by congruence.
    destruct (nvl_exist H_nvldata b).
    generalize (H3 (or_introl _ H1)).
    intros.
    assert (Plt b (cilimit ld)) by eauto using Well_formed_hierarchy.well_founded.
    rewrite (offsets'_eq H5).
    eauto using Well_formed_hierarchy.complete, offsets_exist.

    intros.
    case_eq (nvl_pbase nvldata); try congruence.
    intros.
    generalize (nvl_primary_base_dynamic H_nvldata H0).
    intros.
    generalize (nvl_primary_base H_nvldata H0).
    intros.
    assert ((nvl_offsets nvldata) ! i <> None) by congruence.
    destruct (nvl_exist H_nvldata i).
    generalize (H5 (or_introl _ H3)).
    intros.
    eapply is_dynamic_base.
    eassumption.
    eassumption.
    assumption.

    intros until 1.
    intro.
    replace c with h by congruence.
    generalize (nvl_exist H_nvldata bi).
    rewrite H_nvldata_2.
    simpl .
    tauto.

    intros.
    replace c with h by congruence.
    revert H.
    generalize (nvl_exist H_nvldata bi).
    rewrite H_nvldata_2.
    simpl.
    tauto.

    intros; eauto using nvl_primary_base.

    intros; eauto using nvl_low_bound.

    intros; eauto using nvl_dynamic_no_primary_low_bound.

    intros; eauto using nvl_align_dynamic, fl_align_nvl, Zdivide_trans.

    intros until 1.
    rewrite (nvl_offsets_offsets' H).
    intros; eauto using nvl_offset_align.

    intros until 4.
    rewrite (nvl_offsets_offsets' H).
    rewrite (nvl_offsets_offsets' H1).
    intros.
    eauto using nvl_nonempty_non_overlap.

    intros until 2.
    rewrite (nvl_offsets_offsets' H0).
    intros.
    eauto using nvl_nonempty_high_bound.

    eauto using nvl_data_low_bound.

    eauto using nvl_data_dynamic_low_bound.

    intros.
    replace c with h in * by congruence.
    generalize (fl_exist H_fldata f).
    rewrite H_fldata_2.
    simpl.
    tauto.

    intros.
    replace c with h in * by congruence.
    generalize (fl_exist H_fldata f).
    rewrite H_fldata_2.
    simpl.
    tauto.

    intros.
    eauto using fl_low_bound.

    intros; eauto using fl_nonempty_low_bound.

    intros until 1.
    generalize (fl_offset_align H_fldata H).
    unfold field_align.
    case_eq (FieldSignature.type f).
     tauto.
    intros until 1.
    rewrite (fl_offsets_offsets' H H0).
    tauto.

    intros until 5.
    generalize (fl_non_overlap H_fldata H H1 H0 H3 H2).
    unfold field_data_size.
    case_eq (FieldSignature.type f1).
     case_eq (FieldSignature.type f2).
      tauto.
      intros until 1.
      rewrite (fl_offsets_offsets' H0 H4).
      tauto.
     intros until 1.
   rewrite (fl_offsets_offsets' H H4).
  case_eq (FieldSignature.type f2).
   tauto.
  intros until 1.
  rewrite (fl_offsets_offsets' H0 H5).
  tauto.

  intros.
  destruct (is_dynamic_dec hierarchy_wf (cilimit ld)).
   generalize (nvl_data_dynamic_low_bound H_nvldata i).
   generalize (fl_data_low_bound H_fldata).
   generalize (dynamic_type_data_size_low_bound PF).
   omega.
  pose (G := fun f : _ A => match FieldSignature.type f with
                    | FieldSignature.Scalar _ => true
                    | FieldSignature.Struct ci _ => if is_empty_dec hierarchy_wf ci then false else true
                  end).
  case_eq (filter G (Class.fields h)).
   intros.
   pose (F := fun cl => match cl with
                          | (Class.Inheritance.Repeated, ci) => if is_empty_dec hierarchy_wf ci then false else true
                          | _ => false
                        end).
   case_eq (filter F (Class.super h)).
    intros.
    destruct H.
    econstructor.
    eassumption.
     intros.
     generalize (filter_In G f (Class.fields h)).
     rewrite H0.
     simpl.
     unfold G.
     destruct (FieldSignature.type f).
      tauto.
     intros; repeat esplit.
     intros.
     generalize (filter_In G f (Class.fields h)).
     rewrite H0.
     simpl.
     unfold G.
     rewrite H2.
     destruct (is_empty_dec hierarchy_wf e); tauto.
    intros.
    destruct n.
    eapply is_dynamic_virtual_methods.
    eassumption.
    eauto.
   intros.
   destruct n.
   eapply is_dynamic_virtual_base.
   eleft.
   eassumption.
   eassumption.
   intros.
   generalize (filter_In F (Class.Inheritance.Repeated, b) (Class.super h)).
   rewrite H1.
   simpl.
   destruct 1.
   destruct (is_empty_dec hierarchy_wf b).
    assumption.
   destruct H3.
   auto.
   intros.
   generalize (filter_In F p (Class.super h)).
   destruct p.
   rewrite H1.
   simpl.
   destruct 1.
   destruct (H2 (or_introl _ (refl_equal _))).
   destruct t; try discriminate.
   destruct (is_empty_dec hierarchy_wf i); try discriminate.
   assert ((offsets ld) ! i <> None) by eauto using Well_formed_hierarchy.well_founded, Well_formed_hierarchy.complete, offsets_exist.
   case_eq ((offsets ld) ! i); try congruence.
   intros.
   generalize (nonempty_non_virtual_data_size_positive (offsets_intro ( Hld) H7) n0). 
   intros.
   destruct (nvl_exist H_nvldata i).
   generalize (H9 H4).
   rewrite H_nvldata_2.
   simpl.
   destruct 1; try contradiction.
   case_eq ((nvl_offsets nvldata) ! i); try congruence.
   intros.
   generalize (nvl_low_bound H_nvldata H12).
   generalize (nvl_nonempty_high_bound H_nvldata n0 H12 H7).
   generalize (fl_data_low_bound H_fldata).
   omega.
   intros.
   generalize (filter_In G t (Class.fields h)).
   rewrite H0.
   destruct 1.
   destruct (H1 (or_introl _ (refl_equal _))).
   generalize (fl_exist H_fldata t).
   rewrite H_fldata_2.
   simpl.
   destruct 1.
   destruct (H5 H3); try contradiction. 
   case_eq (assoc (FieldSignature.eq_dec (A := A)) t (fl_offsets fldata)); try congruence.
   intros.
   generalize (fl_low_bound H_fldata H8).
   generalize (fl_nonempty_high_bound H_fldata H8).
   unfold field_data_size.
   revert H4.
   unfold G.
   case_eq (FieldSignature.type t).
    intros.
    assert ( (forall (ty : ident) (n : positive),
         FieldSignature.Scalar t0 =
         FieldSignature.Struct ty n ->
         is_empty hierarchy ty -> False)
    ) by (intros; discriminate).
    generalize (H10 H12 _ (refl_equal _)).
    generalize (typ_size_positive PF t0).
    omega.
   intros until 1.
   destruct (is_empty_dec hierarchy_wf struct); try congruence.
   intros until 1.
   case_eq ((offsets ld) ! struct); try congruence.
   intros.
   assert (
      (forall (ty : ident) (n : positive),
         FieldSignature.Struct (A := A) struct arraysize =
         FieldSignature.Struct ty n ->
         is_empty hierarchy ty -> False) 
   )
   by (congruence).
   generalize (H11 H13  _ (refl_equal _)).
   generalize (size_positive (offsets_intro ( Hld)) H10).
   intros.   
   generalize (Zpos_positive arraysize).
   intros.
   Transparent Zminus. assert (0 <= Zpos arraysize - 1) by omega.
   assert (0 <= LayoutConstraints.size t0) by omega.
   generalize (Zmult_ge H17 H18).
   intros.
   generalize (virtual_base_offsets_data_size (offsets_intro Hld H10) (virtual_base_offsets_self (offsets_intro Hld H10)) n0 H10).
   generalize (nonempty_non_virtual_data_size_positive (offsets_intro Hld H10) n0).
   omega.
   intros.
   assert ((offsets ld) ! struct <> None) by eauto using Well_formed_hierarchy.well_founded_struct, Well_formed_hierarchy.complete_struct, offsets_exist.
   contradiction.

   intros.
   eapply fl_nonempty_high_bound.
   eauto.
   eassumption.
   assumption.
   revert H1.
   unfold field_data_size.
   case_eq (FieldSignature.type f).
    tauto.
   intros until 1.
   rewrite (fl_offsets_offsets' H H1).
   tauto.

   intros until 1.
   generalize (fl_high_bound H_fldata H).
   unfold field_size.
   case_eq (FieldSignature.type f).
    tauto.
   intros until 1.
   rewrite (fl_offsets_offsets' H H0).
   tauto.

   eauto using fl_data_low_bound.

   intros until 1.
   rewrite (nvl_offsets_offsets' H).
   intros; eauto using nvl_high_bound, fl_size_low_bound, Zle_trans.

   intros until 1.
   case_eq ((nvl_offsets nvldata) ! bi); try congruence.
   intros until 1.
   rewrite (nvl_offsets_offsets' H0).
   intros; eauto using nvl_align_prop, Zdivide_trans, fl_align_nvl.

   intros until 1.
   case_eq ( assoc (FieldSignature.eq_dec (A := A)) f (fl_offsets fldata)); try congruence.
   intros until 1.
   generalize (fl_align_prop H_fldata H).
   unfold field_align.
   case_eq (FieldSignature.type f).
    tauto.
   intros until 1.
   rewrite (fl_offsets_offsets' H0 H1).
   tauto.

   intros.
   rewrite PTree.gso.
   destruct (vl_exist H_vldata b).
   generalize (H0 H).
   rewrite H_vldata_2.
   simpl.
   tauto.
   intro; subst b.
   generalize (Well_formed_hierarchy.is_virtual_base_of_lt hierarchy_wf H).
   apply Plt_irrefl.

   intro.
   destruct (peq b (cilimit ld)).
    tauto.
   rewrite PTree.gso.
   destruct (vl_exist H_vldata b).
   rewrite H_vldata_2 in H0.
   simpl in H0.
   tauto.
   assumption.

   apply PTree.gss.

   intro.
   destruct (peq b (cilimit ld)).
    subst.
    rewrite PTree.gss.
    injection 1; intros; subst.
    exists 0; omega.
   rewrite PTree.gso.
   intros until 1.
   rewrite (vl_offsets_offsets' H).
   eauto using vl_offset_align.
   assumption.

   intros ? ?.
   destruct (peq b (cilimit ld)).
    subst.
    rewrite PTree.gss.
    injection 1; intros; subst.
    omega.
   rewrite PTree.gso.
   eauto using vl_low_bound.
   assumption.

   intros ? ?.
   destruct (peq b1 (cilimit ld)).
    subst.
    rewrite PTree.gss.
    injection 1; intro; subst.
    simpl.
    intros.
    rewrite PTree.gso in H1.
    unfold offsets' in H0.
    rewrite PTree.gss in H0.
    rewrite (vl_offsets_offsets' H1) in H2.
    left.
    injection H0; intro;  subst bo1.
    simpl.
    eauto using vl_nonempty_low_bound.
    congruence.
   rewrite PTree.gso.
   intro.
   rewrite (vl_offsets_offsets' H).
   intros until 1.
   intros ? ?.
   destruct (peq b2 (cilimit ld)).
    subst.
    rewrite PTree.gss.
    injection 1; intro; subst.
    unfold offsets'.
    rewrite PTree.gss.
    injection 1; intro; subst bo2.
    simpl.
    intros.
    right.
    eauto using vl_nonempty_low_bound.
   rewrite PTree.gso.
   intro.
   rewrite (vl_offsets_offsets' H1).
   intros.
   eauto using vl_nonempty_non_overlap.
   assumption.
   assumption.

  intros ? ?.
  destruct (peq bi (cilimit ld)).
   subst.
   rewrite PTree.gss.
   injection 1; intro; subst.
   unfold offsets'.
   rewrite PTree.gss.
   injection 2; intro; subst bo.
   simpl.
   eauto using vl_data_low_bound.
  rewrite PTree.gso.
  unfold offsets'.
  rewrite PTree.gso.
  intros. 
  eauto using vl_nonempty_high_bound.
  assumption.
  assumption.

  assumption.

  unfold offsets'.
  intro.
  destruct (peq bi (cilimit ld)).
   subst.
   rewrite PTree.gss.
   rewrite PTree.gss.
   injection 1; intro; subst.
   injection 1; intro; subst bo.
   simpl.
   eauto using Zle_trans, vl_size_low_bound.
  rewrite PTree.gso.
  rewrite PTree.gso.
  intros.
  eauto using Zle_trans, vl_high_bound.
  assumption.
  assumption.

  unfold offsets'.
  intro.
  destruct (peq b (cilimit ld)).
   subst.
   rewrite PTree.gss.
   rewrite PTree.gss.
   injection 2; intro; subst bo.
   simpl.
   eauto using vl_align_field.
  rewrite PTree.gso.
  rewrite PTree.gso.
  eauto using vl_align_prop.
  assumption.
  assumption.

  assumption.

  eauto using vl_align_pos.

  eauto using fl_align_pos.

  generalize (nvl_size_pos H_nvldata). 
  generalize (fl_size_low_bound H_fldata).
  omega.

Qed.

Lemma non_virtual_empty_base_offset_old : forall ci,
  Plt ci (cilimit ld) -> forall b o,
    non_virtual_empty_base_offset Optim (offsets ld) hierarchy ci b o ->
    non_virtual_empty_base_offset Optim offsets' hierarchy ci b o.
Proof.
  apply non_virtual_empty_base_offsets_eq with (PF := PF).
   eauto.
   intros; symmetry; eauto using offsets'_eq.
   eauto using offsets_guard.
   eauto using offsets_preserve_old, offsets_intro.
Qed.

Lemma empty_base_offset_old : forall ci,
  Plt ci (cilimit ld) -> forall b o,
    empty_base_offset Optim (offsets ld) hierarchy ci b o ->
    empty_base_offset Optim offsets' hierarchy ci b o.
Proof.
  apply empty_base_offsets_eq with (PF := PF).
   eauto.
   intros; symmetry; eauto using offsets'_eq.
   eauto using offsets_guard.
   eauto using offsets_preserve_old, offsets_intro.
Qed.

Lemma disjoint_empty_base_offsets_old : forall ci,
  Plt ci (cilimit ld) -> forall of,
    offsets' ! ci = Some of ->
    disjoint_empty_base_offsets Optim offsets' hierarchy ci of.
Proof.
  intros.
  eapply disjoint_empty_base_offsets_eq.    
  eauto.
  intros.
  symmetry.
  eapply offsets'_eq.
  eassumption.
  eauto using offsets_guard.
  unfold offsets'.
  intro.
  destruct (peq ci0 (cilimit ld)).
   subst.
   rewrite PTree.gss.
   intros; congruence.
  rewrite PTree.gso; eauto using offsets_guard.
  eauto using offsets'_preserve, offsets_intro.
  assumption.
  rewrite (offsets'_eq H) in H0.
  eassumption. 
  rewrite (offsets'_eq H) in H0.
  eauto using disjoint_ebo.
  assumption.
Qed.

Lemma non_virtual_empty_base_offset_new : forall ci,
  Plt ci (cilimit ld) -> forall b o,
    non_virtual_empty_base_offset Optim offsets' hierarchy ci b o ->
    non_virtual_empty_base_offset Optim (offsets ld) hierarchy ci b o.
Proof.
  apply non_virtual_empty_base_offsets_eq with (PF := PF).
   eauto.
   intros; eauto using offsets'_eq.
   unfold offsets'.
   intro.
   destruct (peq ci (cilimit ld)).
    subst.
    rewrite PTree.gss.
    congruence.
   rewrite PTree.gso; eauto using offsets_guard.
   eauto using offsets_preserve_old.
Qed.

Lemma empty_base_offset_new : forall ci,
  Plt ci (cilimit ld) -> forall b o,
    empty_base_offset Optim offsets' hierarchy ci b o ->
    empty_base_offset Optim (offsets ld) hierarchy ci b o.
Proof.
  apply empty_base_offsets_eq with (PF := PF).
   eauto.
   intros; eauto using offsets'_eq.
   unfold offsets'.
   intro.
   destruct (peq ci (cilimit ld)).
    subst.
    rewrite PTree.gss.
    congruence.
   rewrite PTree.gso; eauto using offsets_guard.
   eauto using offsets_preserve_old.
Qed.

Lemma Nvebo_prop : forall b o, In (b, o) Nvebo <-> non_virtual_empty_base_offset Optim offsets' hierarchy (cilimit ld) b o.
Proof.
  unfold nvebo.
  unfold nvebo0.
  split.
   intro.
   destruct (in_app_or _ _ _ H).
    revert H0.
    case (is_empty_dec hierarchy_wf (cilimit ld)); simpl; try tauto.
    destruct 2; try contradiction.
    injection H0; intros; subst b o.
    constructor.
    assumption.
    trivial.
   destruct (in_app_or _ _ _ H0).
    destruct (nvl_nvebo_prop H_nvldata b o).
    destruct (H2 H1).
    destruct H4.
    destruct H4.
    eapply non_virtual_empty_base_offset_non_virtual_base.
    unfold offsets'.
    rewrite PTree.gss.
    reflexivity.
    simpl.
    eassumption.
    eauto using non_virtual_empty_base_offset_old, nvl_offsets_lt.
   destruct (fl_ebo_prop H_fldata b o).
   destruct (H2 H1).
   destruct H4.
   destruct H4.
   destruct H5.
   destruct H5.
   destruct H5.
   destruct H6.
   destruct H6.
   destruct H7.
   destruct H8.
   destruct H8.
   assert (assoc (FieldSignature.eq_dec (A := A)) x (fl_offsets fldata) <> None) by congruence.
   destruct (fl_exist H_fldata x). 
   generalize (H12 (or_introl _ H10)).
   intros.
   assert (Plt x1 (cilimit ld)) by eauto using Well_formed_hierarchy.well_founded_struct.
   eapply non_virtual_empty_base_offset_field.
   unfold offsets'.
   rewrite PTree.gss.
   reflexivity.
   simpl.
   eassumption.
   eassumption.
   rewrite (offsets'_eq H14).
   eassumption.
   eassumption.
   assumption.
   eapply empty_base_offset_old.
   assumption.
   assumption.
  intro.
  apply in_or_app.
  inversion H; subst.
   left.
   case (is_empty_dec hierarchy_wf (cilimit ld)); simpl; tauto.
  right.
  apply in_or_app.
   revert H0.
   unfold offsets'.
   rewrite PTree.gss.
   injection 1; intro; subst oc.
   simpl in H1.
   left.
   destruct (nvl_nvebo_prop H_nvldata b o).
   apply H4.
   esplit.
   esplit.
   split.
   eassumption.
   eapply non_virtual_empty_base_offset_new.
   eauto using nvl_offsets_lt.
   assumption.
  right.
  apply in_or_app.
  right.
  revert H0.
  unfold offsets'.
  rewrite PTree.gss.
  injection 1; intro; subst oc.
  destruct (fl_ebo_prop H_fldata b o).
  apply H8.
  simpl in H1.
  assert ( assoc (FieldSignature.eq_dec (A := A)) f (fl_offsets fldata) <> None) by congruence.
  generalize (fl_exist H_fldata f).
  rewrite H_fldata_2.
  simpl.
  destruct 1.
  generalize (H11 (or_introl _ H9)).
  intros.
  esplit.  
  esplit.
  split.
  eassumption.
  esplit.
  esplit.
  split.
  eassumption.
  esplit.
  split.
  eassumption.
  split.
  assumption.
  assert (Plt cif (cilimit ld)) by eauto using Well_formed_hierarchy.well_founded_struct.
  esplit.
  split.
  rewrite <- (offsets'_eq H13).
  eassumption.
  eapply empty_base_offset_new.
  assumption.
  assumption.
Qed.

Lemma disjoint_empty_base_offsets_new :
  disjoint_empty_base_offsets Optim offsets' hierarchy (cilimit ld) o'.
Proof.
  constructor.

  destruct 1.
  subst.
  simpl.
  intros.
  eauto 6 using nvl_disjoint_empty_bases, non_virtual_empty_base_offset_new, nvl_offsets_lt.

  subst.
  simpl.
  intro.
  destruct (peq ci1 (cilimit ld)).
   subst.
   rewrite PTree.gss.
   injection 1; intro; subst.
   intros until 2.
   rewrite PTree.gso in H0.
   simpl.
   intros.
   intro.
   subst.
   destruct (Nvebo_prop bi (o2 + x2)).
   generalize (H5 H2).
   intro.
   destruct (vl_exist H_vldata ci2).
   assert ((vl_offsets vldata) ! ci2 <> None) by congruence.
    generalize (H8 (or_introl _ H9)).
    intros.
    eapply vl_disjoint_empty_bases_main.
    eauto.
    eassumption.
    eapply non_virtual_empty_base_offset_new.
    eauto using Well_formed_hierarchy.is_virtual_base_of_lt.
    eassumption.
    assumption.
    congruence.
   rewrite PTree.gso.
   intros until 1.
   intro.
   destruct (peq ci2 (cilimit ld)).
    subst.
    rewrite PTree.gss.
    injection 1; intro; subst.
    simpl.
    intros.
    intro.
    subst.
   destruct (Nvebo_prop bi (o1 + x1)).
   generalize (H5 H3).
   intro.
   destruct (vl_exist H_vldata ci1).
   assert ((vl_offsets vldata) ! ci1 <> None) by congruence.
    generalize (H8 (or_introl _ H9)).
    intros.
    eapply vl_disjoint_empty_bases_main.
    eauto.
    eassumption.
    eapply non_virtual_empty_base_offset_new.
    eauto using Well_formed_hierarchy.is_virtual_base_of_lt.
    eassumption.
    assumption.
   rewrite PTree.gso.
   intros.
   eapply vl_disjoint_empty_bases.
   eauto.
   eassumption.
   eassumption.
   assumption.
   eapply non_virtual_empty_base_offset_new.
   destruct (vl_exist H_vldata ci1).   
   eapply Well_formed_hierarchy.is_virtual_base_of_lt.
   eauto.
   apply H5.
   left; congruence.
   eassumption.
   eapply non_virtual_empty_base_offset_new.
   destruct (vl_exist H_vldata ci2).   
   eapply Well_formed_hierarchy.is_virtual_base_of_lt.
   eauto.
   apply H5.
   left; congruence.
   eassumption.  
   assumption.
   assumption.

  simpl.
  intros.
  cut (o2 + p2 * LayoutConstraints.size of2 + x2 <> o1 + x1).
   congruence.
  assert (Plt ci1 (cilimit ld)).
   destruct (nvl_exist H_nvldata ci1).
   eapply Well_formed_hierarchy.well_founded.
   eauto.
   eassumption.
   eapply H8.
   left.
   congruence.
  assert (Plt ci2 (cilimit ld)).
   destruct (fl_exist H_fldata f2).
   eapply Well_formed_hierarchy.well_founded_struct.
   eauto.
   eassumption.
   eapply H9.
   left.
   congruence.
   eassumption.
  eapply fl_disjoint_empty_bases.
  eauto.
  eassumption.
  eassumption.
  assumption.
  assumption.
  rewrite <- (offsets'_eq H8).
  assumption.
  eapply empty_base_offset_new.
  assumption.
  eassumption.
  eassumption.
  eapply non_virtual_empty_base_offset_new.
  assumption.
  assumption.  

  simpl.
  intros.
  assert (Plt ci1 (cilimit ld)).
   destruct (fl_exist H_fldata f1).
   eapply Well_formed_hierarchy.well_founded_struct.
   eauto.
   eassumption.
   eapply H13.
   left.
   congruence.
   eassumption.
  assert (Plt ci2 (cilimit ld)).
   destruct (fl_exist H_fldata f2).
   eapply Well_formed_hierarchy.well_founded_struct.
   eauto.
   eassumption.
   eapply H14.
   left.
   congruence.
   eassumption.
  eapply fl_disjoint_empty_bases_fields.
  eauto.
  eassumption.
  eassumption.
  assumption.
  assumption.
  rewrite <- (offsets'_eq H12).
  assumption.
  eapply empty_base_offset_new.
  assumption.
  eassumption.
  eassumption.
  eassumption.
  assumption.
  assumption.
  rewrite <- (offsets'_eq H13).
  assumption.
  eapply empty_base_offset_new.
  assumption.
  assumption.  
  assumption.
Qed.
  
Let ld' := Ld 
  offsets'
  (Psucc (cilimit ld))
  (PTree.set (cilimit ld) (Nvebo ++ vl_nvebo vldata) (ebo ld))
  (PTree.set (cilimit ld) Nvebo (nvebo ld))
.

(** The proof of the global invariant of the algorithm (guard conditions and specifications for [nvebo] and [ebo] *)

Lemma step' : prop hierarchy ld'.
Proof.
  constructor; simpl.

   unfold offsets'.
   intro.
   case (peq ci (cilimit ld)).
    intros; subst.
    congruence.
   intro.
   rewrite PTree.gso; eauto using offsets_guard.

   unfold offsets' at 1.
   intros ? ?.
   destruct (peq ci (cilimit ld)).
    subst.
    rewrite PTree.gss.
    injection 1; intro; subst of.
    eauto using offsets'_preserve.
   rewrite PTree.gso.
   intros.
   assert ((offsets ld) ! ci <> None) by congruence.
   generalize (offsets_guard2 ( Hld) H0).
   intros.
   rewrite <- (offsets'_eq H1) in H.
   eauto using offsets_preserve_old.
   assumption.

   unfold offsets'.
   intro.
   destruct (peq ci (cilimit ld)).
    subst.
    rewrite PTree.gss.
    intros.
    apply Plt_succ.
   rewrite PTree.gso.
   intros.
   generalize (offsets_guard2 ( Hld) H).
   intros; eauto using Plt_trans, Plt_succ.
   assumption.
   
   intros.
   unfold offsets'.
   destruct (peq ci (cilimit ld)).
    subst.
    rewrite PTree.gss.
    congruence.
   rewrite PTree.gso.
   destruct (Plt_succ_inv _ _ H).
    eauto using offsets_exist.
   contradiction.
   assumption.

   intros.
   generalize H.
   unfold offsets' at 1.
   destruct (peq ci (cilimit ld)).
    subst.
    rewrite PTree.gss.
    injection 1; intro; subst o'0.
    eauto using disjoint_empty_base_offsets_new.
   rewrite PTree.gso.
   intros.
   assert (Plt ci (cilimit ld)).
    eapply offsets_guard2.
    eauto.
    congruence.
   eauto using disjoint_empty_base_offsets_old.
   assumption.

   intros ? ?.
   destruct (peq ci (cilimit ld)).
    subst.
    rewrite PTree.gss.
    injection 1; intro; subst.
    split.
    intros.
    destruct (in_app_or _ _ _ H0).
     destruct (Nvebo_prop b o'0).
      econstructor.
      unfold offsets'.
      rewrite PTree.gss.
      reflexivity.
      simpl.
      rewrite PTree.gss.
      reflexivity.
      replace (o'0 - 0) with o'0.
      auto.
      Transparent Zminus. omega.
    destruct (vl_nvebo_prop H_vldata b o'0).
    destruct (H2 H1).
    destruct H4.
    destruct H4.
    assert ((vl_offsets vldata) ! x <> None) by congruence.
    destruct (vl_exist H_vldata x).
    generalize (H8 (or_introl _ H6)).
    intros.
    assert (Plt x (cilimit ld)) by eauto using Well_formed_hierarchy.is_virtual_base_of_lt. 
    econstructor.
    unfold offsets'.
    rewrite PTree.gss.
    reflexivity.
    simpl.
    rewrite PTree.gso.
    eassumption.
    intro; subst.
    eapply Plt_irrefl.
    eauto.
   eauto using non_virtual_empty_base_offset_old.
  inversion 1.
  subst.
  revert H1.
  unfold offsets'.
  rewrite PTree.gss.
  injection 1; intro; subst oc.
  apply in_or_app.
  revert H2.
  simpl.  
  destruct (peq ci' (cilimit ld)).
   subst.
   rewrite PTree.gss.
   injection 1; intro; subst.
   left.
   destruct (Nvebo_prop b o'0).
    apply H5.
    replace o'0 with (o'0 - 0) by omega.
    assumption.
   rewrite PTree.gso.
   intros.
   right.
    destruct (vl_nvebo_prop H_vldata b o'0).
    apply H5.
    esplit.
    esplit.
    split.
    eassumption.
    eapply non_virtual_empty_base_offset_new.
    eapply Well_formed_hierarchy.is_virtual_base_of_lt.
    eauto.
    destruct (vl_exist H_vldata ci').
    apply H7.
    left.
    congruence.
   assumption.
   assumption.
  rewrite PTree.gso.
  intros.
  assert ((ebo ld) ! ci <> None) by congruence.
  generalize (ebo_guard ( Hld) H0) .
  intros.
  generalize (@empty_base_offset_new _ H1 b o'0).
  generalize (@empty_base_offset_old _ H1 b o'0).
  generalize (ebo_prop ( Hld) H b o'0).
  tauto.
  assumption.

  intros.
  destruct (peq ci (cilimit ld)).
   subst.
   rewrite PTree.gss.
   congruence.
  rewrite PTree.gso.
  eapply ebo_exist.
  eauto.
  destruct (Plt_succ_inv _ _ H).
   assumption.
  contradiction.
  assumption.

  intro.
  destruct (peq ci (cilimit ld)).
   subst.
   intros; apply Plt_succ.
  rewrite PTree.gso; intros; eauto using Plt_trans, Plt_succ, ebo_guard.

  intros ? ?.
  destruct (peq ci (cilimit ld)).
   subst.
   rewrite PTree.gss.
   injection 1; intro; subst e.
   eapply Nvebo_prop.
  rewrite PTree.gso.
  intros.
  assert ((nvebo ld) ! ci <> None) by congruence.
  assert (Plt ci (cilimit ld)) by eauto using nvebo_guard.
  generalize (@non_virtual_empty_base_offset_old _ H1 b o'0).
  generalize (@non_virtual_empty_base_offset_new _ H1 b o'0).
  generalize (nvebo_prop ( Hld) H b o'0).
  tauto.
  assumption.

  intros.
  destruct (peq ci (cilimit ld)).
   subst.
   rewrite PTree.gss.
   congruence.
  rewrite PTree.gso.
  eapply nvebo_exist.
  eauto.
  destruct (Plt_succ_inv _ _ H).
   assumption.
  contradiction.
  assumption.

  intro.
  destruct (peq ci (cilimit ld)).
   subst.
   intros; apply Plt_succ.
  rewrite PTree.gso; intros; eauto using Plt_trans, Plt_succ, nvebo_guard.

Qed.
 
(* Corollary *) Definition layout_step_defined : {
  ld'0 | prop hierarchy ld'0 /\ cilimit ld'0 = Psucc (cilimit ld)
}.
  exists ld'.
Proof.
  split.
  apply step'.
  reflexivity.
Qed.

End Def.

(** ** What to do if [cilimit ld] is not an identifier of a defined class *)

Section Undef.

Hypothesis undef : hierarchy ! (cilimit ld) = None.

Definition layout_step_undefined : {
  ld'0 | prop hierarchy ld'0 /\ cilimit ld'0 = Psucc (cilimit ld)
}.
  exists (Ld
    (offsets ld)
    (Psucc (cilimit ld))
    (PTree.set (cilimit ld) nil (ebo ld))
    (PTree.set (cilimit ld) nil (nvebo ld))
  ); simpl.
Proof.
  split; try trivial.
  inversion Hld.
  constructor; simpl; try assumption.

  intros; eauto using Plt_succ, Plt_trans.

  intros.
  eapply offsets_exist.
  eassumption.
  destruct (peq ci (cilimit ld)).
   subst.
   contradiction.
  destruct (Plt_succ_inv _ _ H).
   assumption.
  contradiction.
  assumption.

  intros ? ?.
  destruct (peq ci (cilimit ld)).
   subst.
   rewrite PTree.gss.
   injection 1; intros; subst; simpl.
   split.
    tauto.
   inversion 1; subst.
   assert ((offsets ld) ! (cilimit ld) <> None) by congruence.
   assert (hierarchy ! (cilimit ld) <> None) by eauto.
   contradiction.
   rewrite PTree.gso; eauto.


  intros.
  destruct (peq ci (cilimit ld)).
   subst.
   rewrite PTree.gss.
   congruence.
  rewrite PTree.gso.
  eapply ebo_exist.
  eauto.
  destruct (Plt_succ_inv _ _ H).
   assumption.
  contradiction.
  assumption.

  intro.
  destruct (peq ci (cilimit ld)).
   subst.
   intros; apply Plt_succ.
  rewrite PTree.gso; intros; eauto using Plt_trans, Plt_succ, ebo_guard.

  intros ? ?.
  destruct (peq ci (cilimit ld)).
   subst.
   rewrite PTree.gss.
   injection 1; intro; subst e.
   simpl.
   split.
    tauto.
   inversion 1; subst.
    inversion H1; congruence.
   assert ((offsets ld) ! (cilimit ld) <> None) by congruence.
   assert (hierarchy ! (cilimit ld) <> None) by eauto.
   contradiction.
   assert ((offsets ld) ! (cilimit ld) <> None) by congruence.
   assert (hierarchy ! (cilimit ld) <> None) by eauto.
   contradiction.
  rewrite PTree.gso; eauto.
   
  intros.
  destruct (peq ci (cilimit ld)).
   subst.
   rewrite PTree.gss.
   congruence.
  rewrite PTree.gso.
  eapply nvebo_exist.
  eauto.
  destruct (Plt_succ_inv _ _ H).
   assumption.
  contradiction.
  assumption.

  intro.
  destruct (peq ci (cilimit ld)).
   subst.
   intros; apply Plt_succ.
  rewrite PTree.gso; intros; eauto using Plt_trans, Plt_succ, nvebo_guard.
   
Qed.

End Undef.

Definition layout_step : {
  ld'0 | prop hierarchy ld'0 /\ cilimit ld'0 = Psucc (cilimit ld)
}.
Proof.
 case_eq (hierarchy ! (cilimit ld)); eauto using layout_step_defined, layout_step_undefined.
Qed.

End Step.

(** * Packing all together *)

Definition empty_layout : {
  ld'0 | prop hierarchy ld'0 /\ cilimit ld'0 = xH
}.
  exists (Ld 
    (PTree.empty _)
    xH
    (PTree.empty _)
    (PTree.empty _)
  ); simpl.
Proof.
  split; try trivial.
  constructor; simpl; try (intros; rewrite PTree.gempty in *; simpl in *); try congruence.

  destruct ci; simpl in *; discriminate.

  destruct ci; simpl in *; discriminate.

  destruct ci; simpl in *; discriminate.

Qed.

Let max0 := max_index hierarchy.

Let max := let (m, _) := max0 in m.

Let H_max : forall j, hierarchy ! j <> None -> Plt j max.
Proof.
  unfold max.
  destruct max0.
  assumption.
Qed.

Definition layout_end : {
  ld'0 | prop hierarchy ld'0 /\ cilimit ld'0 = max
}.
Proof.
  cut (forall j, Plt j max -> forall ld,
    prop hierarchy ld ->
    cilimit ld = j -> {
  ld'0 | prop hierarchy ld'0 /\ cilimit ld'0 = max
  }). 
  intros.
  destruct (plt xH max).
   destruct (empty_layout).
   destruct a.   
   eauto.
  unfold Plt in n.
  destruct (peq max xH).
   rewrite e.
   exact empty_layout.
  assert (Zpos max <> Zpos xH) by congruence.
  assert (Plt max xH).
   unfold Plt.
   omega.
  generalize H0.
  generalize max.
  intro.
  intro.
  destruct max1; simpl in *; discriminate.
induction j using (well_founded_induction_type (bounded_gt_wf max)).
 intros.
 subst.
 destruct (layout_step H0).
 destruct a.
 destruct (peq (Psucc (cilimit ld)) max).
  rewrite <- e.
  esplit.
  esplit.
   eassumption.
   assumption.
  assert (Plt (Psucc (cilimit ld)) max).
  unfold Plt in *.
  assert (Zpos (Psucc (cilimit ld)) <> Zpos max) by congruence.  
  rewrite Psucc_Zsucc in *.
  unfold Zsucc in *.
  omega.
  eapply (X (Psucc (cilimit ld))).
  split.
    apply Plt_succ.
    assumption.
   assumption.
   eassumption.
   assumption.
 Qed.

(* Theorem *) Definition layout : {
  offsets |
    (forall ci, hierarchy ! ci <> None <-> offsets ! ci <> None) /\
    forall ci of, offsets ! ci = Some of -> (
      class_level_prop Optim PF (offsets ) hierarchy ci of /\
      disjoint_empty_base_offsets Optim (offsets) hierarchy ci of
    )
}.
Proof.
 destruct (layout_end).
 destruct a.
 inversion H.
 exists (offsets x).
 split.
  split.
  intros.
  eapply offsets_exist.
  eassumption.
  rewrite H0.
  eauto.
 assumption.
 auto.
  split; eauto.
Qed.

End Layout.


(*
Require Import ConcreteOp.

Variable hierarchy : PTree.t (Class.t A).

Hypothesis Hhier : Well_formed_hierarchy.prop (A:=A) hierarchy.

Definition off := let (l, _) := layout Hhier in l.

Lemma ointro : (forall (ci : positive) (o : t A),
        off ! ci = Some o ->
        class_level_prop Optim PF off hierarchy ci o).
Proof.
  unfold off.
  destruct layout.
  destruct a.
  intros.
  destruct (H0 _ _ H1).
  assumption.
Qed.

Lemma oexist : (forall ci : positive, off ! ci <> None -> hierarchy ! ci <> None).
Proof.
  unfold off.
  destruct layout.
  destruct a.
  intro.
  destruct (H ci).
  assumption.
Qed.

Lemma oguard : (forall ci : positive, hierarchy ! ci <> None -> off ! ci <> None).
Proof.
  unfold off.
  destruct layout.
  destruct a.
  intro.
  destruct (H ci).
  assumption.
Qed.

Definition vtbl := vtables Hhier ointro oexist oguard.

Theorem preservation : forall (NO : NATIVEOP A) (psize palign : Z)
         (MEM : MEMORY PF psize palign)
          (objects : ident -> option Z)
         (s : state NO (Value.t A) (source_specific_stmt A) (Globals.t A))
         (t0 : state NO (memval A) target_specific_stmt (mem MEM)),
       invariant Optim (MEM:=MEM) off Hhier objects s t0 ->
       forall
         s' : state NO (Value.t A) (source_specific_stmt A) (Globals.t A),
       source_step Optim hierarchy s s' ->
       exists t' : state NO (memval A) target_specific_stmt (mem MEM),
         Relation_Operators.clos_trans
           (state NO (memval A) target_specific_stmt (mem MEM))
           (step vtbl (MEM:=MEM)) t0 t' /\
         invariant Optim (MEM:=MEM) off Hhier objects s' t'.
Proof.
 unfold vtbl.
 intros.
 eapply preservation.
 eapply is_dynamic_virtual_base.
 eapply is_empty_dec.
 assumption.
 unfold off.
 destruct layout.
 destruct a.
 intros.
 destruct (H2 _ _ H3).
 assumption.
 eassumption.
 assumption.
Qed.
*)

End Compcert.

