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
Require Import Interm.
Require Import IntermSetDynType.
Require Import IntermSetDynTypeWf.
Require Memory.
Require Import Events.
Require Import Smallstep.
Require Import Target.
Require Import Vtables.
Require Import CompileSetDynType.
Require Import Eqdep_dec.
Open Scope Z_scope.
Load Param.

Function oapply (A B : Type) (f : A -> B) (oa : option A) {struct oa} : option B :=
  match oa with
    | None => None
    | Some a => Some (f a)
  end.

Notation OldVar := (xO) (only parsing).
Notation NewVar := (xI) (only parsing).

Section Common.

  Variable A : ATOM.t.

  Variable nativeop : Type.

  Variable prog : Interm.program A nativeop.

  Notation hierarchy := (Interm.hierarchy prog) (only parsing).

  Hypothesis Hhier : Well_formed_hierarchy.prop hierarchy.

Notation is_dynamic := (Dynamic.is_dynamic).

Variable COP : CPPOPTIM A.

Variable vop' : valop' A Z.

Hypothesis vop'_pos : forall k t, 0 < vop' k t.     

  Variable offsets : PTree.t (LayoutConstraints.t A).

      
      Hypothesis intro : forall ci o, offsets ! ci = Some o -> class_level_prop (OP COP) (PF vop'_pos) offsets hierarchy ci o.
      
      Hypothesis guard : forall ci, offsets ! ci <> None -> hierarchy ! ci <> None.

      Hypothesis exis: forall ci, hierarchy ! ci <> None -> offsets ! ci <> None. 

      Hypothesis empty_prop : forall (ci : positive) (oc : LayoutConstraints.t A),
        offsets ! ci = Some oc ->
        disjoint_empty_base_offsets (OP COP) offsets hierarchy ci oc.   

      Variable mblock : Type.
   
        Notation GARBAGE := (skip _ _) (only parsing).
        
        Notation paths := (let (T, _) := Well_formed_hierarchy.paths Hhier in T) (only parsing).

        Notation STATIC := (xO) (only parsing).
        Notation NONSTATIC := (xI) (only parsing).

        Function compile_method_name (cn : ident) (ms : MethodSignature.t A) : ident :=
          match hierarchy ! cn with
            | None => xH
            | Some c =>
              match Method.find ms (Class.methods c) with
                | None => xH
                | Some m =>
                  match Method.kind m with
                    | Method.concrete k => NONSTATIC k
                    | _ => xH
                  end
              end
          end.

Function compile_callkind (ct : callkind A) : ident :=
  match ct with
    | Interm.Static id => STATIC id
    | NonVirtual id ms => compile_method_name id ms
  end.

Function repeated_criterion (hp : Class.Inheritance.t * list ident) : bool :=
  match hp with
    | (Class.Inheritance.Repeated, _) => true
    | _ => false
  end.
  
Function compile_statcast (from to : ident) (source target : var) : Target.stmt nativeop (romty A) :=  
  match peq from to with
    | left _ => move _ _ (OldVar source) (OldVar target)
    | _ =>
      match plt from to with
        | left _ =>
          match paths ! from with
            | None => GARBAGE
            | Some pfrom =>
              match pfrom ! to with
                | None => GARBAGE
                | Some l =>
                  match filter repeated_criterion l with
                    | nil => GARBAGE
                    | (_, p) :: _ =>
                      match non_virtual_subobject_offset offsets 0 p with
                        | None => GARBAGE
                        | Some off => ptrshift _ _ (OldVar source) (0 - off) (OldVar target)
                      end
                  end
              end
          end
        | right _ =>
          match paths ! to with
            | None => GARBAGE
            | Some pto =>
              match pto ! from with
                | Some ((Class.Inheritance.Repeated, p) :: _) =>
                  match non_virtual_subobject_offset offsets 0 p with
                    | None => GARBAGE
                    | Some off => ptrshift _ _ (OldVar source) off (OldVar target)
                  end
                | Some ((Class.Inheritance.Shared, b :: p) :: _) =>
                  match non_virtual_subobject_offset offsets 0 (b :: p) with
                    | None => GARBAGE
                    | Some off => seq
                      (Target.load _ _ (vop' Size (tyVptr _)) (OldVar source) 0 (NewVar xH))
                      (seq
                        (romop _ (Some (NewVar xH)) (vbase_offset (romty := romty A) from b) (NewVar (xO xH)))
                        (seq
                          (ptrshiftmult _ _ (OldVar source) (NewVar (xO xH)) 1 (NewVar (xH)))
                          (ptrshift  _ _ (NewVar (xH)) off (OldVar target))
                        )
                      )
                  end
                | _ => GARBAGE
              end
          end
      end
  end.

Function compile_invoke (use_thunks : bool) (source : var) (class : ident) (ms : MethodSignature.t A) (args : list var) (retval : option var) : Target.stmt nativeop (romty A) :=
  if use_thunks
    then
      thunkcall (romty := romty A) _ (OldVar source) class ms (map OldVar args) (oapply OldVar retval)
    else
      (** on-site (callee) adjustment *)
      seq
      (Target.load _ _ (vop' Size (tyVptr _)) (OldVar source) 0 (NewVar xH))     (seq
        (romop _ (Some (NewVar xH)) (Target.dispatch_offset (romty := romty A) class ms) (NewVar (xI xH)))
        (seq
          (ptrshiftmult _ _ (OldVar source) (NewVar (xI xH)) 1 (NewVar (xI xH)))
          (seq
            (romop _ (Some (NewVar xH)) (Target.dispatch_function (romty := romty A) class ms) (NewVar xH))
            (call _ _ Dynamic (NewVar xH) (NewVar (xI xH) :: map OldVar args) (oapply OldVar retval))
          )
        )        
      ).
      
Function compile_pathop (path_oper : path_operation) (source : option var) (target : var) : Target.stmt nativeop (romty A) :=
  match path_oper with
    | rootpath cn =>
      if is_dynamic_dec Hhier cn
        then 
          (romop _ None (Target.initVTT (romty := romty A) cn) (OldVar target))          
        else 
          (null _ _ (OldVar target)) (** non-dynamic classes have no VTTs. However, it remains necessary to set a dummy value to the target variable, as it will be passed to the constructor/destructor *)

    | addbase cn h b =>
      if is_dynamic_dec Hhier b
        then
          (romop _ (oapply OldVar source) (Target.subVTT (romty := romty A) cn (h, b)) (OldVar target))
        else
          (null _ _ (OldVar target)) (** non-dynamic subclasses have no subVTTs. This also includes the case where cn itself is not dynamic (and thus the source PVTT is not valid) *)
          
  end.

Variable use_thunks : Interm.stmt A nativeop -> bool.

        Function compile (s : Interm.stmt A nativeop) {struct s} : Target.stmt nativeop (romty A)  :=
          match s with
            | Interm.skip => skip _ _
            | Interm.seq s1 s2 => seq (compile s1) (compile s2)
            | Interm.test var ifso ifnot => test (OldVar var) (compile ifso) (compile ifnot)
            | Interm.block None s' => block None (compile s')
            | Interm.block (Some (var, (cn, ncells))) s' =>
              match offsets ! cn with
                | None => GARBAGE
                | Some o => block (Some (OldVar var, ncells * size o)) (compile s')
              end
            | Interm.exit n => exit _ _ n
            | Interm.loop s' => loop (compile s')
            | Interm.native op args ores => native _ op (map OldVar args) (oapply OldVar ores)
            | Interm.move src tgt => move _ _ (OldVar src) (OldVar tgt)
            | Interm.ret ores => ret _ _ (oapply OldVar ores)
            | Interm.call ck vargs ores =>
              call _ _ Static (compile_callkind ck) (map OldVar vargs) (oapply OldVar ores)


(** C++-specific *)

(** Null pointer *)
            | Interm.null _ target => (null _ _ (OldVar target))
              
(** Pointer equality *)              
            | Interm.ptreq ptr1 ptr2 target => ptreq _ _ (OldVar ptr1) (OldVar ptr2) (OldVar target)

(** Get field (scalar or structure) *)
            | Interm.getfield class field source target =>
              match offsets ! class with
                | None => GARBAGE
                | Some o =>
                  match assoc (FieldSignature.eq_dec (A := A)) field (field_offsets o) with
                    | None => GARBAGE
                    | Some fo =>
                      match FieldSignature.type field with
                        | FieldSignature.Scalar ty => Target.load _ _ (vop' Size (valtype_of_typ ty)) (OldVar source) fo (OldVar target)
                        | _ =>  (ptrshift _ _ (OldVar source) fo (OldVar target))
                      end
                  end
              end

(** put field (scalar only, cf. Object.put_field) *)
            | Interm.putfield class field source newvalue =>
              match offsets ! class with
                | None => GARBAGE
                | Some o =>
                  match assoc (FieldSignature.eq_dec (A := A)) field (field_offsets o) with
                    | None => GARBAGE
                    | Some fo =>
                      match FieldSignature.type field with
                        | FieldSignature.Scalar ty =>
                          Target.store _ _ (vop' Size (valtype_of_typ ty)) (OldVar source) fo (OldVar newvalue)
                        | _ => GARBAGE
                      end
                  end
              end

(** static cast : two cases *)
            | statcast from to source target => compile_statcast from to source target


(** dynamic cast : directly read into Vtable *)
            | Interm.dyncast from to source target =>
              seq
              (Target.load _ _ (vop' Size (tyVptr _)) (OldVar source) 0 (NewVar xH))
              (seq
                (romop _ (Some (NewVar xH)) (Target.dyncast_exists (romty := romty A) to) (NewVar (xI xH)))
                (test (NewVar (xI xH))
                  (seq
                    (romop _ (Some (NewVar xH)) (Target.dyncast_offset (romty := romty A) to) (NewVar (xI xH)))
                    (ptrshiftmult _ _ (OldVar source) (NewVar (xI xH)) 1 (OldVar target))
                  )
                  (null _ _ (OldVar target))
                )
              )

(** array index *)
            | arrayindex class index source target =>
              match offsets ! class with
                | None => GARBAGE
                | Some o => ptrshiftmult _ _ (OldVar source) (OldVar index) (size o) (OldVar target)
              end
              
(** invoke *)
            | invoke source class ms args retval =>
              compile_invoke (use_thunks s) source class ms args retval

(** operations on VTTs *)
            | pathop p osrc tgt =>
              compile_pathop p osrc tgt

(** set dynamic type *)
            | setdyntype ismostderived class source path =>
              compile_set_dynamic_type Hhier vop' offsets nativeop ( source) ( path) xH class ismostderived 

(** casttobase (particular case of constant adjustment) *)
            | casttobase source cn k b target =>
              match offsets ! cn with
                | None => GARBAGE
                | Some o =>
                  match k with
                    | Class.Inheritance.Repeated =>
                      match (non_virtual_direct_base_offsets o) ! b with 
                        | None => GARBAGE
                        | Some off => ptrshift _ _ (OldVar source) off (OldVar target)
                      end
                    | _ =>
                      match (virtual_base_offsets o) ! b with
                        | None => GARBAGE
                        | Some off => ptrshift _ _ (OldVar source) off (OldVar target)
                      end
                  end
              end
              
      end.

Function compile_method_body (mb : method_body A nativeop) : Target.func nativeop (romty A) :=
  match mb with
    | Method_body mthis margs mcode =>
      Func (OldVar mthis :: map OldVar margs) (compile mcode)
  end.

Definition f_compile_method (i : ident) (mb : method_body A nativeop) : option (ident * Target.func nativeop (romty A)) := Some (NONSTATIC i, compile_method_body mb). 

Function compile_static_fun (sf : static_fun A nativeop) : Target.func nativeop (romty A) :=
  match sf with
    | Static_fun sargs scode => Func (map OldVar sargs) (compile scode)
  end.

Definition f_compile_static (i : ident) (sf : static_fun A nativeop) : option (ident * Target.func nativeop (romty A)) := Some (STATIC i, compile_static_fun sf).

Definition prog' : Target.program nativeop (romty A) :=
  Target.Program
  (ptree_to_ptree f_compile_static (Interm.statics prog) (ptree_to_ptree f_compile_method (Interm.methods prog) (PTree.empty _)))
  (compile (Interm.main prog))
  (rom := rom Hhier intro guard exis compile_method_name)
  (vtable_access_wf Hhier intro guard)
  .


        Variables memblocks memvalues : Type.

        Variable memop : Memory.op (val A (romty A) mblock)  memblocks memvalues mblock.

        Hypothesis memprop : Memory.prop memop (valop (romty A)  mblock vop').

        Section Match_values.

          Variable global : Globals.t A.
          Variable objmap : PTree.t mblock.

          Inductive match_values : Interm.value A -> Target.val A (romty A) mblock -> Prop
  := 
          | match_values_atom : forall ty va,
            match_values (Interm.Val (Value.atom ty va)) (Target.Atom _ _ va)

          | match_values_pvtt : forall from h p,
            forall v,
              (forall to, path hierarchy to p from h -> is_dynamic hierarchy to -> v = Target.VTTptr (romty := romty A) _ _ (from, (h, p))) ->
              match_values (Interm.Path _ from h p) v
            
          | match_values_null : forall cn,
            match_values (Interm.Val (Value.ptr (Value.null _ cn))) (Target.Ptr _ _ None)

          | match_values_ptr : forall obj,
            Plt obj (Globals.next_object global) ->
            forall ar i h p v,
              (forall o, (Globals.heap global) ! obj = Some o ->
                forall ato to,
                  valid_relative_pointer hierarchy (Object.class o) (Object.arraysize o) ar ato i h p to ->
                  exists bl, objmap ! obj = Some bl /\
                    exists off, relative_pointer_offset offsets (Object.class o) ato ar i p = Some off /\
                      v = (Some (bl, off)))
              ->
              forall hp,
                match_values (Interm.Val (Value.ptr (Value.subobject obj ar i h p hp))) (Target.Ptr _ _ v) (** A pointer still has to match a pointer, because of putfield *)
              .

          Definition match_values' (_ _ : True) := match_values.

        End Match_values.

        Lemma match_values_alloc :
          forall global cn cells obj global',
          Globals.new global cn cells = (obj, global') ->
          forall objmap mb objmap',
            PTree.set obj mb objmap = objmap' ->
              forall v1 v2, match_values global objmap v1 v2 ->
                match_values global' objmap' v1 v2.
        Proof.
          intros until 2.
          inversion 1; subst; econstructor; eauto.
          injection  H; intros; subst; simpl in *.
          eapply Plt_trans.
          eassumption.
          apply Plt_succ.
          injection  H; intros until 2; subst; simpl in *.
          destruct (peq obj0 (Globals.next_object global)).
          subst.
          destruct (Plt_irrefl _ H2).
          repeat rewrite PTree.gso; eauto.
        Qed.

        Lemma match_values_free :
          forall global obj global',
            Globals.remove global obj = global' ->
            forall objmap objmap',
              PTree.remove obj objmap = objmap' ->
              forall v1 v2, match_values global objmap v1 v2 ->
                match_values global' objmap' v1 v2.
        Proof.
          intros until 2.
          destruct global; simpl in *.
          inversion 1; subst; econstructor; eauto.
          destruct (peq obj0 obj).
           subst.
           simpl.
           rewrite PTree.grs.
           congruence.
           simpl; repeat rewrite PTree.gro; eauto.
        Qed.

        Lemma match_values_update : forall global fd global',
          Globals.update global fd = global' ->
          forall objmap v1 v2, match_values global objmap v1 v2 ->
            match_values global' objmap v1 v2.
        Proof.
          unfold Globals.update.
          destruct global; simpl in *.
          inversion 2; subst; econstructor; eauto.
        Qed.

        Section Match_frames.

          Variable global : Globals.t A.
          Variable objmap : PTree.t mblock.

          Inductive match_frames : list ident -> list ident -> Interm.frame A nativeop -> Target.frame A nativeop (romty A) mblock -> Prop :=
          | match_frames_block : forall bo bo' lo lo',
            match bo with
              | None => bo' = None /\ lo = lo'
              | Some o => Plt o (Globals.next_object global) /\ lo = o :: lo' /\ exists o', objmap ! o = Some o' /\ bo' = Some o'
            end ->
            forall stl stl', stl' = map compile stl ->
              match_frames lo lo' (Interm.Block bo stl) (Target.Block _ bo' stl')

          | match_frames_callframe : forall stl stl',
            stl' = map compile stl ->
            forall vars vars', 
              (forall i v, vars ! i = Some v -> exists v', vars' ! (OldVar i) = Some v' /\ match_values global objmap v v') ->
              forall lo fret fret',
                fret' = oapply OldVar fret ->
                match_frames lo lo (Interm.Callframe stl vars fret) (Target.Callframe stl' vars' fret').

        Lemma match_frames_not_a_member : forall q q' u v,
          match_frames q q' u v ->
          forall p, (In p q -> False) -> (In p q' -> False).
        Proof.
          inversion 1; subst; simpl in *; eauto.
        destruct bo; invall; subst; simpl; eauto.
      Qed.

        End Match_frames.

        Lemma match_frames_alloc :
          forall global cn cells obj global',
          Globals.new global cn cells = (obj, global') ->
          forall objmap mb objmap',
            PTree.set obj mb objmap = objmap' ->
              forall lo lo' v1 v2, match_frames global objmap lo lo' v1 v2 ->
                match_frames global' objmap' lo lo' v1 v2.
        Proof.
          intros until 2.
          inversion 1; subst; econstructor; eauto.
          destruct bo; auto.
          injection  H; intros until 2; subst; simpl in *.
          destruct H2.
          destruct H2.
          destruct H3.
          destruct H3.
         split.
          eapply Plt_trans.
          eassumption.
          apply Plt_succ.
         split; trivial.
         destruct (peq p (Globals.next_object global)).
           subst.
           destruct (Plt_irrefl _ H0).
          rewrite PTree.gso; eauto.
          intros.
          destruct (H3 _ _ H0).
          destruct H2.
          eauto using match_values_alloc.
        Qed.

        Lemma match_frames_free :
          forall global obj global',
            Globals.remove global obj = global' ->
            forall objmap objmap',
              PTree.remove obj objmap = objmap' ->
              forall lo,
                (In obj lo -> False) ->
                forall lo' v1 v2, match_frames global objmap lo lo' v1 v2 ->
                  match_frames global' objmap' lo lo' v1 v2.
        Proof.
          intros until 3.
          inversion 1; subst; econstructor; eauto.
          destruct bo; auto.          
          destruct H3.
          destruct H0.
          destruct H3.
          destruct H3.
          destruct global; simpl in *.
          split; trivial.
          split; trivial.
          destruct (peq p obj).
           subst.
           destruct H1.
           auto.
          repeat rewrite PTree.gro; eauto.
          intros.
          destruct (H4 _ _ H).
          destruct H0.
          eauto using match_values_free.
        Qed.

        Lemma match_frames_update :  forall global fd global',
          Globals.update global fd = global' ->
          forall objmap lo lo' v1 v2, match_frames global objmap lo lo' v1 v2 ->
                  match_frames global' objmap lo lo' v1 v2.
        Proof.
          intros until 1.
          inversion 1; subst; econstructor; eauto.
          intros.
          destruct (H2 _ _ H).
          destruct H1.
          eauto using match_values_update.
        Qed.         
              
        Section Bilist.
          
          Variables Q U V : Type.

          Section BDef.
            
          Variable P : Q -> Q -> U -> V -> Type.

          Inductive bilist : Q -> list U -> list V -> Prop :=
          | bilist_nil : forall q, bilist q nil nil
          | bilist_cons : forall q u v q',
            P q q' u v ->
            forall lu lv, bilist q' lu lv ->
              bilist q (u :: lu) (v :: lv)
              .

        End BDef.

        Variables P P' : Q -> Q -> U -> V -> Type.
        Variable R : Q -> Type.
        Hypothesis HimpP : forall q q' u v, P q q' u v -> R q -> R q'.
        Hypothesis Himp : forall q, R q -> forall q' u v, P q q' u v -> P' q q' u v.

        Lemma bilist_imp : forall lo, R lo -> forall lu lv, bilist P lo lu lv -> bilist P' lo lu lv.
        Proof.
          intros.
          revert X.
          induction H; intros; econstructor; eauto.
        Qed.

        End Bilist.      


        Section State.
          
          Variable st : Interm.state A nativeop.
          Variable st' : Target.state A nativeop (romty A) mblock memblocks memvalues.

          Section Invariant'.

            Variable objmap : PTree.t mblock.
            Variable lo : list ident.
          
              Record invariant' : Type := invariant'_intro {
                invariant_current : Target.current st' = compile (Interm.current st);
                invariant_further : Target.further st' = map compile (Interm.further st);
                invariant_vars : forall v vr, (Interm.vars st) ! v = Some vr -> exists vs, (Target.vars st') ! (OldVar v) = Some vs /\ match_values (Interm.globals (Interm.global st)) objmap vr vs
                  ;
                invariant_stack : bilist (match_frames (Interm.globals (Interm.global st)) objmap) lo (Interm.stack st) (Target.stack st');
                invariant_stack_lt : forall i, In i lo -> Plt i (Globals.next_object (Interm.globals (Interm.global st)));
                invariant_stack_no_dup : NoDup lo;
                invariant_object_offsets : forall obj o,
                  (Globals.heap (Interm.globals (Interm.global st))) ! obj = Some o ->
                  offsets ! (Object.class o) <> None
                  ;
                invariant_objects : forall obj,
                  (Globals.heap (Interm.globals (Interm.global st))) ! obj <> None ->
                  objmap ! obj <> None
                  ;
                invariant_fields_guard : forall obj ar i h p fs, Globals.get_field (Globals.field_values (Interm.globals (Interm.global st))) (obj, ar, i, (h, p), fs) <> None ->
                  forall ty, FieldSignature.type fs = FieldSignature.Scalar ty ->
                    Plt obj (Globals.next_object (Interm.globals (Interm.global st)))
                    ;
                invariant_fields : forall obj o,
                  (Globals.heap (Interm.globals (Interm.global st))) ! obj = Some o ->
                  forall ar real i h p from,
                    valid_relative_pointer hierarchy (Object.class o) (Object.arraysize o) ar real i h p from ->
                    forall cfrom, hierarchy ! from = Some cfrom ->
                      forall fs, In fs (Class.fields cfrom) ->
                        forall ty, FieldSignature.type fs = FieldSignature.Scalar ty ->
                          forall vr, Globals.get_field (Globals.field_values (Interm.globals (Interm.global st))) (obj, ar, i, (h, p), fs) = Some vr ->
                            forall oh, objmap ! obj = Some oh ->
                              forall off, relative_pointer_offset offsets (Object.class o) real ar i p = Some off ->
                                forall ofrom, offsets ! from = Some ofrom ->
                                  forall foff, assoc (FieldSignature.eq_dec (A := A)) fs (field_offsets ofrom) = Some foff ->
                                    exists vs, Memory.load memop (vop' Size (valtype_of_typ ty)) (Target.mblocks (Target.memory st')) (Target.mvalues (Target.memory st')) (oh, off + foff) = Some vs /\ match_values (Interm.globals (Interm.global st)) objmap (Interm.Val vr) vs
                                      ;
                invariant_dynamic_type_guard : forall obj ar  i h p ,
                  assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (Interm.dynamic_type (Interm.global st)) <> None ->
                  Plt obj (Globals.next_object (Interm.globals (Interm.global st)))
                  ;
                invariant_dynamic_type : forall obj o,
                  (Globals.heap (Interm.globals (Interm.global st))) ! obj = Some o ->
                  forall ar real i h p from,
                    valid_relative_pointer hierarchy (Object.class o) (Object.arraysize o) ar real i h p from ->
                    is_dynamic hierarchy from ->
                    forall h0 p0 h1 p1,
                      assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (Interm.dynamic_type (Interm.global st)) = Some ((h0, p0), (h1, p1)) ->
                  exists through, 
                    path hierarchy through p0 real h0 /\
                    path hierarchy from p1 through h1 /\
                    (h, p) = concat (h0, p0) (h1, p1)
                    ;
                invariant_vptr : forall obj o,
                  (Globals.heap (Interm.globals (Interm.global st))) ! obj = Some o ->
                  forall ar real i h p from,
                    valid_relative_pointer hierarchy (Object.class o) (Object.arraysize o) ar real i h p from ->
                    is_dynamic hierarchy from ->
                    forall h0 p0 h1 p1,
                      assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (Interm.dynamic_type (Interm.global st)) = Some ((h0, p0), (h1, p1)) ->          
                      forall oh, objmap ! obj = Some oh ->
                        forall off, relative_pointer_offset offsets (Object.class o) real ar i p = Some off ->
                          Memory.load memop (vop' Size (tyVptr _)) (Target.mblocks (Target.memory st')) (Target.mvalues (Target.memory st')) (oh, off) = Some (Vptr (romty := romty A) _ _ (real, (h0, p0), (h1, reduce_path offsets p1)))
                            ;
                invariant_disjoint_objects : forall obj1 obj2,
                  obj1 <> obj2 ->
                  forall o1,
                    objmap ! obj1 = Some o1 ->
                    forall o2,
                      objmap ! obj2 = Some o2 ->
                      o1 <> o2
                      ; 
                invariant_valid_blocks : forall obj of, objmap ! obj = Some of ->
                  Memory.valid_block memop (Target.mblocks (Target.memory st')) of
              ;          
              invariant_object_sizes : forall obj o,
                (Globals.heap (Interm.globals (Interm.global st))) ! obj = Some o ->
                forall of, offsets ! (Object.class o) = Some of ->
                  forall ob, objmap ! obj = Some ob ->
                    Object.arraysize o * size of <= Memory.block_size memop (Target.mblocks (Target.memory st')) ob
              }.

            End Invariant'.

            Inductive invariant : Prop :=
              | invariant_intro (objmap : _) (lo : _) (_ : invariant' objmap lo).

    End State.

    Variable sem : semparam A nativeop.

    Variable tsp : targetsemparam.

    Theorem init : forall st, Interm.initial_state prog st ->
      exists st1, Target.initial_state memop prog' st1 /\
        exists st2,
          star _ (Target.step (sem := sem) vop' memop prog' tsp)
          st1 E0 st2 /\
          invariant st st2.
    Proof.
      inversion 1; subst.
      esplit.
      split.
      econstructor.
      esplit.
      split.
      eleft.
      exists (PTree.empty _) nil.
      split; simpl; try tauto; try (
        intros ? ?;
          rewrite PTree.gempty; congruence
      ); try (
        intro; 
          rewrite PTree.gempty; congruence
      ).
      econstructor.
      constructor.
    intros.
    rewrite H1 in H0; congruence.
    Qed.

    Theorem fin : forall st1 st2 r,
      invariant st1 st2 ->
      Interm.final_state (sem := sem) st1 r ->
      exists st2', 
        star _ (Target.step (sem := sem) vop' memop prog' tsp)
        st2 E0 st2' /\
        Target.final_state st2' r.
    Proof.
      inversion 2; subst.
      esplit.
      split.
      eleft.
      destruct st2.
      destruct H.
      generalize (invariant_stack H).
      simpl.
      inversion 1; subst.
      generalize (invariant_current H).
      simpl.
      intro; subst.
      destruct (invariant_vars H H1).
      Opaque PTree.get PTree.set.
      simpl in *.
      destruct H4.
      inversion H5; subst.
      generalize (inj_pair2_eq_dec _ (ATOM.ty_eq_dec (t := A)) _ _ _  _  H8).
      intro; subst.
      econstructor.
      eassumption.
      assumption.
    Qed.
      
     Hypothesis Htsp_thunks : allow_thunk_call tsp = false ->
       forall s, use_thunks s = false.

     Lemma Htsp_thunks' : forall s, use_thunks s = true ->
       allow_thunk_call tsp = true.
     Proof.
       case_eq (allow_thunk_call tsp).
       trivial.
       intros.
       generalize (Htsp_thunks H s).
       congruence.
     Qed.

     Hypothesis Htsp_function_pointers : allow_function_pointers tsp = false ->
       forall s, use_thunks s = true.

     Lemma Htsp_function_pointers' : forall s, use_thunks s = false ->
       allow_function_pointers tsp = true.
     Proof.
       case_eq (allow_function_pointers tsp).
       trivial.
       intros.
       generalize (Htsp_function_pointers H s).
       congruence.
     Qed.       

     Hypothesis is_empty_dec : forall cn, {is_empty COP hierarchy cn} + {~ is_empty COP hierarchy cn}.

     Section Step.

     Variable st1 : Interm.state A nativeop.
     Variable t : trace (evtr sem).   
     Variable st1' : Interm.state A nativeop.

     Hypothesis Hstep : Interm.step prog (is_primary_path offsets) st1 t st1'.

     Variable st2 : Target.state A nativeop (romty A) mblock memblocks memvalues.

     Hypothesis Hinv : invariant st1 st2.

     Notation goal := (exists st2',
       plus _ (step (sem := sem) vop' memop prog' tsp) st2 t st2' /\
       invariant st1' st2') (only parsing).

     Lemma preservation_skip : forall stm stl vars stack global, 
       Interm.State (Interm.skip A nativeop) (stm :: stl) vars stack global =
       st1 -> goal.
     Proof.
       intros; subst.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       Opaque concat Globals.get_field Globals.put_field.
       inversion H; simpl in *; subst; simpl in *.
       esplit.
       split.
       eapply plus_left.
       econstructor.
       eleft.
       repeat rewrite E0_left; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; auto.
     Qed.      

     Lemma preservation_seq : forall s1 s2 stl vars stack global,
       Interm.State (Interm.seq s1 s2) stl vars stack global = st1 ->
       goal.
     Proof.
       intros; subst.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       Opaque concat Globals.get_field Globals.put_field.
       inversion H; simpl in *; subst; simpl in *.
       esplit.
       split.
       eapply plus_left.
       econstructor.
       eleft.
       repeat rewrite E0_left; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; auto.
     Qed.

     Lemma preservation_move : forall source target stl vars stack global,
       Interm.State (Interm.move A nativeop source target) stl vars stack global = st1 ->
       goal.
     Proof.
       intros; subst.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       Opaque concat Globals.get_field Globals.put_field.
       inversion H; simpl in *; subst; simpl in *.
       destruct (invariant_vars0 _ _ H7).
       destruct H0.
       esplit.
       split.
       eapply plus_left.
       econstructor.
       eassumption.
       reflexivity.
       eleft.
       repeat rewrite E0_left; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; auto.
       intros ? ?.
       destruct (peq target v0).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intros; subst; eauto.
       repeat rewrite PTree.gso; eauto; congruence.
     Qed.       

     Lemma preservation_test : forall varb ifso ifnot stl vars stack global,
       Interm.State (Interm.test varb ifso ifnot) stl vars stack global = st1 ->
       goal.
     Proof.
       intros; subst.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       Opaque concat Globals.get_field Globals.put_field.
       inversion H; simpl in *; subst; simpl in *.
       destruct (invariant_vars0 _ _ H8).
       destruct H0.
       inversion H1; subst.
       generalize (inj_pair2_eq_dec _ (ATOM.ty_eq_dec (t := A)) _ _ _  _  H4).
       intro; subst.      
       esplit.
       split.
       eapply plus_left.
       econstructor.
       eassumption.
       eassumption.
       reflexivity.
       eleft.
       repeat rewrite E0_left; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; auto.
       destruct b; reflexivity.
     Qed.

     Lemma preservation_loop : forall stmt stl vars stack global,
       Interm.State (Interm.loop stmt) stl vars stack global = st1 ->
       goal.
     Proof.
       intros; subst.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       Opaque concat Globals.get_field Globals.put_field.
       inversion H; simpl in *; subst; simpl in *.
       esplit.
       split.
       eapply plus_left.
       econstructor.
       eleft.
       repeat rewrite E0_left; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; auto.
     Qed.       

     Lemma preservation_block_None : forall stm stl vars stack global,
       Interm.State (Interm.block None stm) stl vars stack global = st1 ->
       goal.
     Proof.
       intros; subst.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       Opaque concat Globals.get_field Globals.put_field.
       inversion H; simpl in *; subst; simpl in *.
       esplit.
       split.
       eapply plus_left.
       econstructor.
       eleft.
       repeat rewrite E0_left; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; auto.       
       econstructor; eauto.
       econstructor; eauto.
     Qed.

     Lemma preservation_block_Some : forall c cn sz stm stl vars stack gl dt,
       Interm.State (Interm.block (Some (c, (cn, sz))) stm) stl vars stack (Global gl dt) = st1 ->
       goal.
     Proof.
       intros; subst.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       Opaque concat Globals.get_field Globals.put_field.
       inversion H; simpl in *; subst; simpl in *.
       assert (offsets ! cn <> None) by eauto.
       case_eq (offsets ! cn); try congruence.
       intros.
       injection H12; intros; subst.
       destruct memory; simpl in *.
       case_eq (Memory.alloc memop mblocks (sz * size t)).
       intros.
       esplit.
       split.
       eapply plus_left.
       econstructor.
       eassumption.
       reflexivity.
       eleft.       
       repeat rewrite E0_left; eauto using evtr_sem.
       exists (PTree.set (Globals.next_object gl) m objmap) (Globals.next_object gl :: lo).
       split; simpl; auto.
       
(** 14 variables *)
       intros ? ?.
       destruct (peq c v); simpl.
        subst.
        repeat rewrite PTree.gss; simpl.
        injection 1; intro; subst; simpl.
        esplit.
        split.
        reflexivity.
        econstructor; simpl.
        apply Plt_succ.
        repeat rewrite PTree.gss.
        injection 1; intro; subst; simpl.
        intros.
        esplit.
        split.
         reflexivity.
        inversion H5; subst.
        inversion H6; subst.
        exists 0.
        unfold relative_pointer_offset.
        simpl.
        rewrite H1.
        unfold subobject_offset.
        rewrite H1.
        rewrite (virtual_base_offsets_self (intro H1)).
        simpl.
        eauto.
       rewrite PTree.gso; try congruence.
       rewrite PTree.gso; try congruence.
       intro.
       destruct (invariant_vars0 _ _ H3).
       destruct H4.
       esplit.
       split.
        eassumption.
       eapply match_values_alloc.
       eassumption.
       reflexivity.
       assumption.

(** 13 blocks *)
      econstructor; simpl.
       econstructor; simpl.
       split.
        apply Plt_succ.
       split.
        reflexivity.
       rewrite PTree.gss.
       eauto.
       reflexivity.
      eapply bilist_imp with (R := fun _ => True).
      tauto.
      intros ? ? ? ? ?.
      eapply match_frames_alloc.
      eassumption.
      reflexivity.
      trivial.
      eassumption.

(** 12 list lt *)
destruct 1.
 subst.
 apply Plt_succ.
eapply Plt_trans.
eauto.
apply Plt_succ.

(** 11 list no dup *)
constructor.
intro.
destruct (Plt_irrefl (Globals.next_object gl)).
eapply invariant_stack_lt0.
assumption.
assumption.

(** 10 offset data *)
      intro.
      destruct (peq obj (Globals.next_object gl)).
       subst.
       rewrite PTree.gss.
       injection 1; intro; subst; simpl.
       eauto.
      rewrite PTree.gso; eauto.

(** 9 block-object mapping *)
      intro.
      destruct (peq obj (Globals.next_object gl)).
       subst.
       repeat rewrite PTree.gss.
       congruence.
      repeat rewrite PTree.gso; eauto.

(** 8 field guard *)
      intros.
      eapply Plt_trans.
      eauto.
      apply Plt_succ.

(** 7 fields *)
      intro.
      destruct (peq obj (Globals.next_object gl)).
       subst.
       intros.
       assert (
 Globals.get_field (Globals.field_values gl) (Globals.next_object gl, ar, i, (h, p), fs) <> None
      ) by congruence.             
      destruct (Plt_irrefl _ (invariant_fields_guard0 _ _ _ _ _ _ H16 _ H7)).     
     repeat rewrite PTree.gso; eauto.
     intros.
     destruct (invariant_fields0 _ _ H3 _ _ _ _ _ _ H4 _ H5 _ H6 _ H7 _ H8 _ H9 _ H13 _ H14 _ H15).
     destruct H16.
     esplit.
     split.
     eapply trans_equal.
     eapply Memory.load_alloc.
     eassumption.
     eassumption.
     eassumption.
    eapply match_values_alloc.
    eassumption.
    reflexivity.
    assumption.

(** 6 dynamic type guard *)    
    intros.
    eapply Plt_trans.
    eauto.
    apply Plt_succ.

(** 5 dynamic type paths *)
    intro.
    destruct (
      peq obj (Globals.next_object gl)
    ).
     subst.
     intros.
     assert (
assoc (pointer_eq_dec (A:=A))
         (Globals.next_object gl, (ar, i, (h, p))) dt <> None
     ) by congruence.
     destruct (Plt_irrefl _ (invariant_dynamic_type_guard0 _ _ _ _ _ H7)).
    rewrite PTree.gso; eauto.

(** 4 dynamic type memory *)
    intro.
    destruct (
      peq obj (Globals.next_object gl)
    ).
     subst.
     intros.
     assert (
       assoc (pointer_eq_dec (A:=A))
       (Globals.next_object gl, (ar, i, (h, p))) dt <> None
     ) by congruence.
     destruct (Plt_irrefl _ (invariant_dynamic_type_guard0 _ _ _ _ _ H9)).     
    rewrite PTree.gso; eauto.
    rewrite PTree.gso; eauto.
    intros.
    eapply trans_equal.
    eapply Memory.load_alloc.
    eassumption.
    eassumption.
    eauto.

(** 3 disjoint blocks *)    
    intro.
    destruct (peq obj1 (Globals.next_object gl)).
     subst.
     rewrite PTree.gss.
     injection 2; intro; subst.
     rewrite PTree.gso; try congruence.
     intros.
     generalize (invariant_valid_blocks0 _ _ H5).
     intro.
     generalize (Memory.alloc_invalid_before memprop H2).
     intro.
     congruence.
    rewrite PTree.gso; try congruence.
    intros until 2.
    destruct (peq obj2 (Globals.next_object gl)).
     subst.
     rewrite PTree.gss.
     injection 1; intro; subst.
     generalize (invariant_valid_blocks0 _ _ H4).
     intro.
     generalize (Memory.alloc_invalid_before memprop H2).
     intro; congruence.
    rewrite PTree.gso; eauto.

(** 2 valid blocks *)
intro.
destruct (peq obj (Globals.next_object gl)).
 subst.
 rewrite PTree.gss.
 injection 1; intro; subst.
 eauto using Memory.alloc_valid_same.
rewrite PTree.gso.
intros.
eapply Memory.alloc_valid_other.
eassumption.
eassumption.
eauto.
assumption.

(** 1 block sizes *)
intro.
destruct (peq obj (Globals.next_object gl)).
 subst.
 rewrite PTree.gss.
 injection 1; intro; subst.
 simpl.
 rewrite H1.
 injection 1; intro; subst.
 rewrite PTree.gss.
 injection 1; intro; subst.
 erewrite Memory.alloc_block_size_same.
 3 : eassumption.
 omega.
 eassumption.
repeat rewrite PTree.gso; eauto.
intros.
erewrite Memory.alloc_block_size_other; eauto.
generalize (invariant_valid_blocks0 _ _ H5).
intro.
generalize (Memory.alloc_invalid_before memprop H2).
intro; congruence.

Qed.

Lemma preservation_exit_O : forall stl vars stack global,
  Interm.State (Interm.exit A nativeop 0) stl vars stack global = st1 ->
  goal.
Proof.
       intros; subst.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       Opaque concat Globals.get_field Globals.put_field.
       inversion H; simpl in *; subst; simpl in *.
       esplit.
       split.
       eapply plus_left.
       econstructor.
       eleft.
       repeat rewrite E0_left; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; auto.
Qed.

Lemma preservation_exit_S : forall stm stl vars oobj stl' stack gl dt,
  Interm.State stm stl vars (Interm.Block oobj stl' :: stack)
         (Global gl dt) = st1 ->
  forall stm',  Interm.exit_succ stm = Some stm' ->

         goal.
Proof.
       intros; subst.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       Opaque concat Globals.get_field Globals.put_field.
       inversion H; simpl in *; subst; simpl in *.
       replace stm'0 with stm' in * by congruence.
       assert (Target.exit_succ (compile stm) = Some (compile stm')).
        functional inversion H11; subst; reflexivity.
       inversion invariant_stack0; subst.
       inversion H5; subst.
       destruct oobj.

(** some object to deallocate *)
 destruct H8.
 destruct H3.
 subst.
 destruct H4.
 destruct H3.
 subst.
 destruct memory; simpl in *.
       esplit.
       split.
       eapply plus_left.
       econstructor.
       reflexivity.
       eassumption.
       eleft.
       repeat rewrite E0_left; eauto using evtr_sem.
       exists (PTree.remove p objmap) q'.
       split; simpl; auto.

(** 12 vars *)
intros.
destruct (invariant_vars0 _ _ H4).
destruct H6.
eauto using match_values_free.

(** 11 stack *)
revert H7.
eapply bilist_imp with (R := fun q' => In p q' -> False).
intros; eauto using match_frames_not_a_member.
eapply match_frames_free.
reflexivity.
reflexivity.
inversion invariant_stack_no_dup0.
assumption.

(** 10 no dup *)
inversion invariant_stack_no_dup0.
assumption.

(** 9 offsets exist *)
intro.
destruct (peq p obj).
 subst.
 rewrite PTree.grs.
 congruence.
rewrite PTree.gro; eauto.

(** 8 objmap exist *)
intro.
destruct (peq p obj).
 subst.
 rewrite PTree.grs.
 congruence.
repeat rewrite PTree.gro; eauto.

(** 7 field values *)
intro.
destruct (peq p obj).
 subst.
 rewrite PTree.grs.
 congruence.
repeat rewrite PTree.gro; eauto.
intros.
destruct (invariant_fields0 _ _ H4 _ _ _ _ _ _ H6
 _ H8 _ H9 _ H10 _ H12 _ H13 _ H14 _ H15 _ H16).
destruct H17.
esplit.
split.
erewrite Memory.load_free_other.
eassumption.
eassumption.
eauto.
eauto using match_values_free.

(** 6 dynamic type well formed *)
intro.
destruct (peq p obj).
 subst.
 rewrite PTree.grs.
 congruence.
rewrite PTree.gro; eauto.

(** 5 vptr *)
intro.
destruct (peq p obj).
 subst.
 rewrite PTree.grs.
 congruence.
repeat rewrite PTree.gro; eauto.
intros.
erewrite Memory.load_free_other; eauto.

(** 4 disjoint blocks *)
intro.
destruct (peq p obj1).
 subst.
 rewrite PTree.grs.
 congruence.
intro.
destruct (peq p obj2).
 subst.
 rewrite PTree.grs.
 congruence.
intro.
repeat rewrite PTree.gro; eauto; congruence.

(** 3 valid blocks *)
intro.
destruct (peq p obj).
 subst.
 rewrite PTree.grs.
 congruence.
rewrite PTree.gro.
intros.
eapply Memory.free_valid_other.
eassumption.
eauto.
eauto.
congruence.

(** 2 block size *)
intro.
destruct (peq p obj).
 subst.
 rewrite PTree.grs.
 congruence.
repeat rewrite PTree.gro; eauto.
intros.
erewrite Memory.free_block_size_other; eauto.

(** 1 : no object *)
destruct H8; subst.
destruct memory; simpl in *.
esplit.
split.
eapply plus_left.
econstructor.
reflexivity.
eassumption.
eleft.
repeat rewrite E0_left; eauto using evtr_sem.
exists objmap q'.
split; simpl; auto.
Qed.

Lemma preservation_return : forall ov stl vars stl' vars' orv stack global,
  Interm.State (Interm.ret A nativeop ov) stl vars
  (Interm.Callframe stl' vars' orv :: stack) global = st1
  -> goal.
Proof.
       intros; subst.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       Opaque concat Globals.get_field Globals.put_field.
       inversion H; simpl in *; subst; simpl in *.
       inversion invariant_stack0; subst; simpl in *.
       inversion H3; subst; simpl in *.
       destruct orv; simpl in *.

(** some argument *)
invall; subst.
destruct (invariant_vars0 _ _ H2).
destruct H0.
esplit.
split.
eapply plus_left.
econstructor.
esplit.
 split.
 reflexivity.
eauto.
eleft.
repeat rewrite E0_left; eauto using evtr_sem.
exists objmap q'.
split; simpl; auto.       
intro.
destruct (peq i v).
 subst.
 repeat rewrite PTree.gss.
 injection 1; intro; subst.
 eauto.
repeat rewrite PTree.gso; eauto; congruence.

(** no argument *)
invall; subst.
esplit.
split.
 eapply plus_left.
econstructor.
eexact vars0.
split.
 reflexivity.
reflexivity.
eleft.
repeat rewrite E0_left; eauto using evtr_sem.
exists objmap q'.
split; simpl; auto.       
Qed.

Section Set_params.
  Variable vars : PTree.t (Interm.value A).
  Variable gl : Globals.t A.
  Variable objmap : PTree.t mblock.

  Variable vars0 : PTree.t (val A (romty A) mblock).
  
  Hypothesis Hvars: forall (v : positive) (vr : value A),
    vars ! v = Some vr ->
    exists vs : val A (romty A) mblock,
      vars0 ! (v~0) = Some vs /\
      match_values gl objmap vr vs
      .

  Lemma set_params_exist : forall l vargs, 
    map (@Some _) l = map (fun v => vars ! v) vargs ->
    exists l',
      map (@Some _) l' = map (fun v => vars0 ! v) (map xO vargs) /\
      forall lp (v : positive) (vr : value A),
        (Interm.set_params l lp) ! v = Some vr ->
        exists vs : val A (romty A) mblock,
          (Target.set_params l' (map xO lp)) ! (v~0) = Some vs /\
          match_values gl objmap vr vs
      .
Proof.
  Transparent Interm.set_params Target.set_params.
  induction l; destruct vargs; simpl; try congruence.
   intros _.
   exists nil.
   split.
    reflexivity.
   intro.   
   replace (Interm.set_params (A := A) nil lp)  with (PTree.empty (value A)) by (destruct lp; reflexivity).
   intro.
   rewrite PTree.gempty.
   congruence.
  injection 1; intros; subst.
  symmetry in H1.
  destruct (IHl _ H0).
  destruct H2.
  destruct (Hvars H1).
  destruct H4.
  exists (x0 :: x).
  simpl.
  split.
  congruence.
  intro.
  destruct lp.
   simpl.
   intro.
   rewrite PTree.gempty.
   congruence.
  simpl.
  intros ? ?.
  destruct (peq i v).
   subst.
   repeat rewrite PTree.gss.
   injection 1; intro; subst; eauto.
  repeat rewrite PTree.gso; eauto.
  congruence.
Qed.

Lemma map_atom : forall args source,
  map
  (fun a : sigT (ATOM.val (t:=A)) =>
    let (ty, va) := a in Some (Val (Value.atom ty va))) args =
  map (fun v : positive => vars ! v) (source) ->
  map (fun a : sigT (ATOM.val (t := A)) => let (ty, va) := a in Some (Target.Atom (romty A) _ va)) args =         
  map (fun v => PTree.get v vars0) (map xO source).
Proof.
  induction args; destruct source; simpl; try congruence.
  destruct a.
  injection 1; intros.
  symmetry in H1.
  destruct (Hvars H1).
  destruct H2.
  inversion H3; subst.
  generalize (inj_pair2_eq_dec _ (ATOM.ty_eq_dec (t := A)) _ _ _  _  H6).
  intro; subst.
  f_equal.
  congruence.
  auto.
Qed.

End Set_params.

Lemma preservation_call : forall kind vargs oret stl vars stack global,
  Interm.State (Interm.call nativeop kind vargs oret) stl vars stack global = st1   ->
  goal.
Proof.
       intros; subst.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       Opaque concat Globals.get_field Globals.put_field.
       inversion H; simpl in *; subst; simpl in *.
       Opaque Interm.set_params Target.set_params.
       destruct kind; invall; subst; simpl in *.

(** non-virtual *)
unfold compile_method_name.
rewrite H1.
rewrite H2.
rewrite H3.
destruct x2; simpl in *.
destruct (set_params_exist invariant_vars0 H8).
destruct H0.
generalize (H5 (mthis :: margs)).
intros.
esplit.
split.
eapply plus_left.
econstructor.
reflexivity.
simpl.
erewrite ptree_to_ptree_other.
eapply ptree_to_ptree_some.
unfold f_compile_method.
intros; left; congruence.
eassumption.
reflexivity.
unfold f_compile_static; intros; congruence.
eassumption.
reflexivity.
eleft.
repeat rewrite E0_left; eauto using evtr_sem.
exists objmap lo.
split; simpl; auto.
econstructor; eauto.
econstructor; eauto.

(** static *)
destruct x; simpl in *.
destruct (set_params_exist invariant_vars0 H8).
destruct H0.
generalize (H2 (sargs)).
intros.
esplit.
split.
eapply plus_left.
econstructor.
reflexivity.
simpl.
eapply ptree_to_ptree_some.
unfold f_compile_static.
intros; left; congruence.
eassumption.
reflexivity.
eassumption.
reflexivity.
eleft.
repeat rewrite E0_left; eauto using evtr_sem.
exists objmap lo.
split; simpl; auto.
econstructor; eauto.
econstructor; eauto.
Qed.
  
Lemma preservation_native : forall op source target stl vars stack global,
  Interm.State (Interm.native A op source target) stl vars stack global = st1->
  goal.
Proof.
       intros; subst.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       Opaque concat Globals.get_field Globals.put_field.
       inversion H; simpl in *; subst; simpl in *.
       destruct ores; invall; subst; simpl in *.

(** some result *)
       destruct s; invall; subst; simpl in *.
       esplit.
       split.
       eapply plus_left.
       econstructor.
       eauto using map_atom.
       eassumption.
       simpl.
       eauto.
       econstructor.
       rewrite E0_right; eauto using evtr_sem.
       exists objmap lo.
       split; simpl;  eauto.
       intro.
       destruct (peq v0 x0).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intro; subst.
        esplit.
        split.
        reflexivity.
        econstructor.
       repeat rewrite PTree.gso; eauto.
       congruence.

(** no result *)
       esplit.
       split.
       eapply plus_left.
       econstructor.
       eauto using map_atom.
       eassumption.
       simpl.
       eauto.
       econstructor.
       rewrite E0_right; eauto using evtr_sem.
       exists objmap lo.
       split; simpl;  eauto.
Qed.

Lemma preservation_null : forall class target stl vars stack global,
  Interm.State (Interm.null A nativeop class target) stl vars stack global = st1 ->
  goal.
Proof.
       intros; subst.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       Opaque concat Globals.get_field Globals.put_field.
       inversion H; simpl in *; subst; simpl in *.
       esplit.
       split.
       eapply plus_left.
       econstructor.
       reflexivity.
       eleft.
       rewrite E0_right; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; eauto.
       intro.
       destruct (peq target v).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intro; subst.
        esplit.
        split.
         reflexivity.
        econstructor.
       repeat rewrite PTree.gso; eauto.
       congruence.
Qed.

Lemma preservation_ptreq : forall v1 v2 target stl vars stack global dt,
  Interm.State (Interm.ptreq A nativeop v1 v2 target) stl vars stack (Global global dt) = st1 ->
  goal.
Proof.
       intros; subst.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       Opaque concat Globals.get_field Globals.put_field.
       inversion H; simpl in *; subst; simpl in *.
       destruct (invariant_vars0 _ _ H9).
       destruct H0.
       destruct (invariant_vars0 _ _ H11).
       destruct H2.
       inversion H1; subst.
       inversion H3; subst.

       (** null vs null *)
       destruct (
         Value.pointer_eq_dec (Value.null A cn) (Value.null A cn0)
       ); try congruence.
       esplit.
       split.
       eapply plus_left.
       eapply step_ptreq with (b := true).
       eassumption.
       eassumption.
       reflexivity.
       reflexivity.
       reflexivity.
       eleft.
       rewrite E0_right; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; eauto.
       intro.
       destruct (peq target v).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intro; subst.
        esplit.
        split.
         reflexivity.
        econstructor.
       repeat rewrite PTree.gso; eauto.
       congruence.

       (** null vs non-null *)
       destruct (
         Value.pointer_eq_dec (Value.null A cn)
         (Value.subobject obj ar i h p hp)
       ); try congruence.      
       inversion H12; subst.
       destruct (H6 _ H8 _ _ H17).
       invall; subst.
       esplit.
       split.
       eapply plus_left.
       eapply step_ptreq with (b := false).
       eassumption.
       eassumption.
       congruence.
       reflexivity.
       reflexivity.
       eleft.
       rewrite E0_right; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; eauto.
       intro.
       destruct (peq target v).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intro; subst.
        esplit.
        split.
         reflexivity.
        econstructor.
       repeat rewrite PTree.gso; eauto.
       congruence.

    inversion H10; subst.
    destruct (H6 _ H8 _ _ H17).
    invall; subst.
    inversion H3; subst.

     (* non-null vs null *)
     esplit.
     split.
     eapply plus_left.
     eapply step_ptreq with (b := false).
      eassumption.
      eassumption.
      congruence.
      reflexivity.
      reflexivity.
     eleft.
       rewrite E0_right; eauto using evtr_sem.
       destruct (
         Value.pointer_eq_dec (Value.subobject obj ar i h p hp)
         (Value.null A cn)
       ); try congruence.
       exists objmap lo.
       split; simpl; eauto.
       intro.
       destruct (peq target v).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intro; subst.
        esplit.
        split.
         reflexivity.
        econstructor.
       repeat rewrite PTree.gso; eauto.
       congruence.

       (* both non-null *)
       destruct (is_some_constr hp).
       destruct (is_some_constr hp0).
       replace x2 with x0 in * by congruence.
       inversion H3; subst.
       inversion H12; subst.
       destruct (H24 _ H20 _ _ H25).
       invall; subst.
       destruct (
          Value.pointer_eq_dec (Value.subobject obj ar i h p hp)
                   (Value.subobject obj0 ar0 i0 h0 p0 hp0)
       ).

(** equal *)
       replace o0 with o in * by congruence.
       injection e1; intros; subst.
       inversion H17; subst.
       inversion H25; subst.
       generalize (valid_array_path_last H4 H27).
       intro; subst.
       functional inversion H21; subst.
       functional inversion H14; subst.
       replace z0 with z1 in * by congruence.
       replace ofto0 with ofto in * by congruence.
       replace z3 with z2 in * by congruence.
       replace x3 with x in * by congruence.
       esplit.
       split.
       eapply plus_left.
       eapply step_ptreq with (b := true).
       eassumption.
       eassumption.
       reflexivity.
       reflexivity.
       reflexivity.
       eleft.
       rewrite E0_right; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; eauto.
       intro.
       destruct (peq target v).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intro; subst.
        esplit.
        split.
         reflexivity.
        constructor.
       repeat rewrite PTree.gso; eauto.
       congruence.

(** not equal *)
destruct (peq obj0 obj).

 (** same object: invoke POPL'11 theorem *)
 subst.
 assert (to0 = to).
  inversion H17.
  inversion H25.
  generalize (path_last H30).
  generalize (path_last H26).
  intro; congruence.
subst.
replace x3 with x in * by congruence.
replace o0 with o in * by congruence.
assert (x1 <> x4).
 assert (offsets ! to <> None).
  eapply exis.
  inversion H17; subst; eauto using path_defined_to.
 destruct (is_empty_dec to).
 (** empty *)
  intro; subst.
  generalize (disjoint_empty_base_offsets_disjoint_pointer_paths
 Hhier intro guard empty_prop i1 H4 H17 H25 H14 H21).
  injection 1; intros; subst.
  generalize (is_some_eq hp hp0).
  congruence.
 (** not empty *)
  eapply (nonempty_distinct_offsets
   Hhier intro n0 H4 H17 H25 H14 H21).
  intro.
  injection H22; intros; subst.
  generalize (is_some_eq hp hp0).
  congruence.
     esplit.
     split.
     eapply plus_left.
     eapply step_ptreq with (b := false).
      eassumption.
      eassumption.
      congruence.
      reflexivity.
      reflexivity.
     eleft.
       rewrite E0_right; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; eauto.
       intro.
       destruct (peq target v).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intro; subst.
        esplit.
        split.
         reflexivity.
        econstructor.
       repeat rewrite PTree.gso; eauto.
       congruence.

(** different objects: OK thanks to simplified memory model *)
     assert (x <> x3) by eauto.
     esplit.
     split.
     eapply plus_left.
     eapply step_ptreq with (b := false).
      eassumption.
      eassumption.
      congruence.
      reflexivity.
      reflexivity.
     eleft.
       rewrite E0_right; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; eauto.
       intro.
       destruct (peq target v).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intro; subst.
        esplit.
        split.
         reflexivity.
        econstructor.
       repeat rewrite PTree.gso; eauto.
       congruence.
Qed.

  Lemma array_path_offset_right : forall cn ar n cn' n', valid_array_path hierarchy cn' n' cn n ar -> forall accu o,
    array_path_offset offsets accu cn ar = Some o ->

      forall co', offsets ! cn' = Some co' ->
      forall i, 0 <= i < n' -> forall h p cl, path hierarchy cl p cn' h ->
        forall z, subobject_offset offsets cn' p = Some z ->
          forall co, offsets ! cl = Some co ->
            forall fs fz, assoc (FieldSignature.eq_dec (A := A)) fs (field_offsets co) = Some fz ->
              forall ty n'', FieldSignature.type fs = FieldSignature.Struct ty n'' ->
              array_path_offset offsets accu cn (ar ++ (i, (h, p), fs) :: nil) = Some (o + i * size co' + z + fz).
Proof.
  induction 1;
    functional inversion 1; subst; simpl.
     intros.
     rewrite H2.
     rewrite H5.
     rewrite (path_last H4).
     rewrite H6.
     rewrite H8.
     rewrite H7.
     trivial.
    intros.
    rewrite H13.
    rewrite H16.
    rewrite H18.
    rewrite H19.
    rewrite H20.
    rewrite H21.
    replace ci'0 with by in * by congruence.
    replace _x0 with by_n in * by congruence.
    erewrite IHvalid_array_path.
    reflexivity.
    assumption.
    assumption.
    assumption.
    eassumption.
    assumption.
    eassumption.
    assumption.
    eassumption.
Qed. (** carbon copy of POPL'11 *)

Lemma preservation_getfield : forall class fs source target stl vars stack global dt,
  Interm.State (getfield nativeop class fs source target) stl vars stack (Global global dt) = st1 ->
  goal.
Proof.
       intros; subst.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       destruct memory; simpl in *.
       Opaque concat Globals.get_field Globals.put_field.
       inversion H; simpl in *; subst; simpl in *.
       destruct (invariant_vars0 _ _ H10).
       destruct H0.
       inversion H1; subst.
       inversion H11; subst.
       destruct (H9 _ H4 _ _ H16).
       invall; subst.
       inversion H16; subst.
       generalize (path_last H17).
       intro.
       replace to with class in * by congruence.
       assert (offsets ! class <> None) by eauto using path_defined_to.
       case_eq (offsets ! class); try congruence.
       intros.
       generalize (field_offsets_exist (intro H20) H13 H14).
       case_eq (assoc (@FieldSignature.eq_dec _) fs (field_offsets t)); try congruence.
       intros until 1.
       intros _.
       case_eq (FieldSignature.type fs).

(** scalar *)
intros.
destruct (invariant_fields0 _ _ H4 _ _ _ _ _ _ H16 _ H13 _ H14 _ H22 _ H15 _ H3 _ H5 _ H20 _ H21).
destruct H23.
esplit.
split.
eapply plus_left.
econstructor.
eassumption.
eassumption.
reflexivity.
eleft.
       rewrite E0_right; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; eauto.
       intro.
       destruct (peq target v0).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intro; subst; eauto.
       repeat rewrite PTree.gso; eauto.
       congruence.

(** structure *)
intros.
revert H15.
Transparent Globals.get_field.
unfold Globals.get_field.
rewrite H22.
injection 1; intro; subst.
functional inversion H5; subst.
assert (offsets ! struct <> None) by eauto using Well_formed_hierarchy.complete_struct.
case_eq (offsets ! struct); try congruence.
intros.
esplit.
split.
eapply plus_left.
econstructor.
eassumption.
reflexivity.
eleft.
       rewrite E0_right; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; eauto.
       intro.
       destruct (peq target v).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intro; subst.
        esplit.
        split.
         reflexivity.
        econstructor.
        assumption.
        rewrite H4.
        injection 1; intro; subst.
        inversion 1; subst.
        destruct (valid_array_path_concat_recip H31).
        destruct H35.
        destruct H35.
        generalize (valid_array_path_last H2 H35).
        intro; subst.
        esplit.
        split.
        eassumption.
        unfold relative_pointer_offset.
        rewrite (array_path_offset_right H2 H24 H25 (conj H6 H7) H17  H26 H20 H21 H22).
        inversion H34; subst.
        injection H37; intros; subst.
        injection (path_last H34); intro; subst.
        rewrite H27.
        unfold subobject_offset.
        rewrite H27.
        rewrite (virtual_base_offsets_self (intro H27)).
        simpl.
        esplit.
        split.
        reflexivity.
        f_equal.
        f_equal.
        omega.
       repeat rewrite PTree.gso; eauto.
       congruence.
Qed.

Lemma preservation_putfield : forall class fs source newvalue stl vars stack global dt,
  Interm.State (putfield nativeop class fs source newvalue) stl vars stack (Global global dt) = st1 ->
  goal.
Proof.
       intros; subst.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       destruct memory; simpl in *.
       Opaque concat Globals.get_field Globals.put_field.
       inversion H; simpl in *; subst; simpl in *.
       destruct (invariant_vars0 _ _ H10).
       destruct H0.
       inversion H1; subst.
       inversion H11; subst.
       destruct (H9 _ H4 _ _ H17).
       invall; subst.
       inversion H17; subst.
       generalize (path_last H18).
       intro.
       replace to with class in * by congruence.
       assert (offsets ! class <> None) by eauto using path_defined_to.
       case_eq (offsets ! class); try congruence.
       intros.
       generalize (field_offsets_exist (intro H21) H13 H14).
       case_eq (assoc (@FieldSignature.eq_dec _) fs (field_offsets t)); try congruence.
       intros until 1.
       intros _.
       generalize H16.
       Transparent Globals.put_field.
       unfold Globals.put_field.
       case_eq (FieldSignature.type fs); try congruence.
       intros until 1.
       case_eq (Value.check t0 v); try congruence.
       intros until 1.
       generalize (Value.check_some H24).
       intro; subst.
       injection 1; intro; subst.
       destruct (invariant_vars0 _ _ H15).
       destruct H26.
       assert (typ_size (PF (vop' := vop') vop'_pos) t0 =
         Memory.valsize (valop (A:=A) (romty A) mblock vop') x1 /\
         typ_align (PF (vop':=vop') vop'_pos) t0 =
         Memory.valalign (valop (A:=A) (romty A) mblock vop') x1 
       ).
        functional inversion H24.
         clear H33; subst.
         inversion H27; subst; split; reflexivity.
        clear H33; subst.
        inversion H27; subst; split; reflexivity.
        clear H34; subst.
        inversion H27; subst; split; reflexivity. 
       assert (~ is_empty COP hierarchy class).
        intro.
        destruct (Is_empty.fields_struct (is_empty_prop COP hierarchy) H29 H13 H14).
        destruct H30.
        congruence.
        assert (offsets ! (Object.class o) <> None) by eauto.
        case_eq (offsets ! (Object.class o)); try congruence.
        intros.
        destruct H28.
        generalize (refl_equal (field_align (PF (vop':=vop') vop'_pos) offsets fs)).
        unfold field_align at 2.
        rewrite H23.
        intros.
        destruct (field_align_prop Hhier intro H17 H5 H31 H21 H33 H22).
        destruct (relative_pointer_data_incl intro H17 H29  H5).        
        generalize (H37 _ H31 _ H21).
       intro.
       generalize (data_size_high_bound (intro H31)).
       intro.
        generalize (field_offsets_low_bound (intro H21) H22).
        intro.
        generalize (refl_equal (field_data_size (PF (vop' := vop') vop'_pos) offsets fs)).
        unfold field_data_size at 2.
        rewrite H23.
        intros.
        refine (_ (non_virtual_data_size_field_offsets (intro H21) H22 _ H41)).
        2 : intros; congruence.
       intro.
       assert ((Object.arraysize o - 1) * size t1 + size t1 = Object.arraysize o * size t1) by ring.
refine (_ (Memory.store_some (val := val A (romty A) mblock)
(o := memop)
(v := valop (romty A) mblock vop')
_
(i := x0 + z)
(mv :=  x1)
_
(memb := mblocks)
(b := x)
_
_
_
(memv := mvalues)
)).
   2 : assumption.
   2 : rewrite <- H32; assumption.
   2 : eauto.
   2 : omega.
   2: assert (Object.arraysize o * size t1 <= Memory.block_size memop mblocks x) by eauto; rewrite <- H28; omega.
intro.
match type of x3 with ?x <> None => case_eq x ; try congruence end.
clear x3.
intros.
       esplit.
       split.
       eapply plus_left.
       econstructor.
       eassumption.
       eassumption.
       assumption.
       simpl in H28.
       unfold valdata in H28.
       simpl.
       unfold typ_data in H28.
       simpl.
       simpl in H43.
       unfold valdata in H43.
       rewrite H28.
       eassumption.
       eleft.
       rewrite E0_right; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; eauto.
       intros.
       destruct (invariant_vars0 _ _ H44).
       destruct H45.
       eauto using match_values_update.
       generalize invariant_stack0.
       eapply bilist_imp with (R := fun _ => True).
       tauto.
       intros; eauto using match_frames_update.
       trivial.
       intros.
       destruct (
         cfield_dec
          (obj, ar, i, (h, p), fs)
          (obj0, ar0, i0, (h0, p0), fs0)
       ).
        congruence.
       erewrite Globals.get_put_field_other in H44.
       2 : eassumption.
       eauto.
       assumption.

(** memory : fields *)
intros.
destruct (
  cfield_dec
  (obj, ar, i, (h, p), fs)
  (obj0, ar0, i0, (h0, p0), fs0)
).
 injection e; intros; subst.
 replace o0 with o in * by congruence.
 assert (through = real /\ class = from).
  inversion H45; subst.
  inversion H17; subst.
  generalize (valid_array_path_last H54 H58).
  generalize (path_last H57).
  generalize (path_last H61).
  split; congruence.
 destruct H54; subst.
 replace off with x0 in * by congruence.
 replace foff with z in * by congruence.
 replace ty with t0 in * by congruence.
 replace oh with x in * by congruence.
 esplit.
 split.
  eapply Memory.load_store_same.
  eassumption.
  simpl in H28, H43.
  rewrite <- H28 in H43.
  eassumption.
 eapply match_values_update.
 reflexivity.
 erewrite Globals.get_put_field_same in H49.
 2 : eassumption.
 congruence.
erewrite Globals.get_put_field_other in H49.
2 : eassumption.
2 : assumption.
destruct (invariant_fields0
_ _ H44 _ _ _ _ _ _ H45 _ H46 _ H47 _ H48 _ H49 _ H50 _ H51 _ H52 _ H53).
destruct H54.
erewrite Memory.load_store_other.
2 : eassumption.
2 :   simpl in H28, H43; rewrite <- H28 in H43; eassumption.
eauto using match_values_update.
destruct (peq obj0 obj).
 subst.
 right.
 replace o0 with o in * by congruence.
 assert (
   (ar, i, (h, p), fs) <> (ar0, i0, (h0, p0), fs0)
 ) by (unfold ident in *; congruence).
 generalize (scalar_fields_disjoint (** POPL 2011 *)
Hhier intro guard H17 H45 H5 H51 H21 H52 H22 H23 H53 H48 H56).
 simpl.
 unfold typ_data.
 omega.
(** different objects: OK thanks to simplified memory model *) eauto.

(** memory: dynamic type data *)
intros.
erewrite Memory.load_store_other; eauto.
destruct (peq obj0 obj).
 subst.
 right.
 replace o0 with o in * by congruence.
 assert (offsets ! from <> None).
  inversion H45; subst; eauto using path_defined_to.
 generalize (scalar_field_dynamic_type_data_disjoint
Hhier intro guard H17 H45 H5 H49 H21 H50 H22 H23 H46).
 simpl.
 simpl in H28.
 rewrite <- H28.
 unfold typ_data.
 omega.
left; eauto.

Qed.  

Lemma primary_vtable_access_le : forall l, is_primary_path offsets l = true -> forall x2 x3, l = x2 :: x3 -> forall from, last l = Some from ->
  vtable_access_le (romty:=romty A)
  (Target.vtable_access_sharing (Target.rom prog')) from x2
.
Proof.
  intro l.
  functional induction (is_primary_path offsets l); try (intro; discriminate).
   intros _.
   injection 1; intros until 2; subst.
   injection 1; intros; subst.
   eapply Relations.Relation_Operators.rt_refl.
  injection 2; intros until 2; subst.
  change (last (x2 :: a' :: _x)) with (last (a' :: _x)).
  intros.
  generalize (IHb H _ _ (refl_equal _) _ H1).
  intro.
  eapply Relations.Relation_Operators.rt_trans with a'.
  eauto.
  eapply Relations.Relation_Operators.rt_step.
  unfold vtable_access_prec.
  simpl.
  unfold vtable_access_sharing.
  rewrite e1.
  assumption.
Qed.

Lemma preservation_static_cast : forall from to source target stl vars stack global dt,
  Interm.State (statcast A nativeop from to source target) stl vars stack (Global global dt) = st1 ->
  goal.
Proof.
       intros; subst.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       destruct memory; simpl in *.
       Opaque concat Globals.get_field Globals.put_field.
       inversion H; simpl in *; subst; simpl in *.
       destruct (invariant_vars0 _ _ H10).
       destruct H0.
       inversion H1; subst.
       destruct (H9 _ H12 _ _ H13).
       invall; subst.
       inversion H13; subst.
       functional inversion H4; subst.
       unfold compile_statcast.
       destruct (peq from to).

(** same class (identity cast) *)
        subst.
        assert (path hierarchy to (to :: nil) to Class.Inheritance.Repeated).
         eleft with (lt := nil).
         reflexivity.
         reflexivity.
         simpl.
         generalize (path_defined_to H7).
         case_eq (hierarchy ! to); congruence.
        assert (
          (h', p') = (h, p)
        ).
         inversion H14; subst.
         generalize (H21 _ _ H15).
         injection 1; intros; subst.
         erewrite concat_trivial_right in H22.
         assumption.
         eassumption.
        generalize (H21 _ H15).
        intro; subst.
        erewrite concat_trivial_right in H22.
        congruence.
        eassumption.
       injection H19; intros; subst.
       replace hp' with hp in * by eauto using is_some_eq.
       esplit.
       split.
        eapply plus_left.
        econstructor.
        eassumption.
        reflexivity.
        eleft.
               rewrite E0_right; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; eauto.
       intro.
       destruct (peq target v).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intro; subst; eauto.
       repeat rewrite PTree.gso; eauto.
       congruence.

(** different classes *)
destruct (
  Well_formed_hierarchy.paths Hhier 
).
destruct a.
destruct (plt from to).

(** cast to derived non-virtual *)
inversion H14; subst.
 generalize (Well_formed_hierarchy.path_le Hhier H21).
 intro.
 destruct (Plt_irrefl _ (Plt_Ple_trans _ _ _ p0 H24)).
assert (x0 ! from <> None) by eauto using path_defined_to.
case_eq (x0 ! from); try congruence.
intros.
destruct (H19 _ _ H25).
assert (t ! to <> None) by eauto using path_defined_to.
case_eq (t ! to); try congruence.
intros.
generalize (H27 _ _ H29).
intro.
case_eq (filter repeated_criterion l).
 intro.
 assert (In (Class.Inheritance.Repeated, p1) (filter repeated_criterion l)).
  eapply filter_In.
  split.
  eapply H30.
  assumption.
  reflexivity.
 rewrite H31 in H32.
 destruct H32.
intros.
assert (In p2 (filter repeated_criterion l)).
 rewrite H31; eauto.
destruct (let (K, _) := filter_In _ _ _ in K H32).
functional inversion H34; subst.
generalize (let (K, _) := H30 _ in K H33).
intro.
generalize (H22 _ H35).
intro; subst.
generalize (non_virtual_subobject_offset_exist
Hhier intro (fun ci _ => @exis ci) (Plt_succ _) H35 (accu := 0)).
case_eq (non_virtual_subobject_offset offsets 0 p1); try congruence.
intros until 1.
intros _.
functional inversion H18; subst.
replace o0 with ofto in * by congruence.
inversion H21; subst.
Transparent concat. simpl in H23.
rewrite (path_last H20) in H23.
destruct (peq to to); try congruence.
injection H23; intros; subst.
generalize (last_correct (path_last H20)).
destruct 1.
subst.
rewrite app_ass in H39.
simpl in H39.
rewrite H39 in H37.
destruct (non_virtual_subobject_offset_app_recip H37).
destruct H43.
rewrite (non_virtual_subobject_offset_rewrite H36) in H44.
injection H44; intro; subst.
esplit.
split.
eapply plus_left.
econstructor.
eassumption.
reflexivity.
eleft.
       rewrite E0_right; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; eauto.
       intros ? ?.
       destruct (peq target v).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intros; subst.
        esplit.
        split.
         reflexivity.
        econstructor.
        assumption.
        rewrite H12.
        injection 1; intro; subst.
        inversion 1; subst.
        generalize (valid_array_path_last H2 H48).
        intro; subst.
        esplit.
        split.
         eassumption.
        unfold relative_pointer_offset.
        rewrite H16.
        rewrite H17.
        unfold subobject_offset.
        rewrite H17.
        assert (exists g, x1 ++ to :: nil = b :: g).
         destruct x1; injection H39; intros; subst; simpl in *; eauto. 
        destruct H52.
        rewrite H52.
        rewrite H41.
        rewrite <- H52.
        rewrite H43.
        esplit.
        split.
         reflexivity.
        f_equal.
        f_equal.
        omega.
       repeat rewrite PTree.gso; eauto; congruence.

(** cast to base *)
inversion H14; subst.
 assert (x0 ! to <> None) by eauto using path_defined_to.
 case_eq (x0 ! to); try congruence.
 intros.
 destruct (H19 _ _ H25).
 assert (t ! from <> None) by eauto using path_defined_from.
 case_eq (t ! from); try congruence.
 intros.
 generalize (H27 _ _ H29).
 intro.
 destruct l.
  destruct (let (_, K) := H30 (_, _) in K H21).
 destruct p1.
 generalize (let (K, _) := H30 (_, _) in K (or_introl _ (refl_equal _))).
 intro.
 generalize (H22 _ _ H31).
 injection 1; intros; subst.
 generalize (path_path1 H21).
  inversion 1; subst.
  (** non-virtual *)
   generalize (non_virtual_subobject_offset_exist
   Hhier intro (fun ci _ => @exis ci) (Plt_succ _) H21 (accu := 0)).
   case_eq (non_virtual_subobject_offset offsets 0 (from :: lf)); try congruence.
   intros until 1.
   intros _.
   simpl in H23.
   rewrite (path_last H7) in H23.
   destruct (peq from from); try congruence.
   functional inversion H18; subst.
   replace o0 with ofto in * by congruence.
   destruct (last_correct (path_last H7)).
   generalize H23.
   rewrite e0 in H23.
   simpl.
   injection 1; intros; subst.
   injection H23; intros.
   esplit.
   split.
   eapply plus_left.
   econstructor.
   eassumption.
   reflexivity.
   eleft.
       rewrite E0_right; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; eauto.
       intros ? ?.
       destruct (peq target v).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intros; subst.
        esplit.
        split.
         reflexivity.
        econstructor.
        assumption.
        rewrite H12.
        injection 1; intro; subst.
        inversion 1; subst.       
        generalize (valid_array_path_last H2 H45).
        intro; subst.
        esplit.
        split.
         eassumption.
        unfold relative_pointer_offset.
        rewrite H16.
        rewrite H17.
        unfold subobject_offset.
        rewrite H17.
        rewrite H41.
        rewrite H40.
        rewrite app_ass; simpl.
        rewrite e0 in H37.
        rewrite (non_virtual_subobject_offset_app H37).
        rewrite (non_virtual_subobject_offset_rewrite H34).
        esplit.
        split.
        reflexivity.
        f_equal.
        f_equal.
        omega.
       repeat rewrite PTree.gso; eauto; congruence.
      (** virtual *)
      inversion H35; subst.
      generalize (non_virtual_subobject_offset_exist 
        Hhier intro (fun ci _ => @exis ci) (Plt_succ _) H35 (accu := 0)).
      case_eq (non_virtual_subobject_offset offsets 0 (base :: lf)); try congruence.
      intros until 1.
      intros _.
      assert (is_dynamic hierarchy from) by eauto using is_dynamic_virtual_base.
      case_eq (assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (h, p))) dt); try congruence. (** RIGHT to get virtual base *)
      intros.
      destruct p0.
      destruct p0.
      destruct p1.
      destruct (
        invariant_dynamic_type0 _ _ H12
_ _ _ _ _ _ H13 H39 _ _ _ _ H40).
      destruct H41.
      destruct H42.
      destruct (reduce_path_prefix offsets Hhier H42).
      invall.      
      destruct (vboffsets_l_complete Hhier intro exis H41 H42 H43 H18 H34).
      invall.
      replace x4 with ofto in * by congruence.
      case_eq (Zsem sem (x5 - z2)).
      intros.

      esplit.
      split.
      eapply plus_left.
      econstructor.
      eright.
      econstructor.
      eassumption.
      replace (
        z1 + i * size ofto + z2 + 0
      ) with (
        z1 + i * size ofto + z2
      ) by omega.
      erewrite invariant_vptr0.
      reflexivity.
      eassumption.
      eassumption.
      assumption.
      eassumption.
      assumption.
      assumption.
      reflexivity.
      eright.
      econstructor.
      eright.
      econstructor.
      eright.
      econstructor.
      rewrite PTree.gss.
      eauto.
      econstructor.
      simpl.
      eapply map_all_pvtable_complete.
      eassumption.
      eassumption.
      erewrite reduce_path_idem.
      reflexivity.
      eassumption.
      eauto using path_nonempty.
      eauto using is_dynamic_path.
      Opaque vboffsets_l. simpl.
      eassumption.
      eassumption.
      simpl.
      eauto using path_last.
      eauto using primary_vtable_access_le, path_last.
     simpl.
     unfold vtable_access_VBase.     
     destruct (vborder_list_ex Hhier from).
     destruct s.
     destruct e.
     destruct H52.
     eauto using virtual_base_vborder_list.
    generalize (path_defined_to H45).
    intro; contradiction.
    reflexivity.
    eright.
    econstructor.
    eright.
    econstructor.
    eright.
    econstructor.
    rewrite PTree.gso.
    rewrite PTree.gso.
    eassumption.
    congruence.
    congruence.
    rewrite PTree.gss.
    reflexivity.
    eauto using Zsem_semZ.
    replace (
      (x5 - z2) * 1
    ) with (
      x5 - z2
    ) by ring.
    reflexivity.
    eright.
    econstructor.
    eright.
    econstructor.
    rewrite PTree.gss.
    reflexivity.
    reflexivity.
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
    exists objmap lo.
    split; simpl; eauto.
    intro.
    destruct (peq target v0).
     subst v0.
     repeat rewrite PTree.gss.
     injection 1; intro; subst vr.
     esplit.
     split.
     reflexivity.
    econstructor.
    assumption.
    rewrite H12.
    injection 1; intro; subst o0.
    inversion 1.
     generalize (valid_array_path_last H2 H55).
     intro; subst ato.
     esplit.
     split.
     eassumption.
     unfold relative_pointer_offset.
     rewrite H16.
     rewrite H17.
     unfold subobject_offset.
     rewrite H17.
     simpl in H23.
     injection H23; intros; subst h' p'.
     rewrite H50.
     rewrite (non_virtual_subobject_offset_rewrite H36).
     esplit.
     split.
     reflexivity.
     f_equal.
     f_equal.
     omega.
    repeat rewrite PTree.gso; eauto; congruence.

(** absurd case: cast to derived *)
generalize (Well_formed_hierarchy.path_le Hhier H21).
intro.
assert (Zpos from <> Zpos to) by congruence.
unfold Plt, Ple in n0, H24.
omegaContradiction.

Qed.

Lemma preservation_dynamic_cast : forall from to source target stl vars stack global dt,
  Interm.State (Interm.dyncast A nativeop from to source target) stl vars stack (Global global dt) = st1 ->
  goal.
Proof.
       intros; subst.
       Opaque concat Globals.get_field Globals.put_field.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       destruct memory; simpl in *.
       inversion H; simpl in *; subst; simpl in *.
       destruct (invariant_vars0 _ _ H8).
       destruct H0.
       inversion H1; subst.
       inversion H9; subst.
       destruct (H11 _ H4 _ _ H19).
       invall; subst.
       inversion H19; subst.
       functional inversion H5; subst.
       generalize (path_last H20).
       intros.
       replace to0 with from in * by congruence.
       destruct (invariant_dynamic_type0 _ _ H4 _ _ _ _ _ _ H19 H15 _ _ _ _ H12).
       invall.
       generalize (path_last H26).
       intros.
       replace x0 with real in * by congruence.
       destruct (reduce_path_prefix offsets Hhier H25).
       invall.
       destruct (dyncast_offset_l_reduce_path
          Hhier intro guard exis H18 H25 H26).
       destruct (Well_formed_hierarchy.dynamic_cast_dec
Hhier real h1 p1 from to).

(** success *)
destruct s.
destruct s.
destruct (H16 _ _ d).
invall; subst newptr.
destruct (H32 _ _ d _ _ H28 _ H24 _ _ H35).
destruct H36.
assert ( Atom (A:=A) (romty A) mblock (ty:=tyTRUE sem) (TRUE sem) =  match
     assoc (DCast_eq_dec (Target.rom prog')) to
       (dyncast
          (vtable Hhier (COP:=COP) (vop':=vop') (vop'_pos:=vop'_pos) intro
             guard exis compile_method_name
             (through, (h0, p0), (h1, reduce_path (A:=A) offsets p1))))
   with
   | Some _ => Atom (A:=A) (romty A) mblock (ty:=tyTRUE sem) (TRUE sem)
   | None => Atom (A:=A) (romty A) mblock (ty:=tyFALSE sem) (FALSE sem)
   end
).
case_eq (
assoc (DCast_eq_dec (Target.rom prog')) to
       (dyncast
          (vtable Hhier (COP:=COP) (vop':=vop') (vop'_pos:=vop'_pos) intro
             guard exis compile_method_name
             (through, (h0, p0), (h1, reduce_path (A:=A) offsets p1))))
).
 trivial.
intro.
match type of H37 with ?x = _ =>
  match type of H38 with ?y = _ =>
    assert (x = y)
  end
end.
 reflexivity.
congruence.
case_eq (Zsem sem (x8 - z2)).
intros.
esplit.
split.
eapply plus_left.
econstructor.
eright.
econstructor.
eassumption.
replace (
z1 + i * size ofto + z2 + 0
) with (
z1 + i * size ofto + z2
) by omega.
erewrite invariant_vptr0.
reflexivity.
eassumption.
eassumption.
assumption.
eassumption.
assumption.
assumption.
reflexivity.
eright.
econstructor.
eright.
econstructor.
eright.
econstructor.
rewrite PTree.gss.
eauto.
econstructor.
simpl.
eapply map_all_pvtable_complete.
eassumption.
eassumption.
erewrite reduce_path_idem.
reflexivity.
eassumption.
eauto using path_nonempty.
eauto using is_dynamic_path.
eassumption. (** AND NOT reflexivity *)
reflexivity.
eright.
econstructor.
eright.
econstructor.
rewrite PTree.gss.
reflexivity.
eauto using semTRUE.
simpl. reflexivity.
eright.
econstructor.
eright.
econstructor.
rewrite PTree.gso.
rewrite PTree.gss.
eauto.
congruence.
econstructor.
simpl.
eapply map_all_pvtable_complete.
eassumption.
eassumption.
erewrite reduce_path_idem.
reflexivity.
eassumption.
eauto using path_nonempty.
eauto using is_dynamic_path.
eassumption.
eassumption.
reflexivity.
eright.
econstructor.
eright.
econstructor.
rewrite PTree.gso.
rewrite PTree.gso.
rewrite PTree.gso.
eassumption.
congruence.
congruence.
congruence.
rewrite PTree.gss.
reflexivity.
eauto using Zsem_semZ.
replace ( z1 + i * size ofto + z2 + (x8 - z2) * 1
) with ( z1 + i * size ofto + z2 + (x8 - z2) 
) by ring.
reflexivity.
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
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
exists objmap lo.
split; simpl; eauto.
intro.
destruct (peq target v0).
 subst v0.
 repeat rewrite PTree.gss.
 injection 1; intro; subst vr.
 esplit.
 split.
 reflexivity.
 econstructor.
 assumption.
 rewrite H4.
 injection 1; intro; subst o0.
 inversion 1.
 generalize (valid_array_path_last H2 H43).
 intro; subst ato.
 esplit.
 split.
 eassumption.
 unfold relative_pointer_offset.
 rewrite H22.
 rewrite H23.
 rewrite H36.
 esplit.
 split.
 reflexivity.
 f_equal.
 f_equal.
 omega.
 repeat rewrite PTree.gso; eauto; congruence.

(** failure *)
generalize (H34 f).
intro.
generalize (H17 f).
intro; subst newptr.
assert (
     assoc (DCast_eq_dec (Target.rom prog')) to
       (dyncast
          (vtable Hhier (COP:=COP) (vop':=vop') (vop'_pos:=vop'_pos) intro
             guard exis compile_method_name
             (through, (h0, p0), (h1, reduce_path (A:=A) offsets p1)))) = None
) by assumption.
esplit.
split.
eapply plus_left.
econstructor.
eright.
econstructor.
eassumption.
erewrite invariant_vptr0.
reflexivity.
eassumption.
eassumption.
assumption.
eassumption.
assumption.
replace (
  z1 + i * size ofto + z2 + 0
) with (
z1 + i * size ofto + z2
) by omega.
assumption.
reflexivity.
eright.
econstructor.
eright.
econstructor.
eright.
econstructor.
rewrite PTree.gss.
eauto.
econstructor.
simpl.
eapply map_all_pvtable_complete.
eassumption.
eassumption.
erewrite reduce_path_idem.
reflexivity.
eassumption.
eauto using path_nonempty.
eauto using is_dynamic_path.
rewrite H36.
reflexivity.
reflexivity.
eright.
econstructor.
eright.
econstructor.
rewrite PTree.gss.
reflexivity.
eauto using semFALSE.
simpl.
reflexivity.
eright.
econstructor.
reflexivity.
eleft.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
exists objmap lo.
split; simpl; eauto.
intro.
destruct (peq target v).
 subst v.
 repeat rewrite PTree.gss.
 injection 1; intro; subst vr.
 esplit.
 split.
 reflexivity.
 econstructor.
repeat rewrite PTree.gso; eauto; congruence.
Qed.

Lemma preservation_invoke : forall source from ms vargs vres stl vars0 stack global dt,
Interm.State (invoke nativeop source from ms vargs vres) stl vars0
          stack (Global global dt) = st1
->
  goal.
Proof.
       intros; subst.
       Opaque concat Globals.get_field Globals.put_field.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       destruct memory; simpl in *.
       inversion H; simpl in *; subst; simpl in *.
       destruct (invariant_vars0 _ _ H9).
       destruct H0.
       inversion H1; subst.
       inversion H11; subst.
       destruct (H15 _ H4 _ _ H16).
       invall; subst.
       inversion H16; subst.
       functional inversion H5; subst.
       replace to with from in * by (generalize (path_last H24); intro; congruence).       
       inversion H14; subst.
       assert (is_dynamic hierarchy from) by
         (eauto 8 using is_dynamic_path, is_dynamic_virtual_methods, Method.find_in).
       destruct (invariant_dynamic_type0 _ _ H4 _ _ _ _ _ _ H16 H34 _ _ _ _ H10).
       invall.
       replace x0 with real in * by (generalize (path_last H36); congruence).
       destruct (reduce_path_prefix offsets Hhier H35).
       invall.
       destruct (dispfunc_l_reduce_path
Hhier intro guard compile_method_name H14 H12 through h0).
       invall.
       replace x3 with mcn in * by congruence.
       inversion H32.
       replace dispatched with mcn in * by (generalize (path_last H50); congruence).
       replace dispatched_body with mc in * by congruence.
       destruct (dispoff_l_reduce_path
         Hhier intro guard exis H14 H36 H38 H28 H23).
       destruct H55.
       destruct mb.
       assert (compile_method_name mcn ms = NONSTATIC mcd).
        unfold compile_method_name.
        rewrite H18.
        rewrite H19.
        rewrite H20.
        reflexivity.


unfold compile_invoke.
case_eq (use_thunks (invoke nativeop source from ms vargs vres)).

(** thunkcall *)
intros.
destruct (set_params_exist invariant_vars0 H22).
destruct H59.
esplit.
split.
eapply plus_left.
econstructor.
eauto using Htsp_thunks'.
eassumption.
erewrite invariant_vptr0.
reflexivity.
eassumption.
eassumption.
assumption.
eassumption.
assumption.
assumption.
simpl.
eapply map_all_pvtable_complete.
eassumption.
eassumption.
erewrite reduce_path_idem.
reflexivity.
eassumption.
eauto using path_nonempty.
eauto using is_dynamic_path.
eassumption.
eassumption.
simpl.
rewrite ptree_to_ptree_other.
erewrite ptree_to_ptree_some.
reflexivity.
unfold f_compile_method.
intros; left; congruence.
eassumption.
unfold f_compile_method.
rewrite H57.
simpl.
reflexivity.
unfold f_compile_static.
rewrite H57.
congruence.
simpl.
eauto using path_last.
eauto using primary_vtable_access_le, path_last.
simpl.
eapply virtual_functions_complete.
4 : eassumption.
3 : eassumption.
2 : eassumption.
eassumption.
eassumption.
Transparent set_params.
simpl; reflexivity.
Opaque set_params.
eleft.
repeat rewrite E0_left; eauto using evtr_sem.
exists objmap lo.
split; simpl; eauto.
Transparent Interm.set_params.
simpl.
Opaque Interm.set_params.
intro.
destruct (peq mthis v).
 subst v.
 repeat rewrite PTree.gss.
 injection 1; intro; subst vr.
 esplit.
 split.
 reflexivity.
 econstructor.
 assumption.
 rewrite H4.
 injection 1; intro; subst o0.
 inversion 1.
 generalize (valid_array_path_last H2 H64).
 intro; subst ato.
 esplit.
 split.
  eassumption.
 unfold relative_pointer_offset.
 rewrite H26.
 rewrite H27.
 rewrite H55.
 esplit.
 split.
 reflexivity.
 f_equal.
 f_equal.
 omega.
repeat rewrite PTree.gso; eauto; congruence.
econstructor; eauto.
econstructor; eauto.

(** call-site adjustment *)
intros.
       case_eq (Zsem sem (x4 - z2)).
       intros.
       refine (_ (set_params_exist (gl := global) (objmap := objmap)
 (vars0 :=     (PTree.set 3 (Fptr A (romty A) mblock (compile_method_name mcn ms))
       (PTree.set 7
          (Ptr A (romty A)
             (Some (x, z1 + i * size ofto + z2 + (x4 - z2) * 1)))
          (PTree.set 7 (Atom (A:=A) (romty A) mblock (ty:=x5) v)
             (PTree.set 3
                (Vptr A (romty:=romty A) mblock
                   (through, (h0, p0), (h1, reduce_path (A:=A) offsets p1)))
                vars))))) _ H22)).
       destruct 1.
       destruct H60.
esplit.
split.
eapply plus_left.
econstructor.
eright.
econstructor.
eassumption.
erewrite invariant_vptr0.
reflexivity.
eassumption.
eassumption.
assumption.
eassumption.
assumption.
replace (
z1 + i * size ofto + z2 + 0
) with (z1 + i * size ofto + z2 
) by omega.
assumption.
reflexivity.
eright.
econstructor.
eright.
econstructor.
eright.
econstructor.
rewrite PTree.gss.
eauto.
econstructor.
simpl.
eapply map_all_pvtable_complete.
eassumption.
eassumption.
erewrite reduce_path_idem.
reflexivity.
eassumption.
eauto using path_nonempty.
eauto using is_dynamic_path.
eassumption.
simpl.
eauto using path_last.
eauto using primary_vtable_access_le, path_last.
simpl.
eapply virtual_functions_complete.
4 : eassumption.
3 : eassumption.
2 : eassumption.
eassumption.
eassumption.
reflexivity.
eright.
econstructor.
eright.
econstructor.
eright.
econstructor.
rewrite PTree.gso.
rewrite PTree.gso.
eassumption.
congruence.
congruence.
rewrite PTree.gss.
reflexivity.
eauto using Zsem_semZ.
reflexivity.
eright.
econstructor.
eright.
econstructor.
eright.
econstructor.
rewrite PTree.gso.
rewrite PTree.gso.
rewrite PTree.gss.
eauto.
congruence.
congruence.
econstructor.
simpl.
eapply map_all_pvtable_complete.
eassumption.
eassumption.
erewrite reduce_path_idem.
reflexivity.
eassumption.
eauto using path_nonempty.
eauto using is_dynamic_path.
eassumption.
simpl.
eauto using path_last.
eauto using primary_vtable_access_le, path_last.
simpl.
eapply virtual_functions_complete.
4 : eassumption.
3 : eassumption.
2 : eassumption.
eassumption.
reflexivity.
eright.
econstructor.
eright.
eapply step_call with (args := _ :: _).
split.
rewrite PTree.gss.
rewrite H57.
reflexivity.
eauto using Htsp_function_pointers'.
simpl.
rewrite ptree_to_ptree_other.
erewrite ptree_to_ptree_some.
reflexivity.
unfold f_compile_method.
intros; left; congruence.
eassumption.
unfold f_compile_method.
simpl.
reflexivity.
unfold f_compile_static.
congruence.
simpl.
f_equal.
2 : symmetry.
2 : rewrite PTree.gso.
2 : rewrite PTree.gss.
2 : reflexivity.
2 : congruence.
2 : eassumption.
congruence.
reflexivity.
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
reflexivity.
reflexivity.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
exists objmap lo.
split; simpl; eauto.
Transparent Interm.set_params Target.set_params.
simpl.
Opaque Interm.set_params Target.set_params.
intro.
destruct (peq mthis v0).
 subst v0.
 repeat rewrite PTree.gss.
 injection 1; intro; subst vr.
 esplit.
 split.
 reflexivity.
 econstructor.
 assumption.
 rewrite H4.
 injection 1; intro; subst o0.
 inversion 1.
 generalize (valid_array_path_last H2 H65).
 intro; subst ato.
 esplit.
 split.
  eassumption.
 unfold relative_pointer_offset.
 rewrite H26.
 rewrite H27.
 rewrite H55.
 esplit.
 split.
 reflexivity.
 f_equal.
 f_equal.
 omega.
repeat rewrite PTree.gso; eauto; congruence.
econstructor; eauto.
econstructor; eauto.
intros.
repeat rewrite PTree.gso; eauto; congruence.
intros.
repeat rewrite PTree.gso; eauto; congruence.
Qed.

Lemma preservation_array_index : forall class index source target stl vars stack global dt,
  Interm.State (arrayindex A nativeop class index source target) stl vars stack (Global global dt) = st1 ->
  goal.
Proof.
       intros; subst.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       destruct memory; simpl in *.
       Opaque concat Globals.get_field Globals.put_field.
       inversion H; simpl in *; subst; simpl in *.
       assert (hierarchy ! class <> None) by eauto using Well_formed_hierarchy.array_path_valid.
       assert (path hierarchy class (class :: nil) class Class.Inheritance.Repeated).
       eleft with (lt := nil).
       reflexivity.
       reflexivity.
       simpl.
       case_eq (hierarchy ! class); congruence.
      assert (
        valid_relative_pointer hierarchy (Object.class o) (Object.arraysize o) ar class i Class.Inheritance.Repeated (class :: nil) class
      ) by (econstructor; invall; eauto).
      destruct (invariant_vars0 _ _ H10).
       destruct H3.
       inversion H4; subst.       
       destruct (H19 _ H11 _ _ H2).
       invall; subst.
       functional inversion H7; subst.
       generalize H21.
       unfold subobject_offset.
       rewrite H20.
       rewrite (virtual_base_offsets_self (intro H20)).
       simpl.
       injection 1; intro; subst.
       destruct (invariant_vars0 _ _ H14).
       destruct H22.
       inversion H23; subst.
       generalize (inj_pair2_eq_dec _ (ATOM.ty_eq_dec (t := A)) _ _ _  _  H26).
       intro; subst.
esplit.
split.
eapply plus_left.
econstructor.
eassumption.
eassumption.
eassumption.
reflexivity.
eleft.
       rewrite E0_right; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; eauto.
       intro.
       destruct (peq target v).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intro; subst.
        esplit.
        split.
         reflexivity.
        econstructor.
        assumption.
        rewrite H11.
        injection 1; intro; subst.
        inversion 1; subst.
        generalize (valid_array_path_last H28 H12).
        intro; subst.
        generalize (path_last H31).
        injection 1; intro; subst.
        esplit.
        split.
        eassumption.
        unfold relative_pointer_offset.
        rewrite H13.
        rewrite H20.
        rewrite H21.
        esplit.
        split.
        reflexivity.
        f_equal.
        f_equal.
        ring.
       repeat rewrite PTree.gso; eauto.
       congruence.
Qed.

Lemma is_dynamic_defined : forall d, is_dynamic hierarchy d -> hierarchy ! d <> None.
Proof.
  inversion 1; congruence.
Qed.
  
Lemma preservation_rootpath : forall cn ovar target stl vars stack global,
  Interm.State (pathop A nativeop (rootpath cn) ovar target) stl vars stack global = st1 ->
  goal.
Proof.
       intros; subst.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       Opaque concat Globals.get_field Globals.put_field.
       inversion H; simpl in *; subst; simpl in *.
       inversion H9; subst.
       destruct (is_dynamic_dec Hhier cn).

(** dynamic *)
esplit.
split.
eapply plus_left.
econstructor.
reflexivity.
econstructor.
simpl.
eapply init_pvtt_complete.
assumption.
reflexivity.
eleft.
       rewrite E0_right; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; eauto.
       intro.
       destruct (peq target v).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intro; subst.
        esplit.
        split.
         reflexivity.
        econstructor.
        reflexivity.
       repeat rewrite PTree.gso; eauto.
       congruence.

       (** non dynamic : dummy value *)
       esplit.
       split.
       eapply plus_left.
       econstructor.
       reflexivity.
       eleft.
       rewrite E0_right; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; eauto.
       intro.
       destruct (peq target v).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intro; subst.
        esplit.
        split.
         reflexivity.
        econstructor.
        intros until 1.
        generalize (path_last H1).
        injection 1; intros; subst; contradiction.
       repeat rewrite PTree.gso; eauto.
       congruence.
Qed.

Lemma preservation_addbase : forall i t0 cn ovar target stl vars stack global,  
  Interm.State (pathop A nativeop (addbase i t0 cn) ovar target) stl vars stack global = st1 ->
  goal.
Proof.
       intros; subst.
       Opaque concat Globals.get_field Globals.put_field.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       inversion H; simpl in *; subst; simpl in *.
       inversion H9; subst.
       destruct ovar; try congruence.
       invall.
       injection H2; intro; subst.
       destruct (invariant_vars0 _ _ H1).
       destruct H0.
       inversion H4; subst.
       destruct (is_dynamic_dec Hhier cn).

(** dynamic *)
assert (hierarchy ! cn <> None) by eauto using is_dynamic_defined.
assert (path hierarchy cn (cn :: nil) cn Class.Inheritance.Repeated).
eleft with (lt := nil); try reflexivity.
simpl; case_eq (hierarchy ! cn); congruence.
destruct t0.

(** non-virtual  *)
invall.
assert (is_dynamic hierarchy i) by eauto using is_dynamic_base.
generalize (H12 _ H3 H10).
intro; subst.
esplit.
split.
eapply plus_left.
econstructor; simpl.
rewrite H0.
eauto.
rewrite H0.
econstructor.
simpl.
eapply map_all_pvtt_complete.
eassumption.
assumption.
Opaque sub_pvtt.
simpl.
erewrite sub_pvtt_non_virtual_complete.
reflexivity.
eassumption.
assumption.
eassumption.
assumption.
simpl.
eauto using path_last.
reflexivity.
eleft.
       rewrite E0_right; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; eauto.
       intro.
       destruct (peq target v).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intro; subst.
        esplit.
        split.
         reflexivity.
        econstructor.
        intros.
        congruence.
       repeat rewrite PTree.gso; eauto.
       congruence.

(** virtual  *)
invall.
assert (is_dynamic hierarchy i) by eauto using is_dynamic_virtual_base.
injection H10; intro; subst.
generalize (path_last H3).
injection 1; intros; subst.
generalize (H12 _ H3 H7).
intro; subst.
esplit.
split.
eapply plus_left.
econstructor; simpl.
rewrite H0.
eauto.
rewrite H0.
econstructor.
simpl.
eapply map_all_pvtt_complete.
eassumption.
assumption.
Opaque sub_pvtt.
simpl.
erewrite sub_pvtt_virtual_complete.
reflexivity.
eassumption.
assumption.
eassumption.
reflexivity.
eleft.
       rewrite E0_right; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; eauto.
       intro.
       destruct (peq target v).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intro; subst.
        esplit.
        split.
         reflexivity.
        econstructor.
        intros.
        congruence.
       repeat rewrite PTree.gso; eauto.
       congruence.

       (** non dynamic : dummy value *)
       esplit.
       split.
       eapply plus_left.
       econstructor.
       reflexivity.
       eleft.
       rewrite E0_right; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; eauto.
       intro.
       destruct (peq target v).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intro; subst.
        esplit.
        split.
         reflexivity.
        econstructor.
        intros until 1.
        generalize (path_last H8).
        destruct t0;
         injection H6; intros until 2; subst;
           try rewrite last_complete;
         injection 1; intros; subst; contradiction.
       repeat rewrite PTree.gso; eauto;
       congruence.
Qed.

Lemma list_concat_prefix_left : forall (U : Type) (lu1l lu1r lu2l lu2r : list U),
  lu1l ++ lu1r = lu2l ++ lu2r ->
  (length lu1l <= length lu2l)%nat ->
  exists l, lu2l = lu1l ++ l /\ lu1r = l ++ lu2r.
Proof.
  induction lu1l; simpl.
   intros; subst.
   esplit.
   split.
   reflexivity.
   reflexivity.
  destruct lu2l; simpl.
   intros; omegaContradiction.
  injection 1; intros; subst.
  assert (length lu1l <= length lu2l)%nat by omega.
  destruct (IHlu1l _ _ _ H0 H1).
  destruct H3.
  subst.
  eauto.
Qed. 

Lemma reduce_non_primary_path : forall hyperreal to0 h0 p0,
  path hierarchy to0 p0 hyperreal h0 ->
  forall to1 h1 p1, path hierarchy to1 p1 hyperreal h1 -> (
    forall h' p', path hierarchy to1 p' to0 h' ->
      (h1, p1) <> concat (h0, p0) (h', p')
  ) -> (
    (forall p'', is_primary_path offsets (to1 :: p'') = true -> (h0, p0) <> concat (h1, p1) (Class.Inheritance.Repeated, to1 :: p''))
  ) ->
  forall to2 h' p', path hierarchy to2 p' to0 h' ->
    forall h2 p2, (h2, p2) = concat (h0, p0) (h', p') ->
      reduce_path offsets p1 <> reduce_path offsets p2.
Proof.
  (** p1 and p2 are primary subobjects of the same object, so either is a primary base of the other *)
  intros.
  intro.
  destruct (reduce_path_prefix offsets Hhier H0).
  invall.
  generalize (path_concat H H3 H4).
  intro.
  generalize (reduce_path_prefix offsets Hhier H9).
  rewrite <- H5.
  clear H5.
  revert H6 H8.
  generalize (reduce_path offsets p1).
  intros; invall; subst.
  generalize (path_last H6).
  rewrite (path_last H11).
  injection 1; intros; subst.
  generalize (Well_formed_hierarchy.path_eq_hierarchy_eq Hhier H11 H6).
  intro; subst.
  clear H8 H11.
  destruct (le_lt_dec (length x2) (length x0)).
(** p1 is a base of p2, thus of p0 : absurd *)
   destruct (primary_path_prefix l0 H14 H10).
   subst.
   assert ((h1, l ++ x2 ++ x1) = concat (h1, l ++ x2) (Class.Inheritance.Repeated, to2 :: x1)).
    Transparent concat. simpl.
    rewrite (path_last H9).
    destruct (peq to2 to2); try congruence.
    rewrite app_ass; trivial.
   destruct (concat_repeated H0 (path_last H9) H8).
   destruct H12.
   clear H13.
   rewrite H4 in H8.
   rewrite concat_assoc in H8.
   case_eq (concat (h', p') (Class.Inheritance.Repeated, to2 :: x1)).
   intros.
   symmetry in H13.
   rewrite <- H13 in H8.
   generalize (path_concat H3 H12 H13).
   intro.
   eapply H1; eauto.
 (** p2 is a primary base of p1. *) 
 assert (length x0 <= length x2)%nat by omega.  
 destruct (primary_path_prefix H8 H10 H14).
 subst.
   generalize (path_path1 H3).
    inversion 1; subst.
    (** p2 is a non-virtual base of p0 *)
    simpl in H4.
    rewrite (path_last H) in H4.
    destruct (peq to0 to0); try congruence.
    injection H4; intros; subst.
    destruct (le_lt_dec (length p0) (length l)).
     (** (reduce_path p1) is a base of p0, thus p1 also, absurd. *)
     symmetry in H12.
     destruct (list_concat_prefix_left H12 l1).
     destruct H16.
     subst.
     assert ((h0, p0 ++ x2) = concat (h0, p0) (Class.Inheritance.Repeated, to0 :: x2)).
      simpl.
      rewrite (path_last H).
      destruct (peq to0 to0); congruence.
      destruct (concat_repeated H6 (path_last H) H16).
      destruct H18.
      clear H19.
      edestruct H1.
      eapply path_concat.
      eassumption.
      eassumption.
      Opaque last. simpl.
      rewrite (path_last H18).
      destruct (peq x x).
       reflexivity.
      destruct n.
      trivial.
      simpl.
      rewrite (path_last H).
      destruct (peq to0 to0); try congruence.
      rewrite app_ass; auto.
     (** p0 is a base of (reduce_path p1), so everything is a primary base of (reduce_path p1). *)
     assert (length l <= length p0)%nat by omega.
     destruct (list_concat_prefix_left H12 H16).
     destruct H17.
     subst.
     assert ((h0, l ++ x2) = concat (h0, l) (Class.Inheritance.Repeated, x :: x2)).
      simpl.
      rewrite (path_last H6).
      destruct (peq x x); congruence.
     destruct (concat_repeated H (path_last H6) H17).
     clear H19.
     destruct H20.
     clear H20.
     destruct (last_correct (path_last H19)).
     generalize H14.
     rewrite H18.
     change (x :: x2 ++ lf) with ((x :: x2) ++ lf).
     rewrite e0.
     rewrite app_ass.
     simpl.
     intro.
     generalize (primary_path_split_left Hhier H20).
     rewrite <- e0.
     intro.
     generalize (primary_path_split_right Hhier H20).
     intro.
     destruct (le_lt_dec (length x0) (length x2)).
       (** p0 is a primary base of p1 *)
       destruct (list_concat_prefix_left H18 l2).
       destruct H23; subst.
       change (x :: x0 ++ x4) with ((x :: x0) ++ x4) in H21.
       destruct (last_correct (path_last H7)).
       rewrite e1 in H21.
       rewrite app_ass in H21.
       simpl in H21.
       generalize (primary_path_split_right Hhier H21).
       intro.
       edestruct H2.
       eassumption.
       simpl.
       rewrite (path_last H0).
       destruct (peq to1 to1); try congruence.
       rewrite app_ass.
       reflexivity.
      (** p1 is a base of p0 *)
      assert (length x2 <= length x0)%nat by omega.
      symmetry in H18.
      destruct (list_concat_prefix_left H18 H23).
      destruct H24; subst.
      assert ((h0, l ++ x2 ++ x4) = concat (h0, l ++ x2) (Class.Inheritance.Repeated, to0 :: x4)).
       simpl.
       rewrite (path_last H).
       destruct (peq to0 to0); try congruence.
       rewrite app_ass.
       reflexivity.
      destruct (concat_repeated H0 (path_last H) H24).
      destruct H26.
      edestruct H1; eauto.
(** p2 is a virtual base of p0: as p2 and p1 are non-virtual bases of the same virtual base of p0, this is absurd. *)
simpl in H4.
injection H4; intros; subst.
generalize (path_path1 H6).
inversion 1; subst.
inversion H17; subst.
simpl in H13.
inversion H13; subst.
injection H18; intros; subst.
simpl in H0.
generalize (path_path1 H0).
inversion 1; subst.
inversion H25; intros; subst.
injection H26; intros; subst.
edestruct H1.
eright.
eassumption.
eassumption.
reflexivity.
Qed.


Lemma preservation_set_dynamic_type : forall ismostderived_flag from vptr vpath stl vars stack gl dt,
  Interm.State
  (setdyntype A nativeop ismostderived_flag from vptr vpath) stl vars stack (Global gl dt) = st1 ->
  goal.
Proof.
         intros; subst.
       Opaque concat Globals.get_field Globals.put_field.
       inversion Hstep; subst; simpl in *; try discriminate.
       destruct Hinv.
       destruct st2; simpl in *.
       destruct memory; simpl in *.
       inversion H; simpl in *; subst; simpl in *.
       destruct (invariant_vars0 _ _ H10).
       destruct H0.
       inversion H1; subst.
       destruct (H9 _ H11 _ _ H12).
       invall; subst. 
       destruct (invariant_vars0 _ _ H13).
       destruct H2.
       inversion H5; subst.
       inversion H12; subst.
       generalize (H18 _ H17).
       intros.
       assert (offsets ! (Object.class o) <> None) by eauto.
       case_eq (offsets ! (Object.class o)); try congruence.
       intros.
       assert (
         is_dynamic hierarchy from ->
         vars0 ! (vpath~0) =
         Some (VTTptr A (romty:=romty A) mblock (real, (h, p)))).
        intro.
        generalize (H19 H22).
        congruence.
assert (ismostderived_flag = true ->
  (h, p) = (Class.Inheritance.Repeated, real :: nil) \/
  (forall b : ident,
    is_virtual_base_of (A:=A) (Interm.hierarchy prog) b from -> False)).
 intro.
 destruct (H15 H23).
  injection H24; intros; subst.
  inversion H17; subst.
  left; congruence.
 eauto.
destruct (compile_set_dynamic_type_correct
  memprop
  xH
  H12 (invariant_valid_blocks0 _ _ H3)
  H21
  (invariant_object_sizes0 _ _ H11 _ H21 _ H3)
  H4
  stack0
  (prog := prog') (refl_equal _)
  tsp sem H0
  H22
  H23
  (map compile stl) mvalues
).
invall.
destruct H25.
esplit.
split.
eassumption.
exists objmap lo.
split; simpl; eauto.

(** 5 variables *)
intro.
rewrite sm_other.
eauto.
congruence.

(** 4 fields *)
intros.
erewrite H28.
eauto.
destruct (peq obj0 obj).
 subst.
 right.
 intros.
 replace o0 with o in * by congruence.
 (** POPL 2011 *)
 assert (offsets ! to <> None) by eauto using path_defined_to.
 assert (
   valid_relative_pointer (A:=A) (Interm.hierarchy prog)
          (Object.class o) (Object.arraysize o) ar real i h' p' to
 ) by (econstructor; eauto using path_concat). 
 generalize (
   scalar_field_dynamic_type_data_disjoint
 Hhier intro guard H27 H40 H34 Hoz H35 H39 H36 H31 H37).
 simpl; unfold typ_data; simpl; omega.
left; eauto.

(** 3 dynamic type guard lt *)
intros.
destruct (peq obj0 obj).
 subst; eauto.
assert ((obj0, ar0, i0) <> (obj, ar, i)) by congruence.
rewrite (set_dynamic_type_strong_other_cell H14 H27) in H25; eauto.

(** 2 dynamic type guard paths *)
intros.
destruct (
  prod_eq_dec (prod_eq_dec peq (@array_path_eq_dec A)) Z_eq_dec (obj0, ar0, i0) (obj, ar, i)
).
 injection e; intros; subst.
 inversion H27; subst.
 replace o0 with o  in * by congruence.
 generalize (valid_array_path_last H31 H6).
 intro; subst.
 destruct (Well_formed_hierarchy.path_is_base_dec
Hhier H17  H34 ).
   destruct s.
   destruct s.
   destruct a.
   rewrite (set_dynamic_type_same_path
     Hhier H17 H14 H35 H36) in H30.
   injection H30; intros; subst; eauto.
  destruct (
    primary_ancestor_dec h p (is_primary_path offsets) h0 p0
  ).
   destruct s.
   destruct s.
   destruct a.
   destruct H36.
   rewrite (path_last H34) in H35.
   injection H35; intro; subst.
   erewrite set_dynamic_type_strong_other_primary_base in H30.
   discriminate.
   eassumption.
   eassumption.
   4 : eassumption.
   2 : eauto using path_last.
   eauto.
   eassumption.
   eassumption.
  generalize (f _ (path_last H34)).
  intro.
  erewrite (set_dynamic_type_strong_other_not_primary_base) in H30.
  2 : eassumption.
  2 : eassumption.
  4 : eassumption.
  eauto.
  2 : eassumption.
  eauto.
  assumption.
erewrite set_dynamic_type_strong_other_cell in H30.
2 : eassumption.
eauto.
assumption.

(** dynamic type: vptr *)
intros.
destruct (peq obj0 obj).
 subst.
 replace o0 with o in * by congruence.
 replace x with oh in * by congruence.
 destruct (prod_eq_dec (@array_path_eq_dec A) Z_eq_dec (ar0, i0) (ar, i)).
  injection e; intros; subst.
   inversion H27; subst.
   generalize (valid_array_path_last H33 H6).
   intro; subst.
   destruct (
    Well_formed_hierarchy.path_is_base_dec Hhier H17 H36
   ).
    destruct s.
    destruct s.
    destruct a.
    rewrite (H26 _ H29 _ _ H37 _ _ H38 _ H32).
    generalize (set_dynamic_type_same_path
Hhier H17 H14 H37 H38).
    congruence.
 destruct (
    primary_ancestor_dec h p (is_primary_path offsets) h0 p0
  ).
   destruct s.
   destruct s.
   destruct a.
   destruct H38.
   rewrite (path_last H36) in H37.
   injection H37; intro; subst.
   erewrite set_dynamic_type_strong_other_primary_base in H30.
   discriminate.
   eassumption.
   eassumption.
   3 : eassumption.
   3 : eassumption.
   3 : eassumption.
   2 : eauto using path_last.
   eauto.
  generalize (f _ (path_last H36)).
  intro.
  erewrite set_dynamic_type_strong_other_not_primary_base in H30.
  2 : eassumption.
  2 : eassumption.
  4 : eassumption.
  3 : eassumption.
  3 : eassumption.
  2 : eauto.
  erewrite H28.
  eauto.
  right.
  intros.
  assert (
    valid_relative_pointer (A:=A) (Interm.hierarchy prog)
    (Object.class o) (Object.arraysize o) ar real i h' p' to
  ) by (econstructor; eauto using path_concat).
  assert (offsets ! to <> None) by eauto using path_defined_to.
  assert (offsets ! from0 <> None) by eauto using path_defined_to.
  refine (_ (reduce_path_dynamic_type_disjoint
  Hhier intro H27 H40 _ H42 H41 H29 H38 H32 Hoz)).
  simpl.
  tauto.
  right.
  eapply reduce_non_primary_path.
  4 : eassumption.
  eassumption.
  assumption.
  eauto.
  2 : eassumption.
  eassumption.
 erewrite set_dynamic_type_strong_other_cell in H30.
 2 : eassumption.
 2 : congruence.
 erewrite H28.
 eauto.
 right.
 intros.
  assert (
    valid_relative_pointer (A:=A) (Interm.hierarchy prog)
    (Object.class o) (Object.arraysize o) ar real i h' p' to
  ) by (econstructor; eauto using path_concat).
  assert (offsets ! to <> None) by eauto using path_defined_to.
  assert (offsets ! from0 <> None) by (inversion H27; subst; eauto using path_defined_to).
  refine ( (reduce_path_dynamic_type_disjoint
  Hhier intro H35 H27 _ H36 H37 H33 H29 Hoz H32)).
  left; congruence.
 erewrite set_dynamic_type_strong_other_cell in H30.
 2: eassumption.
 2 : congruence.
 erewrite H28.
 eauto.
 left; eauto.
Qed.

Lemma preservation_casttobase_repeated : forall vptr from b target stl vars stack global dt,
  Interm.State
  (casttobase A nativeop vptr from Class.Inheritance.Repeated b target)
  stl vars stack (Global global dt) = st1 ->
  goal.
Proof.
       intros; subst.
       Opaque concat Globals.get_field Globals.put_field.
       inversion Hstep; subst; simpl in *; try discriminate.
       invall; subst.
       destruct Hinv.
       destruct st2; simpl in *.
       destruct memory; simpl in *.
       inversion H; simpl in *; subst; simpl in *.
       destruct (invariant_vars0 _ _ H11).
       destruct H0.
       inversion H1; subst.
       inversion H12; subst.
       destruct (H14 _ H6 _ _ H15).
       invall; subst.
       inversion H15; subst.
       functional inversion H7; subst.
       functional inversion H20; subst.
       generalize (path_last H16).
       intro.
       replace to with from in * by congruence.
       assert (offsets ! from <> None) by eauto using path_defined_to.
       case_eq (offsets ! from); try congruence.
       intros.
       assert ((non_virtual_direct_base_offsets t) ! b <> None) by eauto using non_virtual_direct_base_offsets_exist.
       case_eq ((non_virtual_direct_base_offsets t) ! b); try congruence.
       intros.
       replace o0 with ofto in * by congruence.
       esplit.
       split.
       eapply plus_left.
       econstructor.
       eassumption.
       reflexivity.
       eleft.
       rewrite E0_left; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; eauto.
       intro.
       destruct (peq target v).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intro; subst.
        esplit.
        split.
        reflexivity.
        econstructor.
        assumption.
        rewrite H6.
        injection 1; intro; subst o1.
        inversion 1; subst.
        generalize (valid_array_path_last H31 H4).
        intro; subst.
        esplit.
        split.
         eassumption.
        unfold relative_pointer_offset.
        rewrite H18.
        rewrite H19.
        unfold subobject_offset.
        rewrite H19.
        rewrite H24.
        destruct (last_correct H13).
        change (b0 :: _x ++ b :: nil) with ((b0 :: _x) ++ b :: nil).
        rewrite e.
        rewrite e in H17.
        rewrite app_ass.
        simpl.
        rewrite (non_virtual_subobject_offset_app H17).
        simpl.
        rewrite H25.
        rewrite H27.
        esplit.
        split.
        reflexivity.
        f_equal.
        f_equal.
        omega.
       repeat rewrite PTree.gso; eauto; congruence.
Qed.

Lemma preservation_casttobase_shared : forall vptr from b target stl vars stack global dt,
  Interm.State
  (casttobase A nativeop vptr from Class.Inheritance.Shared b target)
  stl vars stack (Global global dt) = st1 ->
  goal.
Proof.
       intros; subst.
       Opaque concat Globals.get_field Globals.put_field.
       inversion Hstep; subst; simpl in *; try discriminate.
       invall; subst.
       destruct Hinv.
       destruct st2; simpl in *.
       destruct memory; simpl in *.
       inversion H0; simpl in *; subst; simpl in *.
       destruct (invariant_vars0 _ _ H11).
       destruct H1.
       inversion H2; subst.
       inversion H12; subst.
       destruct (H10 _ H5 _ _ H14).
       invall; subst.
       inversion H14; subst.
       inversion H15; subst.
       injection H16; intros; subst.
       generalize (path_last H15).
       injection 1; intros; subst.
       functional inversion H6; subst.
       unfold subobject_offset in H23.
       rewrite H22 in H23.
       rewrite (virtual_base_offsets_self (intro H22)) in H23.
       simpl in H23.
       injection H23; intro; subst.
       rewrite H22.
       assert ((virtual_base_offsets ofto) ! b <> None) by eauto using virtual_base_offsets_exist.
       case_eq ((virtual_base_offsets ofto) ! b); try congruence.
       intros.
       esplit.
       split.
       eapply plus_left.
       econstructor.
       eassumption.
       reflexivity.
       eleft.
       rewrite E0_left; eauto using evtr_sem.
       exists objmap lo.
       split; simpl; eauto.
       intro.
       destruct (peq target v).
        subst.
        repeat rewrite PTree.gss.
        injection 1; intro; subst.
        esplit.
        split.
        reflexivity.
        econstructor.
        assumption.
        rewrite H5.
        injection 1; intro; subst o0.
        inversion 1; subst.
        generalize (valid_array_path_last H28 H3).
        intro; subst.
        esplit.
        split.
         eassumption.
        unfold relative_pointer_offset.
        rewrite H21.
        rewrite H22.
        unfold subobject_offset.
        rewrite H22.
        rewrite H24.
        simpl.
        esplit.
        split.
        reflexivity.
        f_equal.
        f_equal.
        omega.
       repeat rewrite PTree.gso; eauto; congruence.
Qed.

  

     Theorem preservation : goal.
     Proof.
      simple inversion Hstep; intros.
      solve [ eapply preservation_skip; eauto ].
      solve [ eapply preservation_seq; eauto ].
      solve [ eapply preservation_move; eauto ].
      solve [ eapply preservation_test; eauto ]. 
      solve [ eapply preservation_loop; eauto ]. 
      solve [ eapply preservation_block_None; eauto ].
      solve [ eapply preservation_block_Some; eauto ].
      solve [ eapply preservation_exit_O; eauto ].
      solve [ eapply preservation_exit_S; eauto ].
      solve [ eapply preservation_return; eauto ].
      solve [ eapply preservation_call; eauto ].
      solve [ eapply preservation_native; eauto ].
      solve [ eapply preservation_null; eauto ].
      solve [ eapply preservation_ptreq; eauto ].
      solve [ eapply preservation_getfield; eauto ].
      solve [ eapply preservation_putfield; eauto ].
      solve [ eapply preservation_static_cast; eauto ].
      solve [ eapply preservation_dynamic_cast; eauto ].
      solve [ eapply preservation_invoke; eauto ].
      solve [ eapply preservation_array_index; eauto ].
      destruct pop.
       solve [ eapply preservation_rootpath; eauto ].       
       solve [ eapply preservation_addbase; eauto ].       
      solve [ eapply preservation_set_dynamic_type ; eauto ].
      destruct kind.
       solve [ eapply preservation_casttobase_repeated ; eauto ].    
        solve [ eapply preservation_casttobase_shared ; eauto ].     
      Qed.

End Step.

Corollary simulation : forall beh,
  not_wrong beh ->
  program_behaves (Interm.step prog (sem := sem) (is_primary_path offsets)) (Interm.initial_state prog) (@Interm.final_state A nativeop sem) beh ->
  program_behaves (Target.step (sem:=sem) vop' memop prog' tsp) (Target.initial_state memop prog') (@Target.final_state A (nativeop) (sem) (romty A) mblock memblocks memvalues) beh.
Proof.
 intro.
 apply simulation_plus_preservation with (match_states := invariant).
 eauto using evtr_sem.
 eauto using init.
 eauto using fin.
 intros; eauto using preservation.
Qed.

End Common.

Check simulation.