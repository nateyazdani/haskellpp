Require Import Coqlib.
Require Import Cplusconcepts.
Require Import CplusWf.
Require Import LibLists.
Require Import Tactics.
Require Import LibMaps.
Require Import Relations.
Require Import Dynamic.
Require Import Events.
Require Import Smallstep.
Require Import Cppsem.
Require Import Interm.
Require Import IntermSetDynType.
Require Import IntermSetDynTypeWf.
Require Import Eqdep_dec.
Require Import Invariant.
Require Import Preservation.
Require Import ForLoop.
Require Import SubobjectOrdering.
Require Import ConstrSubobjectOrdering.
Require Import Dyntype.
Require Import Constrorder.
Require Import ScalarFields.
Load Param.
Open Scope Z_scope.

Section Compiler.

Variable A : ATOM.t.

Variable nativeop : Type.

Notation GARBAGE := (Interm.skip A nativeop) (only parsing).

Inductive newvar : Type :=
| Oldvar (_ : var)
| Newvar (_ : positive)
.


Inductive newstatic : Type :=
| Newstatic (_ : ident)
| Oldstatic (_ : ident)
.


Variable sem : semparam A nativeop.

Variable prog : Program.t A nativeop.

Variable compile_var : newvar -> var.
Hypothesis compile_var_inj : forall v1 v2, compile_var v1 = compile_var v2 -> v1 = v2.

Lemma compile_var_other : forall v1 v2, v1 <> v2 -> compile_var v1 <> compile_var v2.
Proof.
  intros.
  intro.
  generalize (compile_var_inj H0).
  assumption.
Qed.

Variable compile_static : newstatic -> ident.


Inductive constrdestr : Type :=
| StaticConstructor (_ : list (Typ.t A))
| StaticDestructor
.

Variable compile_constrdestr : ident -> constrdestr -> bool -> ident.

Definition compile_initcell (cn : ident)  (blockvar index newobj newpath : var) (i : Z) (init : Interm.stmt A nativeop) :=
  let (ty, va) := Zsem sem i in
    seq
    (Interm.native _ (CONST sem va) nil (Some (compile_var (Newvar index))))
    (seq      
      (Interm.arrayindex _ _ cn (compile_var (Newvar index)) (compile_var (Newvar blockvar)) (compile_var (Newvar newobj)))
      (seq
        (Interm.pathop _ _ (Interm.rootpath cn) None (compile_var (Newvar newpath)))
        init
      )
    ).

Definition compile_constrarray_aux (cn : ident) (sz : Z) (blockvar index newobj newpath : var) (instr : Z -> Interm.stmt A nativeop) (q : Interm.stmt A nativeop) :=
  forup q
  (fun j => seq (compile_initcell cn blockvar index newobj newpath j (instr j))) sz 
.

Definition compile_destrarray_aux (cn : ident) (blockvar index newobj newpath : var) (q : Interm.stmt A nativeop) :=
  fordown q
  (fun j => seq 
    (compile_initcell cn blockvar index newobj newpath j
      (call _ (Static _ (compile_static (Newstatic (compile_constrdestr cn (StaticDestructor ) true)))) (compile_var (Newvar newobj) :: compile_var (Newvar newpath) :: nil) None)
    )
  ) (-1).

Definition compile_destrarray cn blockvar maxvar :=
  let index := Psucc maxvar in
    let newobj := Psucc index in
      let newpath := Psucc newobj in
        compile_destrarray_aux cn blockvar index newobj newpath.
  
Fixpoint compile_discard (n : nat) (blocks : list (option (var * var * (ident * Z)))) maxvar (q : Interm.stmt A nativeop) {struct n} : Interm.stmt A nativeop :=
  match n with
    | O => q
    | S n' =>
      match blocks with
        | nil => q
        | None :: blocks' => seq (skip _ _) (compile_discard n' blocks' maxvar q)
        | Some (blockvar, maxvar', (cn, sz)) :: blocks' =>
          seq (
            block None 
            (compile_destrarray cn blockvar maxvar (exit _ _ 1%nat) (sz-1))
          )
          (compile_discard n' blocks' maxvar' q)
      end
  end.

Record context : Type := Context {  
  maxvar : positive;
  curobjpathfield : option ((positive * positive * bool) * option (ident * FieldSignature.t A));
  blocks : list (option (var * var * (ident * Z)));
  further_blocks : nat;
  is_destructor_body : bool
}.

Hypothesis hierarchy_wf : Well_formed_hierarchy.prop (Program.hierarchy prog).

Fixpoint compile (c : context) (s : Cppsem.stmt A nativeop) {struct s} : Interm.stmt A nativeop  :=
  match s with
    | Sskip => skip _ _
    | Sif var iftrue iffalse =>
      test (compile_var (Oldvar var)) (compile c iftrue) (compile c iffalse)
    | Sloop st => loop (compile c st)
    | Sseq s1 s2 => seq (compile c s1) (compile c s2)
    | Sblock localstruct initializers body =>
      match localstruct with
        | None => block None (
          let bl' :=  (None :: blocks c) in
            seq
            (compile (Context (maxvar c) (curobjpathfield c) bl' (further_blocks c) (is_destructor_body c)) body)
            (
              (compile_discard 1%nat bl' (maxvar c) (Interm.exit _ _ 1%nat))
            )
        )
        | Some (v, cn, sz) =>
          let blockvar := Psucc (maxvar c) in
            let midvar := Psucc blockvar in
              let blockvar' := Psucc midvar in (* the same variable cannot be used in two different contexts *)
              block
              (Some (compile_var (Newvar blockvar), (cn, sz)))
              (seq
                (seq
                  (Interm.move _ _ (compile_var (Newvar blockvar)) (compile_var (Oldvar v)))
                  (Interm.move _ _ (compile_var (Newvar blockvar)) (compile_var (Newvar blockvar')))
                )           
                (
                  let index := Psucc blockvar' in
                    let newobj := Psucc index in
                      let newpath := Psucc newobj in
                        let maxvar' := Psucc newpath in
                          seq (
                            block None (
                              compile_constrarray_aux cn sz blockvar' index newobj newpath (fun j =>
                                block None 
                                (
                                  (seq
                                    (compile (Context maxvar' (Some ((newobj, newpath, true), None)) nil O false) (initializers j))
                                    (compile_discard 1%nat nil maxvar' (Interm.exit _ _ 1%nat))
                                  )
                                )
                              ) (exit _ _ 1%nat) 0
                            )
                          )
                          (
                            let bl' := (Some (blockvar, maxvar c, (cn, sz)) :: blocks c) in
                              seq
                              (compile (Context midvar (curobjpathfield c) bl' (further_blocks c) (is_destructor_body c)) body)
                              (compile_discard 1%nat bl' midvar (Interm.exit _ _ 1%nat))
                          )
                )
              )
      end
    | Sexit n => 
      compile_discard n (blocks c) (maxvar c) (Interm.exit _ _ (further_blocks c + n)%nat)
    | Sreturn ov =>
      compile_discard (length (blocks c)) (blocks c) (maxvar c) (
        if is_destructor_body c
          then (Interm.exit _ _ (S (further_blocks c + length (blocks c))))
          else Interm.ret _ _ 
            (match ov with
               None => None
               | Some v => Some (compile_var (Oldvar v))
             end))

    | Sconstructor cn vargs =>
      match curobjpathfield c with
        | Some ((curobj, curpath, ismostderived), None) =>
          seq (
            call _ (Static _ (compile_static (Newstatic (compile_constrdestr cn (StaticConstructor  (map (fun tyv : _ * _ => let (ty, _) := tyv in ty) vargs)) ismostderived)))) (compile_var (Newvar (curobj )) :: compile_var (Newvar (curpath )) :: map (fun v => compile_var (Oldvar v)) (map (fun tyv : _ * _ => let (_, v) := tyv in v) vargs)) None
          ) (
            exit _ _ 1%nat
          )
        | _ => GARBAGE
      end

    | Sinitscalar v => 
      match curobjpathfield c with
        | Some ((curobj, _, _), Some (cn, f)) => seq
          (Interm.putfield _ cn f (compile_var (Newvar (curobj ))) (compile_var (Oldvar v)))          
          (exit _ _ 1%nat)
        | _ => GARBAGE
      end

    | Scall kind vargs vret =>
      call _ (
        match kind with
          | Cppsem.Static f => Static _ (compile_static (Oldstatic f))
          | Cppsem.NonVirtual cn ms => NonVirtual cn ms
        end
      ) (map (fun v => compile_var (Oldvar v)) vargs)
      (match vret with
         None => None
         | Some v => Some (compile_var (Oldvar v))
       end)

    | Snative n l tg => Interm.native _ ( n) (map (fun v => compile_var (Oldvar v)) l) (
      match tg with
        None => None
        | Some v => Some (compile_var (Oldvar v))
      end)

    | Smove src tgt => Interm.move _ _ (compile_var (Oldvar src)) (compile_var (Oldvar tgt))

    | Sgetfield obj cn fs tgt => Interm.getfield _ cn fs (compile_var (Oldvar obj)) (compile_var (Oldvar tgt))

    | Sputfield obj cn fs val => Interm.putfield _ cn fs (compile_var (Oldvar obj)) (compile_var (Oldvar val))

    | Sindex obj cn idx tgt => Interm.arrayindex _ _ cn (compile_var (Oldvar idx)) (compile_var (Oldvar obj)) (compile_var (Oldvar tgt))

    | Sinvoke obj class method args retval => Interm.invoke _ (compile_var (Oldvar obj)) class method (map (fun v => compile_var (Oldvar v)) args) 
      (match retval with
         None => None
         | Some v => Some (compile_var (Oldvar v))
       end)

    | Sdyncast obj cfrom cto res =>
      let (tree, _) := Well_formed_hierarchy.path_to hierarchy_wf cto in
        match (tree ! cfrom) with
          | None => GARBAGE
          | Some nil => (* not a base *) Interm.dyncast _ _ cfrom cto (compile_var (Oldvar obj)) (compile_var (Oldvar res))
          | Some l => (* base: resolve dynamic cast as static cast, or NULL if ambiguous *)
            match at_most_list path_eq_dec l with
              | inleft _ => (* ambiguous: cast fails *) Interm.null _ _ cto (compile_var (Oldvar res))
              | inright _ => Interm.statcast _ _  cfrom cto (compile_var (Oldvar obj)) (compile_var (Oldvar res))
            end
        end
        
    | Sstatcast obj cfrom cto res => Interm.statcast _ _ cfrom cto (compile_var (Oldvar obj)) (compile_var (Oldvar res))      
    | Sptreq ptr1 ptr2 vres => Interm.ptreq _ _ (compile_var (Oldvar ptr1)) (compile_var (Oldvar ptr2)) (compile_var (Oldvar vres))

  end.

Lemma compile_exit_succ : forall cur cur', Cppsem.exit_succ cur = Some cur' ->
  forall maxvar maxvar' curobjpathfield q' n' bo blockvar cn sz,
    compile (Context maxvar curobjpathfield (Some (blockvar, maxvar', (cn, sz)) :: q') n' bo) cur =
    seq (
      block None 
      (compile_destrarray cn blockvar maxvar (exit _ _ 1%nat) (sz-1))
    )
    (compile (Context maxvar' curobjpathfield q' (S n') bo) cur').
Proof.
  functional inversion 1; subst; simpl; unfold compile_discard; simpl; intros.
  replace (
    (S (S (n' + length q')))
  ) with (
    (S (n' + S (length q')))
  ) by omega.
  reflexivity.
 replace (
   (n' + S n)%nat
 ) with (
   (S (n' + n))
 ) by omega.
 reflexivity.
Qed.   

Definition compile' (c : context) (s : Cppsem.stmt A nativeop) : Interm.stmt A nativeop :=
  seq
  (compile c s)
  (compile_discard 1%nat (blocks c) (maxvar c) (Interm.exit _ _ 1%nat))
.

Definition compile_base_initializer (class : ident) (init : option (Cppsem.stmt A nativeop)) (h : Class.Inheritance.t) (b : ident) (curobj curpath maxvar : var) : Interm.stmt A nativeop :=
  let newobj := Psucc maxvar in
    let newpath := Psucc newobj in
      let maxvar' := Psucc newpath in
        block None (
          seq (
            seq
            (pathop _ _ (addbase class h b) (Some (compile_var (Newvar curpath))) (compile_var (Newvar newpath)))
            (casttobase _ _ (compile_var (Newvar curobj)) class h b (compile_var (Newvar newobj)))
          )
          (
            compile' (Context maxvar' (Some ((newobj, newpath, false), None)) nil O false) 
            match init with
              | None => Sconstructor b nil
              | Some s => s
            end
          )
        )
          .

Definition compile_constrarray tinit b sz newobj index newobj' newpath' maxvar' :=
  compile_constrarray_aux b sz newobj index newobj' newpath' (
    fun j => block None (compile' (Context maxvar' (Some ((newobj', newpath', true), None)) nil O false) (tinit j))
  ) (exit _ _ 1%nat).


Definition compile_field_initializer class tinit init f curobj curpath maxvar :=
  let newobj := Psucc maxvar in
    let index := Psucc newobj in
      let newobj' := Psucc index in
        let newpath' := Psucc newobj' in
        let maxvar' := Psucc newpath' in
  match FieldSignature.type f with
    | FieldSignature.Scalar ty =>
      match assoc (@Constructor.initializer_key_eq_dec _) (existT _ Constructor.field (tt, f)) init with
        | None => skip _ _
        | Some st => block None (
          compile' (Context maxvar (Some ((curobj, curpath, false (** irrelevant here **)), (Some (class, f)))) nil O false) st
        )
      end
    | FieldSignature.Struct b psz =>
      seq (
        getfield _ class f (compile_var (Newvar curobj)) (compile_var (Newvar newobj))
      ) (
        block None (
          compile_constrarray (
            match assoc (@FieldSignature.eq_dec _) f tinit with
              | Some init'' => init''
              | _ => (fun _ => Sconstructor b nil)
            end
          ) b (Zpos psz) newobj index newobj' newpath' maxvar' 0
        )
      )
  end.


Definition compile_constr_fields fields class tinit init body curobj curpath maxvar :=
  fold_right (fun f s => seq (
    compile_field_initializer class tinit init f curobj curpath maxvar
  ) s)
  ((compile' (Context xH (* maxvar *) None nil O false) body))
  fields.

Lemma vborder_list_ex : forall class, {vb | exists c, (Program.hierarchy prog) ! class = Some c /\ vborder_list (Program.hierarchy prog) (Class.super c) vb} + {(Program.hierarchy prog) ! class = None}.
Proof.
  intros.
  case_eq ((Program.hierarchy prog) ! class).
   intros.
   left.
   destruct (Well_formed_hierarchy.vborder_list_exists hierarchy_wf H).
   esplit.
   esplit.
   split.
    reflexivity.
   eassumption.
  right; trivial.
Qed.

Definition compile_constr_all_fields (ismostderived : bool) class tinit init body curobj curpath maxvar :=
    match (Program.hierarchy prog) ! class with
      | None => GARBAGE
      | Some cl => seq (
        setdyntype _ _ (
          if ismostderived then true else
            match vborder_list_ex class with
              | inleft (exist (_ :: _) _) => false
              | _ => true
            end
        ) class
        (compile_var (Newvar curobj)) (compile_var (Newvar curpath))
      )
      (compile_constr_fields  (Class.fields cl) class tinit init body curobj curpath maxvar)
    end
    .

Definition compile_constr_direct_non_virtual_bases ismostderived vb class tinit init body curobj curpath maxvar := 
  fold_right (fun (b : ident) (s : Interm.stmt A nativeop) => seq (
    compile_base_initializer class (assoc (@Constructor.initializer_key_eq_dec _) (existT _ Constructor.base (Constructor.direct_non_virtual, b)) init) Class.Inheritance.Repeated b curobj curpath maxvar
  )
  s
  )
  (compile_constr_all_fields ismostderived class tinit init body curobj curpath maxvar)
  vb
.
 
Definition compile_constr_non_virtual_part ismostderived class tinit init body curobj curpath maxvar :=
  match (Program.hierarchy prog) ! class with
    | None => GARBAGE
    | Some cl => compile_constr_direct_non_virtual_bases ismostderived (map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b) (filter (fun hb : _ * ident =>
        match hb with
          | (Class.Inheritance.Shared, _) => false
          | _ => true
        end
      ) (Class.super cl)))
 class tinit init body
      curobj curpath maxvar
  end.

Definition compile_constr_virtual_bases  vb class tinit init body curobj curpath maxvar :=
  fold_right (fun (b : ident) (s : Interm.stmt A nativeop) => seq (
    compile_base_initializer class (assoc (@Constructor.initializer_key_eq_dec A) (existT _ Constructor.base (Constructor.virtual, b)) init) Class.Inheritance.Shared b curobj curpath maxvar
  )
  s
  ) 
  (seq (skip _ _) (compile_constr_non_virtual_part true class tinit init body curobj curpath maxvar))
  vb
.

Definition compile_constr ismostderived (k : Constructor.init_key_primary) (k2 : Constructor.init_key_secondary k) (vb : list (Constructor.init_key_item A k)) class tinit init body curobj curpath maxvar :=
  match k as k' return Constructor.init_key_secondary k' -> list (Constructor.init_key_item A k') -> _ with
    | Constructor.base => fun k2' vb' =>
      match k2' with
        | Constructor.direct_non_virtual => compile_constr_direct_non_virtual_bases ismostderived vb'  class tinit init body curobj curpath maxvar
        | Constructor.virtual => compile_constr_virtual_bases vb' class tinit init body curobj curpath maxvar
      end
    | Constructor.field => fun _ vb' =>
      compile_constr_fields vb' class tinit init body curobj curpath maxvar
  end k2 vb.

Definition compile_constructor (class : ident) (c : Constructor.t A nativeop) (ismostderived : bool) : Interm.static_fun A nativeop :=
  let curobj := Psucc xH in
    let curpath := Psucc curobj in
      let is_most_derived := Psucc curpath in
        let maxvar := Psucc is_most_derived in
          Interm.Static_fun
          (compile_var (Oldvar (Constructor.this c)) :: compile_var (Newvar curpath) :: map (fun v => compile_var (Oldvar v)) (Constructor.args c))
          (
            seq
            (Interm.move _ _ (compile_var (Oldvar (Constructor.this c)))  (compile_var (Newvar curobj)))
            (
              let nv :=seq
                (skip _ _) (** introduced to ensure equality of constructors for classes with no virtual bases *)
                (compile_constr_non_virtual_part false class (Constructor.struct_field_initializers c) (Constructor.initializers c) (Constructor.body c) curobj curpath maxvar)
                in
                if ismostderived
                  then
                    match vborder_list_ex class with
                      | inright _ => nv (** dead code, but nv instead of skip is easier to prove equality with no virtual bases *)
                      | inleft (exist vb _) => compile_constr_virtual_bases vb class (Constructor.struct_field_initializers c) (Constructor.initializers c) (Constructor.body c) curobj curpath maxvar 
                    end
                  else
                    nv
            )
          )
          .

Lemma compile_constructor_eq_with_no_virtual_bases : forall class,
  (forall b, is_virtual_base_of (Program.hierarchy prog) b class -> False) ->
  forall c,
    compile_constructor class c true = compile_constructor class c false.
Proof.
  intros.
  unfold compile_constructor; simpl.
  unfold compile_constr_non_virtual_part; simpl.
  unfold compile_constr_direct_non_virtual_bases; simpl.
  unfold compile_constr_all_fields; simpl.
  destruct (vborder_list_ex class); try reflexivity.
  destruct s.
  destruct e.
  destruct H0.
  destruct x; try reflexivity.
  destruct (H i).
  eauto using vborder_list_virtual_base.  
Qed.   

Definition compile_base_finalizer (class : ident) (h : Class.Inheritance.t) (b : ident) (curobj curpath maxvar : var) : Interm.stmt A nativeop :=
  let newobj := Psucc maxvar in
    let newpath := Psucc newobj in
      let maxvar' := Psucc newpath in
        seq (
          seq
          (pathop _ _ (addbase class h b) (Some (compile_var (Newvar curpath))) (compile_var (Newvar newpath)))
          (casttobase _ _ (compile_var (Newvar curobj)) class h b (compile_var (Newvar newobj)))
        )        
        (call _ (Static _ (compile_static (Newstatic (compile_constrdestr b (StaticDestructor ) false)))) (compile_var (Newvar newobj) :: compile_var (Newvar newpath) :: nil) None)
        .

Definition compile_destr_virtual_bases vb class curobj curpath maxvar := 
  fold_right (fun (b : ident) (s : Interm.stmt A nativeop) => seq (
    compile_base_finalizer class Class.Inheritance.Shared b curobj curpath maxvar
  )
  s
  ) 
  (ret _ _ None)
  vb
.

Definition compile_destr_all_virtual_bases (ismostderived : bool) class curobj curpath maxvar :=
  seq (skip _ _) (** necessary for step *)
  (if ismostderived
    then match vborder_list_ex class with
           | inright _ => GARBAGE
           | inleft (exist vb _) => (compile_destr_virtual_bases  (rev vb) class curobj curpath maxvar)
         end
    else          
      ret _ _ None)
      .

Definition compile_destr_direct_non_virtual_bases (ismostderived : bool) vb class curobj curpath maxvar := 
    fold_right (fun (b : ident) (s : Interm.stmt A nativeop) => seq (
      compile_base_finalizer class Class.Inheritance.Repeated b curobj curpath maxvar
    )
    s
    )
    (compile_destr_all_virtual_bases ismostderived class curobj curpath maxvar)
    vb
.

Definition compile_destr_field  f class curobj maxvar :=
  let newobj := Psucc maxvar in
    let index := Psucc newobj in
      let newobj' := Psucc index in
        let newpath' := Psucc newobj' in
          let maxvar' := Psucc newpath' in
            match FieldSignature.type f with
              | FieldSignature.Scalar ty => skip _ _
              | FieldSignature.Struct b psz =>
                seq (
                  getfield _ class f (compile_var (Newvar curobj)) (compile_var (Newvar newobj))
                ) (
                  block None (
                    compile_destrarray_aux b newobj index newobj' newpath' (exit _ _ 1%nat)  (Zpos psz - 1)
                  )
                )
            end.

Definition compile_destr_all_direct_non_virtual_bases ismostderived class curobj curpath maxvar :=  
  match (Program.hierarchy prog) ! class with
    | None => GARBAGE
    | Some cl => compile_destr_direct_non_virtual_bases ismostderived (rev (
      (map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b) (filter (fun hb : _ * ident =>
        match hb with
          | (Class.Inheritance.Shared, _) => false
          | _ => true
        end
      ) (Class.super cl)))
    )      
    ) class curobj curpath maxvar
  end.

Definition compile_destr_fields ismostderived l class  curobj curpath maxvar := 
  fold_right (fun f (s : Interm.stmt A nativeop) => seq (
    compile_destr_field f class curobj maxvar
  )
  s
  )
  (seq (skip _ _  (** necessary for step *) ) (compile_destr_all_direct_non_virtual_bases ismostderived class curobj curpath maxvar))
  l
.

Definition compile_destr_all_fields ismostderived class curobj curpath maxvar := 
  match (Program.hierarchy prog) ! class with
    | None => GARBAGE
    | Some cl => compile_destr_fields ismostderived (rev (Class.fields cl)) class curobj curpath maxvar
  end.

Definition compile_destr (ismostderived : bool) (k : Constructor.init_key_primary) (k2 : Constructor.init_key_secondary k) (vb : list (Constructor.init_key_item A k)) :=
  match k as k' return Constructor.init_key_secondary k' -> list (Constructor.init_key_item A k') -> _ with
    | Constructor.base => fun k2' vb' =>
      match k2' with
        | Constructor.direct_non_virtual => compile_destr_direct_non_virtual_bases ismostderived vb'
        | Constructor.virtual => compile_destr_virtual_bases vb'
      end
    | Constructor.field => fun _ vb' =>
      compile_destr_fields ismostderived vb'
  end k2 vb.

Definition compile_destructor (class : ident) (ismostderived : bool) : Interm.static_fun A nativeop :=  
  let curobj := Psucc xH in
    let curpath := Psucc curobj in
      let maxvar := Psucc curpath in
        Interm.Static_fun
        (compile_var (Newvar curobj) :: compile_var (Newvar curpath) :: nil)
        (
          (
            if ismostderived           
              then (fun s => s) (** do not set dynamic type when destructing a most-derived object *)
              else
                seq
                (setdyntype _ _ false class
                  (compile_var (Newvar curobj)) (compile_var (Newvar curpath)))
          )(
            seq
            match (Program.hierarchy prog) ! class with
              | None => GARBAGE
              | Some cl =>
                match Method.find (Program.destructor_sig prog) (Class.methods cl) with
                  | None => GARBAGE
                  | Some m =>
                    match Method.kind m with
                      | Method.concrete mi => 
                        match (Program.methods prog) ! mi with
                          | None => GARBAGE
                          | Some code => (* inlining destructor body *)
                            block None
                              (seq
                                (move _ _ (compile_var (Newvar curobj)) (compile_var (Oldvar (Method_body.this code))))
                                (compile' (Context maxvar None nil O true (** irrelevant *)) (Method_body.code code))
                              )
                        end
                      | _ => GARBAGE
                    end
                end
            end
            (
              compile_destr_all_fields ismostderived class curobj curpath maxvar
            )
          )
        ).

Definition vars_invariant vars vars' :=
  forall var v, vars ! var = Some v -> vars' ! (compile_var (Oldvar var)) = Some (Val (A := A) v).

Lemma vars_invariant_newvar : forall vars vars',
  vars_invariant vars vars' ->
  forall var val, vars_invariant vars (PTree.set (compile_var (Newvar var)) val vars').
Proof.
  unfold vars_invariant.
  intros.
  rewrite PTree.gso.
  eauto.
  apply compile_var_other.
  congruence.
Qed.

Lemma vars_invariant_newvar_recip : forall vars vars' var val,
  vars_invariant vars (PTree.set (compile_var (Newvar var)) val vars') ->
  vars_invariant vars vars'.
Proof.
  unfold vars_invariant.
  intros.
  generalize (H _ _ H0).
  rewrite PTree.gso.
  eauto.
  apply compile_var_other.
  congruence.
Qed.

Lemma vars_invariant_oldvar : forall vars vars',
  vars_invariant vars vars' ->
  forall var val,
    vars_invariant (PTree.set var val vars) (PTree.set (compile_var (Oldvar var)) (Val val) vars').
Proof.
  unfold vars_invariant.
  intros.
  destruct (peq var var0).
   subst.
   rewrite PTree.gss.
   rewrite PTree.gss in H0.
   congruence.
  rewrite PTree.gso in H0; eauto.
  rewrite PTree.gso.
  eauto.
  apply compile_var_other.
  congruence.
Qed. 

Section Block_invariant.

  Variable heap : PTree.t Object.t.
  Variable vars : PTree.t (value A).
  Variable curobjpathfield : option ((ident * ident * bool) * option (ident * FieldSignature.t A)).
  Variable destrbody : bool.
  Variable minvar : positive.

Inductive block_invariant :  ident -> list (BlockPoint.t A nativeop) -> list (option (var * var * (ident * Z))) -> list (frame A nativeop) -> Prop := 
| block_invariant_nil :
  match curobjpathfield with
    | Some ((curobj, curpath, _), _) => Plt curobj curpath /\ Plt curpath minvar
    | _ => True
  end ->  
  block_invariant minvar nil nil nil

| block_invariant_cons_none : forall maxvar bl cbl fbl,
  block_invariant maxvar bl cbl fbl ->
  forall stl stl', stl' = map (compile (Context maxvar curobjpathfield cbl O destrbody)) stl ++
    (compile_discard 1%nat (cbl) (maxvar ) (Interm.exit _ _ 1%nat)) :: nil   
    ->
    block_invariant maxvar (BlockPoint.make stl None :: bl) (None :: cbl) (Interm.Block None stl' :: fbl)

| block_invariant_cons_some : forall  maxvar bl cbl fbl,
  block_invariant  maxvar  bl cbl fbl ->
  forall var, Plt maxvar var ->
    forall maxvar', Plt var maxvar' ->
      forall obj o, heap ! obj = Some o ->
        forall cn, cn = Object.class o ->
          forall sz, sz = Object.arraysize o ->
            forall hp,
              vars ! (compile_var (Newvar var)) = Some (Val (Value.ptr (Value.subobject obj nil 0 Class.Inheritance.Repeated (cn :: nil) hp))) ->
            forall stl stl', stl' = map (compile (Context maxvar curobjpathfield cbl O destrbody)) stl ++
              (compile_discard 1%nat (cbl) (maxvar ) (Interm.exit _ _ 1%nat)) :: nil
 ->
              block_invariant maxvar' (BlockPoint.make stl (Some obj) :: bl) (Some (var, maxvar, (cn, sz)) :: cbl) (Interm.Block (Some obj) stl' :: fbl).

End Block_invariant.

Lemma block_invariant_heap_new : forall heap vars curobjpathfield destrbody minvar maxvar bl cbl fbl,
  block_invariant heap vars curobjpathfield destrbody minvar maxvar bl cbl fbl ->
  forall obj, heap ! obj = None -> forall o,
    block_invariant (PTree.set obj o heap) vars curobjpathfield destrbody minvar maxvar bl cbl fbl.
Proof.
  induction 1.
   intros; constructor; eauto.
  intros; constructor; eauto.
 intros; econstructor.
 eauto.
 assumption.
 assumption.
 rewrite PTree.gso; eauto.
 congruence.
 assumption.
 assumption.
 eassumption.
 assumption.
Qed.

Lemma block_invariant_oldvar : forall heap vars curobjpathfield destrbody minvar maxvar bl cbl fbl,
  block_invariant heap vars curobjpathfield destrbody minvar maxvar bl cbl fbl ->
  forall var val,
    block_invariant heap (PTree.set (compile_var (Oldvar var)) val vars) curobjpathfield destrbody minvar maxvar bl cbl fbl.
Proof.
  induction 1.
  intros; constructor; eauto.
  intros; constructor; eauto.
  intros; econstructor; eauto.
  rewrite PTree.gso; eauto.
  apply compile_var_other.
  congruence.
Qed.

Lemma block_invariant_newvar_gt : forall heap vars curobjpathfield destrbody minvar maxvar bl cbl fbl,
  block_invariant heap vars curobjpathfield destrbody minvar maxvar bl cbl fbl ->
  forall var, Plt maxvar var ->
    forall val,
      block_invariant heap (PTree.set (compile_var (Newvar var)) val vars) curobjpathfield destrbody minvar maxvar bl cbl fbl.
Proof.
  induction 1.
  intros; constructor; eauto.
  intros; constructor; eauto.
  intros; econstructor; eauto.
  eapply IHblock_invariant.
  eauto using Plt_trans. 
  rewrite PTree.gso; eauto.
  apply compile_var_other.
  intro.
  injection H8; intros; subst.
  eapply Plt_irrefl with var0.
  eapply Plt_trans.
  eassumption.
  assumption.
Qed.
 
Lemma block_invariant_curobj_lt_curpath : forall heap vars curobj curpath ismostderived curfield destrbody minvar maxvar bl cbl fbl,
  block_invariant heap vars (Some ((curobj, curpath, ismostderived), curfield)) destrbody minvar maxvar bl cbl fbl ->
  Plt curobj curpath.
Proof.
  induction 1; simpl in *; invall; eauto using Plt_trans.
Qed.

Lemma block_invariant_curpath_lt_minvar : forall heap vars curobj curpath ismostderived curfield minvar maxvar destrbody bl cbl fbl,
  block_invariant heap vars (Some ((curobj, curpath, ismostderived), curfield)) destrbody minvar maxvar bl cbl fbl ->
  Plt curpath minvar.
Proof.
  induction 1; simpl in *; invall; eauto using Plt_trans.
Qed.

Lemma block_invariant_minvar_le_maxvar : forall heap vars curobjpathfield minvar maxvar destrbody bl cbl fbl,
  block_invariant heap vars curobjpathfield destrbody minvar maxvar bl cbl fbl ->
  Ple minvar maxvar.
Proof.
  induction 1; simpl in *; invall.
   apply Ple_refl.
   assumption.
   eapply Plt_Ple.
   eapply Ple_Plt_trans.
   eassumption.
   eauto using Plt_trans.
Qed.

Fixpoint retrieve_list_stmt (U V : Type) (ls : U) (p : list (V * U)) {struct p} : U :=
  match p with
    | nil => ls
    | (_, ls') :: p' => retrieve_list_stmt ls' p'
  end.

Lemma retrieve_list_stmt_app : forall (U V : Type) p1 ls p2, retrieve_list_stmt (U := U) (V := V) ls (p1 ++ p2) = retrieve_list_stmt (retrieve_list_stmt ls p1) p2.
Proof.
  induction p1; simpl.
  trivial.
  destruct a.
  eauto.
Qed.


Section Stack_invariant.

  Variable heap : PTree.t (Object.t).
  Variable deallocated_objects : list positive.        

Inductive stack_invariant : forall called_by_destr_body : bool,  list (StackFrame.t A nativeop) ->
  (* transmission of variables across stack frames *)
  option (option (PTree.t (Value.t A)) * positive * PTree.t (value A) * option ((positive * positive * bool) * option (ident * FieldSignature.t A))) ->
list (Interm.frame A nativeop) -> Prop := 
| stack_invariant_Kconstr : forall fr obj ar i h p tinit init body k k2 b bases,
  fr = StackFrame.Kconstr obj ar i (h, p) tinit init body k k2 b bases ->
  forall o, heap ! obj = Some o ->
    forall X class, valid_relative_pointer (Program.hierarchy prog) (Object.class o) (Object.arraysize o) ar X i h p class ->
      forall vars vars', vars_invariant vars vars' ->
        forall curobj hp, vars' ! (compile_var (Newvar curobj)) = Some (Val (Value.ptr (Value.subobject obj ar i h p hp))) ->
          forall curpath, Plt curobj curpath -> vars' ! (compile_var (Newvar curpath)) = Some (Path _ X h p) ->
            forall midvar,
              Plt curpath midvar ->
            forall fr' be,
              fr' = Block None (compile_constr (if path_eq_dec (h, p) (Class.Inheritance.Repeated, class :: nil) then true else false) k2 bases class tinit init body curobj curpath midvar :: be) ->
              forall newobj newpath newfield maxvar,
                match k as k' return Constructor.init_key_item _ k' -> Constructor.init_key_secondary k' -> _ with
                  | Constructor.field => fun f _ => newobj = curobj /\ newpath = curpath /\ midvar = maxvar /\ be = nil /\ exists cn, last p = Some cn /\ newfield = Some (cn, f)
                  | Constructor.base => fun ba k2' =>
                    newfield = None /\ Plt midvar newobj /\ Plt newobj newpath /\ Plt newpath maxvar /\
                    let h' := match k2' with Constructor.direct_non_virtual => h | _ => Class.Inheritance.Shared end in
                      let p' := match k2' with
                                  | Constructor.direct_non_virtual => p ++ ba :: nil
                                  | Constructor.virtual => ba :: nil
                                end in
                      vars' ! (compile_var (Newvar newpath)) = Some (Path _ X h' p') /\
                      be = nil (* match k2' with
                             | Constructor.direct_non_virtual => nil
                             | Constructor.virtual => compile_constr_non_virtual_part (if path_eq_dec (h, p) (Class.Inheritance.Repeated, class :: nil) then true else false) class tinit init body curobj curpath midvar :: nil
                           end *) /\
                      exists hp',
                        vars' ! (compile_var (Newvar newobj)) = Some  (Val (Value.ptr (Value.subobject obj ar i h' p' hp')))
                end b k2 ->
              forall stk stk',
                stack_invariant false stk None stk' ->
                stack_invariant false (fr :: stk) (Some (Some vars, maxvar, vars', Some ((newobj, newpath, false), newfield))) (fr' :: stk')               

| stack_invariant_Kconstrarray : forall fr obj ar n i cn tinit vars,
  fr = StackFrame.Kconstrarray obj ar n i cn tinit ->
  forall o, heap ! obj = Some o ->
    valid_array_path (Program.hierarchy prog) cn n (Object.class o) (Object.arraysize o) ar ->
      0 <= i < n ->
      forall vars', vars_invariant vars vars' ->
        forall blockvar hp, vars' ! (compile_var (Newvar blockvar)) = Some (Val (Value.ptr (Value.subobject obj ar 0 Class.Inheritance.Repeated (cn :: nil) hp))) ->
          forall minvar, Plt minvar blockvar ->
            forall index, Plt  blockvar index ->
(*              forall ty va,
                vars' ! (compile_var (Newvar index)) = Some (Val (Value.atom ty va)) ->
                semZ sem va = Some i -> *)
                forall newobj, Plt index newobj ->
              forall hp'', vars' ! (compile_var (Newvar newobj)) = Some (Val (Value.ptr (Value.subobject obj ar i Class.Inheritance.Repeated (cn :: nil) hp''))) ->
                forall newpath, Plt newobj newpath ->
                  vars' ! (compile_var (Newvar newpath)) = Some (Path _ cn Class.Inheritance.Repeated (cn :: nil)) ->
                  forall maxvar, Plt newpath maxvar ->
                    forall fr',
                      fr' = Block None (compile_constrarray tinit cn n blockvar index newobj newpath maxvar (i+1) :: nil) ->
                      forall bo stk stk' so,
                        stack_invariant bo stk  (Some (Some vars, minvar, vars', so)) stk' ->
                        stack_invariant false (fr :: stk) (Some (Some vars, maxvar, vars', Some ((newobj, newpath, true), None))) (fr' :: stk')

| stack_invariant_Kconstrother : forall fr obj ar i h p tinit init body vars1 k k2 b bases,
  fr = StackFrame.Kconstrother obj ar i (h, p) tinit init body vars1 k k2 b bases ->
  forall o, heap ! obj = Some o ->
    forall X class, valid_relative_pointer (Program.hierarchy prog) (Object.class o) (Object.arraysize o) ar X i h p class ->
      forall vars0 vars', vars_invariant vars0 vars' ->
        forall curobj hp, vars' ! (compile_var (Newvar curobj)) = Some (Val (Value.ptr (Value.subobject obj ar i h p hp))) ->
          forall curpath, Plt curobj curpath -> vars' ! (compile_var (Newvar curpath)) = Some (Path _ X h p) ->         
            forall maxvar, Plt curpath maxvar ->
              forall fr1, match k with
                            | Constructor.field => fr1 = nil
                            | Constructor.base => exists stl, fr1 = Callframe (exit _ _ 1%nat :: stl) vars' None :: nil
                          end ->
            forall fr' stk' be,
              fr' = fr1 ++ Block None (compile_constr (if path_eq_dec (h, p) (Class.Inheritance.Repeated, class :: nil) then true else false) k2 bases class tinit init body curobj curpath maxvar :: be) :: stk' ->
              be = nil (*
              match k as k' return Constructor.init_key_secondary k' -> _ with
                | Constructor.field => fun _ => nil
                | Constructor.base => fun k'2 => 
                  match k'2 with
                    | Constructor.direct_non_virtual => nil
                    | Constructor.virtual => compile_constr_non_virtual_part (if path_eq_dec (h, p) (Class.Inheritance.Repeated, class :: nil) then true else false) class tinit init body curobj curpath maxvar :: nil
                  end
              end k2 *) ->
              forall so,
                match k with
                  | Constructor.base => vars0 = vars1
                  | Constructor.field => so = Some (Some vars0, maxvar, vars', None)
                end ->
                forall stk,
                  stack_invariant false stk None stk' ->
                  stack_invariant false (fr :: stk) so fr'

| stack_invariant_Kconstrothercells : forall fr obj ar n i cn tinit vars,
  fr = StackFrame.Kconstrothercells obj ar n i cn tinit vars ->
      forall vars', vars_invariant vars vars' ->
        forall blockvar hp, vars' ! (compile_var (Newvar blockvar)) = Some (Val (Value.ptr (Value.subobject obj ar 0 Class.Inheritance.Repeated (cn :: nil) hp))) ->
          forall minvar, Plt minvar blockvar ->
            forall index, Plt  blockvar index ->
              forall newobj, Plt index newobj ->
                forall newpath, Plt newobj newpath ->
                  forall maxvar, Plt newpath maxvar ->
                    forall fr' stl stk',
                      fr' = Callframe (exit _ _ 1%nat :: stl) vars' None :: Block None (compile_constrarray tinit cn n blockvar index newobj newpath maxvar (i+1) :: nil) :: stk' ->
                      forall bo stk so',
                        stack_invariant bo stk (Some (Some vars, minvar, vars', so')) stk' ->
                        forall so,
                        stack_invariant false (fr :: stk) so fr'

| stack_invariant_Kreturnfromcall : forall fr ores vars further blocks,
  fr = StackFrame.Kreturnfromcall ores vars further blocks ->
  forall bo q q' curobjpathfield minvar maxvar vars',  
    block_invariant heap vars' curobjpathfield bo minvar maxvar blocks q' q ->
    vars_invariant vars vars' ->
    forall ores', ores' = match ores with
                            | None => None
                            | Some res => Some (compile_var (Oldvar res))
                          end ->
    forall fr' stk',
      fr' = Callframe (map (compile (Context maxvar curobjpathfield q' O bo)) further ++                               (compile_discard 1%nat q' maxvar (Interm.exit _ _ 1%nat)) :: nil) vars' ores' :: q ++ stk' ->
      forall stk ,
        stack_invariant bo stk (Some (Some vars, minvar, vars', curobjpathfield)) stk' ->
        forall so,
        stack_invariant false (fr :: stk) so (fr')

| stack_invariant_Kdestr :
forall fr obj ar i h p,
  fr = StackFrame.Kdestr obj ar i (h, p) ->
  forall o, heap ! obj = Some o ->
    forall X class, valid_relative_pointer (Program.hierarchy prog) (Object.class o) (Object.arraysize o) ar X i h p class ->
      forall vars vars',
        vars_invariant vars vars' ->
        forall curobj hp, vars' ! (compile_var (Newvar curobj)) = Some (Val (Value.ptr (Value.subobject obj ar i h p hp))) ->
          forall curpath, Plt curobj curpath -> vars' ! (compile_var (Newvar curpath)) = Some (Path _ X h p) ->         
            forall maxvar,
              Plt curpath maxvar ->
              forall fr',
                fr' = Block None (compile_destr_all_fields (if path_eq_dec (h, p) (Class.Inheritance.Repeated, class :: nil) then true else false) class curobj curpath maxvar :: nil) ->
                forall stk stk',
                  stack_invariant false stk None stk' ->
                  stack_invariant true (fr :: stk) (Some (Some vars, maxvar, vars', None)) (fr' :: stk')

| stack_invariant_Kdestrcell : forall fr obj ar i cn,
  fr = StackFrame.Kdestrcell obj ar i cn ->
  forall vars',
    forall blockvar hp, vars' ! (compile_var (Newvar blockvar)) = Some (Val (Value.ptr (Value.subobject obj ar 0 Class.Inheritance.Repeated (cn :: nil) hp))) ->
      forall minvar, Plt minvar blockvar ->
        forall index, Plt  blockvar index ->
          forall newobj, Plt index newobj ->
            forall newpath, Plt newobj newpath ->
              forall fr' stl,
                fr' = Callframe (compile_destrarray_aux cn blockvar index newobj newpath (exit _ _ 1%nat) (i-1) :: stl) vars' None ->
                forall bo stk stk' oo,
                  stack_invariant bo stk (Some (None, minvar, vars', oo)) stk' ->
                  stack_invariant false (fr :: stk) None (fr' :: stk')

| stack_invariant_Kdestrother : forall fr obj ar i h p k k2 base other,
  fr = StackFrame.Kdestrother obj ar i (h, p) k k2 base other ->
  forall o, heap ! obj = Some o ->
    forall X class, valid_relative_pointer (Program.hierarchy prog) (Object.class o) (Object.arraysize o) ar X i h p class ->
      forall vars',
        forall curobj hp, vars' ! (compile_var (Newvar curobj)) = Some (Val (Value.ptr (Value.subobject obj ar i h p hp))) ->
          forall curpath, Plt curobj curpath -> vars' ! (compile_var (Newvar curpath)) = Some (Path _ X h p) ->
            forall maxvar, Plt curpath maxvar ->
              forall fr' so,
                match k with
                  | Constructor.base => fr' = Callframe (compile_destr (if path_eq_dec (h, p) (Class.Inheritance.Repeated, class :: nil) then true else false) k2 other class curobj curpath maxvar :: nil) vars' None /\ so = None
                  | Constructor.field => fr' = Block None (compile_destr (if path_eq_dec (h, p) (Class.Inheritance.Repeated, class :: nil) then true else false) k2 other class curobj curpath maxvar :: nil) /\ so = Some (None, maxvar, vars', None)
                end ->
                forall s1,
                s1 = match k as k' return Constructor.init_key_secondary k' -> _ with
                       | Constructor.base => fun k'2 => match k'2 with Constructor.virtual  => StackFrame.Kdestrcell obj ar (i) X :: nil | _ => nil
                                                        end
                       | _ => fun _ => nil
                     end k2 ->
                forall stk stk',
                  stack_invariant false (s1 ++ stk) None stk' ->   
                  stack_invariant false (fr :: stk) so (fr' :: stk')

| stack_invariant_Kcontinue : forall fr k stm obj stl blocks,
  fr = StackFrame.Kcontinue k stm obj stl blocks ->
  forall o, heap ! obj = Some o ->
    forall vars vars',
      vars_invariant vars vars' ->
      forall p
        q' midvar maxvar curobjpathfield bo so,
        match k with
          | StackFrame.continue_constr =>
            so = Some vars /\
            exists blockvar,
              Plt midvar blockvar /\
              Plt blockvar maxvar /\
              exists hp,
                vars' ! (compile_var (Newvar blockvar)) = Some (Val (Value.ptr (Value.subobject obj nil 0 Class.Inheritance.Repeated (Object.class o :: nil) hp))) /\
                p = Interm.Block None (compile' (Context maxvar curobjpathfield (Some (blockvar, midvar, (Object.class o, Object.arraysize o)) :: q') O bo) stm :: nil)
                :: Interm.Block (Some obj) (map (compile (Context midvar curobjpathfield q' O bo)) stl ++ (compile_discard 1%nat q' midvar (Interm.exit _ _ 1%nat)) :: nil)
                :: nil
          | StackFrame.continue_destr varsd =>
            midvar = maxvar /\
            varsd = vars /\
            so = None /\
            exists stm', Cppsem.exit_succ stm = Some stm' /\
            exists p', exists fur',
              p = Block None (compile (Context maxvar curobjpathfield q' (S (length p')) bo) stm' :: fur')               
              :: map (fun ob : _ * _ => let (o, b) := ob in Block o b) p'
              ++
              Block (Some obj) (map (compile (Context midvar curobjpathfield q' O bo)) stl          ++ (compile_discard 1%nat q' midvar (Interm.exit _ _ 1%nat)) :: nil
) :: nil /\ forall o b, In (Some o, b) p' -> In o deallocated_objects
        end ->
        forall q minvar,
          block_invariant heap vars' curobjpathfield bo minvar midvar blocks q' q ->
          forall stk' stk'',
            stk'' = p ++ q ++ stk' ->
            forall stk,
              stack_invariant bo stk (Some (Some vars, minvar, vars', curobjpathfield)) stk' ->
              stack_invariant false (fr :: stk) (Some (so, maxvar, vars', None)) stk''

| stack_invariant_nil : 
  forall so,
    stack_invariant false nil so nil
.   

Lemma stack_invariant_oldvar : forall bo stk so stk',
  stack_invariant bo stk so stk' ->
  forall vars minvar vars' curobjpathfield, so = Some (Some vars, minvar, vars', curobjpathfield) ->
    forall var val, stack_invariant bo stk (Some (Some (PTree.set var val vars), minvar, PTree.set (compile_var (Oldvar var)) (Val val) vars', curobjpathfield)) stk'.
Proof.
  induction 1; try (intros; discriminate); injection 1; intros; subst; simpl in *.

  (* Kconstr *)
  destruct k; invall; subst.
   (* base *)
   eapply stack_invariant_Kconstr.
   reflexivity.
   eassumption.
   eassumption.
   eauto using vars_invariant_oldvar.   
   rewrite PTree.gso. eassumption.
   apply compile_var_other.  congruence.
   eassumption.
   rewrite PTree.gso. assumption.
   apply compile_var_other. congruence.
   eassumption.
   reflexivity.
   simpl.
   split; trivial.
   split; trivial.
   split; trivial.
   split; trivial.
   split.
    rewrite PTree.gso. assumption.
    apply compile_var_other. congruence.
   split; trivial.
   rewrite PTree.gso. eauto.
   apply compile_var_other. congruence.
   assumption.
  (* field *)
  eapply stack_invariant_Kconstr.
  reflexivity.
  eassumption.
  eassumption.
  eauto using vars_invariant_oldvar.
  rewrite PTree.gso. eassumption.
  apply compile_var_other. congruence.
  eassumption.
  rewrite PTree.gso. eassumption.
  apply compile_var_other. congruence.
  eassumption.
  reflexivity.
  simpl.
  eauto 8.
  assumption.

(* Kconstrarray *)
  eapply stack_invariant_Kconstrarray.
  reflexivity.
  eassumption.
  assumption.
  assumption.
  eauto using vars_invariant_oldvar.
  rewrite PTree.gso. eassumption.
  apply compile_var_other. congruence.
  eassumption. eassumption. assumption.
  rewrite PTree.gso. eassumption.
  apply compile_var_other. congruence.
  assumption.
  rewrite PTree.gso. assumption.
  apply compile_var_other. congruence.
  assumption. reflexivity.
  eauto.

(* Kconstrother *)
destruct k.
 (* base *)
 subst. 
 eapply stack_invariant_Kconstrother.
 reflexivity.  eassumption.  eassumption.
 7 : simpl; reflexivity.
 7 : simpl; reflexivity.
 eassumption.
 eassumption.
 assumption.
 assumption.
 assumption.
 assumption.
 reflexivity.
 assumption.
(* field *)
subst.
injection H10; intros; subst.
eapply stack_invariant_Kconstrother.
reflexivity. eassumption. eassumption.
6 : simpl; reflexivity.
6 : simpl; reflexivity.
6 : simpl; reflexivity.
6 : simpl; reflexivity.
eauto using vars_invariant_oldvar.
rewrite PTree.gso. eassumption.
apply compile_var_other. congruence.
assumption.
rewrite PTree.gso. eassumption.
apply compile_var_other. congruence.
assumption. assumption.

(* Kconstrothercells *)
eapply stack_invariant_Kconstrothercells.
reflexivity.
8 : reflexivity.
assumption.
eassumption.
eassumption.
assumption.
assumption.
assumption.
assumption.
eassumption.

(* Kreturnfromcall *)
eapply stack_invariant_Kreturnfromcall.
reflexivity.
3 : reflexivity.
3 : reflexivity.
eassumption.
assumption.
assumption.

(* Kdestr *)
eapply stack_invariant_Kdestr.
reflexivity.
eassumption.
eassumption.
eauto using vars_invariant_oldvar.
rewrite PTree.gso. eassumption.
apply compile_var_other. congruence.
eassumption.
rewrite PTree.gso. eassumption.
apply compile_var_other. congruence.
assumption. reflexivity. assumption.

(* Kdestrother *)
destruct k; invall; try discriminate.

(* Kcontinue *)
destruct k; invall; subst; try discriminate.
injection H; intros; subst.
 eapply stack_invariant_Kcontinue.
 reflexivity.
 eassumption.
 eauto using vars_invariant_oldvar.
 simpl.
 split; trivial.
 esplit.
 split.
  2 : split; try eassumption.
 eassumption.
 esplit.
 split.
 rewrite PTree.gso. eassumption.
 apply compile_var_other. congruence.
 reflexivity.
 eapply block_invariant_oldvar.
 eassumption.
 reflexivity.
 eauto.

 (* nil *)
 constructor.

Qed.


Ltac differt :=
  match goal with
    |- (PTree.set (compile_var (Newvar ?var)) _ _) ! _ = _ =>
      rewrite PTree.gso; [ eassumption |
        apply compile_var_other; intro Habs; injection Habs; intro; subst; destruct (Plt_irrefl var); repeat (eassumption || eapply Plt_trans)
      ]
  end.

Lemma stack_invariant_newvar_lt : forall bo stk so stk',
  stack_invariant bo stk so stk' ->
  forall ovars minvar vars' oo, so = Some (ovars, minvar, vars', oo) ->
    forall var, Plt minvar var -> forall val, stack_invariant bo stk (Some (ovars, minvar, PTree.set (compile_var (Newvar var)) (val) vars', oo)) stk'.
Proof.
  induction 1; try (intros; discriminate); injection 1; intros; subst.

(* Kconstr *)
destruct k; invall; subst.
 (* base *)
 simpl in H13.
 invall; subst.
 eapply stack_invariant_Kconstr.
 reflexivity.
 eassumption.
 eassumption.
 eauto using vars_invariant_newvar.
 differt.
eassumption.
differt.
eassumption.
reflexivity.
simpl.
split; trivial.
split; trivial.
split; trivial.
split; trivial.
split.
differt.
split; trivial.
esplit.
differt.
assumption.
(* field *)
 eapply stack_invariant_Kconstr.
 reflexivity.
 eassumption.
 eassumption.
 eauto using vars_invariant_newvar.
 differt.
eassumption.
 differt.
 eassumption.
 reflexivity.
 simpl.
 eauto 8.
 assumption.

(* Kconstrarray *)
eapply stack_invariant_Kconstrarray.
reflexivity.
eassumption.
assumption.
assumption.
eauto using vars_invariant_newvar.
differt.
eassumption.
eassumption.
assumption.
differt.
assumption.
differt.
assumption.
reflexivity.
eauto 8 using Plt_trans.

(* Kconstrother *)
destruct k; invall; subst.
 (* base *)
 eapply stack_invariant_Kconstrother; simpl; eauto; simpl; eauto.
 simpl; reflexivity.
(* field *)
injection H10; intros; subst.
eapply stack_invariant_Kconstrother.
reflexivity.
eassumption.
eassumption.
6 : simpl; reflexivity.
7 : simpl; reflexivity.
7 : simpl; reflexivity.
eauto using vars_invariant_newvar.
differt.
eassumption.
differt.
assumption.
reflexivity.
assumption.

(* Kconstrothercells *)
eapply stack_invariant_Kconstrothercells; eauto.

(* Kreturnfromcall *)
eapply stack_invariant_Kreturnfromcall; eauto.

(* Kdestr *)
eapply stack_invariant_Kdestr.
reflexivity.
eassumption.
eassumption.
eauto using vars_invariant_newvar.
differt.
eassumption.
differt.
assumption.
reflexivity.
assumption.

(* Kdestrother *)
destruct k; invall; subst; try discriminate.
(* field *)
injection H7; intros; subst.
eapply stack_invariant_Kdestrother.
reflexivity.
eassumption.
eassumption.
Focus 5.
simpl.
split.
 reflexivity.
reflexivity.
differt.
assumption.
differt.
assumption.
simpl; reflexivity.
assumption.

(* Kcontinue *)
destruct k; invall; subst.
 (* constr *)
 eapply stack_invariant_Kcontinue.
 reflexivity.
 eassumption.
 Focus 2.
  simpl.
  split.
   reflexivity.
  esplit.
  split.
   2 : split; try eassumption.
   eassumption.
  esplit.
  split.
  differt.
  reflexivity.
 eauto using vars_invariant_newvar.
 eapply block_invariant_newvar_gt.
 eassumption.
 eauto using Plt_trans.
 reflexivity.
 generalize (block_invariant_minvar_le_maxvar H3).
 intro.
 eauto 8 using Plt_trans, Ple_Plt_trans, Plt_Ple_trans.
(* destr *)
eapply stack_invariant_Kcontinue.
reflexivity.
eassumption.
Focus 2.
 simpl.
 split.
  eauto.
 split.
  reflexivity.
 split.
  trivial.
 esplit.
 split.
  eassumption.
 eauto.
eauto using vars_invariant_newvar.
eapply block_invariant_newvar_gt.
eassumption.
eauto using block_invariant_newvar_gt, Plt_trans.
reflexivity.
generalize (block_invariant_minvar_le_maxvar H3).
intro.
eauto 8 using Plt_trans, Ple_Plt_trans, Plt_Ple_trans.

(* nil *)
constructor.

Qed.

End Stack_invariant.


Lemma stack_invariant_heap_new : forall heap deallo bo stk so stk',
  stack_invariant heap deallo bo stk so stk' ->
  forall obj, heap ! obj = None -> forall o,
    stack_invariant (PTree.set obj o heap) deallo bo stk so stk'.
Proof.
  induction 1; simpl; intros.
  (* Kconstr *)
  eapply stack_invariant_Kconstr; try eassumption.
  rewrite PTree.gso at 1; congruence.
  eauto.
  (* Kconstrarray *)
  eapply stack_invariant_Kconstrarray; try eassumption.
  rewrite PTree.gso at 1; congruence.
  eauto.
  (* Kconstrother *)
  eapply stack_invariant_Kconstrother; try eassumption.
  rewrite PTree.gso at 1; congruence.
  eauto.
  (* Kconstrothercells *)
  eapply stack_invariant_Kconstrothercells; try eassumption.
  eauto.
  (* Kreturnfromcall *)
  eapply stack_invariant_Kreturnfromcall; try eassumption.
  eauto using block_invariant_heap_new.
  eauto.
  (* Kdestr *)
  eapply stack_invariant_Kdestr; try eassumption.
  rewrite PTree.gso at 1; congruence.
  eauto.
  (* Kdestrcell *)
  eapply stack_invariant_Kdestrcell; try eassumption.
  eauto.
  (* Kdestrother *)
  eapply stack_invariant_Kdestrother; try eassumption.
  rewrite PTree.gso at 1; congruence.
  eauto.
  (* Kcontinue *)
  eapply stack_invariant_Kcontinue; try eassumption.
  rewrite PTree.gso at 1; congruence.
  eauto using block_invariant_heap_new.
  eauto.
  (* nil *)
  constructor.
Qed.

Lemma stack_invariant_dealloc_cons : forall heap dealloc bo stk so stk',
  stack_invariant heap dealloc bo stk so stk' ->
  forall obj,
    stack_invariant heap (obj :: dealloc) bo stk so stk'.
Proof.
  induction 1; simpl; intros.
  eapply stack_invariant_Kconstr; eauto.
  eapply stack_invariant_Kconstrarray; eauto.
  eapply stack_invariant_Kconstrother; eauto.
  eapply stack_invariant_Kconstrothercells; eauto.
  eapply stack_invariant_Kreturnfromcall; eauto.
  eapply stack_invariant_Kdestr; eauto.
  eapply stack_invariant_Kdestrcell; eauto.
  eapply stack_invariant_Kdestrother; eauto.
  (* Kcontinue *)
  destruct k.   
   eapply stack_invariant_Kcontinue; eauto; simpl; eauto.
  (* destr *)
  invall; subst; simpl in *.
  eapply stack_invariant_Kcontinue.
  reflexivity.
  eassumption.
  eassumption.
  simpl.
  split. 
   eauto.
  split; trivial.
  split; trivial.
  exists x.
  split.
   assumption.
  esplit.
  esplit.
  eauto.
  eassumption.
  reflexivity.
  eauto.
  (* nil *)
  constructor.
Qed.

Inductive state_invariant : State.t A nativeop -> Interm.state A nativeop -> Prop := 

| state_invariant_constr : forall s obj ar i h p tinit init body vars k k2 bases,
  State.kind s = State.constr obj ar i (h, p) tinit init body vars k k2 bases ->
  forall o, (Globals.heap (State.global s)) ! obj = Some o ->
    forall X class, valid_relative_pointer (Program.hierarchy prog) (Object.class o) (Object.arraysize o) ar X i h p class ->
      forall vars', vars_invariant vars vars' ->
        forall curobj hp, vars' ! (compile_var (Newvar curobj)) = Some (Val (Value.ptr (Value.subobject obj ar i h p hp))) ->        
          forall curpath, Plt curobj curpath -> vars' ! (compile_var (Newvar curpath)) = Some (Path _ X h p) ->         
            forall maxvar, Plt curpath maxvar ->
            forall s',
              Interm.current s' = compile_constr (if path_eq_dec (h, p) (Class.Inheritance.Repeated, class :: nil) then true else false) k2 bases class tinit init body curobj curpath maxvar ->
              Interm.further s' = nil (*
              match k as k' return Constructor.init_key_secondary k' -> _ with
                | Constructor.field => fun _ => nil
                | Constructor.base => fun k2' =>
                  match k2' with
                    | Constructor.direct_non_virtual => nil
                    | Constructor.virtual => compile_constr_non_virtual_part (if path_eq_dec (h, p) (Class.Inheritance.Repeated, class :: nil) then true else false) class tinit init body curobj curpath maxvar :: nil
                  end
              end k2  *)
              ->
              Interm.vars s' = vars' ->
              stack_invariant (Globals.heap (State.global s)) (State.deallocated_objects s) false (State.stack s) None (Interm.stack s') ->   
              state_invariant s s'

| state_invariant_constr_array : forall s obj ar n i cn tinit vars,
  State.kind s = State.constr_array obj ar n i cn tinit vars ->
  forall o, (Globals.heap (State.global s)) ! obj = Some o ->
    valid_array_path (Program.hierarchy prog) cn n (Object.class o) (Object.arraysize o) ar ->
      0 <= i <= n ->
(*       0 < n -> *)
      forall vars', vars_invariant vars vars' ->
        forall blockvar hp, vars' ! (compile_var (Newvar blockvar)) = Some (Val (Value.ptr (Value.subobject obj ar 0 Class.Inheritance.Repeated (cn :: nil) hp))) ->
          forall minvar, Plt minvar blockvar ->
            forall index, Plt  blockvar index ->
              forall newobj', Plt index newobj' ->
                forall newpath', Plt newobj' newpath' ->
                  forall maxvar', Plt newpath' maxvar' ->
                    forall s',
                      Interm.current s' = compile_constrarray tinit cn n blockvar index newobj' newpath' maxvar' i ->
                      Interm.further s' = nil ->
                      Interm.vars s' = vars' ->
                      forall bo curobjpathfield,
                        stack_invariant (Globals.heap (State.global s)) (State.deallocated_objects s) bo (* false *) (State.stack s) (Some (Some vars, minvar, vars', curobjpathfield))  (Interm.stack s') ->
                        state_invariant s s'

| state_invariant_codepoint : forall s vars cur fur blocks,
  State.kind s = State.codepoint vars cur fur blocks ->
  forall q q' curobjpathfield minvar maxvar vars' bo,  
    block_invariant (Globals.heap (State.global s)) vars' curobjpathfield bo minvar maxvar blocks q' q ->
      forall p
        (Hp_dealloc : forall o b, In (Some o, b) p -> In o (State.deallocated_objects s))
        s',
        ((if requires_destruct cur then True else cur = Sexit O) \/ p = nil) ->
        Interm.current s' = compile (Context maxvar curobjpathfield q' (length p) bo) cur ->
        ((requires_destruct cur) = (true) \/ retrieve_list_stmt (Interm.further s') p = map (compile (Context maxvar curobjpathfield q' O bo)) fur ++ (compile_discard 1%nat q' maxvar (Interm.exit _ _ 1%nat)) :: nil) ->
        vars_invariant vars vars' ->
        Interm.vars s' = vars' ->
        forall r,
        Interm.stack s' = map (fun ob : _ * _ => let (o, b) := ob in Block o b) p ++ q ++ r ->
        stack_invariant (Globals.heap (State.global s)) (State.deallocated_objects s) bo (State.stack s) (Some (Some vars, minvar, vars', curobjpathfield)) r ->   
        state_invariant s s'

| state_invariant_destr : forall s obj ar i h p k k2 bases,
  State.kind s = State.destr obj ar i (h, p) k k2 bases ->
  forall o, (Globals.heap (State.global s)) ! obj = Some o ->
    forall X class, valid_relative_pointer (Program.hierarchy prog) (Object.class o) (Object.arraysize o) ar X i h p class ->
      forall vars' curobj hp, vars' ! (compile_var (Newvar curobj)) = Some (Val (Value.ptr (Value.subobject obj ar i h p hp))) ->        
          forall curpath, Plt curobj curpath -> vars' ! (compile_var (Newvar curpath)) = Some (Path _ X h p) ->         
            forall maxvar, Plt curpath maxvar ->
            forall s',
              Interm.current s' = compile_destr (if path_eq_dec (h, p) (Class.Inheritance.Repeated, class :: nil) then true else false) k2 bases class curobj curpath maxvar ->
              Interm.further s' = nil ->
              Interm.vars s' = vars' ->
              forall s1,
                s1 = match k as k' return Constructor.init_key_secondary k' -> _ with
                       | Constructor.base => fun k'2 => match k'2 with Constructor.virtual  => StackFrame.Kdestrcell obj ar (i) X :: nil | _ => nil
                                                        end
                       | _ => fun _ => nil
                     end k2 ->
                stack_invariant (Globals.heap (State.global s)) (State.deallocated_objects s) false (s1 ++ State.stack s) None (Interm.stack s') ->   
                state_invariant s s'

| state_invariant_destrarray : forall s obj ar i cn,
  State.kind s = State.destr_array obj ar i cn ->
  forall o, (Globals.heap (State.global s)) ! obj = Some o ->
    forall n,
    valid_array_path (Program.hierarchy prog) cn n (Object.class o) (Object.arraysize o) ar ->
    (* 0 < n -> *)
      forall vars' blockvar hp, vars' ! (compile_var (Newvar blockvar)) = Some (Val (Value.ptr (Value.subobject obj ar 0 Class.Inheritance.Repeated (cn :: nil) hp))) ->
          forall minvar, Plt minvar blockvar ->
          forall index, Plt  blockvar index ->
            forall newobj', Plt index newobj' ->
              forall newpath', Plt newobj' newpath' ->
                  forall s',
                    Interm.current s' = (compile_destrarray_aux cn blockvar index newobj' newpath' (exit _ _ 1%nat) (i)) ->
                    Interm.vars s' = vars' ->
                    forall bo curobjpathfield,
                      stack_invariant (Globals.heap (State.global s)) (State.deallocated_objects s) bo (State.stack s) (Some (None, minvar, vars', curobjpathfield)) (Interm.stack s') ->
                      state_invariant s s'

.

Function exitable (s : stmt A nativeop) (n : nat) {struct s} : option (stmt A nativeop) :=
  match s with
    | exit n' => if le_lt_dec n n' then Some (exit _ _ (n' - n)) else None
    | ret ovar => Some (ret _ _ ovar)
    | _ => None
  end.

Lemma exitable_O : forall s s', exitable s O = Some s' -> s = s'.
Proof.
  functional inversion 1; try congruence.
  replace (n' - 0)%nat with n' by omega.
  trivial.
Qed.  

Lemma exitable_S : forall n stm stm', exitable stm (S n) = Some stm' ->
  exists stm1, exit_succ stm = Some stm1 /\ exitable stm (S n) = exitable stm1 n.
Proof.
  functional inversion 1; try (simpl; eauto; fail).
  subst.
  rewrite H.
  destruct n'.
   omegaContradiction.
  simpl.
  esplit.
  split.
  reflexivity.
  simpl.
  destruct (le_lt_dec n n').
   reflexivity.
  omegaContradiction.
Qed.

Variable is_primary_path : list ident -> bool.

Variable prog' : Interm.program A nativeop.

Lemma exit_further : forall p stm stm',
  exitable stm (length p) = Some stm' ->
  forall next_object dyntype field_values heap further vars1 stk,
    exists heap',
      star (evtr sem) (step (sem:=sem) prog' is_primary_path)
      (State stm further vars1
        (map
          (fun ob : option positive * list (stmt A nativeop) =>
            let (o, b) := ob in Block o b) p ++ stk) (Global (Globals.make heap next_object field_values) dyntype)) E0
    (State stm' (retrieve_list_stmt further p) vars1 stk (Global (Globals.make heap' next_object field_values) dyntype)) /\
    forall obj, (exists stl, In (Some obj, stl) p) \/ heap' ! obj = heap ! obj
.
Proof.
  induction p; simpl.
  intros until 1.
  generalize (exitable_O H).
  intros; subst.
  esplit.
  split.
  eleft.
  right; reflexivity.
 intros until 1.
 destruct (exitable_S H).
 destruct H0.
 rewrite H1 in H.
 intros.
 destruct a.
 generalize (step_exit_S_return_cons prog' sem (oobj := o) is_primary_path (refl_equal _) H0 (gl := Globals.make heap next_object field_values)
further l vars1 (
map
                (fun ob : option positive * list (stmt A nativeop) =>
                 let (o0, b) := ob in Block o0 b) p ++ stk
) dyntype
).
 unfold Globals.remove; simpl.
replace (
match o with
           | Some obj =>
               Globals.make (PTree.remove obj heap) next_object field_values
           | None => Globals.make heap next_object field_values
           end
) with (
  Globals.make 
  match o with
    | Some obj => PTree.remove obj heap
    | None => heap
  end
  next_object field_values
) by ( destruct o; reflexivity).
intro.
destruct (IHp _ _ H next_object dyntype field_values 
 match o with
    | Some obj => PTree.remove obj heap
    | None => heap
 end
 l vars1 stk
).
destruct H3.
esplit.
split.
eright.
eassumption.
eassumption.
rewrite E0_left; eauto using evtr_sem.
intro.
destruct (H4 obj).
 destruct H5; eauto.
destruct o; eauto.
destruct (peq obj p0).
 subst.
 eauto.
rewrite PTree.gro in H5; eauto.
Qed.
                    
Lemma map_atom' : forall la,
  map
  (fun a : (sigT (ATOM.val (t := A))) => let (ty, va) := a in Some (Val (Value.atom ty va))) la =
  map (@Some _) (map (@Val _) (map (fun a : sigT (ATOM.val (t := A)) => let (ty, va) := a in Value.atom ty va) la)).
Proof.
  induction la; simpl.
   trivial.
  destruct a.
  congruence.
Qed.

Lemma map_atom : forall la,
  map
  (fun x : sigT (ATOM.val (t := A)) =>
    let (ty, va) := x in Some (Value.atom ty va)) la =
  map (@Some _) (map (fun a : (sigT (ATOM.val (t := A))) => let (ty, va) := a in Value.atom ty va) la).
Proof.
  induction la; simpl.
   trivial.
  destruct a; congruence.
Qed.

Lemma vars_invariant_map : forall v v', vars_invariant v v' ->
  forall lv args, map (@Some _) args = map (fun var => v ! var) lv  ->
    map (@Some _) (map (@Val _) args) = map (fun var => v' ! var) (map (fun var => compile_var (Oldvar var)) lv).
Proof.
  intros until 1.
  induction lv; destruct args; simpl; try (intro; congruence).
  injection 1; intros; subst.
  rewrite (IHlv _ H1).
  symmetry in H2.
  rewrite (H _ _ H2).
  reflexivity.
Qed.  

Lemma constructed_field_not_deallocated : forall s, Invariant.invariant prog s -> 
  forall obj ar i h p hp,
    valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s)) (Value.subobject obj ar i h p hp) ->
    forall cn, last p = Some cn ->
      forall c, (Program.hierarchy prog) ! cn = Some c ->
        forall fs, In fs (Class.fields c) ->
          assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, (h, p), fs) (State.field_construction_states s) = Some Constructed ->
          In obj (State.deallocated_objects s) -> False.
Proof.
 inversion 2; subst.
 intros. 
 destruct (inclusion_subobject_of_full_object H7).
 destruct H8.
 generalize (deallocated_objects_destructed H H6 H3 H8).
 intros.
 generalize (construction_includes_destructed (inclusion_construction_order H H3 H9) H10).
 intro.
 assert (
   Some DestructingBases =<
assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (h, p)))
          (State.construction_states s)
 ).
  unfold_ident_in_all.
   rewrite H11; simpl; omega.
 generalize ( constructed_field_child_of_destructed (construction_states_fields H H0 H1 H2 H4) H12).
 unfold_ident_in_all.
 congruence.
Qed.

Corollary get_field_scalar_some_not_deallocated_object :
  forall s, scalar_fields_some_constructed prog s -> invariant prog s ->
    forall obj ar i h p hp, valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s)) (Value.subobject obj ar i h p hp) -> forall cn, last p = Some cn ->
      forall c, (Program.hierarchy prog) ! cn = Some c ->
        forall fs, In fs (Class.fields c) ->
          forall ty, FieldSignature.type fs = FieldSignature.Scalar ty ->
            forall v, Globals.get_field (Globals.field_values (State.global s)) (obj, ar, i, (h, p), fs) = Some v ->
              In obj (State.deallocated_objects s) -> False.
Proof.
intros.
eapply constructed_field_not_deallocated.
eassumption.
eassumption.
eassumption.
eassumption.
eassumption.
2 : assumption.
unfold scalar_fields_some_constructed in *.
eauto.
Qed.

Lemma vars_invariant_set_params : forall args vargs',
  vars_invariant
  (Cppsem.set_params args vargs')
  (Interm.set_params (map (@Val _) args) (map (fun v => compile_var (Oldvar v)) vargs')).
Proof.
  intros.
  functional induction (Cppsem.set_params args vargs'); simpl.
   eauto using vars_invariant_oldvar.
  unfold vars_invariant.
  intros ? ?.
  rewrite PTree.gempty.
  intro; discriminate.
Qed.

Record invariant (s : State.t A nativeop) (s' : Interm.state A nativeop) : Prop := invariant_intro {
  invariant_state : state_invariant s s';
  invariant_heap : forall obj, In obj (State.deallocated_objects s) \/ (Globals.heap (globals (global s'))) ! obj = (Globals.heap (State.global s)) ! obj
    ;
  invariant_next_object : Globals.next_object (globals (global s')) = Globals.next_object (State.global s)
    ;
  invariant_field_values : forall f v, Globals.get_field (Globals.field_values (State.global s)) f = Some v -> Globals.get_field (Globals.field_values (globals (global s'))) f = Some v
    ;
  invariant_dynamic_type : forall obj ar i sh sp ch cp dh dp,
    Cppsem.dynamic_type (Program.hierarchy prog) (Globals.heap (State.global s)) (State.construction_states s) obj ar i sh sp ch cp dh dp ->
    assoc (@pointer_eq_dec _) (obj, (ar, i, (sh, sp))) (dynamic_type (global s')) = Some ((ch, cp), (dh, dp))
    ;
  invariant_allow_static_cast : forall obj ar i h p hp,
    valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s))  (Value.subobject obj ar i h p hp) ->
 (*
    (Some BasesConstructed =< assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states s)) ->
    In (obj, (ar, i, (h, p))) (allow_static_cast (global s')) *) (** this is WRONG because a vptr can be erased because of a primary base *)
    assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states s) = Some Constructed ->
    assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (dynamic_type (global s')) <> None
    ;
  invariant_inheritance : Invariant.invariant prog s
    ;
  invariant_scalar_fields : scalar_fields_some_constructed prog s  
}.

Lemma invariant_allow_static_cast_strong : forall s s', invariant s s' ->
  forall obj ar i h p hp,
    valid_pointer (Program.hierarchy prog) (Globals.heap (State.global s))  (Value.subobject obj ar i h p hp) ->
    (Some BasesConstructed =< assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states s)) ->
    (assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states s) =< Some StartedDestructing) ->
    assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (dynamic_type (global s')) <> None
.
Proof.
 intros.
 destruct (Z_eq_dec (Z_of_construction_state (assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) (State.construction_states s))) (Z_of_construction_state (Some Constructed))).
  generalize (Z_of_construction_state_inj e); intros; eauto using invariant_allow_static_cast.
inversion H0; subst.
inversion H9; subst.
assert ((Program.hierarchy prog) ! to <> None) by eauto using path_defined_to.
case_eq ((Program.hierarchy prog) ! to); try congruence.
intros.
erewrite invariant_dynamic_type.
2 : eassumption.
2 : eright.
2 : eassumption.
2 : eassumption.
2 : tauto.
2 : eassumption.
2 : reflexivity.
4 : symmetry; eapply concat_trivial_right; eauto.
congruence.
revert H1 H2 n.
sdestruct (
 assoc (pointer_eq_dec (A:=A)) (obj, (ar, i, (h, p)))
     (State.construction_states s) 
); try (simpl ; intros; omegaContradiction).
destruct c; auto; try (simpl; intros; omegaContradiction).
eleft with (lt := nil).
reflexivity.
reflexivity.
simpl.
rewrite H10.
trivial.
Qed.    
  

Lemma true_uniq : forall h1 h2 : True, h1 = h2.
Proof.
  dependent inversion h1.
  dependent inversion h2.
  trivial.
Qed.

Hypothesis prog'_hierarchy : Program.hierarchy prog = Interm.hierarchy prog'.

Hypothesis prog'_constructors : forall cn c, (Program.constructors prog) ! cn = Some c -> forall ty co, assoc (@Program.constructor_key_eq_dec _) ty c = Some co -> forall b,
  (Interm.statics prog') ! (compile_static (Newstatic (compile_constrdestr cn (StaticConstructor ty) b))) = Some (compile_constructor cn co b).

Hypothesis prog'_destructors : forall cn, (Program.hierarchy prog) ! cn <> None -> forall b, (Interm.statics prog') ! (compile_static (Newstatic (compile_constrdestr cn (StaticDestructor) b))) = Some (compile_destructor cn b).

Hypothesis prog'_statics : forall i m, (Program.static_methods prog) ! i = Some m -> (Interm.statics prog') ! (compile_static (Oldstatic i)) = Some (
  Static_fun (map (fun v => compile_var (Oldvar v)) (Static_method.args m)) (compile' (Context  xH None nil O false) (Static_method.code m))
).

Hypothesis prog'_methods : forall i m, (Program.methods prog) ! i = Some m -> (Interm.methods prog') ! i = Some (  
  Interm.Method_body
  (compile_var (Oldvar (Method_body.this m)))
  (map (fun v => compile_var (Oldvar v)) (Cppsem.Method_body.args m)) (compile' (Context xH None nil O false) (Cppsem.Method_body.code m))
).

Hypothesis prog'_main : 
  Interm.main prog' = compile' (Context xH None nil O false) (Program.main prog).

Theorem init : forall st1, Cppsem.initial_state prog st1 ->
  exists st2, Interm.initial_state prog' st2 /\
    exists st2', star _ (Interm.step (sem := sem) prog' is_primary_path) st2 E0 st2' /\
      invariant st1 st2'.
Proof.
  inversion 1; subst.
  esplit.
  split.
  econstructor.
  rewrite prog'_main.
  unfold compile'.
  esplit.
  split.
  eapply star_left.
  econstructor.
  eapply star_refl.
  rewrite E0_left; eauto using evtr_sem.
  constructor; simpl.
   eapply state_invariant_codepoint with (p := nil) (q := nil) (r := nil); simpl.
   reflexivity.
   2 : auto.
   2 : auto.
   2 : reflexivity.
   econstructor.
   constructor.
   simpl; auto.
   unfold vars_invariant.
   intros.
   rewrite PTree.gempty in H0.
   discriminate.
   reflexivity.
   reflexivity.
   constructor.
  auto.
  reflexivity.
  trivial.
  inversion 1; subst; rewrite PTree.gempty in *; discriminate.
  intros; congruence.
  eauto using Preservation.init.
  eauto using init_scalar_fields_some_constructed.
Qed.

Theorem fin : forall st1 st2 (r : outcome (evtr sem)),
  invariant st1 st2 ->
  Cppsem.final_state st1 r ->
  exists st2', star _ (Interm.step (sem := sem) prog' is_primary_path) st2 E0 st2' /\
    Interm.final_state st2' r.
Proof.
  inversion 2; subst.
  destruct st2; simpl in *.
  generalize (invariant_state H).
  inversion 1; subst; try discriminate; simpl in *.
  injection H4; intros; subst; simpl in *.
  inversion H12; subst; simpl in *.
  inversion H5; subst; simpl in *.
  destruct global; simpl in *.
  destruct globals; simpl in *.
  destruct (exit_further
    (p := p) (stm := ret _ _ (Some (compile_var (Oldvar rv)))) (refl_equal _) next_object dynamic_type field_values heap further vars nil).
  invall.
  esplit.
  split.
  eassumption.
  econstructor.
  eauto.
  assumption.
Qed. 


Variable s1 : State.t A nativeop.
Variable t : trace (evtr sem).
Variable s2 : State.t A nativeop.

Variable cppsem : cppsemparam.

Hypothesis Hstep : Cppsem.step prog cppsem s1 t s2.

Variable s1' : state A nativeop.

Variable Hinv : invariant s1 s1'.

Notation goal := (exists s2',
  plus (evtr sem) (Interm.step prog' (sem := sem) is_primary_path) s1' t s2' /\ 
    invariant s2 s2')
  (only parsing).


Remark kind_inj : forall s18 s42 : State.t A nativeop, s18 = s42 ->
  State.kind s18 = State.kind s42.
Proof.
  congruence.
Qed.


Remark stack_inj : forall s18 s42 : State.t A nativeop,
  s18 = s42 ->
  State.stack s18 = State.stack s42.
Proof.
  intros; congruence.
Qed.    



Ltac abs t := (* abstract *) t.

Lemma preservation_requires_destruct : forall vars sdestruct stl0
  stl obj bl stk gl cs auxcs f
  (Hs1 : State.make
         (State.codepoint vars sdestruct stl0
            (BlockPoint.make stl (Some obj) :: bl)) stk gl cs auxcs f = s1)
(Hdestruct : requires_destruct sdestruct = true), 
goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate; try
    match goal with H : State.make (State.codepoint _ _ _ _) _ _ _ _ _ = _ |- _ => injection H; intros; subst; abs discriminate
  end.
injection H3; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H1; intros; subst; simpl in *.
inversion H2; subst; simpl in *.
case_eq (Cppsem.exit_succ cur).
2 : generalize (requires_destruct_exit_succ Hdestruct); intros; contradiction.
intros.
rewrite (compile_exit_succ H5).
replace o0 with o in * by congruence.
esplit.
split.
eapply plus_left.
econstructor.
eapply star_left.
econstructor.
eleft.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
split; simpl; try assumption.
 eapply state_invariant_destrarray; simpl.
 reflexivity.
 eassumption.
 econstructor.
 eauto using object_arraysizes_nonnegative.
 omega.
 eassumption.
 eassumption.
 4 : reflexivity.
 eapply Plt_trans.
 eassumption.
 eapply Plt_succ.
 eapply Plt_succ.
 eapply Plt_succ.
 reflexivity.
 eapply stack_invariant_Kcontinue.
 reflexivity.
 eassumption.
 2 : simpl.
 eassumption.
 split. 
 2: split.
 2: reflexivity.
 2: split.
 2: reflexivity.
 2: esplit.
 2: split.
 2: eassumption.
 2: exists p.
 2: exists  further.
 4 : simpl.
 2: split.
 2: reflexivity.
 2: assumption.
 2: eassumption.
 2: simpl.
 2: rewrite app_ass.
 2: simpl.
 2: reflexivity.
 reflexivity.
assumption.
eauto using Preservation.goal.
Qed. (* slow *)


Lemma preservation_exit_O : forall vars stl0 bl stk gl cs auxcs f
  (Hs1 : State.make (State.codepoint vars (Sexit 0) stl0 bl) stk gl cs auxcs f =  s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  2 : injection H0; intros; subst; discriminate.
  2 : injection H3; intros; subst; discriminate.
injection H; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H0; intros; subst; simpl in *.
destruct H4; try discriminate.
destruct global.
destruct globals.
replace (length p + 0)%nat with (length p) by omega.
assert (exitable (exit _ _ (length p)) (length p) = Some (exit _ _ O)).
 simpl.
 destruct (le_lt_dec (length p) (length p)).
  replace (length p - length p)%nat with O by omega.
  reflexivity.
 omegaContradiction.
destruct (exit_further H4
next_object dynamic_type field_values heap further vars1 (q ++ r)
).
destruct H6.
esplit.
split.
eapply plus_right.
eapply evtr_sem.
eassumption.
econstructor.
repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
eapply state_invariant_codepoint with (p := nil).
reflexivity.
eassumption.
simpl; intros; contradiction.
right; reflexivity.
reflexivity.
right; assumption.
assumption.
reflexivity.
simpl; reflexivity.
assumption.
 simpl.
 intro.
 destruct (H7 obj).
  invall; eauto.
 rewrite H9.
 eauto.
eauto using Preservation.goal.
Qed. (* slow *)


Transparent compile_discard.

Lemma preservation_exit_S_none : forall vars n stl0 stl bl stk gl cs auxcs f
  (Hs1 : State.make
    (State.codepoint vars (Sexit (S n)) stl0
      (BlockPoint.make stl None :: bl)) stk gl cs auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  2 : injection H0; intros; subst; discriminate.
injection H; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H0; intros; subst.
inversion H1; subst.
simpl.
esplit.
split.
eapply plus_left.
econstructor.
eright.
econstructor.
eleft.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
eapply state_invariant_codepoint with (p := p ++ (None, map (compile (Context maxvar0 curobjpathfield0 cbl 0 bo)) stl ++ compile_discard 1 cbl maxvar0 (exit A nativeop 1) :: nil) :: nil).
reflexivity.
eassumption.
 simpl.
 intros.
 destruct (in_app_or _ _ _ H3).
 eauto.
 destruct H6.
  discriminate.
 contradiction.
destruct n; simpl; auto.
unfold compile_discard.
simpl.
rewrite app_length.
simpl.
replace (length p + S n)%nat with (length p + 1 + n)%nat by omega.
reflexivity.
simpl.
rewrite retrieve_list_stmt_app.
simpl.
right.
reflexivity.
assumption.
reflexivity.
simpl.
rewrite map_app.
simpl.
rewrite app_ass.
simpl.
reflexivity.
assumption.
eauto using Preservation.goal.
Qed. (* slow *)

Lemma preservation_skip_nil : forall vars bl stk gl cs auxcs f
  (Hs1: State.make (State.codepoint vars Sskip nil bl) stk gl cs auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  2 : injection H0; intros; subst; discriminate.
  2 : injection H3; intros; subst; discriminate.
injection H; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H0; intros; subst; simpl in *.
destruct H2; try discriminate.
destruct H4; try discriminate.
subst; simpl in *; subst; simpl in *.
esplit.
split.
 eapply plus_left.
 econstructor.
 eleft.
 repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
eapply state_invariant_codepoint with (p := nil).
reflexivity.
eassumption.
eassumption.
auto.
reflexivity.
left; reflexivity.
assumption.
reflexivity.
simpl; reflexivity.
assumption.
eauto using Preservation.goal.
Qed. (* slow *)

Lemma preservation_requires_exit_none : forall vars sexit stl0 stl bl stk gl cs auxcs f 
(Hs1 : State.make
  (State.codepoint vars sexit stl0 (BlockPoint.make stl None :: bl))
  stk gl cs auxcs f = s1
)
(Hrequires_exit : requires_exit sexit = true)
, goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate; try
    match goal with H : State.make (State.codepoint _ _ _ _) _ _ _ _ _ = _ |- _ => injection H; intros; subst; abs discriminate
  end.
injection H0; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H1; intros; subst; simpl in *.
inversion H2; subst; simpl in *.
replace
  (compile
    (Context maxvar0 curobjpathfield0 (None :: cbl) (length p) bo)
    cur)
with (
  seq (skip _ _) (
    compile
    (Context maxvar0 curobjpathfield0 cbl
      (length
        (p ++
          (None,
            map (compile (Context maxvar0 curobjpathfield0 cbl 0 bo)) stl ++
              compile_discard 1 cbl maxvar0 (exit A nativeop 1) :: nil)
          :: nil)) bo) cur
  )
).
esplit.
split.
eapply plus_left.
econstructor.
eright.
econstructor.
eleft.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
eapply state_invariant_codepoint with (p := p ++ (None, map (compile (Context maxvar0 curobjpathfield0 cbl 0 bo)) stl ++
              compile_discard 1 cbl maxvar0 (exit A nativeop 1) :: nil) :: nil).
reflexivity.
eassumption.
 simpl.
 intros.
 destruct (in_app_or _ _ _ H4).
 eauto.
 destruct H7.
  discriminate.
 contradiction.
functional inversion H; simpl; eauto.
simpl.
reflexivity.
simpl.
right.
rewrite retrieve_list_stmt_app.
reflexivity.
assumption.
reflexivity.
simpl.
rewrite map_app.
simpl.
rewrite app_ass.
simpl.
reflexivity.
assumption.
eauto using Preservation.goal.
rewrite app_length.
simpl.
replace (length p + 1)%nat with (S (length p)) by omega.
functional inversion H; simpl.
replace (S (S (length p + length cbl)))%nat with (S (length p + S (length cbl)))%nat by omega.
reflexivity.
Qed. (* slow *)

Lemma preservation_Sreturn_Kconstrother_base : forall vars stl obj ar i h p tinit init0 body vars' k2 b q stk gl cs auxcs f
(Hs1 :
  State.make (State.codepoint vars (Sreturn None) stl nil)
  (StackFrame.Kconstrother obj ar i (h, p) tinit init0 body vars'
    Constructor.base k2 b q :: stk) gl cs auxcs f = s1),
goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
injection H1; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H; intros; subst; simpl in *.
inversion H8; subst; simpl in *; try discriminate.
injection H7; intros; subst; simpl in *.
generalize (StackFrame.Kconstrother_base_inj H7).
intro; invall; subst.
inversion H0; subst; simpl in *.
destruct global; simpl in *.
destruct globals; simpl in *.
destruct (exit_further (p := p0) (stm :=(ret A nativeop None) ) (refl_equal _)
next_object  dynamic_type field_values heap further vars1 (
Callframe (exit A nativeop 1 :: x) vars'0 None
               :: Block None
                    (match k1 with
                     | Constructor.direct_non_virtual =>
                         compile_constr_direct_non_virtual_bases
                           (if path_eq_dec (h0, p1)
                                 (Class.Inheritance.Repeated, class :: nil)
                            then true
                            else false) bases class tinit0 init1 body0 curobj
                           curpath maxvar1
                     | Constructor.virtual =>
                         compile_constr_virtual_bases bases class tinit0
                           init1 body0 curobj curpath maxvar1
                     end :: nil) :: stk'
)).
destruct H6.
generalize (kind invariant_inheritance0).
unfold state_kind_inv.
simpl; intro; invall; subst.
generalize (stack invariant_inheritance0 (or_introl _ (refl_equal _))).
simpl; intro; invall; subst.
destruct (list_inj (stack_inj H1)).
generalize (StackFrame.Kconstrother_base_inj H19).
intro; invall; subst.
esplit.
split.
eapply plus_right.
eauto using evtr_sem.
eapply star_trans.
eauto using evtr_sem.
eassumption.
eapply star_left.
eapply step_return_nil
with (vars'' := vars'0).
split; trivial.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
reflexivity.
reflexivity.
eapply star_left.
econstructor.
eleft.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
econstructor.
repeat rewrite E0_left; eauto using evtr_sem.
split; simpl; try assumption.
eapply state_invariant_constr with (k := Constructor.base).
reflexivity.
eassumption.
eassumption.
6 : simpl; reflexivity.
6 : simpl; reflexivity.
6 : simpl; reflexivity.
assumption.
eassumption.
assumption.
assumption.
assumption.
assumption.
simpl.
intros.
destruct (H16 obj).
 destruct H26.
 eauto.
destruct (invariant_heap0 obj); auto.
rewrite H26; auto.
reflexivity.
(** dynamic type *)
simpl.
intros.
destruct (
  prod_eq_dec 
   (prod_eq_dec peq (array_path_eq_dec (A := A)))
   Z_eq_dec
    (obj0, ar0, i0) (obj, ar, i)
).
 injection e; intros; subst.
 assert (is_some (last (
match k1 with
           | Constructor.direct_non_virtual => p1 ++ b1 :: nil
           | Constructor.virtual => b1 :: nil
           end
 ))).
  destruct k1; try exact I.
  rewrite last_complete; exact I.
 refine (False_rect _ (set_dynamic_type_Constructed_after_not_most_derived
hierarchy_wf invariant_inheritance0 Hstep (hp := H27) _ _ _ _ H26)).
 inversion H10; subst.
 assert (x3 = class).
  generalize (path_last H31).
  unfold_ident_in_all; intro; congruence.
 subst.
 econstructor.
 eassumption.
 econstructor.
 eassumption.
 assumption.
 assumption.
 eapply path_concat with
   (k :=
match k1 with
            | Constructor.direct_non_virtual => h0
            | Constructor.virtual => Class.Inheritance.Shared
            end
   )
   (k2 := 
   match k1 with 
     | Constructor.direct_non_virtual => Class.Inheritance.Repeated
     | Constructor.virtual => Class.Inheritance.Shared
   end
 ) (p2 := 
   match k1 with
     | Constructor.direct_non_virtual => class :: b1 :: nil
     | Constructor.virtual => b1 :: nil
   end
 ) (c := b1).
 eassumption.
 destruct k1; invall; subst.
  eleft with (lt := class :: nil).
  reflexivity.
  reflexivity.
  simpl.
  rewrite H22.
  sdestruct (
In_dec super_eq_dec (Class.Inheritance.Repeated, b1) (Class.super x4)
  ).
   rewrite H34.
   trivial.
  destruct n.
  eapply in_map_bases_elim.
  rewrite H25.
  eauto using in_or_app.
 eright.
 eapply vborder_list_virtual_base.
 eassumption.
 eassumption.
 eapply in_or_app; right; left; reflexivity.
 eleft with (lt := nil).
 reflexivity.
 reflexivity.
 simpl.
 rewrite H36.
 trivial.
 destruct k1; try reflexivity.
 Transparent concat. simpl. Opaque concat.
 rewrite H21. destruct (
  peq class class
 ).
  reflexivity.
 destruct n; trivial.
 simpl.
sdestruct (
 pointer_eq_dec (A:=A)
         (obj,
         (ar, i,
         (match k1 with
          | Constructor.direct_non_virtual => h0
          | Constructor.virtual => Class.Inheritance.Shared
          end,
         match k1 with
         | Constructor.direct_non_virtual => p1 ++ b1 :: nil
         | Constructor.virtual => b1 :: nil
         end)))
         (obj,
         (ar, i,
         (match k1 with
          | Constructor.direct_non_virtual => h0
          | Constructor.virtual => Class.Inheritance.Shared
          end,
         match k1 with
         | Constructor.direct_non_virtual => p1 ++ b1 :: nil
         | Constructor.virtual => b1 :: nil
         end)))
).
 reflexivity.
destruct n.
trivial.
intro.
destruct k1; try congruence.
destruct p1.
 contradiction.
destruct p1; simpl; congruence.
simpl.
destruct k1; invall; subst; unfold_ident_in_all.
 rewrite H28.
 cut (
 Some BasesConstructed <>
   (if pointer_eq_dec (A:=A) (obj, (ar, i, (h0, p1 ++ b1 :: nil)))
         (obj, (ar, i, (h0, p1 ++ b1 :: nil)))
    then Some Constructed
    else Some BasesConstructed)
 ).
  intro; assumption.
  sdestruct ( 
 pointer_eq_dec (A:=A) (obj, (ar, i, (h0, p1 ++ b1 :: nil)))
         (obj, (ar, i, (h0, p1 ++ b1 :: nil)))
 );
  congruence.
  sdestruct ( 
 pointer_eq_dec (A:=A) (obj, (ar, i, (Class.Inheritance.Shared, b1 :: nil)))
         (obj, (ar, i, (Class.Inheritance.Shared, b1 :: nil)))
 );
  congruence.
 apply invariant_dynamic_type0.
 exact (set_dynamic_type_other_before invariant_inheritance0 Hstep (refl_equal _) n H26).
 simpl.
 intros until 1.
 sdestruct (
pointer_eq_dec (A:=A)
           (obj0,
           (ar0, i0,
           (match k1 with
            | Constructor.direct_non_virtual => h0
            | Constructor.virtual => Class.Inheritance.Shared
            end,
           match k1 with
           | Constructor.direct_non_virtual => p1 ++ b1 :: nil
           | Constructor.virtual => b1 :: nil
           end))) (obj, (ar, i, (h, p)))
 ); eauto.
 intros _. 
 injection e; intros; subst.
 eapply (invariant_allow_static_cast_strong Hinv) with (hp := hp0); simpl.
 assumption.
 destruct k1; invall; subst; unfold_ident_in_all.
  rewrite H27.
  simpl; omega.
 rewrite H28.
 simpl; omega.
 destruct k1; invall; subst; unfold_ident_in_all.
  rewrite H27.
  simpl; omega.
 rewrite H28.
 simpl; omega.
eauto using Preservation.goal.
Qed. (* slow *)

Lemma preservation_Sreturn_Kdestr : forall vars stl obj ar i h p stk gl cs auxcs f 
  (Hs1 :
    State.make (State.codepoint vars (Sreturn None) stl nil)
    (StackFrame.Kdestr obj ar i (h, p) :: stk) gl cs auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
injection H2; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H3; intros; subst; simpl in *.
inversion H11; subst; simpl in *; try discriminate.
injection H15; intros; subst; simpl in *.
inversion H4; subst; simpl in *.
destruct global; simpl in *.
destruct globals; simpl in *.
refine (_ (exit_further (p := p0) (stm :=(exit A nativeop (S (length p0 + O)))) _
next_object  dynamic_type field_values heap further vars1 (
Block None
             (compile_destr_all_fields  (if path_eq_dec (h0, p1)
                                      (Class.Inheritance.Repeated,
                                      class :: nil)
                                 then true
                                 else false) class curobj curpath maxvar0 :: nil)
           :: stk'
))).
 Focus 2.
 Opaque minus.
  simpl.
  Transparent minus.
  destruct (le_lt_dec (length p0) (S (length p0 + 0)))%nat.
   replace (S (length p0 + 0) - length p0)%nat with (S O) by omega.
   reflexivity.
  omegaContradiction.
destruct 1.  
destruct H9.
generalize (kind invariant_inheritance0).
unfold state_kind_inv.
simpl; intro; invall; subst.
unfold_ident_in_all.
replace x1 with cn in * by congruence.
inversion H17; subst.
assert (cn = class).
 generalize (path_last H29).
 unfold_ident_in_all; congruence.
subst.
replace x2 with c in * by congruence.
assert (l = rev (Class.fields c)).
 rewrite H1.
 rewrite rev_involutive.
 trivial.
subst.
esplit.
split.
eapply plus_right.
eauto using evtr_sem.
eapply star_trans.
eauto using evtr_sem.
eassumption.
eapply star_left.
econstructor.
reflexivity.
reflexivity.
eapply star_left.
econstructor.
eleft.
reflexivity.
reflexivity.
reflexivity.
unfold compile_destr_all_fields.
rewrite H22.
econstructor.
repeat rewrite E0_left; eauto using evtr_sem.
split; simpl; try trivial.
eapply state_invariant_destr with (k := Constructor.field).
reflexivity.
eassumption.
eassumption.
6 : simpl; reflexivity.
6 : simpl; reflexivity.
6 : simpl; reflexivity.
eassumption.
eassumption.
assumption.
eassumption.
reflexivity.
simpl.
assumption.
intros.
destruct (H10 obj).
 destruct H30.
 eauto.
destruct (invariant_heap0 obj); auto.
rewrite H30; auto.
eauto using Preservation.goal.
Qed. (* slow *)

Lemma preservation_Sreturn_Kconstrothercells : forall vars stl obj ar n i cn init0 vars' stk gl cs auxcs f
  (Hs1 :
    State.make (State.codepoint vars (Sreturn None) stl nil)
    (StackFrame.Kconstrothercells obj ar n i cn init0 vars' :: stk) gl
    cs auxcs f = s1
  ),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
injection H0; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H; intros; subst; simpl in *.
inversion H8; subst; simpl in *; try discriminate.
injection H7; intros; subst; simpl in *.
inversion H1; subst; simpl in *.
destruct global; simpl in *.
destruct globals; simpl in *.
destruct (exit_further (p := p) (stm :=(ret A nativeop None) ) (refl_equal _)
next_object dynamic_type field_values heap further vars1 (
  (Callframe (exit A nativeop 1 :: stl) vars'0 None
          :: Block None
               (compile_constrarray tinit cn0 n0 blockvar index newobj
                  newpath maxvar1 (i0 + 1) :: nil) :: stk'
))).
destruct H6.
generalize (kind invariant_inheritance0).
unfold state_kind_inv.
simpl; intro; invall; subst.
generalize (stack invariant_inheritance0 (or_introl _ (refl_equal _))).
simpl; intro; invall; subst.
esplit.
split.
eapply plus_right.
eauto using evtr_sem.
eapply star_trans.
eauto using evtr_sem.
eassumption.
eapply star_left.
eapply step_return_nil
with (vars'' := vars'0).
split; trivial.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
reflexivity.
reflexivity.
eapply star_left.
econstructor.
eleft.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
econstructor.
repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
eapply state_invariant_constr_array.
reflexivity.
eassumption.
assumption.
omega.
(* omega. *)
eassumption.
eassumption.
eassumption.
eassumption.
eassumption.
eassumption.
eassumption.
reflexivity.
reflexivity.
reflexivity.
eassumption.
simpl. 
intros.
destruct (H16 obj).
 destruct H24.
 eauto.
destruct (invariant_heap0 obj); auto.
rewrite H24; auto.
reflexivity.
simpl.
intros.
destruct (
  prod_eq_dec 
   (prod_eq_dec peq (array_path_eq_dec (A := A)))
   Z_eq_dec
    (obj0, ar0, i0) (obj, ar, i)
).
 injection e; intros; subst.
 generalize (dynamic_type_prop H24).
 intro; invall; subst.
 replace x2 with x1 in * by congruence.
 generalize (valid_array_path_last H22 H29).
 intro; subst.
 assert (
   path (Program.hierarchy prog) x6 sp x3 sh
 ) by eauto using path_concat.  
 refine (_ (set_dynamic_type_Constructed_before_same_path hierarchy_wf invariant_inheritance0 Hstep (h := Class.Inheritance.Repeated) (p := x3 :: nil) (hp := I)  _ _ _ _ _ _)); simpl.
 Focus 2.
 econstructor.
 eassumption.
 econstructor.
 eassumption.
 eassumption.
 assumption.
 eleft with (lt := nil).
 reflexivity.
 reflexivity.
 simpl.
 rewrite H19.
 trivial.
 4 : reflexivity.
 4 : eassumption.
 4 : erewrite concat_trivial_left; eauto.
 intro.
 refine (_ (set_dynamic_type_Constructed_after_most_derived
 invariant_inheritance0 Hstep H17 H29 (conj H31 H35) _ H30)).
 simpl.
 intro.
 generalize (dynamic_type_unique_strong hierarchy_wf (Preservation.goal hierarchy_wf invariant_inheritance0 Hstep) H24 x8).
 injection 1; intros; subst; eauto.
 simpl.
 sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, x3 :: nil)))
         (obj, (ar, i, (Class.Inheritance.Repeated, x3 :: nil)))
 ); congruence.
 sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, x3 :: nil)))
         (obj, (ar, i, (Class.Inheritance.Repeated, x3 :: nil)))
 ); congruence.
 sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, x3 :: nil)))
         (obj, (ar, i, (Class.Inheritance.Repeated, x3 :: nil)))
 ); unfold_ident_in_all; congruence.
 generalize (set_dynamic_type_other_before invariant_inheritance0 Hstep (refl_equal _) n H24).
 intro; eauto.
 simpl.
 intros until 1.
 sdestruct (
pointer_eq_dec (A:=A)
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn0 :: nil)))
           (obj, (ar, i, (h, p0)))
 ); eauto.
 injection e; intros; subst.
 apply (invariant_allow_static_cast_strong Hinv) with (hp := hp0).
 assumption.
 simpl; unfold_ident_in_all; rewrite H18; simpl; omega.
 simpl; unfold_ident_in_all; rewrite H18; simpl; omega.
eauto using Preservation.goal.
Qed. (* slow *)


Lemma preservation_return_nil : forall vars vres stl vres' vars' stl' bl' stk gl cs auxcs f
  (Hs1 : State.make (State.codepoint vars (Sreturn vres) stl nil)
    (StackFrame.Kreturnfromcall vres' vars' stl' bl' :: stk) gl cs auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
injection H0; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H1; intros; subst; simpl in *.
inversion H9; subst; simpl in *; try discriminate.
injection H8; intros; subst; simpl in *.
inversion H2; subst; simpl in *.
destruct global; simpl in *.
destruct globals; simpl in *.
destruct (exit_further (p := p) (stm :=(ret A nativeop
  match vres with
    | Some v => Some (compile_var (Oldvar v))
    | None => None
  end) ) (refl_equal _)
next_object  dynamic_type field_values heap further vars1 (
 Callframe
             (map (compile (Context maxvar1 curobjpathfield1 q'0 0 bo0))
                further0 ++
              compile_discard 1 q'0 maxvar1 (exit A nativeop 1) :: nil) vars'0
             match ores with
             | Some res => Some (compile_var (Oldvar res))
             | None => None
             end :: q0 ++ stk'
)).
destruct H7.
esplit.
split.
eapply plus_right.
eauto using evtr_sem.
eassumption.
eapply step_return_nil
with (vars'' :=
  match ores with
    | Some res =>
      match vres with
        | Some v =>
          match vars1 ! (compile_var (Oldvar v)) with
            | Some val => PTree.set (compile_var (Oldvar res)) val vars'0
            | _ => vars'0
          end
        | _ => vars'0
      end
    | None => vars'0
  end
).
destruct vres; invall; subst; simpl in *.
esplit.
split.
 reflexivity.
esplit.
asplit.
 eauto.
rewrite H13.
reflexivity.
auto.
repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
destruct vres; invall; subst; simpl in *.
rewrite (H6 _ _ H).
eapply state_invariant_codepoint with (p := nil).
reflexivity.
7 : simpl; reflexivity.
simpl.
eapply block_invariant_oldvar.
eassumption.
simpl; intros; contradiction.
right; reflexivity.
reflexivity.
right; reflexivity.
eauto using vars_invariant_oldvar.
simpl; reflexivity.
simpl. eapply stack_invariant_oldvar. eassumption.
reflexivity.
eapply state_invariant_codepoint with (p := nil).
reflexivity.
eassumption.
simpl; intros; contradiction.
right; reflexivity.
reflexivity.
right; reflexivity.
assumption.
reflexivity.
simpl; reflexivity.
assumption.
simpl.
intros.
destruct (H12 obj).
 invall; eauto.
rewrite H13; eauto.
eauto using Preservation.goal.
Qed. (* slow *) 


(* HERE *)


Lemma preservation_destr_array_nil_Kcontinue : forall obj i cn vars stm obj' ostl bl stk gl cs auxcs f
  (Hs1 : State.make (State.destr_array obj nil i cn)
    (StackFrame.Kcontinue (StackFrame.continue_destr (A:=A) vars) stm
      obj' ostl bl :: stk) gl cs auxcs f = s1)
  (Hnil : i = -1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  injection H6; intros; omegaContradiction.
injection H2; intros; subst; simpl in *.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H; intros; subst.
Opaque compile_discard.
inversion H10; subst; simpl; try discriminate.
injection H15; intros; subst.
invall; subst; simpl in *.
unfold compile_destrarray_aux.
rewrite fordown_le; try omega.
destruct global; simpl in *.
generalize (kind invariant_inheritance0).
unfold state_kind_inv; simpl; intro; invall; subst.
replace x with stm' in * by congruence.
esplit.
split.
eapply plus_left.
econstructor.
reflexivity.
reflexivity.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eleft.
reflexivity.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
eapply state_invariant_codepoint with (p := x0 ++ (Some obj0, (
(map (compile (Context minvar curobjpathfield1 q' 0 bo0)) stl ++
             compile_discard 1 q' minvar (exit A nativeop 1) :: nil)
)) :: nil
); simpl.
reflexivity.
eassumption.
 simpl.
 intros.
 destruct (in_app_or _ _ _ H12).
 eauto.
 destruct H19.
  left; congruence.
 contradiction.
functional inversion Hsucc; simpl; auto.
destruct n0; auto.
rewrite app_length.
simpl.
replace (length x0 + 1)%nat with (S (length x0))%nat by omega.
reflexivity.
right.
rewrite retrieve_list_stmt_app.
reflexivity.
assumption.
reflexivity.
simpl.
rewrite map_app.
 simpl.
 rewrite app_ass.
 simpl.
 rewrite app_ass.
 simpl.
 reflexivity.
 eauto using stack_invariant_dealloc_cons.
 simpl in *; intros; assert (forall A B C : Prop, (A \/ (B \/ C)) -> ((A \/ B) \/ C)) by tauto; eauto.
 eauto using Preservation.goal.
Qed. (* slow *)


Lemma preservation_block_some : forall vars vlocstruct cn num init0 stm stl bl stk gl cs auxcs f
  (Hs1 : State.make
    (State.codepoint vars
      (Sblock (Some (vlocstruct, cn, num)) init0 stm) stl bl) stk gl cs
    auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  injection H0; intros; subst; discriminate.
  2 : injection H3; intros; subst; discriminate.
injection H4; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H2; intros; subst; simpl in *.
destruct H5; try discriminate.
destruct H7; try discriminate.
subst; simpl in *; subst; simpl in *.
destruct global; simpl in *.
injection H1; intros; subst; simpl in *.
esplit.
split.
 eapply plus_left.
 econstructor.
 assumption.
 rewrite <- prog'_hierarchy.
 assumption.
 unfold Globals.new.
 rewrite invariant_next_object0.
 reflexivity.
 reflexivity.
 eright.
 econstructor.
 eright.
 econstructor.
 eright.
 econstructor.
 rewrite PTree.gss. reflexivity.
 reflexivity.
 eright.
 econstructor.
 eright.
 econstructor.
 rewrite PTree.gso.
 rewrite PTree.gss.
 reflexivity.
 apply compile_var_other. congruence.
 reflexivity.
 eright.
 econstructor.
 eright.
 econstructor.
 eright.
 econstructor.
 eleft.
 reflexivity.
 reflexivity.
 reflexivity.
 reflexivity.
 reflexivity.
 reflexivity.
 reflexivity.
 reflexivity.
 repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
(** state_invariant *)
 eapply state_invariant_constr_array.
 reflexivity.
 simpl. rewrite PTree.gss. reflexivity.
 simpl. constructor. omega. omega. omega. (* assumption. *)
 10 : simpl; reflexivity.
 eapply vars_invariant_newvar.
 eapply vars_invariant_oldvar.
 eapply vars_invariant_newvar.
 eassumption.
 7 : reflexivity.
 rewrite PTree.gss.
 reflexivity.
 eapply Plt_succ.
 eapply Plt_succ.
 eapply Plt_succ.
 eapply Plt_succ.
 eapply Plt_succ.
 reflexivity.
 simpl.
 eapply stack_invariant_newvar_lt.
  2 : reflexivity.
 eapply stack_invariant_oldvar.
 2 : reflexivity.
 eapply stack_invariant_Kcontinue.
 reflexivity.
 rewrite PTree.gss. reflexivity.
 eapply vars_invariant_newvar. eassumption.
 simpl.
 split.
  trivial.
 exists (Psucc maxvar0).
 split.
 eapply Plt_succ.
 split.
 eapply Plt_succ.
 rewrite PTree.gss.
 esplit.
 split.
  reflexivity.
 reflexivity.
 eapply block_invariant_newvar_gt.
 eapply block_invariant_heap_new.
 eassumption.
 eapply Globals.valid_none.
 exact (valid_global invariant_inheritance0).
 apply Ple_refl.
 apply Plt_succ.
 simpl.
 reflexivity.
 eapply stack_invariant_heap_new.
 eapply stack_invariant_newvar_lt.
 eassumption.
 reflexivity.
 eapply Ple_Plt_trans.
 eapply block_invariant_minvar_le_maxvar.
 eassumption.
 apply Plt_succ.
 eapply Globals.valid_none.
 exact (valid_global invariant_inheritance0).
 apply Ple_refl.
 apply Plt_succ.
(** 6 deallocated objects *)
simpl.
intro.
destruct (invariant_heap0 obj).
 auto.
right.
destruct (peq (Globals.next_object gl) obj).
 subst; rewrite PTree.gss; rewrite PTree.gss; reflexivity.
rewrite PTree.gso; eauto; rewrite PTree.gso; eauto.
(** 5 next_object *)
reflexivity.
(** 4 dynamic type *)
simpl.
intros.
destruct (peq (Globals.next_object gl) obj).
 apply False_rect.
 subst.
 generalize (Globals.valid_none (valid_global invariant_inheritance0) (Ple_refl _)).
 simpl.
 intro.
 inversion H5; subst.
  rewrite (construction_states_none invariant_inheritance0 H6) in H12.
  discriminate.
 rewrite (construction_states_none invariant_inheritance0 H6) in H14.
 destruct H14; discriminate.
assert ( Cppsem.dynamic_type (A:=A) (Program.hierarchy prog)
  (Globals.heap gl) cs obj ar i sh sp ch cp dh dp
).
 inversion H5; subst.
  rewrite PTree.gso in H6; eauto.
  eleft; eauto.
 rewrite PTree.gso in H6; eauto.
 eright; eauto.
eauto.
(** allow static cast *)
simpl.
inversion 1; subst.
destruct (peq obj (Globals.next_object gl)).
 subst.
 rewrite (construction_states_none invariant_inheritance0 (Globals.valid_none (valid_global invariant_inheritance0) (Ple_refl _))).
 intro; discriminate.
rewrite PTree.gso in H9.
eapply invariant_allow_static_cast0 with (hp := hp0).
econstructor; eauto.
assumption.
(** CPP invariants *)
eauto using Preservation.goal.
eauto using preservation_scalar_fields_some_constructed.
Qed. (* slow *)

Lemma preservation_constr_array_nil_Kcontinue : forall obj ar n cn init0 vars stm obj' obk bl stk gl cs auxcs f
  (Hs1 :
    State.make (State.constr_array obj ar n n cn init0 vars)
    (StackFrame.Kcontinue (StackFrame.continue_constr A) stm obj' obk bl
      :: stk) gl cs auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  2 : injection H1; intros; omegaContradiction.
 injection H1; intros; subst; simpl in *.
subst; simpl in *.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H; intros; subst; subst.
inversion H15; try discriminate.
subst.
injection H19; intros; subst.
invall.
subst.
simpl in *.
unfold compile_constrarray.
simpl.
unfold compile_constrarray_aux.
rewrite forup_ge.
2 : omega.
destruct global.
esplit.
split.
 eapply plus_left.
  econstructor.
  reflexivity.
  reflexivity.
 eright.
 econstructor.
 eright.
 econstructor.
unfold compile'.
eapply star_left.
econstructor.
 eleft.
 reflexivity.
 reflexivity.
 reflexivity.
 repeat rewrite E0_left; eauto using evtr_sem.
 split; try assumption.
  eapply state_invariant_codepoint with (p := nil).
   reflexivity.
   econstructor.
    eassumption.
   eassumption.
   eassumption.
   eassumption.
   reflexivity.
   reflexivity.
   eassumption.
   reflexivity.
   simpl; tauto.
   auto.
  reflexivity.
  right; reflexivity.
  assumption.
 reflexivity.
 simpl; reflexivity.
 simpl.
 injection H11; intros; subst; assumption.
eauto using Preservation.goal.
Qed. (* slow *)

Lemma preservation_skip_cons : forall vars stm stl bl stk gl cs auxcs f
  (Hs1 : s1 = (State.make (State.codepoint vars Sskip (stm :: stl) bl) stk gl cs auxcs f)),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  2 : injection H0; intros; subst; discriminate.
  2 : injection H3; intros; subst; discriminate.
  injection H; intros; subst.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
  injection H0; intros; subst.
destruct H2; try discriminate.
destruct H4; try discriminate.
subst; simpl in *; subst; simpl in *.
esplit.
split.
eapply plus_left.
econstructor.
eleft.
repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
eapply state_invariant_codepoint with (p := nil).
reflexivity.
eassumption.
eassumption.
auto.
reflexivity.
right; reflexivity.
assumption.
reflexivity.
simpl.
reflexivity.
assumption.
eauto using Preservation.goal.
Qed. (* slow *)


Lemma preservation_if : forall vars test iftrue iffalse stl bl stk gl cs auxcs f
  (Hs1 : State.make (State.codepoint vars (Sif test iftrue iffalse) stl bl) stk gl cs auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  2 : injection H0; intros; subst; discriminate.
  2 : injection H3; intros; subst; discriminate.
injection H2; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H1; intros; subst; simpl in *.
destruct H4; try discriminate.
destruct H6; try discriminate.
subst; simpl in *; subst; simpl in *.
esplit.
split.
eapply plus_left.
econstructor.
eauto.
eassumption.
reflexivity.
eleft.
repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
eapply state_invariant_codepoint with (p := nil).
reflexivity.
eassumption.
eassumption.
auto.
destruct b; reflexivity.
right; reflexivity.
assumption.
reflexivity.
simpl; reflexivity.
assumption.
eauto using Preservation.goal.
Qed. (* slow *)
  
Lemma preservation_loop : forall vars stm stl bl stk gl cs auxcs f
(Hs1 : State.make (State.codepoint vars (Sloop stm) stl bl) stk gl cs auxcs f = s1),
goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  2 : injection H0; intros; subst; discriminate.
  2 : injection H3; intros; subst; discriminate.
injection H; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H0; intros; subst; simpl in *.
destruct H2; try discriminate.
destruct H4; try discriminate.
subst; simpl in *; subst; simpl in *.
esplit.
split.
 eapply plus_left.
 econstructor.
 eleft.
 repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
eapply state_invariant_codepoint with (p := nil).
reflexivity.
eassumption.
eassumption.
auto.
reflexivity.
right; reflexivity.
assumption.
reflexivity.
simpl; reflexivity.
assumption.
eauto using Preservation.goal.
Qed. (* slow *)

Lemma preservation_seq : forall vars stm1 stm2 stl bl stk gl cs auxcs f
  (Hs1 : State.make (State.codepoint vars (Sseq stm1 stm2) stl bl) stk gl cs auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  2 : injection H0; intros; subst; discriminate.
  2 : injection H3; intros; subst; discriminate.
injection H; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H0; intros; subst; simpl in *.
destruct H2; try discriminate.
destruct H4; try discriminate.
subst; simpl in *; subst; simpl in *.
esplit.
split.
 eapply plus_left.
 econstructor.
 eleft.
 repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
eapply state_invariant_codepoint with (p := nil).
reflexivity.
eassumption.
eassumption.
auto.
reflexivity.
right; reflexivity.
assumption.
reflexivity.
simpl; reflexivity.
assumption.
eauto using Preservation.goal.
Qed. (* slow *)

Lemma preservation_block_none : forall vars i stm stl bl stk gl cs auxcs f (Hs1 : State.make (State.codepoint vars (Sblock None i stm) stl bl) stk gl cs auxcs f = s1), goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  injection H0; intros; subst; discriminate.
  2 : injection H3; intros; subst; discriminate.
injection H; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H0; intros; subst; simpl in *.
destruct H2; try discriminate.
destruct H4; try discriminate.
subst; simpl in *; subst; simpl in *.
esplit.
split.
 eapply plus_left.
 econstructor.
 eapply star_left.
 econstructor.
 eleft.
 reflexivity.
 repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
eapply state_invariant_codepoint with (p := nil).
reflexivity.
econstructor.
eassumption.
reflexivity.
assumption.
auto.
reflexivity.
right.
reflexivity.
assumption.
reflexivity.
simpl; reflexivity.
assumption.
eauto using Preservation.goal.
Qed. (* slow *)  

Lemma preservation_native : forall vars op vargs vres stl bl stk gl cs auxcs f 
  (Hs1 : State.make (State.codepoint vars (Snative op vargs vres) stl bl) stk gl cs auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  injection H0; intros; subst; discriminate.
  2 : injection H3; intros; subst; discriminate.
injection H; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H2; intros; subst; simpl in *.
injection H4; intros; subst; simpl in *.
destruct H6; try discriminate.
destruct H8; try discriminate.
subst; simpl in *; subst; simpl in *.
esplit.
split.
eapply plus_left.
eapply step_native with (vars' :=
  match res with
    | None => vars2
    | Some (existT rty rva) =>
      match vres with
        | None => vars2
        | Some v => PTree.set (compile_var (Oldvar v)) (Val (Value.atom rty rva)) vars2
      end
  end).
eapply trans_equal.
eapply map_atom'.
eapply vars_invariant_map.
eassumption.
eapply trans_equal.
symmetry.
eapply map_atom.
eassumption.
eassumption.
destruct vres; invall; subst; simpl in *.
 esplit.
 split.
  reflexivity.
 reflexivity.
auto.
eleft.
rewrite E0_right. trivial. eauto using evtr_sem. 
split; try assumption.
destruct vres; invall; subst; simpl in *.
 eapply state_invariant_codepoint with (p := nil).
 reflexivity.
 eapply block_invariant_oldvar.
 eassumption.
 assumption.
 right; reflexivity.
 reflexivity.
 right; reflexivity.
 eauto using vars_invariant_oldvar.
 reflexivity.
 simpl; reflexivity.
 eauto using stack_invariant_oldvar.
eapply state_invariant_codepoint with (p := nil).
reflexivity.
eassumption.
assumption.
auto.
reflexivity.
right; reflexivity.
assumption.
reflexivity.
simpl; reflexivity.
assumption.
eauto using Preservation.goal.
Qed. (* slow *)

Lemma preservation_move : forall vars src tgt stl bl stk gl cs auxcs f (Hs1 : State.make (State.codepoint vars (Smove src tgt) stl bl) stk gl cs  auxcs f = s1), goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  injection H0; intros; subst; discriminate.
  2 : injection H3; intros; subst; discriminate.
injection H1; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H0; intros; subst; simpl in *.
destruct H3; try discriminate.
destruct H5; try discriminate.
subst; simpl in *; subst; simpl in *.
esplit.
split.
eapply plus_left.
econstructor.
eauto.
reflexivity.
eleft.
repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
eapply state_invariant_codepoint with (p := nil).
reflexivity.
eapply block_invariant_oldvar. eassumption.
assumption.
right; reflexivity.
reflexivity.
right; reflexivity.
eauto using vars_invariant_oldvar.
reflexivity.
simpl; reflexivity.
eauto using stack_invariant_oldvar.
eauto using Preservation.goal.
Qed. (* slow *)

Lemma preservation_getfield : forall vars vobj ty fs tgt stl bl stk gl constate auxcs f
  (Hs1 : State.make (State.codepoint vars (Sgetfield vobj ty fs tgt) stl bl)
         stk gl constate auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  injection H0; intros; subst; discriminate.
  2 : injection H3; intros; subst; discriminate.
injection H7; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H6; intros; subst; simpl in *.
destruct H9; try discriminate.
destruct H11; try discriminate.
subst; simpl in *; subst; simpl in *.
assert (In obj f -> False).
 case_eq (FieldSignature.type fs).
  2 : assumption.
 intros.
 eauto using get_field_scalar_some_not_deallocated_object.
destruct (invariant_heap0 obj).
 contradiction.
destruct global; simpl in *.
esplit.
split.
eapply plus_left.
econstructor.
eauto.
rewrite <- prog'_hierarchy.
eapply valid_pointer_preserve.
eassumption.
assumption.
assumption.
rewrite <- prog'_hierarchy.
eassumption.
assumption.
eapply invariant_field_values0.
eassumption.
reflexivity.
eleft.
repeat rewrite E0_left; eauto using evtr_sem.
split; try eassumption.
eapply state_invariant_codepoint with (p := nil).
reflexivity.
eapply block_invariant_oldvar.
eassumption.
assumption.
auto.
reflexivity.
right; reflexivity.
eapply vars_invariant_oldvar.
assumption.
reflexivity.
simpl; reflexivity.
eapply stack_invariant_oldvar.
eassumption.
reflexivity.
eauto using Preservation.goal.
Qed. (* slow *)

Lemma preservation_putfield : forall vars vobj ty fs tgt stl bl stk gl constate auxcs f
  (Hs1 : State.make (State.codepoint vars (Sputfield vobj ty fs tgt) stl bl) stk gl constate auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  injection H0; intros; subst; discriminate.
  2 : injection H3; intros; subst; discriminate.
injection H4; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H3; intros; subst; simpl in *.
destruct H6; try discriminate.
destruct H8; try discriminate.
subst; simpl in *; subst; simpl in *.
assert (In obj f -> False).
 eauto using constructed_field_not_deallocated.
destruct (invariant_heap0 obj).
 contradiction.
destruct global; simpl in *.
assert (exists l'', Globals.put_field (Globals.field_values globals)
         (obj, ar, i, (h, p), fs) val = Some l'').
 functional inversion H2; subst.
 Transparent Globals.put_field.
 unfold Globals.put_field.
 Opaque Globals.put_field.
 rewrite H15.
 rewrite H16.
 eauto.
invall.
esplit.
split.
eapply plus_left.
econstructor.
eauto.
rewrite <- prog'_hierarchy.
eapply valid_pointer_preserve.
eassumption.
assumption.
assumption.
rewrite <- prog'_hierarchy.
eassumption.
assumption.
eauto.
eassumption.
reflexivity.
eleft.
repeat rewrite E0_left; eauto using evtr_sem.
split; try eassumption.
eapply state_invariant_codepoint with (p := nil).
reflexivity.
eassumption.
assumption.
right; reflexivity.
reflexivity.
right; reflexivity.
assumption.
reflexivity.
simpl; reflexivity.
assumption.
simpl.
intro.
destruct (aux_constr_state_key_eq_dec (obj, ar, i, (h, p), fs) f0).
 subst.
 rewrite (Globals.get_put_field_same H2).
 rewrite (Globals.get_put_field_same H10).
 tauto.
rewrite (Globals.get_put_field_other H2 n).
rewrite (Globals.get_put_field_other H10 n).
eauto.
eauto using Preservation.goal.
eauto using preservation_scalar_fields_some_constructed.
Qed. (* slow *)

Lemma preservation_index : forall vars vobj cn vindex tgt stl bl stk gl constate auxcs f
  (Hs1 : State.make (State.codepoint vars (Sindex vobj cn vindex tgt) stl bl) stk gl constate auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  injection H0; intros; subst; discriminate.
  2 : injection H3; intros; subst; discriminate.
injection H8; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H7; intros; subst; simpl in *.
destruct H10; try discriminate.
destruct H12; try discriminate.
subst; simpl in *; subst; simpl in *.
destruct global; simpl in *.
destruct (invariant_heap0 obj).
 contradiction.
esplit.
split.
eapply plus_left.
econstructor.
eauto.
rewrite H10; eassumption.
rewrite <- prog'_hierarchy.
eassumption.
assumption.
eauto.
eassumption.
assumption.
reflexivity.
eleft.
repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
eapply state_invariant_codepoint with (p := nil).
reflexivity.
eapply block_invariant_oldvar.
eassumption.
assumption.
right; reflexivity.
reflexivity.
right; reflexivity.
eauto using vars_invariant_oldvar.
reflexivity.
simpl; reflexivity.
eauto using stack_invariant_oldvar.
eauto using Preservation.goal.
Qed. (* slow *)

Lemma preservation_ptreq : forall vars vptr1 vptr2 tgt stl bl stk gl constate auxcs f
  (Hs1 : State.make (State.codepoint vars (Sptreq vptr1 vptr2 tgt) stl bl) stk gl constate auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try  discriminate.
  injection H0; intros; subst; discriminate.
  2 : injection H3; intros; subst; discriminate.
injection H8; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H6; intros; subst; simpl in *.
destruct H9; try discriminate.
destruct H11; try discriminate.
subst; simpl in *; subst; simpl in *.
destruct global; simpl in *.
assert (valid_pointer (hierarchy prog') (Globals.heap globals) ptr1).
 rewrite <- prog'_hierarchy.
 inversion H1; subst.
  constructor.
  assumption.
 destruct (invariant_heap0 id).
  contradiction.
 eauto using valid_pointer_preserve.
assert (valid_pointer (hierarchy prog') (Globals.heap globals) ptr2).
 rewrite <- prog'_hierarchy.
 inversion H2; subst.
  constructor.
  assumption.
 destruct (invariant_heap0 id).
  contradiction.
 eauto using valid_pointer_preserve.
esplit.
split.
eapply  plus_left.
econstructor.
eauto.
assumption.
eauto.
assumption.
assumption.
reflexivity.
eleft.
repeat rewrite E0_left; eauto using evtr_sem.
replace (
if Value.pointer_eq_dec ptr1 ptr2
            then
             Val (Value.atom (tyTRUE sem) (TRUE sem))
            else
             Val
               (Value.atom (tyFALSE sem) (FALSE sem))
) with (Val (
if Value.pointer_eq_dec ptr1 ptr2
            then
               (Value.atom (tyTRUE sem) (TRUE sem))
            else             
               (Value.atom (tyFALSE sem) (FALSE sem))
)).
split; try assumption.
eapply state_invariant_codepoint with (p := nil).
reflexivity.
eapply block_invariant_oldvar.
eassumption.
assumption.
right; reflexivity.
reflexivity.
right; reflexivity.
eauto using vars_invariant_oldvar.
reflexivity.
simpl; reflexivity.
eauto using stack_invariant_oldvar.
eauto using Preservation.goal.
destruct (Value.pointer_eq_dec ptr1 ptr2); reflexivity.
Qed. (* slow *)

Lemma preservation_call : forall vars ckind vargs oret stl blocks0 stack global constate auxcs f
  (Hs1 : State.make
    (State.codepoint vars (Scall nativeop ckind vargs oret) stl
      blocks0) stack global constate auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  injection H0; intros; subst; discriminate.
  2 : injection H3; intros; subst; discriminate.
injection H2; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H1; intros; subst; simpl in *.
destruct H4; try discriminate.
destruct H6; try discriminate.
subst; simpl in *; subst; simpl in *.
 esplit.
 split.
 eapply plus_left.
 eapply step_call with (
   vargs' := match ckind with
               | Cppsem.Static f0 =>
                 match (statics prog') ! (compile_static (Oldstatic f0)) with
                   | Some f => sargs f
                   | _ => nil
                 end
               | Cppsem.NonVirtual cn ms =>
                 match (Program.hierarchy prog) ! cn with
                   | Some c =>
                     match Method.find ms (Class.methods c) with
                       | Some m =>
                         match Method.kind m with
                           | Method.concrete cid =>
                             match (methods prog') ! cid with
                               | Some mb => mthis mb :: margs mb
                               | _ => nil
                             end
                           | _ => nil
                         end
                       | _ => nil
                     end
                   | _ => nil
                 end
             end
   ) (
     body' := compile' (Context  xH None nil O false)
     match ckind with
       | Cppsem.Static f0 =>
         match (Program.static_methods prog) ! f0 with
           | Some m => Static_method.code m
           | _ => Sskip
         end
       | Cppsem.NonVirtual cn ms =>
         match (Program.hierarchy prog) ! cn with
           | Some c =>
             match Method.find ms (Class.methods c) with
               | Some m =>
                 match Method.kind m with
                   | Method.concrete cid =>
                     match (Program.methods prog) ! cid with
                       | Some mb => Method_body.code mb
                       | _ => Sskip
                     end
                   | _ => Sskip
                 end
               | _ => Sskip
             end
           | _ => Sskip
         end
     end
   ).
 eapply vars_invariant_map.
 eassumption.
 eassumption.
 destruct ckind; invall; subst. 
  rewrite  (prog'_statics H0).
  rewrite H0.
  eauto.
 rewrite <- prog'_hierarchy.
 rewrite H0.
 esplit.
 split.
  reflexivity.
 rewrite H5.
 esplit.
 split.
  reflexivity.
 rewrite H6.
 esplit.
 split.
  reflexivity.
 rewrite (prog'_methods H8).
 rewrite H8.
 simpl.
 eauto.
reflexivity.
unfold compile'.
eapply star_left.
econstructor.
eleft.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
eapply state_invariant_codepoint with (p := nil) (maxvar := xH) (curobjpathfield := None) (bo := false); simpl.
reflexivity.
econstructor.
trivial.
tauto.
auto.
destruct ckind; invall; subst.
rewrite H0.  reflexivity.
rewrite H0.
rewrite H5.
rewrite H6.
rewrite H8.
reflexivity.
right; reflexivity.
eapply vars_invariant_set_params.
destruct ckind; invall; subst.
 rewrite (prog'_statics H0).
 reflexivity.
rewrite H0.
rewrite H5.
rewrite H6.
rewrite (prog'_methods H8).
reflexivity.
simpl.
reflexivity.
eapply stack_invariant_Kreturnfromcall.
reflexivity.
eassumption.
assumption.
reflexivity.
reflexivity.
assumption.
eauto using Preservation.goal.
Qed. (* slow *)

Lemma preservation_invoke : forall vars vobj cn ms vargs vres stl bl stk gl constate auxcs f
  (Hs1 : State.make
    (State.codepoint vars (Sinvoke vobj cn ms vargs vres) stl bl) stk
    gl constate auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  injection H0; intros; subst; discriminate.
  2 : injection H3; intros; subst; discriminate.
injection H13; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H11; intros; subst; simpl in *.
destruct H14; try discriminate.
destruct H16; try discriminate.
subst; simpl in *; subst; simpl in *.
generalize (dynamic_type_prop H0).
intro; invall.
assert (is_some (last cp)).
 rewrite (path_last H19).
 exact I.
destruct global; simpl in *.
destruct (invariant_heap0 obj). 
 destruct (dynamic_type_not_deallocated invariant_inheritance0 H0 H24).
generalize (concat_last (path_nonempty H21) H22).
rewrite H1.
rewrite (path_last H21).
injection 1; intros; subst.
generalize H2.
rewrite (path_last H19).
injection 1; intros; subst.
esplit.
split.
eapply plus_left.
eapply step_invoke.
eauto.
eauto.
rewrite <- prog'_hierarchy.
eapply valid_pointer_preserve.
eassumption.
econstructor.
eassumption.
econstructor; eauto.
eauto using path_concat.
eauto using path_last.
assumption.
rewrite <- prog'_hierarchy; eassumption.
eassumption.
rewrite <- prog'_hierarchy; eassumption.
eassumption.
eassumption.
eauto using prog'_methods.
eapply vars_invariant_map.
eassumption.
eassumption.
eassumption.
reflexivity.
reflexivity.
unfold compile'.
simpl.
eapply star_left.
econstructor.
eleft.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
eapply state_invariant_codepoint with (p := nil) (maxvar := xH) (curobjpathfield := None) (bo := false); simpl.
reflexivity.
econstructor.
trivial.
tauto.
auto.
reflexivity.
right; reflexivity.
eapply vars_invariant_oldvar.
eapply vars_invariant_set_params.
reflexivity.
simpl; reflexivity.
eapply stack_invariant_Kreturnfromcall.
reflexivity.
eassumption.
assumption.
reflexivity.
reflexivity.
assumption.
eauto using Preservation.goal.
Qed. (* slow *)  

Lemma preservation_dyncast : forall
  vars vobj cfrom cto vres stl bl stk gl constate auxcs f
  (Hs1 : 
State.make
         (State.codepoint vars (Sdyncast vobj cfrom cto vres) stl bl) stk gl
         constate auxcs f = s1
  ), goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  injection H0; intros; subst; discriminate.
  2 : injection H3; intros; subst; discriminate.
injection H7; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H6; intros; subst; simpl in *.
destruct H9; try discriminate.
destruct H11; try discriminate.
subst; simpl in *; subst; simpl in *.
destruct (Well_formed_hierarchy.path_to hierarchy_wf cto).
destruct a.
generalize (dynamic_type_prop H0).
intro; invall.
destruct (invariant_heap0 obj). 
 destruct (dynamic_type_not_deallocated invariant_inheritance0 H0 H14).
assert (is_some (last cp)).
 rewrite (path_last H17).
 exact I.
generalize (concat_last (path_nonempty H18) H19).
rewrite H2.
rewrite (path_last H18).
injection 1; intros; subst.
generalize (path_last H17).
rewrite H1.
injection 1; intros; subst.
destruct global; simpl in *.
case_eq (x ! x4).
 intros.
 generalize (H10 _ _ H24).
 intros.
 destruct l.
  (* not a base *)
  esplit.
  split.
  eapply plus_left.
  eapply step_dyncast .
  eauto.
  rewrite <- prog'_hierarchy.
  eapply valid_pointer_preserve.
  eassumption.
  econstructor; eauto.
  econstructor; eauto.
  eauto using path_concat.
  eauto.
  eassumption.
  assumption.
  rewrite <- prog'_hierarchy; eassumption.
  rewrite <- prog'_hierarchy; eassumption.
  rewrite <- prog'_hierarchy; assumption.
  rewrite <- prog'_hierarchy. intros. generalize (H25 (h'', p'')). simpl; tauto.
  reflexivity.
  eleft.
  repeat rewrite E0_left; eauto using evtr_sem.
  split; try assumption.
   eapply state_invariant_codepoint with (p := nil).
   reflexivity.
   eapply block_invariant_oldvar. eassumption.
   assumption.
   auto.
   reflexivity.
   right; reflexivity.
   eauto using vars_invariant_oldvar.
   reflexivity.
   simpl; reflexivity.
   eauto using stack_invariant_oldvar.
  eauto using Preservation.goal.
  (* base *)
  destruct (
    at_most_list path_eq_dec (p :: l)
  ).
   (* ambiguous *)
   invall.
   destruct (H25 x5).
   generalize (H28 H26).
   destruct (H25 x6).
   generalize (H31 H27).
   destruct x5.
   destruct x6.
   intros.
   assert (
     forall (kh : Class.Inheritance.t) (kp : list ident),
       dynamic_cast (A:=A) (Program.hierarchy prog) x3 dh dp x4 cto kh kp -> False
   ).
    intros.
    generalize (Well_formed_hierarchy.dynamic_cast_base_static_cast hierarchy_wf H35 H33).
    intro.
    eauto using (Well_formed_hierarchy.ambiguous_base_no_static_cast).
   generalize (H5 H35).
   intros; subst.
  esplit.
  split.
  eapply plus_left.
  econstructor.
  reflexivity.
  eleft.
  repeat rewrite E0_left; eauto using evtr_sem.
  split; try assumption.
   eapply state_invariant_codepoint with (p := nil).
   reflexivity.
   eapply block_invariant_oldvar. eassumption.
   assumption.
   auto.
   reflexivity.
   right; reflexivity.
   eauto using vars_invariant_oldvar.
   reflexivity.
   simpl; reflexivity.
   eauto using stack_invariant_oldvar.
  eauto using Preservation.goal.
 (* unique base *)
 destruct (H25 p).
 generalize (H26 (or_introl _ (refl_equal _))).
 destruct p.
 intro.
 case_eq (concat (dh, dp) (t, l0)).
 intros.
 assert (
   static_cast (Program.hierarchy prog) x3 dh dp x4 cto t0 l1
 ).
  eleft.
  assumption.
  eassumption.
  intros.
  eapply e.
  auto.
  eapply H25.
  assumption.
  symmetry; assumption.
 generalize (static_cast_dynamic_cast H30).
 intro.
 generalize (H4 _ _ H31).
 intros; invall; subst.
 assert (
   static_cast (Program.hierarchy prog) x1 sh sp x4 cto x5 x6
 ).
  eleft.
  eauto using path_concat.
  eassumption.
 intros.
  eapply e.
  auto.
  eapply H25.
  assumption.
  rewrite H19.
  rewrite concat_assoc.
  rewrite H29.
  assumption.
 esplit.
 split.
 eapply plus_left.
 econstructor.
 eauto.
 eapply (invariant_allow_static_cast_strong Hinv) with (hp := shp).
 econstructor; eauto.
 econstructor; eauto using path_concat.
 generalize (dynamic_type_base_constructed invariant_inheritance0 hierarchy_wf H0).
 simpl; unfold_ident; intro; omega. 
 generalize (dynamic_type_base_constructed invariant_inheritance0 hierarchy_wf H0).
 simpl; unfold_ident; intro; omega. 
 rewrite H14.
 eassumption.
 rewrite <- prog'_hierarchy; econstructor; eauto using path_concat.
 rewrite <- prog'_hierarchy; eassumption.
 reflexivity.
 eleft.
 repeat rewrite E0_left; eauto using evtr_sem.
 split; try assumption.
 eapply state_invariant_codepoint with (p := nil).
 reflexivity.
 eapply block_invariant_oldvar; eassumption.
 assumption.
 auto.
 reflexivity.
 right; reflexivity.
 eauto using vars_invariant_oldvar.
 reflexivity.
 simpl; reflexivity.
 eauto using stack_invariant_oldvar.
 eauto using Preservation.goal.
(* absurd case (undefined) *)
intro.
apply False_rect.
generalize (path_defined_to H18).
intro.
generalize (H9 _ H25).
intro; contradiction.
Qed. (* slow *)

Lemma preservation_statcast : forall vars vobj cfrom cto vres stl bl stk gl constate auxcs f
  (Hs1 : State.make
    (State.codepoint vars (Sstatcast vobj cfrom cto vres) stl bl) stk gl
    constate auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  injection H0; intros; subst; discriminate.
  2 : injection H3; intros; subst; discriminate.
injection H9; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H1; intros; subst; simpl in *.
destruct H10; try discriminate.
destruct H12; try discriminate.
subst; simpl in *; subst; simpl in *.
assert (path (Program.hierarchy prog) cfrom p ato h).
 inversion H7; subst; eauto using path_concat.
assert (valid_relative_pointer (Program.hierarchy prog) (Object.class o) (Object.arraysize o) ar ato i h p cfrom).
 econstructor; eauto; omega.
destruct (invariant_heap0 obj).
 destruct (inclusion_subobject_of_full_object H11); invall.
 generalize (deallocated_objects_destructed invariant_inheritance0 H12 H4 (conj H14 H18)).
 intro.
 generalize (construction_includes_destructed (inclusion_construction_order invariant_inheritance0 H4 H17) H6).
 simpl.
 unfold_ident_in_all.
 intro.
 rewrite H20 in H2, H3.
 simpl in *; omegaContradiction.
destruct global; simpl in *.
esplit.
split.
eapply plus_left.
eapply step_statcast with (hp' := chp).
eauto.
eapply (invariant_allow_static_cast_strong Hinv) with (hp := hp).
econstructor; eauto.
simpl; eassumption.
simpl; eassumption.
rewrite H12; eauto.
rewrite <- prog'_hierarchy; eauto.
rewrite <- prog'_hierarchy; eauto.
reflexivity.
eleft.
 repeat rewrite E0_left; eauto using evtr_sem.
 split; try assumption.
 eapply state_invariant_codepoint with (p := nil).
 reflexivity.
 eapply block_invariant_oldvar; eassumption.
 assumption.
 auto.
 reflexivity.
 right; reflexivity.
 eauto using vars_invariant_oldvar.
 reflexivity.
 simpl; reflexivity.
 eauto using stack_invariant_oldvar.
 eauto using Preservation.goal.
Qed. (* slow *)

(** Construction *)

Lemma preservation_constr_array_cons : forall obj ar n i cn init0 vars stk gl cs auxcs f
  (Hs1 :
    State.make (State.constr_array obj ar n i cn init0 vars) stk gl cs
    auxcs f = s1)
  (Hcons : i < n),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  injection H1; intros; omegaContradiction.
  2: injection H; intros; omegaContradiction.
injection H1; intros; subst; simpl in *.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H0; intros; subst; subst.
destruct (invariant_heap0 obj0).
 edestruct (deallocated_objects_not_in_stack invariant_inheritance0).
  2 : eassumption.
 destruct (kind_object_in_construction invariant_inheritance0 (refl_equal _)).
 rewrite H13.
 auto.
generalize (kind invariant_inheritance0).
unfold state_kind_inv; simpl.
intros; invall.
destruct global; simpl in *.
unfold compile_constrarray.
unfold compile_constrarray_aux.
rewrite forup_lt.
2 : assumption.
unfold compile_initcell.
case_eq (Zsem sem i0).
intros.
esplit.
split.
 eapply plus_left.
 econstructor.
 eright.
 econstructor.
 eright.
 econstructor.
  2 : eapply semCONST.
  reflexivity.
  simpl. esplit. split. reflexivity. reflexivity.
 eright.
 econstructor.
 eright.
 econstructor.
 eright.
 econstructor.
 rewrite PTree.gso.
 eassumption.
 apply compile_var_other.
 intro Habs.
 injection Habs; intros; subst.
 eapply Plt_irrefl.
 eassumption.
 rewrite H12. eassumption.
 rewrite <- prog'_hierarchy. eassumption.
 omega.
 rewrite PTree.gss. reflexivity.
 eapply Zsem_semZ.
 eassumption.
 omega.
 reflexivity.
 eright.
 econstructor.
 eright.
 econstructor.
 eright.
 econstructor.
 reflexivity.
 econstructor.
(*  rewrite <- prog'_hierarchy; eauto using Well_formed_hierarchy.array_path_valid, valid_object_classes. *)
 reflexivity.
 eright.
 econstructor.
 eright.
 econstructor.
 unfold compile'.
 eright.
 econstructor.
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
 repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
 eapply state_invariant_codepoint with (p := nil).
 reflexivity.
 2 : simpl; tauto.
 2 : auto.
 2 : reflexivity.
 econstructor.
 split; assumption.
 right; reflexivity.
 2 : reflexivity.
simpl. 
eauto using vars_invariant_newvar.
simpl. reflexivity.
eapply stack_invariant_Kconstrarray.
reflexivity.
simpl. eassumption.
assumption.
omega.
simpl. eauto using vars_invariant_newvar.
simpl. rewrite PTree.gso. rewrite PTree.gso.  rewrite PTree.gso. eassumption.
apply compile_var_other. intro Habs. injection Habs; intros; subst. 
eapply Plt_irrefl.
eassumption.
apply compile_var_other. intro Habs. injection Habs; intros; subst. 
eapply Plt_irrefl with newobj'. eapply Plt_trans. eassumption. assumption.
apply compile_var_other. intro Habs. injection Habs; intros; subst. 
eapply Plt_irrefl with newpath'. eapply Plt_trans. eassumption. eapply Plt_trans. eassumption. assumption.
eassumption. eassumption. assumption.
simpl.
rewrite PTree.gso. rewrite PTree.gss. reflexivity.
apply compile_var_other. intro Habs. injection Habs; intros; subst. 
eapply Plt_irrefl with newpath'. eassumption. 
assumption.
simpl. rewrite PTree.gss. reflexivity.
assumption.
reflexivity. 
simpl.
eapply stack_invariant_newvar_lt.
eapply stack_invariant_newvar_lt.
eapply stack_invariant_newvar_lt.
eassumption.
5 : reflexivity.
3 : reflexivity.
reflexivity.
eauto using Plt_trans. 
eauto using Plt_trans.
eauto using Plt_trans.
eauto using Preservation.goal.
Qed. (* slow *)

Lemma preservation_constr_cons_base_direct_non_virtual : forall obj ar i hp tinit init0 body vars b q stk gl cs auxcs f
  (Hs1 : State.make
    (State.constr obj ar i hp tinit init0 body vars Constructor.base
      Constructor.direct_non_virtual (b :: q)) stk gl cs auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
Focus 2.
 generalize (kind_inj H2).
 simpl.
 intro.
 destruct (State.constr_inj_base H1).
 discriminate.
  injection H1; intros; subst.
clear H7 H8 H9.
destruct (State.constr_inj_base (kind_inj H1)).
injection H3; intros; subst; simpl in  *.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H0; intros; subst; subst.
destruct (State.constr_inj_base H0).
subst; simpl in *.
destruct (invariant_heap0 obj0).
 edestruct (deallocated_objects_not_in_stack invariant_inheritance0).
  2 : eassumption.
 destruct (kind_object_in_construction invariant_inheritance0 (refl_equal _)).
 rewrite H11.
 auto.
generalize (kind invariant_inheritance0).
unfold state_kind_inv; simpl.
intros; invall.
destruct global; simpl in *.
unfold compile_base_initializer.
inversion H4; subst.
assert (x1 = class).
 generalize (path_last H25).
 unfold_ident_in_all; congruence.
subst.
assert (Hsome : is_some (last (p ++ b :: nil))).
 rewrite last_complete.
 exact I.
esplit.
split.
eapply plus_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
eapply step_pathop.
rewrite H8.
esplit.
split.
reflexivity.
reflexivity.
econstructor.
rewrite <- prog'_hierarchy.
eassumption.
reflexivity.
rewrite <- prog'_hierarchy.
esplit.
split.
eassumption.
eapply in_map_bases_elim.
rewrite H17.
eauto using in_or_app.
reflexivity.
eapply star_left.
econstructor.
eapply star_left.
eapply step_casttobase.
rewrite PTree.gso.
eassumption.
apply compile_var_other.
intro Habs.
injection Habs; intros; subst.
destruct (Plt_irrefl curpath).
eapply Plt_trans.
eassumption.
eapply Plt_trans.
eapply Plt_succ.
eapply Plt_trans.
eapply Plt_succ.
eassumption.
rewrite <- prog'_hierarchy.
replace hp0 with x0.
eapply valid_pointer_preserve.
eassumption.
assumption.
eauto using is_some_eq.
assumption.
split.
 reflexivity.
split.
 reflexivity.
rewrite <- prog'_hierarchy.
esplit.
split.
eassumption.
eapply in_map_bases_elim.
rewrite H17.
eauto using in_or_app.
reflexivity.
eapply star_left.
econstructor.
unfold compile'.
eapply star_left.
econstructor.
eleft.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
eapply state_invariant_codepoint with (p := nil); simpl.
reflexivity.
2: tauto.
2 : auto.
2 : reflexivity.
2 : right; reflexivity.
3 : reflexivity.
econstructor.
split.
eapply Plt_succ.
eapply Plt_succ.
eapply vars_invariant_newvar.
eapply vars_invariant_newvar.
assumption.
reflexivity.
eapply stack_invariant_Kconstr with (k := Constructor.base).
reflexivity.
eassumption.
eassumption.
eapply vars_invariant_newvar.
eapply vars_invariant_newvar.
assumption.
rewrite PTree.gso.
rewrite PTree.gso.
eassumption.
apply compile_var_other.
intro Habs.
injection Habs; intros; subst.
destruct (Plt_irrefl curpath).
eapply Plt_trans.
eassumption.
eapply Plt_trans.
eapply Plt_succ.
eapply Plt_trans.
eapply Plt_succ.
eassumption.
apply compile_var_other.
intro Habs.
injection Habs; intros; subst.
destruct (Plt_irrefl curpath).
eapply Plt_trans.
eassumption.
eapply Plt_trans.
eapply Plt_succ.
eassumption.
eassumption.
rewrite PTree.gso.
rewrite PTree.gso.
assumption.
apply compile_var_other.
intro Habs.
injection Habs; intros; subst.
destruct (Plt_irrefl maxvar0).
eapply Plt_trans.
eapply Plt_succ.
eapply Plt_trans.
eapply Plt_succ.
assumption.
apply compile_var_other.
intro Habs.
injection Habs; intros; subst.
destruct (Plt_irrefl maxvar0).
eapply Plt_trans.
eapply Plt_succ.
eassumption.
eassumption.
reflexivity.
split; trivial.
split.
 apply Plt_succ.
split.
 apply Plt_succ.
split.
 apply Plt_succ.
simpl.
split.
rewrite PTree.gso.
rewrite PTree.gss.
reflexivity.
apply compile_var_other.
intro Habs.
injection Habs; intro Habs'.
generalize (Plt_succ (Psucc maxvar0)).
rewrite Habs'.
apply Plt_irrefl.
split; trivial.
exists Hsome.
rewrite PTree.gss.
reflexivity.
assumption.
eauto using Preservation.goal.
Qed. (* slow *)

Lemma preservation_constr_cons_field_scalar_some : forall obj ar i hp tinit init0 body vars b q stk gl cs auxcs f
  (Hs1 :
    State.make
    (State.constr obj ar i hp tinit init0 body vars Constructor.field tt
      (b :: q)) stk gl cs auxcs f = s1
  )
  (Hscalar : match FieldSignature.type b with
               | FieldSignature.Scalar _ => True
               | FieldSignature.Struct _ _ => False
             end)
  code
  (Hinit :
    assoc (Constructor.initializer_key_eq_dec (A:=A))
    (existT (Constructor.init_subkey A) Constructor.field (tt, b)) init0 =
    Some code),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
Focus 2.
 generalize (kind_inj H2).
 simpl.
 intro.
 generalize (State.constr_inj_field H0).
 injection 1; intros; subst.
 rewrite H in Hscalar; contradiction.
Focus 2.
 generalize (kind_inj H1).
 simpl.
 intro.
 generalize (State.constr_inj_field H2).
 injection 1; intros; subst.
 injection H2; intros; subst.
 unfold_ident_in_all; congruence.
injection H1; intros; subst.
clear H7 H8 H9.
destruct k2.
generalize (State.constr_inj_field (kind_inj H1)).
injection 1; intros; subst; simpl in *.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H3; intros; subst; subst.
destruct k2.
generalize (State.constr_inj_field H3).
intro; subst.
replace code0 with code in * by congruence.
unfold compile_constr; simpl.
unfold compile_field_initializer; simpl.
case_eq (FieldSignature.type b).
 Focus 2.
 intros.
 rewrite H11 in *.
 contradiction.
rewrite Hinit.
unfold compile'.
simpl.
intros.
esplit.
split.
eapply plus_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eleft.
reflexivity.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
assert (last p = Some class).
 inversion H5; subst; eauto using path_last.
eapply state_invariant_codepoint with (p := nil) (q := nil).
reflexivity.
2 : simpl; tauto.
2 : auto.
2 : simpl; reflexivity.
2 : right; simpl; reflexivity.
3 : simpl; reflexivity.
econstructor.
split.
 assumption.
assumption.
assumption.
simpl; reflexivity.
simpl; eapply stack_invariant_Kconstr with (k := Constructor.field).
reflexivity.
eassumption.
eassumption.
assumption.
eassumption.
eassumption.
assumption.
eassumption.
reflexivity.
split; trivial.
split; trivial.
split; trivial.
split; trivial.
eauto.
assumption.
eauto using Preservation.goal.
Qed. (* slow *)

Lemma  preservation_constr_cons_field_struct : forall obj ar i hp tinit init0 body vars fs q stk gl cs auxcs f
  (Hs1 : State.make
    (State.constr obj ar i hp tinit init0 body vars Constructor.field tt
      (fs :: q)) stk gl cs auxcs f = s1)
  b n
  (Hstruct : FieldSignature.type fs = FieldSignature.Struct b n),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  injection H1; intros; subst.
  destruct k2.
 generalize (kind_inj H1).
 simpl.
 intro.
 generalize (State.constr_inj_field H2).
 injection 1; intros; subst.
 rewrite Hstruct in H; contradiction.
Focus 2.
injection H1; intros; subst.
 generalize (kind_inj H1).
 simpl.
 intro.
 generalize (State.constr_inj_field H2).
 injection 1; intros; subst.
 unfold_ident_in_all; congruence.
injection H2; intros; subst.
generalize (State.constr_inj_field (kind_inj H2)).
injection 1; intros; subst; simpl in *.
replace b0 with b in * by congruence.
replace n0 with n in * by congruence.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H1; intros; subst; subst.
destruct k2.
generalize (State.constr_inj_field H1).
intro; subst.
unfold compile_constr.
unfold compile_constr_fields.
simpl.
unfold compile_field_initializer at 1.
rewrite Hstruct.
simpl.
destruct global.
destruct (invariant_heap0 obj0).
 edestruct (deallocated_objects_not_in_stack invariant_inheritance0).
  2 : eassumption.
 destruct (kind_object_in_construction invariant_inheritance0 (refl_equal _)).
 rewrite H11.
 auto.
simpl in H10.
generalize (kind invariant_inheritance0).
unfold state_kind_inv; simpl; intro; invall; subst.
assert (x1 = class).
 inversion H4; subst.
 generalize (path_last H23).
 congruence.
subst.
esplit.
split.
eapply plus_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eassumption.
rewrite <- prog'_hierarchy.
econstructor.
rewrite H10.
eassumption.
eassumption.
assumption.
rewrite <- prog'_hierarchy.
eassumption.
rewrite H17; eauto using in_or_app.
Transparent Globals.get_field. unfold Globals.get_field. Opaque Globals.get_field.
rewrite Hstruct.
reflexivity.
reflexivity.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eleft.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
inversion H4; subst.
split; simpl; try assumption.
eapply state_invariant_constr_array.
reflexivity.
eassumption.
eapply valid_array_path_concat.
eassumption.
econstructor.
assumption.
assumption.
eassumption.
eassumption.
rewrite H17; eauto using in_or_app.
eassumption.
econstructor.
compute; congruence.
omega.
split.
 omega.
compute; congruence.
(* compute; congruence. *)
8 : simpl; reflexivity.
8 : simpl; reflexivity.
8 : simpl; reflexivity.
eauto using vars_invariant_newvar.
rewrite PTree.gss. reflexivity.
eapply Plt_succ.
apply Plt_succ.
apply Plt_succ.
apply Plt_succ.
apply Plt_succ.
simpl.
eapply stack_invariant_Kconstrother with (k := Constructor.field).
reflexivity.
eassumption.
eassumption.
6 : reflexivity.
7 : reflexivity.
7 : reflexivity.
eauto using vars_invariant_newvar.
rewrite PTree.gso.
eassumption.
apply compile_var_other.
intro.
injection H24; intro; subst.
destruct (Plt_irrefl curpath).
eapply Plt_trans.
eassumption.
eapply Plt_trans.
eapply Plt_succ.
assumption.
eassumption.
rewrite PTree.gso.
assumption.
apply compile_var_other.
intro.
injection H24; intro; subst.
destruct (Plt_irrefl maxvar0).
eapply Plt_trans.
eapply Plt_succ.
assumption.
assumption.
simpl.
reflexivity.
assumption.
eauto using Preservation.goal.
eauto using preservation_scalar_fields_some_constructed.
Qed. (* slow *)

Lemma preservation_constr_base_direct_non_virtual_nil : forall  obj ar i h p tinit init0 body vars stk gl cs auxcs f
  (Hs1 :
    State.make
    (State.constr obj ar i (h, p) tinit init0 body vars Constructor.base
      Constructor.direct_non_virtual nil) stk gl cs auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
 generalize (kind_inj H2).
 simpl.
 intro.
 destruct (State.constr_inj_base H1).
 discriminate.
  injection H2; intros; subst.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H1; intros; subst; subst.
destruct (State.constr_inj_base H1).
subst; simpl in *.
destruct (invariant_heap0 obj0).
 edestruct (deallocated_objects_not_in_stack invariant_inheritance0).
  2 : eassumption.
 destruct (kind_object_in_construction invariant_inheritance0 (refl_equal _)).
 rewrite H11.
 auto.
generalize (kind invariant_inheritance0).
unfold state_kind_inv; simpl; intros; invall; subst.
destruct global; simpl in *.
unfold compile_base_initializer.
assert (x1 = class).
 inversion H4; subst.
 generalize (path_last H24).
 unfold_ident_in_all; congruence.
subst.
unfold compile_constr_all_fields.
replace (
 match (Program.hierarchy prog) ! class with
          | Some cl =>
              seq
                (setdyntype A nativeop
                   (if if path_eq_dec (h0, p0)
                            (Class.Inheritance.Repeated, class :: nil)
                       then true
                       else false
                    then true
                    else
                     match vborder_list_ex class with
                     | inleft (exist nil _) => true
                     | inleft (exist (_ :: _) _) => false
                     | inright _ => true
                     end) class (compile_var (Newvar curobj))
                   (compile_var (Newvar curpath)))
                (compile_constr_fields (Class.fields cl) class tinit0 init1
                   body0 curobj curpath maxvar0)
          | None => skip A nativeop
          end
) with (let cl := x2 in seq
                (setdyntype A nativeop
                   (if if path_eq_dec (h0, p0)
                            (Class.Inheritance.Repeated, class :: nil)
                       then true
                       else false
                    then true
                    else
                     match vborder_list_ex class with
                     | inleft (exist nil _) => true
                     | inleft (exist (_ :: _) _) => false
                     | inright _ => true
                     end) class (compile_var (Newvar curobj))
                   (compile_var (Newvar curpath)))
                (compile_constr_fields (Class.fields cl) class tinit0 init1
                   body0 curobj curpath maxvar0)
).
simpl.
assert ((Program.hierarchy prog) ! class <> None) by congruence.
destruct (set_dynamic_type_exists hierarchy_wf obj0 ar0 i0 h0 H15 H12 (erase_non_primary_ancestor_dynamic_type (A:=A) obj0 ar0 i0 h0 p0
        is_primary_path dynamic_type)).
esplit.
split.
eapply plus_left.
econstructor.
eapply star_left.
econstructor.
eassumption.
rewrite H10.
eassumption.
rewrite <- prog'_hierarchy.
eassumption.
assumption.
rewrite <- prog'_hierarchy.
eassumption.
destruct (
path_eq_dec (h0, p0) (Class.Inheritance.Repeated, class :: nil)
); auto.
destruct (
  vborder_list_ex class 
); auto.
destruct s0.
destruct x1; try (intros; discriminate).
destruct e.
destruct H21.
right.
rewrite <- prog'_hierarchy.
intros.
exact (virtual_base_vborder_list H25 H21 H23).
eapply star_left.
econstructor.
eleft.
reflexivity.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
unfold_ident_in_all.
replace cn with class in * by congruence.
replace x2 with c in * by congruence.
split; try assumption.
eapply state_invariant_constr with (k := Constructor.field).
reflexivity.
eassumption.
eassumption.
6 : simpl; reflexivity.
6 : simpl; reflexivity.
6 : simpl; reflexivity.
assumption.
eassumption.
assumption.
assumption.
assumption.
simpl.
assumption.
(** dynamic type *)
simpl.
intros.
destruct (
  prod_eq_dec 
   (prod_eq_dec peq (array_path_eq_dec (A := A)))
   Z_eq_dec
    (obj0, ar0, i0) (obj, ar, i)
).
 injection e; intros; subst.
 generalize (dynamic_type_prop H21).
 intro; invall; subst.
 replace x1 with o in * by congruence.
 inversion H4; subst.
 generalize (valid_array_path_last H24 H25).
 intro; subst.
 generalize (path_concat H27 H28 H29).
 intro.
 destruct (Well_formed_hierarchy.path_is_base_dec hierarchy_wf H33 H34).
  (** base *)
  invall; subst.
  refine (_ (set_dynamic_type_BasesConstructed_after_same_path invariant_inheritance0  Hstep (hp := hp) _ (refl_equal _) _ H H35 H37)).
  simpl.
  intro.
  generalize (dynamic_type_unique_strong hierarchy_wf (Preservation.goal hierarchy_wf invariant_inheritance0 Hstep) H21 x9).
  injection 1; intros; subst.
  eapply set_dynamic_type_same_path.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  assumption.
  econstructor.
  eassumption.
  eassumption.
  auto.
  (** not a base *)     
  refine (False_rect _ (set_dynamic_type_BasesConstructed_after_other_path (hp := hp) (s1 := (State.make
              (State.constr obj ar i (h0, p0) tinit0 init1 body0 vars0
                 Constructor.base Constructor.direct_non_virtual nil) stk gl
              cs auxcs f)) (s2 :=  (State.make
               (State.constr obj ar i (h0, p0) tinit0 init1 body0 vars0
                  Constructor.field tt (Class.fields c)) stk gl
               ((obj, (ar, i, (h0, p0)), BasesConstructed) :: cs) auxcs f)) hierarchy_wf invariant_inheritance0 Hstep _ (refl_equal _) _ _ _ H21)).
  econstructor.
  eassumption.
  eassumption.
  auto.
  eassumption.
  intros.
  eapply n.
  2 : eassumption.
  replace x7 with to.
  assumption.
  refine (_ (concat_last _ H36)).
  2 : eauto using path_nonempty.
  rewrite (path_last H35).
  rewrite (path_last H34).
  congruence.
(* other object *)
 erewrite set_dynamic_type_strong_other_cell.
 2 : eassumption.
 2 : congruence.
 generalize (set_dynamic_type_other_before invariant_inheritance0 Hstep (refl_equal _) n H21).
 simpl; eauto.
simpl.
(** allow static cast *)
intros until 1.
sdestruct (
pointer_eq_dec (A:=A) (obj0, (ar0, i0, (h0, p0)))
           (obj, (ar, i, (h, p)))
).
 intro; discriminate.
intros.
destruct (prod_eq_dec (prod_eq_dec peq (@array_path_eq_dec _)) Z_eq_dec (obj, ar, i) (obj0, ar0, i0)).
 injection e; intros; subst.
 inversion H21; subst.
 replace o0 with o in * by congruence.
 inversion H30; subst.
 inversion H4; subst.
 generalize (valid_array_path_last H29 H24).
 intro; subst.
 destruct (Well_formed_hierarchy.path_is_base_dec hierarchy_wf H33 H28).
  destruct s0.
  destruct s0.
  destruct a.
  erewrite set_dynamic_type_same_path.
  2 : eassumption.
  3 : eassumption.
  2 : eassumption.
  3 : eassumption.
  congruence.
  eassumption.
 destruct (
   primary_ancestor_dec
   h0 p0 is_primary_path h p
 ). 
  (** primary path: show that p0 is a base of p *)
  apply False_rect.
  destruct s0.
  destruct s0.
  destruct a.
  destruct H35.
  generalize (concat_repeated H33 H34 H36).
  destruct 1.
  destruct H38.
  subst.
  replace x4 with to in * by (generalize (path_last H28); intro; congruence).
  refine (_ (bases_constructed invariant_inheritance0 hierarchy_wf H21 _ _
    H34 _ _ H36)); simpl; unfold_ident_in_all.
   congruence.
  rewrite H23; simpl; omega.
  rewrite H23; simpl; omega.
  eassumption.
  intro Habs.
  revert H36.
  rewrite Habs.
  Transparent concat. simpl. Opaque concat.
  unfold_ident_in_all.
  rewrite H34.
  destruct (peq to to); try congruence.
  rewrite <- app_nil_end.
  congruence.
(** not a primary base *)
erewrite set_dynamic_type_strong_other_not_primary_base. 
2 : eassumption.
2 : eassumption.
2 : eauto.
2 : assumption.
3 : eassumption.
eauto.
exact (f0 _ (path_last H28)).
(** other cell *)
erewrite set_dynamic_type_strong_other_cell. 
2 : eassumption.
eauto.
assumption.
eauto using Preservation.goal.
simpl.
generalize (vborder_list_ex class).
rewrite H16.
auto. 
Qed. (* slow *) 
    
Lemma preservation_constr_cons_field_scalar_none : forall
  obj ar i h p tinit init0 body vars fs q stk gl cs auxcs f
  (Hs1: State.make
    (State.constr obj ar i (h, p) tinit init0 body vars
      Constructor.field tt (fs :: q)) stk gl cs auxcs f = s1)
  ty (Hscalar : FieldSignature.type fs = FieldSignature.Scalar ty)
  (Hnone : assoc (Constructor.initializer_key_eq_dec (A:=A))
    (existT (Constructor.init_subkey A) Constructor.field (tt, fs)) init0 =
    None),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
injection H1; intros; subst.
clear H7 H8 H9.
destruct k2.
generalize (State.constr_inj_field (kind_inj H1)).
injection 1; intros; subst; simpl in *.
congruence.
 generalize (kind_inj H2).
 simpl.
 intro.
 generalize (State.constr_inj_field H0).
 injection 1; intros; subst.
 congruence.
injection H1; intros; subst.
generalize (kind_inj H1).
simpl.
intro.
generalize (State.constr_inj_field H2).
injection 1; intros; subst.
simpl in *.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H4; intros; subst; subst.
destruct k2.
generalize (State.constr_inj_field H4).
intro; subst.
unfold compile_constr; simpl.
unfold compile_field_initializer; simpl.
rewrite Hscalar.
rewrite Hnone.
esplit.
split.
eapply plus_left.
econstructor.
eapply star_left.
econstructor.
eleft.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
eapply state_invariant_constr with (k := Constructor.field).
reflexivity.
eassumption.
eassumption.
eassumption.
eassumption.
eassumption.
assumption.
eassumption.
simpl; reflexivity.
simpl; reflexivity.
simpl; reflexivity.
simpl; assumption.
eauto using Preservation.goal.
eauto using preservation_scalar_fields_some_constructed.
Qed. (* slow *)

Lemma preservation_Sinitscalar : forall vars varg stl obj ar i h p tinit init0 body fs q stk gl cs auxcs f 
  (Hs1 : 
    State.make (State.codepoint vars (Sinitscalar varg) stl nil)
    (StackFrame.Kconstr obj ar i (h, p) tinit init0 body
      Constructor.field tt fs q :: stk) gl cs auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
injection H5; intros; subst.
destruct (list_inj (stack_inj H5)).
destruct (StackFrame.Kconstr_field_inj H4).
subst.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H7; intros; subst; subst.
inversion H15; subst; try discriminate.
injection H19; intros; invall; subst.
destruct k2.
destruct (StackFrame.Kconstr_field_inj H19).
subst; simpl in *; invall; subst.
inversion H8; invall; subst; simpl in *.
destruct H9; try discriminate.  
subst; simpl in *.
replace x with cn in * by congruence.
assert (
  exists c,
    (Program.hierarchy prog) ! cn = Some c /\
    In b (Class.fields c)
).
 generalize (kind invariant_inheritance0).
 unfold state_kind_inv; simpl; intro; invall; subst.
 replace x2 with cn in * by congruence.
 esplit.
 split.
  eassumption.
 rewrite H29.
 eauto using in_or_app.
invall.
destruct (invariant_heap0 obj0).
 edestruct (deallocated_objects_not_in_stack invariant_inheritance0).
  2 : eassumption.
 destruct (stack_objects_in_construction invariant_inheritance0 (l1 := nil) (refl_equal _) (refl_equal _)). 
 simpl.
 rewrite H16.
 auto.
destruct global; simpl in *.
assert (exists l'',
  Globals.put_field 
  (Globals.field_values globals)
  (obj0, ar0, i0, (h0, p1), b) arg = Some l''
).
revert H3. 
Transparent Globals.put_field. unfold Globals.put_field. Opaque Globals.put_field.
rewrite H.
case_eq (Value.check ty arg); try congruence.
eauto.
invall.
esplit.
split.
eapply plus_left.
econstructor.
eapply star_left.
eapply step_putfield.
eassumption.
rewrite <- prog'_hierarchy.
econstructor.
rewrite H10.
eassumption.
eassumption.
assumption.
rewrite <- prog'_hierarchy.
eassumption.
assumption.
eauto.
eassumption.
reflexivity.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
reflexivity.
reflexivity.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eleft.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
eapply state_invariant_constr with (k := Constructor.field).
reflexivity.
eassumption.
eassumption.
eassumption.
eassumption.
eassumption.
assumption.
eassumption.
simpl; reflexivity.
simpl; reflexivity.
simpl; reflexivity.
simpl; assumption.
simpl.
intros.
destruct (cfield_dec f0 (obj0, ar0, i0, (h0, p1), b)).
 subst.
 erewrite Globals.get_put_field_same in H16.
 2 : eassumption.
 erewrite Globals.get_put_field_same.
 2 : eassumption.
 assumption.
erewrite Globals.get_put_field_other.
2 : eassumption.
erewrite Globals.get_put_field_other in H16.
2 : eassumption.
eauto.
unfold_ident_in_all; congruence.
unfold_ident_in_all; congruence.
eauto using Preservation.goal.
eauto using preservation_scalar_fields_some_constructed.
Qed. (* slow *)
    
Lemma preservation_constr_array_nil_Kconstrother_field : forall obj ar n b init0 vars obj' ar' i' h p tinit' init' body' vars' fs q stk gl cs auxcs f
  (Hs1 : 
    State.make (State.constr_array obj ar n n b init0 vars)
    (StackFrame.Kconstrother obj' ar' i' (h, p) tinit' init' body' vars'
      Constructor.field tt fs q :: stk) gl cs auxcs f = s1
  ), goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  injection H1; intros; omegaContradiction.
injection H; intros; subst; simpl in *.
destruct (list_inj (stack_inj H)).
destruct (StackFrame.Kconstrother_field_inj H0).
subst; simpl in *.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H2; intros; subst; subst.
inversion H16; try discriminate.
subst.
injection H15; intros; subst; simpl in *.
destruct k2.
destruct (StackFrame.Kconstrother_field_inj H15).
subst.
simpl in *.
unfold compile_constrarray.
simpl.
unfold compile_constrarray_aux.
rewrite forup_ge.
2 : omega.
destruct global.
esplit.
esplit.
eapply plus_left.
econstructor.
reflexivity.
reflexivity.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eleft.
reflexivity.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
injection H29; intros; subst.
split; try assumption.
eapply state_invariant_constr with (k := Constructor.field).
simpl; reflexivity.
eassumption.
eassumption.
eassumption.
eassumption.
eassumption.
assumption.
eassumption.
simpl; reflexivity.
simpl; reflexivity.
simpl; reflexivity.
simpl; assumption.
eauto using Preservation.goal.
eauto using preservation_scalar_fields_some_constructed.
Qed. (* slow *)

Lemma preservation_constr_fields_nil : forall obj ar i h p tinit init0 body vars stk gl cs auxcs f 
  (Hs1 :
    State.make
    (State.constr obj ar i (h, p) tinit init0 body vars Constructor.field
      tt nil) stk gl cs auxcs f = s1),
  goal. 
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
injection H; intros; subst.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H0; intros; subst; subst; simpl in *.
destruct k2.
generalize (State.constr_inj_field H0).
intro; subst.
unfold compile_constr; simpl.
unfold compile_field_initializer; simpl.
unfold compile'; simpl.
esplit.
split.
eapply plus_left.
econstructor.
eleft.
repeat rewrite E0_left; eauto using evtr_sem.
assert (forall so,
  stack_invariant (Globals.heap gl) f false stk so stack
).
 intro.
 generalize (kind invariant_inheritance0).
 unfold state_kind_inv; simpl.
 intro; invall; subst.
 destruct stk; try contradiction.
 destruct t; try contradiction; simpl in *.
  inversion H11; subst; try discriminate.
  eapply stack_invariant_Kconstrother; eauto; try reflexivity.
  destruct k0; try discriminate.
  assumption.
 inversion H11; subst; try discriminate.
 eapply stack_invariant_Kconstrothercells; eauto.
split; try assumption.
eapply state_invariant_codepoint with (p := nil).
reflexivity.
2 : simpl; tauto.
2 : auto.
2 : simpl; reflexivity.
2 : simpl; right; reflexivity.
3 : simpl; reflexivity.
econstructor.
auto.
eassumption.
simpl; reflexivity.
eauto.
eauto using Preservation.goal.
Qed. (* slow *)  

(** Destruction *)
  
Lemma preservation_destr_array_cons : forall 
  obj ar j cn stk gl cs auxcs f
  (Hs1 : State.make (State.destr_array obj ar j cn) stk gl cs auxcs f = s1)
  (Hnonnegative : 0 <= j),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  2 : injection H0; intros; omegaContradiction.
  2 : injection H2; intros; omegaContradiction.
injection H6; intros; subst; simpl in *.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H4; intros; subst.
unfold compile_destrarray_aux.
rewrite fordown_gt.
unfold compile_initcell at 1.
case_eq (Zsem sem i).
intros.
destruct global; simpl in *.
destruct (invariant_heap0 obj0).
 edestruct (deallocated_objects_not_in_stack invariant_inheritance0).
  2 : eassumption.
 destruct (kind_object_in_construction invariant_inheritance0 (refl_equal _)).
 rewrite H16.
 auto.
generalize (kind invariant_inheritance0).
unfold state_kind_inv; simpl; intro; invall; subst.
replace x1 with o in * by congruence.
generalize (valid_array_path_last H7 H17).
intro; subst.
esplit.
split.
eapply plus_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
eapply step_native with (args := nil).
reflexivity.
eapply semCONST.
simpl.
esplit.
split.
reflexivity.
reflexivity.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
rewrite PTree.gso.
eassumption.
apply compile_var_other.
intro Habs.
injection Habs; intro; subst.
exact (Plt_irrefl _ H10).
rewrite H14.
eassumption.
rewrite <- prog'_hierarchy.
eassumption.
omega.
rewrite PTree.gss.
reflexivity.
eapply Zsem_semZ.
eassumption.
omega.
reflexivity.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
reflexivity.
rewrite <- prog'_hierarchy.
econstructor.
reflexivity.
eapply star_left.
econstructor.
eapply star_left.
eapply step_call with (args := _ :: _ :: nil).
simpl.
rewrite PTree.gso.
rewrite PTree.gss.
rewrite PTree.gss.
reflexivity.
apply compile_var_other.
intro Habs.
injection Habs; intros; subst.
exact (Plt_irrefl _ H12).
assert ((Program.hierarchy prog) ! cn0 <> None) by congruence.
rewrite (prog'_destructors H25).
esplit.
split.
reflexivity.
split.
reflexivity.
reflexivity.
simpl.
reflexivity.
unfold compile_destructor.
simpl.
eapply star_left.
econstructor.
rewrite H0.
rewrite H1.
rewrite H2.
rewrite H3.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
rewrite PTree.gss.
reflexivity.
reflexivity.
eapply star_left.
econstructor.
unfold compile'.
eapply star_left.
econstructor.
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
reflexivity.
reflexivity.
reflexivity.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
split; simpl; try assumption.
 eapply state_invariant_codepoint with (p := nil); simpl.
 reflexivity.
 2 : simpl; tauto.
 2 : auto.
 2 : reflexivity.
 econstructor.
 trivial.
 right; reflexivity.
 2 : simpl; reflexivity.
simpl. 
replace hp0 with hp.
eapply vars_invariant_oldvar.
intro.
intro.
rewrite PTree.gempty.
congruence.
eauto using true_uniq.
simpl; reflexivity.
simpl.
eapply stack_invariant_Kdestr.
reflexivity.
eassumption.
econstructor.
eassumption.
assumption.
assumption.
eleft with (lt := nil).
reflexivity.
reflexivity.
simpl.
rewrite H0.
trivial.
replace hp0 with hp.
eapply vars_invariant_oldvar.
intro.
intro.
rewrite PTree.gempty.
congruence.
eauto using true_uniq.
rewrite PTree.gso.
rewrite PTree.gss.
reflexivity.
apply compile_var_other; congruence.
2 : rewrite PTree.gso.
2 : rewrite PTree.gso.
2 : rewrite PTree.gss.
compute; congruence.
reflexivity.
apply compile_var_other; congruence.
apply compile_var_other; congruence.
compute; congruence.
sdestruct (path_eq_dec (Class.Inheritance.Repeated, cn0 :: nil)
              (Class.Inheritance.Repeated, cn0 :: nil)
); congruence.
eapply stack_invariant_Kdestrcell.
reflexivity.
6 : reflexivity.
rewrite PTree.gso.
rewrite PTree.gso.
rewrite PTree.gso.
eassumption.
apply compile_var_other.
intro Habs.
injection Habs; intro; subst.
exact (Plt_irrefl _ H10).
apply compile_var_other.
intro Habs.
injection Habs; intro; subst.
exact (Plt_irrefl _ (Plt_trans _ _ _ H10 H11)).
apply compile_var_other.
intro Habs.
injection Habs; intro; subst.
exact (Plt_irrefl _ (Plt_trans _ _ _ H10 (Plt_trans _ _ _ H11 H12))).
eassumption.
eassumption.
eassumption.
eassumption.
eapply stack_invariant_newvar_lt.
eapply stack_invariant_newvar_lt.
eapply stack_invariant_newvar_lt.
eassumption.
reflexivity.
2 : reflexivity.
3 : reflexivity.
eauto using Plt_trans.
eauto using Plt_trans.
eauto using Plt_trans.
(** dynamic type *)
simpl.
intros.
destruct (
  prod_eq_dec 
   (prod_eq_dec peq (array_path_eq_dec (A := A)))
   Z_eq_dec
   (obj0, ar0, i)    (obj, ar, i0)
).
 injection e; intros; subst.
 generalize (dynamic_type_prop H25).
 intro; invall; subst.
 replace x2 with o in * by congruence.
 generalize (valid_array_path_last H27 H7).
 intro; subst.
 assert (
   path (Program.hierarchy prog) x6 sp cn0 sh
 ) by eauto using path_concat.  
 refine (_ (set_dynamic_type_BasesConstructed_after_same_path invariant_inheritance0 Hstep (h := Class.Inheritance.Repeated) (p := cn0 :: nil) (hp := I)  _ _ _ _ _ _)); simpl.
 Focus 2.
 econstructor.
 eassumption.
 econstructor.
 eassumption.
 eassumption.
 assumption.
 eleft with (lt := nil).
 reflexivity.
 reflexivity.
 simpl.
 rewrite H0.
 trivial.
 4 : reflexivity.
 4 : eassumption.
 4 : erewrite concat_trivial_left; eauto.
 intro.
 refine (_ (set_dynamic_type_StartedDestructing_before_most_derived
 invariant_inheritance0 Hstep H26 H27 (conj H29 H33) _ _ H28)).
 simpl.
 intro.
 generalize (dynamic_type_unique_strong hierarchy_wf (Preservation.goal hierarchy_wf invariant_inheritance0 Hstep) H25 x3).
 injection 1; intros; subst; eauto.
 simpl.
 sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i0, (Class.Inheritance.Repeated, cn0 :: nil)))
         (obj, (ar, i0, (Class.Inheritance.Repeated, cn0 :: nil)))
 ); congruence.
 simpl.
 sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i0, (Class.Inheritance.Repeated, cn0 :: nil)))
         (obj, (ar, i0, (Class.Inheritance.Repeated, cn0 :: nil)))
 ); try congruence.
 assert (0 <= i0 <= i0) by omega.
 unfold_ident_in_all.
 rewrite (H21 _ H34).
 congruence.
 reflexivity.
 auto.
 generalize (set_dynamic_type_other_before invariant_inheritance0 Hstep (refl_equal _) n0 H25).
 intro; eauto.
(** allow static cast *)
intros until 1.
sdestruct (
pointer_eq_dec (A:=A)
         (obj0, (ar0, i, (Class.Inheritance.Repeated, cn0 :: nil)))
         (obj, (ar, i0, (h, p)))
); eauto.
intro; discriminate.
eauto using Preservation.goal.
omega.
Qed. (* slow *) 
  
Lemma preservation_destr_field_cons_scalar : forall obj ar i h p fs l stk gl cs auxcs f
  (Hs1 :
    State.make
    (State.destr obj ar i (h, p) Constructor.field tt (fs :: l)) stk gl
    cs auxcs f = s1)
  ty (Hscalar : FieldSignature.type fs = FieldSignature.Scalar ty),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat Zminus.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
Focus 2.
 injection H2; intros; subst.
 generalize (State.destr_inj_field (kind_inj H2)).
 injection 1; intros; subst; simpl in *.
 congruence.
injection H0; intros; subst.
generalize (kind_inj H0).
simpl.
intro.
generalize (State.destr_inj_field H1).
injection 1; intros; subst.
simpl in *.
replace ty0 with ty in * by congruence.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H3; intros; subst; subst.
destruct k2.
generalize (State.destr_inj_field H3).
intro; subst.
unfold compile_destr; simpl.
unfold compile_destr_field; simpl.
rewrite Hscalar.
esplit.
split.
eapply plus_left.
econstructor.
eapply star_left.
econstructor.
eleft.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
split; simpl; try assumption.
eapply state_invariant_destr with (k := Constructor.field).
reflexivity.
eassumption.
eassumption.
eassumption.
eassumption.
eassumption.
eassumption.
simpl; reflexivity.
simpl; reflexivity.
simpl; reflexivity.
reflexivity.
simpl; assumption.
intros.
apply invariant_field_values0.
revert H10.
Transparent Globals.get_field. unfold Globals.get_field. Opaque Globals.get_field.
destruct f0.
destruct p.
destruct p.
destruct p.
destruct p1.
case_eq (FieldSignature.type t).
 intros.
 destruct (cfield_dec 
   (obj0, ar0, i0, (h0, p0), fs)
   (p, a, z, (t0, l0), t)
 ).
  injection e; intros; subst.
  rewrite find_remove_field_same in H11.
  discriminate.
 rewrite find_remove_field_other in H11.
 assumption.
 assumption.
 trivial.
eauto using Preservation.goal.
eauto using preservation_scalar_fields_some_constructed.
Qed. (* slow *)

Lemma preservation_destr_field_cons_struct : forall obj ar i h p fs l stk gl cs auxcs f
  (Hs1 : State.make
    (State.destr obj ar i (h, p) Constructor.field tt (fs :: l)) stk gl
    cs auxcs f = s1)
 b n 
 (Hstruct : FieldSignature.type fs = FieldSignature.Struct b n),
 goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat Zminus.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
injection H0; intros; subst.
generalize (kind_inj H0).
simpl.
intro.
generalize (State.destr_inj_field H1).
congruence.
 injection H2; intros; subst.
 generalize (State.destr_inj_field (kind_inj H2)).
 injection 1; intros; subst; simpl in *.
 replace b0 with b in * by congruence.
 replace n0 with n in * by congruence.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H1; intros; subst; subst.
destruct k2.
generalize (State.destr_inj_field H1).
intro; subst.
unfold compile_destr; simpl.
unfold compile_destr_field; simpl.
rewrite Hstruct.
destruct global; simpl in *.
destruct (invariant_heap0 obj0).
 edestruct (deallocated_objects_not_in_stack invariant_inheritance0).
  2 : eassumption.
 destruct (kind_object_in_construction invariant_inheritance0 (refl_equal _)).
 rewrite H10.
 auto.
generalize (kind invariant_inheritance0).
unfold state_kind_inv; simpl; intro; invall; subst.
inversion H4; subst.
assert (x1 = class).
 generalize (path_last H22).
 congruence.
subst.
assert (
  In fs (Class.fields x2)
).
 rewrite <- (rev_involutive).
 rewrite H16.
 eapply In_rev.
 rewrite rev_involutive.
 eauto using in_or_app.
esplit.
split.
eapply plus_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eassumption.
rewrite <- prog'_hierarchy.
econstructor.
rewrite H9.
eassumption.
eassumption.
assumption.
rewrite <- prog'_hierarchy.
eassumption.
assumption.
Transparent Globals.get_field. unfold Globals.get_field. Opaque Globals.get_field.
rewrite Hstruct.
reflexivity.
reflexivity.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eleft.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
split; simpl; try assumption.
eapply state_invariant_destrarray; simpl.
reflexivity.
eassumption.
eapply valid_array_path_concat.
eassumption.
econstructor.
assumption.
assumption.
eassumption.
eassumption.
assumption.
eassumption.
eleft with (to_n := Zpos n).
compute; congruence.
omega.
(* compute; congruence. *)
7 : reflexivity.
rewrite PTree.gss.
reflexivity.
5 : simpl; reflexivity.
eapply Plt_succ.
eapply Plt_succ.
eapply Plt_succ.
eapply Plt_succ.
eapply stack_invariant_Kdestrother with (k := Constructor.field).
reflexivity.
eassumption.
eassumption.
5 : split.
5 : unfold compile_destr.
5 : reflexivity.
5 : reflexivity.
rewrite PTree.gso.
eassumption.
apply compile_var_other.
intro.
injection H24; intros; subst.
exact (Plt_irrefl _ (Plt_trans _ _ _ H8 (Plt_trans _ _ _ (Plt_succ _) H6))).
assumption.
rewrite PTree.gso.
assumption.
apply compile_var_other.
intro.
injection H24; intros; subst.
exact (Plt_irrefl _ (Plt_trans _ _ _ H8 (Plt_succ _))).
assumption.
reflexivity.
assumption.
eauto using Preservation.goal.
eauto using preservation_scalar_fields_some_constructed.
Qed. (* slow *) 

Lemma preservation_destr_array_nil_Kdestrother_field : forall obj ar j cn obj' ar' i' hp' fs l stk gl cs auxcs f
  (Hs1 :
    State.make (State.destr_array obj ar j cn)
    (StackFrame.Kdestrother obj' ar' i' hp' Constructor.field tt fs l
      :: stk) gl cs auxcs f = s1)
  (Hnil : j = -1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  injection H6; intros; omegaContradiction.
injection H0; intros; subst; simpl in *.
destruct (list_inj (stack_inj H0)).
destruct (StackFrame.Kdestrother_field_inj H).
subst.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H2; intros; subst.
inversion H12; subst; simpl in *; try discriminate.
injection H13; intros; subst.
destruct k2.
destruct (StackFrame.Kdestrother_field_inj H13).
invall; subst; simpl in *.
unfold compile_destrarray_aux.
rewrite fordown_le; try omega.
destruct global; simpl in *.
esplit.
split.
eapply plus_left.
econstructor.
reflexivity.
reflexivity.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eleft.
reflexivity.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
injection H22; intros; subst.
split; simpl; try assumption.
eapply state_invariant_destr with (k := Constructor.field).
reflexivity.
eassumption.
eassumption.
eassumption.
eassumption.
eassumption.
eassumption.
simpl; reflexivity.
simpl; reflexivity.
simpl; reflexivity.
reflexivity.
simpl; assumption.
eauto using Preservation.goal.
eauto using preservation_scalar_fields_some_constructed.
Qed. (* slow *)
  
Lemma preservation_destr_field_nil : forall obj ar i h p stk gl cs auxcs f
  (Hs1 : State.make (State.destr obj ar i (h, p) Constructor.field tt nil) stk gl cs auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat Zminus.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
injection H2; intros; subst.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H3; intros; subst; subst.
destruct k2.
generalize (State.destr_inj_field H3).
intro; subst.
unfold compile_destr; simpl.
unfold compile_destr_all_direct_non_virtual_bases; simpl.
inversion H5; subst.
assert (cn = class).
 generalize (path_last H13).
 unfold_ident_in_all; congruence.
subst.
rewrite H0.
assert (bases =
rev (
map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b)
         (filter
            (fun hb : Class.Inheritance.t * ident =>
             let (y, _) := hb in
             match y with
             | Class.Inheritance.Repeated => true
             | Class.Inheritance.Shared => false
             end) (Class.super c))
)
).
 rewrite <- H1. 
 rewrite rev_involutive.
 trivial.
subst.
esplit.
split.
eapply plus_left.
econstructor.
eapply star_left.
econstructor.
eleft.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
 generalize (kind invariant_inheritance0).
 unfold state_kind_inv; simpl; intro; invall; subst.
split; simpl; try assumption.
eapply state_invariant_destr with (k := Constructor.base); simpl.
reflexivity.
eassumption.
eassumption.
eassumption.
eassumption.
assumption.
eassumption.
simpl.
reflexivity.
reflexivity.
reflexivity.
simpl; reflexivity.
simpl; assumption.
(** dynamic type *)
intros.
destruct
(
  prod_eq_dec 
   (prod_eq_dec peq (array_path_eq_dec (A := A)))
   Z_eq_dec
    (obj0, ar0, i0) (obj, ar, i)
).
 injection e; intros; subst.
 refine (False_rect _ (set_dynamic_type_StartedConstructing_after hierarchy_wf invariant_inheritance0 Hstep _ _ _ _ H16)); simpl.
 eassumption.
 sdestruct (
 pointer_eq_dec (A:=A) (obj, (ar, i, (h0, p0)))
         (obj, (ar, i, (h0, p0)))
 ).
  reflexivity.
 destruct n; trivial.
 auto.
 sdestruct (
pointer_eq_dec (A:=A) (obj, (ar, i, (h0, p0)))
         (obj, (ar, i, (h0, p0)))
 ).
  unfold_ident_in_all.
  rewrite H15.
  congruence.
 destruct n; trivial.
(** other object *)
 generalize (set_dynamic_type_other_before invariant_inheritance0 Hstep (refl_equal _) n H16).
 simpl; eauto.
intros until 1.
sdestruct (
pointer_eq_dec (A:=A) (obj0, (ar0, i0, (h0, p0)))
           (obj, (ar, i, (h, p)))
); eauto.
intro; discriminate.
eauto using Preservation.goal.
Qed. (* slow *)
  
Lemma preservation_destr_base_cons_direct_non_virtual : forall obj ar i h p b bases stk gl cs auxcs f
    (Hs1 :
      State.make
      (State.destr obj ar i (h, p) Constructor.base Constructor.direct_non_virtual (b :: bases)) stk
      gl cs auxcs f = s1),
    goal.
Proof.
 Opaque Globals.get_field Globals.put_field concat Zminus.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  Focus 2.
   generalize (kind_inj H1).
   simpl; intro.
   destruct (State.destr_inj_base H0).
   discriminate.
injection H7; intros; subst.
destruct (State.destr_inj_base (kind_inj H7)).
subst.
injection H0; intros; subst.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H; intros; subst.
destruct (State.destr_inj_base H).
subst.
unfold compile_destr.
unfold compile_destr_direct_non_virtual_bases.
simpl.
unfold compile_base_finalizer at 1.
simpl.
destruct global; simpl in *.
destruct (invariant_heap0 obj0).
 edestruct (deallocated_objects_not_in_stack invariant_inheritance0).
  2 : eassumption.
 destruct (kind_object_in_construction invariant_inheritance0 (refl_equal _)).
 rewrite H13.
 auto.
inversion H6; subst.
assert (last p0 = Some class).
 generalize (path_last H17).
 unfold_ident_in_all.
 congruence.
generalize (kind invariant_inheritance0).
unfold state_kind_inv; simpl; intro; invall; subst.
replace x1 with class in * by congruence.
assert (In (Class.Inheritance.Repeated, b) (Class.super x2)).
 eapply in_map_bases_elim.
 eapply In_rev.
 rewrite H24.
 eauto using in_or_app.
refine (_ (set_dynamic_type_exists
hierarchy_wf obj0 ar0 i0 h0 (p0 := p0 ++ b :: nil) _ _ (erase_non_primary_ancestor_dynamic_type (A:=A) obj0 ar0 i0 h0
        (p0 ++ b :: nil) is_primary_path dynamic_type))).
2 : eapply last_complete.
2 : congruence.
destruct 1.
assert (
valid_relative_pointer (A:=A) (Program.hierarchy prog) 
     (Object.class o) (Object.arraysize o) ar0 X i0 h0 
     (p0 ++ b :: nil) b
).
 econstructor.
 eassumption.
 assumption.
 assumption.
 eapply path_concat.
 eassumption.
 eleft with (lf := b :: nil) (lt := class :: nil).
 reflexivity.
 simpl; reflexivity.
 simpl.
 rewrite H23.
 sdestruct (In_dec super_eq_dec (Class.Inheritance.Repeated, b) (Class.super x2)
); try contradiction.
 rewrite H1.
 trivial.
 Transparent concat. unfold concat. Opaque concat.
 simpl.
 rewrite H18.
 unfold_ident.
 destruct (peq class class); congruence.
esplit.
esplit.
eapply plus_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
rewrite H10.
eauto.
rewrite H10.
econstructor.
rewrite <- prog'_hierarchy.
eassumption.
reflexivity.
rewrite <- prog'_hierarchy.
esplit.
split.
eassumption.
assumption.
reflexivity.
eapply star_left.
econstructor.
eapply star_left.
eapply step_casttobase with (hp' := hp').
rewrite PTree.gso.
eassumption.
apply compile_var_other.
intro Habs.
injection Habs; intro; subst.
destruct (Plt_irrefl curpath).
eapply Plt_trans.
eassumption.
eapply Plt_trans.
eapply Plt_succ.
eapply Plt_trans.
eapply Plt_succ.
assumption.
rewrite <- prog'_hierarchy.
econstructor.
rewrite H12.
eassumption.
eassumption.
assumption.
split.
reflexivity.
split.
reflexivity.
rewrite <- prog'_hierarchy.
esplit.
split.
eassumption.
assumption.
reflexivity.
eapply star_left.
econstructor.
eapply star_left.
eapply step_call with (args := _ :: _ :: nil).
simpl.
rewrite PTree.gss.
rewrite PTree.gso.
rewrite PTree.gss.
reflexivity.
apply compile_var_other.
intro Habs.
injection Habs.
intro Habs'.
apply (Plt_irrefl (Psucc  maxvar0)).
rewrite <- Habs' at 2.
apply Plt_succ.
rewrite prog'_destructors.
eauto.
congruence.
simpl; reflexivity.
unfold compile_destructor; simpl.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
rewrite PTree.gss.
reflexivity.
rewrite H12.
eassumption.
rewrite <- prog'_hierarchy.
eassumption.
rewrite PTree.gso.
rewrite PTree.gss.
reflexivity.
apply compile_var_other; congruence.
rewrite <- prog'_hierarchy.
eassumption.
intro; discriminate.
rewrite H1.
rewrite H2.
rewrite H3.
rewrite H4.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
rewrite PTree.gss.
reflexivity.
reflexivity.
eapply star_left.
econstructor.
unfold compile'.
eapply star_left.
econstructor.
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
reflexivity.
reflexivity.
reflexivity.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem, evtr_sem.
split; simpl; try assumption.
 eapply state_invariant_codepoint with (p := nil); simpl.
 reflexivity.
 2 : simpl; tauto.
 2 : auto.
 2 : reflexivity.
 econstructor.
 trivial.
 right; reflexivity.
 2 : simpl; reflexivity.
simpl. 
eapply vars_invariant_oldvar.
intro.
intro.
rewrite PTree.gempty.
congruence.
simpl; reflexivity.
simpl.
eapply stack_invariant_Kdestr.
reflexivity.
eassumption.
eassumption.
eapply vars_invariant_oldvar.
intro.
intro.
rewrite PTree.gempty.
congruence.
rewrite PTree.gso.
rewrite PTree.gss.
reflexivity.
apply compile_var_other; congruence.
2 : rewrite PTree.gso.
2 : rewrite PTree.gso.
2 : rewrite PTree.gss.
compute; congruence.
reflexivity.
apply compile_var_other; congruence.
apply compile_var_other; congruence.
compute; congruence.
sdestruct (
 path_eq_dec (h0, p0 ++ b :: nil)
              (Class.Inheritance.Repeated, b :: nil)
); try reflexivity.
destruct p0; try contradiction.
destruct p0; discriminate.
eapply stack_invariant_Kdestrother with (k := Constructor.base); simpl.
reflexivity.
eassumption.
eassumption.
5 : simpl; split.
7 : simpl; reflexivity.
7 : assumption.
5 : unfold compile_destr_direct_non_virtual_bases; simpl; reflexivity.
rewrite PTree.gso.
rewrite PTree.gso.
eassumption.
apply compile_var_other.
intro Habs.
injection Habs; intro; subst.
eapply Plt_irrefl with curpath.
eapply Plt_trans.
eassumption.
eapply Plt_trans.
eapply Plt_succ.
eapply Plt_trans.
eapply Plt_succ.
assumption.
apply compile_var_other.
intro Habs.
injection Habs; intro; subst.
eapply Plt_irrefl with curpath.
eapply Plt_trans.
eassumption.
eapply Plt_trans.
eapply Plt_succ.
assumption.
assumption.
rewrite PTree.gso.
rewrite PTree.gso.
assumption.
apply compile_var_other.
intro Habs.
injection Habs; intro; subst.
eapply Plt_irrefl with (Psucc (Psucc maxvar0)).
eapply Plt_trans.
eassumption.
eapply Plt_trans.
eapply Plt_succ.
eapply Plt_succ.
apply compile_var_other.
intro Habs.
injection Habs; intro; subst.
eapply Plt_irrefl with (Psucc maxvar0).
eapply Plt_trans.
eassumption.
eapply Plt_succ.
assumption.
reflexivity.
(** dynamic type *)
simpl.
intros.
destruct (
  prod_eq_dec 
   (prod_eq_dec peq (array_path_eq_dec (A := A)))
   Z_eq_dec
   (obj0, ar0, i0)    (obj, ar, i)
).
 injection e; intros; subst.
 generalize (dynamic_type_prop H30).
 intro; invall; subst.
 replace x4 with o in * by congruence.
 generalize (valid_array_path_last H32 H13).
 intro; subst.
 generalize (path_concat H35 H36 H37).
 intro.
 inversion H28; subst.
 destruct (Well_formed_hierarchy.path_is_base_dec hierarchy_wf H42 H33).
  (** base *)
  invall; subst.
  refine (_ (set_dynamic_type_BasesConstructed_after_same_path invariant_inheritance0  Hstep (hp := hp') _ (refl_equal _) _ (last_complete _ _) H43 H45)).
  simpl.
  intro.
  generalize (dynamic_type_unique_strong hierarchy_wf (Preservation.goal hierarchy_wf invariant_inheritance0 Hstep) H30 x10).
  injection 1; intros; subst.
  eapply set_dynamic_type_same_path.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  assumption.
  econstructor.
  eassumption.
  eassumption.
  auto.
  (** not a base *)     
  refine (False_rect _ (set_dynamic_type_BasesConstructed_after_other_path (hp := hp') hierarchy_wf invariant_inheritance0 Hstep _ (refl_equal _) _ _ _ H30)).
  econstructor.
  eassumption.
  eassumption.
  auto.
  eapply last_complete.
  intros.
  eapply n.
  2 : eassumption.
  replace x8 with to.
  assumption.
  refine (_ (concat_last _ H44)).
  2 : eauto using path_nonempty.
  rewrite (path_last H33).
  rewrite (path_last H43).
  congruence.
(* other object *)
 erewrite set_dynamic_type_strong_other_cell.
 2 : eassumption.
 2 : unfold_ident_in_all; congruence.
 generalize (set_dynamic_type_other_before invariant_inheritance0 Hstep (refl_equal _) n H30).
 simpl; eauto.
(** allow static cast *)
intros until 1.
sdestruct (
pointer_eq_dec (A:=A) (obj0, (ar0, i0, (h0, p0 ++ b :: nil)))
           (obj, (ar, i, (h, p)))
).
 intro; discriminate.
intros.
destruct (prod_eq_dec (prod_eq_dec peq (@array_path_eq_dec _)) Z_eq_dec (obj, ar, i) (obj0, ar0, i0)).
 injection e; intros; subst.
 inversion H30; subst.
 replace o0 with o in * by congruence.
 inversion H38; subst.
 generalize (valid_array_path_last H32 H13).
 intro; subst.
 inversion H28; subst.
 destruct (Well_formed_hierarchy.path_is_base_dec hierarchy_wf H41 H36).
  destruct s0.
  destruct s0.
  destruct a.
  erewrite set_dynamic_type_same_path.
  2 : eassumption.
  3 : eassumption.
  2 : eassumption.
  3 : eassumption.
  congruence.
  eassumption.
 destruct (
   primary_ancestor_dec
   h0 (p0 ++ b :: nil) is_primary_path h p
 ). 
  (** primary path: show that p0 is a base of p+b *)
  apply False_rect.
  destruct s0.
  destruct s0.
  destruct a.
  destruct H43.
  generalize (concat_repeated H41 H42 H44).
  destruct 1.
  destruct H46.
  subst.
  replace x5 with to in * by (generalize (path_last H36); intro; congruence).
  refine (_ (bases_constructed (Preservation.goal hierarchy_wf invariant_inheritance0 Hstep) hierarchy_wf H30 _ _
    H42 _ _ H44)); simpl; unfold_ident_in_all.
  sdestruct (
pointer_eq_dec (A:=A) (obj0, (ar0, i0, (h0, p0 ++ b :: nil)))
         (obj0, (ar0, i0, (h0, p0 ++ b :: nil)))
  ); congruence.
  sdestruct (
    pointer_eq_dec (A:=A) (obj0, (ar0, i0, (h0, p0 ++ b :: nil)))
    (obj0, (ar0, i0, (h0, p)))
  ); try congruence.
  rewrite H31; simpl; omega.
  sdestruct (
    pointer_eq_dec (A:=A) (obj0, (ar0, i0, (h0, p0 ++ b :: nil)))
    (obj0, (ar0, i0, (h0, p)))
  ); try congruence.
  rewrite H31; simpl; omega.   
  eassumption.
  intro Habs.
  revert H44.
  rewrite Habs.
  Transparent concat. simpl. Opaque concat.
  unfold_ident_in_all.
  rewrite H42.
  destruct (peq to to); try congruence.
  rewrite <- app_nil_end.
  congruence.
(** not a primary base *)
erewrite set_dynamic_type_strong_other_not_primary_base. 
2 : eassumption.
2 : eassumption.
2 : eauto.
2 : assumption.
3 : eassumption.
eauto.
exact (f0 _ (path_last H36)).
(** other cell *)
erewrite set_dynamic_type_strong_other_cell. 
2 : eassumption.
eauto.
assumption.
eauto using Preservation.goal.
Qed. (* slow *) 

Lemma preservation_destr_base_cons_virtual : forall obj ar i h p b bases stk gl cs auxcs f
  (Hs1 :
    State.make
    (State.destr obj ar i (h, p) Constructor.base Constructor.virtual
      (b :: bases)) stk gl cs auxcs f = s1),
  goal.
Proof.
 Opaque Globals.get_field Globals.put_field concat Zminus.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  Focus 2.
   generalize (kind_inj H).
   simpl; intro.
   destruct (State.destr_inj_base H0).
   discriminate.
  Focus 2.
   generalize (kind_inj H1).
   simpl; intro.
   destruct (State.destr_inj_base H2).
   discriminate.
injection H7; intros; subst.
destruct (State.destr_inj_base (kind_inj H7)).
subst.
injection H0; intros; subst.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H; intros; subst.
destruct (State.destr_inj_base H).
subst.
unfold compile_destr.
unfold compile_destr_virtual_bases.
simpl.
unfold compile_base_finalizer at 1.
simpl.
destruct global; simpl in *.
destruct (invariant_heap0 obj0).
 edestruct (deallocated_objects_not_in_stack invariant_inheritance0).
  2 : eassumption.
 destruct (kind_object_in_construction invariant_inheritance0 (refl_equal _)).
 rewrite H13.
 auto.
generalize (kind invariant_inheritance0).
unfold state_kind_inv; simpl; intro; invall; subst.
inversion H6; subst.
assert (x1 = class).
 generalize (path_last H26). 
 simpl; congruence.
subst.
assert (is_virtual_base_of (Program.hierarchy prog) b class).
 eapply vborder_list_virtual_base.
 eassumption.
 eassumption.
 eapply In_rev.
 rewrite rev_involutive.
 eauto using in_or_app.
refine (_ (set_dynamic_type_exists
hierarchy_wf obj0 ar0 i0 Class.Inheritance.Shared (p0 := b :: nil) _ _ (erase_non_primary_ancestor_dynamic_type (A:=A) obj0 ar0 i0 Class.Inheritance.Shared
       (b :: nil) is_primary_path dynamic_type))).
2 : reflexivity.
2 : congruence.
destruct 1.
assert (
valid_relative_pointer (A:=A) (Program.hierarchy prog) 
     (Object.class o) (Object.arraysize o) ar0 X i0 Class.Inheritance.Shared 
     (b :: nil) b
).
 econstructor.
 eassumption.
 assumption.
 assumption.
 eapply path_concat.
 eassumption.
 eright.
 eassumption.
 eleft with  (lt := nil).
 reflexivity.
 simpl; reflexivity.
 simpl.
 rewrite H1.
 trivial.
 reflexivity.
assert (X = class).
 inversion H26; congruence.
subst.
esplit.
esplit.
eapply plus_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
rewrite H10.
eauto.
rewrite H10.
econstructor.
rewrite <- prog'_hierarchy.
eassumption.
reflexivity.
split.
reflexivity.
rewrite <- prog'_hierarchy.
eapply vborder_list_virtual_base.
eassumption.
eassumption.
eapply In_rev.
rewrite rev_involutive.
eauto using in_or_app.
reflexivity.
eapply star_left.
econstructor.
eapply star_left.
eapply step_casttobase with (p' := b :: nil) (hp' := I).
rewrite PTree.gso.
eassumption.
apply compile_var_other.
intro Habs.
injection Habs; intro; subst.
destruct (Plt_irrefl curpath).
eapply Plt_trans.
eassumption.
eapply Plt_trans.
eapply Plt_succ.
eapply Plt_trans.
eapply Plt_succ.
assumption.
rewrite <- prog'_hierarchy.
econstructor.
rewrite H12.
eassumption.
eassumption.
assumption.
split.
rewrite <- prog'_hierarchy.
assumption.
split.
reflexivity.
split.
reflexivity.
split.
reflexivity.
reflexivity.
reflexivity.
eapply star_left.
econstructor.
eapply star_left.
eapply step_call with (args := _ :: _ :: nil).
simpl.
rewrite PTree.gss.
rewrite PTree.gso.
rewrite PTree.gss.
reflexivity.
apply compile_var_other.
intro Habs.
injection Habs.
intro Habs'.
apply (Plt_irrefl (Psucc  maxvar0)).
rewrite <- Habs' at 2.
apply Plt_succ.
rewrite prog'_destructors.
eauto.
congruence.
simpl; reflexivity.
unfold compile_destructor; simpl.
eapply star_left.
econstructor.
eapply star_left.
eapply step_setdyntype with (p := b :: nil).
rewrite PTree.gss.
reflexivity.
rewrite H12.
eassumption.
rewrite <- prog'_hierarchy.
eassumption.
rewrite PTree.gso.
rewrite PTree.gss.
reflexivity.
apply compile_var_other; congruence.
rewrite <- prog'_hierarchy.
eassumption.
intro; discriminate.
rewrite H1.
rewrite H2.
rewrite H3.
rewrite H4.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
rewrite PTree.gss.
reflexivity.
reflexivity.
eapply star_left.
econstructor.
unfold compile'.
eapply star_left.
econstructor.
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
reflexivity.
reflexivity.
reflexivity.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem, evtr_sem.
split; simpl; try assumption.
 eapply state_invariant_codepoint with (p := nil); simpl.
 reflexivity.
 2 : simpl; tauto.
 2 : auto.
 2 : reflexivity.
 econstructor.
 trivial.
 right; reflexivity.
 2 : simpl; reflexivity.
simpl. 
replace hp' with I.
eapply vars_invariant_oldvar.
intro.
intro.
rewrite PTree.gempty.
congruence.
eauto using true_uniq.
simpl; reflexivity.
simpl.
eapply stack_invariant_Kdestr.
reflexivity.
eassumption.
eassumption.
replace hp' with I by eauto using true_uniq.
eapply vars_invariant_oldvar.
intro.
intro.
rewrite PTree.gempty.
congruence.
rewrite PTree.gso.
rewrite PTree.gss.
reflexivity.
apply compile_var_other; congruence.
2 : rewrite PTree.gso.
2 : rewrite PTree.gso.
2 : rewrite PTree.gss.
compute; congruence.
reflexivity.
apply compile_var_other; congruence.
apply compile_var_other; congruence.
compute; congruence.
sdestruct (
 path_eq_dec (Class.Inheritance.Shared, b :: nil)
              (Class.Inheritance.Repeated, b :: nil)
); congruence.
eapply stack_invariant_Kdestrother with (k := Constructor.base); simpl.
reflexivity.
eassumption.
eassumption.
5 : simpl; split.
7 : simpl; reflexivity.
7 : assumption.
5 : unfold compile_destr_virtual_bases; simpl; reflexivity.
rewrite PTree.gso.
rewrite PTree.gso.
eassumption.
apply compile_var_other.
intro Habs.
injection Habs; intro; subst.
eapply Plt_irrefl with curpath.
eapply Plt_trans.
eassumption.
eapply Plt_trans.
eapply Plt_succ.
eapply Plt_trans.
eapply Plt_succ.
assumption.
apply compile_var_other.
intro Habs.
injection Habs; intro; subst.
eapply Plt_irrefl with curpath.
eapply Plt_trans.
eassumption.
eapply Plt_trans.
eapply Plt_succ.
assumption.
assumption.
rewrite PTree.gso.
rewrite PTree.gso.
assumption.
apply compile_var_other.
intro Habs.
injection Habs; intro; subst.
eapply Plt_irrefl with (Psucc (Psucc maxvar0)).
eapply Plt_trans.
eassumption.
eapply Plt_trans.
eapply Plt_succ.
eapply Plt_succ.
apply compile_var_other.
intro Habs.
injection Habs; intro; subst.
eapply Plt_irrefl with (Psucc maxvar0).
eapply Plt_trans.
eassumption.
eapply Plt_succ.
assumption.
reflexivity.
(** dynamic type *)
simpl.
intros.
destruct (
  prod_eq_dec 
   (prod_eq_dec peq (array_path_eq_dec (A := A)))
   Z_eq_dec
   (obj0, ar0, i0)    (obj, ar, i)
).
 injection e; intros; subst.
 generalize (dynamic_type_prop H29).
 intro; invall; subst.
 replace x1 with o in * by congruence.
 generalize (valid_array_path_last H31 H14).
 intro; subst.
 generalize (path_concat H34 H35 H36).
 intro.
 inversion H28; subst.
 destruct (Well_formed_hierarchy.path_is_base_dec hierarchy_wf H41 H32).
  (** base *)
  invall; subst.
  refine (_ (set_dynamic_type_BasesConstructed_after_same_path invariant_inheritance0  Hstep _ (refl_equal _) _ (refl_equal _) H42 H44 )).
  simpl.
  intro.
  generalize (dynamic_type_unique_strong hierarchy_wf (Preservation.goal hierarchy_wf invariant_inheritance0 Hstep) H29 x9).
  injection 1; intros; subst.
  eapply set_dynamic_type_same_path.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  assumption.
  eright with (hp := I).
  eassumption.
  eassumption.
  auto.
  (** not a base *)     
  refine (False_rect _ (set_dynamic_type_BasesConstructed_after_other_path hierarchy_wf invariant_inheritance0 Hstep _ (refl_equal _)  _ _ _ H29)).
  eright with (hp := I).
  eassumption.
  eassumption.
  auto.
  reflexivity.
  intros.
  eapply n.
  2 : eassumption.
  replace x7 with to.
  assumption.
  refine (_ (concat_last _ H43)).
  2 : eauto using path_nonempty.
  rewrite (path_last H32).
  rewrite (path_last H42).
  congruence.
(* other object *)
 erewrite set_dynamic_type_strong_other_cell.
 2 : eassumption.
 2 : unfold_ident_in_all; congruence.
 generalize (set_dynamic_type_other_before invariant_inheritance0 Hstep (refl_equal _) n H29).
 simpl; eauto.
(** allow static cast *)
intros until 1.
sdestruct (
pointer_eq_dec (A:=A) (obj0, (ar0, i0, (Class.Inheritance.Shared, b :: nil)))
           (obj, (ar, i, (h, p)))
).
 intro; discriminate.
intros.
destruct (prod_eq_dec (prod_eq_dec peq (@array_path_eq_dec _)) Z_eq_dec (obj, ar, i) (obj0, ar0, i0)).
 injection e; intros; subst.
 inversion H29; subst.
 replace o0 with o in * by congruence.
 inversion H37; subst.
 generalize (valid_array_path_last H31 H14).
 intro; subst.
 inversion H28; subst.
 destruct (Well_formed_hierarchy.path_is_base_dec hierarchy_wf H40 H35).
  destruct s0.
  destruct s0.
  destruct a.
  erewrite set_dynamic_type_same_path.
  2 : eassumption.
  3 : eassumption.
  2 : eassumption.
  3 : eassumption.
  congruence.
  eassumption.
(** not a primary base *)
erewrite set_dynamic_type_strong_other_not_primary_base. 
2 : eassumption.
2 : eassumption.
2 : eauto.
2 : assumption.
3 : eassumption.
eauto.
intros. (** a virtual base class is not a primary base ! *)
Transparent concat. simpl. Opaque concat.
rewrite (path_last H35).
destruct (peq to to); try congruence.
destruct p''.
 rewrite <- app_nil_end.
 unfold_ident_in_all.
 congruence.
destruct p.
 destruct (path_nonempty H35 (refl_equal _)).
 destruct p; simpl; congruence.
(** other cell *)
erewrite set_dynamic_type_strong_other_cell. 
2 : eassumption.
eauto.
assumption.
eauto using Preservation.goal.
Qed. (* slow *) 

 Lemma  preservation_destr_base_direct_non_virtual_nil_Kdestrother_base : forall obj ar i hp obj' ar' i' hp' beta b bases' stk gl cs auxcs f 
   (Hs1 :
     State.make
     (State.destr obj ar i hp Constructor.base
       Constructor.direct_non_virtual nil)
     (StackFrame.Kdestrother obj' ar' i' hp' Constructor.base beta b
       bases' :: stk) gl cs auxcs f = s1),
   goal.
Proof.
 Opaque Globals.get_field Globals.put_field concat Zminus.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  Focus 2.
   generalize (kind_inj H1).
   simpl; intro.
   destruct (State.destr_inj_base H0).
   discriminate.
injection H; intros; subst.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H0; intros; subst.
destruct (State.destr_inj_base H0).
subst.
simpl in *.
inversion H11; subst; try discriminate.
injection H9; intros; subst.
destruct (StackFrame.Kdestrother_base_inj H9).
invall; subst.
unfold compile_destr_all_virtual_bases.
Opaque compile_destr.
generalize (kind invariant_inheritance0).
unfold state_kind_inv; simpl; intro; invall; subst.
assert ((obj0, ar0, i0) = (obj, ar, i)).
 destruct k2; invall; congruence.
injection H8; intros; subst.
assert (forall cn, (h, p) <> (Class.Inheritance.Repeated, cn :: nil)).
 intros.
 destruct k2; invall; subst; try congruence.
 generalize (stack invariant_inheritance0 (or_introl _ (refl_equal _))).
 simpl; intro; invall; subst.
 destruct p0.
  discriminate.
 destruct p0; simpl; congruence.
sdestruct (path_eq_dec (h, p)
                   (Class.Inheritance.Repeated, class :: nil)
).
 destruct (H26 _ e).
esplit.
split.
eapply plus_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
split.
reflexivity.
reflexivity.
eapply star_left.
econstructor.
eleft.
reflexivity.
reflexivity.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
replace o0 with o in * by congruence.
destruct (list_inj (stack_inj H)).
generalize (StackFrame.Kdestrother_base_inj H28).
intro; invall; subst.
split; simpl; try assumption.
eapply state_invariant_destr with (k := Constructor.base); simpl.
reflexivity.
eassumption.
eassumption.
eassumption.
eassumption.
assumption.
eassumption.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
assumption.
(** dynamic type *)
simpl.
intros.
destruct (
  prod_eq_dec 
   (prod_eq_dec peq (array_path_eq_dec (A := A)))
   Z_eq_dec
    (obj, ar, i) (obj0, ar0, i0)
).
 symmetry in e; injection e; intros; subst.
 refine (_ (set_dynamic_type_StartedConstructing_after hierarchy_wf invariant_inheritance0 (h := h) (p := p) Hstep _ _ _ _ H30)); simpl.
 intro; contradiction.
 eassumption.
 sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (h, p)))
         (obj, (ar, i, (h, p)))
 ).
  reflexivity.
 destruct n0.
 trivial.
 auto.
 sdestruct ( 
pointer_eq_dec (A:=A)
         (obj, (ar, i, (h, p)))
         (obj, (ar, i, (h, p)))
 ).
  unfold_ident_in_all.
  rewrite H7.
  congruence.
 destruct n0; trivial.
 generalize (set_dynamic_type_other_before invariant_inheritance0 Hstep (refl_equal _) n0 H30).
 simpl; eauto.
(** allow static cast *)
intros until 1.
sdestruct (
pointer_eq_dec (A:=A)(obj, (ar, i, (h, p)))
           (obj0, (ar0, i0, (h1, p1)))
); eauto.
intro; discriminate.
eauto using Preservation.goal.
Qed. (* slow *)

Lemma preservation_destr_base_direct_non_virtual_nil_Kdestrcell : forall obj ar i hp obj' ar' i' cn' stk gl cs auxcs f
  (Hs1 : State.make
         (State.destr obj ar i hp Constructor.base
            Constructor.direct_non_virtual nil)
         (StackFrame.Kdestrcell obj' ar' i' cn' :: stk) gl cs auxcs f = s1),
         goal.
Proof.
 Opaque Globals.get_field Globals.put_field concat Zminus.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  Focus 2.
   generalize (kind_inj H1).
   simpl; intro.
   destruct (State.destr_inj_base H0).
   discriminate.
injection H1; intros; subst.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H2; intros; subst.
destruct (State.destr_inj_base H2).
subst.
simpl in *.
inversion H13; subst; try discriminate.
injection H11; intros; subst.
Transparent compile_destr.
unfold compile_destr.
unfold compile_destr_direct_non_virtual_bases.
simpl.
unfold compile_destr_all_virtual_bases.
generalize (kind invariant_inheritance0).
unfold state_kind_inv; simpl; intro; invall; subst; simpl in *.
inversion H4; subst.  
generalize (path_last H28).
injection 1; intro; subst.
sdestruct (
path_eq_dec (Class.Inheritance.Repeated, class :: nil)
                   (Class.Inheritance.Repeated, class :: nil)
); try congruence.
destruct (vborder_list_ex class).
 2 : congruence.
destruct s.
invall.
replace x4 with c in * by congruence.
generalize (vborder_list_func H0 H32).
intro; subst.
inversion H28; subst.
injection H30; intros; subst.
rewrite rev_involutive.
esplit.
split.
eapply plus_left.
econstructor.
eapply star_left.
econstructor.
eleft.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
split; simpl; try assumption.
eapply state_invariant_destr with (k := Constructor.base); simpl.
 reflexivity.
 eassumption.
 eassumption.
 7 : reflexivity.
  eassumption.
 eassumption.
 assumption.
 eassumption.
 reflexivity.
 reflexivity.
 simpl; reflexivity.
 assumption.
eauto using Preservation.goal.
Qed. (* slow *) 

Lemma preservation_destr_base_virtual_nil : forall obj ar i h p stk gl cs auxcs f
  (Hs1 :
  State.make
           (State.destr obj ar i (h, p) Constructor.base Constructor.virtual
              nil) stk gl cs auxcs f = s1),
goal.
Proof.
 Opaque Globals.get_field Globals.put_field concat Zminus.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  generalize (kind_inj H).
  simpl; intro.
  destruct (State.destr_inj_base H0).
  discriminate.
  generalize (kind_inj H1).
  simpl; intro.
  destruct (State.destr_inj_base H2).
  discriminate.
injection H1; intros; subst.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H0; intros; subst.
destruct (State.destr_inj_base H0).
subst.
simpl in *.
inversion H12; subst; try discriminate.
injection H10; intros; subst.
generalize (kind invariant_inheritance0).
unfold state_kind_inv; simpl; intro; invall; subst.
injection H; intros; subst.
inversion H3; subst.
generalize (path_last H28).
injection 1; intro; subst.
inversion H28; subst.
injection H30; intros; subst.
esplit.
split.
eapply plus_left.
econstructor.
split.
reflexivity.
reflexivity.
eapply star_left.
econstructor.
eleft.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
split; simpl; try assumption.
eapply state_invariant_destrarray; simpl.
reflexivity.
eassumption.
eassumption.
(* omega. *)
eassumption.
eassumption.
eassumption.
eassumption.
eassumption.
reflexivity.
reflexivity.
eassumption.
(** dynamic type *)
simpl.
intros.
destruct (
  prod_eq_dec 
   (prod_eq_dec peq (array_path_eq_dec (A := A)))
   Z_eq_dec
    (obj, ar, i) (obj0, ar0, i0)
).
 symmetry in e; injection e; intros; subst.
 refine (_ (set_dynamic_type_StartedConstructing_after hierarchy_wf invariant_inheritance0 (h := Class.Inheritance.Repeated) (p := cn0 :: nil) Hstep _ _ _ _ H33)); simpl.
 intro; contradiction.
 eassumption.
 sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn0 :: nil)))
         (obj, (ar, i, (Class.Inheritance.Repeated, cn0 :: nil)))
 ).
  reflexivity.
 destruct n.
 trivial.
 auto.
 sdestruct ( 
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn0 :: nil)))
         (obj, (ar, i, (Class.Inheritance.Repeated, cn0 :: nil)))
 ).
  unfold_ident_in_all.
  rewrite H8.
  congruence.
 destruct n; trivial.
 generalize (set_dynamic_type_other_before invariant_inheritance0 Hstep (refl_equal _) n H33).
 simpl; eauto.
(** allow static cast *)
intros until 1.
sdestruct (
pointer_eq_dec (A:=A)(obj, (ar, i, (Class.Inheritance.Repeated, cn0 :: nil)))
           (obj0, (ar0, i0, (h, p)))
); eauto.
intro; discriminate.
eauto using Preservation.goal.
Qed. (* slow *)  
 

Lemma preservation_Sconstructor_Kconstrarray : forall vars b tvargs stl obj ar n i cn init0 stk gl cs auxcs f
  (Hs1 : State.make (State.codepoint vars (Sconstructor b tvargs) stl nil)
    (StackFrame.Kconstrarray obj ar n i cn init0 :: stk) gl cs auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
  injection H9; intros; subst; simpl in *.
  inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H2; intros; subst; simpl in *.
destruct H4; try discriminate.
destruct H8; try discriminate.
subst; simpl in *; subst; simpl in *.
destruct global; simpl in *.
inversion H13; try discriminate.
subst.
injection H15; intros; subst; simpl in *.
destruct (invariant_heap0 obj0).
 edestruct (deallocated_objects_not_in_stack invariant_inheritance0).
  2 : eassumption.
  simpl.
 destruct (stack_objects_in_construction invariant_inheritance0 (l1 := nil) (refl_equal _) (refl_equal _)).
 rewrite H5.
 auto.
generalize (kind invariant_inheritance0).
unfold state_kind_inv; simpl.
intro; invall.
simpl.
generalize (prog'_constructors H H0). 
unfold compile_constructor.
destruct (
 vborder_list_ex cn
); try congruence.
destruct s.
invall.
replace x1 with c in * by congruence.
generalize (vborder_list_func H7 H34).
intro; subst.
intro.
inversion H3; subst; simpl in *.
esplit.
split.
 eapply plus_left.
 econstructor.
 eright.
refine (_ (step_call sem (args := _ :: _ :: _) _ _ _ _ _ _ _ _)).
 intro.
 eexact x2.
 simpl.
 f_equal.
 2 : symmetry; eassumption.
 2 : f_equal.
 3 : symmetry ; eassumption.
 3 : eapply vars_invariant_map.
 3 : eassumption.
 3 : eapply trans_equal.
 3 : eassumption.
intros; congruence. 
intros; congruence.
rewrite list_map_compose.
apply list_map_exten.
destruct x2; reflexivity.
simpl.
rewrite H18.
esplit.
split.
 reflexivity.
split; simpl; reflexivity.
simpl; reflexivity.
eright.
econstructor.
eright.
econstructor.
rewrite PTree.gss. reflexivity.
reflexivity.
eright. econstructor.
eleft.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
eapply state_invariant_constr with (k := Constructor.base); simpl.
reflexivity.
eassumption.
econstructor.
eassumption.
assumption.
assumption.
eleft with (lt := nil).
reflexivity.
reflexivity.
simpl.
rewrite H6.
trivial.
8 : simpl; reflexivity.
replace hp with hp''.
eapply vars_invariant_newvar.
eapply vars_invariant_oldvar.
eapply vars_invariant_newvar.
eapply vars_invariant_set_params.
apply true_uniq.
rewrite PTree.gss.
reflexivity.
apply Plt_succ.
simpl.
rewrite PTree.gso.
rewrite PTree.gso.
rewrite PTree.gss.
reflexivity.
apply compile_var_other; congruence.
apply compile_var_other; congruence.
2 : simpl; reflexivity.
compute. trivial.
reflexivity.
eapply stack_invariant_Kconstrothercells.
reflexivity.
eassumption.
eassumption.
eassumption.
eassumption.
eassumption.
eassumption.
eassumption.
simpl.
2 : eassumption.
 reflexivity.
(** dynamic type *)
simpl.
intros.
destruct (
  prod_eq_dec 
   (prod_eq_dec peq (array_path_eq_dec (A := A)))
   Z_eq_dec
    (obj0, ar0, i0) (obj, ar, i)
).
 injection e; intros; subst.
 refine (_ (set_dynamic_type_StartedConstructing_after hierarchy_wf invariant_inheritance0 (h := Class.Inheritance.Repeated) (p := cn :: nil) Hstep _ _ _ _ H36)); simpl.
 intro; contradiction.
 eright with (hp := I).
 eassumption.
 econstructor.
 eassumption.
 assumption.
 assumption.
 eleft with (lt := nil).
 reflexivity.
 reflexivity.
 simpl.
 rewrite H6.
 trivial.
 sdestruct (
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
 ).
  reflexivity.
 destruct n.
 trivial.
 auto.
 sdestruct ( 
pointer_eq_dec (A:=A)
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
         (obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)))
 ).
  assert (i <= i < n0) by omega.
  unfold_ident_in_all.
  rewrite (H27 _ H37).
  congruence.
 destruct n; trivial.
 generalize (set_dynamic_type_other_before invariant_inheritance0 Hstep (refl_equal _) n H36).
 simpl; eauto.
simpl.
intros ? ? ? ? ?.
sdestruct (
pointer_eq_dec (A:=A)
           (obj0, (ar0, i0, (Class.Inheritance.Repeated, cn :: nil)))
           (obj, (ar, i, (h, p)))
); eauto.
simpl; intros; discriminate.
eauto using Preservation.goal.
Qed. (* slow *)

Lemma preservation_constr_cons_base_virtual : forall obj ar i hp tinit init0 body vars b q stk gl cs auxcs f
  (Hs1 : State.make
    (State.constr obj ar i hp tinit init0 body vars Constructor.base
      Constructor.virtual (b :: q)) stk gl cs auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
Focus 2.
 generalize (kind_inj H2).
 simpl.
 intro.
 destruct (State.constr_inj_base H1).
 discriminate.
  injection H1; intros; subst.
clear H7 H8 H9.
destruct (State.constr_inj_base (kind_inj H1)).
injection H3; intros; subst; simpl in  *.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H0; intros; subst; subst.
destruct (State.constr_inj_base H0).
subst; simpl in *.
destruct (invariant_heap0 obj0).
 edestruct (deallocated_objects_not_in_stack invariant_inheritance0).
  2 : eassumption.
 destruct (kind_object_in_construction invariant_inheritance0 (refl_equal _)).
 rewrite H11.
 auto.
generalize (kind invariant_inheritance0).
unfold state_kind_inv; simpl.
intros; invall.
destruct stk; try contradiction.
destruct t; simpl in H19; try contradiction.
invall; subst.
injection H15; intros; subst.
destruct global.
unfold compile_base_initializer.
inversion H4; subst.
assert (x1 = class).
 generalize (path_last H23).
 simpl; congruence.
subst.
assert (X = class).
 inversion H23; congruence.
subst.
esplit.
split.
eapply plus_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
eapply step_pathop.
rewrite H8.
esplit.
split.
reflexivity.
reflexivity.
econstructor.
rewrite <- prog'_hierarchy.
eleft with (lt := nil).
reflexivity.
reflexivity.
simpl.
rewrite H16.
trivial.
reflexivity.
split.
reflexivity.
rewrite <- prog'_hierarchy.
eauto using vborder_list_virtual_base, in_or_app.
reflexivity.
eapply star_left.
econstructor.
eapply star_left.
eapply step_casttobase.
rewrite PTree.gso.
eassumption.
apply compile_var_other.
intro Habs.
injection Habs; intros; subst.
destruct (Plt_irrefl curpath).
eapply Plt_trans.
eassumption.
eapply Plt_trans.
eapply Plt_succ.
eapply Plt_trans.
eapply Plt_succ.
eassumption.
rewrite <- prog'_hierarchy.
replace hp0 with x0.
eapply valid_pointer_preserve.
eassumption.
assumption.
eauto using is_some_eq.
reflexivity.
split.
 rewrite <- prog'_hierarchy.
 eapply vborder_list_virtual_base.
 eassumption.
 eassumption.
 eauto using in_or_app.
split.
 reflexivity.
split.
 reflexivity.
split.
 reflexivity.
reflexivity.
reflexivity.
eapply star_left.
econstructor.
unfold compile'.
eapply star_left.
econstructor.
eleft.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
split; try assumption.
eapply state_invariant_codepoint with (p := nil); simpl.
reflexivity.
2 : tauto.
2 : auto.
2 : reflexivity.
2 : right; reflexivity.
3 : reflexivity.
econstructor.
split.
eapply Plt_succ.
eapply Plt_succ.
eapply vars_invariant_newvar.
eapply vars_invariant_newvar.
assumption.
reflexivity.
eapply stack_invariant_Kconstr with (k := Constructor.base); simpl.
reflexivity.
eassumption.
eassumption.
eapply vars_invariant_newvar.
eapply vars_invariant_newvar.
assumption.
rewrite PTree.gso.
rewrite PTree.gso.
eassumption.
apply compile_var_other.
intro Habs.
injection Habs; intros; subst.
destruct (Plt_irrefl curpath).
eapply Plt_trans.
eassumption.
eapply Plt_trans.
eapply Plt_succ.
eapply Plt_trans.
eapply Plt_succ.
eassumption.
apply compile_var_other.
intro Habs.
injection Habs; intros; subst.
destruct (Plt_irrefl curpath).
eapply Plt_trans.
eassumption.
eapply Plt_trans.
eapply Plt_succ.
eassumption.
eassumption.
rewrite PTree.gso.
rewrite PTree.gso.
assumption.
apply compile_var_other.
intro Habs.
injection Habs; intros; subst.
destruct (Plt_irrefl maxvar0).
eapply Plt_trans.
eapply Plt_succ.
eapply Plt_trans.
eapply Plt_succ.
assumption.
apply compile_var_other.
intro Habs.
injection Habs; intros; subst.
destruct (Plt_irrefl maxvar0).
eapply Plt_trans.
eapply Plt_succ.
eassumption.
eassumption.
reflexivity.
split; trivial.
split.
 apply Plt_succ.
split.
 apply Plt_succ.
split.
 apply Plt_succ.
simpl.
split.
rewrite PTree.gso.
rewrite PTree.gss.
reflexivity.
apply compile_var_other.
intro Habs.
injection Habs; intro Habs'.
generalize (Plt_succ (Psucc maxvar0)).
rewrite Habs'.
apply Plt_irrefl.
split; trivial.
exists I.
rewrite PTree.gss.
reflexivity.
assumption.
eauto using Preservation.goal.
Qed. (* slow *)


Lemma preservation_Sconstructor_Kconstr_base : forall vars b tvargs stl obj ar i h p tinit init0 body k2 q stk gl cs auxcs f
(Hs1 : State.make (State.codepoint vars (Sconstructor b tvargs) stl nil)
  (StackFrame.Kconstr obj ar i (h, p) tinit init0 body
    Constructor.base k2 b q :: stk) gl cs auxcs f = s1),
goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
injection H10; intros; subst.
destruct (list_inj (stack_inj H10)).
generalize (StackFrame.Kconstr_base_inj H2).
intro; invall; subst.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H5; intros; subst; subst.
inversion H15; subst; try discriminate.
injection H19; intros; subst.
generalize (StackFrame.Kconstr_base_inj H19).
intro; invall; subst; simpl in *; invall; subst.
inversion H6; subst.
esplit.
split.
eapply plus_left.
econstructor.
eapply star_left.
eapply step_call with (args := _ :: _ :: _).
simpl.
f_equal.
2 : symmetry; eassumption.
2 : f_equal.
3 : symmetry; eassumption.
3 : eapply vars_invariant_map.
3 : eassumption.
3 : eapply trans_equal.
3 : eassumption.
3 : rewrite list_map_compose.
3 : eapply list_map_exten.
3 : destruct x0; intros; reflexivity.
intros; congruence.
intros; congruence.
2 : simpl; reflexivity.
rewrite (prog'_constructors H0 H1).
eauto.
simpl.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
rewrite PTree.gss.
reflexivity.
reflexivity.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eapply star_left.
econstructor.
eleft.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
inversion H21; subst.
generalize (kind (Preservation.goal hierarchy_wf invariant_inheritance0 Hstep)).
unfold state_kind_inv; simpl; intro; invall; subst.
inversion H34; subst.
replace o0 with o in * by congruence.
assert (x2 = b0).
 destruct k0; simpl in *; try congruence.
 rewrite last_complete in *; congruence.
subst. 
replace x3 with c in * by congruence.
assert (to = b0).
 inversion H48; subst.
 generalize (path_last H46); congruence.
subst.
unfold_ident_in_all.
assert (through = X).
 inversion H48; subst; eauto using valid_array_path_last.
subst. 
destruct H7; try discriminate.
subst; simpl in *.
unfold_ident_in_all.
split; try assumption.
eapply state_invariant_constr with (k := Constructor.base); simpl.
reflexivity.
eassumption.
eassumption.
6 : simpl.
6 : unfold compile_constr_non_virtual_part.
6 : rewrite H36.
6 : sdestruct ( path_eq_dec
    (match k0 with
       | Constructor.direct_non_virtual => h0
       | Constructor.virtual => Class.Inheritance.Shared
     end,
    match k0 with
      | Constructor.direct_non_virtual => p1 ++ b0 :: nil
      | Constructor.virtual => b0 :: nil
    end) (Class.Inheritance.Repeated, b0 :: nil)
); try reflexivity.
7 : simpl; reflexivity.
7 : simpl; reflexivity.
eapply vars_invariant_newvar.
replace x with hp' by eauto using is_some_eq.
eapply vars_invariant_oldvar.
eapply vars_invariant_newvar.
eapply vars_invariant_set_params.
rewrite PTree.gss.
reflexivity.
compute; congruence.
rewrite PTree.gso.
rewrite PTree.gso.
rewrite PTree.gss.
reflexivity.
apply compile_var_other; congruence.
apply compile_var_other; congruence.
compute; congruence.
destruct k0; try discriminate.
destruct p1; try contradiction.
destruct p1; discriminate.
simpl.
eapply stack_invariant_Kconstrother with (k := Constructor.base).
reflexivity.
eassumption.
eassumption.
6 : exists further; reflexivity.
6 : simpl; reflexivity.
6 : reflexivity.
6 : reflexivity.
assumption.
eassumption.
assumption.
assumption.
assumption.
assumption.
(** dynamic type *)
simpl.
intros.
apply invariant_dynamic_type0.
destruct (
  prod_eq_dec 
   (prod_eq_dec peq (array_path_eq_dec (A := A)))
   Z_eq_dec
    (obj0, ar0, i0) (obj, ar, i)
).
 injection e; intros; subst.
 refine (_ (set_dynamic_type_StartedConstructing_after hierarchy_wf invariant_inheritance0 (h := 
   match k0 with
     | Constructor.direct_non_virtual => h0
     | Constructor.virtual => Class.Inheritance.Shared
   end
 ) (p :=
   match k0 with
     | Constructor.direct_non_virtual => p1 ++ b0 :: nil
     | Constructor.virtual => b0 :: nil
   end   
 ) (hp := x) Hstep _ _ _ _ _)); simpl.
 intro; contradiction.
 eright.
 eassumption.
 eassumption.
 sdestruct (
pointer_eq_dec (A:=A)
         (obj,
         (ar, i,
         (match k0 with
          | Constructor.direct_non_virtual => h0
          | Constructor.virtual => Class.Inheritance.Shared
          end,
         match k0 with
         | Constructor.direct_non_virtual => p1 ++ b0 :: nil
         | Constructor.virtual => b0 :: nil
         end)))
         (obj,
         (ar, i,
         (match k0 with
          | Constructor.direct_non_virtual => h0
          | Constructor.virtual => Class.Inheritance.Shared
          end,
         match k0 with
         | Constructor.direct_non_virtual => p1 ++ b0 :: nil
         | Constructor.virtual => b0 :: nil
         end)))
 ).
  reflexivity.
 destruct n.
 trivial.
 auto.
 sdestruct ( 
pointer_eq_dec (A:=A)
         (obj,
         (ar, i,
         (match k0 with
          | Constructor.direct_non_virtual => h0
          | Constructor.virtual => Class.Inheritance.Shared
          end,
         match k0 with
         | Constructor.direct_non_virtual => p1 ++ b0 :: nil
         | Constructor.virtual => b0 :: nil
         end)))
         (obj,
         (ar, i,
         (match k0 with
          | Constructor.direct_non_virtual => h0
          | Constructor.virtual => Class.Inheritance.Shared
          end,
         match k0 with
         | Constructor.direct_non_virtual => p1 ++ b0 :: nil
         | Constructor.virtual => b0 :: nil
         end)))
 ).
  generalize (kind invariant_inheritance0).
  unfold state_kind_inv; simpl.
  intro; invall; subst.
  destruct k0; invall; subst.
   unfold_ident_in_all.
   rewrite (H50 _ (or_introl _ (refl_equal _))).
   congruence.
  unfold_ident_in_all.
  rewrite (H52 _ (or_introl _ (refl_equal _))).
  congruence.
  destruct n.
  trivial.
  eassumption.
  exact (set_dynamic_type_other_before invariant_inheritance0 Hstep (refl_equal _) n H7).
 simpl.
 intros until 1.
 sdestruct (
 pointer_eq_dec (A:=A)
           (obj0,
           (ar0, i0,
           (match k0 with
            | Constructor.direct_non_virtual => h0
            | Constructor.virtual => Class.Inheritance.Shared
            end,
           match k0 with
           | Constructor.direct_non_virtual => p1 ++ b0 :: nil
           | Constructor.virtual => b0 :: nil
           end))) (obj, (ar, i, (h, p)))
 ); eauto.
 intros; discriminate.
eauto using Preservation.goal.
Qed. (* slow *)

  

Lemma preservation_constr_base_virtual_nil : forall obj ar i h p tinit init0 body vars stk gl cs auxcs f
  (Hs1 :
    State.make
    (State.constr obj ar i (h, p) tinit init0 body vars Constructor.base
      Constructor.virtual nil) stk gl cs auxcs f = s1),
  goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  intros; inversion Hstep; subst; simpl in *; subst; try abs discriminate.
Focus 2.
 generalize (kind_inj H2).
 simpl.
 intro.
 destruct (State.constr_inj_base H1).
 discriminate.
  injection H2; intros; subst.
inversion Hinv; inversion invariant_state0; destruct s1'; subst; simpl in *; subst; try discriminate.
injection H1; intros; subst; subst.
destruct (State.constr_inj_base H1).
subst; simpl in *.
destruct (invariant_heap0 obj0).
 edestruct (deallocated_objects_not_in_stack invariant_inheritance0).
  2 : eassumption.
 destruct (kind_object_in_construction invariant_inheritance0 (refl_equal _)).
 rewrite H11.
 auto.
generalize (kind invariant_inheritance0).
unfold state_kind_inv; simpl; intros; invall; subst.
destruct global; simpl in *.
unfold compile_base_initializer.
inversion H4; subst.
assert (x1 = class).
 generalize (path_last H24).
 unfold_ident_in_all; congruence.
subst.
esplit.
split.
eapply plus_left.
econstructor.
unfold compile_constr_non_virtual_part.
rewrite H16.
eright.
econstructor.
eleft.
reflexivity.
repeat rewrite E0_left; eauto using evtr_sem.
unfold_ident_in_all.
replace cn with class in * by congruence.
replace x2 with c in * by congruence.
split; try assumption.
destruct stk; try contradiction.
destruct t; try contradiction.
simpl in H19.
invall; subst; simpl in *.
injection H; intro; subst.
eapply state_invariant_constr with (k := Constructor.base).
reflexivity.
eassumption.
eassumption.
7 : simpl; reflexivity.
7 : simpl; reflexivity.
assumption.
eassumption.
eassumption.
assumption.
eassumption.
simpl.
sdestruct (
path_eq_dec (Class.Inheritance.Repeated, class :: nil)
           (Class.Inheritance.Repeated, class :: nil)
); congruence.
assumption.
eauto using Preservation.goal.
Qed. (* slow *)

(** To put it in a nutshell *)

Theorem preservation : goal.
Proof.
  Opaque Globals.get_field Globals.put_field concat.
  simple inversion Hstep.
  solve [eapply preservation_skip_cons; eauto].
  solve [intros; eapply preservation_if; eauto].
  solve [eapply preservation_loop; eauto].
  solve [eapply preservation_seq; eauto].
  solve [eapply preservation_exit_S_none; eauto].
  solve [eapply preservation_exit_O; eauto].
  solve [eapply preservation_skip_nil; eauto].
  solve [intros; eapply preservation_requires_exit_none; eauto].
  solve [eapply preservation_block_none; eauto].
  solve [intros; eapply preservation_return_nil; eauto].
  solve [intros; eapply preservation_native; eauto].
  solve [intros; eapply preservation_move; eauto].
  solve [intros; eapply preservation_getfield; eauto].
  solve [intros; eapply preservation_putfield; eauto].
  solve [intros; eapply preservation_index; eauto].
  solve [intros; eapply preservation_ptreq; eauto].
  solve [intros; eapply preservation_call; eauto].
  solve [intros; eapply preservation_invoke; eauto].
  solve [intros; eapply preservation_dyncast; eauto].
  solve [intros; eapply preservation_statcast; eauto].
  solve [intros; eapply preservation_block_some; eauto].
  solve [intros; eapply preservation_constr_array_nil_Kcontinue; eauto].
  solve [intros; eapply preservation_constr_array_cons; eauto].
  solve [intros; eapply preservation_Sconstructor_Kconstrarray; eauto].
  solve [intros; eapply preservation_Sreturn_Kconstrothercells; eauto].
  destruct k.
   destruct k2.
   solve [intros; eapply preservation_constr_cons_base_direct_non_virtual; eauto].
   solve [intros; eapply preservation_constr_cons_base_virtual; eauto].
  solve [  destruct k2; intros; eapply preservation_constr_cons_field_scalar_some; eauto].
  solve [intros; eapply preservation_constr_cons_field_struct; eauto].
  solve [intros; eapply preservation_Sconstructor_Kconstr_base; eauto].
  solve [intros; eapply preservation_Sreturn_Kconstrother_base; eauto].
  solve [intros; eapply preservation_constr_base_virtual_nil; eauto].
  solve [intros; eapply preservation_constr_base_direct_non_virtual_nil; eauto].
  solve [intros; eapply preservation_constr_cons_field_scalar_none; eauto].
  solve [intros; eapply preservation_Sinitscalar; eauto].
  solve [intros; eapply preservation_constr_array_nil_Kconstrother_field; eauto].
  solve [intros; eapply preservation_constr_fields_nil; eauto].
  solve [intros; eapply preservation_destr_array_cons; eauto].
  solve [intros; eapply preservation_Sreturn_Kdestr; eauto].
  solve [intros; eapply preservation_destr_field_cons_scalar; eauto].
  solve [intros; eapply preservation_destr_field_cons_struct; eauto].
  solve [intros; eapply preservation_destr_array_nil_Kdestrother_field; eauto].
  solve [intros; eapply preservation_destr_field_nil; eauto].
   destruct beta.
    solve [intros; eapply preservation_destr_base_cons_direct_non_virtual; eauto].
    solve [intros; eapply preservation_destr_base_cons_virtual; eauto].
  solve [intros; eapply preservation_destr_base_direct_non_virtual_nil_Kdestrother_base; eauto].
  solve [intros; eapply preservation_destr_base_direct_non_virtual_nil_Kdestrcell; eauto].
  solve [intros; eapply preservation_destr_base_virtual_nil; eauto].
  solve [intros; eapply preservation_requires_destruct; eauto].
  solve [intros; eapply preservation_destr_array_nil_Kcontinue; eauto].
Qed.


End Compiler.
