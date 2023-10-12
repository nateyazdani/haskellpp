Require Export BuiltinTypes.
Require Import LibLists.
Require Import Cplusconcepts.
Require Import Maps.
Require Import Coqlib.
Require Import Events.
Require Import Eqdep_dec.
Require Import Dynamic. (* because of is_dynamic, for dynamic cast *)

Load Param.

Definition var    := positive.

(** * Syntax *)
Section Stmt.
  Variable A : ATOM.t.
  Variable nativeop : Type. (** Operators on atomic values : constants, arithmetics, external calls, etc. *)

Inductive callkind : Type :=
| Static (fid : ident)
| NonVirtual (cn : ident) (ms : MethodSignature.t A)
.

Inductive stmt : Type :=
(** Control structures *)
| Sskip
| Sif (test : var) (iftrue iffalse : stmt) 
| Sloop (body : stmt)
| Sblock
  (localstruct : option (var * ident * Z))  
  (initializers : Z -> stmt)
  (body : stmt) (* block, may contain a structure array variable to be constructed using the given initializers. *)
| Sexit (n : nat) (* exitting from (S n) blocks, automatically destructing local structures if any *)
| Sseq (_ _ : stmt)
| Scall (ckind : callkind) (args : list var) (retval : option var) (* call to static function *)
| Sreturn (value : option var)  (* Return from function *)
| Sconstructor (class : ident) (args : list (Typ.t A * var)) (* Hand over to a constructor *)
| Sinitscalar (value : var) (* End of initializer, "construct" scalar field to specified value *)

(** Basic operations *)
| Snative (op : nativeop) (args : list var) (retval : option var) (* Native operations on atoms (constants, arithmetics, system calls, etc.) *)
| Smove (src : var) (tgt : var) (* scalar move *)

(** Field and array access *)
| Sgetfield (object : var) (class : ident) (field : FieldSignature.t A) (target : var) (* may be a structure field, in this case returns a pointer to the first structure *)
| Sputfield (object : var) (class : ident) (field : FieldSignature.t A) (value : var) (* must be scalar *)
| Sindex (object : var) (class : ident) (index : var) (target : var) (* array index *)

(** Object-oriented features *)
| Sinvoke (object : var) (class : ident) (method : MethodSignature.t A) (args : list var) (retval : option var) (* Invoke method (virtual or not) *)
| Sdyncast (object : var) (cfrom cto : ident) (res : var)
| Sstatcast (object : var) (cfrom cto : ident) (res : var)
(* | Sbasecast (object : var) (cfrom cto : ident) *)
| Sptreq (v1 v2 : var) (vres : var) (* pointer comparison *)

(*
(** Free store object construction and destruction *)
| Snew (object : var) (class : ident) (nbcells : var) (* free store combined allocation+construction *)
| Sdeleteobject (object : var) (class : ident) (* free store combined destruction+deallocation for an object through one of its bases having a virtual destructor *)
| Sdeletearray (array : var) (class : ident) (* free store combined destruction+deallocation for an array *)
*)
.

(*
with list_Z_stmt : Type :=
| list_Z_stmt_nil 
| list_Z_stmt_cons (_ : Z) (_ : stmt) (_ : list_Z_stmt)
.

Fixpoint list_of_list_Z_stmt (l : list_Z_stmt ) {struct l} : list (Z * stmt) :=
  match l with
    | list_Z_stmt_nil => nil
    | list_Z_stmt_cons z s l' => (z, s) :: list_of_list_Z_stmt l'
  end.

Fixpoint list_Z_stmt_of_list (l : list (Z * stmt)) {struct l} : list_Z_stmt  :=
  match l with
    | nil => list_Z_stmt_nil 
    | (z, s) :: l' => list_Z_stmt_cons z s (list_Z_stmt_of_list l' )
  end.

Lemma list_of_list_Z_stmt_of_list : forall l,
  list_of_list_Z_stmt (list_Z_stmt_of_list l) = l.
Proof.
  induction l; simpl; eauto.
  intros; destruct a; simpl; f_equal; eauto.
Qed.

Lemma list_Z_stmt_of_list_of_list_Z_stmt : forall l,
  list_Z_stmt_of_list (list_of_list_Z_stmt l) = l.
Proof.
 induction l; simpl; eauto.
 f_equal; eauto.
Qed.

Scheme stmt_rect2 := Induction for stmt Sort Type
with list_Z_stmt_rect2 := Induction for list_Z_stmt Sort Type.

Definition stmt_rect3 P := stmt_rect2 (P := P) (P0 := fun l => forall z s, In (z, s) (list_of_list_Z_stmt l) -> P s).
*)


End Stmt. 

Implicit Arguments Sskip [A nativeop].
Implicit Arguments Sexit [A nativeop].
Implicit Arguments Sreturn [A nativeop].
Implicit Arguments Sconstructor [A nativeop].
Implicit Arguments Sinitscalar [A nativeop].
Implicit Arguments Snative [A nativeop].
Implicit Arguments Smove [A nativeop].
Implicit Arguments Sgetfield [A nativeop].
Implicit Arguments Sputfield [A nativeop].
Implicit Arguments Sindex [A nativeop].
Implicit Arguments Sinvoke [A nativeop].
Implicit Arguments Sdyncast [A nativeop].
Implicit Arguments Sstatcast [A nativeop].
(* Implicit Arguments Sbasecast [A nativeop]. *)
Implicit Arguments Sptreq [A nativeop].
(*
Implicit Arguments Snew [A nativeop].
Implicit Arguments Sdeleteobject [A nativeop].
Implicit Arguments Sdeletearray [A nativeop].
*)

Module Method_body.
  Section MB.
  Variable A : ATOM.t.
  Variable nativeop : Type.
  Record t : Type := make {
    this : var;
    args : list var;
    code : stmt A nativeop
  }.
End MB.
End Method_body.

Module Static_method.
  Section SM.
  Variable A : ATOM.t.
  Variable nativeop : Type.    
  Record t : Type := make {
    args   : list var (* * Typ.t A *);
(*    retval : option (Typ.t A); *)
    code   : stmt A nativeop
  }.
End SM.
End Static_method. 

Module Constructor.
Section P.
 Variable A : ATOM.t.
 Variable nativeop : Type.

 Inductive init_key_primary : Type :=
 | base
 | field
   .

 Lemma init_key_primary_eq_dec : forall a b : init_key_primary, {a = b} + {a <> b}.
 Proof.
   decide equality.
 Qed.

 Inductive init_key_secondary_base : Type :=
 | direct_non_virtual
 | virtual
   .

 Function init_key_secondary (k : init_key_primary) : Type :=
   match k with
     | base => init_key_secondary_base
     | field => unit
   end.

 Lemma init_key_secondary_eq_dec : forall k (a b : init_key_secondary k),
   {a = b} + {a <> b}.
 Proof.
   destruct k; simpl; decide equality.
 Qed.
 
 Function init_key_item (k : init_key_primary) : Type :=
   match k with
     | base => ident
     | field => FieldSignature.t A
   end.

 Lemma init_key_item_eq_dec : forall k (a b : init_key_item k),
   {a = b} + {a <> b}.
 Proof.
   destruct k; simpl.
    exact peq.
   apply FieldSignature.eq_dec.
 Qed.

 Definition init_subkey k := (init_key_secondary k * init_key_item k)%type. 

 Lemma init_subkey_eq_dec : forall k (a b : init_subkey k),
   {a = b} + {a <> b}.
 Proof.
   unfold init_subkey.
   intros; eauto using prod_eq_dec, init_key_secondary_eq_dec, init_key_item_eq_dec.
 Qed.

 Definition initializer_key := sigT init_subkey.

 Lemma initializer_key_eq_dec : forall k1 k2 : initializer_key,
   {k1 = k2} + {k1 <> k2}.
 Proof.
   destruct k1.
   destruct k2.
   destruct (init_key_primary_eq_dec x x0).
    subst.
    destruct (init_subkey_eq_dec i i0).
     left; congruence.
    right; intro.
    destruct n.
    eapply inj_pair2_eq_dec.
     exact init_key_primary_eq_dec.
    assumption.
   right; congruence.
 Qed.

 Record t : Type := make {
   this : var;
   args : list var;
   initializers : list (initializer_key * stmt A nativeop);
   struct_field_initializers : list (FieldSignature.t A * (Z -> stmt A nativeop) (* list (Z * stmt A nativeop) *) );
   body : stmt A nativeop
 }.

End P.
End Constructor.

Module Program.
  Section P.
  Variable A : ATOM.t.
  Variable nativeop : Type.    

Record t : Type := make {
  hierarchy : PTree.t (Class.t A) ;
  methods : PTree.t (Method_body.t A nativeop) ;
  static_methods : PTree.t (Static_method.t A nativeop);
  constructors : PTree.t (list (list (Typ.t A) * (Constructor.t A nativeop)));
  destructor_id : ident;
  main : stmt A nativeop
}.

Lemma constructor_key_eq_dec : forall k1 k2 : list (Typ.t A),
  {k1 = k2} + {k1 <> k2}.
Proof.
  eauto using list_eq_dec, Typ.eq_dec.
Qed.

Definition destructor_sig (p : t) := MethodSignature.make (A := A) (destructor_id p) nil None.

End P.
End Program.


(** Semantics *)

(** A block code point *)

Module BlockPoint.
Section CP.
  Variable A : ATOM.t.
  Variable nativeop : Type.
  Record t : Type := make {
    next_on_exit : list (stmt A nativeop); (* further instructions AFTER block end *)
    localstruct :  option ident (* object heap identifier to destruct  *)
  }.
End CP.
End BlockPoint.

Module StackFrame.
Section SF.

  Variable A : ATOM.t.

Inductive continue_kind : Type :=
| continue_constr
| continue_destr (_ : PTree.t (Value.t A)).


  Variable nativeop : Type.
  Inductive t : Type :=
  | Kreturnfromcall (res : option ident) (vars : PTree.t (Value.t A)) (further : list (stmt A nativeop)) (blocks : list (BlockPoint.t A nativeop))
  | Kcontinue (_ : continue_kind) (further : stmt A nativeop) (curobj : ident) (blockinstr : (* option *) (list (stmt A nativeop))) (blocks : list (BlockPoint.t A nativeop)) (* for instance after construction *)

  (** Object construction *)

  | Kconstr (obj : ident) (array : array_path A) (array_index : Z) (inhpath : Class.Inheritance.t * list ident) (tinit : list (FieldSignature.t A * (Z -> stmt A nativeop) (* list (Z * stmt A nativeop) *) )) (initializers : list (Constructor.initializer_key A * stmt A nativeop)) (body : stmt A nativeop)  (k : Constructor.init_key_primary) (kind : Constructor.init_key_secondary k) (current : Constructor.init_key_item A k) (others : list (Constructor.init_key_item A k)) (* construction should resume after initialization *)

  | Kconstrarray (obj : ident) (array : array_path A) (array_count : Z) (array_index : Z) (cn : ident) (init : Z -> stmt A nativeop (* list (Z * stmt A nativeop) *) ) (* array construction should resume after cell initialization *)

  | Kconstrother (obj : ident) (array : array_path A) (array_index : Z) (inhpath : Class.Inheritance.t * list ident) (tinit : list (FieldSignature.t A * (Z -> stmt A nativeop) (* list (Z * stmt A nativeop) *) )) (initializers : list (Constructor.initializer_key A * stmt A nativeop)) (body : stmt A nativeop) (vars : PTree.t (Value.t A)) (k : Constructor.init_key_primary) (kind : Constructor.init_key_secondary k) (current : Constructor.init_key_item A k) (others : list (Constructor.init_key_item A k)) (* construction of others should resume after construction of current *)

  (** Array construction *)
  | Kconstrothercells (obj : ident) (array : array_path A) (array_size current_index : Z) (class : ident) (initializers : Z -> stmt A nativeop (* list (Z * stmt A nativeop) *)) (vars : PTree.t (Value.t A))

  (** Destruction. Simpler, as there are no equivalent to initializers *)
  | Kdestr (obj : ident) (array : array_path A) (array_index : Z) (inhpath : Class.Inheritance.t * list ident) (* destruction should resume after running destructor body *)
  | Kdestrother (obj : ident) (array : array_path A) (array_index : Z) (inhpath : Class.Inheritance.t * list ident) (k : Constructor.init_key_primary) (kind : Constructor.init_key_secondary k) (current : Constructor.init_key_item A k) (others : list (Constructor.init_key_item A k)) (* destruction of others should resume after destruction of current *)
  | Kdestrcell (obj : ident) (array : array_path A) (current_index : Z) (class : ident) (* destruction of virtual bases should occur after destructing non-virtual part of cell *)
    .


Remark Kconstrother_inj : forall obj ar i cn tinit init body vars  k k2 b q obj' ar' i' cn' tinit' init' body' vars' k' k2' b' q',
  Kconstrother obj ar i cn tinit init body vars (k := k) k2 b q = Kconstrother obj' ar' i' cn'  tinit' init' body' vars' (k := k') k2' b' q' ->
  k = k' /\ existT (fun t => (Constructor.init_key_secondary t * Constructor.init_key_item _ t * list (Constructor.init_key_item _ t))%type) k (k2, b, q) = existT (fun t => (Constructor.init_key_secondary t * Constructor.init_key_item _ t * list (Constructor.init_key_item _ t))%type) k' (k2', b', q').
Proof.
  injection 1; intros; subst.
  split; auto.
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H0)).
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H1)).
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H2)).
  congruence.
Qed.

Corollary Kconstrother_base_inj : forall obj ar i cn tinit init body vars k2 b q obj' ar' i' cn' tinit' init' body' vars' k2' b' q',
  Kconstrother obj ar i cn tinit init body vars (k := Constructor.base) k2 b q = Kconstrother obj' ar' i' cn' tinit' init' body' vars' (k := Constructor.base) k2' b' q' ->
  k2 = k2' /\ b = b' /\ q = q'.
Proof.
  intros.
  destruct (Kconstrother_inj H).
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H1)).
  injection 1.
  tauto.
Qed.

Corollary Kconstrother_field_inj : forall obj ar i cn tinit init body vars b q obj' ar' i' cn' tinit' init' body' vars' b' q',
  Kconstrother obj ar i cn tinit init body vars (k := Constructor.field) tt b q = Kconstrother obj' ar' i' cn' tinit' init' body' vars' (k := Constructor.field) tt b' q' ->
  b = b' /\ q = q'.
Proof.
  intros.
  destruct (Kconstrother_inj H).
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H1)).
  injection 1.
  tauto.
Qed.


Remark Kconstr_inj : forall obj ar i cn tinit init body  k k2 b q obj' ar' i' cn' tinit' init' body' k' k2' b' q',
  Kconstr obj ar i cn tinit init body (k := k) k2 b q = Kconstr obj' ar' i' cn'  tinit' init' body' (k := k') k2' b' q' ->
  k = k' /\ existT (fun t => (Constructor.init_key_secondary t * Constructor.init_key_item _ t * list (Constructor.init_key_item _ t))%type) k (k2, b, q) = existT (fun t => (Constructor.init_key_secondary t * Constructor.init_key_item _ t * list (Constructor.init_key_item _ t))%type) k' (k2', b', q').
Proof.
  injection 1; intros; subst.
  split; auto.
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H0)).
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H1)).
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H2)).
  congruence.
Qed.

Corollary Kconstr_base_inj : forall obj ar i cn tinit init body k2 b q obj' ar' i' cn' tinit' init' body' k2' b' q',
  Kconstr obj ar i cn tinit init body (k := Constructor.base) k2 b q = Kconstr obj' ar' i' cn' tinit' init' body' (k := Constructor.base) k2' b' q' ->
  k2 = k2' /\ b = b' /\ q = q'.
Proof.
  intros.
  destruct (Kconstr_inj H).
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H1)).
  injection 1.
  tauto.
Qed.

Corollary Kconstr_field_inj : forall obj ar i cn tinit init body b q obj' ar' i' cn' tinit' init' body' b' q',
  Kconstr obj ar i cn tinit init body (k := Constructor.field) tt b q = Kconstr obj' ar' i' cn' tinit' init' body' (k := Constructor.field) tt b' q' ->
  b = b' /\ q = q'.
Proof.
  intros.
  destruct (Kconstr_inj H).
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H1)).
  injection 1.
  tauto.
Qed.


Remark Kdestrother_inj : forall obj ar i cn  k k2 b q obj' ar' i' cn'  k' k2' b' q',
  Kdestrother obj ar i cn (k := k) k2 b q = Kdestrother obj' ar' i' cn' (k := k') k2' b' q' ->
  k = k' /\ existT (fun t => (Constructor.init_key_secondary t * Constructor.init_key_item _ t * list (Constructor.init_key_item _ t))%type) k (k2, b, q) = existT (fun t => (Constructor.init_key_secondary t * Constructor.init_key_item _ t * list (Constructor.init_key_item _ t))%type) k' (k2', b', q').
Proof.
  injection 1; intros; subst.
  split; auto.
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H0)).
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H1)).
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H2)).
  congruence.
Qed.

Corollary Kdestrother_base_inj : forall obj ar i cn k2 b q obj' ar' i' cn' k2' b' q',
  Kdestrother obj ar i cn (k := Constructor.base) k2 b q = Kdestrother obj' ar' i' cn' (k := Constructor.base) k2' b' q' ->
  k2 = k2' /\ b = b' /\ q = q'.
Proof.
  intros.
  destruct (Kdestrother_inj H).
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H1)).
  injection 1.
  tauto.
Qed.

Corollary Kdestrother_field_inj : forall obj ar i cn  b q obj' ar' i' cn'  b' q',
  Kdestrother obj ar i cn  (k := Constructor.field) tt b q = Kdestrother obj' ar' i' cn' (k := Constructor.field) tt b' q' ->
  b = b' /\ q = q'.
Proof.
  intros.
  destruct (Kdestrother_inj H).
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H1)).
  injection 1.
  tauto.
Qed.

End SF.
Implicit Arguments Kconstr [A nativeop].
Implicit Arguments Kconstrarray [A nativeop].
Implicit Arguments Kconstrother [A nativeop].
Implicit Arguments Kdestr [A nativeop].
Implicit Arguments Kdestrother [A nativeop].
Implicit Arguments Kdestrcell [A nativeop].


End StackFrame.


Inductive construction_state : Set :=
| StartedConstructing
| BasesConstructed
| Constructed
| StartedDestructing
| DestructingBases
| Destructed.

Function Z_of_construction_state (o : option construction_state) : Z :=
  match o with
    | None => 0
    | Some b =>
      match b with
        | StartedConstructing => 1
        | BasesConstructed => 2
        | Constructed => 3
        | StartedDestructing => 4
        | DestructingBases => 5
        | Destructed => 6
      end
  end.

Lemma Z_of_construction_state_inj : forall a b,
  Z_of_construction_state a = Z_of_construction_state b ->
  a = b.
Proof.
  intros a b;
  functional induction (Z_of_construction_state a);
  functional induction (Z_of_construction_state b);
    congruence.
Qed.


Notation "( a '<<' b )" := (Z_of_construction_state a < Z_of_construction_state b).

Lemma cs_lt_irrefl : forall a, (a << a) -> False.
Proof.
  intro; omega.
Qed.  

Lemma cs_lt_trans : forall a b, (a << b) -> forall c, (b << c) -> (a << c).
Proof.
  intros; omega.
Qed.


Notation "( a '=<' b )" := (Z_of_construction_state a <= Z_of_construction_state b).

Lemma cs_le_refl : forall a, (a =< a).
Proof.
  intro; omega.
Qed.

Lemma cs_le_trans : forall a b, (a =< b) -> forall c, (b =< c) -> (a =< c).
Proof.
  intros; omega.
Qed.

Lemma cs_le_antisym : forall a b, (a =< b) -> (b =< a) -> a = b.
Proof.
  intros; eapply Z_of_construction_state_inj; omega.
Qed.

Notation aux_constr_state_t := (fun A : ATOM.t => list (ident * array_path A * Z * (Class.Inheritance.t * list ident) * FieldSignature.t A * construction_state)).

Lemma aux_constr_state_key_eq_dec : forall (A : ATOM.t) (a b : ident * array_path A * Z * (Class.Inheritance.t * list ident) * FieldSignature.t A), {a = b} + {a <> b}.
Proof.
  intro.
  apply prod_eq_dec.
   apply prod_eq_dec.
    apply prod_eq_dec.
     apply prod_eq_dec.
      exact peq.
     apply array_path_eq_dec.
    exact Z_eq_dec.
   exact path_eq_dec.
  apply FieldSignature.eq_dec.
Qed.



Section DynamicType.

  Variable A : ATOM.t.

  Variable hierarchy : PTree.t (Class.t A).

  Variable heap : PTree.t Object.t.

  Variable construction_states : list ((ident * (array_path A * Z * (Class.Inheritance.t * list ident))) * construction_state).

  Variable obj : positive.

  Variable ar : array_path A.

  Variable i : Z.

  Variable h: Class.Inheritance.t.
  
  Variable p: list ident.


  Inductive dynamic_type : Class.Inheritance.t -> list ident -> Class.Inheritance.t -> list ident -> Prop := 
  | dynamic_type_most_derived_constructed
    (o : _)
    (_ : (heap) ! obj = Some o)
    (ato : _) (zto  : _)
    (_ : valid_array_path (hierarchy ) ato zto  (Object.class o) (Object.arraysize o) ar)
    (_ : 0 <= i < zto)
    (_ : assoc (@pointer_eq_dec _) (obj, (ar, i, (Class.Inheritance.Repeated, ato :: nil))) (construction_states) = Some Constructed)
    (to : _)
    (_ : path (hierarchy) to p ato h) :
    dynamic_type
    Class.Inheritance.Repeated
    (ato :: nil) h p
  | dynamic_type_constructing_or_destructing
    (o : _)
    (_ : (heap) ! obj = Some o)
    (ato : _) (zto  : _)
    (_ : valid_array_path (hierarchy ) ato zto  (Object.class o) (Object.arraysize o) ar)
    (_ : 0 <= i < zto)
    (mdto : _) (mdh : _) (mdp : _)
    (_ : path (hierarchy ) mdto mdp ato mdh)
    (mdcs : _)
    (_ : mdcs = assoc (@pointer_eq_dec _) (obj, (ar, i, (mdh, mdp))) (construction_states))
    (_ : mdcs = Some BasesConstructed \/ mdcs = Some StartedDestructing)
    (to : _) (mdh' : _) (mdp' : _)
    (_ : path (hierarchy ) to mdp' mdto mdh')
    (_ : (h, p) = concat (mdh, mdp) (mdh', mdp')) :
    dynamic_type
    mdh
    mdp
    mdh' mdp'
.


Lemma dynamic_type_prop : forall mdh mdp mdh' mdp',
  dynamic_type mdh mdp mdh' mdp' ->
  exists o,
    (heap) ! obj = Some o /\
    exists ato, exists zto,
      valid_array_path (hierarchy ) ato zto  (Object.class o) (Object.arraysize o) ar /\
      0 <= i < zto /\
      exists mdto,
        path (hierarchy ) mdto mdp ato mdh /\
        exists to,
          path (hierarchy ) to mdp' mdto mdh' /\
          (h, p) = concat (mdh, mdp) (mdh', mdp')
          .
Proof.
 inversion 1; try subst.
  2 : eauto 11.
 symmetry in H7, H8; subst.
 case_eq (hierarchy ! ato).
 intros.
 esplit.
 split.
  eassumption.
 esplit.
 esplit.
 split.
  eassumption.
 split.
  assumption.
 esplit.
 split.
 eleft with (lt := nil).
 reflexivity.
 simpl; reflexivity.
 simpl.
 rewrite H5; trivial.
 esplit.
 split.
  eassumption.
 erewrite concat_trivial_left.
 reflexivity.
 eassumption.
 generalize (path_defined_from H4).
 intros; contradiction.
Qed.

End DynamicType.



Module State.
Section S.
  Variable A : ATOM.t.
  Variable nativeop : Type.

Inductive state_kind : Type :=
| codepoint (vars : PTree.t (Value.t A)) (current : stmt A nativeop) (further : list (stmt A nativeop)) (blocks : list (BlockPoint.t A nativeop))

(** Construction *)
| constr (obj : ident) (array : array_path A) (array_index : Z) (inhpath : Class.Inheritance.t * list ident) (tinit : list (FieldSignature.t A * (Z -> stmt A nativeop) (* list (Z * stmt A nativeop) *) ))  (initializers : list (Constructor.initializer_key A * stmt A nativeop)) (body : stmt A nativeop) (vars : PTree.t (Value.t A)) (k : Constructor.init_key_primary) (kind : Constructor.init_key_secondary k) (bases : list (Constructor.init_key_item A k))

(** Array cell construction *)
| constr_array (obj : ident) (array : array_path A) (array_size : Z) (array_index : Z) (class : ident) (init : (* list (Z * stmt A nativeop) *) Z -> stmt A nativeop) (vars : PTree.t (Value.t A))

(** Destruction *)
| destr (obj : ident) (array : array_path A) (array_index : Z) (inhpath : Class.Inheritance.t * list ident) (k : Constructor.init_key_primary) (kind : Constructor.init_key_secondary k) (bases : list (Constructor.init_key_item A k))
| destr_array (obj : ident) (array : array_path A) (array_index : Z) (class : ident)
.

Remark constr_inj : forall obj ar i cn tinit init body vars  k k2 q obj' ar' i' cn' tinit' init' body' vars' k' k2' q',
  constr obj ar i cn tinit init body vars (k := k) k2 q = constr obj' ar' i' cn'  tinit' init' body' vars' (k := k') k2' q' ->
  k = k' /\ existT (fun t => (Constructor.init_key_secondary t * list (Constructor.init_key_item _ t))%type) k (k2, q) = existT (fun t => (Constructor.init_key_secondary t * list (Constructor.init_key_item _ t))%type) k' (k2', q').
Proof.
  injection 1; intros; subst.
  split; auto.
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H0)).
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H1)).
  congruence.
Qed.


Corollary constr_inj_base : forall obj ar i cn tinit init body vars  k2 q obj' ar' i' cn' tinit' init' body' vars' k2' q',
  constr obj ar i cn tinit init body vars (k := Constructor.base) k2 q = constr obj' ar' i' cn'  tinit' init' body' vars' (k := Constructor.base) k2' q' ->
  k2 = k2' /\ q = q'.
Proof.
  intros.
  destruct (constr_inj H).
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H1)).
  injection 1.
  tauto.
Qed.

Corollary constr_inj_field : forall obj ar i cn tinit init body vars q obj' ar' i' cn' tinit' init' body' vars' q',
  constr obj ar i cn tinit init body vars (k := Constructor.field) tt q = constr obj' ar' i' cn'  tinit' init' body' vars' (k := Constructor.field) tt q' ->
  q = q'.
Proof.
  intros.
  destruct (constr_inj H).
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H1)).
  injection 1.
  tauto.
Qed.


Remark destr_inj : forall obj ar i cn   k k2 q obj' ar' i' cn' k' k2' q',
  destr obj ar i cn (k := k) k2 q = destr obj' ar' i' cn' (k := k') k2' q' ->
  k = k' /\ existT (fun t => (Constructor.init_key_secondary t * list (Constructor.init_key_item _ t))%type) k (k2, q) = existT (fun t => (Constructor.init_key_secondary t * list (Constructor.init_key_item _ t))%type) k' (k2', q').
Proof.
  injection 1; intros; subst.
  split; auto.
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H0)).
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H1)).
  congruence.
Qed.


Corollary destr_inj_base : forall obj ar i cn  k2 q obj' ar' i' cn' k2' q',
  destr obj ar i cn  (k := Constructor.base) k2 q = destr obj' ar' i' cn' (k := Constructor.base) k2' q' ->
  k2 = k2' /\ q = q'.
Proof.
  intros.
  destruct (destr_inj H).
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H1)).
  injection 1.
  tauto.
Qed.

Corollary destr_inj_field : forall obj ar i cn q obj' ar' i' cn' q',
  destr obj ar i cn (k := Constructor.field) tt q = destr obj' ar' i' cn' (k := Constructor.field) tt q' ->
  q = q'.
Proof.
  intros.
  destruct (destr_inj H).
  refine (_ (inj_pair2_eq_dec _ Constructor.init_key_primary_eq_dec _ _ _ _ H1)).
  injection 1.
  tauto.
Qed.

Record t : Type := make {
  kind : state_kind ;
  stack : list (StackFrame.t A nativeop) ;
  global : Globals.t A ;
  construction_states : list ((ident * (array_path A * Z * (Class.Inheritance.t * list ident))) * construction_state);
  field_construction_states : aux_constr_state_t A;
  deallocated_objects : list positive (* it is necessary to keep track of deallocated objects, to disallow some operations on such objects (e.g. pointing to an array cell, comparing pointers) *)
}.
End S.

Implicit Arguments constr [A nativeop].
Implicit Arguments constr_array [A nativeop].
Implicit Arguments destr [A nativeop].
Implicit Arguments destr_array [A nativeop].

End State.

Section Step.
Variable A : ATOM.t.
Variable nativeop : Type.

Record cppsemparam : Type := CppsemParam {
  enable_uninitialized_scalar_fields : bool
}.

  Variable prog : Program.t A nativeop.
  Let hierarchy := Program.hierarchy prog.

  Variable cppsem : cppsemparam.

  Variable sem : semparam A nativeop.
  Let evtr := evtr (sem).
  Let trace := trace evtr.
 
Inductive initial_state : State.t A nativeop -> Prop :=
| initial_state_intro :
  initial_state (State.make (State.codepoint (PTree.empty _) (Program.main prog) nil nil) nil (Globals.empty A) nil nil nil (* PTree.empty _ *)).

Inductive final_state : State.t A nativeop -> outcome evtr -> Prop :=
| final_state_intro : forall v rv stl g c auxc ty a i f,
  v ! rv = Some (Value.atom ty a) ->
  outcome_sem a i ->
  final_state (State.make (State.codepoint v (Sreturn (Some rv)) stl nil) nil g c auxc f) i.


Function requires_exit (s : stmt A nativeop) : bool :=
  match s with
    | Sreturn _ => true
(*    | Sconstructor _ _ => True
    | Sinitscalar _ => True *)
    | _ => false
  end.

Function requires_destruct (s : stmt A nativeop) : bool :=
  match s with
    | Sexit (S _) => true
    | _ => requires_exit s
  end.

Function exit_succ (s : stmt A nativeop) : option (stmt A nativeop) :=
  match s with
    | Sreturn r => Some (Sreturn r)
    | Sexit (S n) => Some (Sexit n)
    | _ => None
  end.

Lemma exit_succ_requires_destruct : forall s, exit_succ s <> None -> requires_destruct s = true.
Proof.
  intro s.
  functional induction (exit_succ s); simpl; congruence.
Qed.

Lemma requires_destruct_exit_succ : forall s, requires_destruct s = true -> exit_succ s <> None.
Proof.
  intro s.
  functional induction (requires_destruct s); simpl; try congruence.
  clear y.
  functional induction (requires_exit s); simpl; congruence.
Qed.
 

(** The following functions build the initial local environment at
  function entry, binding parameters to the provided arguments. *)

Function set_params (vl: list (Value.t A)) (il: list ident) {struct il} : PTree.t (Value.t A) :=
  match il, vl with
  | i1 :: is, v1 :: vs => PTree.set i1 v1 (set_params vs is)
  | _, _ => PTree.empty (Value.t A)
  end.

Inductive step : State.t A nativeop -> trace -> State.t A nativeop -> Prop :=
| step_Sskip : forall vars stm stl bl stk gl cs auxcs f,
  step
  (State.make (State.codepoint vars Sskip (stm :: stl) bl) stk gl cs auxcs f) E0
  (State.make (State.codepoint vars stm stl bl) stk gl cs auxcs f)

| step_Sif : forall vars stl bl stk gl cs auxcs test iftrue iffalse tgt b ty v f,
  vars ! test = Some (Value.atom ty v) ->
  sembool sem v = Some b ->
  tgt = (if b then iftrue else iffalse) ->
  step
  (State.make (State.codepoint vars (Sif test iftrue iffalse) stl bl) stk gl cs auxcs f) E0
  (State.make (State.codepoint vars tgt stl bl) stk gl cs auxcs f)

| step_Sloop : forall vars stm stl bl stk gl cs auxcs f,
  step
  (State.make (State.codepoint vars (Sloop stm) stl bl) stk gl cs auxcs f) E0
  (State.make (State.codepoint vars stm (Sloop stm :: stl) bl) stk gl cs auxcs f)

| step_Sseq :  forall vars stm1 stm2 stl bl stk gl cs auxcs f,
  step
  (State.make (State.codepoint vars (Sseq stm1 stm2) stl bl) stk gl cs auxcs f) E0
  (State.make (State.codepoint vars stm1 (stm2 :: stl) bl) stk gl cs auxcs f)

| step_Sexit_S : forall vars n stl stl0 bl stk gl cs auxcs f,
  step
  (State.make (State.codepoint vars (Sexit (S n)) stl0 (BlockPoint.make stl None :: bl)) stk gl cs auxcs f) E0
  (State.make (State.codepoint vars (Sexit n) stl bl) stk gl cs auxcs f)

| step_Sexit_O : forall vars stl0 bl stk gl cs auxcs f,
  step
  (State.make (State.codepoint vars (Sexit O) stl0 bl) stk gl cs auxcs f) E0
  (State.make (State.codepoint vars Sskip stl0 bl) stk gl cs auxcs f)

| step_Sskip_nil : forall vars bl stk gl cs auxcs f,
  step
  (State.make (State.codepoint vars Sskip nil bl) stk gl cs auxcs f) E0
  (State.make (State.codepoint vars (Sexit (S O)) nil bl) stk gl cs auxcs f)

| step_requires_exit : forall vars sexit stl stl0 bl stk gl cs auxcs f,
  requires_exit sexit = true ->
  step
  (State.make (State.codepoint vars sexit stl0 (BlockPoint.make stl None :: bl)) stk gl cs auxcs f) E0
  (State.make (State.codepoint vars sexit stl bl) stk gl cs auxcs f)

| step_Sblock_none : forall vars i stm stl bl stk gl cs auxcs f,
  step
  (State.make (State.codepoint vars (Sblock None i stm) stl bl) stk gl cs auxcs f) E0
  (State.make (State.codepoint vars stm nil (BlockPoint.make stl None :: bl)) stk gl cs auxcs f)

| step_Kreturnfromcall : forall vres vres' vars'' vars' vars stl stl' bl' stk gl cs auxcs f,
  match vres with
    | None => vres' = None /\ vars'' = vars'
    | Some v => exists val,
      vars ! v = Some val /\
      exists v', vres' = Some v' /\ vars'' = PTree.set v' val vars'
  end ->
  step
  (State.make (State.codepoint vars (Sreturn vres) stl nil) (StackFrame.Kreturnfromcall vres' vars' stl' bl' :: stk) gl cs auxcs f) E0
  (State.make (State.codepoint vars'' Sskip stl' bl') stk gl cs auxcs f)

| step_Snative :
  forall args vargs op vars stl bl stk gl cs auxcs f t vars' vres res,
  map (fun x : sigT (ATOM.val (t := A)) => match x with
               | existT ty va => Some (Value.atom ty va)
             end) args = map (fun i => vars ! i) vargs
   ->
   nativeop_sem op args res t ->
   match vres with
     | None => res = None /\ vars' = vars
     | Some vr => exists ty, exists va, res = Some (existT _ ty va) /\ vars' = PTree.set vr (Value.atom ty va) vars
   end ->
  step
  (State.make (State.codepoint vars (Snative op vargs vres) stl bl) stk gl cs auxcs f) t
  (State.make (State.codepoint vars' Sskip stl bl) stk gl cs auxcs f) 

| step_Smove : forall vars src val vars' tgt stl bl stk gl cs auxcs f,
  vars ! src = Some val ->
  vars' = PTree.set tgt val vars ->
  step
  (State.make (State.codepoint vars (Smove src tgt) stl bl) stk gl cs auxcs f) E0
  (State.make (State.codepoint vars' Sskip stl bl) stk gl cs auxcs f)

| step_Sgetfield : forall vars vobj obj ar i h p hp gl ty constate auxcs fs val vars' tgt stl bl stk f,
  vars ! vobj = Some (Value.ptr (Value.subobject obj ar i h p hp)) ->
  valid_pointer hierarchy (Globals.heap gl) ((Value.subobject obj ar i h p hp)) ->
  last p = Some ty -> forall fc, hierarchy ! ty = Some fc -> In fs (Class.fields fc) ->
    (forall cn sz, FieldSignature.type fs = FieldSignature.Struct cn sz -> In obj f -> False) (* this condition is necessary to avoid pointing to a structure field for a Destructed object. Unnecessary if the field is a scalar: the Invariant will show that, if it has a value, then the object is not yet deallocated. *) ->
  Globals.get_field (Globals.field_values gl) (obj, ar, i, (h, p), fs) = Some val ->
  vars' = PTree.set tgt val vars ->
  step
  (State.make (State.codepoint vars (Sgetfield vobj ty fs tgt) stl bl) stk gl constate auxcs f) E0
  (State.make (State.codepoint vars' Sskip stl bl) stk gl constate auxcs f)

| step_Sputfield : forall vars vobj obj ar i h p hp gl ty auxcs constate fs val l' gl' tgt stl bl stk f fc (fcn_def : last p = Some ty) (fc_def : hierarchy ! ty = Some fc) (fs_def : In fs (Class.fields fc)),
  vars ! vobj = Some (Value.ptr (Value.subobject obj ar i h p hp)) ->
  valid_pointer hierarchy (Globals.heap gl) ((Value.subobject obj ar i h p hp)) ->
  assoc (@aux_constr_state_key_eq_dec _) (obj, ar, i, (h, p), fs) auxcs = Some Constructed ->
  forall (Hval : vars ! tgt = Some val),
    Globals.put_field (Globals.field_values gl) (obj, ar, i, (h, p), fs) val = Some l' ->
  Globals.update gl l' = gl' ->
  step
  (State.make (State.codepoint vars (Sputfield vobj ty fs tgt) stl bl) stk gl constate auxcs f) E0
  (State.make (State.codepoint vars Sskip stl bl) stk gl' constate auxcs f)

| step_Sindex : forall vars vobj obj ar i cn hp vindex ty v delta vars' tgt stl bl stk gl constate auxcs f,
  (* this is a purely arithmetic operation, valid only if the pointer points to a most derived object. However, the pointer must be valid. Moreover, the complete object must not have been deallocated, otherwise the operation cannot compile. *)
  vars ! vobj = Some (Value.ptr (Value.subobject obj ar i Class.Inheritance.Repeated (cn :: nil) hp)) ->
  (In obj f -> False) ->
  forall o, (Globals.heap gl) ! obj = Some o ->
    forall n,
    valid_array_path hierarchy cn n (Object.class o) (Object.arraysize o) ar ->
    0 <= i < n ->
    0 <= i + delta < n ->
    vars ! vindex = Some (Value.atom ty v) ->
    semZ sem v = Some delta ->
    vars' = PTree.set tgt (Value.ptr (Value.subobject obj ar (i + delta) Class.Inheritance.Repeated (cn :: nil) hp)) vars ->
      step
      (State.make (State.codepoint vars (Sindex vobj cn vindex tgt) stl bl) stk gl constate auxcs f) E0
      (State.make (State.codepoint vars' Sskip stl bl) stk gl constate auxcs f)

| step_Sptreq : forall gl ptr1 ptr2 vars' (* ty *) vb vars vptr1 vptr2 tgt stl bl stk constate auxcs f,
  vars ! vptr1 = Some (Value.ptr ptr1) ->
  vars ! vptr2 = Some (Value.ptr ptr2) ->
  valid_pointer hierarchy (Globals.heap gl) ptr1 ->
  valid_pointer hierarchy (Globals.heap gl) ptr2 ->
  (* again, pointers must not point to deallocated objects *)
  match ptr1 with
    | (Value.null _) => True
    | (Value.subobject obj _ _ _ _ _) => (In obj f -> False)
  end ->
  match ptr2 with
    | (Value.null _) => True
    | (Value.subobject obj _ _ _ _ _) => (In obj f -> False)
  end ->
  Value.type_of (Value.ptr ptr1) = Value.type_of (Value.ptr ptr2) ->
  vb = (if Value.pointer_eq_dec ptr1 ptr2 then Value.atom _ (TRUE sem) else Value.atom _ (FALSE sem)) ->
  vars' = PTree.set tgt ((* Value.atom ty *) vb) vars ->
  step
  (State.make (State.codepoint vars (Sptreq vptr1 vptr2 tgt) stl bl) stk gl constate auxcs f) E0
  (State.make (State.codepoint vars' Sskip stl bl) stk gl constate auxcs f)

| step_Scall : forall args vars vargs,
  map (@Some _) args = map (fun v => PTree.get v vars) vargs ->
  forall ckind vargs' body',
    match ckind with
      | Static fid =>
        exists f, (Program.static_methods prog) ! fid = Some f /\
          vargs' = Static_method.args f /\
          body' = Static_method.code f
      | NonVirtual cn ms =>
        exists c, hierarchy ! cn = Some c /\
          exists m, Method.find ms (Class.methods c) = Some m /\
            exists cid, Method.kind m = Method.concrete cid /\
              exists mb, (Program.methods prog) ! cid = Some mb /\
                vargs' = Method_body.this mb :: Method_body.args mb /\
                body' = Method_body.code mb
    end ->
    forall vars',
      vars' = set_params args vargs' ->
      forall oret stl blocks stack global constate auxcs f,
        step
        (State.make (State.codepoint vars (Scall _ ckind vargs oret) stl blocks) stack global constate auxcs f)
        E0
        (State.make (State.codepoint vars' body' nil nil) (StackFrame.Kreturnfromcall oret vars stl blocks :: stack) global constate auxcs f)
  
| step_Sinvoke_virtual : forall args vars vobj obj ar i sh sp cn hp ch cp dh dp ccn ms mh mp mcn mc m mcode mb vargs h' p' hp' vars' stm' stl vres bl stk gl constate auxcs f,
  vars ! vobj = Some (Value.ptr (Value.subobject obj ar i sh sp hp)) ->
  dynamic_type (Program.hierarchy prog) (Globals.heap gl) constate obj ar i sh sp ch cp dh dp -> (* static pointer sh, sp is the dh, dp subobject of the dynamic complete object ch, cp *)
  last sp = Some cn ->
  last cp = Some ccn (* complete object so far (dynamic type) *) ->
  method_dispatch hierarchy ms cn ccn dh dp mh mp -> (* mh, mp is the path from the dynamic cc to the dispatched method *)
  (* calling dispatched method *)
  last mp = Some mcn ->
  hierarchy ! mcn = Some mc ->
  Method.find ms (Class.methods mc) = Some m ->
  Method.kind m = Method.concrete mcode ->
  (Program.methods prog) ! mcode = Some mb ->
  map (@Some _) args = map (fun v => vars ! v) vargs ->
  (h', p') = concat (ch, cp) (mh, mp) -> (* THIS pointer adjustment *)
  vars' = set_params (Value.ptr (Value.subobject obj ar i h' p' hp') :: args) (Method_body.this mb :: Method_body.args mb) ->
  stm' = Method_body.code mb ->
  step
  (State.make (State.codepoint vars (Sinvoke vobj cn ms vargs vres) stl bl) stk gl constate auxcs f) E0
  (State.make (State.codepoint vars' stm' nil nil) (StackFrame.Kreturnfromcall vres vars stl bl :: stk) gl constate auxcs f)

| step_Sdyncast : forall vars vobj obj ar i sh sp shp gl ch cp dh dp ccn cfrom cto vars' vres pres stl bl stk constate auxcs f,
  vars ! vobj = Some (Value.ptr (Value.subobject obj ar i sh sp shp)) ->
  dynamic_type (Program.hierarchy prog) (Globals.heap gl) constate obj ar i sh sp ch cp dh dp -> (* static pointer sh, sp is the dh, dp subobject of the dynamic complete object ch, cp *)
  last cp = Some ccn ->
  last sp = Some cfrom ->
  is_dynamic hierarchy cfrom ->
  (forall kh kp,
    dynamic_cast hierarchy ccn dh dp cfrom cto kh kp ->
    exists h', exists p', (h', p') = concat (ch, cp) (kh, kp) /\
      exists hp', pres = Value.subobject obj ar i h' p' hp') ->
  ((forall kh kp, dynamic_cast hierarchy ccn dh dp cfrom cto kh kp -> False) -> pres = Value.null A cto) ->  
  vars' = PTree.set vres (Value.ptr pres) vars ->
  step
  (State.make (State.codepoint vars (Sdyncast vobj cfrom cto vres) stl bl) stk gl constate auxcs f) E0
  (State.make (State.codepoint vars' Sskip stl bl) (stk) gl constate auxcs f)  

| step_Sstatcast : forall vars vobj obj ar i h p hp cfrom cs constate gl o ato zto cto ch cp vars' vres chp stl bl stk auxcs f,
  vars ! vobj = Some (Value.ptr (Value.subobject obj ar i h p hp)) ->
  last p = Some cfrom ->
  cs = assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) constate ->
  (Some BasesConstructed =< cs) ->
  (cs =< Some StartedDestructing) ->
  (Globals.heap gl) ! obj = Some o ->
  (valid_array_path (hierarchy ) ato zto  (Object.class o) (Object.arraysize o) ar) ->
  0 <= i < zto ->
  static_cast (Program.hierarchy prog) ato h p cfrom cto ch cp ->
  vars' = PTree.set vres (Value.ptr (Value.subobject obj ar i ch cp chp)) vars ->
  step
  (State.make (State.codepoint vars (Sstatcast vobj cfrom cto vres) stl bl) stk gl constate auxcs f) E0
  (State.make (State.codepoint vars' Sskip stl bl) (stk) gl constate auxcs f)
  

(* object construction *)

| step_Sblock_some : forall cn vars' init init' obj gl' gl num vars vlocstruct stm stl bl stk cs auxcs f hp,
  (* class must be defined in the program... *)
  hierarchy ! cn <> None ->
  0 < num ->
  (obj, gl') =  Globals.new gl cn num  ->
  vars' = PTree.set vlocstruct (Value.ptr (Value.subobject obj nil 0 Class.Inheritance.Repeated (cn :: nil) hp)) vars ->
    init' = (* list_of_list_Z_stmt *) init ->
  step
  (State.make (State.codepoint vars (Sblock (Some (vlocstruct, cn, num)) init stm) stl bl) stk gl cs auxcs f) E0
  (State.make (State.constr_array obj nil num 0 cn init' vars') (StackFrame.Kcontinue (StackFrame.continue_constr _) stm obj ((* Some *) stl) bl :: stk) gl' cs auxcs f)

| step_constr_array_nil_Kcontinue : forall ar gl obj n cn init vars stm bl stk cs auxcs f f' obj' obk bl',
  bl' = (* match obk with
          | Some stl' => BlockPoint.make stl' (Some obj') :: nil
          | _ => nil
        end ++ bl *) BlockPoint.make obk (Some obj') :: bl
  ->
  f' = f (* match obk with
         | None => PTree.set obj' (Some Constructed) f
         | _ => f
       end *)
  ->
  step
  (State.make (State.constr_array obj ar n n cn init vars) (StackFrame.Kcontinue (StackFrame.continue_constr _) stm obj' obk bl :: stk) gl cs auxcs f) E0
  (State.make (State.codepoint vars (* array construction variables prevail *) stm nil bl') stk gl cs auxcs f')

| step_constr_array_cons : forall gl obj cn n ar i cs vars init st stk auxcs f,
  i < n ->
  st = init i (* match assoc Z_eq_dec i init with
         | Some st' => st'
         | None => Sconstructor cn nil -- call default constructor if initializer not present -- necessary for dynamic arrays created by new[] --
       end *) -> 
  step
  (State.make (State.constr_array obj ar n i cn init vars) stk gl cs auxcs f) E0
  (State.make (State.codepoint vars st nil nil) (StackFrame.Kconstrarray obj ar n i cn init :: stk) gl cs auxcs f)

| step_constructor_Kconstrarray : forall args cn lconstr tvargs constr tinit' init' body' vars vars' hp c bases init b stl obj ar n i stk gl cs auxcs f,
  (* assume the specified constructor exists *)
  (Program.constructors prog) ! cn = Some lconstr ->
  assoc (@Program.constructor_key_eq_dec A) (map (fun tv : Typ.t A * var => let (ty, _) := tv in ty) tvargs) lconstr = Some constr ->
  map (@Some _) args = map (fun tv : Typ.t A * _ => let (_, v) := tv in vars ! v) tvargs ->
  tinit' = Constructor.struct_field_initializers constr ->
  init' = Constructor.initializers constr ->
  body' = Constructor.body constr ->
  vars' = set_params (Value.ptr (Value.subobject obj ar i Class.Inheritance.Repeated (cn :: nil) hp) :: args) (Constructor.this constr :: Constructor.args constr) ->
  hierarchy ! cn = Some c ->
  vborder_list hierarchy (Class.super c) bases ->
  b = cn ->
  step
  (State.make (State.codepoint vars (Sconstructor b tvargs) stl nil) (StackFrame.Kconstrarray obj ar n i cn init :: stk) gl cs auxcs f) E0
  (State.make (State.constr obj ar i (Class.Inheritance.Repeated, cn :: nil) tinit' init' body' vars' Constructor.base Constructor.virtual bases) (StackFrame.Kconstrothercells obj ar n i cn init vars :: stk) gl ((obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil)), StartedConstructing) :: cs) auxcs f)

| step_Kconstrothercells : forall gl obj cn n ar i i' stl init vars vars' stk cs auxcs f,
  i' = i + 1 ->
  step
  (State.make (State.codepoint vars (Sreturn None) stl nil) (StackFrame.Kconstrothercells obj ar n i cn init vars' :: stk) gl cs auxcs f) E0
  (State.make (State.constr_array obj ar n i' cn init vars') stk gl (((obj, (ar, i, (Class.Inheritance.Repeated, cn :: nil))), Constructed) :: cs) auxcs f)

| step_constr_cons : forall gl obj i ar hp tinit init code body vars stk cs auxcs f k k2 b q,
  (match k as k' return Constructor.init_key_item _ k' -> Prop with
     | Constructor.field => fun b' =>
       match FieldSignature.type b' with
         | FieldSignature.Struct _ _ => False
         | _ => True
       end
     | _ => fun _ => True
   end b) ->
  (match k as k' return Constructor.init_key_item _ k' -> Prop with
     | Constructor.field => fun _ => assoc (@Constructor.initializer_key_eq_dec _) (existT _ k (k2, b)) init = Some code
     | Constructor.base => fun b' =>
       code = match assoc (@Constructor.initializer_key_eq_dec _) (existT _ k (k2, b)) init with
                | Some code' => code'
                | None => Sconstructor b' nil (* default constructor if does not exist *)
              end
   end b) ->
  step
  (State.make (State.constr obj ar i hp tinit init body vars k k2 (b :: q)) stk gl cs auxcs f) E0
  (State.make (State.codepoint vars code nil nil) (StackFrame.Kconstr obj ar i hp tinit init body k k2 b q :: stk) gl cs auxcs f)

| step_constr_cons_field_struct : forall fs hp b n init' obj ar i ar' tinit init body vars q stk gl cs auxcs f,
  FieldSignature.type fs = FieldSignature.Struct b n ->
  init' = match assoc (@FieldSignature.eq_dec _) fs tinit with
            | Some init'' => init''
            | _ => (fun _ => Sconstructor b nil) (* call default constructors if initializer not present *)
          end ->
  ar' = ar ++ (i, hp, fs) :: nil ->
  step
  (State.make (State.constr obj ar i hp tinit init body vars Constructor.field tt (fs :: q)) stk gl cs auxcs f) E0
  (State.make (State.constr_array obj ar' (Zpos n) 0 b init' vars) (StackFrame.Kconstrother obj ar i hp tinit init body vars Constructor.field tt fs q :: stk) gl cs ((obj, ar, i, hp, fs, StartedConstructing) :: auxcs) f)

| step_Kconstr_base : forall args tvargs b lconstr constr tinit' init' body' vars' obj ar i h p h' p' hp' c bases stl tinit init body vars q stk gl cs f auxcs k2,
  map (@Some _) args = map (fun tv : Typ.t A * _ => let (_, v) := tv in vars ! v) tvargs ->
  (Program.constructors prog) ! b = Some lconstr ->
  assoc (@Program.constructor_key_eq_dec _) (map (fun tv :  Typ.t A * var => let (ty, _) := tv in ty) tvargs) lconstr = Some constr ->
  tinit' = Constructor.struct_field_initializers constr ->
  init' = Constructor.initializers constr ->
  body' = Constructor.body constr ->
  h' = match k2 with
         | Constructor.virtual => Class.Inheritance.Shared
         | _ => h
       end ->
  p' = match k2 with
         | Constructor.virtual => b :: nil
         | _ => p ++ b :: nil
       end ->
  vars' = set_params (Value.ptr (Value.subobject obj ar i h' p' hp') :: args) (Constructor.this constr :: Constructor.args constr) ->
  hierarchy ! b = Some c ->
  bases = map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b) (filter (fun hb : _ * ident =>
    match hb with
      | (Class.Inheritance.Shared, _) => false
      | _ => true
    end
  ) (Class.super c)) ->
  step
  (State.make (State.codepoint vars (Sconstructor b tvargs) stl nil) (StackFrame.Kconstr obj ar i (h, p) tinit init body Constructor.base k2 b q :: stk) gl cs auxcs f) E0
  (State.make (State.constr obj ar i (h', p') tinit' init' body' vars' Constructor.base Constructor.direct_non_virtual bases) (StackFrame.Kconstrother obj ar i (h, p) tinit init body vars Constructor.base k2 b q :: stk) gl (((obj, (ar, i, (h', p'))), StartedConstructing) :: cs) auxcs f)

| step_Kconstrother_bases : forall vars stl obj ar i tinit init body vars' b q stk gl cs f k2 h p h' p' auxcs ,
  h' = match k2 with
         | Constructor.virtual => Class.Inheritance.Shared
         | _ => h
       end ->
  p' = match k2 with
         | Constructor.virtual => b :: nil
         | _ => p ++ b :: nil
       end ->
  step
  (State.make (State.codepoint vars (Sreturn None) stl nil) (StackFrame.Kconstrother obj ar i (h, p) tinit init body vars' Constructor.base k2 b q :: stk) gl cs auxcs f) E0
  (State.make (State.constr obj ar i (h, p) tinit init body vars' Constructor.base k2 q) stk gl (((obj, (ar, i, (h', p'))), Constructed) :: cs) auxcs f)

| step_constr_virtual_bases_nil : forall gl obj i ar h p cn tinit init body vars stk cs f bases c auxcs,
  last p = Some cn ->
  hierarchy ! cn = Some c ->
  bases = map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b) (filter (fun hb : _ * ident =>
    match hb with
      | (Class.Inheritance.Shared, _) => false
      | _ => true
    end
  ) (Class.super c)) ->
  step
  (State.make (State.constr obj ar i (h, p) tinit init body vars Constructor.base Constructor.virtual nil) stk gl cs auxcs f) E0
  (State.make (State.constr obj ar i (h, p) tinit init body vars Constructor.base Constructor.direct_non_virtual bases) stk gl cs auxcs f)

| step_constr_non_virtual_bases_nil : forall gl obj cn i ar h p tinit init body vars stk cs f fields auxcs c,
  last p = Some cn ->
  hierarchy ! cn = Some c ->
  fields = Class.fields c ->
  step
  (State.make (State.constr obj ar i (h, p) tinit init body vars Constructor.base Constructor.direct_non_virtual nil) stk gl cs auxcs f) E0
  (State.make (State.constr obj ar i (h, p) tinit init body vars Constructor.field tt fields) stk gl (((obj,(ar, i, (h, p))), BasesConstructed) :: cs) auxcs f)

| step_constr_fields_cons_scalar_no_init : forall fs ty tinit init obj ar i h p body vars q stk gl cs auxcs f
  (Henable : enable_uninitialized_scalar_fields cppsem = true)
  ,
  FieldSignature.type fs = FieldSignature.Scalar ty ->
  assoc (@Constructor.initializer_key_eq_dec _) (existT _ Constructor.field (tt, fs)) init = None ->
  step
  (State.make (State.constr obj ar i (h, p) tinit init body vars Constructor.field tt (fs :: q)) stk gl cs auxcs f) E0
  (State.make (State.constr obj ar i (h, p) tinit init body vars Constructor.field tt q) stk gl cs ((obj, ar, i, (h, p), fs, Constructed) :: auxcs) f)

| step_Kconstr_field_scalar : forall fs ty varg arg p cn gl obj ar i h l' gl' vars stl tinit init body q stk cs auxcs f,
  FieldSignature.type fs = FieldSignature.Scalar ty ->
  vars ! varg = Some arg ->
  last p = Some cn ->
  True ->
  Globals.put_field (Globals.field_values gl) (obj, ar, i, (h, p), fs) arg = Some l' ->
  gl' = Globals.update gl l' ->
  step
  (State.make (State.codepoint vars (Sinitscalar varg) stl nil) (StackFrame.Kconstr obj ar i (h, p) tinit init body Constructor.field tt fs q :: stk) gl cs auxcs f) E0
  (State.make (State.constr obj ar i (h, p) tinit init body vars Constructor.field tt q) stk gl' cs ((obj, ar, i, (h, p), fs, Constructed) :: auxcs) f)

| step_Kconstrother_fields : forall obj ar n b init vars obj' ar' i' h p tinit' init' body' vars' q stk gl cs auxcs fs f,  
  step
  (State.make (State.constr_array obj ar n n b init vars) (StackFrame.Kconstrother obj' ar' i' (h, p) tinit' init' body' vars' Constructor.field tt fs q :: stk) gl cs auxcs f) E0
  (State.make (State.constr obj' ar' i' (h, p) tinit' init' body' vars (* variables for array construction prevail *) Constructor.field tt q) stk gl cs ((obj', ar', i', (h, p), fs, Constructed) :: auxcs) f)

| step_constr_fields_nil : forall obj ar i h p tinit init body vars stk gl cs auxcs f,
  step
  (State.make (State.constr obj ar i (h, p) tinit init body vars Constructor.field tt nil) stk gl cs auxcs f) E0
  (State.make (State.codepoint vars body nil nil) stk gl cs auxcs f)

(* Object destruction :  *)

| step_destr_array : forall obj ar j cn stk gl cs auxcs f c m mcode mb v stm hp,
  0 <= j ->
  hierarchy ! cn = Some c ->
  Method.find (Program.destructor_sig prog) (Class.methods c) = Some m ->
  Method.kind m = Method.concrete mcode ->
  (Program.methods prog) ! mcode = Some mb ->
  v = PTree.set (Method_body.this mb) (Value.ptr (Value.subobject obj ar j Class.Inheritance.Repeated (cn :: nil) hp)) (PTree.empty _) ->
  stm = Method_body.code mb -> 
  step
  (State.make (State.destr_array obj ar j cn) stk gl cs auxcs f) E0
  (State.make (State.codepoint v stm nil nil) (StackFrame.Kdestr obj ar j (Class.Inheritance.Repeated, cn :: nil) :: StackFrame.Kdestrcell obj ar j cn :: stk) gl (((obj, (ar, j, (Class.Inheritance.Repeated, cn :: nil))), StartedDestructing) :: cs) auxcs f)

| step_Kdestr_return : forall p cn c l vars stl obj ar i h stk gl cs auxcs f,
  last p = Some cn ->
  hierarchy ! cn = Some c ->
  Class.fields c = rev l ->
  step
  (State.make (State.codepoint vars (Sreturn None) stl nil) (StackFrame.Kdestr obj ar i (h, p) :: stk) gl cs auxcs f) E0
  (State.make (State.destr obj ar i (h, p) Constructor.field tt l) stk gl cs auxcs f)

| step_destr_field_scalar : forall fs ty obj ar i h p l stk gl gl' cs auxcs f
  (Hunassign: gl' = Globals.update gl (remove_field (obj, ar, i, (h, p), fs) (Globals.field_values gl))),
  FieldSignature.type fs = FieldSignature.Scalar ty ->
  step
  (State.make (State.destr obj ar i (h, p) Constructor.field tt (fs :: l)) stk gl cs auxcs f) E0
  (State.make (State.destr obj ar i (h, p) Constructor.field tt l) stk gl' cs ((obj, ar, i, (h, p), fs, Destructed) :: auxcs) f)

| step_destr_field_struct : forall fs b n ar' ar i h p j obj l stk gl cs auxcs f,
  FieldSignature.type fs = FieldSignature.Struct b n ->  
  ar' = ar ++ (i, (h, p), fs) :: nil ->
  j = Zpos n - 1 ->
  step
  (State.make (State.destr obj ar i (h, p) Constructor.field tt (fs :: l)) stk gl cs auxcs f) E0
  (State.make (State.destr_array obj ar' j b) (StackFrame.Kdestrother obj ar i (h, p) Constructor.field tt fs l :: stk) gl cs ((obj, ar, i, (h, p), fs, StartedDestructing) :: auxcs) f)  

| step_destr_array_nil_fields : forall obj ar j cn obj' ar' i' hp' l stk gl cs auxcs f fs,
  j = -1 ->
  step
  (State.make (State.destr_array obj ar j cn) (StackFrame.Kdestrother obj' ar' i' hp' Constructor.field tt fs l :: stk) gl cs auxcs f) E0
  (State.make (State.destr obj' ar' i' hp' Constructor.field tt l) stk gl cs ((obj', ar', i', hp', fs, Destructed) :: auxcs) f)

| step_destr_field_nil : forall p cn c bases obj ar i h stk gl cs auxcs f,
  last p = Some cn ->
  hierarchy ! cn = Some c ->
  rev bases = map (fun hb : Class.Inheritance.t * ident => let (_, b) := hb in b) (filter (fun hb : _ * ident =>
    match hb with
      | (Class.Inheritance.Shared, _) => false
      | _ => true
    end
  ) (Class.super c)) ->
  step
  (State.make (State.destr obj ar i (h, p) Constructor.field tt nil) stk gl cs auxcs f) E0
  (State.make (State.destr obj ar i (h, p) Constructor.base Constructor.direct_non_virtual bases) stk gl (((obj, (ar, i, (h, p))), DestructingBases) :: cs) auxcs f)

| step_destr_base_cons : forall h' beta h p' hp' b p obj ar i bases stk gl cs f c m mcode mb v auxcs stm,
  h' = match beta with
         | Constructor.virtual => Class.Inheritance.Shared
         | _ => h
       end ->
  p' = match beta with
         | Constructor.virtual => b :: nil
         | _ => p ++ b :: nil
       end ->
  hierarchy ! b = Some c ->
  Method.find (Program.destructor_sig prog) (Class.methods c) = Some m ->
  Method.kind m = Method.concrete mcode ->
  (Program.methods prog) ! mcode = Some mb ->
  v = PTree.set (Method_body.this mb) (Value.ptr (Value.subobject obj ar i h' p' hp')) (PTree.empty _) ->
  stm = Method_body.code mb -> 
  step
  (State.make (State.destr obj ar i (h, p) Constructor.base beta (b :: bases)) stk gl cs auxcs f) E0
  (State.make (State.codepoint v stm nil nil) (StackFrame.Kdestr obj ar i (h', p') :: StackFrame.Kdestrother obj ar i (h, p) Constructor.base beta b bases :: stk) gl (((obj, (ar, i, (h', p'))), StartedDestructing) :: cs) auxcs f)

| step_destr_base_non_virtual_nil_bases : forall obj ar i hp obj' ar' i' hp' beta bases' stk gl cs f auxcs b,
step
  (State.make (State.destr obj ar i hp Constructor.base Constructor.direct_non_virtual nil) (StackFrame.Kdestrother obj' ar' i' hp' Constructor.base beta b bases' :: stk) gl cs auxcs f) E0
  (State.make (State.destr obj' ar' i' hp' Constructor.base beta bases') stk gl (((obj, (ar, i, hp)), Destructed) :: cs) auxcs f)

| step_destr_base_non_virtual_nil_cell : forall cn' c bases' obj ar i hp obj' ar' i' stk gl cs auxcs f,
  hierarchy ! cn' = Some c ->
  vborder_list hierarchy (Class.super c) (rev bases') ->  
  step
  (State.make (State.destr obj ar i hp Constructor.base Constructor.direct_non_virtual nil) (StackFrame.Kdestrcell obj' ar' i' cn' :: stk) gl cs auxcs f) E0
  (State.make (State.destr obj' ar' i' (Class.Inheritance.Repeated, cn' :: nil) Constructor.base Constructor.virtual bases') stk gl cs auxcs f)

| step_destr_base_virtual_nil : forall p cn i i' obj ar h stk gl cs auxcs f,
  last p = Some cn ->
  i' = i - 1 ->
  step
  (State.make (State.destr obj ar i (h, p) Constructor.base Constructor.virtual nil) stk gl cs auxcs f) E0
  (State.make (State.destr_array obj ar i' cn) stk gl (((obj, (ar, i, (h,p))), Destructed) :: cs) auxcs f) 

| step_requires_destruct : forall sdestruct gl obj o i cn stl bl stk cs auxcs f vars stl0,
  requires_destruct sdestruct = true ->
  (Globals.heap gl) ! obj = Some o ->
  i = Object.arraysize o - 1 ->
  cn = Object.class o ->
  step
  (State.make (State.codepoint vars sdestruct stl0 (BlockPoint.make stl (Some obj) :: bl)) stk gl cs auxcs f) E0
  (State.make (State.destr_array obj nil i cn) (StackFrame.Kcontinue (StackFrame.continue_destr vars) (sdestruct  ) obj ( (* Some *) stl) bl :: stk) gl cs auxcs f)

| step_destr_array_nil_continue : forall i obj cn vars stm bl stk gl cs auxcs f f' obj' ostl stm' bl',
  i = -1 -> 
  bl' = bl ->
  forall
  (Hsucc :exit_succ stm = Some stm') (* match ostl with
          | Some stl => BlockPoint.make stl None :: nil
          | _ => nil
        end ++ bl *),
  f' = obj' :: f (* "deallocate" obj' *) ->
  step
  (State.make (State.destr_array obj nil i cn) (StackFrame.Kcontinue (StackFrame.continue_destr vars) stm obj' ostl bl :: stk) gl cs auxcs f) E0
  (State.make (State.codepoint vars stm' ostl bl') stk gl cs auxcs f')
.

End Step.
