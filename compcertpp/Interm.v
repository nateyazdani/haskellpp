Require Import Coqlib.
Require Import Cplusconcepts.
Require Import LibLists.
Require Import Tactics.
Require Import LibMaps.
Require Import Relations.
Require Import Dynamic.
Require Import Events.
Require Import IntermSetDynType.
Load Param.
Open Scope Z_scope.

Notation var := (ident) (only parsing).

    Section Source.

  Inductive path_operation : Type :=
  | rootpath (cn : ident) (* create a root path for class C (~ pointer to VTT of most-derived object C) *)
  | addbase (_ : ident) (_ : Class.Inheritance.t) (cn : ident) (* add a base to the given path (~ access sub-VTT of a base) *)
.

Variable A : ATOM.t .
Variable nativeop : Type.

  Inductive callkind :=
  | NonVirtual (cn : ident) (ms : MethodSignature.t A)
  | Static (fid : ident)
    .
           
      Inductive stmt : Type :=
      | skip
      | seq (_ _ : stmt)
      | move (source target : var)
      | test (test : var) (ifso ifnot : stmt)
      | block (array : option (ident * (ident * Z))) (body : stmt)
      | exit (n : nat) (** block/exit, cf. Compcert Cminor *)
      | loop (body : stmt)
      | native (op : nativeop) (source : list var) (target : option var)
      | ret (_ : option var)
      | call (ck : callkind) (vargs : list var) (target : option var) (* static function call *)

      (** C++ object-oriented features *)
      | null (class : ident) (target : var) (** creates a null pointer of some type *)
      | ptreq (ptr1 ptr2 : var) (target : var)
      | getfield (class : ident) (field : FieldSignature.t A) (source : var) (target : var)
      | putfield (class : ident) (field : FieldSignature.t A) (source : ident) (newvalue : var)
      | statcast (from : ident) (to : ident) (source : var) (target : var)
      | dyncast (from : ident) (to : ident) (source : var) (target : var)
      | arrayindex (class : ident) (index : var) (source : var) (target : var)
      | invoke (source : var) (class : ident) (ms : MethodSignature.t A) (args : list var) (retval : option var)

      (* construction-specific *)
      | pathop (_ : path_operation) (source : option var) (target : var)
      | setdyntype (ismostderived_flag : bool) (class : ident) (source path : var) (* declares the source pointer to be a dynamically most-derived object (i.e. object under construction). The path must match the path of the pointer. *)
      | casttobase (source : var) (cn : ident) (kind : Class.Inheritance.t) (base : ident) (target : var) (* *constant* cast to base (i.e. virtual cast requires the pointer to point to a most-derived object) *)
        .

      Record method_body : Type := Method_body {
        mthis : var;
        margs : list var;
        mcode : stmt
      }.

      Record static_fun : Type := Static_fun {
        sargs   : list var;
        scode   : stmt
      }.


      Record program : Type := Program {
        hierarchy : PTree.t (Class.t A);
        methods : PTree.t method_body;
        statics : PTree.t static_fun;
        main : stmt
      }.     

      Section Sem.

        Inductive value : Type :=
        | Val (_ : Value.t A)
        | Path (_ : ident) (_ : Class.Inheritance.t) (_ : list ident) (* needed for construction and destruction ~ pointer to VTT *)
        .


        Record global_state : Type := Global {
          globals : Globals.t A;
(*          allow_static_cast : list (positive * (array_path A * Z * (Class.Inheritance.t * list ident))); *)
          dynamic_type : list_dynamic_type A
        }.

(*
        Lemma dynamic_type_key_eq_dec : forall (a1 a2 : positive * array_path A * Z), {a1 = a2} + {a1 <> a2}.
        Proof.
          apply prod_eq_dec.
          apply prod_eq_dec.
          exact peq.
          apply array_path_eq_dec.
          exact Z_eq_dec.
        Qed.          
*)

        Inductive frame : Type :=
        | Block (bobject : option positive) (bstmt : list stmt)
        | Callframe (ffurther : list stmt) (fvars : PTree.t value) (fret : option var)
          .

        Record state : Type := State {
          current : stmt;
          further : list stmt;
          vars : PTree.t value;
          stack : list frame;
          global : global_state
        }.
        
        Notation atom := (fun ty va => Val (Value.atom ty va)) (only parsing).

        Function exit_succ (s : stmt) : option stmt :=
          match s with
            | exit (S n) => Some (exit n)
            | ret ov => Some (ret ov)
            | _ => None
          end.

        Section Path_operation_sem.

          Variable hierarchy : PTree.t (Class.t A).

          Inductive path_operation_sem : path_operation -> option value ->  value -> Prop := 

          | path_operation_sem_rootpath : forall cn, (* hierarchy ! cn <> None -> *)
            path_operation_sem (rootpath cn) None (Path cn  Class.Inheritance.Repeated (cn :: nil))
            
          | path_operation_sem_addbase : forall h p cn to,
            path hierarchy to p cn h ->
            forall h' p' inh b, (h', p') =
              match inh with
                | Class.Inheritance.Repeated => (h, p ++ b :: nil)
                | Class.Inheritance.Shared => (Class.Inheritance.Shared, b :: nil)
              end ->
              match inh with
                | Class.Inheritance.Repeated => exists c, hierarchy ! to = Some c /\ In (Class.Inheritance.Repeated, b) (Class.super c)
                | Class.Inheritance.Shared => (h, p) = (Class.Inheritance.Repeated, cn :: nil) /\ is_virtual_base_of hierarchy b to
              end ->
              path_operation_sem (addbase to inh b) (Some (Path cn h p)) (Path cn h' p')
              .

          End Path_operation_sem.

Function set_params (vl: list value) (il: list ident) {struct il} : PTree.t (value) :=
  match il, vl with
  | i1 :: is, v1 :: vs => PTree.set i1 v1 (set_params vs is)
  | _, _ => PTree.empty (value)
  end.

        Variable prog : program.
        Notation hierarchy := (hierarchy prog) (only parsing).

        Variable sem : semparam A nativeop.
        Variable is_primary_path : list ident -> bool.

        Inductive initial_state : state -> Prop :=
        | initial_state_intro :
          initial_state (State (main prog) nil (PTree.empty _) nil (Global (Globals.empty A) nil)).

        Inductive final_state : state -> outcome (evtr sem) -> Prop :=
        | final_state_intro : forall v rv stl g ty a i,
          v ! rv = Some (Val (Value.atom ty a)) ->
          outcome_sem a i ->
          final_state (State (ret (Some rv)) stl v nil g) i
          .
        
        Inductive step : state -> trace (evtr sem) -> state -> Prop :=

        | step_skip : forall stm stl vars stack global,
          step
          (State skip (stm :: stl) vars stack global)
          E0
          (State stm stl vars stack global)

        | step_seq : forall stl s1 s2 vars stack global,
          step
          (State (seq s1 s2) stl vars stack global)
          E0
          (State s1 (s2 :: stl) vars stack global)

        | step_move : forall source v vars,
          vars ! source = Some v ->
          forall target vars',
            vars' = PTree.set target v vars ->
              forall stl stack global,
                step
                (State (move source target) stl vars stack global)
                E0
                (State skip stl vars' stack global)          

        | step_test : forall vars varb tyb valb,
          vars ! varb = Some (@atom tyb valb) ->
          forall b, sembool sem valb = Some b ->
            forall s ifso ifnot, s = (if b then ifso else ifnot) ->
              forall stl stack global,
                step
                (State (test varb ifso ifnot) stl vars stack global)
                E0
                (State s stl vars stack global)

        | step_loop : forall stmt stl vars stack global,
          step
          (State (loop stmt) stl vars stack global)
          E0
          (State stmt (loop stmt :: stl) vars stack global)

        | step_block_None : forall stm stl vars stack global,
          step
          (State (block None stm) stl vars stack global)
          E0
          (State stm nil vars (Block None stl :: stack) global)
         
        | step_block_Some : forall sz, 
          (0 < sz)%Z ->
          forall cn,
            hierarchy ! cn <> None ->
            forall gl obj gl',
            Globals.new gl cn sz = (obj, gl') ->
            forall c vars' vars hp, vars' = PTree.set c (Val (Value.ptr (Value.subobject obj nil 0 Class.Inheritance.Repeated (cn :: nil) hp))) vars ->
              forall stm stl stack  dt,
                step
                (State (block (Some (c, (cn, sz))) stm) stl vars stack (Global gl  dt))
                E0
                (State stm nil vars' (Block (Some obj) stl :: stack) (Global gl'  dt))

        | step_exit_O : forall stl vars stack global,
          step
          (State (exit O) stl vars stack global)
          E0
          (State skip stl vars stack global) (* skip *)

        | step_exit_S_return_cons : forall oobj gl gl',
          gl' = match oobj with
                  | None => gl
                  | Some obj => Globals.remove gl obj
                end ->
          forall stm stm',
            exit_succ stm = Some stm' ->
            forall stl stl' vars stack  dt,
              step
              (State stm stl vars (Block oobj stl' :: stack) (Global gl  dt))
              E0
              (State stm' stl' vars stack (Global gl'  dt))
        
        | step_return_nil : forall orv ov vars'' vars' vars,
          match orv with
            | None => ov = None /\ vars'' = vars'
            | Some rv => exists v, ov = Some v /\ exists val, vars ! v = Some val /\ vars'' = PTree.set rv val vars'
          end -> forall stl stl'  stack global,
          step
          (State (ret ov) stl vars (Callframe stl' vars' orv :: stack) global)
          E0
          (State skip stl' vars'' stack global)

        | step_call : 
          forall args vars vargs,
            map (@Some _) args = map (fun v => PTree.get v vars) vargs ->
            forall kind vargs' body',
              match kind with
                | Static fid =>
                  exists f, (statics prog) ! fid = Some f /\
                    vargs' = sargs f /\
                    body' = scode f
                | NonVirtual cn ms =>
                  exists c, hierarchy ! cn = Some c /\
                    exists m, Method.find ms (Class.methods c) = Some m /\
                      exists cid, Method.kind m = Method.concrete cid /\
                        exists mb, (methods prog) ! cid = Some mb /\
                          vargs' = mthis mb :: margs mb /\
                          body' = mcode mb
              end ->
              forall vars',
                vars' = set_params args vargs' ->
                forall oret stl stack global,
                  step
                  (State (call kind vargs oret) stl vars stack global)
                  E0
                  (State body' nil vars' (Callframe stl vars oret :: stack) global)            
      | step_native :
        forall args source vars,
          map (fun a : sigT (ATOM.val (t := A)) => let (ty, va) := a in Some (atom ty va)) args =         
          map (fun v => PTree.get v vars) source ->
          forall op ores t,
            nativeop_sem op args ores t ->
            forall vars' target,
            match ores with
              | None => vars' = vars /\ target = None
              | Some (existT rty rva) => exists tarv, target = Some tarv /\ vars' = PTree.set tarv (atom rty rva) vars
            end ->
                forall stl stack global,
                  step
                  (State (native op source target) stl vars stack global)
                  t
                  (State skip stl vars' stack global)

        (** null pointer *)
        | step_null : forall vars vars' class target,
          vars' = PTree.set target (Val (Value.ptr (Value.null A class))) vars ->
            forall stl global stack,
              step
              (State (null class target) stl vars stack global)
              E0
              (State skip stl vars' stack global)

(** pointer equality *)
      | step_ptreq : forall v1 ptr1 vars,
        vars ! v1 = Some (Val (Value.ptr ptr1)) ->
        forall global,
        valid_pointer hierarchy (Globals.heap global) ptr1 ->
        forall v2 ptr2,
          vars ! v2 = Some (Val (Value.ptr ptr2)) ->
          valid_pointer hierarchy (Globals.heap global) ptr2 ->
          Value.type_of (Value.ptr ptr1) = Value.type_of (Value.ptr ptr2) ->
          forall vars' target,
            vars' = PTree.set target
              (if Value.pointer_eq_dec ptr1 ptr2
                then
                  atom (tyTRUE sem)
                  (TRUE sem)
                else
                  atom (tyFALSE sem)
                  (FALSE sem)
              ) vars ->
              forall stl stack  dt,
                step
                (State (ptreq v1 v2 target) stl vars stack (Global global  dt))
                E0
                (State skip stl vars' stack (Global global  dt))

(** get field *)
      | step_getfield : forall vars source obj ar i h p hp,
        vars ! source = Some (Val (Value.ptr (@Value.subobject _ obj ar i h p hp))) ->
        forall global,
          valid_pointer hierarchy (Globals.heap global) (Value.subobject obj ar i h _ hp) ->
          forall class,
            last p = Some class ->
            forall c, hierarchy ! class = Some c ->
              forall fs, In fs (Class.fields c) ->              
                forall v, Globals.get_field (Globals.field_values global) (obj, ar, i, (h, p), fs) = Some v ->
                  forall vars' target,
                    vars' = PTree.set target (Val v) vars ->
                      forall stl stack  dt,
                        step
                        (State (getfield class fs source target) stl vars stack (Global global  dt))
                        E0
                        (State skip stl vars' stack (Global global  dt))

(** put field *)
      | step_putfield : forall vars source obj ar i h p hp,
        vars ! source = Some (Val (Value.ptr (@Value.subobject _ obj ar i h p hp))) ->
        forall global,
          valid_pointer hierarchy (Globals.heap global) (Value.subobject obj ar i h _ hp) ->
            forall class, last p = Some class ->
              forall c, hierarchy ! class = Some c ->
                forall fs, In fs (Class.fields c) ->
                  forall newvalue v,
                    vars ! newvalue = Some (Val v) ->
                    forall l',
                      Globals.put_field (Globals.field_values global) (obj, ar, i, (h, p), fs) v = Some l' ->
                    forall global', global' = Globals.update global l' ->
                      forall stl stack  dt,
                        step
                        (State (putfield class fs source newvalue) stl vars stack (Global global  dt))
                        E0
                        (State skip stl vars stack (Global global'  dt))

(** static cast *)
        | step_statcast : forall vars source obj ar i h p hp,
          vars ! source = Some (Val (Value.ptr (@Value.subobject _ obj ar i h p hp))) ->
          forall dt,
          assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) dt <> None -> (* we are allowed to access virtual bases *)
        (** real : class of the most derived object *)
        (** from : static type of the pointer *)
        (** to : class to which to cast *)
            forall o global,
              (Globals.heap global) ! obj = Some o ->
              forall real from,
                valid_relative_pointer hierarchy (Object.class o) (Object.arraysize o) ar real i h p from ->
                forall to h' p',
                  static_cast hierarchy real h p from to h' p' ->
                  forall hp' target vars',
                    vars' = PTree.set target (Val (Value.ptr (@Value.subobject _ obj ar i h' p' hp'))) vars ->
                      forall stl  stack,
                        step
                        (State (statcast from to source target) stl vars stack (Global global dt))
                        E0
                        (State skip stl vars' stack (Global global dt))

(** dynamic cast *)
        | step_dyncast : forall vars source obj ar i h p hp,
          vars ! source = Some (Val (Value.ptr (@Value.subobject _ obj ar i h p hp))) ->
          forall global,
            valid_pointer hierarchy (Globals.heap global) (@Value.subobject _ obj ar i h p hp) ->
          forall dt h0 p0 h1 p1,
            assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) dt = Some ((h0, p0), (h1, p1)) ->
        (** real : class of the most derived object *)
        (** from : static type of the pointer *)
        (** to : class to which to cast *)
            forall real, last p0 = Some real ->           
              forall from,
                last p = Some from ->
                is_dynamic hierarchy from -> (** required by the Standard; needed for access to VTable *)
                forall newptr to,
                  (forall h2 p2, dynamic_cast hierarchy real h1 p1 from to h2 p2 -> exists h', exists p', (h', p') = concat (h0, p0) (h2, p2) /\ exists hp', newptr = (@Value.subobject _ obj ar i h' p' hp')) ->                
                  ((forall h' p', dynamic_cast hierarchy real h1 p1 from to h' p' -> False) -> newptr = (Value.null _ to)) ->
                  (forall h'' p'', path hierarchy to p'' from h'' -> False) -> (* target must not be a base, in which case a more complete compiler should replace dynamic cast with static cast *)
                  forall target vars',
                    vars' = PTree.set target (Val (Value.ptr newptr)) vars ->
                      forall  stl stack,
                        step
                        (State (dyncast from to source target) stl vars stack (Global global  dt))
                        E0
                        (State skip stl vars' stack (Global global  dt))

(* invoke *)
        | step_invoke : forall vars source obj ar i h p hp,
          vars ! source = Some (Val (Value.ptr (@Value.subobject _ obj ar i h p hp))) ->
          forall dt h0 p0 h1 p1,
            assoc (@pointer_eq_dec _) (obj, (ar, i, (h, p))) dt = Some ((h0, p0), (h1, p1)) ->
            forall global,
              valid_pointer hierarchy (Globals.heap global) (@Value.subobject _ obj ar i h p hp) ->
        (** real : class of the most derived object *)
        (** from : static type of the pointer *)
        (** to : class to which to cast *)
              forall real, last p0 = Some real ->           
                forall from,
                  last p = Some from ->
                  forall ms h2 p2,
                    method_dispatch hierarchy ms from real h1 p1 h2 p2 ->
                    forall mcn,
                      last p2 = Some mcn ->
                      forall mc,
                      hierarchy ! mcn = Some mc ->
                      forall m, Method.find ms (Class.methods mc) = Some m ->
                        forall mcd, Method.kind m = Method.concrete mcd ->
                          forall mb, (methods prog) ! mcd = Some mb ->
                            forall args vargs,
                              map (@Some _) args = map (fun v => vars ! v) vargs ->
                              forall h' p',
                                (h', p') = concat (h0, p0) (h2, p2) -> (* THIS pointer adjustment *)
                                forall hp' vars', vars' = set_params (Val (Value.ptr (Value.subobject obj ar i h' p' hp')) :: args) (mthis mb :: margs mb) ->
                                  forall stm', stm' = mcode mb ->
                                    forall vres stl stack ,
                                      step
                                      (State (invoke source from ms vargs vres) stl vars stack (Global global  dt))
                                      E0
                                      (State stm' nil vars' (Callframe stl vars vres :: stack) (Global global  dt))                               

(** array index *)
        | step_arrayindex : forall vars source obj ar i class hp,
          vars ! source = Some (Val (Value.ptr (@Value.subobject _ obj ar i Class.Inheritance.Repeated (class :: nil) hp))) (** must be a most derived object *) ->
        forall o global n,
          (Globals.heap global) ! obj = Some o ->
          valid_array_path hierarchy class n  (Object.class o) (Object.arraysize o) ar ->
          0 <= i < n ->
          forall index tyj vaj, vars ! index = Some (Val (Value.atom tyj vaj)) ->
            forall j,
              semZ sem vaj = Some j ->
              0 <= i + j < n ->
              forall vars' target,
                vars' = PTree.set target (Val (Value.ptr (Value.subobject obj ar (i + j) Class.Inheritance.Repeated _ hp))) vars ->
                  forall stl stack dt ,
                    step
                    (State (arrayindex class index source target) stl vars stack (Global global  dt))
                    E0
                    (State skip stl vars' stack (Global global  dt))

        (* Construction-specific *)
        | step_pathop : forall ovar oval vars,
          match ovar with
            | None => oval = None
            | Some var => exists val, vars ! var = Some val /\ oval = Some val 
          end ->
          forall pop val',
            path_operation_sem hierarchy pop oval val' ->
            forall vars' target,
              vars' = PTree.set target val' vars ->
                forall stl stack global,
                  step
                  (State (pathop pop ovar target) stl vars stack global)
                  E0
                  (State skip stl vars' stack global)

        | step_setdyntype : forall vars vptr obj ar i h p hp,
          vars ! vptr = Some (Val (Value.ptr (Value.subobject obj ar i h p hp))) ->
          forall o gl,
            (Globals.heap gl) ! obj = Some o ->
            forall real from,
              valid_relative_pointer hierarchy (Object.class o) (Object.arraysize o) ar real i h p from ->
              forall vpath, vars ! vpath = Some (Path real h p) -> (* pointer and path must match *)
                forall dt dt', set_dynamic_type (hierarchy) obj ar i h p (erase_non_primary_ancestor_dynamic_type obj ar i h p is_primary_path dt) dt' ->
                  forall ismostderived_flag,
                    (ismostderived_flag = true -> (
                      (h, p) = (Class.Inheritance.Repeated, from :: nil) \/ (forall b, is_virtual_base_of hierarchy b from -> False)
                    )) ->
                    forall  stl stack,
                      step
                      (State (setdyntype ismostderived_flag from vptr vpath) stl vars stack (Global gl  dt))
                      E0
                      (State skip stl vars stack (Global gl  dt'))

        | step_casttobase : forall vars vptr obj ar i h p hp,
          vars ! vptr = Some (Val (Value.ptr (Value.subobject obj ar i h p hp))) ->
          forall global,
          valid_pointer hierarchy (Globals.heap global) (@Value.subobject _ obj ar i h p hp) ->      
          forall from, last p = Some from ->
            forall kind b h' p',
              match kind with
                | Class.Inheritance.Shared => is_virtual_base_of hierarchy b from /\ h = Class.Inheritance.Repeated /\ p = from :: nil /\ h' = Class.Inheritance.Shared /\ p' = b :: nil
                | Class.Inheritance.Repeated => h' = h /\ p' = p ++ b :: nil /\ exists c, hierarchy ! from = Some c /\ In (Class.Inheritance.Repeated, b) (Class.super c)
              end ->
              forall hp' vars' target, vars' = PTree.set target (Val (Value.ptr (Value.subobject obj ar i h' p' hp'))) vars ->
                forall dt stl  stack,
                  step
                  (State (casttobase vptr from kind b target) stl vars stack (Global global  dt))
                  E0
                  (State skip stl vars' stack (Global global  dt))

.
            
            

    End Sem.

    End Source.


