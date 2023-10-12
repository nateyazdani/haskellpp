Require Import BuiltinTypes.
Require Import Coqlib.
Require Import LibLists.
Require Import Tactics.
Require Import LibMaps.
Require Import Relations.
Require Import Events.
Require Memory.
Load Param.
Open Scope Z_scope.

Notation var := (positive) (only parsing).

Section Target.

Variable (A : ATOM.t).

Variable nativeop : Type.

Variable sem : semparam A nativeop.

Record romtypes : Type := ROMTypes {
  InitVTT : Type;
  SubVTT : Type;
  VTTAccess : Type;
  VTableAccess : Type;
  VtblPath : Type;
  VBase : Type;
  DCast : Type;
  Dispatch : Type;
  PVTT : Type;
  PVTable : Type
}.

Variable romty : romtypes.

Inductive ROMop : Type :=
| initVTT (_ : InitVTT romty)
| subVTT (_ : VTTAccess romty) (_ : SubVTT romty)
| vtable (_ : VTTAccess romty) (_ : VtblPath romty)
| vbase_offset  (_ : VTableAccess romty) (_ : VBase romty)
| dyncast_exists (_ : DCast romty)
| dyncast_offset (_ : DCast romty)
| dispatch_function (_ : VTableAccess romty) (_ : Dispatch romty)
| dispatch_offset (_ : VTableAccess romty) (_ : Dispatch romty)
.

Inductive calltype : Type := Static | Dynamic.

      Inductive stmt : Type :=
      | skip
      | seq (_ _ : stmt)
      | test (test : var) (ifso ifnot : stmt)
      | block (object : option (var * Z)) (body : stmt)
      | exit (n : nat) (** block/exit, cf. Compcert Cminor *)
      | loop (body : stmt)
      | native (op : nativeop ) (source : list var) (target : option var)
      | ret (_ : option var)
      | move (src tgt : var)

      (** function invocation *)
      | call (_ : calltype) (_ : positive) (vargs : list var) (vres : option var)
      | thunkcall (this : var) (_ : VTableAccess romty) (_ : Dispatch romty) (vargs : list var) (vres : option var) (** thunks *)

      (** low-level memory operations *)
      | load (chunksize : Z) (ptr : var) (off : Z) (target : var) (** load/store at ptr+off, where off is constant *)
      | store (chunksize : Z) (ptr : var) (off : Z) (newvalue : var)

      (** pointer arith *)
      | null (ptr' : var) (** create a null pointer *)
      | ptrshift (ptr : var) (off : Z) (ptr' : var) (** compute ptr+off, where off is constant *)
      | ptrshiftmult (ptr : var) (delta : var) (factor : Z) (ptr' : var) (** compute ptr + delta*factor, where delta is variable, and factor is constant *)
      | ptreq (ptr1 ptr2 : var) (target : var) (** equality of two low-level pointers *)

      (** ROM operations *)
      | romop (vptr : option var) (rop : ROMop) (res : var) 

.

      Record func : Type := Func {
        vargs : list var;
        body : stmt
      }.


      (** * Virtual tables and VTTs. *)
            
      Record vTable : Type := VTable {
        vboff : list (VBase romty * Z);
        dyncast : list (DCast romty * (* option *) Z);
        dispfunc : list (Dispatch romty * positive);
        dispoff : list (Dispatch romty * Z)
      }.
      
      Record vTT : Type := VTT {
        subvtt : list (SubVTT romty * PVTT romty);
        pvtable : list (VtblPath romty * PVTable romty)
      }.
      
      Notation "( 'EqDec' ty )" := (forall a1 a2 : ty, {a1 = a2} + {a1 <> a2}) (only parsing). 
      
      Record romopsemparam : Type := ROMopsemparam {
        initvtt : list (InitVTT romty * PVTT romty);
        InitVTT_eq_dec : (EqDec (InitVTT romty));
        vtt : list (PVTT romty * (vTT));
        PVTT_eq_dec : (EqDec (PVTT romty));
        SubVTT_eq_dec : (EqDec (SubVTT romty));
        VtblPath_eq_dec : (EqDec (VtblPath romty));
        vtables : list (PVTable romty * vTable);
        PVTable_eq_dec : (EqDec (PVTable romty));
        VBase_eq_dec : (EqDec (VBase romty));
        DCast_eq_dec : (EqDec (DCast romty));
        Dispatch_eq_dec : (EqDec (Dispatch romty));
        vtable_access : PVTable romty -> option (VTableAccess romty);
        vtable_access_sharing : VTableAccess romty -> option (VTableAccess romty);
        vtable_access_vbase : VTableAccess romty -> list (VBase romty);
        vtable_access_dispatch : VTableAccess romty -> list (Dispatch romty);
        vtt_access : PVTT romty -> option (VTTAccess romty)
      }.

      Section Vtable_access.
        Variable vtable_access_sharing : VTableAccess romty -> option (VTableAccess romty).

        Definition vtable_access_prec (a b : VTableAccess romty) :=
          vtable_access_sharing b = Some a.

        Definition vtable_access_lt := clos_trans _ vtable_access_prec.

        Definition vtable_access_le := clos_refl_trans _ vtable_access_prec.
      End Vtable_access.

      Record program : Type := Program {
        funcs : PTree.t func;
        main : stmt;
        rom : romopsemparam;
        vtable_access_wf : well_founded (vtable_access_lt (vtable_access_sharing rom))
      }.

      Section Sem.

Variable mblock : Type.

Inductive val : Type :=
| Ptr (_ : option (mblock * Z)) (** pointer (None : null pointer) *)
| Fptr (_ : positive) (** pointer to function *)
| Vptr (_ : PVTable romty) (** pointer to VTable *)
| VTTptr (_ : PVTT romty) (** pointer to VTT *)
| Atom (ty : (ATOM.ty A)) (_ : (ATOM.val (t := A)) ty) (** atomic value *)
  .
  
(** * Language semantics *)

Inductive valtype : Type :=
| tyAtom (_ : ATOM.ty A)
| tyPtr
| tyFptr
| tyVptr
| tyVTTptr
.

Function type_of_value (v : val) : valtype :=
  match v with
    | Atom ty _ => (tyAtom ty)
    | Ptr _ => tyPtr
    | Fptr _ => tyFptr
    | Vptr _ => tyVptr
    | VTTptr _ => tyVTTptr
  end.

Definition typedata (A : Type) := valtype -> A.

Definition valdata (B : Type) (tyd : typedata B) (v : val) :=
  tyd (type_of_value v).

Inductive datakind : Type :=
| Size
| Align.

Definition valop' (A : Type) := datakind -> valtype -> A.

Variable vop' : valop' Z.

Definition valop := Memory.Valop (valdata (vop' Size)) (valdata (vop' Align)).

        Variables memblocks memvalues : Type.

        Variable memop : Memory.op val memblocks memvalues mblock.

        Inductive frame : Type := 
        | Block (bobject : option mblock) (bstmt : list stmt)
        | Callframe (ffurther : list stmt) (fvars : PTree.t val) (fret : option var)
          .

        Record mem : Type := Mem {
          mblocks : memblocks;
          mvalues : memvalues
        }.

        Record state : Type := State {
          current : stmt;
          further : list stmt;
          vars : PTree.t val;
          stack : list frame;          
          memory : mem
        }.

        Variable prog : program.

        Notation romopsem := (rom prog) (only parsing).

Inductive ROMopsem : option val -> ROMop -> val -> Prop :=
| ROMopsem_initVTT: forall iv pv,
  assoc (InitVTT_eq_dec romopsem) iv (initvtt romopsem) = Some pv ->
  ROMopsem None (initVTT iv) (VTTptr pv)

| ROMopsem_subVTT : forall pv v,
  assoc (PVTT_eq_dec romopsem) pv (vtt romopsem) = Some v ->
  forall sv pv',
    assoc (SubVTT_eq_dec romopsem) sv (subvtt v) = Some pv' ->
    forall va, vtt_access romopsem pv = Some va ->
    ROMopsem (Some (VTTptr pv)) (subVTT va sv) (VTTptr pv')

| ROMopsem_vtable : forall pv vt,
  assoc (PVTT_eq_dec romopsem) pv (vtt romopsem) = Some vt ->
  forall vp v,
    assoc (VtblPath_eq_dec romopsem) vp (pvtable vt) = Some v ->
    forall va, vtt_access romopsem pv = Some va ->
    ROMopsem (Some (VTTptr pv)) (vtable va vp) (Vptr v)

| ROMopsem_vboff : forall pv v,
  assoc (PVTable_eq_dec romopsem) pv (vtables romopsem) = Some v ->
  forall vb off, assoc (VBase_eq_dec romopsem) vb (vboff v) = Some off ->
    forall ty va, Zsem sem off = existT _ ty va ->
      forall vta0, vtable_access romopsem pv = Some vta0 ->
        forall vta, vtable_access_le (vtable_access_sharing romopsem) vta vta0 ->
          In vb (vtable_access_vbase romopsem vta) ->
          ROMopsem (Some (Vptr pv)) (vbase_offset vta vb) (Atom va)

| ROMopsem_dyncast_exists : forall pv v,
  assoc (PVTable_eq_dec romopsem) pv (vtables romopsem) = Some v ->
  forall dc ato, ato = match assoc (DCast_eq_dec romopsem) dc (dyncast v) with
                         | Some _ => Atom (TRUE sem)
                         | _ => Atom (FALSE sem)
                       end ->
  ROMopsem (Some (Vptr pv)) (dyncast_exists dc) ato

| ROMopsem_dyncast_offset : forall pv v,
  assoc (PVTable_eq_dec romopsem) pv (vtables romopsem) = Some v ->
  forall dc off, assoc (DCast_eq_dec romopsem) dc (dyncast v) = Some off ->
    forall ty va, Zsem sem off = existT _ ty va ->
      ROMopsem (Some (Vptr pv)) (dyncast_offset dc) (Atom va)

| ROMopsem_dispatch_function : forall pv v,
  assoc (PVTable_eq_dec romopsem) pv (vtables romopsem) = Some v ->
  forall df id, assoc (Dispatch_eq_dec romopsem) df (dispfunc v) = Some id ->
    forall vta0, vtable_access romopsem pv = Some vta0 ->
      forall vta, vtable_access_le (vtable_access_sharing romopsem) vta vta0 ->
        In df (vtable_access_dispatch romopsem vta) ->
        ROMopsem (Some (Vptr pv)) (dispatch_function vta df) (Fptr id)

| ROMopsem_dispatch_offset : forall pv v,
  assoc (PVTable_eq_dec romopsem) pv (vtables romopsem) = Some v ->
  forall df off, assoc (Dispatch_eq_dec romopsem) df (dispoff v) = Some off ->
    forall vta0, vtable_access romopsem pv = Some vta0 ->
      forall vta, vtable_access_le (vtable_access_sharing romopsem) vta vta0 ->
        In df (vtable_access_dispatch romopsem vta) ->
        forall ty va, Zsem sem off = existT _ ty va ->        
          ROMopsem (Some (Vptr pv)) (dispatch_offset vta df) (Atom va)
.

        Inductive initial_state : state -> Prop :=
        | initial_state_intro :
          initial_state (State (main prog) nil (PTree.empty _) nil (Mem (Memory.initmembl memop) (Memory.initmemval memop)))
            .

        Inductive final_state : state -> outcome (evtr sem) -> Prop :=
        | final_state_intro : forall vars v ty va,
          vars ! v = Some (Atom va) ->
          forall res, 
          outcome_sem (ty := ty) va res ->
          forall stl mem,
          final_state (State (ret (Some v)) stl vars nil mem) res
          .

        Function set_params (vl: list val) (il: list var) {struct il} : PTree.t (val) :=
          match il, vl with
            | i1 :: is, v1 :: vs => PTree.set i1 v1 (set_params vs is)
            | _, _ => PTree.empty (val)
          end.

        Function exit_succ (s : stmt) : option stmt :=
          match s with
            | ret ov => Some (ret ov)
            | exit (S n) => Some (exit n)
            | _ => None
          end.

        Record targetsemparam : Type := Targetsem {
          allow_function_pointers : bool;
          allow_thunk_call : bool
        }.

        Variable targetsem : targetsemparam.

        Inductive step : state -> trace (evtr sem) -> state -> Prop :=

        | step_skip : forall stm stl vars stack m,
          step
          (State skip (stm :: stl) vars stack m)
          E0
          (State stm stl vars stack m)

        | step_seq : forall stl s1 s2 vars stack m,
          step
          (State (seq s1 s2) stl vars stack m)
          E0
          (State s1 (s2 :: stl) vars stack m)

        | step_loop : forall stl stm vars stack m,
          step
          (State (loop stm) stl vars stack m)
          E0
          (State stm (loop stm :: stl) vars stack m)

        | step_test : forall vars varb tyb valb,
          vars ! varb = Some (@Atom tyb valb) ->
          forall b, sembool sem valb = Some b ->
            forall s ifso ifnot, s = (if b then ifso else ifnot) ->
              forall stl stack global,
                step
                (State (test varb ifso ifnot) stl vars stack global)
                E0
                (State s stl vars stack global)
                
        | step_block_none : forall stm stl vars stack global,
          step
          (State (block None stm) stl vars stack global)
          E0
          (State stm nil vars (Block None stl :: stack) global)
          
        | step_block_some : forall memb sz p memb',
          Memory.alloc memop memb sz = (p, memb') ->
          forall vars v vars',
            vars' = PTree.set v (Ptr (Some (p, 0))) vars ->
              forall stm stl stack memv,
                step
                (State (block (Some (v, sz)) stm) stl vars stack (Mem memb memv))
                E0
                (State stm nil vars' (Block (Some p) stl :: stack) (Mem memb' memv))

        | step_exit_O : forall stl vars stack global,
          step
          (State (exit O) stl vars stack global)
          E0
          (State (skip) stl vars stack global)          

        | step_exit_S_return_cons : forall ob memb memb',
          memb' = match ob with
                    | Some b => Memory.free memop memb b
                    | _ => memb
                  end ->
          forall stm stm', exit_succ stm = Some stm' ->
            forall stl stl' vars stack memv,
              step
              (State stm stl vars (Block ob stl' :: stack) (Mem memb memv))
              E0
        (State stm' stl' vars stack (Mem memb' memv))        
        
        | step_return_nil : forall orv ov vars vars'' vars' ,
          match orv with
            | None => ov = None /\ vars'' = vars'
            | Some rv => exists v, ov = Some v /\ exists val, vars ! v = Some val /\ vars'' = PTree.set rv val vars'
          end ->
          forall global  stl stl' vars stack,
            step
            (State (ret ov) stl vars (Callframe stl'  vars' orv :: stack) global)
            E0
            (State skip stl' vars'' stack global)            

        | step_native :
          forall args source vars,
            map (fun a : sigT (ATOM.val (t := A)) => let (ty, va) := a in Some (Atom va)) args =         
            map (fun v => PTree.get v vars) source ->
            forall op ov  t,
              nativeop_sem op args ov t ->
              forall target vars',
                match ov with
                  | None => target = None /\ vars' = vars
                  | Some (existT rty rva) => exists tarv, target = Some tarv /\ vars' = PTree.set tarv (Atom rva) vars
                end ->
                forall stl stack global,
                  step
                  (State (native op source target) stl vars stack global)
                  t
                  (State skip stl vars' stack global)

      | step_move :
        forall vars src v, 
          vars ! src = Some v ->
          forall tgt vars', vars' = PTree.set tgt v vars ->
            forall stl vars stack global,
              step
              (State (move src tgt) stl vars stack global)
              E0
              (State skip stl vars' stack global)

      | step_call : forall id fid vars kind,
        match kind with
          | Static => fid = id
          | Dynamic => vars ! id = Some (Fptr fid) /\ allow_function_pointers targetsem = true
        end ->
        forall vargs' stm', (funcs prog) ! fid = Some (Func vargs' stm') ->
          forall args vargs,  
            map (@Some _) args = map (fun v => vars ! v) vargs ->
            forall vars',
              vars' = set_params args vargs' ->
              forall global vret stl stack,
                  step
                  (State (call kind id vargs vret) stl vars stack global)
                  E0
                  (State stm' nil vars' (Callframe stl vars vret :: stack) global)

      | step_thunkcall : 
        allow_thunk_call targetsem = true ->
        forall vars this b o,
          vars ! this = Some (Ptr (Some (b, o))) ->
          forall memb memv vptr,
            Memory.load memop (vop' Size tyVptr) memb memv (b, o) = Some (Vptr vptr) ->
              forall vtbl,
                assoc (PVTable_eq_dec romopsem) vptr (vtables romopsem) = Some vtbl ->
                forall disp fid, assoc (Dispatch_eq_dec romopsem) disp (dispfunc vtbl) = Some fid ->
                  forall off, assoc (Dispatch_eq_dec romopsem) disp (dispoff vtbl) = Some off ->                    
                    forall vargs' stm', (funcs prog) ! fid = Some (Func vargs' stm') ->
                      forall va0, vtable_access romopsem vptr = Some va0 ->
                        forall va,
                          vtable_access_le (vtable_access_sharing romopsem) va va0 ->
                          In disp (vtable_access_dispatch romopsem va) ->
                          forall args vars vargs,  
                            map (@Some _) args = map (fun v => vars ! v) vargs ->
                            forall vars',
                              vars' = set_params (Ptr (Some (b, o + off)) :: args) (vargs') ->
                              forall stl stack vret,
                                step
                                (State (thunkcall this va disp vargs vret) stl vars stack (Mem memb memv))
                                E0
                                (State stm' nil vars' (Callframe stl vars vret :: stack) (Mem memb memv))


        (** low-level memory load *)
      | step_load : forall ptr b z vars,
        vars ! ptr = Some (Ptr (Some (b, z))) ->
        forall sz memb memv off v,
          Memory.load memop sz memb memv (b, z + off) = Some v ->
          forall target vars', vars' = PTree.set target v vars ->
            forall stl stack,
              step
              (State (load sz ptr off target) stl vars stack (Mem memb memv))
              E0
              (State skip stl vars' stack (Mem memb memv))

        (** low-level memory store *)
      | step_store : forall ptr b z vars,
        vars ! ptr = Some (Ptr (Some (b, z))) ->
        forall newvalue v,
          vars ! newvalue = Some v ->
          forall sz, sz = Memory.valsize valop v ->
            forall memb memv memv' off,
              Memory.store memop sz memb memv (b, z + off) v = Some memv' ->
              forall stl stack,
                step
                (State (store sz ptr off newvalue) stl vars stack (Mem memb memv))
                E0
                (State skip stl vars stack (Mem memb memv'))
                
        (** null pointer *)
      | step_null : forall vars vars' target,
        vars' = PTree.set target  (Ptr None) vars ->
          forall stl stack m,
            step
            (State (null target) stl vars stack m)
            E0
            (State skip stl vars' stack m)
 
        (** constant shift *)
      | step_ptrshift : forall b z vars ptr,
        vars ! ptr = Some ((Ptr (Some (b,z)))) ->
        forall off vars' target,
          vars' = PTree.set target ((Ptr (Some (b, z + off)))) vars ->
            forall stl stack m,
              step
              (State (ptrshift ptr off target) stl vars stack m)
              E0
              (State skip stl vars' stack m)

        (** variable shift (up to a constant factor) *)
      | step_ptrshiftmult : forall b z vars ptr,
        vars ! ptr = Some ((Ptr (Some (b, z)))) ->
        forall delta tyoff vaoff,
          vars ! delta = Some ( (@Atom tyoff vaoff)) ->
          forall off, semZ sem vaoff = Some off ->
            forall factor vars' target,
              vars' = PTree.set target ( (Ptr (Some (b, z + off * factor)))) vars ->
                forall stl stack m,
                  step
                  (State (ptrshiftmult ptr delta factor target) stl vars stack m)
                  E0
                  (State skip stl  vars' stack m)

      | step_ptreq : forall ptr1 oz1 vars,
        vars ! ptr1 = Some ((Ptr oz1)) ->
        forall ptr2 oz2, vars ! ptr2 = Some ((Ptr oz2)) ->
          forall b : bool,
            (if b then (oz1 = oz2) else (oz1 <> oz2)) ->
            forall v, v = (if b then (Atom (TRUE sem)) else  (Atom (FALSE sem))) ->
              forall vars' target, vars' = PTree.set target v vars ->
                forall stl  stack m,
                  step
                  (State (ptreq ptr1 ptr2 target) stl  vars stack m)
                  E0
                  (State skip stl  vars' stack m)

      | step_romop :
        forall vars ovptr ov,
          match ovptr with
            | Some vptr => exists v, vars ! vptr = Some v /\ ov = Some v
            | None => ov = None
          end ->
          forall ro res,
            ROMopsem ov ro res ->
            forall vars' vres, vars' = PTree.set vres res vars ->
              forall stl  stack m,
                step
                (State (romop ovptr ro vres) stl  vars stack m)
                E0
                (State skip stl  vars' stack m)
                .

    End Sem.

End Target.
