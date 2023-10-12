Require Import LibLists.
Require Import Cplusconcepts.
Require Import Coqlib.
Require Import Tactics.
Require Import LibMaps.
Require Import LibPos.
Load Param.


(** A class is dynamic if, and only if, one of the following conditions holds:
   - it has a virtual method
   - it has a direct virtual base
   - it has a direct dynamic base

This definition is common to both algorithms studied in POPL 2011, Section 6. Moreover, it is formalized in the C++ Standard (since 1999) as "to have a polymorphic behaviour".
 However, it plays no role in the correctness of conditions stated in Section 4 and proved in Section 5.
 *)

Section DYN.


Variable A : ATOM.t.

Variable hierarchy : PTree.t (Class.t A).

Inductive is_dynamic : ident -> Prop :=
| is_dynamic_virtual_methods : forall i c
  (H_i_c     : hierarchy ! i = Some c)
  (H_methods : exists m, In m (Class.methods c) /\ Method.virtual m = true),
    is_dynamic i
| is_dynamic_direct_virtual_base : forall i c
  (H_i_c : hierarchy ! i = Some c)
  b
  (Hb    : In (Class.Inheritance.Shared, b) (Class.super c)),
  is_dynamic i
| is_dynamic_base : forall i c
  (H_i_c          : hierarchy ! i = Some c)
  h b
  (H_h_b          : In (h, b) (Class.super c))
  (H_is_dynamic_b : is_dynamic b),
  is_dynamic i
.

Lemma is_dynamic_virtual_base : forall i b,
  is_virtual_base_of hierarchy b i ->
  is_dynamic i.
Proof.
  induction 1.
  eauto using is_dynamic_direct_virtual_base.
  eauto using is_dynamic_base.
Qed.

Lemma is_dynamic_path : forall to via from by
  (Hpath : path hierarchy to via from by)
  (H_dyn_to : is_dynamic to),
  is_dynamic from.
Proof.
  intros.
  generalize (path_path2 Hpath).
  clear Hpath.
  intro Hpath.
  revert H_dyn_to.
  induction Hpath ; intros ; eauto 10 using is_dynamic_base.
Qed.   

Lemma method_dispatch_dynamic : forall ms cn ccn dh dp mh mp,
  method_dispatch hierarchy ms cn ccn dh dp mh mp -> (* mh, mp is the path from the dynamic cc to the dispatched method *)
  is_dynamic cn.
Proof.
 inversion 1; subst.
 eapply is_dynamic_path.
 eassumption.
 eapply is_dynamic_virtual_methods.
 eassumption.
 generalize (Method.find_in H2).
 eauto.
Qed.

End DYN.
