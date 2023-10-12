Require Import LibLists.
Require Import Cplusconcepts.
Require Import CplusWf.
Require Import Coqlib.
Require Import Tactics.
Require Import LibMaps.
Require Import LibPos.
Require Import Dynamic.
Load Param.

Section DYN.

Variable A : ATOM.t.

Variable hierarchy : PTree.t (Class.t A).

Hypothesis hierarchy_wf : Well_formed_hierarchy.prop hierarchy.

Lemma is_dynamic_dec : forall i, {is_dynamic hierarchy i} + {~ is_dynamic hierarchy i}.
Proof.
 induction i using  (well_founded_induction Plt_wf).
 rename H into IHi.
 case_eq (hierarchy ! i).
  intros c Hc.
  case_eq (List.filter (Method.virtual (A := A)) (Class.methods c)).
   intros H_no_methods.
   pose (f := (fun (x : _ * ident) => match x with (Class.Inheritance.Shared, _) => true | _ => false end)).
   case_eq (List.filter f (Class.super c)).
    intros H_no_direct_virtual_bases.
    generalize (Well_formed_hierarchy.well_founded hierarchy_wf Hc).
    intros Hlt.
    generalize (fun (hc : _ * _) Hc => 
      match hc as hc' return In hc' (Class.super c) -> Plt (let (_, cisuper) := hc' in cisuper) _ with
        | pair h cisuper => fun Hin => Hlt h cisuper Hin
      end Hc
    ).
    intro Hlt'.
    generalize (tag_list Hlt').
    intros [l' Hl'].
    pose (g := fun (x : sigT (fun hc : (Class.Inheritance.t * _) => Plt (let (h, cisuper) := hc in cisuper) i)) =>
      match x with
        | existT hc hlt =>
          match hc as hc' return (Plt (let (_, cisuper) := hc' in cisuper) i -> bool) with
            | (h, cisuper) => fun hlt' => if IHi cisuper hlt' then true else false
          end hlt
      end
    ).          
    case_eq (filter g l').

     intro H_no_dynamic_bases.
     right.
     intro Habs.
     inversion Habs ; try congruence.
      subst i0.
      destruct H_methods.
      destruct H.
      generalize (filter_In (Method.virtual (A := A)) x (Class.methods c)).
      rewrite H_no_methods.
      simpl.
      replace c0 with c in * by congruence.
      tauto.
      subst i0.
      replace c0 with c in * by congruence.
      generalize (filter_In f (Class.Inheritance.Shared, b) (Class.super c)).
      intros [_ Hin].
      simpl in Hin.
      generalize (Hin (conj Hb (refl_equal _))).
      rewrite H_no_direct_virtual_bases.
      tauto.
     subst i0.
     replace c0 with c in * by congruence.
     generalize (Hl' (h, b)).
     intros [Hin_l' _].
     generalize (Hin_l' H_h_b).
     intros [p Hp].     
     assert (g (existT _ (h, b) p) = true) as Hg.
      simpl.
      destruct (IHi b p).
       trivial.
       contradiction.      
      generalize (filter_In g (existT _ (h, b) p) l').
      intros [_ Hin].
      generalize (Hin (conj Hp Hg)).
      rewrite H_no_dynamic_bases.
      tauto.

     intros s l Hs.
     assert (In s (filter g l')) as Hin_g.
      rewrite Hs.
      simpl. tauto.
     generalize (filter_In g s l').
     intros [Hin_g_l' _].
     generalize (Hin_g_l' Hin_g).
     intros [Hin_l' Hg].
     destruct s as [h p].
     generalize (Hl' h).
     intros [_ Hin_super].
     generalize (Hin_super (ex_intro _ p Hin_l')).
     intros.
     destruct h.
     simpl in Hg.
     left.
      eapply is_dynamic_base.
      eassumption.
      eassumption.
      destruct (IHi p0 p).
      assumption.
      congruence.

    intros h l Hh.
    assert (In h (filter f (Class.super c))) as Hin_f.
     rewrite Hh.
     simpl. tauto.
    generalize (filter_In f h (Class.super c)).
    intros [Hin_h _].
    generalize (Hin_h Hin_f).
    intros [? Hf].
    destruct h as [t ?].
    simpl in Hf.
    destruct t ; try congruence.
    left.
    eapply is_dynamic_direct_virtual_base.
    eassumption.
    eassumption.
   
  intros.
  left.
  eapply is_dynamic_virtual_methods.
  eassumption.
  exists t.
  generalize (filter_In (Method.virtual (A := A)) t (Class.methods c)).
  rewrite H.
  simpl.
  tauto.

  intros.
  right.
  intro Habs.
  inversion Habs ; congruence.

Qed.

End DYN.