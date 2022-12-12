Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Adjunctions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.


Local Open Scope cat.

Section Aux.

  Context {C : category} {D : disp_cat C}.

  Definition disp_mor_up_to_eq
             {x1 x2 y1 y2 : C}
             {f : C⟦x1,y1⟧}
             (py : y1 = y2)
             (px : x2 = x1)
             {g : C⟦x2,y2⟧}
             {xx1 : D x1} {xx2 : D x2} {yy1 : D y1} {yy2 : D y2}
             (q : idtoiso px · f · idtoiso py = g)
             (ff : xx1 -->[f] yy1)
             (ppy : yy1 = transportb _ py yy2)
             (ppx : xx1 = transportf _ px xx2)
    : xx2 -->[g] yy2.
  Proof.
    induction q.
    use comp_disp.
    2: {
      use comp_disp.
      3: exact ff.
      induction (! ppx).
      induction px.
      apply id_disp.
    }
    induction (! ppy).
    induction py.
    apply id_disp.
  Defined.

  Definition disp_mor_up_to_eq_r {x y1 y2 : C}
             {f : C⟦x,y1⟧} (p : y1 = y2)
             {g : C⟦x,y2⟧}
             {xx : D x} {yy1 : D y1} {yy2 : D y2}
             (q : f · idtoiso p = g)
             (ff : xx -->[f] yy1)
             (pp : yy1 = transportb _ p yy2)
    : xx -->[g] yy2.
  Proof.

    assert (px : idtoiso (idpath x) · f · idtoiso p = g).
    {
      rewrite assoc'.
      rewrite q.
      apply id_left.
    }

    use (disp_mor_up_to_eq p (idpath _) px ff).
    - exact pp.
    - apply idpath.
  Defined.

  Definition disp_mor_up_to_eq_l {x1 x2 y : C}
             {f : C⟦x1,y⟧} (p : x2 = x1)
             {g : C⟦x2,y⟧}
             {xx1 : D x1} {xx2 : D x2} {yy : D y}
             (q : idtoiso p · f = g)
             (ff : xx1 -->[f] yy)
             (pp : xx1 = transportf _ p xx2)
    : xx2 -->[g] yy.
  Proof.

    assert (px : idtoiso p · f · idtoiso (idpath _) = g).
    {
      rewrite q.
      apply id_right.
    }

    use (disp_mor_up_to_eq (idpath _) p px ff).
    - apply idpath.
    - exact pp.
  Defined.

End Aux.

Section FF_SPLITESO_TO_EQUIV_OVER.

  Context {C1 C2 : category} (F : adj_equiv C1 C2)
          {D1 : disp_cat C1} {D2 : disp_cat C2}
          {FF : disp_functor (left_functor F) D1 D2}
          (FF_split : disp_functor_disp_ess_split_surj FF)
          (FF_ff : disp_functor_ff FF)
          (C1_univ : is_univalent C1)
          (C2_univ : is_univalent C2)
          (D1_univ : is_univalent_disp D1)
          (D2_univ : is_univalent_disp D2).

  Let L := pr1 F : functor C1 C2.
  Let R := pr112 F : functor C2 C1.
  Let η := adjunit F.
  Let ε := adjcounit F.

  Let ηiso := pr122 F.
  Let εiso := pr222 F.

  (* Definition D1_iso_cleaving
    : Fibrations.iso_cleaving D1
    := Fibrations.iso_cleaving_category C1 C1_univ D1. *)
  Definition D2_iso_cleaving
    : iso_cleaving D2
    := iso_cleaving_category C2 C2_univ D2.

  Definition rad_ob {x : C2} (xx : D2 x) : D1 (R x).
  Proof.
    set (i := _ ,, εiso x : z_iso (F (R x)) x).
    set (xx' := pr1 (D2_iso_cleaving x (F (R x)) i xx) : D2 (F (R x))).
    exact (pr1 (FF_split (R x) xx')).
  Defined.

  Lemma TODO_JOKER (A : UU) : A. Proof. Admitted.



  Definition rad_unit_ob {x : C1} (xx : D1 x)
    : xx -->[η x] rad_ob (FF x xx).
  Proof.
    set (i := FF_ff x (R (L x)) xx (rad_ob (FF x xx)) (η x)).
    set (w := _ ,, i).
    use (pr1weq (invweq w)).
    cbn.
    (* set (g := (# F)%Cat (unit_from_are_adjoints F x)).
    cbn in g.
    assert (g = (#L)%Cat (η x)).
    {
      apply idpath.
    } *)

    set (ik := z_iso_inv (functor_on_z_iso F (_ ,, ηiso x))).
    cbn in ik.
    set (j := D2_iso_cleaving _ _ ik (FF x xx)).
    set (jj := Isos.z_iso_inv_from_z_iso_disp (pr2 j)).
    assert (q : pr1 j = FF (R (L x)) (rad_ob (FF x xx))).
    {

      admit.
    }

    set (p := z_iso_inv_z_iso_inv _ _ (functor_on_z_iso F (_ ,, ηiso x))).
    assert (pp : z_iso_inv_from_z_iso ik · idtoiso (idpath (F ((pr112 F) (pr1 F x)))) =
                   # F (unit_from_are_adjoints F x)).
    {
      etrans. { apply id_right. }
      exact (base_paths _ _ p).
    }

    use (@disp_mor_up_to_eq_r C2 D2 (L x) (L (R (L x))) (F ((pr112 F) (pr1 F x)))).
    5: exact (pr1 jj).
    - apply idpath.
    - exact (pp).
    - exact q.

      (** The code below would work if we assume that C1 and D1 are univalent **)
    (* set (i := z_iso_inv (_ ,, ηiso x)).
    set (j := D1_iso_cleaving x (R (L x)) i xx).
    set (jj := Isos.z_iso_inv_from_z_iso_disp (pr2 j)).
    assert (p : pr1 j = rad_ob (FF x xx)).
    {
      apply TODO_JOKER.
    }
    induction p.
    exact (pr1 jj). *)
  Admitted.

  Definition rad_unit_inv_ob {x : C1} (xx : D1 x)
    : rad_ob (FF x xx) -->[pr1 (ηiso x)] xx.
  Proof.
    set (i := FF_ff (R (L x)) x (rad_ob (FF x xx)) xx (pr1 (ηiso x))).
    set (w := _ ,, i).
    use (pr1weq (invweq w)).
    cbn.

    use (@disp_mor_up_to_eq_l C2 D2).
    6:

    use (@disp_mor_up_to_eq_l C2 D2 (L (R (L x))) (L x)).

  (* set (i := _ ,, ηiso x : z_iso x (R (L x))).
    set (ii := z_iso_inv i).
    set (j := D1_iso_cleaving x (R (L x)) ii xx).

    assert (p : pr1 j = rad_ob (FF x xx)).
    {
      apply TODO_JOKER.
    }
    induction p.
    exact (pr12 j).
  Defined. *)
  Admitted.

  Definition rad_unit_z_iso {x : C1} (xx : D1 x)
    : Isos.is_z_iso_disp (adjunitiso F x) (rad_unit_ob xx).
  Proof.
    exists (rad_unit_inv_ob xx).
    split.
    - cbn.
      unfold disp_functor_ff in FF_ff.
      Check  (rad_unit_inv_ob xx ;; rad_unit_ob xx)%mor_disp.
      set (p := FF_ff _ _ (rad_ob  (FF x xx)) (rad_ob (FF x xx))).

      (* use (isweqonpathsincl _ _ _ (isinclweq _ _ _ (p _))). *)


  Admitted.

  Definition rad_counit_ob
             {x : C2} (xx : D2 x)
    : FF (R x) (rad_ob xx) -->[ε x] xx.
  Proof.
    set (i := _ ,, εiso x : z_iso (F (R x)) x).
    set (j := D2_iso_cleaving x (F (R x)) i xx).
    cbn in j.
    assert (p : pr1 j = FF (R x) (rad_ob xx)).
    {
      admit.
    }
    induction p.
    exact (pr12 j).
  Admitted.

  Definition rad_counit_inv_ob
             {x : C2} (xx : D2 x)
    : xx -->[pr1 (εiso x)] FF (R x) (rad_ob xx).
  Proof.
    set (i := _ ,, εiso x : z_iso (F (R x)) x).
    set (j := D2_iso_cleaving x (F (R x)) i xx).
    set (jj := Isos.z_iso_inv_from_z_iso_disp (pr2 j)).
    cbn in jj.
    assert (p : pr1 j = FF (R x) (rad_ob xx)).
    {

      admit.
    }
    induction p.
    exact (pr1 jj).
  Admitted.

  Definition rad_counit_z_iso {x : C2} (xx : D2 x)
    : Isos.is_z_iso_disp (adjcounitiso F x) (rad_counit_ob xx).
  Proof.
    exists (rad_counit_inv_ob xx).
    split.
    - cbn.
  Admitted.

  Definition rad_over_functor_data
    : disp_functor_data (right_functor F) D2 D1.
  Proof.
    unfold disp_functor_data.
    use tpair.
    - exact (λ x xx, rad_ob xx).
    - intros x y xx yy f ff.
      set (xx' := rad_ob xx).
      set (yy' := rad_ob yy).

      set (w := FF_ff (R x) (R y) xx' yy' ((# R)%Cat f)).
      set (ww := _ ,, w : weq _ _).
      set (winv := pr1weq (invweq ww)).
      cbn.

      apply winv.

      assert (p : ε x · f · pr1 (εiso y) = (# F)%Cat ((# R)%Cat f)).
      {
        etrans. {
          apply maponpaths_2.
          exact (! pr2 ε x y f).
        }
        rewrite assoc'.
        etrans. {
          apply maponpaths.
          apply εiso.
        }
        apply id_right.
      }
      cbn.
      induction p.

      set (εε_x := rad_counit_ob xx).
      set (εεinv_y := rad_counit_inv_ob yy).
      exact (comp_disp (comp_disp εε_x ff) εεinv_y).
  Defined.

  Lemma rad_over_functor_axioms
    : disp_functor_axioms rad_over_functor_data.
  Proof.
    split.
    - intros x xx.
      cbn.


      admit.
    - intros x y z xx yy zz f g ff gg.
      admit.
  Admitted.

  Definition rad_over_functor
    : disp_functor (right_functor F) D2 D1
    := _ ,, rad_over_functor_axioms.

  Lemma rad_unit_is_nat_trans
    : disp_nat_trans_axioms (R' := disp_functor_identity _)
                            (R := disp_functor_composite _ rad_over_functor)
                            (a := η)
                            (λ (x : C1) (xx : D1 x), rad_unit_ob xx).
  Proof.
  Admitted.

  Definition rad_unit
    :  NaturalTransformations.disp_nat_trans
         (adjunit F)
         (disp_functor_identity D1)
         (disp_functor_composite FF rad_over_functor)
    := (λ x xx, rad_unit_ob xx) ,, rad_unit_is_nat_trans.

  Lemma rad_counit_is_nat_trans
    : disp_nat_trans_axioms (R' := disp_functor_composite rad_over_functor _)
                            (R := disp_functor_identity _)
                            (a := ε)
                            (λ (x : C2) (xx : D2 x), rad_counit_ob xx).
  Proof.
  Admitted.

  Definition rad_counit
    :  NaturalTransformations.disp_nat_trans
         (adjcounit F)
         (disp_functor_composite rad_over_functor FF)
         (disp_functor_identity D2)
    := (λ x xx, rad_counit_ob xx) ,, rad_counit_is_nat_trans.

  Definition rad_over_data
    : @right_adjoint_over_data C1 C2 F D1 D2 FF.
  Proof.
    exists rad_over_functor.
    exists rad_unit.
    exact rad_counit.
  Defined.

  Lemma rad_over_form_disp_adjunction
    : form_disp_adjunction F rad_over_data.
  Proof.
    split.
    - intros x xx ; cbn.
      admit.
    - intros x xx ; cbn.
      admit.
  Admitted.

  Definition rad_over
    : @right_adjoint_over C1 C2 F D1 D2 FF.
  Proof.
    exists rad_over_data.
    exact rad_over_form_disp_adjunction.
  Defined.

  Definition rad_over_form_equiv
    : @form_equiv_over C1 C2 F D1 D2 rad_over.
  Proof.
    exists (λ x xx, rad_unit_z_iso xx).
    exact (λ x xx, rad_counit_z_iso xx).
  Defined.

  Definition ff_spliteso_to_is_equiv_over
    : is_equiv_over F FF.
  Proof.
    exists rad_over.
    exact rad_over_form_equiv.
  Defined.

End FF_SPLITESO_TO_EQUIV_OVER.
