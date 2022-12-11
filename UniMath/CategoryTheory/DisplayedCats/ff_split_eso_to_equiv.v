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
    set (pp := base_paths _ _ p).
    simpl in pp.
    induction (pp).
    induction (! q).

    (* exact (pr1 jj). *)


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
