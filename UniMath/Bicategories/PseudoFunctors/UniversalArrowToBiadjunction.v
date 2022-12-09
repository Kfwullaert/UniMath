(* In this file, it is shown that any left universal arrow (of a pseudo functor R) induces the data of a biadjunction.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.Modifications.Modification.

Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.
Import PseudoFunctor.Notations.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.


Local Open Scope cat.

Section LeftUniversalArrowToLeftAdjoint.

  Context {B1 B2 : bicat}
          {R : psfunctor B1 B2}
          (LUR : left_universal_arrow R).

  Let L : B2 -> B1 := pr1 LUR.
  Let η : ∏ x : B2, B2 ⟦ x, R (L x) ⟧ := pr12 LUR.

  Let adj :  ∏ (x : B2) (y : B1), adj_equivalence_of_cats (left_universal_arrow_functor R x y η)
      := pr22 LUR.
  Let adjinv : ∏ (x : B2) (y : B1), adj_equivalence_of_cats _
      := λ x y, adj_equivalence_of_cats_inv (adj x y).

  Notation "ε{ x }_{ y }" := (counit_nat_z_iso_from_adj_equivalence_of_cats (adj x y)).
  Notation "η{ x }_{ y }" := (unit_nat_z_iso_from_adj_equivalence_of_cats (adj x y)).

  Notation "ε'{ x }_{ y }" := (counit_nat_z_iso_from_adj_equivalence_of_cats (adjinv x y)).
  Notation "η'{ x }_{ y }" := (unit_nat_z_iso_from_adj_equivalence_of_cats (adjinv x y)).

  Definition lift_mor {x : B2} {y : B1}
             (f : B2⟦x, R y⟧)
    : B1⟦L x, y⟧
    := pr11 (adj x y) f.

  Definition lift_mor' {x : B2} {y : B1}
             (f : B1⟦L x, y⟧)
    : B2⟦x, R y⟧
    := pr11 (adjinv x y) f.

  Definition lift_mor_of_lift_mor' {x : B2} {y : B1} (f : B1⟦L x , y⟧)
    : (hom _ _)⟦lift_mor (lift_mor' f), f⟧
    := ε'{x}_{y} f.

  Definition lift_mor'_of_lift_mor {x : B2} {y : B1} (f : B1⟦L x, y⟧)
    : (hom _ _)⟦f, lift_mor (lift_mor' f)⟧
    := η{x}_{y} f.

  Definition lift_mor_of_lift_mor'_is_z_iso
             {x : B2} {y : B1} (f : B1⟦L x , y⟧)
    : is_z_isomorphism (C := hom _ _) (lift_mor_of_lift_mor' f)
    := (pr2 ε'{x}_{y} f).

  Definition lift_mor_of_lift_mor'_z_iso
        {x : B2} {y : B1} (f : B1⟦L x , y⟧)
    : z_iso (C := hom _ _) (lift_mor (lift_mor' f)) f
    := _ ,, lift_mor_of_lift_mor'_is_z_iso f.

  Definition lift_2cell {x : B2} {y : B1}
             {f g : B2⟦x, R y⟧}
             (α : (hom x (R y))⟦f,g⟧)
    : (hom (L x) y)⟦lift_mor f, lift_mor g⟧
    := # (pr11 (adj x y)) α.

  Definition lift_2cell_is_z_iso
             {x : B2} {y : B1}
             {f g : B2⟦x, R y⟧}
             {α : (hom x (R y))⟦f,g⟧}
             (αiso : is_z_isomorphism α)
    : is_z_isomorphism (C := hom _ _) (lift_2cell α)
    := functor_on_is_z_isomorphism (pr11 (adj x y)) αiso.

  Definition lift_invertible_2cell
             {x : B2} {y : B1}
             {f g : B2⟦x, R y⟧}
             {α : (hom x (R y))⟦f,g⟧}
             (αiso : is_z_isomorphism α)
    : z_iso (C := hom _ _) (lift_mor f) (lift_mor g)
    := _ ,, lift_2cell_is_z_iso αiso.

  Definition lift_2cell_eq {x : B2} {y : B1}
             {f g : B2⟦x, R y⟧}
             {α β : (hom x (R y))⟦f,g⟧}
             (p : lift_2cell α = lift_2cell β)
    : α = β.
  Proof.
    set (ff := fully_faithful_from_equivalence
                   _ _ _
                   (adjinv x y)).
    set (f_f := fully_faithful_implies_full_and_faithful _ _ _ ff).
    set (fa := pr2 f_f).
    set (fa_fg := fa f g).
    set (i := isweqonpathsincl _ fa_fg).
    set (j := i α β).
    set (ii := (Injectivity _ i α β)).
    use (invmap ii).
    exact p.
  Qed.

  Definition unit_on_ob {x : B2} {y : B1} (f : B1⟦L x, y⟧)
    :  f ==> lift_mor (η x · # R f)
    := η{x}_{y} f.

  Definition counitinv_on_ob {x : B2} {y : B1} (f : B1⟦L x, y⟧)
    :  lift_mor (η x · # R f) ==> f
    := ε'{x}_{y} f.

  Definition lift_2cell' {x : B2} {y : B1}
             {f g : B1⟦L x, y⟧}
             (α : (hom x (R y))⟦lift_mor' f,lift_mor' g⟧)
    : (hom (L x) y)⟦f, g⟧
    := unit_on_ob f • lift_2cell α • counitinv_on_ob g.

  Definition lift_unit (x : B2)
    :  id₁ (L x) ==> lift_mor (id₁ x · η x).
  Proof.
    refine (unit_on_ob (id₁ (L x)) • (lift_2cell _)).
    refine (_ • linvunitor _).
    refine (_ • runitor _).
    use lwhisker.
    apply (inv_of_invertible_2cell (psfunctor_id R (L x))).
  Defined.

  Definition no_idea_lift_id (x : B1)
    : (η (R x) · # R (lift_mor (id₁ (R x)))) ==> (id₁ (R x)).
  Proof.
    set (t :=  pr121 (adjinv (R x) x)).

    transparent assert (si : (is_invertible_2cell (pr1 t  (id₁ (R x))))).
    {
      apply is_z_iso_to_is_inv2cell.
      apply (pr12 (adjinv (R x) x)).
    }
    exact (inv_of_invertible_2cell (make_invertible_2cell si)).
  Defined.

  Definition no_idea_lift_id_z_iso (x : B1)
    : z_iso (C := hom _ _) (η (R x) · # R (lift_mor (id₁ (R x)))) (id₁ (R x)).
  Proof.
    exists (no_idea_lift_id x).
    use is_inv2cell_to_is_z_iso.
    apply inv_of_invertible_2cell.
  Defined.

  Definition lift_unit_is_z_iso (x : B2)
    :  is_z_isomorphism (C := hom _ _) (lift_unit x).
  Proof.
    use is_z_iso_comp_of_is_z_isos.
    - apply (pr12 (adj x (L x))).
    - use functor_on_is_z_isomorphism.
      use is_z_iso_comp_of_is_z_isos.
      + use is_z_iso_comp_of_is_z_isos.
        * use is_inv2cell_to_is_z_iso.
          use is_invertible_2cell_lwhisker.
          exact (inv_of_invertible_2cell (psfunctor_id R (L x))).
        * apply is_z_iso_runitor.
      + exact (is_z_iso_inv_from_z_iso (make_z_iso' _ (is_z_iso_lunitor (η x)))).
  Defined.

  Definition lift_unit_z_iso (x : B2)
    :  z_iso (C := hom _ _) (id₁ (L x)) (lift_mor (id₁ x · η x))
    := _ ,, lift_unit_is_z_iso x.

  Definition lift_comp
             {x y z : B2} (f : B2 ⟦ x, y⟧) (g : B2 ⟦ y, z ⟧)
    : lift_mor (f · η y) · lift_mor (g · η z) ==> lift_mor (f · g · η z).
  Proof.
    refine (η{x}_{L z} ( lift_mor (f · η y) · lift_mor (g · η z)) • _).
    use lift_2cell.
    refine (_ • _).
    { use lwhisker.
      2: apply (inv_of_invertible_2cell (psfunctor_comp _ _ _)).
    }
    refine (lassociator _ _ _ • _).
    refine (_ • _).
    {
      use rwhisker.
      2: apply ((ε{ x }_{L y})).
    }
    refine (rassociator _ _ _ • _).
    refine (_ • lassociator _ _ _).
    use lwhisker.
    apply ((ε{y}_{L z})).
  Defined.

  Definition lift_comp_is_z_iso
             {x y z : B2} (f : B2 ⟦ x, y ⟧) (g : B2 ⟦ y, z ⟧)
    : is_z_isomorphism (C := hom _ _) (lift_comp f g).
  Proof.
    use is_z_isomorphism_comp.
    { apply η{x}_{L z}. }
    use lift_2cell_is_z_iso.
    repeat (use is_z_isomorphism_comp).
    - use is_invertible_2cell_lwhisker.
      apply is_invertible_2cell_inv.
    - apply is_z_iso_lassociator.
    - use is_invertible_2cell_rwhisker.
      apply ε{x}_{L y}.
    - apply is_z_iso_rassociator.
    - use is_invertible_2cell_lwhisker.
      apply ε{y}_{L z}.
    - apply is_z_iso_lassociator.
  Defined.

  Definition lift_comp_z_iso
             {x y z : B2} (f : B2 ⟦ x, y ⟧) (g : B2 ⟦ y, z ⟧)
    : z_iso (C := hom _ _) _ _
    := _ ,, lift_comp_is_z_iso f g.

  Definition left_universal_arrow_psfunctor_data
    : psfunctor_data B2 B1.
  Proof.
    use make_psfunctor_data.
    - exact L.
    - exact (λ x y f, lift_mor (f · η y)).
    - exact (λ x y f g α, lift_2cell (rwhisker _ α)).
    - exact (λ x, lift_unit x).
    - exact (λ x y z f g, lift_comp f g).
  Defined.

  Lemma left_universal_arrow_psfunctor_psfunctor_laws
    : psfunctor_laws left_universal_arrow_psfunctor_data.
  Proof.
    repeat split.
    - intros x y f.
      cbn.
      etrans. { apply maponpaths, id2_rwhisker. }
      apply (functor_id (pr11 (adj x (L y)))).
    - intros x y f g h α β.
      cbn.
      etrans.
      2: { apply (functor_comp (pr11 (adj x (L y)))). }
      apply maponpaths.
      apply pathsinv0, rwhisker_vcomp.
    - intros x y f.
      cbn.

      transparent assert (pp : (lift_mor (id₁ x · f · η y) ==> lift_mor (f · η y))).
      {
        use (# (pr11 (adj x (L y)))).
        refine (_ · _).
        - apply rassociator.
        - apply lunitor.
      }

      assert (p : lift_2cell (lunitor f ▹ η y) = pp).
      {
        unfold pp.
        unfold lift_2cell.
        apply maponpaths.
        rewrite (BicategoryLaws.lunitor_assoc (η y) f).
        etrans.
        2: apply vassocl.
        rewrite rassociator_lassociator.
        now rewrite id2_left.
      }

      rewrite vassocl.
      rewrite p.
      unfold pp.
      unfold lift_comp.
      unfold lift_2cell.
      rewrite vassocl.
      etrans.
      2: {
        do 2 apply maponpaths.
        apply (functor_comp (pr11 (adj x (L y)))).
      }
      cbn.
      rewrite ! vassocr.
      etrans.
      2: {
        do 2 apply maponpaths.
        do 2 rewrite vassocl.
        apply maponpaths.
        rewrite vassocr.
        now rewrite lassociator_rassociator.
      }
      rewrite id2_left.
      etrans.
      2: {
        apply maponpaths_2.
        exact (! pr21 η{x}_{L y} _ _ (lift_unit x ▹ lift_mor (f · η y))).
      }
      cbn.

      rewrite vassocl.
      etrans.
      2: {
        apply maponpaths.
        apply (functor_comp (pr11 (adj x (L y)))).
      }







      admit.
    - intros x y f.
      cbn.
      admit.
    - intros x y z w f g h.
      cbn.

      admit.
    - intros  x y z f g1 g2 α.
      cbn.

      admit.
    - intro ; intros ; cbn.
      admit.
  Admitted.

  Definition left_universal_arrow_psfunctor_invertible_cells
    : invertible_cells left_universal_arrow_psfunctor_data.
  Proof.
    split.
    - intro ; apply lift_unit_is_z_iso.
    - intro ; intros ; apply lift_comp_is_z_iso.
  Defined.

  Definition left_universal_arrow_psfunctor
    : psfunctor B2 B1.
  Proof.
    exists left_universal_arrow_psfunctor_data.
    exists left_universal_arrow_psfunctor_psfunctor_laws.
    exact left_universal_arrow_psfunctor_invertible_cells.
  Defined.

  Definition left_universal_arrow_unit_data
    :  pstrans_data
         (Identity.id_psfunctor B2)
         (Composition.comp_psfunctor R left_universal_arrow_psfunctor).
  Proof.
    use make_pstrans_data.
    - exact η.
    - intros x y f.
      use z_iso_to_inv2cell.
      exact (z_iso_inv (_ ,, pr12 (adjinv x (L y)) (f · η y) : z_iso _ _)).
  Defined.

  Definition left_universal_arrow_unit_is_pstrans
    :  is_pstrans left_universal_arrow_unit_data.
  Proof.
    repeat split.
    - intros x y f g α.
      apply (pr21 (ε{x}_{L y})).
    - intro x.
      cbn.
      rewrite id2_rwhisker.
      rewrite id2_right.
      rewrite <- lwhisker_vcomp.
      rewrite vassocl.
      etrans. {
        apply maponpaths.
        unfold lift_unit.
        cbn.
        rewrite psfunctor_vcomp.
        rewrite <- lwhisker_vcomp.
        rewrite vassocl.
        apply maponpaths.
        apply (pr21 ε{x}_{L x}).
      }
      cbn.
      etrans. {
        apply maponpaths.
        rewrite vassocr.
        apply maponpaths_2.
        assert (p : (η x ◃ ## R (unit_on_ob (id₁ (L x)))) • pr1 (counit_from_left_adjoint (adj x (L x))) (η x · # R (id₁ (L x))) = id2 _).
        {
          unfold unit_on_ob.
          admit.
        }
        exact p.
      }
      rewrite id2_left.
      do 2 rewrite vassocr.
      rewrite lwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite lwhisker_id2.
      now rewrite id2_left.
    - intros x y z f g.
      cbn.
      rewrite id2_rwhisker.
      rewrite id2_right.

      admit.
  Admitted.

  Definition left_universal_arrow_unit
    :  pstrans
         (Identity.id_psfunctor B2)
         (Composition.comp_psfunctor R left_universal_arrow_psfunctor).
  Proof.
    use make_pstrans.
    - exact left_universal_arrow_unit_data.
    - exact left_universal_arrow_unit_is_pstrans.
  Defined.

  Definition lift_mor_precompose_id {x y : B1} (f : B1⟦x,y⟧)
    : invertible_2cell
        (lift_mor (id₁ (R x)) · f)
        (lift_mor (# R f · η (R y)) · lift_mor (id₁ (R y))).
  Proof.
  Admitted.

  Definition left_universal_arrow_counit_data
    :  pstrans_data
         (Composition.comp_psfunctor left_universal_arrow_psfunctor R)
         (Identity.id_psfunctor B1).
  Proof.
    use make_pstrans_data.
    - exact (λ x, lift_mor (identity (R x))).
    - exact (λ x y f, lift_mor_precompose_id f).
  Defined.

  Definition left_universal_arrow_counit_is_pstrans
    :  is_pstrans left_universal_arrow_counit_data.
  Proof.
    repeat split.
    - intros x y f g α.
      cbn.


      admit.
    - intro x.
      cbn.
      admit.
    - intros x y z f g.
      cbn.
      admit.
  Admitted.

  Definition left_universal_arrow_counit
    :  pstrans
         (Composition.comp_psfunctor left_universal_arrow_psfunctor R)
         (Identity.id_psfunctor B1).
  Proof.
    use make_pstrans.
    - exact left_universal_arrow_counit_data.
    - exact left_universal_arrow_counit_is_pstrans.
  Defined.

  Definition left_universal_arrow_unit_counit
    :  left_biadj_unit_counit left_universal_arrow_psfunctor.
  Proof.
    use make_biadj_unit_counit.
    - exact R.
    - exact left_universal_arrow_unit.
    - exact left_universal_arrow_counit.
  Defined.

  Definition no_idea_for_the_name (x : B2)
    :  z_iso (C := hom _ _) (lift_mor (η x · η (R (L x))) · lift_mor (id₁ (R (L x)))) (lift_mor (id₁ x · η x)).
  Proof.
    use (z_iso_comp _ (lift_unit_z_iso x)).



  Admitted.

  Definition left_universal_arrow_triangle_l_law_data
    : invertible_modification_data
        (biadj_triangle_l_lhs left_universal_arrow_unit_counit)
        (id_pstrans left_universal_arrow_psfunctor).
  Proof.
    intro x.
    use z_iso_to_inv2cell.
    use z_iso_comp.
    3: exact (z_iso_inv_from_z_iso (lift_unit_z_iso x)).
    use z_iso_comp.
    2: exact (inv2cell_to_z_iso (lunitor_invertible_2cell _)).
    use z_iso_comp.
    2: {
      use lwhisker_of_invertible_2cell.
      2: apply lunitor_invertible_2cell.
    }
    use z_iso_comp.
    2: {
      use lwhisker_of_invertible_2cell.
      2: apply runitor_invertible_2cell.
    }
    apply no_idea_for_the_name.
  Defined.

  Definition left_universal_arrow_triangle_r_law_data
    : invertible_modification_data
        (biadj_triangle_r_lhs left_universal_arrow_unit_counit)
        (id_pstrans left_universal_arrow_unit_counit).
  Proof.
    intro x.
    use z_iso_to_inv2cell.
    use z_iso_comp.
    2: apply lunitor_invertible_2cell.
    use z_iso_comp.
    2: {
      use lwhisker_of_invertible_2cell.
      2: apply lunitor_invertible_2cell.
    }
    use z_iso_comp.
    2: {
      use lwhisker_of_invertible_2cell.
      2: apply runitor_invertible_2cell.
    }
    apply no_idea_lift_id_z_iso.
  Defined.

  Lemma left_universal_arrow_triangle_l_law_is_modification
    : is_modification left_universal_arrow_triangle_l_law_data.
  Proof.
    intros x y f.
  Admitted.

  Lemma left_universal_arrow_triangle_r_law_is_modification
    : is_modification left_universal_arrow_triangle_r_law_data.
  Proof.
    intros x y f.
  Admitted.

  Definition left_universal_arrow_triangle_l_law
    : biadj_triangle_l_law left_universal_arrow_unit_counit.
  Proof.
    use make_invertible_modification.
    - exact left_universal_arrow_triangle_l_law_data.
    - exact left_universal_arrow_triangle_l_law_is_modification.
  Defined.

  Definition left_universal_arrow_triangle_r_law
    : biadj_triangle_r_law left_universal_arrow_unit_counit.
  Proof.
    use make_invertible_modification.
    - exact left_universal_arrow_triangle_r_law_data.
    - exact left_universal_arrow_triangle_r_law_is_modification.
  Defined.

  Definition left_universal_arrow_biadj_data
    : left_biadj_data left_universal_arrow_psfunctor.
  Proof.
    use make_biadj_data.
    - exact left_universal_arrow_unit_counit.
    - exact left_universal_arrow_triangle_l_law.
    - exact left_universal_arrow_triangle_r_law.
  Defined.

End LeftUniversalArrowToLeftAdjoint.
