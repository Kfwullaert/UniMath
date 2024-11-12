Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.

Require Import UniMath.CategoryTheory.DisplayedCats.Adjunctions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.DisplayedCats.TotalAdjunction.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Univalence.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.

Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.Modifications.Modification.

Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.
Import PseudoFunctor.Notations.

Require Import UniMath.Bicategories.DisplayedBicats.DispBiadjunction.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Import DispBicat.Notations.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.

Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrows.core.
Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrows.propositional_builder.

(* Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOnCatToUniv. *)

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Lemma sigma_bicat_of_locally_contractibles
  {B : bicat}
  {D : disp_bicat B}
  (E : disp_bicat (total_bicat D))
  : disp_2cells_iscontr D → disp_2cells_iscontr E → disp_2cells_iscontr (sigma_bicat _ _ E).
Proof.
Admitted.

Lemma sigma_bicat_of_locally_propositionals
  {B : bicat}
  {D : disp_bicat B}
  (E : disp_bicat (total_bicat D))
  : disp_2cells_isaprop D → disp_2cells_isaprop E → disp_2cells_isaprop (sigma_bicat _ _ E).
Proof.
Admitted.

Section MakeDisplayedLeftUniversalArrowOfSigmaIfdPropositional.

  Context {B1 B2 : bicat}
          {R : psfunctor B1 B2}
          {D1 : disp_bicat B1} {D2 : disp_bicat B2}
          {dR : disp_psfunctor D1 D2 R}
          {E1 : disp_bicat (total_bicat D1)}
          {E2 : disp_bicat (total_bicat D2)}
          (ddR : disp_psfunctor E1 E2 (total_psfunctor _ _ _ dR)).

  Context (D1_2cells_prop : disp_2cells_isaprop D1)
    (D2_2cells_prop : disp_2cells_isaprop D2)
    (E1_2cells_prop : disp_2cells_isaprop E1)
    (E2_2cells_prop : disp_2cells_isaprop E2).

  Definition sigma_disp_psfunctor_on_ob {x : B1} (de : sigma_bicat B1 D1 E1 x)
    : sigma_bicat B2 D2 E2 (R x).
  Proof.
    exact (dR x (pr1 de) ,, ddR (x,,pr1 de) (pr2 de)).
  Defined.

  Definition sigma_disp_psfunctor_on_mor
    {x y : B1} {f : B1⟦x, y⟧}
    {xx : sigma_bicat B1 D1 E1 x} {yy : sigma_bicat B1 D1 E1 y}
    (ff : xx -->[ f] yy)
    : sigma_disp_psfunctor_on_ob xx -->[(# R)%cat f] sigma_disp_psfunctor_on_ob yy.
  Proof.
    exists (pr121 dR x y f (pr1 xx) (pr1 yy) (pr1 ff)).
    exact (pr121 ddR (x ,, pr1 xx) (y ,, pr1 yy) (f ,, pr1 ff) (pr2 xx) (pr2 yy) (pr2 ff)).
  Defined.

  Definition sigma_disp_psfunctor_on_2cells
    {x y : B1} {f g : B1 ⟦ x, y ⟧} {α : f ==> g}
    {xx : sigma_bicat _ _ E1 x}
    {yy : sigma_bicat _ _ E1 y}
    {ff : xx -->[f] yy}
    {gg : xx -->[g] yy}
    (α' : ff ==>[α] gg)
    : sigma_disp_psfunctor_on_mor ff ==>[ ## R α] sigma_disp_psfunctor_on_mor gg.
  Proof.
    exists (pr1 (pr221 dR) x y f g α _ _ _ _ (pr1 α')).
    exact (pr1 (pr221 ddR) _ _ _ _ _ _ _ _ _ (pr2 α')).
  Defined.

  Lemma sigma_disp_psfunctor_unital : ∏ (x : B1) (xx : sigma_bicat _ _ E1 x),
  disp_invertible_2cell (psfunctor_id R x) (id_disp (sigma_disp_psfunctor_on_ob xx))
    (sigma_disp_psfunctor_on_mor (id_disp xx)).
  Proof.
    simpl. intros x [xx xxx].
    simple refine (_ ,, _ ,, _).
    + exists (pr12 (pr221 dR) x xx).
      exact (pr12 (pr221 ddR) (x,, xx) xxx).
    + exists (pr12 (pr12 (pr221 dR) x xx)).
      exact (pr12 (pr12 (pr221 ddR) (x,,xx) xxx)).
    + split ; use proofirrelevance ; use isaproptotal2 ; intro ; intros ;
        try (apply E2_2cells_prop) ; try (apply D2_2cells_prop).
  Defined.

  Lemma sigma_disp_psfunctor_assoc {x y z : B1}
    {f : B1 ⟦ x, y ⟧} {g : B1 ⟦ y, z ⟧}
    {xx : sigma_bicat _ _ E1 x}
    {yy : sigma_bicat _ _ E1 y}
    {zz : sigma_bicat _ _ E1 z}
    (ff : xx -->[ f] yy) (gg : yy -->[ g] zz)
    : disp_invertible_2cell (psfunctor_comp R f g)
        (sigma_disp_psfunctor_on_mor ff ;; sigma_disp_psfunctor_on_mor gg)
        (sigma_disp_psfunctor_on_mor (ff ;; gg)).
  Proof.
    simple refine (_ ,, _ ,, _).
    - exists ((pr22 (pr221 dR)) x y z f g _ _ _ (pr1 ff) (pr1 gg)).
      exact ((pr22 (pr221 ddR)) _ _ _ _ _ _ _ _ (pr2 ff) (pr2 gg)).
    - exists (pr12 ((pr22 (pr221 dR)) x y z f g _ _ _ (pr1 ff) (pr1 gg))).
      exact (pr12 ((pr22 (pr221 ddR)) _ _ _ _ _ _ _ _ (pr2 ff) (pr2 gg))).
    - abstract (
          split ; use proofirrelevance ; use isaproptotal2 ; intro ; intros
          ; try (apply E2_2cells_prop) ; try (apply D2_2cells_prop)
        ).
  Defined.

  Definition sigma_disp_psfunctor_data
    : disp_psfunctor_data (sigma_bicat _ _ E1) (sigma_bicat _ _ E2) R.
  Proof.
    repeat (use tpair).
    - exact (λ _ de, sigma_disp_psfunctor_on_ob de).
    - exact (λ _ _ _ _ _ ff, sigma_disp_psfunctor_on_mor ff).
    - exact (λ _ _ _ _ _ _ _ _ _ αα, sigma_disp_psfunctor_on_2cells αα).
    - apply sigma_disp_psfunctor_unital.
    - intro ; intros ; apply sigma_disp_psfunctor_assoc.
  Defined.

  Lemma sigma_disp_psfunctor_laws
    : is_disp_psfunctor (sigma_bicat B1 D1 E1) (sigma_bicat B2 D2 E2) R sigma_disp_psfunctor_data.
  Proof.
    repeat split ; intro ; intros ; use proofirrelevance ; use isaproptotal2 ; intro ; intros
    ; try (apply E2_2cells_prop) ; try (apply D2_2cells_prop).
  Qed.

  Definition sigma_disp_psfunctor
    : disp_psfunctor (sigma_bicat _ _ E1) (sigma_bicat _ _ E2) R.
  Proof.
    exists sigma_disp_psfunctor_data.
    exact sigma_disp_psfunctor_laws.
  Defined.

  Context {LUR : left_universal_arrow R}
          (dLUR : disp_left_universal_arrow LUR dR)
          (ddLUR : disp_left_universal_arrow (total_left_universal_arrow _ _ dLUR) ddR).

  Definition sigma_disp_univ_arrow_LL_ob
    {x : B2} (xx : sigma_bicat B2 D2 E2 x)
    : sigma_bicat B1 D1 E1 (pr1 LUR x).
  Proof.
    exact (pr1 dLUR x (pr1 xx) ,, pr1 ddLUR (x,, pr1 xx) (pr2 xx)).
  Defined.

  Definition sigma_disp_univ_arrow_LL_η
    {x : B2} (xx : sigma_bicat B2 D2 E2 x)
    : xx -->[(pr12 LUR) x] sigma_disp_psfunctor (pr1 LUR x) (sigma_disp_univ_arrow_LL_ob xx).
  Proof.
    exists (pr12 dLUR x (pr1 xx)).
    exact (pr12 ddLUR (x,,pr1 xx) (pr2 xx)).
  Defined.

  Definition sigma_disp_univ_arrow_LL_mor
    {x : B2} {xx : pr1 (sigma_bicat B2 D2 E2) x}
    {y : B1} {yy : sigma_bicat B1 D1 E1 y}
    {f : B2⟦x, R y⟧}
    (ff : xx -->[f] sigma_disp_psfunctor y yy)
    : sigma_disp_univ_arrow_LL_ob xx -->[right_adjoint ((pr22 LUR) x y) f] yy.
  Proof.
    exists (pr22 dLUR _ _ _ _ _ (pr1 ff)).
    exact ((pr22 ddLUR (x,,pr1 xx) (pr2 xx) (y ,, pr1 yy) (pr2 yy)) (f,,pr1 ff) (pr2 ff)).
  Defined.

  Definition sigma_disp_univ_arrow_LL_2cell
    {x : B2} {xx : pr1 (sigma_bicat B2 D2 E2) x}
    {y : B1} {yy : sigma_bicat B1 D1 E1 y}
    {f₁ f₂ : B2⟦x, R y⟧}
    {ff₁ : xx -->[ f₁] sigma_disp_psfunctor y yy}
    {ff₂ : xx -->[ f₂] sigma_disp_psfunctor y yy}
    {α : f₁ ==> f₂}
    (α' : ff₁ ==>[ α] ff₂)
    : sigma_disp_univ_arrow_LL_mor ff₁
        ==>[ (# (right_adjoint ((pr22 LUR) x y)))%cat α]
        sigma_disp_univ_arrow_LL_mor ff₂.
  Proof.
  Admitted.

  Definition make_disp_univ_arrow_of_sigma_if_prop
    : disp_left_universal_arrow LUR sigma_disp_psfunctor.
  Proof.
    use make_disp_univ_arrow_if_prop.
    - exact (sigma_bicat_of_locally_propositionals _ D1_2cells_prop E1_2cells_prop).
    - exact (sigma_bicat_of_locally_propositionals _ D2_2cells_prop E2_2cells_prop).
    - exact (λ _ x', sigma_disp_univ_arrow_LL_ob x').
    - exact (λ _ x', sigma_disp_univ_arrow_LL_η x').
    - exact (λ _ _ _ _ _ f', sigma_disp_univ_arrow_LL_mor f').
    - exact (λ _ _ _ _ _ _ _ _ _ α', sigma_disp_univ_arrow_LL_2cell α').
    - (* intro ; intros ; use tpair. *)
      admit. (* LL_unit*)
    - admit. (** LL_unit_inv *)
    - admit. (* LL_counit *)
    - admit. (* LL_counit_inv *)
  Admitted.

End MakeDisplayedLeftUniversalArrowOfSigmaIfdPropositional.
