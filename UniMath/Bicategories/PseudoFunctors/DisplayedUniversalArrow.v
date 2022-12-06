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

Require Import UniMath.CategoryTheory.DisplayedCats.Core.

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

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.

Local Open Scope cat.

Section DisplayedLeftUniversalArrow.

  Context {B1 B2 : bicat}
          {R : psfunctor B1 B2}
          (LUR : left_universal_arrow R).

  Let L : B2 -> B1 := pr1 LUR.
  Let η : ∏ x : B2, B2 ⟦ x, R (L x) ⟧ := pr12 LUR.
  Let adj :  ∏ (x : B2) (y : B1), adj_equivalence_of_cats (left_universal_arrow_functor R x y η)
      := pr22 LUR.

  Context {D1 : disp_bicat B1} {D2 : disp_bicat B2}
          (RR : disp_psfunctor D1 D2 R).

  Print left_universal_arrow.

  Definition disp_left_universal_arrow : UU
    := ∑ (LL : ∏ x : B2, D2 x → D1 (L x)),
      ∑ (ηη : ∏ (x : B2) (xx : D2 x),  xx -->[η x] (RR _ (LL _ xx))),
      nat.

  Context (dLUR : disp_left_universal_arrow).

  Let LL := pr1 dLUR.
  Let ηη := pr12 dLUR.
  Let dadj := pr22 dLUR.

  (* Have to Require Import UniMath.Bicategories.PseudoFunctor.UniversalArrowToBiadjunction,
     this allows us to use the lemmas in there, e.g. lift_2cell, etc. *)

  Lemma TODO_JOKER (A : UU) : A. Proof. Admitted.

  Definition total_disp_left_universal_arrow_left_adj_functor_data
             {x : B2} (xx : D2 x) {y : B1} (yy : D1 y)
    : functor_data (hom (C := total_bicat _) (x,, xx) (total_psfunctor D1 D2 R RR (y,, yy)))
                   (hom (C := total_bicat _) (L x,, LL x xx) (y,, yy)).
  Proof.
    use make_functor_data.
    - intros [f ff].
      exists (pr11 (adj x y) f).
      apply TODO_JOKER.
    - intros [f ff] [g gg] [α αα].
      exists (#(pr11 (adj x y)) α).
      apply TODO_JOKER.
  Defined.

  Lemma total_disp_left_universal_arrow_left_adj_functor_is_functor
        {x : B2} (xx : D2 x) {y : B1} (yy : D1 y)
    : is_functor (total_disp_left_universal_arrow_left_adj_functor_data xx yy).
  Proof.
    split.
    - intros [f ff].
      use total2_paths_f.
      + exact (functor_id (pr11 (adj x y)) f).
      + admit.
  - intros [f ff] [g gg] [h hh] [α αα] [beta_ betabeta].
    use total2_paths_f.
    + apply (functor_comp (pr11 (adj x y)) α beta_).
    + admit.
  Admitted.

  Definition total_disp_left_universal_arrow_left_adj_functor
             {x : B2} (xx : D2 x) {y : B1} (yy : D1 y)
    : hom (C := total_bicat _) (x,, xx) (total_psfunctor D1 D2 R RR (y,, yy))
          ⟶ hom (C := total_bicat _) (L x,, LL x xx) (y,, yy)
    := _ ,, total_disp_left_universal_arrow_left_adj_functor_is_functor xx yy.

  (* Really need displayed adjoint equivalence and the lemma on the displayed hom-functor
     By the latter I mean that the hom-functor on the total bicat is a total functor *)


  Definition total_disp_left_universal_arrow
    : left_universal_arrow (total_psfunctor D1 D2 R RR).
  Proof.
    use make_left_universal_arrow.
    - intros [x xx].
      exact (L x,, LL _ xx).
    - intros [x xx].
      exact (η x ,, ηη _ xx).
    - intros [x xx] [y yy].
      exact (total_disp_left_universal_arrow_left_adj_functor xx yy).
    - intros [x xx] [y yy].
      use tpair.
      + intros [f ff].
        exists (pr1 (pr121 (adj x y)) f).
        admit.
      + intros [f ff] [g gg] [α αα].
        use total2_paths_f.
        * exact (pr21 (pr121 (adj x y)) f g α).
        * admit.
    -




  (* Definition total_disp_left_universal_arrow
             (TD1 : is_univalent_2_1 (total_bicat D1))
    : left_universal_arrow (total_psfunctor D1 D2 R RR).
  Proof.
    use make_left_universal_arrow'.
    - exact TD1.
    - intros [x xx].
      exact (L x,, LL _ xx).
    - intros [x xx].
      exact (η x ,, ηη _ xx).
    - intros [x xx] [y yy] [f ff] [g gg] [α αα].
      cbn.
      unfold total_prebicat_cell_struct.
      cbn in *.
      repeat (use tpair).
      + exact (lift_2cell gg).


      use tpair.
      + cbn in αα.
        unfold disp_2cells in αα.
        cbn in *.
        unfold total_prebicat_cell_struct.
        cbn. *)







  (* Also show that disp_left_universal_arrow induces disp_adjunction *)

End DisplayedLeftUniversalArrow.
