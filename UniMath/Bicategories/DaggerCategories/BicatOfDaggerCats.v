Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.

Require Import UniMath.Bicategories.DaggerCategories.Core.
Require Import UniMath.Bicategories.DaggerCategories.Univalence.

Local Definition CAT : bicat := bicat_of_cats.

Local Open Scope cat.

Section BicatOfDaggerCategories.

  Definition DAG_disp_cat_ob_mor
    : disp_cat_ob_mor CAT.
  Proof.
    exists (λ C, dagger C).
    exact (λ C D dC dD F, is_dagger_functor dC dD F).
  Defined.

  Definition DAG_disp_cat_id_comp
    : disp_cat_id_comp CAT DAG_disp_cat_ob_mor.
  Proof.
    exists (λ C dC, dagger_functor_id dC).
    exact (λ C D E F G dC dD dE dF dG, is_dagger_functor_comp dF dG).
  Qed.

  Definition DAG_disp_cat_data
    :  disp_cat_data CAT.
  Proof.
    exists DAG_disp_cat_ob_mor.
    exact DAG_disp_cat_id_comp.
  Defined.

  Definition DAG_disp_2cell_struct
    : disp_2cell_struct DAG_disp_cat_data.
  Proof.
    intro ; intros ; exact unit.
  Defined.

  Definition DAG_disp_prebicat_1_id_comp_cells
    : disp_prebicat_1_id_comp_cells CAT.
  Proof.
    exists DAG_disp_cat_data.
    exact DAG_disp_2cell_struct.
  Defined.

  Definition DAG_disp_prebicat_ops
    : disp_prebicat_ops DAG_disp_prebicat_1_id_comp_cells.
  Proof.
    repeat (use tpair) ; intro ; intros ; exact tt.
  Defined.

  Definition DAG_disp_prebicat_data : disp_prebicat_data CAT.
  Proof.
    exists DAG_disp_prebicat_1_id_comp_cells.
    exact DAG_disp_prebicat_ops.
  Defined.

  Definition DAG_disp_prebicat_laws
    : disp_prebicat_laws DAG_disp_prebicat_data.
  Proof.
    repeat (use tpair) ; intro ; intros ; apply isapropunit.
  Qed.

  Definition DAG_disp_prebicat : disp_prebicat CAT.
  Proof.
    exists DAG_disp_prebicat_data.
    exact DAG_disp_prebicat_laws.
  Defined.

  Lemma DAG_has_disp_cellset
    : has_disp_cellset DAG_disp_prebicat.
  Proof.
    intro ; intros ; exact isasetunit.
  Qed.

  Definition DAG_disp_bicat : disp_bicat CAT.
  Proof.
    exists DAG_disp_prebicat.
    exact DAG_has_disp_cellset.
  Defined.

  Definition DAG : bicat
    := total_bicat DAG_disp_bicat.

  Definition is_dagger_univalent (D : DAG)
    : UU
    := is_univalent_dagger (pr2 D).

  Definition UDAG_disp_bicat : disp_bicat DAG
    := disp_fullsubbicat DAG (λ D, is_dagger_univalent D).

End BicatOfDaggerCategories.

Section Constructors.

  Definition make_dagger_category
             {C : category} (d : dagger C)
    : ob DAG := C ,, d.

  Definition make_dagger_category'
             {C : category}
             {d : dagger_structure C}
             (dl : dagger_laws d)
    : ob DAG := C ,, d ,, dl.

  Definition make_dagger_laws
             {C : category} {d : dagger_structure C}
             (lid : dagger_law_id d)
             (lcomp : dagger_law_comp d)
             (lidemp : dagger_law_idemp d)
    : dagger_laws d
    := lid ,, lcomp ,, lidemp.

  Definition make_dagger_functor
             {C D : category}
             {F : functor C D}
             {dagC : dagger C} {dagD : dagger D}
             (dagF : is_dagger_functor dagC dagD F)
    : DAG⟦make_dagger_category dagC, make_dagger_category dagD⟧
    := F ,, dagF.

  Definition make_dagger_transformation
             {C D : category}
             {F G : functor C D}
             (α : nat_trans F G)
             {dagC : dagger C} {dagD : dagger D}
             (dagF : is_dagger_functor dagC dagD F)
             (dagG : is_dagger_functor dagC dagD G)
    : (hom (make_dagger_category dagC) (make_dagger_category dagD))
        ⟦make_dagger_functor dagF, make_dagger_functor dagG⟧
    := α ,, tt.

  Definition make_dagger_transformation'
             {C D : category}
             {F G : functor C D}
             {dagC : dagger C} {dagD : dagger D}
             (dagF : is_dagger_functor dagC dagD F)
             (dagG : is_dagger_functor dagC dagD G)
             {α : nat_trans_data F G}
             (αn : is_nat_trans _ _ α)
    : (hom (make_dagger_category dagC) (make_dagger_category dagD))
        ⟦make_dagger_functor dagF, make_dagger_functor dagG⟧
    := make_nat_trans _ _ α αn ,, tt.

End Constructors.

Section Destructors.

  Definition DAG_to_cat (C : DAG) : category := pr1 C.
  Coercion DAG_to_cat : ob >-> category.

  (* Don't know why the coercion doesn't work *)
  Definition DAG_to_dagger (C : DAG) : dagger (pr1 C) := pr2 C.

End Destructors.
