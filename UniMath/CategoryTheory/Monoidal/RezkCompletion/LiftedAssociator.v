Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PrecompEquivalence.

Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorCategory.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.CategoriesLemmas.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.DisplayedCategoriesLemmas.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedTensor.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedTensorUnit.

Local Open Scope cat.

Section RezkAssociator.

  Context {C D : category} {H : functor C D}
          (Duniv : is_univalent D)
          (H_eso : essentially_surjective H)
          (H_ff : fully_faithful H).

  Context (TC : functor (C ⊠ C) C)
          (α : associator TC).

  Definition DDDuniv : is_univalent ((D ⊠ D) ⊠ D).
  Proof.
    Search (is_univalent (_ ⊠ _)).
    apply is_unvialent_category_binproduct.
    2: exact Duniv.
    apply is_unvialent_category_binproduct.
    exact Duniv.
    exact Duniv.
  Qed.

  Let TD := TransportedTensor Duniv H_eso H_ff TC.

  Local Notation HH := (pair_functor H H).
  Let HH_eso := pair_functor_eso H H H_eso H_eso.
  Let HH_ff := pair_functor_ff H H H_ff H_ff.

  Local Notation HHH := (pair_functor HH H).
  Let HHH_eso := pair_functor_eso HH H HH_eso H_eso.
  Let HHH_ff := pair_functor_ff HH H HH_ff H_ff.

  Local Notation HHH' := (pair_functor H HH).
  Let HHH'_eso := pair_functor_eso _ _ H_eso HH_eso.
  Let HHH'_ff := pair_functor_ff _ _ H_ff HH_ff.

  Lemma TransportedAssocLeft
    :  nat_z_iso (HHH ∙ assoc_left TD) (assoc_left TC ∙ H).
  Proof.
    use nat_z_iso_comp.
    2: {
      apply CategoriesLemmas.pre_whisker_nat_z_iso.
      exact (nat_z_iso_inv (lift_functor_along_comm_prod (_,,Duniv) H H_eso H_ff TC)).
    }
    apply (lift_functor_along_comm (_,,Duniv) _ HHH_eso HHH_ff).
  Defined.

  Lemma unassoc_commutes
    : nat_z_iso (HHH ∙ (precategory_binproduct_unassoc D D D))
                ((precategory_binproduct_unassoc C C C) ∙ (pair_functor H HH)).
  Proof.
    use make_nat_z_iso.
    - use make_nat_trans.
      + intro ; use catbinprodmor ; apply identity.
      + intro ; intros.
        use total2_paths_f.
        * exact (id_right _ @ ! id_left _).
        * abstract (rewrite transportf_const ; exact (id_right _ @ ! id_left _)).
    - intro.
      use tpair.
      * use catbinprodmor ; apply identity.
      * abstract (split ; (use total2_paths_f ; [ apply id_right | rewrite transportf_const ; apply id_right ])).
  Defined.

  Lemma TransportedAssocRight
    : nat_z_iso (HHH ∙ assoc_right TD) (assoc_right TC ∙ H).
  Proof.
    (* This commuting diagram can be split in 3 commuting diagrams stacked together *)
    (* Step 1: The top commuting diagram is unassoc_commutes *)
    use nat_z_iso_comp.
    2: apply CategoriesLemmas.nat_z_iso_functor_comp_assoc.
    use nat_z_iso_comp.
    2: {
      use CategoriesLemmas.post_whisker_nat_z_iso.
      2: exact unassoc_commutes.
    }
    use nat_z_iso_comp.
    2: apply (nat_z_iso_inv (CategoriesLemmas.nat_z_iso_functor_comp_assoc _ _ _)).
    use nat_z_iso_comp.
    3: apply CategoriesLemmas.nat_z_iso_functor_comp_assoc.
    apply CategoriesLemmas.pre_whisker_nat_z_iso.

    (* Step 2: The lowest commuting diagram is the tensor preserving commuting one *)
    use nat_z_iso_comp.
    3: apply CategoriesLemmas.nat_z_iso_functor_comp_assoc.
    use nat_z_iso_comp.
    3: {
      apply CategoriesLemmas.pre_whisker_nat_z_iso.
      apply TransportedTensorComm.
    }

    use nat_z_iso_comp.
    3: apply (nat_z_iso_inv (CategoriesLemmas.nat_z_iso_functor_comp_assoc _ _ _)).
    use nat_z_iso_comp.
    2: apply CategoriesLemmas.nat_z_iso_functor_comp_assoc.
    apply CategoriesLemmas.post_whisker_nat_z_iso.

    (* Step 3: The middle commuting square is the tensor preserving commuting one
               but tensored with the identity functor on the left *)

    use CategoriesLemmas.product_of_commuting_squares.
    { apply (make_nat_z_iso _ _ _ (is_nat_z_iso_nat_trans_id H)). }
    apply TransportedTensorComm.
  Defined.

  Definition TransportedAssociator
    : associator TD.
  Proof.
    use (lift_nat_z_iso_along (_,,Duniv) HHH HHH_eso HHH_ff).
    use nat_z_iso_comp.
    3: apply (nat_z_iso_inv (TransportedAssocRight)).
    use nat_z_iso_comp.
    2: exact TransportedAssocLeft.
    exact (CategoriesLemmas.post_whisker_nat_z_iso α H).
  Defined.

  Let αD := TransportedAssociator.

  Definition TransportedAssociatorEq
    : pre_whisker HHH TransportedAssociator
      = nat_z_iso_comp
          (nat_z_iso_comp TransportedAssocLeft (CategoriesLemmas.post_whisker_nat_z_iso α H))
          (nat_z_iso_inv (TransportedAssocRight)).
  Proof.
    set (t := lift_nat_trans_along_comm (_,,Duniv) _ HHH_eso HHH_ff
          (nat_z_iso_comp TransportedAssocLeft
                          (nat_z_iso_comp
                             (CategoriesLemmas.post_whisker_nat_z_iso α H)
                             (nat_z_iso_inv TransportedAssocRight)
                          )
        )).
    refine (_ @ t @ _).
    clear t.
    - apply maponpaths.
      apply (maponpaths (lift_nat_trans_along (D,, Duniv) HHH HHH_eso HHH_ff)).
      apply nat_trans_comp_assoc'.
      apply homset_property.
    - exact (nat_trans_comp_assoc (homset_property _)
                                     _ _ _ _
              (pr1 TransportedAssocLeft)
              (CategoriesLemmas.post_whisker_nat_z_iso α H)
              (nat_z_iso_inv TransportedAssocRight)).
  Qed.

  Definition TransportedAssociatorOnOb
    : ∏ x : (C ⊠ C) ⊠ C,
        αD (HHH x) = TransportedAssocLeft x · #H (α x) · nat_z_iso_inv TransportedAssocRight x.
  Proof.
    exact (λ x, toforallpaths _ _ _ (base_paths _ _ TransportedAssociatorEq) x).
  Qed.

  Context (I : C).

  Definition H_pα
    : (functor_ass_disp_cat (IC := I) α αD)
        (H ,, (pr1 (TransportedTensorComm Duniv H_eso H_ff TC) ,, identity _)).
  Proof.
    intros x y z.
    (* set (t := toforallpaths _ _ _ (base_paths _ _ TransportedAssociatorEq) ((x,y),z)). *)

    unfold αD.
    unfold TransportedAssociator.

    assert (p0 : TransportedAssocLeft ((x,y),z) =
                   # TD ((pr11 (TransportedTensorComm Duniv H_eso H_ff TC)) (x, y) #, id pr1 H z)
                     · (pr11 (TransportedTensorComm Duniv H_eso H_ff TC)) (TC (x, y), z)).
    {
      admit.
    }

    etrans. {
      apply maponpaths_2.
      exact (! p0).
    }
    clear p0.

    assert (p1' : (# TD (id pr1 H x #, (pr11 (TransportedTensorComm Duniv H_eso H_ff TC)) (y, z))
                     · (pr11 (TransportedTensorComm Duniv H_eso H_ff TC)) (x, TC (y, z))) = TransportedAssocRight ((x,y),z)).
    {

      admit.
    }

    assert (p1 : (nat_z_iso_inv TransportedAssocRight) ((x,y),z)
                 · (# TD (id pr1 H x #, (pr11 (TransportedTensorComm Duniv H_eso H_ff TC)) (y, z))
             · (pr11 (TransportedTensorComm Duniv H_eso H_ff TC)) (x, TC (y, z))) = identity _).
    {
      (* Here use p1' *)

      admit.
    }

    set (cc := lift_nat_z_iso_along (D,, Duniv) HHH HHH_eso HHH_ff
               (nat_z_iso_comp
       (nat_z_iso_comp TransportedAssocLeft (CategoriesLemmas.post_whisker_nat_z_iso α H))
       (nat_z_iso_inv TransportedAssocRight))).

    set (cc1 := (CategoriesLemmas.post_whisker_nat_z_iso α H)).
    set (cc0 := TransportedAssocLeft).
    set (cc2 := (nat_z_iso_inv TransportedAssocRight)).
    set (dd := nat_z_iso_comp cc0 (nat_z_iso_comp cc1 cc2)).
    assert (p2' : dd = CategoriesLemmas.pre_whisker_nat_z_iso HHH cc).
    {
      use total2_paths_f.
      2: { apply isaprop_is_nat_z_iso. }

      etrans. {
        apply (! lift_nat_trans_along_comm (_,,Duniv) _ HHH_eso HHH_ff _).
      }

      apply (maponpaths (pre_whisker HHH)).
      apply (maponpaths (lift_nat_trans_along (D,, Duniv) HHH HHH_eso HHH_ff)).
      apply nat_trans_comp_assoc.
      apply homset_property.
    }

    set (cc' := lift_nat_z_iso_along (D,, Duniv) HHH HHH_eso HHH_ff
    (nat_z_iso_comp
       (nat_z_iso_comp TransportedAssocLeft (CategoriesLemmas.post_whisker_nat_z_iso α H))
       (nat_z_iso_inv TransportedAssocRight)) (HHH ((x,y),z))).

    set (cc1' := (CategoriesLemmas.post_whisker_nat_z_iso α H) ((x,y),z)).
    set (cc0' := TransportedAssocLeft ((x,y),z)).
    set (cc2' := (nat_z_iso_inv TransportedAssocRight) ((x,y),z)).
    set (dd' := cc0' · cc1' · cc2').
    assert (p2 : dd' = cc').
    {
      set (q := toforallpaths _ _ _ (base_paths _ _ (base_paths _ _ p2')) ((x,y),z)).
      (* Have to see what goes wrong in here, this should be exactly the same *)
      admit.
    }

    etrans.
    2: {
      do 2 apply maponpaths_2.
      exact p2.
    }
    clear p2.
    unfold dd', cc0', cc1', cc2'.
    clear dd' cc0' cc1' cc2'.
    rewrite ! assoc'.
    apply maponpaths.
    etrans.
    2: {
      apply maponpaths.
      exact (! p1).
    }
    apply (! id_right _).

  Admitted.

  Context {E : category} (Euniv : is_univalent E)
          (TE : functor (E ⊠ E) E)
          (αE : associator TE).

  Context (IE : E).

  Definition precompA
    : disp_functor (precomp_tensorunit_functor Duniv H_eso H_ff TC I TE IE)
                   (functor_ass_disp_cat αD αE)
                   (functor_ass_disp_cat α αE).
  Proof.
    use tpair.
    - use tpair.
      2: intro ; intros ; exact tt.
      exact (λ G GG, functor_ass_composition H_pα GG).
    - split ; intro ; intros ; apply isapropunit.
  Qed.

  Lemma precompA_ff
    : disp_functor_ff precompA.
  Proof.
    intro ; intros.
    apply isweqinclandsurj.
    - do 3 intro.
      assert (p : isaset ( hfiber (λ ff : unit, (# precompA)%mor_disp ff) y0)).
      {
        use isaset_hfiber ; use isasetaprop ; apply isapropunit.
      }
      use tpair.
      + use total2_paths_f.
        { apply isapropunit. }
        use proofirrelevance.
        use hlevelntosn.
        apply isapropunit.
      + intro ; apply p.
    - intro ; intros.
      apply hinhpr.
      exists tt.
      apply isapropunit.
  Qed.

  Lemma precompA_eso
    : disp_functor_disp_ess_split_surj precompA.
  Proof.
    intros G GG.
    unfold functor_tensorunit_cat in G.
    simpl in G.
    unfold functor_ass_disp_cat in GG.

    use tpair.
    - intros d1 d2 d3.
      use factor_through_squash.
      { exact (∑ a : C, z_iso (H a) d1). }
      { apply homset_property. }
      2: exact (H_eso d1).
      intro cd1.
      induction (isotoid _ Duniv (pr2 cd1)).

      use factor_through_squash.
      { exact (∑ a : C, z_iso (H a) d2). }
      { apply homset_property. }
      2: exact (H_eso d2).
      intro cd2.
      induction (isotoid _ Duniv (pr2 cd2)).

      use factor_through_squash.
      { exact (∑ a : C, z_iso (H a) d3). }
      { apply homset_property. }
      2: exact (H_eso d3).
      intro cd3.
      induction (isotoid _ Duniv (pr2 cd3)).

      set (t := GG (pr1 cd1) (pr1 cd2) (pr1 cd3)).

      transparent assert (m : (E⟦ pr1 G (H (TC (pr1 cd1, TC (pr1 cd2,, pr1 cd3))))
                                  ,  (pr11 G) (TD (H (pr1 cd1), TD (H (pr1 cd2),, H (pr1 cd3))))⟧)).
      {
        apply #(pr1 G).


        admit.
      }

      set (tt := cancel_postcomposition _ _ m t).
      refine (_ @ tt @ _).
      + admit.
      + admit.
    - exists tt.
      exists tt.
      split ; apply isapropunit.
  Admitted.

  Definition precomp_associator_is_ff
    : fully_faithful (total_functor precompA).
  Proof.
    use disp_functor_ff_to_total_ff.
    - apply (precomp_tensorunit_is_ff Duniv Euniv).
    - exact precompA_ff.
  Qed.

  Definition precomp_associator_is_eso
    : essentially_surjective (total_functor precompA).
  Proof.
    use disp_functor_eso_to_total_eso.
    - apply (precomp_tensorunit_is_eso Duniv Euniv).
    - exact precompA_eso.
  Qed.

  Definition precomp_associator_adj_equiv
    : adj_equivalence_of_cats (total_functor precompA).
  Proof.
    apply rad_equivalence_of_cats.
    - apply is_univalent_total_category.
      + apply is_univalent_total_category.
        * apply (is_univalent_functor_category _ _ Euniv).
        * apply is_disp_univalent_functor_tensorunit_disp_cat.
      + apply functor_ass_disp_cat_is_univalent.
    - exact precomp_associator_is_ff.
    - exact precomp_associator_is_eso.
  Defined.

End RezkAssociator.