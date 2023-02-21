Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.DaggerCategories.Core.
Require Import UniMath.Bicategories.DaggerCategories.Univalence.
Require Import UniMath.Bicategories.DaggerCategories.Lemmas.
Require Import UniMath.Bicategories.DaggerCategories.BicatOfDaggerCats.
Require Import UniMath.Bicategories.DaggerCategories.Morphisms.Unitary.

Local Open Scope cat.

Section DaggerFunctorCategories.

  Context (C D : DAG).

  Lemma dagger_functor_cat_structure_is_nat_trans
        {F G : hom (C := DAG) C D}
        (α : (hom C D)⟦F,G⟧)
    : is_nat_trans (pr11 G) (pr11 F)
                   (λ c : pr11 C, (pr12 D) (pr11 F c) (pr11 G c) (pr11 α c)).
  Proof.
    induction α as [α t].
    intro ; intros.

    use dagger_injective.
    { exact (pr2 D). }

    etrans.
    1: apply dagger_to_law_comp.
    etrans.
    2: apply pathsinv0, dagger_to_law_comp.

    etrans.
    1: apply maponpaths_2, dagger_to_law_idemp.
    etrans.
    2: apply maponpaths, pathsinv0, dagger_to_law_idemp.

    simpl in F, G.
    etrans.
    1: apply maponpaths, pathsinv0, (pr2 G).
    etrans.
    2: apply maponpaths_2, (pr2 F).
    apply pathsinv0, (pr2 α).
  Qed.

  Definition dagger_functor_cat_structure
    : dagger_structure (hom C D).
  Proof.
    intros F G α.
    use make_dagger_transformation'.
    - exact (λ c, pr12 D _ _ (pr11 α c)).
    - apply dagger_functor_cat_structure_is_nat_trans.
  Defined.

  Lemma dagger_functor_cat_laws : dagger_laws dagger_functor_cat_structure.
  Proof.
    use make_dagger_laws ;
      (intro ; intros ; apply dagger_transformation_equality ; intro).
    - apply dagger_to_law_id.
    - apply dagger_to_law_comp.
    - apply dagger_to_law_idemp.
  Qed.

  Definition dagger_functor_cat : DAG
    := make_dagger_category' dagger_functor_cat_laws.

  Notation "[ C , D ]†" := dagger_functor_cat.

  Definition unitary_functors (F G : ob (pr1 [C,D]† : category))
    : UU
    := ∑ α : nat_trans (pr11 F) (pr11 G),
        (∏ x : pr11 C, Isos.is_inverse_in_precat (α x) ((pr12 D) _ _ (α x))).

  Definition id_to_pr1_id
             (F G : ob (pr1 [C,D]† : category))
    : F = G ≃ pr1 F = pr1 G.
  Proof.
    use subtypeInjectivity.
    intro.
    apply isaprop_is_dagger_functor.
  Defined.

  Definition id_pr1_to_pr11_id
             (F G : ob (pr1 [C,D]† : category))
    : pr1 F = pr1 G ≃ pr11 F = pr11 G.
  Proof.
    use subtypeInjectivity.
    intro.
    apply isaprop_is_functor.
    apply (pr21 D).
  Defined.

  Definition dagger_functor_cat_unitary
             (F G : ob (pr1 [C,D]† : category))
    : unitary_functors F G ≃ unitary dagger_functor_cat_structure F G.
  Proof.
    use weq_iso.
    - intro α.
      exists (make_dagger_transformation (pr1 α) (pr2 F) (pr2 G)).
      split ; apply dagger_transformation_equality ; intro c ; apply (pr2 α c).
    - intro α.
      exists (pr11 α).
      intro c.
      split.
      + exact (toforallpaths _ _ _ (base_paths _ _ (base_paths _ _ (pr12 α))) c).
      + exact (toforallpaths _ _ _ (base_paths _ _ (base_paths _ _ (pr22 α))) c).
    - intro α.
      use total2_paths_f.
      + use (nat_trans_eq (pr21 D)).
        intro ; apply idpath.
      + use proofirrelevance.
        apply impred_isaprop ; intro.
        apply Isos.isaprop_is_inverse_in_precat.
    - intro α.
      use total2_paths_f.
      + apply dagger_transformation_equality.
        intro ; apply idpath.
      + apply isaprop_is_unitary.
  Defined.

  Definition functors_eq_data
             (F G : ob (pr1 [C,D]† : category))
    : UU
    := ∑ p : (∏ x : pr11 C, (pr11 F x) = (pr11 G x)),
        ∏ (x y : pr11 C) (f : (pr11 C)⟦x,y⟧),
        #(pr11 G) f = idtomor _ _ (! p x) · #(pr11 F) f · idtomor _ _ (p y).

  Definition pr11_id_to_explicit
             (u : is_dagger_univalent D)
             (F G : ob (pr1 [C,D]† : category))
    : pr11 F = pr11 G ≃ functors_eq_data F G.
  Proof.

  Admitted.

  Definition unitary_functors_eq
             (F G : ob (pr1 [C,D]† : category))
    : UU
    := ∑ p : (∏ x : pr11 C, unitary (pr12 D) (pr11 F x) (pr11 G x)),
        ∏ (x y : pr11 C) (f : (pr11 C)⟦x,y⟧),
        #(pr11 G) f = (pr12 D _ _ (pr1 (p x))) · #(pr11 F) f · (pr1 (p y)).

  Lemma TODO_JOKER (A : UU) : A. Proof. Admitted.
  Definition pr11_id_to_unitary_functors_eq
             (u : is_dagger_univalent D)
             (F G : ob (pr1 [C,D]† : category))
    : functors_eq_data F G ≃ unitary_functors_eq F G.
  Proof.
    use weq_iso.
    - intro p.
      exists (λ c, idtodaggeriso (pr2 D) _ _ (pr1 p c)).
      intros x y f.
      unfold functors_eq_data in p.
      refine (pr2 p x y f @ _).
      apply TODO_JOKER.
    - intros p.
      use tpair.
      + intro c ; apply u ; exact (pr1 p c).
      + intros x y f.
        refine (pr2 p x y f @ _).
        cbn.
        apply TODO_JOKER.
    - intro p.
      use total2_paths_f.
      + cbn.
        apply funextsec ; intro c.
        apply TODO_JOKER.
      + repeat (apply funextsec ; intro).
        apply homset_property.
    - intro p.
      use total2_paths_f.
      + cbn.
        apply funextsec ; intro c.
        use total2_paths_f.
        * apply TODO_JOKER.
        * apply isaprop_is_unitary.
      + repeat (apply funextsec ; intro).
        apply homset_property.
  Defined.

  Definition pr11_id_to_unitary_functors
             (u : is_dagger_univalent D)
             (F G : ob (pr1 [C,D]† : category))
    : pr11 F = pr11 G ≃ unitary_functors F G.
  Proof.
    use weq_iso.
    - intro p.
      use tpair.
      + induction p.
        apply nat_trans_id.
      + abstract (intro c ; split ; induction p ;
                [ refine (id_left _ @ _) ; apply dagger_to_law_id
                | refine (id_right _ @ _) ; apply dagger_to_law_id ]).
    - intro α.
      use total2_paths_f.
      + apply funextsec ; intro c.
        apply u.
        exists (pr1 α c).
        abstract (split ; apply (pr2 α c)).
      + repeat (apply funextsec ; intro).
        apply TODO_JOKER.
    - intro x.
      cbn.
      apply TODO_JOKER.
    - cbn.
      intro α.
      unfold unitary_functors in α.

      use total2_paths_f.
      2: {
        use proofirrelevance.
        apply impred_isaprop ; intro.
        apply Isos.isaprop_is_inverse_in_precat.
      }

      use nat_trans_eq.
      { apply homset_property. }
      intro c.
      apply TODO_JOKER.
  Defined.

  Lemma dagger_functor_cat_is_dagger_univalent
        (u : is_dagger_univalent D)
    : is_dagger_univalent [C,D]†.
  Proof.
    intros F G.
    use weqhomot.
    - exact (dagger_functor_cat_unitary F G ∘ pr11_id_to_unitary_functors u F G ∘ id_pr1_to_pr11_id F G ∘ id_to_pr1_id F G)%weq.
    - intro p.
      induction p.

      use total2_paths_f.
      2: apply isaprop_is_unitary.
      apply idpath.
  Qed.

End DaggerFunctorCategories.
