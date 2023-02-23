(* Any groupoid becomes a †-category by defining f^† := f^-1 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.Bicategories.DaggerCategories.Core.
Require Import UniMath.Bicategories.DaggerCategories.Univalence.
Require Import UniMath.Bicategories.DaggerCategories.Morphisms.Unitary.
Require Import UniMath.Bicategories.DaggerCategories.Lemmas.

Local Open Scope cat.

Lemma z_iso_inv_eq {C : category} {x y : C}
      (f : C⟦x,y⟧) (g h : C⟦y,x⟧)
  : is_inverse_in_precat f g -> is_inverse_in_precat f h -> g = h.
Proof.
  intros pg ph.
  apply (inv_z_iso_unique' _ _ _ (f ,, h ,, ph)).
  apply pg.
Qed.

Section GroupoidsAsDaggers.

  Context (C : groupoid).

  Definition GRP_dagger_structure : dagger_structure C.
  Proof.
    intros x y f.
    exact (pr1 (z_iso_inv (_ ,, pr2 C x y f))).
  Defined.

  Lemma GRP_dagger_laws : dagger_laws GRP_dagger_structure.
  Proof.
    repeat split ; intro ; intros ; use z_iso_inv_eq.
    - exact (identity x).
    - apply (pr2 C).
    - apply is_inverse_in_precat_identity.
    - exact (f · g).
    - apply (pr2 C).
    - apply is_inverse_in_precat_comp ; apply (pr2 C).
    - apply (pr2 C x y f).
    - apply (pr2 C).
    - apply is_inverse_in_precat_inv ; apply (pr2 C).
  Qed.

  Definition GRP_dagger : dagger C
    := _ ,, GRP_dagger_laws.

End GroupoidsAsDaggers.

Section UnivalenceOfGroupoids.

  Context (C : groupoid).

  Definition univalence_to_dagger_univalence
        {x y : C} (f : z_iso x y)
    : unitary (GRP_dagger C) x y.
  Proof.
    exists (morphism_from_z_iso _ _ f).
    apply (pr2 C x y f).
  Defined.

  Definition dagger_univalence_to_univalence
             {x y : C} (f : unitary (GRP_dagger C) x y)
    : z_iso x y
    := make_z_iso _ _ (pr2 f).

  Definition z_iso_is_unitary (x y : C)
    : z_iso x y ≃ unitary (GRP_dagger C) x y.
  Proof.
    use weq_iso.
    - exact (λ p, univalence_to_dagger_univalence p).
    - exact (λ p, dagger_univalence_to_univalence p).
    - intro ; apply z_iso_eq, idpath.
    - intro ; apply unitary_eq, idpath.
  Defined.

  Lemma idtodagger_as_idtoiso_pointwise {x y : C} (p : x = y)
    : idtodaggeriso (GRP_dagger C) x y p = z_iso_is_unitary x y (Univalence.idtoiso p).
  Proof.
    apply (unitary_eq (idtodaggeriso (GRP_dagger C) x y p) (univalence_to_dagger_univalence (Univalence.idtoiso p))).
    induction p ; apply idpath.
  Defined.

  Lemma idtoiso_as_idtodagger_pointwise {x y : C} (p : x = y)
    : Univalence.idtoiso p = dagger_univalence_to_univalence (idtodaggeriso (GRP_dagger C) x y p).
  Proof.
    apply (z_iso_eq (Univalence.idtoiso p) (dagger_univalence_to_univalence (idtodaggeriso (GRP_dagger C) x y p))).
    induction p ; apply idpath.
  Defined.

  Definition groupoid_univalence_equiv_dagger_univalence
    : Univalence.is_univalent C ≃ is_univalent_dagger (GRP_dagger C).
  Proof.
    use weqimplimpl.
    - intros u x y.
      apply (isweqhomot' (λ p, z_iso_is_unitary x y (Univalence.idtoiso p))).
      + apply (twooutof3c (Univalence.idtoiso (a := x) (b := y)) (z_iso_is_unitary x y)).
        * apply u.
        * apply z_iso_is_unitary.
      + apply (λ p, ! idtodagger_as_idtoiso_pointwise p).
    - intros u x y.
      apply (isweqhomot' (λ p, invweq (z_iso_is_unitary x y) (idtodaggeriso (GRP_dagger C) _ _ p))).
      + apply (twooutof3c (idtodaggeriso (GRP_dagger C) x y) (invweq (z_iso_is_unitary x y))).
        * apply u.
        * apply (invweq (z_iso_is_unitary _ _)).
      + apply (λ p, ! idtoiso_as_idtodagger_pointwise p).
    - apply Univalence.isaprop_is_univalent.
    - apply isaprop_is_univalent_dagger.
  Qed.

End UnivalenceOfGroupoids.
