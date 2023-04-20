Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws. (* There is a possibility that this one will not be used, hence could be removed. However, this is currently in this file because of search reasons. *)


Local Open Scope cat.

Local Definition fam_of_mor (B : bicat) : UU
  := ∏ x y : B, hom x y -> hProp.

Section FactorizationOfMorphism.

  Context {B : bicat}.

  Definition factorization
    {x y : B} (f : hom x y)
    : UU
    := ∑ z : B,
        ∑ f1 : hom x z, ∑ f2 : hom z y,
            invertible_2cell f (f1 · f2).

  Definition factorization_ob
    {x y : B} {f : hom x y}
    (ff : factorization f) : B
    := pr1 ff.
  Coercion factorization_ob : factorization >-> ob.

  Definition factorization_mor_l
    {x y : B} {f : hom x y}
    (ff : factorization f)
    : hom x ff
    := pr12 ff.

  Definition factorization_mor_r
    {x y : B} {f : hom x y}
    (ff : factorization f)
    : hom ff y
    := pr122 ff.

  Definition factorization_inv_2cell
    {x y : B} {f : hom x y}
    (ff : factorization f)
    : invertible_2cell f (factorization_mor_l ff · factorization_mor_r ff)
    := pr222 ff.

End FactorizationOfMorphism.

Local Definition factorization_system (B : bicat)
  : UU
  := ∏ (x y : B) (f : hom x y), factorization f.

Section Lifting.

  Context {B : bicat}.

  Local Definition comm_square
    {x1 x2 y1 y2 : B} (i : B⟦x1,x2⟧) (j : B⟦y1,y2⟧) : UU
    := ∑ (f1 : B⟦x1,y1⟧) (f2 : B⟦x2,y2⟧),
      invertible_2cell (f1 · j) (i · f2).


  Definition mor_has_LLP_against

End Lifting.

Section WFS.

  Context (B : bicat).

  Definition WFS_data : UU
    := fam_of_mor B × fam_of_mor B.

  Definition WFS_L (wfs : WFS_data) : fam_of_mor B := pr1 wfs.
  Definition WFS_R (wfs : WFS_data) : fam_of_mor B := pr2 wfs.

  Notation "L_{ wfs }" := (WFS_L wfs).
  Notation "R_{ wfs }" := (WFS_R wfs).

  Definition make_WFS_data
    (L R : fam_of_mor B)
    : WFS_data := L ,, R.

  Definition WFS_factorization
    (wfs : WFS_data) : UU
    := ∑ fact : factorization_system B,
        ∏ x y : B, ∏ f : hom x y,
            L_{wfs} _ _ (factorization_mor_l (fact _ _ f))
              × R_{wfs} _ _ (factorization_mor_r (fact _ _ f)).

  Definition WFS_lifting
    (wfs : WFS_data) : UU
    := has_LRP_against L_{wfs} R_{wfs}.
