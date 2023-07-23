(*********************************************************************************

 Displayed symmetric monoidal categories

 In this file, we define the notion of a symmetric displayed monoidal category and show how the total monoidal category is symmetric.

 *********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.

Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Import BifunctorNotations.
Import MonoidalNotations.
Import DisplayedBifunctorNotations.
Import DisplayedMonoidalNotations.

Lemma disp_tensor_distributes_over_transportb_right
  {C : category}
  {D : disp_cat C}
  {M : monoidal C}
  (DM : disp_monoidal D M)
  {x y z : C}
  {f g : y --> z}
  (p : f = g)
  (xx : D x)
  {yy : D y}
  {zz : D z}
  (ff : yy -->[f] zz)
  (gg : yy -->[g] zz)
  : ff = transportb _ p gg
    -> xx ⊗⊗^{DM}_{l} transportb _ p ff
    = transportb _ (maponpaths  (leftwhiskering_on_morphisms M x y z) p) (xx ⊗⊗^{DM}_{l} gg).
Proof.
  induction p.
  intro q.
  cbn.
  apply maponpaths.
  exact q.
Qed.

Lemma disp_tensor_distributes_over_transportb_left
  {C : category}
  {D : disp_cat C}
  {M : monoidal C}
  (DM : disp_monoidal D M)
  {x y z : C}
  {f g : y --> z}
  (p : f = g)
  (xx : D x)
  {yy : D y}
  {zz : D z}
  (ff : yy -->[f] zz)
  (gg : yy -->[g] zz)
  : ff = transportb _ p gg
    -> transportb _ p ff ⊗⊗^{DM}_{r} xx
    = transportb _ (maponpaths  (rightwhiskering_on_morphisms M _ _ _) p) (gg ⊗⊗^{DM}_{r} xx).
Proof.
  induction p.
  intro q.
  cbn.
  apply maponpaths.
  exact q.
Qed.

Lemma disp_tensor_with_id_left
  {C : category}
  {D : disp_cat C}
  {M : monoidal C}
  (DM : disp_monoidal D M)
  {x y z : C}
  {f : z --> y}
  {g : y --> z}
  (p : g · f = identity y)
  (xx : D x)
  (yy : D y)
  : xx ⊗⊗^{DM}_{l} transportb (mor_disp _ _) p (id_disp yy)
    = transportb _ (maponpaths (λ i, x ⊗^{M}_{l} i) p @ bifunctor_leftid M x y) (id_disp (xx ⊗⊗_{DM} yy)).
Proof.
  set (pp := disp_tensor_distributes_over_transportb_right DM p xx (transportb _ p (id_disp yy)) (id_disp yy) (idpath _)).

  rewrite <- transport_b_b.
  etrans.
  2: {
    apply maponpaths.
    apply (disp_bifunctor_leftid DM _ _ xx yy).
  }
  refine (_ @ pp).
  apply maponpaths.
  now rewrite transportb_const.
Qed.

Lemma disp_tensor_with_id_right
  {C : category}
  {D : disp_cat C}
  {M : monoidal C}
  (DM : disp_monoidal D M)
  {x y z : C}
  {f : z --> y}
  {g : y --> z}
  (p : g · f = identity y)
  (xx : D x)
  (yy : D y)
  : transportb (mor_disp _ _) p (id_disp yy)  ⊗⊗^{DM}_{r} xx
    = transportb _ (maponpaths (λ i, i ⊗^{M}_{r} x) p @ bifunctor_rightid M x y) (id_disp (yy ⊗⊗_{DM} _)).
Proof.
  Proof.
  set (pp := disp_tensor_distributes_over_transportb_left DM p xx (transportb _ p (id_disp yy)) (id_disp yy) (idpath _)).

  rewrite <- transport_b_b.
  etrans.
  2: {
    apply maponpaths.
    apply (disp_bifunctor_rightid DM _ _ _ _).
  }
  refine (_ @ pp).
  apply maponpaths.
  now rewrite transportb_const.
Qed.

Definition disp_z_iso_inv_on_left
  {C : category}
  {D : disp_cat C}
  {x y z : C}
  {f : x --> y}
  {g : y --> z}
  {h : x --> z}
  (Hf : is_z_isomorphism f)
  {xx : D x}
  {yy : D y}
  {zz : D z}
  {ff : xx -->[ f ] yy}
  {gg : yy -->[ g ] zz}
  {hh : xx -->[ h ] zz}
  (Hff : is_z_iso_disp (f ,, Hf) ff)
  (p : f · g = h)
  : gg = transportf _ (z_iso_inv_on_right _ _ _ (f,,Hf) g h (! p)) (pr1 Hff ;; hh)
  -> ff ;; gg = transportb _ p hh.
Proof.
  intro q.
  rewrite q.
  clear q.
  rewrite mor_disp_transportf_prewhisker.
  use transportf_transpose_right.
  unfold transportb.
  rewrite transport_f_f.
  rewrite assoc_disp.
  unfold transportb.
  rewrite transport_f_f.
  etrans. {
    apply maponpaths.
    apply maponpaths_2.
    exact (pr22 Hff).
  }
  unfold transportb.
  rewrite mor_disp_transportf_postwhisker.
  rewrite transport_f_f.

  etrans. {
    apply maponpaths_2.
    refine (_ @ idpath (id_left _)).
    apply homset_property.
  }
  apply pathsinv0, id_left_disp_var.
Qed.

Definition disp_z_iso_inv_on_right
  {C : category}
  {D : disp_cat C}
  {x y z : C}
  {f : x --> y}
  {g : y --> z}
  {h : x --> z}
  (Hg : is_z_isomorphism g)
  {xx : D x}
  {yy : D y}
  {zz : D z}
  {ff : xx -->[ f ] yy}
  {gg : yy -->[ g ] zz}
  {hh : xx -->[ h ] zz}
  (Hgg : is_z_iso_disp (g ,, Hg) gg)
  (p : f · g = h)
  : ff = transportb _ (z_iso_inv_on_left _ _ _ f (g,,Hg) h (! p)) (hh ;; pr1 Hgg)
  -> ff ;; gg = transportb _ p hh.
Proof.
  intro q.
  rewrite q.
  clear q.
  unfold transportb.
  rewrite mor_disp_transportf_postwhisker.
  use transportf_transpose_right.
  unfold transportb.
  rewrite transport_f_f.
  rewrite assoc_disp_var.
  rewrite transport_f_f.
  etrans. {
    do 2 apply maponpaths.
    exact (pr12 Hgg).
  }
  unfold transportb.
  rewrite mor_disp_transportf_prewhisker.
  rewrite transport_f_f.

  etrans. {
    apply maponpaths_2.
    refine (_ @ idpath (id_right _)).
    apply homset_property.
  }
  apply pathsinv0, id_right_disp_var.
Qed.

Lemma disp_tensor_with_id_on_right
  {C : category} {D : disp_cat C}
  {M : monoidal C} {DM : disp_monoidal D M}
  {x y z : C}
  {f : C⟦x, y⟧}
  {xx : D x} {yy : D y} {zz : D z}
  (ff : xx -->[f] yy)
  : ff ⊗⊗^{ DM} id_disp zz
    = transportb _ (when_bifunctor_becomes_rightwhiskering M z f) (ff ⊗⊗^{ DM}_{r} zz).
Proof.
  unfold dispfunctoronmorphisms1.
  etrans. {
    apply maponpaths.
    apply disp_bifunctor_leftid.
  }
  etrans. {
    apply mor_disp_transportf_prewhisker.
  }
  use transportf_transpose_left.
  rewrite transport_b_b.
  etrans. {
    apply id_right_disp.
  }
  apply maponpaths_2.
  apply homset_property.
Qed.

Lemma disp_tensor_with_id_on_left
  {C : category} {D : disp_cat C}
  {M : monoidal C} {DM : disp_monoidal D M}
  {x y z : C}
  {f : C⟦x, y⟧}
  {xx : D x} {yy : D y} {zz : D z}
  (ff : xx -->[f] yy)
  : id_disp zz ⊗⊗^{ DM} ff
    = transportb _ (when_bifunctor_becomes_leftwhiskering M z f) (zz ⊗⊗^{ DM}_{l} ff).
Proof.
  unfold dispfunctoronmorphisms1.
  etrans. {
    apply maponpaths_2.
    apply disp_bifunctor_rightid.
  }
  etrans. {
    apply mor_disp_transportf_postwhisker.
  }
  use transportf_transpose_left.
  rewrite transport_b_b.
  etrans. {
    apply id_left_disp.
  }
  apply maponpaths_2.
  apply homset_property.
Qed.

Local Lemma specialized_transport_lemma
  {C : category} {D : disp_cat C}
  {M : monoidal C} {DM : disp_monoidal D M}
  {x y z1 z2 : C}
  {f : C⟦x,y ⊗_{M} z1⟧}
  {g : C⟦z1, z2⟧}
  {h : C⟦x, y ⊗_{M} z2⟧}
  {xx : D x} {yy : D y} {zz1 : D z1} {zz2 : D z2}
  (ff : xx -->[f] (yy ⊗⊗_{DM} zz1))
  (gg : zz1 -->[g] zz2)
  (hh : xx -->[h] (yy ⊗⊗_{DM} zz2))
  (p : h = f · identity y ⊗^{ M} g)
  : ff ;; (id_disp yy ⊗⊗^{DM} gg) = transportf _ p hh
    → ff ;; yy ⊗⊗^{DM}_{l} gg
      = transportf _ (p @ maponpaths (λ i, f · i) (when_bifunctor_becomes_leftwhiskering M y g)) hh.
Proof.
  intro q.
  rewrite <- transport_f_f.
  etrans.
  2: {
    apply maponpaths.
    exact q.
  }
  clear q.
  etrans.
  2: {
    apply mor_disp_transportf_prewhisker.
  }
  apply maponpaths.

  unfold dispfunctoronmorphisms1.
  use transportf_transpose_right.
  apply pathsinv0, disp_tensor_with_id_on_left.
Qed.

Local Lemma specialized_transport_lemma'
  {C : category} {D : disp_cat C}
  {M : monoidal C} {DM : disp_monoidal D M}
  {x y z1 z2 : C}
  {f : C⟦x,y⟧}
  {g : C⟦y ⊗_{M} z1, z2⟧}
  {h : C⟦x ⊗_{M} _, z2⟧}
  {xx : D x} {yy : D y} {zz1 : D z1} {zz2 : D z2}
  (ff : xx -->[f] yy)
  (gg : yy ⊗⊗_{DM} zz1 -->[g] zz2)
  (hh : xx ⊗⊗_{DM} _ -->[h] zz2)
  (p : h = f ⊗^{ M} identity z1 · g)
  : (ff ⊗⊗^{DM} id_disp _) ;; gg = transportf _ p hh
    → ff ⊗⊗^{DM}_{r} _ ;; gg
      = transportf _ (p @ maponpaths (λ i, i · g) (when_bifunctor_becomes_rightwhiskering M z1 f)) hh.
Proof.
  intro q.
  rewrite <- transport_f_f.
  etrans.
  2: {
    apply maponpaths.
    exact q.
  }
  etrans.
  2: {
    apply mor_disp_transportf_postwhisker.
  }
  apply maponpaths_2.
  unfold dispfunctoronmorphisms1.
  use transportf_transpose_right.
  apply pathsinv0, disp_tensor_with_id_on_right.
Qed.

Lemma precomp_disp_id_left_inj
{C : category} {D : disp_cat C}
  {y z : C}
  {f : C⟦y,z⟧}
  {yy : D y} {zz : D z}
  (ff1 ff2 : yy -->[f] zz)
  : id_disp yy ;; ff1 = id_disp yy ;; ff2 → ff1 = ff2.
Proof.
  intro p.
  rewrite ! id_left_disp in p.
  refine (transportb_transpose_right p @ _).
  rewrite transport_b_b.
  use transportf_set.
  apply homset_property.
Qed.

Section DisplayedBraided.

  Context
    {C : category}
    {D : disp_cat C}
    {M : monoidal C}
    (DM : disp_monoidal D M).

  Definition disp_braiding_data
    (B : braiding_data M) : UU
    := ∏ (x y : C) (xx : D x) (yy : D y),
      xx ⊗⊗_{ DM} yy -->[B x y] yy ⊗⊗_{ DM} xx.

  Definition total_braiding_data
    {B : braiding_data M} (DB : disp_braiding_data B)
    : braiding_data (total_monoidal DM)
    := λ x y, _ ,, DB _ _ (pr2 x) (pr2 y).

  Section BraidingLaws.

    Context
      {B : braiding M}
        (DB : disp_braiding_data (monoidal_braiding_data B))
        (DBinv : disp_braiding_data (monoidal_braiding_data_inv B)).

    Definition disp_braiding_law_naturality_left : UU
      := ∏ (x y1 y2 : C)
          (xx : D x) (yy1 : D y1) (yy2 : D y2)
          (g : C⟦y1,y2⟧) gg,
        transportf _ (monoidal_braiding_naturality_left B x y1 y2 g)
          (DB x y1 xx yy1 ;; gg ⊗⊗^{ DM}_{r} xx)
        = xx ⊗⊗^{ DM}_{l} gg ;; DB x y2 xx yy2.

    Definition disp_braiding_law_naturality_right : UU
      := ∏ (x1 x2 y : C)
          (xx1 : D x1) (xx2 : D x2) (yy : D y)
          (f : C⟦x1,x2⟧) ff,
    transportf _ (monoidal_braiding_naturality_right B x1 x2 y f)
      (DB x1 y xx1 yy ;; yy ⊗⊗^{ DM}_{l} ff)
    = ff ⊗⊗^{ DM}_{r} yy ;; DB x2 y xx2 yy.

    Definition disp_braiding_law_naturality
      : UU
      := disp_braiding_law_naturality_left × disp_braiding_law_naturality_right.

    Definition disp_braiding_iso
      : UU
      := ∏ (x y : C) (xx : D x) (yy : D y),
        is_disp_inverse (monoidal_braiding_inverses B x y) (DB _ _ xx yy) (DBinv _ _ yy xx).

    Definition disp_braiding_law_hexagon1 : UU
      := ∏ (x y z : C) (xx : D x) (yy : D y) (zz : D z),
        transportf _ ((pr122 (monoidal_braiding_laws B)) x y z)
          (dα^{ DM }_{ xx, yy, zz}
           ;; DB x (y ⊗_{ M} z) xx (yy ⊗⊗_{ DM} zz)
           ;; dα^{ DM }_{ yy, zz, xx})
        = DB x y xx yy ⊗⊗^{ DM}_{r} zz
          ;; dα^{ DM }_{ yy, xx, zz}
          ;; yy ⊗⊗^{ DM}_{l} DB x z xx zz.

    Definition disp_braiding_law_hexagon2 : UU
      := ∏ (x y z : C) (xx : D x) (yy : D y) (zz : D z),
         transportf _ ((pr222 (monoidal_braiding_laws B)) x y z)
           (dαinv^{DM}_{xx, yy, zz}
            ;; DB (x ⊗_{M} y) z (xx ⊗⊗_{DM} yy) zz
            ;; dαinv^{DM}_{zz, xx, yy})
         = xx ⊗⊗^{DM}_{l} DB y z yy zz
           ;; dαinv^{DM}_{xx, zz, yy}
           ;; DB x z xx zz ⊗⊗^{DM}_{r} yy.

    Definition disp_braiding_law_hexagon : UU
      := disp_braiding_law_hexagon1 × disp_braiding_law_hexagon2.

    Definition disp_braiding_laws
      : UU
      := disp_braiding_law_naturality
         × disp_braiding_iso
         × disp_braiding_law_hexagon.

  End BraidingLaws.

  Definition disp_braiding
    (B : braiding M) : UU
    := ∑ (DB : disp_braiding_data (monoidal_braiding_data B))
         (DBinv : disp_braiding_data (monoidal_braiding_data_inv B)),
      disp_braiding_laws DB DBinv.

  Definition disp_braiding_to_braiding
    {B : braiding M}
    (DB : disp_braiding B)
    : disp_braiding_data (monoidal_braiding_data B)
    := pr1 DB.

  Definition disp_braiding_to_braiding_inv
    {B : braiding M}
    (DB : disp_braiding B)
    : disp_braiding_data (monoidal_braiding_data_inv B)
    := pr12 DB.

  Definition disp_braiding_to_braiding_laws
    {B : braiding M}
    (DB : disp_braiding B)
    : disp_braiding_laws (disp_braiding_to_braiding DB) (disp_braiding_to_braiding_inv DB)
    := pr22 DB.

  Definition disp_braiding_to_naturality
    {B : braiding M}
    (DB : disp_braiding B)
    : disp_braiding_law_naturality (disp_braiding_to_braiding DB)
    := pr1 (disp_braiding_to_braiding_laws DB).

  Definition disp_braiding_to_naturality_left
    {B : braiding M}
    (DB : disp_braiding B)
    : disp_braiding_law_naturality_left (disp_braiding_to_braiding DB)
    := pr1 (disp_braiding_to_naturality DB).

  Definition disp_braiding_to_naturality_right
    {B : braiding M}
    (DB : disp_braiding B)
    : disp_braiding_law_naturality_right (disp_braiding_to_braiding DB)
    := pr2 (disp_braiding_to_naturality DB).

  Definition disp_braiding_to_inverses
    {B : braiding M}
    (DB : disp_braiding B)
    : disp_braiding_iso (disp_braiding_to_braiding DB) (disp_braiding_to_braiding_inv DB)
    := pr12 (disp_braiding_to_braiding_laws DB).

  Definition disp_braiding_to_hexagon
    {B : braiding M}
    (DB : disp_braiding B)
    : disp_braiding_law_hexagon (disp_braiding_to_braiding DB)
    := pr22 (disp_braiding_to_braiding_laws DB).

  Definition disp_braiding_to_hexagon1
    {B : braiding M}
    (DB : disp_braiding B)
    : disp_braiding_law_hexagon1 (disp_braiding_to_braiding DB)
    := pr1 (disp_braiding_to_hexagon DB).

  Definition disp_braiding_to_hexagon2
    {B : braiding M}
    (DB : disp_braiding B)
    : disp_braiding_law_hexagon2 (disp_braiding_to_braiding DB)
    := pr2 (disp_braiding_to_hexagon DB).

  Lemma total_braiding_naturality_left
    {B : braiding M}
    (DB : disp_braiding B)
    : braiding_law_naturality_left (total_braiding_data (disp_braiding_to_braiding DB)).
  Proof.
    intro ; intros.
    use total2_paths_f.
    - apply monoidal_braiding_naturality_left.
    - apply disp_braiding_to_naturality_left.
  Qed.

  Lemma total_braiding_naturality_right
    {B : braiding M}
    (DB : disp_braiding B)
    : braiding_law_naturality_right (total_braiding_data (disp_braiding_to_braiding DB)).
  Proof.
    intro ; intros.
    use total2_paths_f.
    - apply monoidal_braiding_naturality_right.
    - apply disp_braiding_to_naturality_right.
  Qed.

  Lemma total_braiding_naturality
    {B : braiding M}
    (DB : disp_braiding B)
    : braiding_law_naturality (total_braiding_data (disp_braiding_to_braiding DB)).
  Proof.
    exists (total_braiding_naturality_left DB).
    exact (total_braiding_naturality_right DB).
  Qed.

  Lemma total_braiding_iso
    {B : braiding M}
    (DB : disp_braiding B)
    : braiding_iso
        (total_braiding_data (disp_braiding_to_braiding DB))
        (total_braiding_data (disp_braiding_to_braiding_inv DB)).
  Proof.
    intros [x xx] [y yy].
    set (i := is_z_iso_total
      (total_braiding_data (disp_braiding_to_braiding DB) (x,, xx) (y,, yy))
      (_,, monoidal_braiding_inverses B x y : is_z_isomorphism (pr1 B x y))).
    exact (pr2 (i (_ ,, disp_braiding_to_inverses DB _ _ xx yy))).
  Qed.

  Lemma total_braiding_hexagon1
    {B : braiding M}
    (DB : disp_braiding B)
    : braiding_law_hexagon1 (total_braiding_data (disp_braiding_to_braiding DB)).
  Proof.
    intro ; intros.
    use total2_paths_f.
    - apply (pr122 (monoidal_braiding_laws B)).
    - apply disp_braiding_to_hexagon1.
  Qed.

  Lemma total_braiding_hexagon2
    {B : braiding M}
    (DB : disp_braiding B)
    : braiding_law_hexagon2 (total_braiding_data (disp_braiding_to_braiding DB)).
  Proof.
    intro ; intros.
    use total2_paths_f.
    - apply (pr222 (monoidal_braiding_laws B)).
    - cbn. apply disp_braiding_to_hexagon2.
  Qed.

  Lemma total_braiding_hexagon
    {B : braiding M}
    (DB : disp_braiding B)
    : braiding_law_hexagon (total_braiding_data (disp_braiding_to_braiding DB)).
  Proof.
    exists (total_braiding_hexagon1 DB).
    exact (total_braiding_hexagon2 DB).
  Qed.

  Lemma total_braiding_laws
    {B : braiding M}
    (DB : disp_braiding B)
    : braiding_laws
        (total_braiding_data (disp_braiding_to_braiding DB))
        (total_braiding_data (disp_braiding_to_braiding_inv DB)).
  Proof.
    refine (_,,_,,_).
    - exact (total_braiding_naturality DB).
    - exact (total_braiding_iso DB).
    - exact (total_braiding_hexagon DB).
  Qed.

  Definition total_braiding
    {B : braiding M}
    (DB : disp_braiding B)
    : braiding (total_monoidal DM).
  Proof.
    simple refine (_,,_,,_).
    - exact (total_braiding_data (disp_braiding_to_braiding DB)).
    - exact (total_braiding_data (disp_braiding_to_braiding_inv DB)).
    - exact (total_braiding_laws DB).
  Defined.

End DisplayedBraided.

Section DisplayedSymmetric.

  Context {C : category}
    {D : disp_cat C}
    {M : monoidal C}
    (DM : disp_monoidal D M).

  Definition disp_symmetric (B : symmetric M) : UU
    := ∑ DB : disp_braiding_data DM B, disp_braiding_laws _ DB DB.

  Definition disp_symmetric_to_braiding
    {B : symmetric M}
    (DB : disp_symmetric B)
    : disp_braiding DM (symmetric_to_braiding B).
  Proof.
    exists (pr1 DB).
    exists (pr1 DB).
    exact (pr2 DB).
  Defined.

  Coercion disp_symmetric_to_braiding : disp_symmetric >-> disp_braiding.

  Definition total_symmetric
    {B : symmetric M}
    (DB : disp_symmetric B)
    : symmetric (total_monoidal DM).
  Proof.
    exists (total_braiding_data _ (pr1 DB)).
    exact (total_braiding_laws _ DB).
  Defined.

  Definition disp_sym_moncat_laws_tensored_inv
    {B : symmetric M}
    (c : ∏ (x y : C) (xx : D x) (yy : D y),
        xx ⊗⊗_{ DM} yy -->[pr1 B x y] yy ⊗⊗_{ DM} xx)
    : UU
    := ∏ (x y : C) (xx : D x) (yy : D y),
         transportf _ (pr1 (monoidal_braiding_inverses B x y)) (c x y xx yy ;; c y x yy xx)
         = id_disp (xx ⊗⊗_{DM} yy).

  Definition disp_sym_moncat_laws_tensored_nat
    {B : symmetric M}
    (c : ∏ (x y : C) (xx : D x) (yy : D y),
        xx ⊗⊗_{ DM} yy -->[pr1 B x y] yy ⊗⊗_{ DM} xx)
    : UU
    := ∏ (x1 x2 y1 y2 : C) (f : C⟦x1, x2⟧) (g : C⟦y1, y2⟧)
         (xx1 : D x1) (xx2 : D x2) (yy1 : D y1) (yy2 : D y2)
         (ff : xx1 -->[f] xx2) (gg : yy1 -->[g] yy2),
      transportf _ (tensor_sym_mon_braiding ((C,,M),,B) f g)
        (ff ⊗⊗^{DM} gg ;; c x2 y2 xx2 yy2)
      = c x1 y1 xx1 yy1 ;; gg ⊗⊗^{DM} ff.

  Definition disp_sym_moncat_laws_tensored_hex
               {B : symmetric M}
    (c : ∏ (x y : C) (xx : D x) (yy : D y),
        xx ⊗⊗_{ DM} yy -->[pr1 B x y] yy ⊗⊗_{ DM} xx)
    : UU
    := ∏ (x y z : C) (xx : D x) (yy : D y) (zz : D z),
      transportf _ (sym_mon_hexagon_lassociator ((C,,M),,B) x y z)
        (disp_monoidal_associator _ _ _ _ xx yy zz
      ;; c _ _ xx (yy ⊗⊗_{DM} zz)
      ;; disp_monoidal_associator _ _ _ _ yy zz xx)
      = c x y xx yy  ⊗⊗^{DM} id_disp zz
        ;; disp_monoidal_associator _ _ _ _ yy xx zz
        ;; id_disp yy ⊗⊗^{DM} c x z xx zz.

  Definition disp_symm_braiding_laws
    {B : symmetric M}
    (c : ∏ (x y : C) (xx : D x) (yy : D y),
        xx ⊗⊗_{ DM} yy -->[pr1 B x y] yy ⊗⊗_{ DM} xx)
    : UU
    := disp_sym_moncat_laws_tensored_inv c
         × disp_sym_moncat_laws_tensored_nat c
         × disp_sym_moncat_laws_tensored_hex c.

  Definition braiding_laws_one_hexagon_to_braiding_laws
    {B : symmetric M}
    {c : disp_braiding_data DM B}
    (p_inv : disp_braiding_iso DM c c)
    (p_nat : disp_braiding_law_naturality DM c)
    (p_hex1 : disp_braiding_law_hexagon1 DM c)
    : disp_braiding_law_hexagon2 DM c.
  Proof.
    intro ; intros.
    set (p := transportb_transpose_right (p_hex1 _ _ _ zz xx yy)).

    rewrite assoc_disp_var.
    rewrite transport_f_f.
    use transportf_transpose_left.
    use disp_z_iso_inv_on_left.
    { exact (pr2 (z_iso_inv (z_iso_from_associator_iso M x y z))). }
    {
      set (t := disp_monoidal_associatoriso DM _ _ _ xx yy zz).
      exact (_ ,, (pr2 t,, pr1 t)).
    }
    etrans.
    2: {
      apply maponpaths_2.
      apply pathsinv0inv0.
    }

    use disp_z_iso_inv_on_left.
    {
      refine (_,,_).
      apply (pr122 B).
    }
    {
      refine (_ ,, _).
      apply p_inv.
    }
    refine (id_right_disp_var _ @ _).
    use transportf_transpose_left.

    use disp_z_iso_inv_on_left.
    { exact (pr2 (z_iso_inv (z_iso_from_associator_iso M z x y))). }
    {
      set (t := disp_monoidal_associatoriso DM _ _ _ zz xx yy).
      exact (_ ,, (pr2 t,, pr1 t)).
    }
    cbn.
    rewrite mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    apply pathsinv0.
    rewrite assoc_disp.
    rewrite assoc_disp.
    unfold transportb.
    rewrite ! transport_f_f.
    etrans. {
      apply maponpaths.
      apply maponpaths_2.
      exact p.
    }
    clear p.
    cbn.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    rewrite ! assoc_disp_var.
    rewrite transport_f_f.
    etrans. {
      do 4 apply maponpaths.
      rewrite mor_disp_transportf_prewhisker.
      apply maponpaths.
      rewrite assoc_disp.
      apply maponpaths.
      apply maponpaths_2.
      refine (! transportf_transpose_left (disp_bifunctor_leftcomp DM _ _ _ _ _ _ _ _ _ _ _ _) @ _).
      etrans. {
        do 2 apply maponpaths.
        apply p_inv.
      }

      apply maponpaths.
      exact (disp_tensor_with_id_left DM (pr2 (monoidal_braiding_inverses B y z)) xx (zz ⊗⊗_{DM} yy)).
    }
    unfold transportb.
    rewrite ! transport_f_f.
    rewrite ! mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    rewrite mor_disp_transportf_postwhisker.
    rewrite ! mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    rewrite id_left_disp.
    etrans. {
      apply maponpaths.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      do 2 apply maponpaths.
      rewrite assoc_disp.
      apply maponpaths.
      apply maponpaths_2.
      apply disp_monoidal_associatoriso.
    }
    unfold transportb.
    rewrite transport_f_f.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    rewrite id_left_disp.
    unfold transportb.
    rewrite transport_f_f.
    rewrite mor_disp_transportf_prewhisker.
    rewrite (! transportf_transpose_left (disp_bifunctor_rightcomp DM _ _ _ _ _ _ _ _ _ _ _ _)).
    etrans. {
      do 3 apply maponpaths.
      apply maponpaths.
      exact (pr1 (p_inv _ _ xx zz)).
    }
    do 2 rewrite transport_f_f.
    etrans. {
      apply maponpaths.
      apply disp_tensor_with_id_right.
    }
    unfold transportb.
    rewrite transport_f_f.
    use transportf_set.
    apply homset_property.
  Qed.

  Lemma make_disp_symm_braiding_nat_left
    {B : symmetric M}
    {c : disp_braiding_data DM B}
    (p_nat : disp_sym_moncat_laws_tensored_nat c)
    : disp_braiding_law_naturality_left DM c.
  Proof.
    intro ; intros.
      use precomp_disp_id_left_inj.
      set (q := transportb_transpose_right (p_nat _ _ _ _ _ _ xx xx yy1 yy2 (id_disp xx) gg)).
      unfold dispfunctoronmorphisms1 in q.
      set (tq := assoc_disp_var (id_disp xx ⊗⊗^{ DM}_{r} yy1) (xx ⊗⊗^{ DM}_{l} gg) (c x y2 xx yy2)) in q.
      set (q' := transportb_transpose_right (! tq @ q)).
      rewrite disp_bifunctor_rightid in q'.
      unfold transportb in q'.
      rewrite (mor_disp_transportf_postwhisker _ (id_disp (xx ⊗⊗_{ DM} yy1))) in q'.
      set (q'' := transportb_transpose_right q').
      refine (_ @ ! q'').
      clear q'' q' tq q.
      unfold transportb.
      rewrite ! transport_f_f.
      etrans.
      2: {
        apply maponpaths.
        apply pathsinv0, assoc_disp.
      }
      unfold transportb.
      rewrite transport_f_f.
      rewrite mor_disp_transportf_prewhisker.
      use transportf_transpose_right.
      unfold transportb.
      rewrite transport_f_f.
      rewrite id_left_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite disp_bifunctor_leftid.
      unfold transportb.
      rewrite ! mor_disp_transportf_prewhisker.
      use transportf_transpose_right.
      unfold transportb.
      rewrite transport_f_f.
      rewrite id_right_disp.
      use transportf_transpose_right.
      unfold transportb.
      rewrite transport_f_f.
      use transportf_set.
      apply homset_property.
  Qed.

  Lemma make_disp_symm_braiding_nat_right
    {B : symmetric M}
    {c : disp_braiding_data DM B}
    (p_nat : disp_sym_moncat_laws_tensored_nat c)
    : disp_braiding_law_naturality_right DM c.
  Proof.
    intro ; intros.
    set (q := ! p_nat _ _ _ _ _ _ xx1 xx2 yy yy ff (id_disp yy)).
    use transportf_transpose_left.
    set (qq := specialized_transport_lemma (c x1 y xx1 yy) ff _ _ q).
    refine (qq @ _).
    clear qq.
    clear q.
    use transportf_transpose_left.
    unfold transportb.
    rewrite transport_f_f.
    rewrite path_comp_inv_inv.
    etrans.
    2: {
      apply maponpaths_2.
      apply maponpaths.
      refine (idpath (maponpaths (λ i, i · pr1 B _ _) (when_bifunctor_becomes_rightwhiskering M y f)) @ _).
      apply homset_property.
    }

    etrans.
    2: {
      apply maponpaths_2.
      apply (maponpathsinv0  (λ i : C ⟦ x1 ⊗_{ M} y, x2 ⊗_{ M} y ⟧, i · pr1 B x2 y)).
    }

    etrans.
    2: {
      apply mor_disp_transportf_postwhisker.
    }
    apply maponpaths_2.
    apply disp_tensor_with_id_on_right.
  Qed.

  Lemma make_disp_symm_braiding_nat
    {B : symmetric M}
    {c : disp_braiding_data DM B}
    (p_nat : disp_sym_moncat_laws_tensored_nat c)
    : disp_braiding_law_naturality DM c.
  Proof.
    split.
    - exact (make_disp_symm_braiding_nat_left p_nat).
    - exact (make_disp_symm_braiding_nat_right p_nat).
  Qed.

  Lemma make_disp_symm_braiding_iso
    {B : symmetric M}
    {c : disp_braiding_data DM B}
    (p_inv : disp_sym_moncat_laws_tensored_inv c)
    : disp_braiding_iso DM c c.
  Proof.
    intro ; intros.
    split.
    - apply pathsinv0.
      etrans. {
        apply maponpaths.
        exact (! p_inv y x yy xx).
      }
      apply transportb_transpose_left.
      apply maponpaths_2.
      apply homset_property.
    - apply pathsinv0.
      etrans. {
        apply maponpaths.
        exact (! p_inv x y xx yy).
      }
      apply transportb_transpose_left.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Lemma make_disp_symm_braiding_hex1
    {B : symmetric M}
    {c : disp_braiding_data DM B}
    (p_hex : disp_sym_moncat_laws_tensored_hex c)
    : disp_braiding_law_hexagon1 DM c.
  Proof.
    unfold disp_braiding_law_hexagon1.
    intro ; intros.
    set (q := p_hex x y z xx yy zz).
    set (qq := specialized_transport_lemma _ _ _ _ (! q)).
    rewrite assoc_disp_var in qq.
    set (qq' := transportb_transpose_right qq).
    set (qq'' := specialized_transport_lemma' _ _ _ _ qq').
    rewrite assoc_disp in qq''.
    set (qq''' := transportb_transpose_right qq'').
    refine (_ @ ! qq''').
    clear qq''' qq'' qq' qq q.
    use transportf_transpose_left.
    unfold transportb.
    rewrite ! transport_f_f.
    apply pathsinv0.
    use transportf_set.
    apply homset_property.
  Qed.

  Lemma make_disp_symm_braiding_hex2
    {B : symmetric M}
    {c : disp_braiding_data DM B}
    (p_inv : disp_sym_moncat_laws_tensored_inv c)
    (p_nat : disp_sym_moncat_laws_tensored_nat c)
    (p_hex : disp_sym_moncat_laws_tensored_hex c)
    : disp_braiding_law_hexagon2 DM c.
  Proof.
    use braiding_laws_one_hexagon_to_braiding_laws.
    - exact (make_disp_symm_braiding_iso p_inv).
    - exact (make_disp_symm_braiding_nat p_nat).
    - exact (make_disp_symm_braiding_hex1 p_hex).
  Qed.

  Lemma make_disp_symm_braiding_laws
    {B : symmetric M}
    {c : disp_braiding_data DM B}
    (p_inv : disp_sym_moncat_laws_tensored_inv c)
    (p_nat : disp_sym_moncat_laws_tensored_nat c)
    (p_hex : disp_sym_moncat_laws_tensored_hex c)
    : disp_braiding_laws DM c c.
  Proof.
    refine (_ ,,_,, (_ ,, _)).
    - exact (make_disp_symm_braiding_nat p_nat).
    - exact (make_disp_symm_braiding_iso p_inv).
    - exact (make_disp_symm_braiding_hex1 p_hex).
    - exact (make_disp_symm_braiding_hex2 p_inv p_nat p_hex).
  Qed.

  Definition make_disp_symmetric
    {B : symmetric M}
    {c : disp_braiding_data DM B}
    (p_inv : disp_sym_moncat_laws_tensored_inv c)
    (p_nat : disp_sym_moncat_laws_tensored_nat c)
    (p_hex : disp_sym_moncat_laws_tensored_hex c)
    : disp_symmetric B.
  Proof.
    refine (c ,, _).
    exact (make_disp_symm_braiding_laws p_inv p_nat p_hex).
  Defined.

End DisplayedSymmetric.