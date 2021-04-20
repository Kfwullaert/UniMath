(**
Useful lemmas that don't have anything to do with fibrations directly.
Many of these could and should be replaced by something that is already implemented in UniMath, but which I couldn't find at the time of writing my code.
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence. (* only coercions *)
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.MonoEpiIso.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Presheaf.
Local Open Scope cat.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import UniMath.Foundations.All.

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.


(** * Comfortably proving unique existence *)
Section Unique_existence.

Definition contr_equiv_inhab_prop
    (A : UU)
  : (iscontr A) <-> A × (isaprop A).
Proof.
  split.
  - intros H. split.
    -- exact (iscontrpr1 H).
    -- exact (isapropifcontr H).
  - unfold isaprop, isofhlevel, iscontr. intros (a, H).
    exists a. intros a'.
    exact (pr1 (H a' a)).
Defined.

Definition uniex_equiv_ex_uni
    {A : UU} (B : A -> UU)
  : (∃! (a : A), B a) <-> (∑ (a : A), B a) × isaprop (∑ (a : A), B a).
Proof.
  exact (contr_equiv_inhab_prop (∑ (a : A), B a)).
Defined.

(* Replace applictions of this by eapply unique_exists? *)
Corollary unique_exists' {A : UU} {B : A -> UU} (x : A) (b : B x)
          (h : ∏ y, isaprop (B y)) (H : ∏ y y', B y -> B y' -> y = y') :
  iscontr (total2 (λ t : A, B t)).
Proof.
  use make_iscontr.
  - exact (x,,b).
  - intros [t bt]. apply subtypePath.
    + exact h.
    + simpl. apply (H t). exact bt. exact b.
Defined.

End Unique_existence.


(** Transport cancellation *)
(* Replace usage by transportbfinv/transportfbinv. *)

Section Transport_cancellation.
Definition transport_cancel_f_b
    {X : UU} (P : X -> UU) {x x' : X} (e : x' = x) (p : P x)
  : transportf P e (transportb P e p) = p.
Proof.
  induction e. apply idpath.
Defined.

Definition transport_cancel_b_f
    {X : UU} (P : X -> UU) {x x' : X} (e : x = x') (p : P x)
  : transportb P e (transportf P e p) = p.
Proof.
  induction e. apply idpath.
Defined.

End Transport_cancellation.
