(**
In this file, we show that weak equivalences reflect and preserve terminal objects.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.

Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.

Proposition weak_equiv_reflects_terminal
    {C D : category} (F : C ⟶ D)
    : is_weak_equiv F
      → ∏ c : C, isTerminal _ (F c) → isTerminal _ c.
  Proof.
    intros Fw c Fc_term c'.
    apply (iscontrweqb' (Fc_term (F c'))).
    apply ((_ ,, ff_from_weak_equiv _ Fw _ _))%weq.
  Qed.

Section WeakEquivalencePreservationsTerminal.

  (* ∏ t : Terminal C, is_terminal (F t) *)
  Proposition weak_equiv_preserves_chosen_terminal
    {C D : category} (F : C ⟶ D)
    : is_weak_equiv F
      → ∏ t : Terminal C, preserves_chosen_terminal t F.
  Proof.
    intros Fw [x x_is_t] y'.
    use (factor_through_squash (isapropiscontr _) _ (eso_from_weak_equiv _ Fw y')).
    intros [y yi].
    apply (iscontrweqb' (x_is_t y)).
    refine (invweq (_ ,, ff_from_weak_equiv _ Fw y x) ∘ _)%weq.
    apply z_iso_comp_right_weq.
    exact yi.
  Qed.

  (*  ∏ x : C, isTerminal C x → isTerminal D (F x) *)
  Corollary weak_equiv_preserves_terminal
    {C D : category} (F : C ⟶ D)
    : is_weak_equiv F → preserves_terminal F.
  Proof.
    intros Fw ? x_is_t.
    apply (preserves_terminal_if_preserves_chosen (_,,x_is_t)).
    - apply weak_equiv_preserves_chosen_terminal.
      exact Fw.
    - exact x_is_t.
  Qed.

  (*  isTerminal t1 × isTerminal t2 → ∥ F t1 = t2 ∥ *)
  Corollary weak_equiv_preserves_chosen_terminal_eq
    {C D : category} (F : C ⟶ D)
    : is_weak_equiv F
      → is_univalent D
      → ∏ t1 t2, preserves_chosen_terminal_eq F t1 t2.
  Proof.
    intros Fw Duniv t1 t2.
    unfold preserves_chosen_terminal_eq.
    apply hinhpr.
    apply Duniv.
    set (Ft1_t := weak_equiv_preserves_terminal _ Fw _ (pr2 t1)).
    exact (z_iso_Terminals (_ ,, Ft1_t) t2).
  Qed.

End WeakEquivalencePreservationsTerminal.
