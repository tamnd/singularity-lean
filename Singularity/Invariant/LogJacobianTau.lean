/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobian

/-!
# The type `τ` of a clean polynomial

Let `k` be a field of characteristic `p`, and let `g = x^r G` be clean for the divisor
`E = V(∏_{i ∈ Δ} x_i)`, with `r = divisorExponent Δ g` and `G = residualFactor Δ g`. Let
`d = residualOrderAlong Δ p g` be the residual order and `ρ = logJacobianOrder Δ g`.

This file gives Definition 3.9 of research note 03: the type of `g` in the given coordinates is
`τ = d - ρ` (`logJacobianType`). It also gives the form of Corollary 3.8 of the note for fixed
coordinates: `d = ρ + τ` and `τ ∈ {0, 1}`, so the residual order is `ρ` or `ρ + 1`.

The proof. Theorem 3.7 of the note gives `ρ ≤ d ≤ ρ + 1`
(`logJacobianOrder_le_residualOrderAlong`, `residualOrderAlong_le_logJacobianOrder_add_one`).
The type `1` is the case where `∂_j in(G) ≠ 0` for some `j ∉ Δ`
(`logJacobianOrder_add_one_eq_iff`), and the type `0` is the case where `∂_j in(G) = 0` for each
`j ∉ Δ` (`logJacobianOrder_eq_iff`).

Corollary 3.8 of the note is a statement on the largest residual order `d^max` over all
coordinates adapted to `E` and over all clean representatives of `g` modulo `p`-th powers. It needs
part 3 of Lemma 3.6 of the note, the independence of `Θ(g)` of the coordinates. This file does not
prove that part. It only proves the bound in the given coordinates.

## Main definitions

* `logJacobianType Δ p g`: the type `τ = d - ρ`.

## Main results

* `residualOrderAlong_eq_logJacobianOrder_add_logJacobianType`: `d = ρ + τ`.
* `logJacobianType_le_one`, `logJacobianType_eq_zero_or_eq_one`: `τ ∈ {0, 1}`.
* `logJacobianType_eq_zero_iff`: `τ = 0` if and only if `ρ = d`.
* `logJacobianType_eq_one_iff`: for `g ≠ 0`, `τ = 1` if and only if `ρ + 1 = d`.
* `logJacobianType_eq_one_iff_pderiv`, `logJacobianType_eq_zero_iff_pderiv`: the type by the
  initial form of `G`.

## References

* Research note 03, Section 3.4: Theorem 3.7, Corollary 3.8 and Definition 3.9.
* Volume 7, Section 3.1 of the handbook: Theorem 3.1.4.
-/

open MvPolynomial

namespace Singularity

section Tau

variable {σ k : Type*} [Field k]

/-- **The type** of `g` in the given coordinates (research note 03, Definition 3.9): the residual
order minus the log-Jacobian order, `τ = d - ρ`. For a clean `g`, it is `0` or `1`
(`logJacobianType_eq_zero_or_eq_one`). -/
noncomputable def logJacobianType (Δ : Finset σ) (q : ℕ) (g : MvPolynomial σ k) : ℕ∞ :=
  residualOrderAlong Δ q g - logJacobianOrder Δ g

/-- For `a ≤ b < ⊤` in `ℕ∞`, `b - a = 1` if and only if `a + 1 = b`. -/
private theorem tsub_eq_one_iff {a b : ℕ∞} (hab : a ≤ b) (hb : b ≠ ⊤) :
    b - a = 1 ↔ a + 1 = b := by
  lift b to ℕ using hb
  lift a to ℕ using ne_top_of_le_ne_top (ENat.natCast_ne_top b) hab
  have hab' : a ≤ b := by exact_mod_cast hab
  rw [← ENat.natCast_sub, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_inj, Nat.cast_inj]
  omega

/-- The residual factor of `0` is `0`. -/
theorem residualFactor_zero (Δ : Finset σ) : residualFactor Δ (0 : MvPolynomial σ k) = 0 :=
  (mul_eq_zero.mp (monomial_mul_residualFactor Δ (0 : MvPolynomial σ k))).resolve_left
    (by simp)

variable (p : ℕ) [CharP k p] {Δ : Finset σ} {g : MvPolynomial σ k}

omit [CharP k p] in
/-- For a nonzero `g`, the residual order is finite. -/
theorem residualOrderAlong_ne_top (hg : g ≠ 0) (hc : IsClean p g) :
    residualOrderAlong Δ p g ≠ ⊤ := by
  rw [residualOrderAlong, cleanPart_eq_self hc]
  refine ord_ne_top fun h => hg ?_
  rw [← monomial_mul_residualFactor Δ g, h, mul_zero]

/-- **The residual order is `ρ + τ`** (research note 03, Corollary 3.8 in fixed coordinates).
For a clean `g`, `d = ρ + τ`. -/
theorem residualOrderAlong_eq_logJacobianOrder_add_logJacobianType (hc : IsClean p g) :
    residualOrderAlong Δ p g = logJacobianOrder Δ g + logJacobianType Δ p g :=
  (add_tsub_cancel_of_le (logJacobianOrder_le_residualOrderAlong p hc)).symm

omit [CharP k p] in
/-- **The type is at most `1`** (research note 03, Definition 3.9). -/
theorem logJacobianType_le_one (hc : IsClean p g) : logJacobianType Δ p g ≤ 1 :=
  tsub_le_iff_left.mpr (residualOrderAlong_le_logJacobianOrder_add_one p hc)

/-- **The type is `0` if and only if `ρ = d`.** -/
theorem logJacobianType_eq_zero_iff (hc : IsClean p g) :
    logJacobianType Δ p g = 0 ↔ logJacobianOrder Δ g = residualOrderAlong Δ p g := by
  rw [logJacobianType, tsub_eq_zero_iff_le]
  exact ⟨fun h => le_antisymm (logJacobianOrder_le_residualOrderAlong p hc) h, fun h => h.ge⟩

/-- **The type is `1` if and only if `ρ + 1 = d`**, for `g ≠ 0`. -/
theorem logJacobianType_eq_one_iff (hg : g ≠ 0) (hc : IsClean p g) :
    logJacobianType Δ p g = 1 ↔ logJacobianOrder Δ g + 1 = residualOrderAlong Δ p g :=
  tsub_eq_one_iff (logJacobianOrder_le_residualOrderAlong p hc) (residualOrderAlong_ne_top p hg hc)

/-- **The type is `0` or `1`** (research note 03, Definition 3.9 and Corollary 3.8 in fixed
coordinates). -/
theorem logJacobianType_eq_zero_or_eq_one (hc : IsClean p g) :
    logJacobianType Δ p g = 0 ∨ logJacobianType Δ p g = 1 := by
  rcases logJacobianOrder_eq_or p (Δ := Δ) hc with h | h
  · exact Or.inl ((logJacobianType_eq_zero_iff p hc).mpr h)
  · by_cases hg : g = 0
    · left
      rw [logJacobianType_eq_zero_iff p hc]
      subst hg
      have hd : residualOrderAlong Δ p (0 : MvPolynomial σ k) = ⊤ := by
        rw [residualOrderAlong, cleanPart_eq_self hc, residualFactor_zero, ord_zero]
      rw [hd] at h ⊢
      rcases WithTop.add_eq_top.mp h with h1 | h1
      · exact h1
      · exact absurd h1 ENat.one_ne_top
    · exact Or.inr ((logJacobianType_eq_one_iff p hg hc).mpr h)

/-- **The type `1` by the initial form** (research note 03, Definition 3.9). Let `g` be clean with
`ord G = d`. Then `τ = 1` if and only if `∂_j in(G) ≠ 0` for some `j ∉ Δ`, that is the initial
form of `G` depends on a free coordinate in a way that is not a `p`-th power. -/
theorem logJacobianType_eq_one_iff_pderiv (hc : IsClean p g) {d : ℕ}
    (hd : ord (residualFactor Δ g) = d) :
    logJacobianType Δ p g = 1 ↔
      ∃ j ∉ Δ, pderiv j (homogeneousComponent d (residualFactor Δ g)) ≠ 0 := by
  have hg : g ≠ 0 := by
    rintro rfl
    rw [residualFactor_zero, ord_zero] at hd
    exact ENat.top_ne_natCast d hd
  rw [logJacobianType_eq_one_iff p hg hc, residualOrderAlong, cleanPart_eq_self hc, hd]
  exact logJacobianOrder_add_one_eq_iff p hc hd

/-- **The type `0` by the initial form** (research note 03, Definition 3.9). Let `g` be clean with
`ord G = d`. Then `τ = 0` if and only if `∂_j in(G) = 0` for each `j ∉ Δ`. -/
theorem logJacobianType_eq_zero_iff_pderiv (hc : IsClean p g) {d : ℕ}
    (hd : ord (residualFactor Δ g) = d) :
    logJacobianType Δ p g = 0 ↔
      ∀ j ∉ Δ, pderiv j (homogeneousComponent d (residualFactor Δ g)) = 0 := by
  rw [logJacobianType_eq_zero_iff p hc, residualOrderAlong, cleanPart_eq_self hc, hd]
  exact logJacobianOrder_eq_iff p hc hd

end Tau

end Singularity
