/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianNonincrease
import Singularity.Invariant.LogJacobianTau

/-!
# Kangaroo points are type switches

Let `k` be a field of characteristic `p`, let `g ≠ 0` be clean for the divisor
`E = V(∏_{i ∈ Δ} x_i)` with `ord g ≥ p`, and let the chart `pointChart j t` of the blowup of the
origin send `g` to `x_j^p g'`. Let `Δ' = blowupDivisor Δ j t` and let `g'_c = cleanPart p g'`.
Let `d`, `ρ` and `τ` be the residual order, the log-Jacobian order and the type of `g` along `Δ`,
and let `d'`, `ρ'` and `τ'` be those of `g'_c` along `Δ'`.

This file proves Corollary 3.14 of research note 03: if `d' = d + 1`, then `ρ' = ρ = d`, `τ = 0`
and `τ' = 1` (`kangaroo_type_switch`).

The proof. Corollary 3.13 of the note
(`residualOrderAlong_pointChart_le_logJacobianOrder`) gives `d' ≤ ρ' + 1 ≤ ρ + 1 ≤ d + 1`. If
`d' = d + 1`, then equality holds throughout. Since `d` is finite, `ρ' = ρ = d`, and
`τ = d - ρ = 0` and `τ' = d' - ρ' = 1`.

## Main results

* `kangaroo_type_switch`: Corollary 3.14 of research note 03.
* `logJacobianType_cleanPart_eq_one_of_residualOrderAlong_eq_add_one`: the type of `g'_c` is `1`
  at a point where the residual order goes up.

## References

* Research note 03, Section 3.6: Corollaries 3.13 and 3.14.
* Volume 7, Section 3.2 of the handbook: Theorem 3.2.4 and Corollary 3.2.5.
-/

open MvPolynomial

namespace Singularity

section TypeSwitch

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- **Kangaroo points are type switches** (research note 03, Corollary 3.14). Let `g ≠ 0` be
clean with `ord g ≥ p`, and let the chart send `g` to `x_j^p g'`. If the residual order goes up,
`d' = d + 1`, then `ρ(g'_c) = ρ(g) = d`, the type of `g` is `0` and the type of `g'_c` is `1`.
Here `d'`, `ρ(g'_c)` and the type of `g'_c` are along the new divisor `Δ' = blowupDivisor Δ j t`,
in the coordinates of the chart. -/
theorem kangaroo_type_switch (hg : g ≠ 0) (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g)
    (h : pointChart j t g = X j ^ p * g')
    (hd : residualOrderAlong (blowupDivisor Δ j t) p g' = residualOrderAlong Δ p g + 1) :
    logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = logJacobianOrder Δ g ∧
      logJacobianOrder Δ g = residualOrderAlong Δ p g ∧
      logJacobianType Δ p g = 0 ∧
      logJacobianType (blowupDivisor Δ j t) p (cleanPart p g') = 1 := by
  obtain ⟨h1, h2, h3⟩ := residualOrderAlong_pointChart_le_logJacobianOrder p hg hc hord h
  rw [hd] at h1
  have e2 : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') + 1 =
      logJacobianOrder Δ g + 1 := le_antisymm h2 (h3.trans h1)
  have e3 : logJacobianOrder Δ g + 1 = residualOrderAlong Δ p g + 1 :=
    le_antisymm h3 (h1.trans h2)
  have e2' := WithTop.add_right_cancel ENat.one_ne_top e2
  have e3' := WithTop.add_right_cancel ENat.one_ne_top e3
  have hd' : residualOrderAlong (blowupDivisor Δ j t) p (cleanPart p g') =
      residualOrderAlong (blowupDivisor Δ j t) p g' := by
    rw [residualOrderAlong, residualOrderAlong, cleanPart_eq_self (isClean_cleanPart p g')]
  refine ⟨e2', e3', (logJacobianType_eq_zero_iff p hc).mpr e3', ?_⟩
  rw [logJacobianType, hd', hd, e2', e3']
  have hfin := residualOrderAlong_ne_top p (Δ := Δ) hg hc
  lift residualOrderAlong Δ p g to ℕ using hfin with n
  rw [← Nat.cast_one, ← Nat.cast_add, ← ENat.natCast_sub, Nat.add_sub_cancel_left, Nat.cast_one]

/-- **The type of `g'_c` is `1` where the residual order goes up** (research note 03,
Corollary 3.14). -/
theorem logJacobianType_cleanPart_eq_one_of_residualOrderAlong_eq_add_one (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g')
    (hd : residualOrderAlong (blowupDivisor Δ j t) p g' = residualOrderAlong Δ p g + 1) :
    logJacobianType (blowupDivisor Δ j t) p (cleanPart p g') = 1 :=
  (kangaroo_type_switch p hg hc hord h hd).2.2.2

end TypeSwitch

end Singularity
