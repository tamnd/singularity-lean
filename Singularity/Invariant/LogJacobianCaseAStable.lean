/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianDirectrixCaseA

/-!
# The first case is stable if `|r| + d ≠ 0` in `k`

Let `k` be a field of characteristic `p`, let `g ≠ 0` be a clean polynomial with `ord g ≥ p`, and
let `π = pointChart j t` send `g` to `x_j^p g'`. Write `g = x^r G`, let `d = ord G`, and let
`ρ(g) = ρ(g'_c) = d` for the new divisor `Δ' = blowupDivisor Δ j t`. This file proves that if
`|r| + d ≠ 0` in `k`, then the new point is of case A: the order of `Θ₀(g'_c)` is `|r'| + d`, with
`r' = divisorExponent Δ' g'_c` (Volume 7, Section 3.9 of the handbook, Proposition 3.9.7). So
Theorem 3.9.1 holds with no hypothesis on the new point (Corollary 3.9.8).

The proof. The Euler element `e = ∑_i (r_i G + x_i ∂_i G)` has order `d`, since its part of degree
`d` is `(|r| + d) F`. The chart sends `x^r e` to `x_j^p (x_j ∂_j g')`, and `x_j ∂_j g'` is in
`Θ₀(g'_c)`. This element is `x^b U e'`, with a unit `U`, the transform `e'` of order `d`, and
`b ≤ r'`. So the order of `Θ₀(g'_c)` is at most `|b| + d ≤ |r'| + d`. Since `Θ₀(g'_c) ⊆ Θ(g'_c)`,
the order of `Θ₀(g'_c)` is at least `|r'| + ρ(g'_c) = |r'| + d`.

## Main results

* `idealOrd_logJacobianTangent_cleanPart_le_of_pointChart_eq`: the bound `|r'| + d` from an exact
  transport.
* `idealOrd_logJacobianTangent_cleanPart_of_caseA`: Proposition 3.9.7.
* `finrank_logJacobianDirectrix_cleanPart_le_of_ne_zero`,
  `logJacobianDirectrixCodim_le_cleanPart_of_ne_zero`: Corollary 3.9.8.

## References

* Volume 7, Section 3.9 of the handbook: Theorem 3.9.1, Proposition 3.9.7 and Corollary 3.9.8.
-/

open MvPolynomial Finsupp Module

namespace Singularity

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- **The bound from an exact transport.** Let `g ≠ 0` be clean with `ord g ≥ p`, let
`π(g) = x_j^p g'`, and let the order of `Θ₀(g)` be `|r| + d`. Let `ρ(g'_c) = d`. Let `ord ψ = d`
and `x^r ψ ∈ Θ₀(g)`. If `π(x^r ψ) = x_j^p f'` with `f' ∈ Θ₀(g'_c)`, then the order of `Θ₀(g'_c)`
is at most `|r'| + d`, with `r' = divisorExponent Δ' g'_c`. The proof: `f' = x^b U ψ'`, with a unit
`U`, the transform `ψ'` of order `d`, and `b ≤ r'`. -/
theorem idealOrd_logJacobianTangent_cleanPart_le_of_pointChart_eq (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hA : idealOrd (logJacobianTangent Δ g) = ((degree (divisorExponent Δ g) + d : ℕ) : ℕ∞))
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d)
    {ψ f' : MvPolynomial σ k} (hψo : ord ψ = d)
    (hψ : monomial (divisorExponent Δ g) 1 * ψ ∈ logJacobianTangent Δ g)
    (hπ : pointChart j t (monomial (divisorExponent Δ g) 1 * ψ) = X j ^ p * f')
    (hf' : f' ∈ logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g')) :
    idealOrd (logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g')) ≤
      ((degree (divisorExponent (blowupDivisor Δ j t) (cleanPart p g')) + d : ℕ) : ℕ∞) := by
  have hψ' := pointChart_eq_X_pow_mul_chartTransform j t hψo.ge
  have hπ' := pointChart_monomial_mul_eq (r := divisorExponent Δ g) hψ'
  have hle := logJacobianOrder_cleanPart_le_ord_of_pointChart_eq p hg hc hord h hA hψ hπ'
  rw [hρ'] at hle
  have hψ'o : ord (chartTransform j t d ψ) = d := le_antisymm (ord_le_of_pointChart hψo hψ') hle
  obtain ⟨hb, hleI, -⟩ := monomial_mul_mem_logJacobian_cleanPart p hg hord h hA hψ hπ'
  set r' := divisorExponent (blowupDivisor Δ j t) (cleanPart p g')
  set b := single j (degree (divisorExponent Δ g) + d - p) +
    chartExponent j t (divisorExponent Δ g)
  have hpτ : p ≤ degree (divisorExponent Δ g) + d := by
    have := le_idealOrd_logJacobianTangent (Δ := Δ) hord
    rw [hA] at this
    exact_mod_cast this
  have hXb : X j ^ (degree (divisorExponent Δ g) + d) *
      monomial (chartExponent j t (divisorExponent Δ g)) (1 : k) = X j ^ p * monomial b 1 := by
    rw [monomial_single_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hpτ]
  have hf'eq : f' = monomial b 1 *
      (chartUnit j t (divisorExponent Δ g) * chartTransform j t d ψ) := by
    refine mul_left_cancel₀ (pow_ne_zero p (X_ne_zero j (R := k))) ?_
    rw [← hπ, hπ', ← mul_assoc, hXb, mul_assoc]
  have hcl := (logJacobianOrder_cleanPart_le p (Δ := Δ) hg hc hord h).1
  have hbr : b ≤ r' := le_divisorExponent_of_logJacobian_le p hcl (isClean_cleanPart p g') hb hleI
  have hdeg : degree b ≤ degree r' := by
    obtain ⟨c, hbc⟩ := exists_add_of_le hbr
    rw [hbc]
    exact le_self_add.trans_eq (map_add degree b c).symm
  have h1 := idealOrd_le_ord hf'
  rw [hf'eq, ord_mul, ord_mul, ord_monomial one_ne_zero, ord_chartUnit, zero_add, hψ'o] at h1
  refine h1.trans ?_
  rw [Nat.cast_add]
  exact add_le_add (by exact_mod_cast hdeg) le_rfl

/-- **The first case is stable** (Volume 7, Section 3.9 of the handbook, Proposition 3.9.7). Let
`g ≠ 0` be clean with `ord g ≥ p`, let `π(g) = x_j^p g'` in the chart `π = pointChart j t`, let
`d = ord G` with `G = residualFactor Δ g`, and let `ρ(g) = ρ(g'_c) = d` for the new divisor
`Δ' = blowupDivisor Δ j t`. If `|r| + d` is not `0` in `k`, then the new point is of case A: the
order of `Θ₀(g'_c)` is `|r'| + d`, with `r' = divisorExponent Δ' g'_c`. The old point is then also
of case A. The proof uses the transport of the Euler element. -/
theorem idealOrd_logJacobianTangent_cleanPart_of_caseA (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hG : ord (residualFactor Δ g) = d) (hρ : logJacobianOrder Δ g = d)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d)
    (hpd : ((degree (divisorExponent Δ g) + d : ℕ) : k) ≠ 0) :
    idealOrd (logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g')) =
      ((degree (divisorExponent (blowupDivisor Δ j t) (cleanPart p g')) + d : ℕ) : ℕ∞) := by
  -- The Euler element `ψ_E`.
  have hE := monomial_mul_sum_smul_add_X_mul_pderiv_mem Δ g
  have hEo := ord_sum_smul_add_X_mul_pderiv hG hpd
  -- The old point is of case A.
  have hA : idealOrd (logJacobianTangent Δ g) = ((degree (divisorExponent Δ g) + d : ℕ) : ℕ∞) := by
    refine le_antisymm ((idealOrd_le_ord hE).trans (le_of_eq ?_)) ?_
    · rw [ord_mul, ord_monomial one_ne_zero, hEo, Nat.cast_add]
    · rw [Nat.cast_add, ← hρ, ← idealOrd_logJacobian]
      exact idealOrd_anti (logJacobianTangent_le Δ g)
  -- The exact transport of the Euler element.
  have hπ : pointChart j t (monomial (divisorExponent Δ g) 1 * ∑ i,
      ((divisorExponent Δ g i : k) • residualFactor Δ g +
        X i * pderiv i (residualFactor Δ g))) = X j ^ p * (X j * pderiv j g') := by
    rw [← sum_X_mul_pderiv_monomial_mul, monomial_mul_residualFactor]
    exact pointChart_sum_X_mul_pderiv p h
  have hf' : X j * pderiv j g' ∈ logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g') := by
    rw [← pderiv_cleanPart p]
    exact X_mul_pderiv_mem_logJacobianTangent (mem_blowupDivisor.mpr (Or.inl rfl)) _
  refine le_antisymm
    (idealOrd_logJacobianTangent_cleanPart_le_of_pointChart_eq p hg hc hord h hA hρ' hEo hE hπ hf')
    ?_
  -- The order of `Θ₀(g'_c)` is at least the order `|r'| + ρ(g'_c)` of `Θ(g'_c)`.
  rw [Nat.cast_add, ← hρ', ← idealOrd_logJacobian]
  exact idealOrd_anti (logJacobianTangent_le _ _)

/-- **`τ_ρ` does not go down from case A** (Volume 7, Section 3.9 of the handbook,
Corollary 3.9.8). This is Theorem 3.9.1 with no hypothesis on the new point. Let `g ≠ 0` be clean
with `ord g ≥ p`, let `π(g) = x_j^p g'` in the chart `π = pointChart j t`, let `d = ord G` with
`G = residualFactor Δ g`, and let `ρ(g) = ρ(g'_c) = d` for the new divisor
`Δ' = blowupDivisor Δ j t`. If `|r| + d` is not `0` in `k`, then `dim T_ρ(g'_c) ≤ dim T_ρ(g)`. -/
theorem finrank_logJacobianDirectrix_cleanPart_le_of_ne_zero (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hG : ord (residualFactor Δ g) = d) (hρ : logJacobianOrder Δ g = d)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d)
    (hpd : ((degree (divisorExponent Δ g) + d : ℕ) : k) ≠ 0) :
    finrank k (logJacobianDirectrix (blowupDivisor Δ j t) (cleanPart p g')) ≤
      finrank k (logJacobianDirectrix Δ g) :=
  finrank_logJacobianDirectrix_cleanPart_le_of_caseA p hg hc hord h hG hρ hρ'
    (idealOrd_logJacobianTangent_cleanPart_of_caseA p hg hc hord h hG hρ hρ' hpd) hpd

/-- **`τ_ρ` does not go down from case A**, the form with the codimension (Volume 7, Section 3.9
of the handbook, Corollary 3.9.8). This is Theorem 3.9.1 with no hypothesis on the new point. -/
theorem logJacobianDirectrixCodim_le_cleanPart_of_ne_zero (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hG : ord (residualFactor Δ g) = d) (hρ : logJacobianOrder Δ g = d)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d)
    (hpd : ((degree (divisorExponent Δ g) + d : ℕ) : k) ≠ 0) :
    logJacobianDirectrixCodim Δ g ≤
      logJacobianDirectrixCodim (blowupDivisor Δ j t) (cleanPart p g') :=
  logJacobianDirectrixCodim_le_cleanPart_of_caseA p hg hc hord h hG hρ hρ'
    (idealOrd_logJacobianTangent_cleanPart_of_caseA p hg hc hord h hG hρ hρ' hpd) hpd

end Singularity
