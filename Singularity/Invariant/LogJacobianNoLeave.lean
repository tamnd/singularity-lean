/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianCaseAStable

/-!
# The first case is stable if no component of the divisor leaves

Let `k` be a field of characteristic `p`, let `g ≠ 0` be a clean polynomial with `ord g ≥ p`, and
let `π = pointChart j t` send `g` to `x_j^p g'`. Write `g = x^r G`, let `e_i = r_i G + x_i ∂_i G`
and `Φ_i = (e_i)_d` for `i ∈ Δ`, and let `Δ' = blowupDivisor Δ j t` be the new divisor. A component
`i ∈ Δ` with `i ≠ j` leaves if `t_i ≠ 0`. Let the old point be of case A with `ρ(g) = d`: the order
of `Θ₀(g)` is `|r| + d`. Let `ρ(g'_c) = d`. Let `R` be the set of the `i ∈ Δ` with `ord e_i = d`.

This file proves two results (Volume 7, Section 3.9 of the handbook). They have no hypothesis on
`p`.

* Theorem A. If `R` contains an index `i ≠ j` with `t_i = 0`, or if `R = {j}`, then the new point is
  of case A: the order of `Θ₀(g'_c)` is `|r'| + d`, with `r' = divisorExponent Δ' g'_c`. This holds
  if no component of `Δ` leaves.
* Theorem B. If no component of `Δ` leaves, then `dim T_ρ(g'_c) ≤ dim T_ρ(g)`, so
  `τ_ρ(g) ≤ τ_ρ(g'_c)`.

The proof of Theorem A. In case A, each `x_m ∂_l G` with `l ∉ Δ` has order at least `d + 1`. So
`R` is not empty. If `i ∈ R`, `i ≠ j` and `t_i = 0`, then the chart sends `x^r e_i = x_i ∂_i g` to
`x_j^p (x_i ∂_i g')`, and `i ∈ Δ'`. If `R = {j}`, then the Euler element `e = ∑_i e_i` has order
`d`, and the chart sends `x^r e` to `x_j^p (x_j ∂_j g')`. In both cases the bound of
`idealOrd_logJacobianTangent_cleanPart_le_of_pointChart_eq` gives the claim.

The proof of Theorem B. If `|r| + d ≠ 0` in `k`, this is Corollary 3.9.8. If `|r| + d = 0` in `k`,
then the new point is of case A by Theorem A, and the proof of Theorem 3.9.1 applies with one
change. Let `w ∈ T_ρ(g'_c)` with `w_j = 0`. For `i ∈ Δ` with `i ≠ j`, the transport of `e_i` is
exact, so `w ∈ T(Φ_i)`. The Euler identity gives `∑_i Φ_i = (|r| + d) F = 0`, so
`Φ_j = -∑_{i ≠ j} Φ_i`, and `w ∈ T(Φ_j)`.

## Main results

* `exists_mem_ord_smul_add_X_mul_pderiv_eq`: the set `R` is not empty.
* `idealOrd_logJacobianTangent_cleanPart_of_ne_of_eq_zero`: Theorem A, the form with the index `i`.
* `idealOrd_logJacobianTangent_cleanPart_of_lt_ord`: Theorem A, the form with `R = {j}`.
* `idealOrd_logJacobianTangent_cleanPart_of_forall_eq_zero`: Theorem A, the form with no leaving
  component.
* `finrank_logJacobianDirectrix_cleanPart_le_of_forall_eq_zero`,
  `logJacobianDirectrixCodim_le_cleanPart_of_forall_eq_zero`: Theorem B.

## References

* Volume 7, Section 3.9 of the handbook: Theorem 3.9.1, Lemma 3.9.3 and Corollary 3.9.8.
-/

open MvPolynomial Finsupp Module

namespace Singularity

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-! ### The set `R` -/

section Generators

omit [DecidableEq σ] [DecidableEq k] [Fintype σ] in
/-- If `ρ(g) = d` and `l ∉ Δ`, then `x_m ∂_l G` has order at least `d + 1`. -/
theorem natCast_succ_le_ord_X_mul_pderiv_residualFactor {d : ℕ} (hρ : logJacobianOrder Δ g = d)
    {l : σ} (hl : l ∉ Δ) (m : σ) :
    ((d + 1 : ℕ) : ℕ∞) ≤ ord (X m * pderiv l (residualFactor Δ g)) := by
  have h1 := idealOrd_le_ord (pderiv_mem_residualLogJacobian (Δ := Δ) hl
    (divisorExponent Δ g) (residualFactor Δ g))
  rw [show idealOrd (residualLogJacobian Δ (divisorExponent Δ g) (residualFactor Δ g)) = d
    from hρ] at h1
  exact natCast_succ_le_ord_X_mul h1 m

omit [DecidableEq σ] [DecidableEq k] [Fintype σ] in
/-- If `ρ(g) = d` and `l ∉ Δ`, then `e_l = x_l ∂_l G` has order at least `d + 1`. -/
theorem natCast_succ_le_ord_smul_add_X_mul_pderiv_of_notMem {d : ℕ}
    (hρ : logJacobianOrder Δ g = d) {l : σ} (hl : l ∉ Δ) :
    ((d + 1 : ℕ) : ℕ∞) ≤ ord ((divisorExponent Δ g l : k) • residualFactor Δ g +
      X l * pderiv l (residualFactor Δ g)) := by
  rw [divisorExponent_eq_zero hl, Nat.cast_zero, zero_smul, zero_add]
  exact natCast_succ_le_ord_X_mul_pderiv_residualFactor hρ hl l

omit [DecidableEq σ] [DecidableEq k] [Fintype σ] in
/-- `x^r e_i = x_i ∂_i g` is in `Θ₀(g)` for `i ∈ Δ`. -/
theorem monomial_mul_smul_add_X_mul_pderiv_mem {i : σ} (hi : i ∈ Δ) :
    monomial (divisorExponent Δ g) 1 * ((divisorExponent Δ g i : k) • residualFactor Δ g +
      X i * pderiv i (residualFactor Δ g)) ∈ logJacobianTangent Δ g := by
  rw [← X_mul_pderiv_monomial_mul, monomial_mul_residualFactor]
  exact X_mul_pderiv_mem_logJacobianTangent hi g

omit [DecidableEq σ] [DecidableEq k] [Fintype σ] in
/-- If the order of `Θ₀(g)` is `|r| + d` and `i ∈ Δ`, then `e_i` has order at least `d`. -/
theorem le_ord_smul_add_X_mul_pderiv_of_idealOrd_eq {d : ℕ}
    (hA : idealOrd (logJacobianTangent Δ g) = ((degree (divisorExponent Δ g) + d : ℕ) : ℕ∞))
    {i : σ} (hi : i ∈ Δ) :
    (d : ℕ∞) ≤ ord ((divisorExponent Δ g i : k) • residualFactor Δ g +
      X i * pderiv i (residualFactor Δ g)) := by
  have h1 := idealOrd_le_ord (monomial_mul_smul_add_X_mul_pderiv_mem (g := g) hi)
  rw [hA, ord_mul, ord_monomial one_ne_zero, Nat.cast_add] at h1
  exact (ENat.add_le_add_iff_left (ENat.natCast_ne_top _)).mp h1

omit [DecidableEq σ] [DecidableEq k] [Fintype σ] in
/-- **The set `R` is not empty** (Volume 7, Section 3.9 of the handbook). Let `ρ(g) = d`, and let
the order of `Θ₀(g)` be `|r| + d` (case A). Then some `i ∈ Δ` has `ord e_i = d`, with
`e_i = r_i G + x_i ∂_i G`. The proof: the generators `x_m ∂_l G` of `Θ̃₀(G)` with `l ∉ Δ` have
order at least `d + 1`, and the order of `Θ̃₀(G)` is `d`. -/
theorem exists_mem_ord_smul_add_X_mul_pderiv_eq {d : ℕ} (hρ : logJacobianOrder Δ g = d)
    (hA : idealOrd (logJacobianTangent Δ g) = ((degree (divisorExponent Δ g) + d : ℕ) : ℕ∞)) :
    ∃ i ∈ Δ, ord ((divisorExponent Δ g i : k) • residualFactor Δ g +
      X i * pderiv i (residualFactor Δ g)) = d := by
  by_contra hne
  push Not at hne
  have hgen : ∀ s ∈ (fun i => (divisorExponent Δ g i : k) • residualFactor Δ g +
      X i * pderiv i (residualFactor Δ g)) '' (Δ : Set σ) ∪
      (fun a : σ × σ => X a.1 * pderiv a.2 (residualFactor Δ g)) '' {a | a.2 ∉ Δ},
      ((d + 1 : ℕ) : ℕ∞) ≤ ord s := by
    rintro s (⟨i, hi, rfl⟩ | ⟨⟨a, l⟩, hl, rfl⟩)
    · rw [Nat.cast_succ]
      exact Order.add_one_le_of_lt
        (lt_of_le_of_ne (le_ord_smul_add_X_mul_pderiv_of_idealOrd_eq hA hi) (hne i hi).symm)
    · exact natCast_succ_le_ord_X_mul_pderiv_residualFactor hρ hl a
  have h2 := le_idealOrd_span hgen
  have h3 : idealOrd (logJacobianTangent Δ g) = degree (divisorExponent Δ g) +
      idealOrd (residualLogJacobianTangent Δ (divisorExponent Δ g) (residualFactor Δ g)) := by
    conv_lhs => rw [← monomial_mul_residualFactor Δ g]
    rw [logJacobianTangent_monomial_mul (fun _ hi => divisorExponent_eq_zero hi), idealOrd_mul,
      idealOrd_span_singleton, ord_monomial one_ne_zero]
  rw [residualLogJacobianTangent] at h3
  have h4 := add_le_add (le_refl ((degree (divisorExponent Δ g) : ℕ) : ℕ∞)) h2
  rw [← h3, hA] at h4
  have h5 : degree (divisorExponent Δ g) + (d + 1) ≤ degree (divisorExponent Δ g) + d := by
    exact_mod_cast h4
  omega

end Generators

/-! ### Theorem A -/

section TheoremA

omit [Fintype σ] [CharP k p] in
/-- The order of `Θ₀(g'_c)` is at least `|r'| + ρ(g'_c)`. -/
private theorem le_idealOrd_logJacobianTangent_cleanPart {d : ℕ}
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d) :
    ((degree (divisorExponent (blowupDivisor Δ j t) (cleanPart p g')) + d : ℕ) : ℕ∞) ≤
      idealOrd (logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g')) := by
  rw [Nat.cast_add, ← hρ', ← idealOrd_logJacobian]
  exact idealOrd_anti (logJacobianTangent_le _ _)

/-- **The first case is stable, the form with the index `i`** (Volume 7, Section 3.9 of the
handbook, Theorem A of S7.14). Let `g ≠ 0` be clean with `ord g ≥ p`, let `π(g) = x_j^p g'` in the
chart `π = pointChart j t`, and let the order of `Θ₀(g)` be `|r| + d`. Let `ρ(g'_c) = d` for the
new divisor `Δ' = blowupDivisor Δ j t`. Let `i ∈ Δ` with `i ≠ j` and `t_i = 0`, and let
`ord e_i = d`, with `e_i = r_i G + x_i ∂_i G`. Then the new point is of case A: the order of
`Θ₀(g'_c)` is `|r'| + d`, with `r' = divisorExponent Δ' g'_c`. The proof uses the exact transport
of `x_i ∂_i g`. -/
theorem idealOrd_logJacobianTangent_cleanPart_of_ne_of_eq_zero (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hA : idealOrd (logJacobianTangent Δ g) = ((degree (divisorExponent Δ g) + d : ℕ) : ℕ∞))
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d) {i : σ} (hi : i ∈ Δ)
    (hij : i ≠ j) (hti : t i = 0)
    (hio : ord ((divisorExponent Δ g i : k) • residualFactor Δ g +
      X i * pderiv i (residualFactor Δ g)) = d) :
    idealOrd (logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g')) =
      ((degree (divisorExponent (blowupDivisor Δ j t) (cleanPart p g')) + d : ℕ) : ℕ∞) := by
  have hπ : pointChart j t (monomial (divisorExponent Δ g) 1 *
      ((divisorExponent Δ g i : k) • residualFactor Δ g +
        X i * pderiv i (residualFactor Δ g))) = X j ^ p * (X i * pderiv i g') := by
    rw [← X_mul_pderiv_monomial_mul, monomial_mul_residualFactor]
    exact pointChart_X_mul_pderiv_of_ne_of_eq_zero p hij hti h
  have hf' : X i * pderiv i g' ∈ logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g') := by
    rw [← pderiv_cleanPart p]
    exact X_mul_pderiv_mem_logJacobianTangent (mem_blowupDivisor.mpr (Or.inr ⟨hi, hij, hti⟩)) _
  exact le_antisymm
    (idealOrd_logJacobianTangent_cleanPart_le_of_pointChart_eq p hg hc hord h hA hρ' hio
      (monomial_mul_smul_add_X_mul_pderiv_mem hi) hπ hf')
    (le_idealOrd_logJacobianTangent_cleanPart p hρ')

/-- **The first case is stable, the form with `R = {j}`** (Volume 7, Section 3.9 of the handbook,
Theorem A of S7.14). Let `g ≠ 0` be clean with `ord g ≥ p`, let `π(g) = x_j^p g'` in the chart
`π = pointChart j t`, let `ρ(g) = d`, and let the order of `Θ₀(g)` be `|r| + d`. Let `ρ(g'_c) = d`
for the new divisor `Δ' = blowupDivisor Δ j t`. Let `ord e_j = d` and `d < ord e_i` for each other
`i ∈ Δ`, with `e_i = r_i G + x_i ∂_i G`. Then `j ∈ Δ`, and the new point is of case A: the order
of `Θ₀(g'_c)` is `|r'| + d`, with `r' = divisorExponent Δ' g'_c`. The proof: the Euler element has
order `d`, and its transport is exact. -/
theorem idealOrd_logJacobianTangent_cleanPart_of_lt_ord (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hρ : logJacobianOrder Δ g = d)
    (hA : idealOrd (logJacobianTangent Δ g) = ((degree (divisorExponent Δ g) + d : ℕ) : ℕ∞))
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d)
    (hjo : ord ((divisorExponent Δ g j : k) • residualFactor Δ g +
      X j * pderiv j (residualFactor Δ g)) = d)
    (hlt : ∀ i ∈ Δ, i ≠ j → (d : ℕ∞) < ord ((divisorExponent Δ g i : k) • residualFactor Δ g +
      X i * pderiv i (residualFactor Δ g))) :
    idealOrd (logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g')) =
      ((degree (divisorExponent (blowupDivisor Δ j t) (cleanPart p g')) + d : ℕ) : ℕ∞) := by
  -- The Euler element `ψ_E` has order `d`.
  have hE := monomial_mul_sum_smul_add_X_mul_pderiv_mem Δ g
  have hrest : ((d + 1 : ℕ) : ℕ∞) ≤ ord (∑ i ∈ Finset.univ.erase j,
      ((divisorExponent Δ g i : k) • residualFactor Δ g +
        X i * pderiv i (residualFactor Δ g))) := by
    refine Finset.sum_induction _ (fun f => ((d + 1 : ℕ) : ℕ∞) ≤ ord f)
      (fun _ _ ha hb => le_ord_add ha hb) (by rw [ord_zero]; exact le_top) fun i hi => ?_
    by_cases hiΔ : i ∈ Δ
    · rw [Nat.cast_succ]
      exact Order.add_one_le_of_lt (hlt i hiΔ (Finset.ne_of_mem_erase hi))
    · exact natCast_succ_le_ord_smul_add_X_mul_pderiv_of_notMem hρ hiΔ
  have hEo : ord (∑ i, ((divisorExponent Δ g i : k) • residualFactor Δ g +
      X i * pderiv i (residualFactor Δ g))) = d := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ord_add_of_lt, hjo]
    rw [hjo]
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self d) hrest
  -- The exact transport of the Euler element.
  have hπ : pointChart j t (monomial (divisorExponent Δ g) 1 * ∑ i,
      ((divisorExponent Δ g i : k) • residualFactor Δ g +
        X i * pderiv i (residualFactor Δ g))) = X j ^ p * (X j * pderiv j g') := by
    rw [← sum_X_mul_pderiv_monomial_mul, monomial_mul_residualFactor]
    exact pointChart_sum_X_mul_pderiv p h
  have hf' : X j * pderiv j g' ∈ logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g') := by
    rw [← pderiv_cleanPart p]
    exact X_mul_pderiv_mem_logJacobianTangent (mem_blowupDivisor.mpr (Or.inl rfl)) _
  exact le_antisymm
    (idealOrd_logJacobianTangent_cleanPart_le_of_pointChart_eq p hg hc hord h hA hρ' hEo hE hπ hf')
    (le_idealOrd_logJacobianTangent_cleanPart p hρ')

/-- **The first case is stable if no component leaves** (Volume 7, Section 3.9 of the handbook,
Theorem A of S7.14). Let `g ≠ 0` be clean with `ord g ≥ p`, let `π(g) = x_j^p g'` in the chart
`π = pointChart j t`, let `ρ(g) = d`, and let the order of `Θ₀(g)` be `|r| + d` (case A). Let
`ρ(g'_c) = d` for the new divisor `Δ' = blowupDivisor Δ j t`. If `t_i = 0` for each `i ∈ Δ` with
`i ≠ j`, then the new point is of case A: the order of `Θ₀(g'_c)` is `|r'| + d`, with
`r' = divisorExponent Δ' g'_c`. There is no hypothesis on `p`. -/
theorem idealOrd_logJacobianTangent_cleanPart_of_forall_eq_zero (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hρ : logJacobianOrder Δ g = d)
    (hA : idealOrd (logJacobianTangent Δ g) = ((degree (divisorExponent Δ g) + d : ℕ) : ℕ∞))
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d)
    (ht : ∀ i ∈ Δ, i ≠ j → t i = 0) :
    idealOrd (logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g')) =
      ((degree (divisorExponent (blowupDivisor Δ j t) (cleanPart p g')) + d : ℕ) : ℕ∞) := by
  by_cases hex : ∃ i ∈ Δ, i ≠ j ∧ ord ((divisorExponent Δ g i : k) • residualFactor Δ g +
      X i * pderiv i (residualFactor Δ g)) = d
  · obtain ⟨i, hi, hij, hio⟩ := hex
    exact idealOrd_logJacobianTangent_cleanPart_of_ne_of_eq_zero p hg hc hord h hA hρ' hi hij
      (ht i hi hij) hio
  push Not at hex
  obtain ⟨i, hi, hio⟩ := exists_mem_ord_smul_add_X_mul_pderiv_eq hρ hA
  obtain rfl : i = j := by
    by_contra hij
    exact hex i hi hij hio
  exact idealOrd_logJacobianTangent_cleanPart_of_lt_ord p hg hc hord h hρ hA hρ' hio fun l hl hlj =>
    lt_of_le_of_ne (le_ord_smul_add_X_mul_pderiv_of_idealOrd_eq hA hl) (hex l hl hlj).symm

end TheoremA

/-! ### Theorem B -/

section TheoremB

/-- **`τ_ρ` does not go down if no component leaves** (Volume 7, Section 3.9 of the handbook,
Theorem B of S7.14). Let `g ≠ 0` be clean with `ord g ≥ p`, let `π(g) = x_j^p g'` in the chart
`π = pointChart j t`, let `d = ord G` with `G = residualFactor Δ g`, let `ρ(g) = d`, and let the
order of `Θ₀(g)` be `|r| + d` (case A). Let `ρ(g'_c) = d` for the new divisor
`Δ' = blowupDivisor Δ j t`. If `t_i = 0` for each `i ∈ Δ` with `i ≠ j`, then
`dim T_ρ(g'_c) ≤ dim T_ρ(g)`. There is no hypothesis on `p`. If `|r| + d = 0` in `k`, the proof
uses `Φ_j = -∑_{i ≠ j} Φ_i`. -/
theorem finrank_logJacobianDirectrix_cleanPart_le_of_forall_eq_zero (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hG : ord (residualFactor Δ g) = d) (hρ : logJacobianOrder Δ g = d)
    (hA : idealOrd (logJacobianTangent Δ g) = ((degree (divisorExponent Δ g) + d : ℕ) : ℕ∞))
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d)
    (ht : ∀ i ∈ Δ, i ≠ j → t i = 0) :
    finrank k (logJacobianDirectrix (blowupDivisor Δ j t) (cleanPart p g')) ≤
      finrank k (logJacobianDirectrix Δ g) := by
  by_cases hpd : ((degree (divisorExponent Δ g) + d : ℕ) : k) ≠ 0
  · exact finrank_logJacobianDirectrix_cleanPart_le_of_ne_zero p hg hc hord h hG hρ hρ' hpd
  rw [not_not] at hpd
  -- The new point is of case A (Theorem A).
  have hA' := idealOrd_logJacobianTangent_cleanPart_of_forall_eq_zero p hg hc hord h hρ hA hρ' ht
  have hset : ∀ ψ ∈ logJacobianDirectrixSet Δ g,
      ord ψ = d ∧ monomial (divisorExponent Δ g) 1 * ψ ∈ logJacobianTangent Δ g := by
    intro ψ hψ
    obtain ⟨h1, h2⟩ := hψ
    rw [logJacobianCaseIdeal_of_eq (by rw [hA, hρ, Nat.cast_add])] at h2
    exact ⟨h1.trans hρ, h2⟩
  refine finrank_le_finrank_of_mem_of_forall_mem (j := j) (v := chartVector j t) ?_
    (by simp [chartVector]) ?_
  · refine (Submodule.mem_iInf _).mpr fun ψ => (Submodule.mem_iInf _).mpr fun hψ => ?_
    obtain ⟨ho, hm⟩ := hset ψ hψ
    rw [hρ, ENat.toNat_natCast]
    exact chartVector_mem_directrix_of_logJacobianOrder_eq p hg hc hord h hρ hρ' hm ho
  intro w hw hwj
  -- `w ∈ T(Φ_i)` for `i ≠ j`, from the exact transport of `e_i`.
  have hne : ∀ i, i ≠ j → w ∈ directrix (homogeneousComponent d
      ((divisorExponent Δ g i : k) • residualFactor Δ g + X i * pderiv i (residualFactor Δ g))) := by
    intro i hij
    by_cases hi : i ∈ Δ
    · by_cases hΦ : homogeneousComponent d ((divisorExponent Δ g i : k) • residualFactor Δ g +
          X i * pderiv i (residualFactor Δ g)) = 0
      · rw [hΦ, directrix_zero]
        exact Submodule.mem_top
      have hio : ord ((divisorExponent Δ g i : k) • residualFactor Δ g +
          X i * pderiv i (residualFactor Δ g)) = d :=
        le_antisymm (ord_le_of_homogeneousComponent_ne_zero hΦ)
          (le_ord_smul_add_X_mul_pderiv hG.ge _ i)
      have hπ : pointChart j t (monomial (divisorExponent Δ g) 1 *
          ((divisorExponent Δ g i : k) • residualFactor Δ g +
            X i * pderiv i (residualFactor Δ g))) = X j ^ p * (X i * pderiv i g') := by
        rw [← X_mul_pderiv_monomial_mul, monomial_mul_residualFactor]
        exact pointChart_X_mul_pderiv_of_ne_of_eq_zero p hij (ht i hi hij) h
      have hf' : X i * pderiv i g' ∈
          logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g') := by
        rw [← pderiv_cleanPart p]
        exact X_mul_pderiv_mem_logJacobianTangent
          (mem_blowupDivisor.mpr (Or.inr ⟨hi, hij, ht i hi hij⟩)) _
      exact mem_directrix_of_mem_logJacobianDirectrix_cleanPart p hg hc hord h hA hρ' hA' hio
        (monomial_mul_smul_add_X_mul_pderiv_mem hi) hπ hf' hw hwj
    · rw [homogeneousComponent_eq_zero_of_lt_ord (lt_of_lt_of_le
        (by exact_mod_cast Nat.lt_succ_self d)
        (natCast_succ_le_ord_smul_add_X_mul_pderiv_of_notMem hρ hi)), directrix_zero]
      exact Submodule.mem_top
  -- `w ∈ T(Φ_j)`, since `Φ_j = -∑_{i ≠ j} Φ_i` by the Euler identity and `|r| + d = 0` in `k`.
  have hj : w ∈ directrix (homogeneousComponent d
      ((divisorExponent Δ g j : k) • residualFactor Δ g + X j * pderiv j (residualFactor Δ g))) := by
    have hsum := homogeneousComponent_sum_smul_add_X_mul_pderiv d (divisorExponent Δ g)
      (residualFactor Δ g)
    rw [hpd, zero_smul, map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j),
      add_eq_zero_iff_eq_neg] at hsum
    rw [hsum]
    exact mem_directrixPolys_iff.mp (neg_mem (Submodule.sum_mem _ fun i hi =>
      mem_directrixPolys_iff.mpr (hne i (Finset.ne_of_mem_erase hi))))
  refine (Submodule.mem_iInf _).mpr fun ψ => (Submodule.mem_iInf _).mpr fun hψ => ?_
  obtain ⟨-, hm⟩ := hset ψ hψ
  rw [hρ, ENat.toNat_natCast]
  refine le_directrix_homogeneousComponent_of_mem_span (n := d) (W := Submodule.span k {w}) ?_ ?_
    (mem_residualLogJacobianTangent hm) (Submodule.mem_span_singleton_self w)
  · rintro s (⟨i, -, rfl⟩ | ⟨⟨a, l⟩, hl, rfl⟩)
    · exact le_ord_smul_add_X_mul_pderiv hG.ge _ i
    · exact le_trans (by exact_mod_cast Nat.le_succ d)
        (natCast_succ_le_ord_X_mul_pderiv_residualFactor hρ hl a)
  rintro s (⟨i, -, rfl⟩ | ⟨⟨a, l⟩, hl, rfl⟩)
  · refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
    by_cases hij : i = j
    · subst hij
      exact hj
    · exact hne i hij
  · dsimp only
    rw [homogeneousComponent_eq_zero_of_lt_ord (lt_of_lt_of_le
      (by exact_mod_cast Nat.lt_succ_self d)
      (natCast_succ_le_ord_X_mul_pderiv_residualFactor hρ hl a)), directrix_zero]
    exact le_top

/-- **`τ_ρ` does not go down if no component leaves**, the form with the codimension (Volume 7,
Section 3.9 of the handbook, Theorem B of S7.14). There is no hypothesis on `p`. -/
theorem logJacobianDirectrixCodim_le_cleanPart_of_forall_eq_zero (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hG : ord (residualFactor Δ g) = d) (hρ : logJacobianOrder Δ g = d)
    (hA : idealOrd (logJacobianTangent Δ g) = ((degree (divisorExponent Δ g) + d : ℕ) : ℕ∞))
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d)
    (ht : ∀ i ∈ Δ, i ≠ j → t i = 0) :
    logJacobianDirectrixCodim Δ g ≤
      logJacobianDirectrixCodim (blowupDivisor Δ j t) (cleanPart p g') := by
  have := finrank_logJacobianDirectrix_cleanPart_le_of_forall_eq_zero p hg hc hord h hG hρ hA hρ'
    ht
  unfold logJacobianDirectrixCodim
  omega

end TheoremB

end Singularity
