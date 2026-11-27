/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianDirectrixCaseA
import Singularity.Invariant.LogJacobianTypeSwitch

/-!
# The points where `ρ` stays lie in the directrix

Let `k` be a field of characteristic `p`, let `g ≠ 0` be a clean polynomial in `k[x_i : i ∈ σ]`
with `ord g ≥ p`, and let `Δ` give the divisor `E = V(∏_{i ∈ Δ} x_i)`. Write `g = x^r G`, with
`r = divisorExponent Δ g` and `G = residualFactor Δ g`, and let `ρ = logJacobianOrder Δ g`. Let
`σ` be the order of the residual ideal `Θ̃_C(G)` (`residualLogJacobianTangent`). Then `σ = ρ` or
`σ = ρ + 1`. Corollary 3.15 of research note 03 takes the ideal

  `I = Θ̃_C(G)` if `σ = ρ`, and `I = Θ̃(G)` if `σ = ρ + 1` (`residualLogJacobianCaseIdeal`).

Let the chart `π = pointChart j t` send `g` to `x_j^p g'`, and let `v = (1, t)` be the vector of the
chart (`chartVector j t`), with `v_j = 1` and `v_i = t_i` for `i ≠ j`. Let `g'_c` be the clean part
of `g'` and `Δ' = blowupDivisor Δ j t`. Corollary 3.15 says: if `ρ(g'_c) = ρ`, then the part of
degree `ρ` of each element of `I` is invariant under the translation by `v`. In other words, `v`
lies in the directrix `T_ρ(g)` of the parts of degree `ρ` (`logJacobianDirectrix`). In particular
this holds at each kangaroo point, where the residual order goes up.

This file proves the corollary in this form.

* `chartVector_mem_directrix_of_mem_residualLogJacobianCaseIdeal`: for each `ψ ∈ I`, `v` lies in
  the directrix of the part `ψ_ρ` of degree `ρ` of `ψ`. There is no hypothesis on `ord ψ`: if
  `ord ψ > ρ`, then `ψ_ρ = 0`, and each vector is in the directrix of `0`.
* `chartVector_mem_logJacobianDirectrix`: `v ∈ T_ρ(g)`.
* `chartVector_mem_logJacobianDirectrix_of_residualOrderAlong_eq_add_one`: the same at a kangaroo
  point, that is if `d' = d + 1` for the residual orders.
* `logJacobianOrder_cleanPart_lt_of_not_mem_directrix`: the contrapositive. If `v` is not in the
  directrix of `ψ_ρ` for some `ψ ∈ I`, then `ρ(g'_c) < ρ`.

The proof. The library proves Theorem 3.7.1 of Volume 7 of the handbook for the `ψ` with
`ord ψ = ρ` and `x^r ψ` in `Θ₀(g)` (case A) or in `Θ(g)` (case B). The chart sends such a `ψ` to
`x_j^ρ ψ'`, and the proof of Theorem 3.2.4 gives `ρ(g'_c) ≤ ord ψ'`
(`logJacobianOrder_cleanPart_le_ord_of_pointChart_eq`). So `ord ψ' ≥ ρ`, and the argument of
Hironaka puts `v` in the directrix of `ψ_ρ` (`mem_directrix_of_le_ord_pointChart`). For an element
`ψ` of `I`, `x^r ψ` is in `Θ₀(g) = x^r Θ̃_C(G)` or in `Θ(g) = x^r Θ̃(G)`. Since `Θ₀(g) ⊆ Θ(g)`,
`ord ψ ≥ ρ`. If `ψ_ρ ≠ 0`, then `ord ψ = ρ`, and the result above applies.

## Main definitions

* `Singularity.residualLogJacobianCaseIdeal Δ g`: the ideal `I` of Corollary 3.15.

## Main results

* `chartVector_mem_directrix_of_mem_logJacobianCaseIdeal`,
  `chartVector_mem_directrix_of_mem_residualLogJacobianCaseIdeal`: Corollary 3.15 for each
  element of `I`.
* `chartVector_mem_logJacobianDirectrix`: Corollary 3.15, `v ∈ T_ρ(g)`.
* `chartVector_mem_logJacobianDirectrix_of_residualOrderAlong_eq_add_one`: Corollary 3.15 at a
  kangaroo point.
* `logJacobianOrder_cleanPart_lt_of_not_mem_directrix`: `ρ` goes down at the points outside the
  directrix.

## References

* Research note 03, Section 3.6: Theorem 3.12 and Corollaries 3.14 and 3.15.
* Volume 7, Sections 3.2, 3.7 and 3.8 of the handbook: Theorems 3.2.4 and 3.7.1.
-/

open MvPolynomial

namespace Singularity

section Def

variable {σ k : Type*} [Field k]

/-- The ideal `I` of Corollary 3.15 of research note 03: `Θ̃_C(G)` if the order of `Θ₀(g)` is
`|r| + ρ` (case A, `σ = ρ`), and `Θ̃(G)` otherwise (case B, `σ = ρ + 1`). Here `g = x^r G`. -/
noncomputable def residualLogJacobianCaseIdeal (Δ : Finset σ) (g : MvPolynomial σ k) :
    Ideal (MvPolynomial σ k) :=
  if idealOrd (logJacobianTangent Δ g) =
      Finsupp.degree (divisorExponent Δ g) + logJacobianOrder Δ g then
    residualLogJacobianTangent Δ (divisorExponent Δ g) (residualFactor Δ g)
  else residualLogJacobian Δ (divisorExponent Δ g) (residualFactor Δ g)

/-- `Θ₀(g) = x^r Θ̃_C(G)` for `g = x^r G`. -/
theorem logJacobianTangent_eq_mul (Δ : Finset σ) (g : MvPolynomial σ k) :
    logJacobianTangent Δ g = Ideal.span {monomial (divisorExponent Δ g) 1} *
      residualLogJacobianTangent Δ (divisorExponent Δ g) (residualFactor Δ g) := by
  conv_lhs => rw [← monomial_mul_residualFactor Δ g]
  exact logJacobianTangent_monomial_mul (fun _ hi => divisorExponent_eq_zero hi) _

/-- If `ψ ∈ I`, then `x^r ψ` is in the ideal of the case of `g` (`logJacobianCaseIdeal`). -/
theorem monomial_mul_mem_logJacobianCaseIdeal {Δ : Finset σ} {g ψ : MvPolynomial σ k}
    (hψ : ψ ∈ residualLogJacobianCaseIdeal Δ g) :
    monomial (divisorExponent Δ g) 1 * ψ ∈ logJacobianCaseIdeal Δ g := by
  unfold residualLogJacobianCaseIdeal at hψ
  unfold logJacobianCaseIdeal
  split_ifs at hψ ⊢
  · rw [logJacobianTangent_eq_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hψ
  · rw [logJacobian_eq_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hψ

/-- The ideal of the case of `g` is contained in `Θ(g)`. -/
theorem logJacobianCaseIdeal_le (Δ : Finset σ) (g : MvPolynomial σ k) :
    logJacobianCaseIdeal Δ g ≤ logJacobian Δ g := by
  unfold logJacobianCaseIdeal
  split_ifs
  · exact logJacobianTangent_le Δ g
  · exact le_rfl

/-- If `x^r ψ ∈ Θ(g)`, then `ρ ≤ ord ψ`. -/
theorem logJacobianOrder_le_ord_of_monomial_mul_mem {Δ : Finset σ} {g ψ : MvPolynomial σ k}
    (hψ : monomial (divisorExponent Δ g) 1 * ψ ∈ logJacobian Δ g) :
    logJacobianOrder Δ g ≤ ord ψ := by
  have h := idealOrd_le_ord hψ
  rw [idealOrd_logJacobian, ord_mul, ord_monomial one_ne_zero] at h
  exact (ENat.add_le_add_iff_left (ENat.natCast_ne_top _)).mp h

end Def

section RhoConstant

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- **Where `ρ` can stay, for the ideal of the case** (research note 03, Corollary 3.15). Let
`g ≠ 0` be clean with `ord g ≥ p`, let `π(g) = x_j^p g'` in the chart `π = pointChart j t`, and let
`ρ(g'_c) = ρ(g) = m` for the new divisor `Δ' = blowupDivisor Δ j t`. Then for each `ψ` with `x^r ψ`
in `Θ₀(g)` (case A) or in `Θ(g)` (case B), the vector of the chart lies in the directrix of the
part `ψ_m` of `ψ` of degree `m`. -/
theorem chartVector_mem_directrix_of_mem_logJacobianCaseIdeal (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m) {ψ : MvPolynomial σ k}
    (hψ : monomial (divisorExponent Δ g) 1 * ψ ∈ logJacobianCaseIdeal Δ g) :
    chartVector j t ∈ directrix (homogeneousComponent m ψ) := by
  by_cases h0 : homogeneousComponent m ψ = 0
  · rw [h0, directrix_zero]
    exact Submodule.mem_top
  have hle : (m : ℕ∞) ≤ ord ψ := by
    rw [← hρ]
    exact logJacobianOrder_le_ord_of_monomial_mul_mem (logJacobianCaseIdeal_le Δ g hψ)
  have hψo : ord ψ = m := le_antisymm (ord_le_of_homogeneousComponent_ne_zero h0) hle
  have hmem : ψ ∈ logJacobianDirectrixSet Δ g := ⟨by rw [hψo, hρ], hψ⟩
  obtain ⟨ψ', hψ'⟩ := exists_pointChart_eq_X_pow_mul (j := j) (t := t) hle
  obtain ⟨f, hf, τ, hτ, hπ⟩ :=
    exists_mem_logJacobianTangent_of_mem_logJacobianDirectrixSet hρ hmem hψ'
  have hle' := logJacobianOrder_cleanPart_le_ord_of_pointChart_eq p hg hc hord h hτ hf hπ
  rw [hρ'] at hle'
  exact mem_directrix_of_le_ord_pointChart hle hψ' hle'

/-- **Where `ρ` can stay** (research note 03, Corollary 3.15). Let `g ≠ 0` be clean with
`ord g ≥ p`, let `π(g) = x_j^p g'` in the chart `π = pointChart j t`, and let `ρ(g'_c) = ρ(g) = m`
for the new divisor `Δ' = blowupDivisor Δ j t`. Let `I` be `Θ̃_C(G)` if `σ = ρ` and `Θ̃(G)` if
`σ = ρ + 1`. Then for each `ψ ∈ I`, the part `ψ_m` of degree `m` of `ψ` is invariant under the
translation by the vector `v` of the chart: `v` lies in the directrix of `ψ_m`. -/
theorem chartVector_mem_directrix_of_mem_residualLogJacobianCaseIdeal (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m) {ψ : MvPolynomial σ k}
    (hψ : ψ ∈ residualLogJacobianCaseIdeal Δ g) :
    chartVector j t ∈ directrix (homogeneousComponent m ψ) :=
  chartVector_mem_directrix_of_mem_logJacobianCaseIdeal p hg hc hord h hρ hρ'
    (monomial_mul_mem_logJacobianCaseIdeal hψ)

/-- **The point lies in the directrix** (research note 03, Corollary 3.15). Let `g ≠ 0` be clean
with `ord g ≥ p`, and let `π(g) = x_j^p g'` in the chart `π = pointChart j t`. If
`ρ(g'_c) = ρ(g)` for the new divisor `Δ' = blowupDivisor Δ j t`, then the vector of the chart lies
in the directrix `T_ρ(g)`. -/
theorem chartVector_mem_logJacobianDirectrix (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g')
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = logJacobianOrder Δ g) :
    chartVector j t ∈ logJacobianDirectrix Δ g := by
  refine (Submodule.mem_iInf _).mpr fun ψ => (Submodule.mem_iInf _).mpr fun hψ => ?_
  have hψo : ord ψ = logJacobianOrder Δ g := hψ.1
  cases hρ : logJacobianOrder Δ g using ENat.recTopCoe with
  | top =>
    rw [hρ, ord_eq_top_iff] at hψo
    rw [hψo, map_zero, directrix_zero]
    exact Submodule.mem_top
  | coe m =>
    rw [hρ] at hρ'
    rw [ENat.toNat_natCast]
    exact chartVector_mem_directrix_of_mem_logJacobianCaseIdeal p hg hc hord h hρ hρ' hψ.2

/-- **Kangaroo points lie in the directrix** (research note 03, Corollary 3.15). Let `g ≠ 0` be
clean with `ord g ≥ p`, and let `π(g) = x_j^p g'` in the chart `π = pointChart j t`. If the
residual order goes up, `d' = d + 1`, then the vector of the chart lies in the directrix `T_ρ(g)`.
-/
theorem chartVector_mem_logJacobianDirectrix_of_residualOrderAlong_eq_add_one (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g')
    (hd : residualOrderAlong (blowupDivisor Δ j t) p g' = residualOrderAlong Δ p g + 1) :
    chartVector j t ∈ logJacobianDirectrix Δ g :=
  chartVector_mem_logJacobianDirectrix p hg hc hord h (kangaroo_type_switch p hg hc hord h hd).1

/-- **`ρ` goes down outside the directrix** (research note 03, Corollary 3.15). Let `g ≠ 0` be
clean with `ord g ≥ p`, let `ρ(g) = m`, and let `π(g) = x_j^p g'` in the chart
`π = pointChart j t`. If some `ψ ∈ I` has a part `ψ_m` of degree `m` whose directrix does not
contain the vector of the chart, then `ρ(g'_c) < m` for the new divisor `Δ' = blowupDivisor Δ j t`.
-/
theorem logJacobianOrder_cleanPart_lt_of_not_mem_directrix (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m) {ψ : MvPolynomial σ k}
    (hψ : ψ ∈ residualLogJacobianCaseIdeal Δ g)
    (hv : chartVector j t ∉ directrix (homogeneousComponent m ψ)) :
    logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') < m := by
  have hle := (logJacobianOrder_cleanPart_le p (Δ := Δ) hg hc hord h).2
  rw [hρ] at hle
  exact lt_of_le_of_ne hle fun heq =>
    hv (chartVector_mem_directrix_of_mem_residualLogJacobianCaseIdeal p hg hc hord h hρ heq hψ)

end RhoConstant

end Singularity
