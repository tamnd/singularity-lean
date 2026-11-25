/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianDirectrixCaseA

/-!
# The full form of the directrix of the log-Jacobian order

Let `k` be a field of characteristic `p`, let `g ≠ 0` be a clean polynomial in `k[x_i : i ∈ σ]`
with `ord g ≥ p`, and let `Δ` give the divisor `E = V(∏_{i ∈ Δ} x_i)`. Write `g = x^r G`, with
`r = divisorExponent Δ g`, and let `ρ = logJacobianOrder Δ g`. The directrix `T_ρ(g)`
(`logJacobianDirectrix`) uses the ideal `Θ₀(g)` in case A and the ideal `Θ(g)` in case B. The full
form `T̃(g)` of the directrix uses `Θ(g)` in the two cases. It is the intersection of the
directrices `T(ψ_ρ)` of the parts `ψ_ρ` of degree `ρ` of the `ψ` with `ord ψ = ρ` and
`x^r ψ ∈ Θ(g)` (`logJacobianFullDirectrix`). Let `τ̃(g)` be the codimension of `T̃(g)`
(`logJacobianFullDirectrixCodim`).

Since `Θ₀(g) ⊆ Θ(g)`, `T̃(g) ⊆ T_ρ(g)` and `τ_ρ(g) ≤ τ̃(g)`. In case B, `T̃(g) = T_ρ(g)` and
`τ̃(g) = τ_ρ(g)`.

This file proves that `τ̃` does not go down at the points of a point blowup where `ρ` stays and
the old point is of case B (Volume 7, Section 3.8 of the handbook, Theorem 3.8.4). The proof is
the proof of Proposition 3.8.2 (`finrank_logJacobianDirectrix_cleanPart_le`). For each `ψ` of the
definition of `T_ρ(g)`, the chart sends `ψ` to `x_j^m ψ'` with `ord ψ' = m`, and
`x^{r'} U ψ' ∈ Θ(g'_c)`, with `U = chartUnit j t r` a unit
(`monomial_mul_chartUnit_mul_mem_logJacobian_cleanPart`). Thus `U ψ'` is in the definition of
`T̃(g'_c)` in the two cases of the new point. So `dim T̃(g'_c) ≤ dim T_ρ(g)` with no hypothesis on
the cases (`finrank_logJacobianFullDirectrix_cleanPart_le_logJacobianDirectrix`). If the old point
is of case B, then `T_ρ(g) = T̃(g)`, and `dim T̃(g'_c) ≤ dim T̃(g)`.

The case condition on the old point is necessary. Over `𝔽₂`, for `g = y z^2 + x z` and
`E = V(x z)`, the point is of case A, `τ_ρ(g) = 1` and `τ̃(g) = 2`. At the origin of the
`y`-chart, `ρ` stays `1`, the new point is of case A, and `τ_ρ(g'_c) = τ̃(g'_c) = 1`
(Example 3.8.5).

## Main definitions

* `logJacobianFullDirectrixSet Δ g`: the `ψ` with `ord ψ = ρ` and `x^r ψ ∈ Θ(g)`.
* `logJacobianFullDirectrix Δ g`: the full directrix `T̃(g)`.
* `logJacobianFullDirectrixCodim Δ g`: the codimension `τ̃(g)` of `T̃(g)`.

## Main results

* `logJacobianFullDirectrix_le_logJacobianDirectrix`, `logJacobianDirectrixCodim_le_fullDirectrixCodim`:
  `T̃(g) ⊆ T_ρ(g)` and `τ_ρ(g) ≤ τ̃(g)`.
* `logJacobianFullDirectrix_eq_of_ne`, `logJacobianFullDirectrixCodim_eq_of_ne`: `T̃(g) = T_ρ(g)`
  and `τ̃(g) = τ_ρ(g)` in case B.
* `finrank_logJacobianFullDirectrix_cleanPart_le_logJacobianDirectrix`: `dim T̃(g'_c) ≤ dim T_ρ(g)`
  if `ρ` stays.
* `finrank_logJacobianFullDirectrix_cleanPart_le`, `logJacobianFullDirectrixCodim_le_cleanPart`:
  Theorem 3.8.4.
* `fullDirectrixExample_finrank`, `fullDirectrixExample_codim`: Example 3.8.5.

## References

* Volume 7, Section 3.8 of the handbook: Proposition 3.8.2, Theorem 3.8.4 and Example 3.8.5.
-/

open MvPolynomial Finsupp Module

namespace Singularity

/-! ### The full directrix `T̃(g)` -/

section Def

variable {σ k : Type*} [Field k]

/-- The polynomials `ψ` of the definition of `T̃(g)`: `ord ψ = ρ` and `x^r ψ ∈ Θ(g)`. -/
def logJacobianFullDirectrixSet (Δ : Finset σ) (g : MvPolynomial σ k) : Set (MvPolynomial σ k) :=
  {ψ | ord ψ = logJacobianOrder Δ g ∧ monomial (divisorExponent Δ g) 1 * ψ ∈ logJacobian Δ g}

/-- **The full directrix `T̃(g)` of the log-Jacobian order** (Volume 7, Section 3.8 of the
handbook). The intersection of the directrices of the parts `ψ_ρ` of degree `ρ` of the `ψ` with
`ord ψ = ρ` and `x^r ψ ∈ Θ(g)`. -/
noncomputable def logJacobianFullDirectrix (Δ : Finset σ) (g : MvPolynomial σ k) :
    Submodule k (σ → k) :=
  ⨅ ψ ∈ logJacobianFullDirectrixSet Δ g,
    directrix (homogeneousComponent (logJacobianOrder Δ g).toNat ψ)

/-- The codimension `τ̃(g)` of the full directrix `T̃(g)`. -/
noncomputable def logJacobianFullDirectrixCodim [Fintype σ] (Δ : Finset σ)
    (g : MvPolynomial σ k) : ℕ :=
  Fintype.card σ - finrank k (logJacobianFullDirectrix Δ g)

theorem logJacobianFullDirectrix_le {Δ : Finset σ} {g ψ : MvPolynomial σ k}
    (hψ : ψ ∈ logJacobianFullDirectrixSet Δ g) :
    logJacobianFullDirectrix Δ g ≤
      directrix (homogeneousComponent (logJacobianOrder Δ g).toNat ψ) :=
  iInf₂_le ψ hψ

theorem le_logJacobianFullDirectrix {Δ : Finset σ} {g : MvPolynomial σ k}
    {W : Submodule k (σ → k)}
    (h : ∀ ψ ∈ logJacobianFullDirectrixSet Δ g,
      W ≤ directrix (homogeneousComponent (logJacobianOrder Δ g).toNat ψ)) :
    W ≤ logJacobianFullDirectrix Δ g :=
  le_iInf₂ h

/-- The ideal of the case of `g` is in `Θ(g)`. -/
theorem logJacobianCaseIdeal_le_logJacobian (Δ : Finset σ) (g : MvPolynomial σ k) :
    logJacobianCaseIdeal Δ g ≤ logJacobian Δ g := by
  unfold logJacobianCaseIdeal
  split_ifs
  · exact logJacobianTangent_le Δ g
  · exact le_rfl

/-- Each `ψ` of the definition of `T_ρ(g)` is in the definition of `T̃(g)`. -/
theorem logJacobianDirectrixSet_subset_fullDirectrixSet (Δ : Finset σ) (g : MvPolynomial σ k) :
    logJacobianDirectrixSet Δ g ⊆ logJacobianFullDirectrixSet Δ g :=
  fun _ hψ => ⟨hψ.1, logJacobianCaseIdeal_le_logJacobian Δ g hψ.2⟩

/-- **`T̃(g) ⊆ T_ρ(g)`** (Volume 7, Section 3.8 of the handbook). -/
theorem logJacobianFullDirectrix_le_logJacobianDirectrix (Δ : Finset σ) (g : MvPolynomial σ k) :
    logJacobianFullDirectrix Δ g ≤ logJacobianDirectrix Δ g :=
  le_logJacobianDirectrix fun _ hψ =>
    logJacobianFullDirectrix_le (logJacobianDirectrixSet_subset_fullDirectrixSet Δ g hψ)

/-- In case B, the definitions of `T̃(g)` and `T_ρ(g)` use the same `ψ`. -/
theorem logJacobianFullDirectrixSet_eq_of_ne {Δ : Finset σ} {g : MvPolynomial σ k}
    (h : idealOrd (logJacobianTangent Δ g) ≠ degree (divisorExponent Δ g) + logJacobianOrder Δ g) :
    logJacobianFullDirectrixSet Δ g = logJacobianDirectrixSet Δ g := by
  unfold logJacobianFullDirectrixSet logJacobianDirectrixSet
  rw [logJacobianCaseIdeal_of_ne h]

/-- **`T̃(g) = T_ρ(g)` in case B** (Volume 7, Section 3.8 of the handbook). If the order of
`Θ₀(g)` is not `|r| + ρ`, then `T̃(g) = T_ρ(g)`. -/
theorem logJacobianFullDirectrix_eq_of_ne {Δ : Finset σ} {g : MvPolynomial σ k}
    (h : idealOrd (logJacobianTangent Δ g) ≠ degree (divisorExponent Δ g) + logJacobianOrder Δ g) :
    logJacobianFullDirectrix Δ g = logJacobianDirectrix Δ g := by
  rw [logJacobianFullDirectrix, logJacobianDirectrix, logJacobianFullDirectrixSet_eq_of_ne h]

variable [Fintype σ]

/-- `dim T̃(g) ≤ dim T_ρ(g)`. -/
theorem finrank_logJacobianFullDirectrix_le (Δ : Finset σ) (g : MvPolynomial σ k) :
    finrank k (logJacobianFullDirectrix Δ g) ≤ finrank k (logJacobianDirectrix Δ g) :=
  Submodule.finrank_mono (logJacobianFullDirectrix_le_logJacobianDirectrix Δ g)

/-- **`τ_ρ(g) ≤ τ̃(g)`** (Volume 7, Section 3.8 of the handbook). -/
theorem logJacobianDirectrixCodim_le_fullDirectrixCodim (Δ : Finset σ) (g : MvPolynomial σ k) :
    logJacobianDirectrixCodim Δ g ≤ logJacobianFullDirectrixCodim Δ g := by
  have := finrank_logJacobianFullDirectrix_le Δ g
  unfold logJacobianDirectrixCodim logJacobianFullDirectrixCodim
  omega

/-- **`τ̃(g) = τ_ρ(g)` in case B** (Volume 7, Section 3.8 of the handbook). -/
theorem logJacobianFullDirectrixCodim_eq_of_ne {Δ : Finset σ} {g : MvPolynomial σ k}
    (h : idealOrd (logJacobianTangent Δ g) ≠ degree (divisorExponent Δ g) + logJacobianOrder Δ g) :
    logJacobianFullDirectrixCodim Δ g = logJacobianDirectrixCodim Δ g := by
  rw [logJacobianFullDirectrixCodim, logJacobianDirectrixCodim, logJacobianFullDirectrix_eq_of_ne h]

end Def

/-! ### Theorem 3.8.4 -/

section Theorem

variable {σ k : Type*} [Field k] [DecidableEq σ] [Fintype σ]

/-- **The dimension inequality for a family of transforms.** Let `S` and `S'` be sets of
polynomials, and let `U` have a nonzero constant term. Let each `ψ ∈ S` have `ord ψ = m`, let the
chart send `ψ` to `x_j^m ψ'` with `ord ψ' = m`, and let `U ψ' ∈ S'`. Then the dimension of the
intersection of the directrices of the parts of degree `m` of the elements of `S'` is at most the
dimension of the same intersection for `S`. -/
theorem finrank_iInf_directrix_le_of_chartTransform_mem {j : σ} {t : σ → k} {m : ℕ}
    {u : MvPolynomial σ k} (hu : constantCoeff u ≠ 0) {S S' : Set (MvPolynomial σ k)}
    (hS : ∀ ψ ∈ S, ord ψ = m ∧ ord (chartTransform j t m ψ) = m ∧
      u * chartTransform j t m ψ ∈ S') :
    finrank k (⨅ ψ ∈ S', directrix (homogeneousComponent m ψ) : Submodule k (σ → k)) ≤
      finrank k (⨅ ψ ∈ S, directrix (homogeneousComponent m ψ) : Submodule k (σ → k)) := by
  refine finrank_le_finrank_of_mem_of_forall_mem (j := j) (v := chartVector j t) ?_
    (by simp [chartVector]) ?_
  · refine (Submodule.mem_iInf _).mpr fun ψ => (Submodule.mem_iInf _).mpr fun hψ => ?_
    obtain ⟨h1, h2, -⟩ := hS ψ hψ
    exact mem_directrix_of_le_ord_pointChart h1.ge
      (pointChart_eq_X_pow_mul_chartTransform j t h1.ge) h2.ge
  · intro w hw hwj
    refine (Submodule.mem_iInf _).mpr fun ψ => (Submodule.mem_iInf _).mpr fun hψ => ?_
    obtain ⟨h1, h2, h3⟩ := hS ψ hψ
    have h4 := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hw _) h3
    rw [directrix_homogeneousComponent_mul hu h2.ge] at h4
    exact mem_directrix_of_mem_directrix_pointChart h1.ge
      (pointChart_eq_X_pow_mul_chartTransform j t h1.ge) h2.ge hwj h4

variable [DecidableEq k] (p : ℕ) [CharP k p] {Δ : Finset σ} {j : σ} {t : σ → k}
  {g g' : MvPolynomial σ k}

/-- **The transform of a `ψ` of `T_ρ(g)` is a `ψ` of `T̃(g'_c)`.** Let `g ≠ 0` be clean with
`ord g ≥ p`, let `π(g) = x_j^p g'`, and let `ρ(g'_c) = ρ(g) = m`. Let `ψ` be in the definition of
`T_ρ(g)`. Then `ord ψ = m`, the chart sends `ψ` to `x_j^m ψ'` with `ord ψ' = m`, and `U ψ'` is in
the definition of `T̃(g'_c)`, with `U = chartUnit j t r`. There is no hypothesis on the cases. -/
theorem chartUnit_mul_chartTransform_mem_logJacobianFullDirectrixSet (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m) {ψ : MvPolynomial σ k}
    (hψ : ψ ∈ logJacobianDirectrixSet Δ g) :
    ord ψ = m ∧ ord (chartTransform j t m ψ) = m ∧
      chartUnit j t (divisorExponent Δ g) * chartTransform j t m ψ ∈
        logJacobianFullDirectrixSet (blowupDivisor Δ j t) (cleanPart p g') := by
  have hψo : ord ψ = m := by rw [hψ.1, hρ]
  have hψ' := pointChart_eq_X_pow_mul_chartTransform j t hψo.ge
  obtain ⟨f, hf, τ, hτ, hπ⟩ :=
    exists_mem_logJacobianTangent_of_mem_logJacobianDirectrixSet hρ hψ hψ'
  have hle := logJacobianOrder_cleanPart_le_ord_of_pointChart_eq p hg hc hord h hτ hf hπ
  rw [hρ'] at hle
  have hψ'o : ord (chartTransform j t m ψ) = m :=
    le_antisymm (ord_le_of_pointChart hψo hψ') hle
  refine ⟨hψo, hψ'o, ?_, ?_⟩
  · rw [ord_mul, ord_chartUnit, zero_add, hψ'o, hρ']
  · exact monomial_mul_chartUnit_mul_mem_logJacobian_cleanPart p hg hc hord h hτ hf hπ hρ' hψ'o

/-- **`τ̃(g'_c) ≥ τ_ρ(g)` if `ρ` stays** (Volume 7, Section 3.8 of the handbook). Let `g ≠ 0` be
clean with `ord g ≥ p`, let `π(g) = x_j^p g'` in the chart `π = pointChart j t`, and let
`ρ(g'_c) = ρ(g) = m` for the new divisor `Δ' = blowupDivisor Δ j t`. Then
`dim T̃(g'_c) ≤ dim T_ρ(g)`. There is no hypothesis on the cases. -/
theorem finrank_logJacobianFullDirectrix_cleanPart_le_logJacobianDirectrix (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m) :
    finrank k (logJacobianFullDirectrix (blowupDivisor Δ j t) (cleanPart p g')) ≤
      finrank k (logJacobianDirectrix Δ g) := by
  have hU : constantCoeff (chartUnit j t (divisorExponent Δ g)) ≠ 0 := fun h0 => by
    have := one_le_ord_iff.mpr h0
    rw [ord_chartUnit] at this
    exact absurd this (by norm_num)
  rw [logJacobianFullDirectrix, logJacobianDirectrix, hρ, hρ', ENat.toNat_natCast]
  exact finrank_iInf_directrix_le_of_chartTransform_mem hU fun ψ hψ =>
    chartUnit_mul_chartTransform_mem_logJacobianFullDirectrixSet p hg hc hord h hρ hρ' hψ

/-- **`τ̃(g'_c) ≥ τ_ρ(g)` if `ρ` stays**, the form with the codimension (Volume 7, Section 3.8 of
the handbook). -/
theorem logJacobianDirectrixCodim_le_fullDirectrixCodim_cleanPart (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m) :
    logJacobianDirectrixCodim Δ g ≤
      logJacobianFullDirectrixCodim (blowupDivisor Δ j t) (cleanPart p g') := by
  have := finrank_logJacobianFullDirectrix_cleanPart_le_logJacobianDirectrix p hg hc hord h hρ hρ'
  unfold logJacobianDirectrixCodim logJacobianFullDirectrixCodim
  omega

/-- **`τ̃` does not go down from an old point of case B** (Volume 7, Section 3.8 of the handbook,
Theorem 3.8.4), the form with the hypothesis that the order of `Θ₀(g)` is not `|r| + ρ`. -/
theorem finrank_logJacobianFullDirectrix_cleanPart_le_of_ne (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m)
    (hB : idealOrd (logJacobianTangent Δ g) ≠ degree (divisorExponent Δ g) + logJacobianOrder Δ g) :
    finrank k (logJacobianFullDirectrix (blowupDivisor Δ j t) (cleanPart p g')) ≤
      finrank k (logJacobianFullDirectrix Δ g) := by
  rw [logJacobianFullDirectrix_eq_of_ne hB]
  exact finrank_logJacobianFullDirectrix_cleanPart_le_logJacobianDirectrix p hg hc hord h hρ hρ'

/-- **`τ̃` does not go down from an old point of case B** (Volume 7, Section 3.8 of the handbook,
Theorem 3.8.4). Let `g ≠ 0` be clean with `ord g ≥ p`, let `π(g) = x_j^p g'` in the chart
`π = pointChart j t`, and let `ρ(g'_c) = ρ(g) = m` for the new divisor `Δ' = blowupDivisor Δ j t`.
If the old point is of case B, that is the order of `Θ₀(g)` is `|r| + m + 1` with
`r = divisorExponent Δ g`, then `dim T̃(g'_c) ≤ dim T̃(g)`. There is no hypothesis on the case of
the new point. -/
theorem finrank_logJacobianFullDirectrix_cleanPart_le (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m)
    (hB : idealOrd (logJacobianTangent Δ g) =
      ((degree (divisorExponent Δ g) + m + 1 : ℕ) : ℕ∞)) :
    finrank k (logJacobianFullDirectrix (blowupDivisor Δ j t) (cleanPart p g')) ≤
      finrank k (logJacobianFullDirectrix Δ g) := by
  refine finrank_logJacobianFullDirectrix_cleanPart_le_of_ne p hg hc hord h hρ hρ' ?_
  rw [hB, hρ, ← Nat.cast_add]
  norm_cast
  omega

/-- **`τ̃` does not go down from an old point of case B**, the form with the codimension and with
the hypothesis that the order of `Θ₀(g)` is not `|r| + ρ` (Volume 7, Section 3.8 of the handbook,
Theorem 3.8.4). -/
theorem logJacobianFullDirectrixCodim_le_cleanPart_of_ne (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m)
    (hB : idealOrd (logJacobianTangent Δ g) ≠ degree (divisorExponent Δ g) + logJacobianOrder Δ g) :
    logJacobianFullDirectrixCodim Δ g ≤
      logJacobianFullDirectrixCodim (blowupDivisor Δ j t) (cleanPart p g') := by
  have := finrank_logJacobianFullDirectrix_cleanPart_le_of_ne p hg hc hord h hρ hρ' hB
  unfold logJacobianFullDirectrixCodim
  omega

/-- **`τ̃` does not go down from an old point of case B**, the form with the codimension
(Volume 7, Section 3.8 of the handbook, Theorem 3.8.4). If the order of `Θ₀(g)` is `|r| + m + 1`,
then `τ̃(g) ≤ τ̃(g'_c)`. -/
theorem logJacobianFullDirectrixCodim_le_cleanPart (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m)
    (hB : idealOrd (logJacobianTangent Δ g) =
      ((degree (divisorExponent Δ g) + m + 1 : ℕ) : ℕ∞)) :
    logJacobianFullDirectrixCodim Δ g ≤
      logJacobianFullDirectrixCodim (blowupDivisor Δ j t) (cleanPart p g') := by
  have := finrank_logJacobianFullDirectrix_cleanPart_le p hg hc hord h hρ hρ' hB
  unfold logJacobianFullDirectrixCodim
  omega

end Theorem

/-! ### Example 3.8.5 -/

section ExampleGeneral

variable {σ k : Type*} [Field k]

/-- If `x^r ψ ∈ Θ(g)` with `r = divisorExponent Δ g`, then `ψ ∈ Θ̃(G)` with
`G = residualFactor Δ g`. -/
theorem mem_residualLogJacobian_of_monomial_mul_mem {Δ : Finset σ} {g ψ : MvPolynomial σ k}
    (hψ : monomial (divisorExponent Δ g) 1 * ψ ∈ logJacobian Δ g) :
    ψ ∈ residualLogJacobian Δ (divisorExponent Δ g) (residualFactor Δ g) := by
  rw [logJacobian_eq_mul] at hψ
  obtain ⟨z, hz, hzeq⟩ := Ideal.mem_span_singleton_mul.mp hψ
  have hne : (monomial (divisorExponent Δ g) (1 : k)) ≠ 0 := by
    rw [Ne, monomial_eq_zero]
    exact one_ne_zero
  rwa [← mul_left_cancel₀ hne hzeq]

/-- The directrix of `x_i` is the hyperplane `w_i = 0`. -/
theorem mem_directrix_X_iff {i : σ} {w : σ → k} :
    w ∈ directrix (X i : MvPolynomial σ k) ↔ w i = 0 := by
  simpa using mem_directrix_X_pow_iff (i := i) (n := 1) (w := w) one_ne_zero

end ExampleGeneral

section Example

/-! The data of Example 3.8.5. The coordinates `(x, y, z)` are `X 0`, `X 1` and `X 2`. -/

local notation "fg" => (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2))
local notation "fG" => (X 1 * X 2 + X 0 : MvPolynomial (Fin 3) (ZMod 2))
local notation "fΔ" => ({0, 2} : Finset (Fin 3))
local notation "fΔ'" => ({0, 1, 2} : Finset (Fin 3))
local notation "fr" => (single 2 1 : Fin 3 →₀ ℕ)
local notation "fW" => (LinearMap.ker (LinearMap.funLeft (ZMod 2) (ZMod 2) ![(0 : Fin 3)]))
local notation "fW'" => (LinearMap.ker (LinearMap.funLeft (ZMod 2) (ZMod 2) ![(0 : Fin 3), 2]))

/-! ### General facts on the data -/

private theorem fde_two : (2 : MvPolynomial (Fin 3) (ZMod 2)) = 0 :=
  two_eq_zero_mvPolynomial_zmod (Fin 3)

private theorem fde_mon (a b : Fin 3 →₀ ℕ) :
    monomial (a + b) (1 : ZMod 2) = monomial a 1 * monomial b 1 := by
  rw [monomial_mul_monomial, mul_one]

private theorem fde_ne {a b : Fin 3 →₀ ℕ} (i : Fin 3) (h : a i ≠ b i) : a ≠ b :=
  fun hab => h (by rw [hab])

private theorem fde_hc_X (i : Fin 3) :
    homogeneousComponent 1 (X i : MvPolynomial (Fin 3) (ZMod 2)) = X i :=
  homogeneousComponent_eq_self (isHomogeneous_X _ i)

private theorem fde_lt_X_mul_X (i l : Fin 3) :
    ((1 : ℕ) : ℕ∞) < ord (X i * X l : MvPolynomial (Fin 3) (ZMod 2)) := by
  rw [ord_mul, ord_X, ord_X]
  norm_num

private theorem fde_finrank_ker {m : ℕ} (f : Fin m → Fin 3) (hf : Function.Injective f) :
    finrank (ZMod 2) (LinearMap.ker (LinearMap.funLeft (ZMod 2) (ZMod 2) f)) + m = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.funLeft (ZMod 2) (ZMod 2) f)
  rw [LinearMap.range_eq_top.mpr (LinearMap.funLeft_surjective_of_injective _ _ f hf),
    finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
  omega

private theorem fde_mem_W {w : Fin 3 → ZMod 2} : w ∈ fW ↔ w 0 = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    simpa using congrFun h 0
  · intro h0
    funext k
    fin_cases k
    simp [h0]

private theorem fde_mem_W' {w : Fin 3 → ZMod 2} : w ∈ fW' ↔ w 0 = 0 ∧ w 2 = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
  · rintro ⟨h0, h2⟩
    funext k
    fin_cases k <;> simp [h0, h2]

private theorem fde_g_monomials : fg =
    monomial (single 1 1 + single 2 2) 1 + monomial (single 0 1 + single 2 1) 1 := by
  simp only [fde_mon, ← X_pow_eq_monomial]
  ring

private theorem fde_isClean : IsClean 2 fg := by
  rw [fde_g_monomials]
  exact isClean_add (isClean_monomial (fun h => absurd (h 1) (by norm_num)) _)
    (isClean_monomial (fun h => absurd (h 0) (by norm_num)) _)

private theorem fde_monomial_r : (monomial fr 1 : MvPolynomial (Fin 3) (ZMod 2)) = X 2 := by
  rw [← X_pow_eq_monomial, pow_one]

private theorem fde_g_eq : fg = monomial fr 1 * fG := by
  rw [fde_monomial_r]
  ring

private theorem fde_G_monomials : fG =
    monomial (single 1 1 + single 2 1) 1 + monomial (single 0 1) 1 := by
  simp only [fde_mon, ← X_pow_eq_monomial]
  ring

private theorem fde_mem_G0 : (single 0 1 : Fin 3 →₀ ℕ) ∈ (fG).support := by
  rw [fde_G_monomials, MvPolynomial.mem_support_iff]
  simp [coeff_monomial, fde_ne (a := single 1 1 + single 2 1) (b := single 0 1) 0 (by simp)]

private theorem fde_mem_G1 : (single 1 1 + single 2 1 : Fin 3 →₀ ℕ) ∈ (fG).support := by
  rw [fde_G_monomials, MvPolynomial.mem_support_iff]
  simp [coeff_monomial, fde_ne (a := single 0 1) (b := single 1 1 + single 2 1) 0 (by simp)]

private theorem fde_hG (i : Fin 3) : ∃ d ∈ (fG).support, d i = 0 := by
  fin_cases i
  · exact ⟨_, fde_mem_G1, by simp⟩
  · exact ⟨_, fde_mem_G0, by simp⟩
  · exact ⟨_, fde_mem_G0, by simp⟩

private theorem fde_hr {Δ : Finset (Fin 3)} (h2 : 2 ∈ Δ) : ∀ i, i ∉ Δ → (fr : Fin 3 →₀ ℕ) i = 0 := by
  intro i hi
  have h : i ≠ 2 := fun h => hi (h ▸ h2)
  simp [h]

private theorem fde_rF {Δ : Finset (Fin 3)} (h2 : 2 ∈ Δ) : residualFactor Δ fg = fG := by
  rw [fde_g_eq]
  exact residualFactor_monomial_mul (fde_hr h2) fun i _ => fde_hG i

private theorem fde_dE {Δ : Finset (Fin 3)} (h2 : 2 ∈ Δ) : divisorExponent Δ fg = fr := by
  have hG0 : fG ≠ 0 := ne_zero_iff.mpr ⟨_, MvPolynomial.mem_support_iff.mp fde_mem_G0⟩
  have h1 : monomial (divisorExponent Δ fg) (1 : ZMod 2) * fG = monomial fr 1 * fG := by
    calc _ = fg := by
          rw [← fde_rF h2]
          exact monomial_mul_residualFactor _ _
      _ = _ := fde_g_eq
  exact monomial_left_injective one_ne_zero (mul_right_cancel₀ hG0 h1)

private theorem fde_deg : degree fr = 1 :=
  degree_single 2 1

private theorem fde_ord_G : ord fG = ((1 : ℕ) : ℕ∞) := by
  rw [add_comm, ord_add_of_lt (by rw [ord_X]; exact fde_lt_X_mul_X 1 2), ord_X, Nat.cast_one]

private theorem fde_ord_g : ord fg = ((2 : ℕ) : ℕ∞) := by
  rw [fde_g_eq, ord_mul, ord_monomial one_ne_zero, fde_deg, fde_ord_G]
  norm_num

private theorem fde_g_ne : fg ≠ 0 := by
  intro h
  have := fde_ord_g
  rw [h, ord_zero] at this
  exact ENat.top_ne_natCast 2 this

private theorem fde_pointChart : pointChart 1 (0 : Fin 3 → ZMod 2) fg = X 1 ^ 2 * fg := by
  simp [pointChart]
  ring

private theorem fde_blowupDivisor : blowupDivisor fΔ 1 (0 : Fin 3 → ZMod 2) = fΔ' := by
  decide

private theorem fde_cleanPart : cleanPart 2 fg = fg :=
  cleanPart_eq_self fde_isClean

/-! ### The generators -/

private theorem fde_e0 : ((fr 0 : ℕ) : ZMod 2) • fG + X 0 * pderiv 0 fG = X 0 := by
  simp [pderiv_X]

private theorem fde_e1 : ((fr 1 : ℕ) : ZMod 2) • fG + X 1 * pderiv 1 fG = X 1 * X 2 := by
  simp [pderiv_X]

private theorem fde_e2 : ((fr 2 : ℕ) : ZMod 2) • fG + X 2 * pderiv 2 fG = X 0 := by
  simp [pderiv_X]
  linear_combination (X 1 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) * fde_two

private theorem fde_pd1 : pderiv 1 fG = X 2 := by
  simp [pderiv_X]

private theorem fde_pd0 : pderiv 0 fg = X 2 := by
  simp [pderiv_X]

private theorem fde_pd1g : pderiv 1 fg = X 2 ^ 2 := by
  simp [pderiv_X]

private theorem fde_l1 {Δ : Finset (Fin 3)} (h0 : 0 ∈ Δ) (h2 : 2 ∈ Δ) {l : Fin 3} (hl : l ∉ Δ) :
    l = 1 := by
  fin_cases l
  · exact absurd h0 hl
  · rfl
  · exact absurd h2 hl

/-! ### The order `ρ` and the cases -/

private theorem fde_rho {Δ : Finset (Fin 3)} (h0 : 0 ∈ Δ) (h2 : 2 ∈ Δ) :
    logJacobianOrder Δ fg = ((1 : ℕ) : ℕ∞) := by
  rw [logJacobianOrder, fde_dE h2, fde_rF h2]
  refine le_antisymm ?_ ?_
  · have hm : ((fr 0 : ℕ) : ZMod 2) • fG + X 0 * pderiv 0 fG ∈ residualLogJacobian Δ fr fG :=
      Ideal.subset_span (Or.inl ⟨0, h0, rfl⟩)
    rw [fde_e0] at hm
    exact (idealOrd_le_ord hm).trans (by rw [ord_X, Nat.cast_one])
  · refine le_idealOrd_span ?_
    rintro s (⟨i, -, rfl⟩ | ⟨l, hl, rfl⟩)
    · exact le_ord_smul_add_X_mul_pderiv fde_ord_G.ge _ i
    · obtain rfl := fde_l1 h0 h2 hl
      dsimp only
      rw [fde_pd1, ord_X, Nat.cast_one]

/-- `Θ₀(g)` has order `2 = |r| + ρ(g)` (case A). -/
private theorem fde_caseA {Δ : Finset (Fin 3)} (h0 : 0 ∈ Δ) (h2 : 2 ∈ Δ) :
    idealOrd (logJacobianTangent Δ fg) = degree (divisorExponent Δ fg) + logJacobianOrder Δ fg := by
  rw [fde_dE h2, fde_rho h0 h2, fde_deg]
  refine le_antisymm ?_ ?_
  · refine (idealOrd_le_ord (X_mul_pderiv_mem_logJacobianTangent h0 fg)).trans (le_of_eq ?_)
    rw [fde_pd0, ord_mul, ord_X, ord_X]
    norm_num
  · refine le_trans (le_of_eq ?_) (le_idealOrd_logJacobianTangent (Δ := Δ) fde_ord_g.ge)
    norm_num

private theorem fde_hn {Δ : Finset (Fin 3)} (h0 : 0 ∈ Δ) (h2 : 2 ∈ Δ) :
    (logJacobianOrder Δ fg).toNat = 1 := by
  rw [fde_rho h0 h2]
  rfl

/-! ### The directrices -/

private theorem fde_mem_X0 {Δ : Finset (Fin 3)} (h0 : 0 ∈ Δ) (h2 : 2 ∈ Δ) :
    (X 0 : MvPolynomial (Fin 3) (ZMod 2)) ∈ logJacobianDirectrixSet Δ fg := by
  rw [logJacobianDirectrixSet, Set.mem_ofPred_eq, logJacobianCaseIdeal_of_eq (fde_caseA h0 h2),
    fde_dE h2, fde_rho h0 h2, fde_monomial_r, ord_X, Nat.cast_one]
  refine ⟨rfl, ?_⟩
  have h : (X 2 * X 0 : MvPolynomial (Fin 3) (ZMod 2)) = X 0 * pderiv 0 fg := by
    rw [fde_pd0, mul_comm]
  rw [h]
  exact X_mul_pderiv_mem_logJacobianTangent h0 fg

/-- `T_ρ(g) ⊆ {w_x = 0}`, for the two divisors. -/
private theorem fde_T_le {Δ : Finset (Fin 3)} (h0 : 0 ∈ Δ) (h2 : 2 ∈ Δ) :
    logJacobianDirectrix Δ fg ≤ fW := by
  intro w hw
  have h1 := logJacobianDirectrix_le (fde_mem_X0 h0 h2) hw
  rw [fde_hn h0 h2, fde_hc_X, mem_directrix_X_iff] at h1
  exact fde_mem_W.mpr h1

/-- The parts of degree `1` of the generators of `Θ̃₀(G)` for `Δ = {x, z}` are multiples of `x`. -/
private theorem fde_gen_tan (s : MvPolynomial (Fin 3) (ZMod 2))
    (hs : s ∈ (fun i => ((fr i : ℕ) : ZMod 2) • fG + X i * pderiv i fG) '' (fΔ : Set (Fin 3)) ∪
      (fun a : Fin 3 × Fin 3 => X a.1 * pderiv a.2 fG) '' {a | a.2 ∉ fΔ}) :
    ((1 : ℕ) : ℕ∞) ≤ ord s ∧
      homogeneousComponent 1 s ∈ Submodule.span (ZMod 2) {(X 0 : MvPolynomial (Fin 3) (ZMod 2))} := by
  rcases hs with ⟨i, hi, rfl⟩ | ⟨⟨a, l⟩, hl, rfl⟩
  · obtain rfl | rfl : i = 0 ∨ i = 2 := by simpa using hi
    all_goals dsimp only
    · rw [fde_e0, ord_X, fde_hc_X]
      exact ⟨by norm_num, Submodule.mem_span_singleton_self _⟩
    · rw [fde_e2, ord_X, fde_hc_X]
      exact ⟨by norm_num, Submodule.mem_span_singleton_self _⟩
  · obtain rfl := fde_l1 (Δ := fΔ) (by decide) (by decide) hl
    dsimp only
    rw [fde_pd1]
    refine ⟨(fde_lt_X_mul_X a 2).le, ?_⟩
    rw [homogeneousComponent_eq_zero_of_lt_ord (fde_lt_X_mul_X a 2)]
    exact zero_mem _

/-- The parts of degree `1` of the generators of `Θ̃(G)` for `Δ = {x, z}` are in the span of `x`
and `z`. -/
private theorem fde_gen_full (s : MvPolynomial (Fin 3) (ZMod 2))
    (hs : s ∈ (fun i => ((fr i : ℕ) : ZMod 2) • fG + X i * pderiv i fG) '' (fΔ : Set (Fin 3)) ∪
      (fun j => pderiv j fG) '' (fΔ : Set (Fin 3))ᶜ) :
    ((1 : ℕ) : ℕ∞) ≤ ord s ∧ homogeneousComponent 1 s ∈
      Submodule.span (ZMod 2) {(X 0 : MvPolynomial (Fin 3) (ZMod 2)), X 2} := by
  rcases hs with ⟨i, hi, rfl⟩ | ⟨l, hl, rfl⟩
  · obtain rfl | rfl : i = 0 ∨ i = 2 := by simpa using hi
    all_goals dsimp only
    · rw [fde_e0, ord_X, fde_hc_X]
      exact ⟨by norm_num, Submodule.subset_span (by simp)⟩
    · rw [fde_e2, ord_X, fde_hc_X]
      exact ⟨by norm_num, Submodule.subset_span (by simp)⟩
  · obtain rfl := fde_l1 (Δ := fΔ) (by decide) (by decide) hl
    dsimp only
    rw [fde_pd1, ord_X, fde_hc_X]
    exact ⟨by norm_num, Submodule.subset_span (by simp)⟩

/-- The parts of degree `1` of the generators of `Θ̃(G')` for `Δ' = {x, y, z}` are multiples of
`x`. -/
private theorem fde_gen_new (s : MvPolynomial (Fin 3) (ZMod 2))
    (hs : s ∈ (fun i => ((fr i : ℕ) : ZMod 2) • fG + X i * pderiv i fG) '' (fΔ' : Set (Fin 3)) ∪
      (fun j => pderiv j fG) '' (fΔ' : Set (Fin 3))ᶜ) :
    ((1 : ℕ) : ℕ∞) ≤ ord s ∧
      homogeneousComponent 1 s ∈ Submodule.span (ZMod 2) {(X 0 : MvPolynomial (Fin 3) (ZMod 2))} := by
  rcases hs with ⟨i, -, rfl⟩ | ⟨l, hl, rfl⟩
  · obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    all_goals dsimp only
    · rw [fde_e0, ord_X, fde_hc_X]
      exact ⟨by norm_num, Submodule.mem_span_singleton_self _⟩
    · rw [fde_e1]
      refine ⟨(fde_lt_X_mul_X 1 2).le, ?_⟩
      rw [homogeneousComponent_eq_zero_of_lt_ord (fde_lt_X_mul_X 1 2)]
      exact zero_mem _
    · rw [fde_e2, ord_X, fde_hc_X]
      exact ⟨by norm_num, Submodule.mem_span_singleton_self _⟩
  · exact absurd (by fin_cases l <;> decide) hl

/-- `T_ρ(g) = {w_x = 0}` at the old point. -/
private theorem fde_T_old : logJacobianDirectrix fΔ fg = fW := by
  refine le_antisymm (fde_T_le (by decide) (by decide)) ?_
  refine le_logJacobianDirectrix fun ψ hψ => ?_
  obtain ⟨-, hψ2⟩ := hψ
  rw [logJacobianCaseIdeal_of_eq (fde_caseA (by decide) (by decide))] at hψ2
  have hψ' := mem_residualLogJacobianTangent hψ2
  rw [fde_dE (by decide), fde_rF (by decide)] at hψ'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (homogeneousComponent_mem_of_mem_span fde_gen_tan hψ')
  rw [fde_hn (by decide) (by decide), ← hc]
  intro w hw
  exact directrix_le_directrix_smul c _ (mem_directrix_X_iff.mpr (fde_mem_W.mp hw))

/-- `T̃(g) = {w_x = w_z = 0}` at the old point. -/
private theorem fde_Tfull_old : logJacobianFullDirectrix fΔ fg = fW' := by
  have hn := fde_hn (Δ := fΔ) (by decide) (by decide)
  refine le_antisymm ?_ ?_
  · intro w hw
    have hX2 : (X 2 : MvPolynomial (Fin 3) (ZMod 2)) ∈ logJacobianFullDirectrixSet fΔ fg := by
      rw [logJacobianFullDirectrixSet, Set.mem_ofPred_eq, fde_dE (by decide),
        fde_rho (by decide) (by decide), fde_monomial_r, ord_X, Nat.cast_one]
      refine ⟨rfl, ?_⟩
      have h : (X 2 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) = pderiv 1 fg := by
        rw [fde_pd1g, sq]
      rw [h]
      exact pderiv_mem_logJacobian (by decide) fg
    have h0 := logJacobianFullDirectrix_le
      (logJacobianDirectrixSet_subset_fullDirectrixSet _ _ (fde_mem_X0 (by decide) (by decide))) hw
    have h2 := logJacobianFullDirectrix_le hX2 hw
    rw [hn, fde_hc_X, mem_directrix_X_iff] at h0 h2
    exact fde_mem_W'.mpr ⟨h0, h2⟩
  · refine le_logJacobianFullDirectrix fun ψ hψ => ?_
    rw [hn]
    have hψ' := mem_residualLogJacobian_of_monomial_mul_mem hψ.2
    rw [fde_dE (by decide), fde_rF (by decide)] at hψ'
    refine le_directrix_of_mem_span ?_ (homogeneousComponent_mem_of_mem_span fde_gen_full hψ')
    rintro s (rfl | rfl) w hw <;> obtain ⟨h0, h2⟩ := fde_mem_W'.mp hw
    · exact mem_directrix_X_iff.mpr h0
    · exact mem_directrix_X_iff.mpr h2

/-- `T̃(g'_c) ⊇ {w_x = 0}` at the new point. -/
private theorem fde_le_Tfull_new : fW ≤ logJacobianFullDirectrix fΔ' fg := by
  refine le_logJacobianFullDirectrix fun ψ hψ => ?_
  rw [fde_hn (by decide) (by decide)]
  have hψ' := mem_residualLogJacobian_of_monomial_mul_mem hψ.2
  rw [fde_dE (by decide), fde_rF (by decide)] at hψ'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (homogeneousComponent_mem_of_mem_span fde_gen_new hψ')
  rw [← hc]
  intro w hw
  exact directrix_le_directrix_smul c _ (mem_directrix_X_iff.mpr (fde_mem_W.mp hw))

/-- `T̃(g'_c) = {w_x = 0}` at the new point. -/
private theorem fde_Tfull_new : logJacobianFullDirectrix fΔ' fg = fW :=
  le_antisymm ((logJacobianFullDirectrix_le_logJacobianDirectrix _ _).trans
    (fde_T_le (by decide) (by decide))) fde_le_Tfull_new

/-- `T_ρ(g'_c) = {w_x = 0}` at the new point. -/
private theorem fde_T_new : logJacobianDirectrix fΔ' fg = fW :=
  le_antisymm (fde_T_le (by decide) (by decide))
    (fde_le_Tfull_new.trans (logJacobianFullDirectrix_le_logJacobianDirectrix _ _))

private theorem fde_finrank_W : finrank (ZMod 2) fW = 2 := by
  have := fde_finrank_ker ![(0 : Fin 3)] (by decide)
  omega

private theorem fde_finrank_W' : finrank (ZMod 2) fW' = 1 := by
  have := fde_finrank_ker ![(0 : Fin 3), 2] (by decide)
  omega

/-! ### The results -/

/-- **Example 3.8.5, the data** (Volume 7, Section 3.8 of the handbook). Over `𝔽₂`, let
`g = y z^2 + x z` and `E = V(x z)`. Then `g ≠ 0`, `g` is clean for `p = 2`, and `ord g ≥ 2`. In
the `y`-chart at the origin, `g` goes to `y^2 g`, so `g' = g`. The new divisor is `V(x y z)`, and
`g'_c = g`. The exponents are `r = r' = (0, 0, 1)`, and `G = G' = y z + x`. -/
theorem fullDirectrixExample_hyp :
    fg ≠ 0 ∧ IsClean 2 fg ∧ ((2 : ℕ) : ℕ∞) ≤ ord fg ∧
      pointChart 1 (0 : Fin 3 → ZMod 2) fg = X 1 ^ 2 * fg ∧
      blowupDivisor fΔ 1 (0 : Fin 3 → ZMod 2) = fΔ' ∧ cleanPart 2 fg = fg ∧
      divisorExponent fΔ fg = fr ∧ residualFactor fΔ fg = fG ∧
      divisorExponent fΔ' fg = fr ∧ residualFactor fΔ' fg = fG :=
  ⟨fde_g_ne, fde_isClean, fde_ord_g.ge, fde_pointChart, fde_blowupDivisor, fde_cleanPart,
    fde_dE (by decide), fde_rF (by decide), fde_dE (by decide), fde_rF (by decide)⟩

/-- **Example 3.8.5, the order `ρ`** (Volume 7, Section 3.8 of the handbook). Over `𝔽₂`, let
`g = y z^2 + x z` and `E = V(x z)`. Then `ρ(g) = 1`, and in the `y`-chart at the origin,
`ρ(g'_c) = 1`. So `ρ` stays. -/
theorem fullDirectrixExample_rho :
    logJacobianOrder fΔ fg = 1 ∧
      logJacobianOrder (blowupDivisor fΔ 1 (0 : Fin 3 → ZMod 2)) (cleanPart 2 fg) = 1 := by
  rw [fde_blowupDivisor, fde_cleanPart]
  exact ⟨by exact_mod_cast fde_rho (by decide) (by decide),
    by exact_mod_cast fde_rho (by decide) (by decide)⟩

/-- **Example 3.8.5, the cases** (Volume 7, Section 3.8 of the handbook). Over `𝔽₂`, let
`g = y z^2 + x z` and `E = V(x z)`. The point is of case A: the order of `Θ₀(g)` is
`|r| + ρ(g)`. In the `y`-chart at the origin, the new point is also of case A. -/
theorem fullDirectrixExample_cases :
    idealOrd (logJacobianTangent fΔ fg) =
        degree (divisorExponent fΔ fg) + logJacobianOrder fΔ fg ∧
      idealOrd (logJacobianTangent (blowupDivisor fΔ 1 (0 : Fin 3 → ZMod 2)) (cleanPart 2 fg)) =
        degree (divisorExponent (blowupDivisor fΔ 1 (0 : Fin 3 → ZMod 2)) (cleanPart 2 fg)) +
          logJacobianOrder (blowupDivisor fΔ 1 (0 : Fin 3 → ZMod 2)) (cleanPart 2 fg) := by
  rw [fde_blowupDivisor, fde_cleanPart]
  exact ⟨fde_caseA (by decide) (by decide), fde_caseA (by decide) (by decide)⟩

/-- **Example 3.8.5, the dimensions** (Volume 7, Section 3.8 of the handbook). Over `𝔽₂`, let
`g = y z^2 + x z` and `E = V(x z)`. Then `T_ρ(g) = {x = 0}` has dimension `2`, and
`T̃(g) = {x = z = 0}` has dimension `1`. In the `y`-chart at the origin, `T_ρ(g'_c)` and
`T̃(g'_c)` are both `{x = 0}`, of dimension `2`. So the dimension of `T̃` goes up from `1` to `2`
at a step from case A. -/
theorem fullDirectrixExample_finrank :
    finrank (ZMod 2) (logJacobianDirectrix fΔ fg) = 2 ∧
      finrank (ZMod 2) (logJacobianFullDirectrix fΔ fg) = 1 ∧
      finrank (ZMod 2)
        (logJacobianDirectrix (blowupDivisor fΔ 1 (0 : Fin 3 → ZMod 2)) (cleanPart 2 fg)) = 2 ∧
      finrank (ZMod 2)
        (logJacobianFullDirectrix (blowupDivisor fΔ 1 (0 : Fin 3 → ZMod 2)) (cleanPart 2 fg)) =
          2 := by
  rw [fde_blowupDivisor, fde_cleanPart, fde_T_old, fde_Tfull_old, fde_T_new, fde_Tfull_new]
  exact ⟨fde_finrank_W, fde_finrank_W', fde_finrank_W, fde_finrank_W⟩

/-- **Example 3.8.5: the case condition of Theorem 3.8.4 is necessary** (Volume 7, Section 3.8 of
the handbook). Over `𝔽₂`, let `g = y z^2 + x z` and `E = V(x z)`. Then `τ_ρ(g) = 1` and
`τ̃(g) = 2`. In the `y`-chart at the origin, `ρ` stays `1`, and `τ_ρ(g'_c) = τ̃(g'_c) = 1`. So
`τ̃` goes down from `2` to `1` at a step from case A, and `τ_ρ` stays `1`. -/
theorem fullDirectrixExample_codim :
    logJacobianDirectrixCodim fΔ fg = 1 ∧ logJacobianFullDirectrixCodim fΔ fg = 2 ∧
      logJacobianDirectrixCodim (blowupDivisor fΔ 1 (0 : Fin 3 → ZMod 2)) (cleanPart 2 fg) = 1 ∧
      logJacobianFullDirectrixCodim (blowupDivisor fΔ 1 (0 : Fin 3 → ZMod 2)) (cleanPart 2 fg) =
        1 := by
  obtain ⟨h1, h2, h3, h4⟩ := fullDirectrixExample_finrank
  unfold logJacobianDirectrixCodim logJacobianFullDirectrixCodim
  rw [h1, h2, h3, h4, Fintype.card_fin]
  exact ⟨rfl, rfl, rfl, rfl⟩

end Example

end Singularity
