/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobian

/-!
# The end case `ρ = 0` of the log-Jacobian ideal

Let `k` be a field of characteristic `p`, let `E = V(∏_{i ∈ Δ} x_i)`, and write `g = x^r G` with
`r = divisorExponent Δ g` and `G = residualFactor Δ g`. Let `ρ = logJacobianOrder Δ g` be the
order of the residual log-Jacobian ideal

  `Θ̃(G) = (r_i G + x_i ∂_i G (i ∈ Δ), ∂_j G (j ∉ Δ))`.

This file proves the end case of the log-Jacobian route (Volume 7, Section 3.5 of the handbook,
Proposition 3.5.1). For a clean `g`, `ρ = 0` if and only if one of these holds.

1. Type 0: `G(0) ≠ 0`, and `p ∤ r_i` for some `i ∈ Δ`.
2. Type 1: `G(0) = 0`, and `∂_j G(0) ≠ 0` for some free coordinate `x_j`, `j ∉ Δ`.

In type 0 the order of `G` is `0`. In type 1 the order of `G` is `1`.

The proof uses the constant terms of the generators. The constant term of `r_i G + x_i ∂_i G` is
`r_i G(0)`, because `x_i ∂_i G` has no constant term. The constant term of `∂_j G` is the
coefficient of `x_j` in `G`. An ideal has order `0` if and only if one of its generators has a
nonzero constant term (`idealOrd_span_eq_zero_iff`). So `ρ = 0` if and only if `r_i G(0) ≠ 0` in
`k` for some `i ∈ Δ`, or `∂_j G(0) ≠ 0` for some `j ∉ Δ` (`logJacobianOrder_eq_zero_iff_exists`).
This step does not use that `g` is clean.

Cleanness is necessary only for type 0. The coefficient of `x^r` in `g` is `G(0)`. If `G(0) ≠ 0`,
then `r` is an exponent of `g`. A clean `g` has no exponent in `p ℕ^n`, so `p ∤ r_i` for some
`i`. Since `r` is supported in `Δ`, this `i` is in `Δ`
(`exists_not_dvd_divisorExponent_of_constantCoeff_ne_zero`).

## Main results

* `idealOrd_span_eq_zero_iff`: an ideal has order `0` if and only if a generator has a nonzero
  constant term.
* `logJacobianOrder_eq_zero_iff_exists`: `ρ = 0` if and only if `r_i G(0) ≠ 0` for some `i ∈ Δ`
  or `∂_j G(0) ≠ 0` for some `j ∉ Δ`, for each `g`.
* `logJacobianOrder_eq_zero_type_zero`: for a clean `g` with `ord G = 0`, `ρ = 0`, `G(0) ≠ 0` and
  `p ∤ r_i` for some `i ∈ Δ`.
* `exists_constantCoeff_pderiv_ne_zero`: if `ρ = 0` and `ord G = 1`, then `∂_j G(0) ≠ 0` for
  some `j ∉ Δ`.
* `logJacobianOrder_eq_zero_of_type_zero`, `logJacobianOrder_eq_zero_of_type_one`: the
  converses.
* `logJacobianOrder_eq_zero_iff`, `logJacobianOrder_eq_zero_iff_ord`: Proposition 3.5.1, `ρ = 0`
  if and only if type 0 or type 1 holds, for a clean `g`.

## References

* V. Cossart, O. Piltant, *Resolution of singularities of threefolds in positive characteristic
  I*, J. Algebra 320 (2008).
* J. Giraud, *Contact maximal en caractéristique positive*, Ann. Sci. ENS 8 (1975).
* Volume 7, Section 3.5 of the handbook: Proposition 3.5.1.
-/

open MvPolynomial Finsupp

namespace Singularity

/-! ### Order zero and constant terms -/

section Semiring

variable {σ k : Type*} [CommSemiring k]

/-- A polynomial has order `0` if and only if its constant term is not `0`. -/
theorem ord_eq_zero_iff_constantCoeff_ne_zero {f : MvPolynomial σ k} :
    ord f = 0 ↔ constantCoeff f ≠ 0 := by
  rw [ne_eq, ← one_le_ord_iff, not_le, Order.lt_one_iff]

/-- An ideal has order `0` if and only if one of its generators has a nonzero constant term. -/
theorem idealOrd_span_eq_zero_iff {S : Set (MvPolynomial σ k)} :
    idealOrd (Ideal.span S) = 0 ↔ ∃ s ∈ S, constantCoeff s ≠ 0 := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have h1 : (1 : ℕ∞) ≤ idealOrd (Ideal.span S) :=
      le_idealOrd_span fun s hs => one_le_ord_iff.mpr (hne s hs)
    rw [h] at h1
    exact absurd h1 (by norm_num)
  · rintro ⟨s, hs, hne⟩
    exact nonpos_iff_eq_zero.mp ((idealOrd_le_ord (Ideal.subset_span hs)).trans
      (ord_eq_zero_iff_constantCoeff_ne_zero.mpr hne).le)

/-- The constant term of the generator `r_i G + x_i ∂_i G` is `r_i G(0)`. -/
theorem constantCoeff_smul_add_X_mul_pderiv (r : σ →₀ ℕ) (i : σ) (G : MvPolynomial σ k) :
    constantCoeff ((r i : k) • G + X i * pderiv i G) = (r i : k) * constantCoeff G := by
  have h := coeff_smul_add_X_mul_pderiv r i G 0
  simp only [Finsupp.coe_zero, Pi.zero_apply, add_zero] at h
  simpa only [constantCoeff_eq] using h

/-- The order of `Θ̃(G)` is `0` if and only if `r_i G(0) ≠ 0` for some `i ∈ Δ` or `∂_j G(0) ≠ 0`
for some `j ∉ Δ`. -/
theorem idealOrd_residualLogJacobian_eq_zero_iff (Δ : Finset σ) (r : σ →₀ ℕ)
    (G : MvPolynomial σ k) :
    idealOrd (residualLogJacobian Δ r G) = 0 ↔
      (∃ i ∈ Δ, (r i : k) * constantCoeff G ≠ 0) ∨
        ∃ j ∉ Δ, constantCoeff (pderiv j G) ≠ 0 := by
  rw [residualLogJacobian, idealOrd_span_eq_zero_iff]
  constructor
  · rintro ⟨s, ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩, hne⟩
    · exact Or.inl ⟨i, hi, by rwa [constantCoeff_smul_add_X_mul_pderiv] at hne⟩
    · exact Or.inr ⟨j, hj, hne⟩
  · rintro (⟨i, hi, hne⟩ | ⟨j, hj, hne⟩)
    · exact ⟨_, Or.inl ⟨i, hi, rfl⟩, by rwa [constantCoeff_smul_add_X_mul_pderiv]⟩
    · exact ⟨_, Or.inr ⟨j, hj, rfl⟩, hne⟩

/-- `ρ = 0` if and only if `r_i G(0) ≠ 0` for some `i ∈ Δ` or `∂_j G(0) ≠ 0` for some `j ∉ Δ`.
This form does not need that `g` is clean. -/
theorem logJacobianOrder_eq_zero_iff_exists (Δ : Finset σ) (g : MvPolynomial σ k) :
    logJacobianOrder Δ g = 0 ↔
      (∃ i ∈ Δ, (divisorExponent Δ g i : k) * constantCoeff (residualFactor Δ g) ≠ 0) ∨
        ∃ j ∉ Δ, constantCoeff (pderiv j (residualFactor Δ g)) ≠ 0 :=
  idealOrd_residualLogJacobian_eq_zero_iff Δ _ _

/-- If `G(0) = 0` and `∂_j G(0) ≠ 0`, then `ord G = 1`. -/
theorem ord_eq_one_of_constantCoeff_pderiv_ne_zero {G : MvPolynomial σ k}
    (h0 : constantCoeff G = 0) {j : σ} (hj : constantCoeff (pderiv j G) ≠ 0) : ord G = 1 := by
  refine le_antisymm ?_ (one_le_ord_iff.mpr h0)
  simp only [constantCoeff_eq, coeff_pderiv, zero_add, Finsupp.coe_zero, Pi.zero_apply,
    Nat.cast_zero, mul_one] at hj
  refine (ord_le hj).trans ?_
  rw [degree_single, Nat.cast_one]

end Semiring

/-! ### The two types -/

section Field

variable {σ k : Type*} [Field k] (p : ℕ) [CharP k p] {Δ : Finset σ} {g : MvPolynomial σ k}

omit [CharP k p] in
/-- The coefficient of `x^r` in `g` is `G(0)`. -/
theorem coeff_divisorExponent (Δ : Finset σ) (g : MvPolynomial σ k) :
    g.coeff (divisorExponent Δ g) = constantCoeff (residualFactor Δ g) := by
  rw [constantCoeff_eq, residualFactor, coeff_divMonomial, add_zero]

omit [CharP k p] in
/-- For a clean `g` with `G(0) ≠ 0`, `p ∤ r_i` for some `i ∈ Δ`. The exponent `r` of `g` is not
in `p ℕ^n`, and `r` is supported in `Δ`. -/
theorem exists_not_dvd_divisorExponent_of_constantCoeff_ne_zero (hc : IsClean p g)
    (h0 : constantCoeff (residualFactor Δ g) ≠ 0) : ∃ i ∈ Δ, ¬ p ∣ divisorExponent Δ g i := by
  have hr : divisorExponent Δ g ∈ g.support := by
    rw [MvPolynomial.mem_support_iff, coeff_divisorExponent]
    exact h0
  obtain ⟨i, hi⟩ := not_forall.mp (hc _ hr)
  refine ⟨i, ?_, hi⟩
  by_contra hiΔ
  rw [divisorExponent_eq_zero hiΔ] at hi
  exact hi (dvd_zero p)

/-- **The converse for type 0**: if `G(0) ≠ 0` and `p ∤ r_i` for some `i ∈ Δ`, then `ρ = 0`.
The constant term of `r_i G + x_i ∂_i G` is `r_i G(0) ≠ 0`. -/
theorem logJacobianOrder_eq_zero_of_type_zero (h0 : constantCoeff (residualFactor Δ g) ≠ 0)
    {i : σ} (hi : i ∈ Δ) (hp : ¬ p ∣ divisorExponent Δ g i) : logJacobianOrder Δ g = 0 :=
  (logJacobianOrder_eq_zero_iff_exists Δ g).mpr
    (Or.inl ⟨i, hi, mul_ne_zero ((CharP.cast_eq_zero_iff k p _).not.mpr hp) h0⟩)

omit [CharP k p] in
/-- **The converse for type 1**: if `∂_j G(0) ≠ 0` for some `j ∉ Δ`, then `ρ = 0`. -/
theorem logJacobianOrder_eq_zero_of_type_one {j : σ} (hj : j ∉ Δ)
    (h : constantCoeff (pderiv j (residualFactor Δ g)) ≠ 0) : logJacobianOrder Δ g = 0 :=
  (logJacobianOrder_eq_zero_iff_exists Δ g).mpr (Or.inr ⟨j, hj, h⟩)

/-- **Type 0** (Volume 7, Section 3.5 of the handbook, Proposition 3.5.1): for a clean `g` with
`ord G = 0`, `G(0) ≠ 0` and `p ∤ r_i` for some `i ∈ Δ`. Then also `ρ = 0`. -/
theorem logJacobianOrder_eq_zero_type_zero (hc : IsClean p g) (hd : ord (residualFactor Δ g) = 0) :
    logJacobianOrder Δ g = 0 ∧ constantCoeff (residualFactor Δ g) ≠ 0 ∧
      ∃ i ∈ Δ, ¬ p ∣ divisorExponent Δ g i := by
  have h0 := ord_eq_zero_iff_constantCoeff_ne_zero.mp hd
  obtain ⟨i, hi, hp⟩ := exists_not_dvd_divisorExponent_of_constantCoeff_ne_zero p hc h0
  exact ⟨logJacobianOrder_eq_zero_of_type_zero p h0 hi hp, h0, i, hi, hp⟩

omit [CharP k p] in
/-- If `ρ = 0` and `G(0) = 0`, then `∂_j G(0) ≠ 0` for some `j ∉ Δ`: each generator
`r_i G + x_i ∂_i G` has the constant term `r_i G(0) = 0`. -/
theorem exists_constantCoeff_pderiv_ne_zero_of_constantCoeff_eq_zero
    (hρ : logJacobianOrder Δ g = 0) (h0 : constantCoeff (residualFactor Δ g) = 0) :
    ∃ j ∉ Δ, constantCoeff (pderiv j (residualFactor Δ g)) ≠ 0 := by
  rcases (logJacobianOrder_eq_zero_iff_exists Δ g).mp hρ with ⟨i, -, hne⟩ | h
  · rw [h0, mul_zero] at hne
    exact absurd rfl hne
  · exact h

omit [CharP k p] in
/-- **Type 1** (Volume 7, Section 3.5 of the handbook, Proposition 3.5.1): if `ρ = 0` and
`ord G = 1`, then `∂_j G(0) ≠ 0` for some free coordinate `x_j`, `j ∉ Δ`. -/
theorem exists_constantCoeff_pderiv_ne_zero (hρ : logJacobianOrder Δ g = 0)
    (hd : ord (residualFactor Δ g) = 1) :
    ∃ j ∉ Δ, constantCoeff (pderiv j (residualFactor Δ g)) ≠ 0 :=
  exists_constantCoeff_pderiv_ne_zero_of_constantCoeff_eq_zero hρ
    (one_le_ord_iff.mp hd.ge)

omit [CharP k p] in
/-- If `ρ = 0`, then `ord G ≤ 1`. This is the dichotomy `d ≤ ρ + 1`. -/
theorem ord_residualFactor_le_one (hρ : logJacobianOrder Δ g = 0) :
    ord (residualFactor Δ g) ≤ 1 := by
  have h := ord_residualFactor_le_logJacobianOrder_add_one Δ g
  rwa [hρ, zero_add] at h

/-- **The end case** (Volume 7, Section 3.5 of the handbook, Proposition 3.5.1): for a clean `g`,
`ρ = 0` if and only if type 0 holds (`G(0) ≠ 0` and `p ∤ r_i` for some `i ∈ Δ`) or type 1 holds
(`G(0) = 0` and `∂_j G(0) ≠ 0` for some `j ∉ Δ`). -/
theorem logJacobianOrder_eq_zero_iff (hc : IsClean p g) :
    logJacobianOrder Δ g = 0 ↔
      (constantCoeff (residualFactor Δ g) ≠ 0 ∧ ∃ i ∈ Δ, ¬ p ∣ divisorExponent Δ g i) ∨
        (constantCoeff (residualFactor Δ g) = 0 ∧
          ∃ j ∉ Δ, constantCoeff (pderiv j (residualFactor Δ g)) ≠ 0) := by
  constructor
  · intro hρ
    by_cases h0 : constantCoeff (residualFactor Δ g) = 0
    · exact Or.inr ⟨h0, exists_constantCoeff_pderiv_ne_zero_of_constantCoeff_eq_zero hρ h0⟩
    · exact Or.inl ⟨h0, exists_not_dvd_divisorExponent_of_constantCoeff_ne_zero p hc h0⟩
  · rintro (⟨h0, i, hi, hp⟩ | ⟨-, j, hj, h⟩)
    · exact logJacobianOrder_eq_zero_of_type_zero p h0 hi hp
    · exact logJacobianOrder_eq_zero_of_type_one hj h

/-- **The end case with the order of `G`** (Volume 7, Section 3.5 of the handbook,
Proposition 3.5.1): for a clean `g`, `ρ = 0` if and only if `ord G = 0` and `p ∤ r_i` for some
`i ∈ Δ`, or `ord G = 1` and `∂_j G(0) ≠ 0` for some `j ∉ Δ`. -/
theorem logJacobianOrder_eq_zero_iff_ord (hc : IsClean p g) :
    logJacobianOrder Δ g = 0 ↔
      (ord (residualFactor Δ g) = 0 ∧ ∃ i ∈ Δ, ¬ p ∣ divisorExponent Δ g i) ∨
        (ord (residualFactor Δ g) = 1 ∧
          ∃ j ∉ Δ, constantCoeff (pderiv j (residualFactor Δ g)) ≠ 0) := by
  rw [logJacobianOrder_eq_zero_iff p hc, ord_eq_zero_iff_constantCoeff_ne_zero]
  constructor
  · rintro (h | ⟨h0, j, hj, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ord_eq_one_of_constantCoeff_pderiv_ne_zero h0 h, j, hj, h⟩
  · rintro (h | ⟨hd, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨one_le_ord_iff.mp hd.ge, h⟩

end Field

end Singularity
