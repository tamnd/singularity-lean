/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.FieldSimp

/-!
# The monomial valuation with negative weights

This file proves the first part of Volume 3, Example 1.6.7 of the handbook. Let `v` be the monomial valuation of `k(x, y)` with `v(x) = v(y) = -1`. On the chart `U_X` of the projective plane put `u = 1/x` and `w = y/x`. The example claims that `𝔪_v ∩ k[u, w] = (u)`.

Mathlib writes valuations multiplicatively, so `v(x) = -1` becomes `1 < v x`. The file does not construct the monomial valuation. It takes the property of the monomial valuation that it uses as a hypothesis: each nonzero homogeneous form `F` of degree `d` in `x` and `y` has value `v(x)^d`.

The proof follows the handbook. A nonzero polynomial `P` of degree `d` in `w` is `F(x, y)/x^d` with `F` homogeneous of degree `d` and `F ≠ 0`, so `v(P(w)) = 1`. An element `g` of `k[u, w]` is `g_0(w) + u g_1`. If `g_0 ≠ 0`, then `g` has value `1`. If `g_0 = 0`, then `u` divides `g` and `g` has value less than `1`.

The ring `k[u, w]` is the ring `k[X][X]` of polynomials in `u` with coefficients in `k[w]`, and `Singularity.chartEval u w` evaluates it in `K`.

## Main results

* `Singularity.valuation_chartEval_lt_one_iff`: if `v(u) < 1` and each nonzero polynomial in `w` has value `1`, then `g ∈ k[u, w]` lies in the maximal ideal of `v` if and only if `u` divides `g`.
* `Singularity.valuation_aeval_div_eq_one`: for the monomial valuation with `v(x) = v(y)`, each nonzero polynomial in `y/x` has value `1`.
* `Singularity.valuation_chartEval_inv_div_lt_one_iff`: Example 1.6.7, the claim `𝔪_v ∩ k[u, w] = (u)` for `u = 1/x` and `w = y/x`.

## Gaps

The file does not construct the monomial valuation, and it does not prove the claims on the centers on `𝔸²_k` and `ℙ²_k` or the second part of the example with an irrational weight.
-/

open Polynomial

namespace Singularity

section NegativeWeights

variable {k K Γ₀ : Type*} [Field k] [Field K] [Algebra k K] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀)

/-- The evaluation `k[w][u] → K` at `u` and `w`. A polynomial in two variables `u, w` is a
polynomial in `u` with coefficients in `k[w]`. -/
noncomputable def chartEval (u w : K) : (k[X])[X] →+* K :=
  Polynomial.eval₂RingHom (Polynomial.aeval w : k[X] →ₐ[k] K).toRingHom u

theorem chartEval_X (u w : K) : chartEval (k := k) u w X = u := by
  simp [chartEval]

theorem chartEval_C (u w : K) (P : k[X]) : chartEval u w (C P) = Polynomial.aeval w P := by
  simp [chartEval]

/-- If `v(u) ≤ 1` and each nonzero polynomial in `w` has value `1`, then each element of
`k[u, w]` has value at most `1`. -/
theorem valuation_chartEval_le_one {u w : K} (hu : v u ≤ 1)
    (hw : ∀ P : k[X], P ≠ 0 → v (Polynomial.aeval w P) = 1) (g : (k[X])[X]) :
    v (chartEval u w g) ≤ 1 := by
  rw [chartEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  refine v.map_sum_le fun n _ => ?_
  rw [v.map_mul, v.map_pow]
  refine mul_le_one' ?_ (pow_le_one' hu n)
  by_cases h : g.coeff n = 0
  · simp [h]
  · exact (hw _ h).le

/-- Volume 3, Example 1.6.7, the claim `𝔪_v ∩ k[u, w] = (u)`, in an abstract form. Let `v` be a
valuation of `K` with `v(u) < 1` such that each nonzero polynomial in `w` over `k` has value `1`.
Then an element `g` of `k[u, w]` lies in the maximal ideal of `v` if and only if `u` divides
`g`. -/
theorem valuation_chartEval_lt_one_iff {u w : K} (hu : v u < 1)
    (hw : ∀ P : k[X], P ≠ 0 → v (Polynomial.aeval w P) = 1) (g : (k[X])[X]) :
    v (chartEval u w g) < 1 ↔ g ∈ Ideal.span {(X : (k[X])[X])} := by
  rw [Ideal.mem_span_singleton]
  obtain ⟨h, hh⟩ := Polynomial.X_dvd_sub_C (p := g)
  have hg : g = C (g.coeff 0) + X * h := by rw [← hh]; ring
  constructor
  · intro hlt
    rw [Polynomial.X_dvd_iff]
    by_contra h0
    have h1 : v (chartEval u w (C (g.coeff 0))) = 1 := by rw [chartEval_C]; exact hw _ h0
    have h2 : v (chartEval u w (X * h)) < 1 := by
      rw [map_mul, chartEval_X, v.map_mul]
      exact mul_lt_one_of_lt_of_le hu (valuation_chartEval_le_one v hu.le hw h)
    have : v (chartEval u w g) = 1 := by
      rw [hg, map_add, ← h1]
      exact v.map_add_eq_of_lt_left (h1 ▸ h2)
    exact absurd hlt (by rw [this]; exact lt_irrefl 1)
  · rintro ⟨h', rfl⟩
    rw [map_mul, chartEval_X, v.map_mul]
    exact mul_lt_one_of_lt_of_le hu (valuation_chartEval_le_one v hu.le hw h')

/-- The step `v(P(y/x)) = 0` of Volume 3, Example 1.6.7. Let `v` be a valuation of `K` such that
each nonzero homogeneous form `F` of degree `d` in `x, y` has value `v(x)^d`, the property of
the monomial valuation with `v(x) = v(y)`. Then each nonzero polynomial in `y/x` has value `1`. -/
theorem valuation_aeval_div_eq_one {x y : K} (hx : x ≠ 0)
    (hF : ∀ (d : ℕ) (F : MvPolynomial (Fin 2) k), F.IsHomogeneous d → F ≠ 0 →
      v (MvPolynomial.aeval ![x, y] F) = v x ^ d)
    (P : k[X]) (hP : P ≠ 0) : v (Polynomial.aeval (y / x) P) = 1 := by
  classical
  set d := P.natDegree
  set F : MvPolynomial (Fin 2) k := ∑ i ∈ Finset.range (d + 1),
    MvPolynomial.C (P.coeff i) * MvPolynomial.X 0 ^ (d - i) * MvPolynomial.X 1 ^ i with hFdef
  have hhom : F.IsHomogeneous d := by
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i hi => ?_
    have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have := ((MvPolynomial.isHomogeneous_C (Fin 2) (P.coeff i)).mul
      ((MvPolynomial.isHomogeneous_X k (0 : Fin 2)).pow (d - i))).mul
      ((MvPolynomial.isHomogeneous_X k (1 : Fin 2)).pow i)
    simpa [Nat.sub_add_cancel hi'] using this
  have hevalP : MvPolynomial.aeval ![(1 : k[X]), Polynomial.X] F = P := by
    rw [hFdef, map_sum]
    simp only [map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one]
    conv_rhs => rw [P.as_sum_range_C_mul_X_pow]
    rfl
  have hF0 : F ≠ 0 := by
    rintro h0; apply hP; rw [← hevalP, h0, map_zero]
  have hevalK : MvPolynomial.aeval ![x, y] F = x ^ d * Polynomial.aeval (y / x) P := by
    rw [hFdef, map_sum, Polynomial.aeval_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp only [map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, div_pow, Algebra.smul_def]
    have hxi : x ^ d = x ^ (d - i) * x ^ i := by rw [← pow_add, Nat.sub_add_cancel hi']
    rw [hxi]
    field_simp
  have hv := hF d F hhom hF0
  rw [hevalK, v.map_mul, v.map_pow] at hv
  have hx0 : v x ^ d ≠ 0 := pow_ne_zero _ ((v.ne_zero_iff).mpr hx)
  exact (mul_eq_left₀ hx0).mp hv

/-- Volume 3, Example 1.6.7, the first part. Let `v` be a valuation of `K` with `v(x) > 1` (that
is, `v(x) < 0` in additive notation) such that each nonzero homogeneous form of degree `d` in
`x, y` has value `v(x)^d`. Put `u = 1/x` and `w = y/x`. Then `𝔪_v ∩ k[u, w] = (u)`: an element
`g` of `k[u, w]` lies in the maximal ideal of `v` if and only if `u` divides `g`. -/
theorem valuation_chartEval_inv_div_lt_one_iff {x y : K} (hx : x ≠ 0) (hvx : 1 < v x)
    (hF : ∀ (d : ℕ) (F : MvPolynomial (Fin 2) k), F.IsHomogeneous d → F ≠ 0 →
      v (MvPolynomial.aeval ![x, y] F) = v x ^ d)
    (g : (k[X])[X]) :
    v (chartEval x⁻¹ (y / x) g) < 1 ↔ g ∈ Ideal.span {(X : (k[X])[X])} := by
  refine valuation_chartEval_lt_one_iff v ?_ (valuation_aeval_div_eq_one v hx hF) g
  rw [v.map_inv]
  exact inv_lt_one_of_one_lt₀ hvx

end NegativeWeights

end Singularity
