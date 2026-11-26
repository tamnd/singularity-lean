/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Finsupp.Order

/-!
# The partial derivative of a polynomial in characteristic p

Let `k` be a field of characteristic `p`, and let `F` be a polynomial in the variables `U_j`. This file proves that `∂F/∂U_j ≠ 0` if and only if `F` has a monomial `c U^a` with `c ≠ 0` and `p ∤ a_j` (Volume 6, Lemma 4.3.1 of the handbook).

The handbook takes the variables `U_1, ..., U_n`. The statement here is for each type `σ` of variables. A monomial `c U^a` of `F` with `c ≠ 0` is an exponent `a` in `F.support`.

The proof uses the formula `MvPolynomial.coeff_pderiv` of Mathlib: the coefficient of `U^b` in `∂F/∂U_j` is `(b_j + 1)` times the coefficient of `U^(b + e_j)` in `F`. This is the argument of the handbook: no two terms cancel.

## Main results

* `Singularity.pderiv_ne_zero_iff`: `∂F/∂U_j ≠ 0` if and only if some exponent `a` of `F` has `p ∤ a_j`.
-/

open MvPolynomial

namespace Singularity

variable {σ k : Type*} [Field k] (p : ℕ) [CharP k p]

/-- Volume 6, Lemma 4.3.1 of the handbook: let `k` be a field of characteristic `p` and let `F` be a polynomial over `k`. Then `∂F/∂U_j ≠ 0` if and only if `F` has a monomial `c U^a` with `c ≠ 0` and `p ∤ a_j`. -/
theorem pderiv_ne_zero_iff (F : MvPolynomial σ k) (j : σ) :
    pderiv j F ≠ 0 ↔ ∃ a ∈ F.support, ¬ (p ∣ a j) := by
  classical
  constructor
  · intro h
    obtain ⟨b, hb⟩ := ne_zero_iff.mp h
    rw [coeff_pderiv] at hb
    refine ⟨b + Finsupp.single j 1, mem_support_iff.mpr (left_ne_zero_of_mul hb), ?_⟩
    have hc := right_ne_zero_of_mul hb
    rw [← CharP.cast_eq_zero_iff k p]
    simpa using hc
  · rintro ⟨a, ha, hpa⟩
    have haj : a j ≠ 0 := by
      intro h
      apply hpa
      rw [h]
      exact dvd_zero p
    obtain ⟨b, hb⟩ : ∃ b : σ →₀ ℕ, b = a - Finsupp.single j 1 := ⟨_, rfl⟩
    have hsum : b + Finsupp.single j 1 = a := by
      rw [hb]
      exact Finsupp.sub_add_single_one_cancel haj
    have hbj : b j + 1 = a j := by
      rw [hb, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    refine ne_zero_iff.mpr ⟨b, ?_⟩
    rw [coeff_pderiv, hsum]
    refine mul_ne_zero (mem_support_iff.mp ha) ?_
    have h1 : ((b j + 1 : ℕ) : k) ≠ 0 := by
      rw [hbj, Ne, CharP.cast_eq_zero_iff k p]
      exact hpa
    exact_mod_cast h1

end Singularity
