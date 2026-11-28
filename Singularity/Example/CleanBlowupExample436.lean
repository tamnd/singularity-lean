/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.Residual
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The polynomial computations of Example 4.3.6

This file proves Volume VI, Example 4.3.6 of the handbook, in part. The variables
`x_1, x_2, x_3, x_4` are `X 0, X 1, X 2, X 3` of `k[X 0, X 1, X 2, X 3]` over a field `k`, and
the divisor `E = div(x_1 x_2 x_3 x_4)` is the finset `Finset.univ`. The polynomial is
`F = x_1^2 x_2^4 - x_1^5 x_2 + x_1^2 x_2 x_3^4 + x_1^2 x_2 x_4^4`.

What the file proves at the point `x`:

* `F` is clean for `3`, `ord F = 6`, the residual factor of `F` for `E` is
  `G = x_2^3 - x_1^3 + x_3^4 + x_4^4` (so `r = (2, 1, 0, 0)`), and `ε(x) = ord G = 3`.
* In characteristic `3`, `∂F/∂x_3 = x_1^2 x_2 x_3^3` and `∂F/∂x_4 = x_1^2 x_2 x_4^3`, and each
  common zero of the four partial derivatives lies in `V(x_1) ∪ V(x_2) ∪ V(x_3, x_4)`, so on `E`.

What the file proves at the point `x'` over `t = (1, 0, 0)` of the `x_1`-chart, in
characteristic `3`:

* The chart sends `F` to `x_1^3 ((x_1 x_2)^3 + F')` with
  `F' = x_1^3 x_2^4 + x_1^4 x_2 x_3^4 + x_1^4 x_2 x_4^4 + x_1^4 x_3^4 + x_1^4 x_4^4`, and it sends
  `Z^3 + F` to `x_1^3` times the shift `Z' ↦ Z' + x_1 x_2` of `Z'^3 + F'`.
* `F'` is clean for `3`, `ord F' = 7`, `E' = div(x_1 x_3 x_4)`, the residual factor of `F'` for
  `E'` is `x_1^{-3} F'` (so `r' = (3, 0, 0)`), and `ε(x') = 4`.

What is not proved: the invariants `ω(x) = 3`, `ω(x') = 3` and `ι` (the module
`CossartPiltantOmega` is not on the build server used to check this file, so `cpOmega` is not
used), the appeal to Lemma 2.3.3 and Lemma 4.3.1, condition (E) as a property of the triple
`(S, h, E)`, the blowups as schemes, and the count of the 40 points of the exceptional divisor
over `𝔽_3`. The series ring is replaced by the polynomial ring.
-/

open MvPolynomial Finsupp

namespace Singularity.Examples

section Example436

variable {k : Type*} [Field k]

private theorem tie436_isClean_add {q : ℕ} {f g : MvPolynomial (Fin 4) k} (hf : IsClean q f)
    (hg : IsClean q g) : IsClean q (f + g) := by
  classical
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  exacts [hf d h, hg d h]

private theorem tie436_isClean_monomial {q : ℕ} {a : Fin 4 →₀ ℕ} (c : k)
    (ha : ∃ i, ¬ q ∣ a i) : IsClean q (monomial a c) := by
  classical
  intro d hd h
  obtain ⟨i, hi⟩ := ha
  rw [Finset.mem_singleton.mp (support_monomial_subset hd)] at h
  exact hi (h i)

private theorem tie436_isClean_neg {q : ℕ} {f : MvPolynomial (Fin 4) k} (hf : IsClean q f) :
    IsClean q (-f) := by
  intro d hd
  rw [MvPolynomial.support_neg] at hd
  exact hf d hd

private theorem tie436_three [CharP k 3] : (3 : MvPolynomial (Fin 4) k) = 0 := by
  have h : (3 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 3
  rw [← map_ofNat (C : k →+* MvPolynomial (Fin 4) k) 3]
  simp [h]

/-! ### The point `x` -/

/-- `F = x_1^2 x_2^4 - x_1^5 x_2 + x_1^2 x_2 x_3^4 + x_1^2 x_2 x_4^4` is clean for `3`: each
monomial has an exponent prime to `3`. Volume 6, Example 4.3.6 of the handbook. -/
theorem example_4_3_6_isClean :
    IsClean 3 (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 +
      X 0 ^ 2 * X 1 * X 3 ^ 4 : MvPolynomial (Fin 4) k) := by
  rw [show (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 +
      X 0 ^ 2 * X 1 * X 3 ^ 4 : MvPolynomial (Fin 4) k) =
      monomial (single 0 2 + single 1 4) 1 + -monomial (single 0 5 + single 1 1) 1 +
        monomial (single 0 2 + single 1 1 + single 2 4) 1 +
        monomial (single 0 2 + single 1 1 + single 3 4) 1 by
    simp [X, monomial_pow, monomial_mul_monomial, sub_eq_add_neg]]
  refine tie436_isClean_add (tie436_isClean_add (tie436_isClean_add ?_
    (tie436_isClean_neg ?_)) ?_) ?_
  · exact tie436_isClean_monomial _ ⟨0, by simp⟩
  · exact tie436_isClean_monomial _ ⟨0, by simp⟩
  · exact tie436_isClean_monomial _ ⟨0, by simp⟩
  · exact tie436_isClean_monomial _ ⟨0, by simp⟩

private theorem tie436_G_mem1 : (single 1 3 : Fin 4 →₀ ℕ) ∈
    (X 1 ^ 3 - X 0 ^ 3 + X 2 ^ 4 + X 3 ^ 4 : MvPolynomial (Fin 4) k).support :=
  MvPolynomial.mem_support_iff.mpr (by
    simp [X, monomial_pow, coeff_monomial, Finsupp.ext_iff, Fin.forall_fin_succ,
      Finsupp.single_apply])

private theorem tie436_G_mem0 : (single 0 3 : Fin 4 →₀ ℕ) ∈
    (X 1 ^ 3 - X 0 ^ 3 + X 2 ^ 4 + X 3 ^ 4 : MvPolynomial (Fin 4) k).support :=
  MvPolynomial.mem_support_iff.mpr (by
    simp [X, monomial_pow, coeff_monomial, Finsupp.ext_iff, Fin.forall_fin_succ,
      Finsupp.single_apply])

private theorem tie436_G_ord :
    ord (X 1 ^ 3 - X 0 ^ 3 + X 2 ^ 4 + X 3 ^ 4 : MvPolynomial (Fin 4) k) = ((3 : ℕ) : ℕ∞) := by
  refine le_antisymm ?_ ?_
  · have h := ord_le (MvPolynomial.mem_support_iff.mp (tie436_G_mem1 (k := k)))
    rw [degree_single] at h
    exact h
  · rw [sub_eq_add_neg]
    refine le_ord_add (le_ord_add (le_ord_add ?_ ?_) ?_) ?_
    · rw [ord_X_pow]
    · rw [ord_neg, ord_X_pow]
    · rw [ord_X_pow]; exact_mod_cast (by norm_num : 3 ≤ 4)
    · rw [ord_X_pow]; exact_mod_cast (by norm_num : 3 ≤ 4)

/-- For `E = div(x_1 x_2 x_3 x_4)`, `F = x_1^2 x_2 G` with `G = x_2^3 - x_1^3 + x_3^4 + x_4^4`,
so `r = (2, 1, 0, 0)`. Volume 6, Example 4.3.6 of the handbook. -/
theorem example_4_3_6_residualFactor :
    residualFactor Finset.univ
      (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 + X 0 ^ 2 * X 1 * X 3 ^ 4 :
        MvPolynomial (Fin 4) k) = X 1 ^ 3 - X 0 ^ 3 + X 2 ^ 4 + X 3 ^ 4 := by
  rw [show (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 +
      X 0 ^ 2 * X 1 * X 3 ^ 4 : MvPolynomial (Fin 4) k) = monomial (single 0 2 + single 1 1) 1 *
        (X 1 ^ 3 - X 0 ^ 3 + X 2 ^ 4 + X 3 ^ 4) by
    rw [show (monomial (single 0 2 + single 1 1) 1 : MvPolynomial (Fin 4) k) = X 0 ^ 2 * X 1 by
      simp [X, monomial_pow, monomial_mul_monomial]]
    ring]
  refine residualFactor_monomial_mul (fun i hi => absurd (Finset.mem_univ i) hi) ?_
  intro i _
  fin_cases i
  · exact ⟨_, tie436_G_mem1, by simp⟩
  · exact ⟨_, tie436_G_mem0, by simp⟩
  · exact ⟨_, tie436_G_mem1, by simp⟩
  · exact ⟨_, tie436_G_mem1, by simp⟩

/-- `ε(x) = 3`. Volume 6, Example 4.3.6 of the handbook. -/
theorem example_4_3_6_epsilon :
    ord (residualFactor Finset.univ
      (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 + X 0 ^ 2 * X 1 * X 3 ^ 4 :
        MvPolynomial (Fin 4) k)) = 3 := by
  rw [example_4_3_6_residualFactor]
  exact tie436_G_ord

/-- `ord F = 6`, so `δ(x) = 2`. Volume 6, Example 4.3.6 of the handbook. -/
theorem example_4_3_6_ord :
    ord (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 +
      X 0 ^ 2 * X 1 * X 3 ^ 4 : MvPolynomial (Fin 4) k) = 6 := by
  rw [show (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 +
      X 0 ^ 2 * X 1 * X 3 ^ 4 : MvPolynomial (Fin 4) k) =
      X 0 ^ 2 * X 1 * (X 1 ^ 3 - X 0 ^ 3 + X 2 ^ 4 + X 3 ^ 4) by ring,
    ord_mul, ord_mul, tie436_G_ord, ord_X_pow, ord_X]
  norm_num

/-- Modulo `3`, `∂F/∂x_3 = x_1^2 x_2 x_3^3`. Volume 6, Example 4.3.6 of the handbook. -/
theorem example_4_3_6_pderiv_2 [CharP k 3] :
    pderiv 2 (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 +
      X 0 ^ 2 * X 1 * X 3 ^ 4 : MvPolynomial (Fin 4) k) = X 0 ^ 2 * X 1 * X 2 ^ 3 := by
  simp [Derivation.leibniz, Derivation.leibniz_pow, pderiv_X]
  linear_combination tie436_three (k := k)

/-- Modulo `3`, `∂F/∂x_4 = x_1^2 x_2 x_4^3`. Volume 6, Example 4.3.6 of the handbook. -/
theorem example_4_3_6_pderiv_3 [CharP k 3] :
    pderiv 3 (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 +
      X 0 ^ 2 * X 1 * X 3 ^ 4 : MvPolynomial (Fin 4) k) = X 0 ^ 2 * X 1 * X 3 ^ 3 := by
  simp [Derivation.leibniz, Derivation.leibniz_pow, pderiv_X]
  linear_combination tie436_three (k := k)

/-- In characteristic `3`, a common zero of the partial derivatives of `F` lies in
`V(x_1) ∪ V(x_2) ∪ V(x_3, x_4)`, so on `E = V(x_1 x_2 x_3 x_4)`. This is the inclusion of the zero
sets that condition (E) uses. Volume 6, Example 4.3.6 of the handbook. -/
theorem example_4_3_6_zero_pderiv [CharP k 3] (v : Fin 4 → k)
    (hv : ∀ i, eval v (pderiv i (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 +
      X 0 ^ 2 * X 1 * X 3 ^ 4 : MvPolynomial (Fin 4) k)) = 0) :
    (v 0 = 0 ∨ v 1 = 0 ∨ (v 2 = 0 ∧ v 3 = 0)) ∧ v 0 * v 1 * v 2 * v 3 = 0 := by
  have h2 := hv 2
  have h3 := hv 3
  rw [example_4_3_6_pderiv_2] at h2
  rw [example_4_3_6_pderiv_3] at h3
  simp only [map_mul, map_pow, eval_X, mul_eq_zero, pow_eq_zero_iff, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true] at h2 h3
  have h : v 0 = 0 ∨ v 1 = 0 ∨ (v 2 = 0 ∧ v 3 = 0) := by tauto
  refine ⟨h, ?_⟩
  rcases h with h | h | ⟨h, -⟩ <;> simp [h]

/-! ### The point `x'` over `t = (1, 0, 0)` of the `x_1`-chart -/

/-- In characteristic `3`, the `x_1`-chart at `t = (1, 0, 0)` sends `F` to
`x_1^3 (x_1^3 x_2^4 + x_1^3 x_2^3 + x_1^4 x_2 x_3^4 + x_1^4 x_2 x_4^4 + x_1^4 x_3^4 + x_1^4 x_4^4)`.
Volume 6, Example 4.3.6 of the handbook. -/
theorem example_4_3_6_chart [CharP k 3] {t : Fin 4 → k} (ht1 : t 1 = 1) (ht2 : t 2 = 0)
    (ht3 : t 3 = 0) :
    pointChart 0 t (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 +
      X 0 ^ 2 * X 1 * X 3 ^ 4 : MvPolynomial (Fin 4) k) =
      X 0 ^ 3 * (X 0 ^ 3 * X 1 ^ 4 + X 0 ^ 3 * X 1 ^ 3 + X 0 ^ 4 * X 1 * X 2 ^ 4 +
        X 0 ^ 4 * X 1 * X 3 ^ 4 + X 0 ^ 4 * X 2 ^ 4 + X 0 ^ 4 * X 3 ^ 4) := by
  have h1 : pointChart 0 t (X 1 : MvPolynomial (Fin 4) k) = X 0 * (X 1 + 1) := by
    rw [pointChart_X_of_ne t (by decide : (1 : Fin 4) ≠ 0), ht1, C_1]
  have h2 : pointChart 0 t (X 2 : MvPolynomial (Fin 4) k) = X 0 * X 2 := by
    rw [pointChart_X_of_ne t (by decide : (2 : Fin 4) ≠ 0), ht2, C_0, add_zero]
  have h3 : pointChart 0 t (X 3 : MvPolynomial (Fin 4) k) = X 0 * X 3 := by
    rw [pointChart_X_of_ne t (by decide : (3 : Fin 4) ≠ 0), ht3, C_0, add_zero]
  simp only [map_add, map_sub, map_mul, map_pow, pointChart_X_self, h1, h2, h3]
  linear_combination (X 0 ^ 6 * (X 1 ^ 3 + 2 * X 1 ^ 2 + X 1)) * tie436_three (k := k)

/-- In characteristic `3`, the `x_1`-chart at `t = (1, 0, 0)` sends `F` to
`x_1^3 ((x_1 x_2)^3 + F')` with
`F' = x_1^3 x_2^4 + x_1^4 x_2 x_3^4 + x_1^4 x_2 x_4^4 + x_1^4 x_3^4 + x_1^4 x_4^4`. Volume 6,
Example 4.3.6 of the handbook. -/
theorem example_4_3_6_chart_eq [CharP k 3] {t : Fin 4 → k} (ht1 : t 1 = 1) (ht2 : t 2 = 0)
    (ht3 : t 3 = 0) :
    pointChart 0 t (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 +
      X 0 ^ 2 * X 1 * X 3 ^ 4 : MvPolynomial (Fin 4) k) =
      X 0 ^ 3 * ((X 0 * X 1) ^ 3 + (X 0 ^ 3 * X 1 ^ 4 + X 0 ^ 4 * X 1 * X 2 ^ 4 +
        X 0 ^ 4 * X 1 * X 3 ^ 4 + X 0 ^ 4 * X 2 ^ 4 + X 0 ^ 4 * X 3 ^ 4)) := by
  rw [example_4_3_6_chart ht1 ht2 ht3]
  ring

/-- In characteristic `3`, the `x_1`-chart at `t = (1, 0, 0)` sends `Z^3 + F` to `x_1^3` times
the image of `Z'^3 + F'` under the translation `Z' ↦ Z' + x_1 x_2`. So the translation removes the
cube `x_1^3 x_2^3`, and `Z'^3 + F'` is the strict transform. Volume 6, Example 4.3.6 of the
handbook. -/
theorem example_4_3_6_strictTransform [CharP k 3] {t : Fin 4 → k} (ht1 : t 1 = 1)
    (ht2 : t 2 = 0) (ht3 : t 3 = 0) :
    pointChartZ 0 t (purelyInseparable 3
      (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 +
        X 0 ^ 2 * X 1 * X 3 ^ 4 : MvPolynomial (Fin 4) k)) =
      X (some 0) ^ 3 * zShift (X 0 * X 1) (purelyInseparable 3
        (X 0 ^ 3 * X 1 ^ 4 + X 0 ^ 4 * X 1 * X 2 ^ 4 + X 0 ^ 4 * X 1 * X 3 ^ 4 +
          X 0 ^ 4 * X 2 ^ 4 + X 0 ^ 4 * X 3 ^ 4)) := by
  rw [pointChartZ_purelyInseparable (example_4_3_6_chart_eq ht1 ht2 ht3)]
  have : ExpChar k 3 := ExpChar.prime Nat.prime_three
  have h := zShift_purelyInseparable 3 1 (X 0 * X 1 : MvPolynomial (Fin 4) k)
    (X 0 ^ 3 * X 1 ^ 4 + X 0 ^ 4 * X 1 * X 2 ^ 4 + X 0 ^ 4 * X 1 * X 3 ^ 4 +
      X 0 ^ 4 * X 2 ^ 4 + X 0 ^ 4 * X 3 ^ 4)
  rw [pow_one] at h
  rw [h, add_comm ((X 0 * X 1) ^ 3)]

/-- The new divisor at `t = (1, 0, 0)` of the `x_1`-chart is `E' = div(x_1 x_3 x_4)`. Volume 6,
Example 4.3.6 of the handbook. -/
theorem example_4_3_6_blowupDivisor [DecidableEq k] {t : Fin 4 → k} (ht1 : t 1 = 1)
    (ht2 : t 2 = 0) (ht3 : t 3 = 0) : blowupDivisor Finset.univ 0 t = {0, 2, 3} := by
  ext i
  fin_cases i <;> simp [blowupDivisor, ht1, ht2, ht3]

/-- `F'` is clean for `3`. Volume 6, Example 4.3.6 of the handbook. -/
theorem example_4_3_6_isClean' :
    IsClean 3 (X 0 ^ 3 * X 1 ^ 4 + X 0 ^ 4 * X 1 * X 2 ^ 4 + X 0 ^ 4 * X 1 * X 3 ^ 4 +
      X 0 ^ 4 * X 2 ^ 4 + X 0 ^ 4 * X 3 ^ 4 : MvPolynomial (Fin 4) k) := by
  rw [show (X 0 ^ 3 * X 1 ^ 4 + X 0 ^ 4 * X 1 * X 2 ^ 4 + X 0 ^ 4 * X 1 * X 3 ^ 4 +
      X 0 ^ 4 * X 2 ^ 4 + X 0 ^ 4 * X 3 ^ 4 : MvPolynomial (Fin 4) k) =
      monomial (single 0 3 + single 1 4) 1 + monomial (single 0 4 + single 1 1 + single 2 4) 1 +
        monomial (single 0 4 + single 1 1 + single 3 4) 1 +
        monomial (single 0 4 + single 2 4) 1 + monomial (single 0 4 + single 3 4) 1 by
    simp [X, monomial_pow, monomial_mul_monomial]]
  refine tie436_isClean_add (tie436_isClean_add (tie436_isClean_add
    (tie436_isClean_add ?_ ?_) ?_) ?_) ?_
  · exact tie436_isClean_monomial _ ⟨1, by simp⟩
  all_goals exact tie436_isClean_monomial _ ⟨0, by simp⟩

private theorem tie436'_G_mem : (single 1 4 : Fin 4 →₀ ℕ) ∈
    (X 1 ^ 4 + X 0 * X 1 * X 2 ^ 4 + X 0 * X 1 * X 3 ^ 4 + X 0 * X 2 ^ 4 + X 0 * X 3 ^ 4 :
      MvPolynomial (Fin 4) k).support :=
  MvPolynomial.mem_support_iff.mpr (by
    simp [X, monomial_pow, monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff,
      Fin.forall_fin_succ, Finsupp.single_apply])

private theorem tie436'_G_ord :
    ord (X 1 ^ 4 + X 0 * X 1 * X 2 ^ 4 + X 0 * X 1 * X 3 ^ 4 + X 0 * X 2 ^ 4 + X 0 * X 3 ^ 4 :
      MvPolynomial (Fin 4) k) = ((4 : ℕ) : ℕ∞) := by
  rw [add_assoc, add_assoc, add_assoc]
  have hB : ((5 : ℕ) : ℕ∞) ≤ ord (X 0 * X 1 * X 2 ^ 4 + (X 0 * X 1 * X 3 ^ 4 +
      (X 0 * X 2 ^ 4 + X 0 * X 3 ^ 4)) : MvPolynomial (Fin 4) k) := by
    refine le_ord_add ?_ (le_ord_add ?_ (le_ord_add ?_ ?_)) <;>
      (simp only [ord_mul, ord_X_pow, ord_X]; norm_num)
  have h : ord (X 1 ^ 4 : MvPolynomial (Fin 4) k) < ord (X 0 * X 1 * X 2 ^ 4 +
      (X 0 * X 1 * X 3 ^ 4 + (X 0 * X 2 ^ 4 + X 0 * X 3 ^ 4)) : MvPolynomial (Fin 4) k) := by
    rw [ord_X_pow]
    exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : 4 < 5)) hB
  rw [ord_add_of_lt h, ord_X_pow]

/-- At `x'`, for `E' = div(x_1 x_3 x_4)`, `F' = x_1^3 G'` with
`G' = x_2^4 + x_1 x_2 x_3^4 + x_1 x_2 x_4^4 + x_1 x_3^4 + x_1 x_4^4`, so `r' = (3, 0, 0)`.
Volume 6, Example 4.3.6 of the handbook. -/
theorem example_4_3_6_residualFactor' :
    residualFactor {0, 2, 3}
      (X 0 ^ 3 * X 1 ^ 4 + X 0 ^ 4 * X 1 * X 2 ^ 4 + X 0 ^ 4 * X 1 * X 3 ^ 4 +
        X 0 ^ 4 * X 2 ^ 4 + X 0 ^ 4 * X 3 ^ 4 : MvPolynomial (Fin 4) k) =
      X 1 ^ 4 + X 0 * X 1 * X 2 ^ 4 + X 0 * X 1 * X 3 ^ 4 + X 0 * X 2 ^ 4 + X 0 * X 3 ^ 4 := by
  rw [show (X 0 ^ 3 * X 1 ^ 4 + X 0 ^ 4 * X 1 * X 2 ^ 4 + X 0 ^ 4 * X 1 * X 3 ^ 4 +
      X 0 ^ 4 * X 2 ^ 4 + X 0 ^ 4 * X 3 ^ 4 : MvPolynomial (Fin 4) k) = monomial (single 0 3) 1 *
        (X 1 ^ 4 + X 0 * X 1 * X 2 ^ 4 + X 0 * X 1 * X 3 ^ 4 + X 0 * X 2 ^ 4 + X 0 * X 3 ^ 4) by
    rw [← X_pow_eq_monomial]
    ring]
  refine residualFactor_monomial_mul ?_ ?_
  · intro i hi
    fin_cases i <;> simp at hi ⊢
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;> exact ⟨_, tie436'_G_mem, by simp⟩

/-- `ε(x') = 7 - 3 = 4 = ε(x) + 1`. Volume 6, Example 4.3.6 of the handbook. -/
theorem example_4_3_6_epsilon' :
    ord (residualFactor {0, 2, 3}
      (X 0 ^ 3 * X 1 ^ 4 + X 0 ^ 4 * X 1 * X 2 ^ 4 + X 0 ^ 4 * X 1 * X 3 ^ 4 +
        X 0 ^ 4 * X 2 ^ 4 + X 0 ^ 4 * X 3 ^ 4 : MvPolynomial (Fin 4) k)) = 4 := by
  rw [example_4_3_6_residualFactor']
  exact tie436'_G_ord

/-- `ord F' = 7`. Volume 6, Example 4.3.6 of the handbook. -/
theorem example_4_3_6_ord' :
    ord (X 0 ^ 3 * X 1 ^ 4 + X 0 ^ 4 * X 1 * X 2 ^ 4 + X 0 ^ 4 * X 1 * X 3 ^ 4 +
      X 0 ^ 4 * X 2 ^ 4 + X 0 ^ 4 * X 3 ^ 4 : MvPolynomial (Fin 4) k) = 7 := by
  rw [show (X 0 ^ 3 * X 1 ^ 4 + X 0 ^ 4 * X 1 * X 2 ^ 4 + X 0 ^ 4 * X 1 * X 3 ^ 4 +
      X 0 ^ 4 * X 2 ^ 4 + X 0 ^ 4 * X 3 ^ 4 : MvPolynomial (Fin 4) k) = X 0 ^ 3 *
        (X 1 ^ 4 + X 0 * X 1 * X 2 ^ 4 + X 0 * X 1 * X 3 ^ 4 + X 0 * X 2 ^ 4 + X 0 * X 3 ^ 4) by
      ring,
    ord_mul, tie436'_G_ord, ord_X_pow]
  norm_num

end Example436

end Singularity.Examples
