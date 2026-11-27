/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.Residual
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The polynomial computations of Examples 4.3.3 and 4.3.5

This file proves Volume VI, Example 4.3.3 and Example 4.3.5 of the handbook, in part. The variables
`x_1, x_2, x_3, x_4` are `X 0, X 1, X 2, X 3` of `k[X 0, X 1, X 2, X 3]` over a field `k`, and
the divisor `E = div(x_1 x_2 x_3 x_4)` is the finset `Finset.univ`. The polynomial is
`F = x_1 x_2^2 x_3 + x_1^2 x_3^3 + x_1^2 x_3 x_4^2`.

What the file proves for Example 4.3.3:

* `F` is clean for `2`, `ord F = 4`, the residual factor of `F` for `E` is
  `G = x_2^2 + x_1 x_3^2 + x_1 x_4^2` (so `r = (1, 0, 1, 0)`), and `ε(x) = ord G = 2`.
* In characteristic `2`, `∂F/∂x_1 = x_2^2 x_3`, and each common zero of the four partial
  derivatives lies on `E` (the zero set inclusion behind condition (E)).
* In characteristic `2`, the `x_4`-chart at `t = (1, 0, 1)` sends `F` to
  `x_4^2 (x_2^2 x_4^2 (x_1 + 1)(x_3 + 1) + x_4^3 (x_1^2 + 1)(x_3^3 + x_3^2))`, which is
  `x_4^2 ((x_2 x_4)^2 + F')` with the clean part `F'` of the handbook. The chart sends `Z^2 + F` to
  `x_4^2` times the shift `Z' ↦ Z' + x_2 x_4` of `Z'^2 + F'`.
* `F'` is clean for `2`, `ord F' = 5`, `E' = div(x_2 x_4)`, the residual factor of `F'` for `E'`
  is `x_4^{-2} F'`, `ε(x') = 3`, and the initial form of `F'` is
  `x_1 x_2^2 x_4^2 + x_2^2 x_3 x_4^2 + x_3^2 x_4^3`.

What the file proves for Example 4.3.5: for each of the four charts at the origin,
`π(F) = x_j^2 F'_j` with the polynomial `F'_j` of the table, the order of `F'_j`, its residual
factor for `E' = E`, and `ε(x')`. The new divisor at the origin of each chart is `E`.

What is not proved: the invariants `ω` and `ι` (the module `CossartPiltantOmega` is not used
here), the appeal to Lemma 2.3.3 and Lemma 4.3.1, condition (E) as a property of the triple
`(S, h, E)`, and the blowups as schemes. The series ring is replaced by the polynomial ring.
-/

open MvPolynomial Finsupp

namespace Singularity.Examples

/-! ### General facts -/

section General

variable {k : Type*} [Field k]

private theorem tie4_isClean_add {q : ℕ} {f g : MvPolynomial (Fin 4) k} (hf : IsClean q f)
    (hg : IsClean q g) : IsClean q (f + g) := by
  classical
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  exacts [hf d h, hg d h]

private theorem tie4_isClean_monomial {q : ℕ} {a : Fin 4 →₀ ℕ} (c : k)
    (ha : ∃ i, ¬ q ∣ a i) : IsClean q (monomial a c) := by
  classical
  intro d hd h
  obtain ⟨i, hi⟩ := ha
  rw [Finset.mem_singleton.mp (support_monomial_subset hd)] at h
  exact hi (h i)

private theorem tie4_ord_add {A B : MvPolynomial (Fin 4) k} {n m : ℕ} (hA : ord A = n)
    (hB : (m : ℕ∞) ≤ ord B) (hnm : n < m) : ord (A + B) = n := by
  have h : ord A < ord B := by
    rw [hA]
    exact lt_of_lt_of_le (by exact_mod_cast hnm) hB
  rw [ord_add_of_lt h, hA]

private theorem tie4_hc_monomial (d : Fin 4 →₀ ℕ) (n : ℕ) :
    homogeneousComponent n (monomial d (1 : k)) = if n = d.degree then monomial d 1 else 0 :=
  homogeneousComponent_of_mem (isHomogeneous_monomial (1 : k) rfl)

private theorem tie4_two [CharP k 2] : (2 : MvPolynomial (Fin 4) k) = 0 := by
  have h : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
  rw [← map_ofNat (C : k →+* MvPolynomial (Fin 4) k) 2]
  simp [h]

/-- The `x_j`-chart at the origin sends `x_i` to `x_j x_i` for `i ≠ j`. -/
private theorem tie4_origin {j i : Fin 4} (h : i ≠ j) :
    pointChart j (0 : Fin 4 → k) (X i) = X j * X i := by
  rw [pointChart_X_of_ne _ h, Pi.zero_apply, C_0, add_zero]

/-- At the origin of each chart of the blowup the new divisor is `E`, since all `t_i` are `0`.
Volume 6, Example 4.3.5 of the handbook. -/
theorem example_4_3_5_blowupDivisor [DecidableEq k] (j : Fin 4) :
    blowupDivisor Finset.univ j (0 : Fin 4 → k) = Finset.univ := by
  ext i
  by_cases h : i = j <;> simp [blowupDivisor, h]

end General

/-! ### Example 4.3.3 at the point `x` -/

section Example433

variable {k : Type*} [Field k]

/-- `F = x_1 x_2^2 x_3 + x_1^2 x_3^3 + x_1^2 x_3 x_4^2` is clean for `2`: each monomial has an odd
exponent. Volume 6, Example 4.3.3 of the handbook. -/
theorem example_4_3_3_isClean :
    IsClean 2 (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 2 :
      MvPolynomial (Fin 4) k) := by
  rw [show (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 2 :
      MvPolynomial (Fin 4) k) = monomial (single 0 1 + single 1 2 + single 2 1) 1 +
        monomial (single 0 2 + single 2 3) 1 + monomial (single 0 2 + single 2 1 + single 3 2) 1
      by simp [X, monomial_pow, monomial_mul_monomial]]
  exact tie4_isClean_add (tie4_isClean_add (tie4_isClean_monomial _ ⟨0, by simp⟩)
    (tie4_isClean_monomial _ ⟨2, by simp⟩)) (tie4_isClean_monomial _ ⟨2, by simp⟩)

private theorem tie_433_G_ord :
    ord (X 1 ^ 2 + X 0 * X 2 ^ 2 + X 0 * X 3 ^ 2 : MvPolynomial (Fin 4) k) =
      ((2 : ℕ) : ℕ∞) := by
  rw [add_assoc]
  exact tie4_ord_add (m := 3) (ord_X_pow 1 2)
    (le_ord_add (by simp only [ord_mul, ord_X_pow, ord_X]; norm_num)
      (by simp only [ord_mul, ord_X_pow, ord_X]; norm_num)) (by norm_num)

private theorem tie_433_ord :
    ord (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 2 :
      MvPolynomial (Fin 4) k) = ((4 : ℕ) : ℕ∞) := by
  rw [show (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 2 :
      MvPolynomial (Fin 4) k) = X 0 * X 2 * (X 1 ^ 2 + X 0 * X 2 ^ 2 + X 0 * X 3 ^ 2) by ring,
    ord_mul, ord_mul, tie_433_G_ord, ord_X, ord_X]
  norm_num

/-- `ord F = 4`, so `δ(x) = 2`. Volume 6, Example 4.3.3 of the handbook. -/
theorem example_4_3_3_ord :
    ord (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 2 :
      MvPolynomial (Fin 4) k) = 4 :=
  tie_433_ord

/-- For `E = div(x_1 x_2 x_3 x_4)`, `F = x_1 x_3 G` with `G = x_2^2 + x_1 x_3^2 + x_1 x_4^2`, so
`r = (1, 0, 1, 0)`. Volume 6, Example 4.3.3 of the handbook. -/
theorem example_4_3_3_residualFactor :
    residualFactor Finset.univ
      (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 2 :
        MvPolynomial (Fin 4) k) = X 1 ^ 2 + X 0 * X 2 ^ 2 + X 0 * X 3 ^ 2 := by
  rw [show (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 2 :
      MvPolynomial (Fin 4) k) = monomial (single 0 1 + single 2 1) 1 *
        (X 1 ^ 2 + X 0 * X 2 ^ 2 + X 0 * X 3 ^ 2) by
    rw [show (monomial (single 0 1 + single 2 1) 1 : MvPolynomial (Fin 4) k) = X 0 * X 2 by
      simp [X, monomial_mul_monomial]]
    ring]
  refine residualFactor_monomial_mul (fun i hi => absurd (Finset.mem_univ i) hi) ?_
  intro i _
  fin_cases i
  · exact ⟨single 1 2, MvPolynomial.mem_support_iff.mpr (by
      simp [X, monomial_pow, monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff,
        Fin.forall_fin_succ, Finsupp.single_apply]), by simp⟩
  · exact ⟨single 0 1 + single 2 2, MvPolynomial.mem_support_iff.mpr (by
      simp [X, monomial_pow, monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff,
        Fin.forall_fin_succ, Finsupp.single_apply]), by simp⟩
  all_goals exact ⟨single 1 2, MvPolynomial.mem_support_iff.mpr (by
      simp [X, monomial_pow, monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff,
        Fin.forall_fin_succ, Finsupp.single_apply]), by simp⟩

/-- `ε(x) = 2`. Volume 6, Example 4.3.3 of the handbook. -/
theorem example_4_3_3_epsilon :
    ord (residualFactor Finset.univ
      (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 2 :
        MvPolynomial (Fin 4) k)) = 2 := by
  rw [example_4_3_3_residualFactor]
  exact tie_433_G_ord

/-- Modulo `2`, `∂F/∂x_1 = x_2^2 x_3`. Volume 6, Example 4.3.3 of the handbook. -/
theorem example_4_3_3_pderiv [CharP k 2] :
    pderiv 0 (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 2 :
      MvPolynomial (Fin 4) k) = X 1 ^ 2 * X 2 := by
  simp [Derivation.leibniz, Derivation.leibniz_pow, pderiv_X]
  linear_combination (X 0 * X 2 ^ 3 + X 0 * X 2 * X 3 ^ 2) * tie4_two (k := k)

/-- A common zero of the partial derivatives of `F` lies on `V(x_2 x_3)`, so on
`E = V(x_1 x_2 x_3 x_4)`. This is the inclusion of the zero sets that condition (E) uses.
Volume 6, Example 4.3.3 of the handbook. -/
theorem example_4_3_3_zero_pderiv [CharP k 2] (v : Fin 4 → k)
    (hv : ∀ i, eval v (pderiv i (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 +
      X 0 ^ 2 * X 2 * X 3 ^ 2 : MvPolynomial (Fin 4) k)) = 0) :
    v 1 * v 2 = 0 ∧ v 0 * v 1 * v 2 * v 3 = 0 := by
  have h := hv 0
  rw [example_4_3_3_pderiv] at h
  simp only [map_mul, map_pow, eval_X, mul_eq_zero, pow_eq_zero_iff, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true] at h
  rcases h with h | h <;> simp [h]

end Example433

/-! ### Example 4.3.3 at the point `x'` -/

section Example433Chart

variable {k : Type*} [Field k]

/-- In characteristic `2`, `(b + 1)^3 + (b + 1) = b^3 + b^2`. Volume 6, Example 4.3.3 of the
handbook. -/
theorem example_4_3_3_chart_identity {R : Type*} [CommRing R] [CharP R 2] (b : R) :
    (b + 1) ^ 3 + (b + 1) = b ^ 3 + b ^ 2 := by
  linear_combination (b ^ 2 + 2 * b + 1) * CharP.cast_eq_zero R 2

private theorem tie_433_chart_X [CharP k 2] {t : Fin 4 → k} (ht0 : t 0 = 1) (ht1 : t 1 = 0)
    (ht2 : t 2 = 1) :
    pointChart 3 t (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 2 :
      MvPolynomial (Fin 4) k) =
      X 3 ^ 4 * (X 0 + 1) * X 1 ^ 2 * (X 2 + 1) + X 3 ^ 5 * (X 0 + 1) ^ 2 * (X 2 + 1) ^ 3 +
        X 3 ^ 5 * (X 0 + 1) ^ 2 * (X 2 + 1) := by
  have h0 : pointChart 3 t (X 0 : MvPolynomial (Fin 4) k) = X 3 * (X 0 + 1) := by
    rw [pointChart_X_of_ne t (by decide : (0 : Fin 4) ≠ 3), ht0, C_1]
  have h1 : pointChart 3 t (X 1 : MvPolynomial (Fin 4) k) = X 3 * X 1 := by
    rw [pointChart_X_of_ne t (by decide : (1 : Fin 4) ≠ 3), ht1, C_0, add_zero]
  have h2 : pointChart 3 t (X 2 : MvPolynomial (Fin 4) k) = X 3 * (X 2 + 1) := by
    rw [pointChart_X_of_ne t (by decide : (2 : Fin 4) ≠ 3), ht2, C_1]
  simp only [map_add, map_mul, map_pow, pointChart_X_self, h0, h1, h2]
  ring

/-- In characteristic `2`, the `x_4`-chart at `t = (1, 0, 1)` sends `F` to
`x_4^2 (x_2^2 x_4^2 (x_1 + 1)(x_3 + 1) + x_4^3 (x_1^2 + 1)(x_3^3 + x_3^2))`. Volume 6,
Example 4.3.3 of the handbook. -/
theorem example_4_3_3_chart [CharP k 2] {t : Fin 4 → k} (ht0 : t 0 = 1) (ht1 : t 1 = 0)
    (ht2 : t 2 = 1) :
    pointChart 3 t (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 2 :
      MvPolynomial (Fin 4) k) =
      X 3 ^ 2 * (X 1 ^ 2 * X 3 ^ 2 * (X 0 + 1) * (X 2 + 1) +
        X 3 ^ 3 * (X 0 ^ 2 + 1) * (X 2 ^ 3 + X 2 ^ 2)) := by
  rw [tie_433_chart_X ht0 ht1 ht2]
  linear_combination (X 3 ^ 5 * (X 0 * (X 2 ^ 3 + X 2 ^ 2) + (X 2 + 1) ^ 2 * (X 0 + 1) ^ 2)) *
    tie4_two (k := k)

/-- In characteristic `2`, the `x_4`-chart at `t = (1, 0, 1)` sends `F` to
`x_4^2 ((x_2 x_4)^2 + F')` with `F' = x_1 x_2^2 x_3 x_4^2 + x_1 x_2^2 x_4^2 + x_2^2 x_3 x_4^2 +
x_1^2 x_3^3 x_4^3 + x_1^2 x_3^2 x_4^3 + x_3^3 x_4^3 + x_3^2 x_4^3`. Volume 6, Example 4.3.3 of the
handbook. -/
theorem example_4_3_3_chart_eq [CharP k 2] {t : Fin 4 → k} (ht0 : t 0 = 1) (ht1 : t 1 = 0)
    (ht2 : t 2 = 1) :
    pointChart 3 t (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 2 :
      MvPolynomial (Fin 4) k) =
      X 3 ^ 2 * ((X 1 * X 3) ^ 2 + (X 0 * X 1 ^ 2 * X 2 * X 3 ^ 2 + X 0 * X 1 ^ 2 * X 3 ^ 2 +
        X 1 ^ 2 * X 2 * X 3 ^ 2 + X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 3 + X 0 ^ 2 * X 2 ^ 2 * X 3 ^ 3 +
        X 2 ^ 3 * X 3 ^ 3 + X 2 ^ 2 * X 3 ^ 3)) := by
  rw [example_4_3_3_chart ht0 ht1 ht2]
  ring

/-- In characteristic `2`, the `x_4`-chart at `t = (1, 0, 1)` sends `Z^2 + F` to `x_4^2` times the
image of `Z'^2 + F'` under the translation `Z' ↦ Z' + x_2 x_4`. So the translation removes the
square `x_2^2 x_4^2`, and `Z'^2 + F'` is the strict transform. Volume 6, Example 4.3.3 of the
handbook. -/
theorem example_4_3_3_strictTransform [CharP k 2] {t : Fin 4 → k} (ht0 : t 0 = 1)
    (ht1 : t 1 = 0) (ht2 : t 2 = 1) :
    pointChartZ 3 t (purelyInseparable 2
      (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 2 :
        MvPolynomial (Fin 4) k)) =
      X (some 3) ^ 2 * zShift (X 1 * X 3) (purelyInseparable 2
        (X 0 * X 1 ^ 2 * X 2 * X 3 ^ 2 + X 0 * X 1 ^ 2 * X 3 ^ 2 + X 1 ^ 2 * X 2 * X 3 ^ 2 +
          X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 3 + X 0 ^ 2 * X 2 ^ 2 * X 3 ^ 3 + X 2 ^ 3 * X 3 ^ 3 +
          X 2 ^ 2 * X 3 ^ 3)) := by
  rw [pointChartZ_purelyInseparable (example_4_3_3_chart_eq ht0 ht1 ht2)]
  have h := zShift_purelyInseparable 2 1 (X 1 * X 3 : MvPolynomial (Fin 4) k)
    (X 0 * X 1 ^ 2 * X 2 * X 3 ^ 2 + X 0 * X 1 ^ 2 * X 3 ^ 2 + X 1 ^ 2 * X 2 * X 3 ^ 2 +
      X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 3 + X 0 ^ 2 * X 2 ^ 2 * X 3 ^ 3 + X 2 ^ 3 * X 3 ^ 3 +
      X 2 ^ 2 * X 3 ^ 3)
  rw [pow_one] at h
  rw [h, add_comm ((X 1 * X 3) ^ 2)]

/-- The new divisor at `t = (1, 0, 1)` of the `x_4`-chart is `E' = div(x_2 x_4)`. Volume 6,
Example 4.3.3 of the handbook. -/
theorem example_4_3_3_blowupDivisor [DecidableEq k] {t : Fin 4 → k} (ht0 : t 0 = 1)
    (ht1 : t 1 = 0) (ht2 : t 2 = 1) : blowupDivisor Finset.univ 3 t = {1, 3} := by
  ext i
  fin_cases i <;> simp [blowupDivisor, ht0, ht1, ht2]

/-- `F'` is clean for `2`. Volume 6, Example 4.3.3 of the handbook. -/
theorem example_4_3_3_isClean' :
    IsClean 2 (X 0 * X 1 ^ 2 * X 2 * X 3 ^ 2 + X 0 * X 1 ^ 2 * X 3 ^ 2 + X 1 ^ 2 * X 2 * X 3 ^ 2 +
      X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 3 + X 0 ^ 2 * X 2 ^ 2 * X 3 ^ 3 + X 2 ^ 3 * X 3 ^ 3 +
      X 2 ^ 2 * X 3 ^ 3 : MvPolynomial (Fin 4) k) := by
  rw [show (X 0 * X 1 ^ 2 * X 2 * X 3 ^ 2 + X 0 * X 1 ^ 2 * X 3 ^ 2 + X 1 ^ 2 * X 2 * X 3 ^ 2 +
      X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 3 + X 0 ^ 2 * X 2 ^ 2 * X 3 ^ 3 + X 2 ^ 3 * X 3 ^ 3 +
      X 2 ^ 2 * X 3 ^ 3 : MvPolynomial (Fin 4) k) =
      monomial (single 0 1 + single 1 2 + single 2 1 + single 3 2) 1 +
        monomial (single 0 1 + single 1 2 + single 3 2) 1 +
        monomial (single 1 2 + single 2 1 + single 3 2) 1 +
        monomial (single 0 2 + single 2 3 + single 3 3) 1 +
        monomial (single 0 2 + single 2 2 + single 3 3) 1 +
        monomial (single 2 3 + single 3 3) 1 + monomial (single 2 2 + single 3 3) 1
      by simp [X, monomial_pow, monomial_mul_monomial]]
  refine tie4_isClean_add (tie4_isClean_add (tie4_isClean_add (tie4_isClean_add
    (tie4_isClean_add (tie4_isClean_add ?_ ?_) ?_) ?_) ?_) ?_) ?_
  · exact tie4_isClean_monomial _ ⟨0, by simp⟩
  · exact tie4_isClean_monomial _ ⟨0, by simp⟩
  · exact tie4_isClean_monomial _ ⟨2, by simp⟩
  · exact tie4_isClean_monomial _ ⟨2, by simp⟩
  · exact tie4_isClean_monomial _ ⟨3, by simp⟩
  · exact tie4_isClean_monomial _ ⟨2, by simp⟩
  · exact tie4_isClean_monomial _ ⟨3, by simp⟩

private theorem tie_433'_G_ord :
    ord (X 0 * X 1 ^ 2 * X 2 + X 0 * X 1 ^ 2 + X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 * X 3 +
      X 0 ^ 2 * X 2 ^ 2 * X 3 + X 2 ^ 3 * X 3 + X 2 ^ 2 * X 3 : MvPolynomial (Fin 4) k) =
      ((3 : ℕ) : ℕ∞) := by
  refine le_antisymm ?_ ?_
  · refine (ord_le_ord_aeval ![X 0, X 1, 0, 0] (fun i => by fin_cases i <;> simp) _).trans ?_
    simp only [map_add, map_mul, map_pow, aeval_X]
    simp only [ord_mul, ord_X_pow, ord_X, Matrix.cons_val, mul_zero, add_zero, zero_add,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    norm_num
  · refine le_ord_add (le_ord_add (le_ord_add (le_ord_add (le_ord_add (le_ord_add ?_ ?_) ?_) ?_)
      ?_) ?_) ?_ <;> (simp only [ord_mul, ord_X_pow, ord_X]; norm_num)

/-- `ord F' = 5`, so `δ(x') = 5/2`. Volume 6, Example 4.3.3 of the handbook. -/
theorem example_4_3_3_ord' :
    ord (X 0 * X 1 ^ 2 * X 2 * X 3 ^ 2 + X 0 * X 1 ^ 2 * X 3 ^ 2 + X 1 ^ 2 * X 2 * X 3 ^ 2 +
      X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 3 + X 0 ^ 2 * X 2 ^ 2 * X 3 ^ 3 + X 2 ^ 3 * X 3 ^ 3 +
      X 2 ^ 2 * X 3 ^ 3 : MvPolynomial (Fin 4) k) = 5 := by
  rw [show (X 0 * X 1 ^ 2 * X 2 * X 3 ^ 2 + X 0 * X 1 ^ 2 * X 3 ^ 2 + X 1 ^ 2 * X 2 * X 3 ^ 2 +
      X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 3 + X 0 ^ 2 * X 2 ^ 2 * X 3 ^ 3 + X 2 ^ 3 * X 3 ^ 3 +
      X 2 ^ 2 * X 3 ^ 3 : MvPolynomial (Fin 4) k) = X 3 ^ 2 * (X 0 * X 1 ^ 2 * X 2 +
        X 0 * X 1 ^ 2 + X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 * X 3 + X 0 ^ 2 * X 2 ^ 2 * X 3 +
        X 2 ^ 3 * X 3 + X 2 ^ 2 * X 3) by ring, ord_mul, tie_433'_G_ord, ord_X_pow]
  norm_num

/-- For `E' = div(x_2 x_4)`, the residual factor of `F'` is `x_4^{-2} F'`, so `r' = (0, 2)`.
Volume 6, Example 4.3.3 of the handbook. -/
theorem example_4_3_3_residualFactor' :
    residualFactor {1, 3}
      (X 0 * X 1 ^ 2 * X 2 * X 3 ^ 2 + X 0 * X 1 ^ 2 * X 3 ^ 2 + X 1 ^ 2 * X 2 * X 3 ^ 2 +
        X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 3 + X 0 ^ 2 * X 2 ^ 2 * X 3 ^ 3 + X 2 ^ 3 * X 3 ^ 3 +
        X 2 ^ 2 * X 3 ^ 3 : MvPolynomial (Fin 4) k) =
      X 0 * X 1 ^ 2 * X 2 + X 0 * X 1 ^ 2 + X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 * X 3 +
        X 0 ^ 2 * X 2 ^ 2 * X 3 + X 2 ^ 3 * X 3 + X 2 ^ 2 * X 3 := by
  rw [show (X 0 * X 1 ^ 2 * X 2 * X 3 ^ 2 + X 0 * X 1 ^ 2 * X 3 ^ 2 + X 1 ^ 2 * X 2 * X 3 ^ 2 +
      X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 3 + X 0 ^ 2 * X 2 ^ 2 * X 3 ^ 3 + X 2 ^ 3 * X 3 ^ 3 +
      X 2 ^ 2 * X 3 ^ 3 : MvPolynomial (Fin 4) k) = monomial (single 3 2) 1 *
        (X 0 * X 1 ^ 2 * X 2 + X 0 * X 1 ^ 2 + X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 * X 3 +
          X 0 ^ 2 * X 2 ^ 2 * X 3 + X 2 ^ 3 * X 3 + X 2 ^ 2 * X 3) by
    rw [← X_pow_eq_monomial]
    ring]
  refine residualFactor_monomial_mul ?_ ?_
  · intro i hi
    fin_cases i <;> simp at hi ⊢
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨single 2 2 + single 3 1, MvPolynomial.mem_support_iff.mpr (by
        simp [X, monomial_pow, monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff,
          Fin.forall_fin_succ, Finsupp.single_apply]), by simp⟩
    · exact ⟨single 0 1 + single 1 2, MvPolynomial.mem_support_iff.mpr (by
        simp [X, monomial_pow, monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff,
          Fin.forall_fin_succ, Finsupp.single_apply]), by simp⟩

/-- `ε(x') = 5 - 2 = 3 = ε(x) + 1`. Volume 6, Example 4.3.3 of the handbook. -/
theorem example_4_3_3_epsilon' :
    ord (residualFactor {1, 3}
      (X 0 * X 1 ^ 2 * X 2 * X 3 ^ 2 + X 0 * X 1 ^ 2 * X 3 ^ 2 + X 1 ^ 2 * X 2 * X 3 ^ 2 +
        X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 3 + X 0 ^ 2 * X 2 ^ 2 * X 3 ^ 3 + X 2 ^ 3 * X 3 ^ 3 +
        X 2 ^ 2 * X 3 ^ 3 : MvPolynomial (Fin 4) k)) = 3 := by
  rw [example_4_3_3_residualFactor']
  exact tie_433'_G_ord

/-- The initial form of `F'` is `x_1 x_2^2 x_4^2 + x_2^2 x_3 x_4^2 + x_3^2 x_4^3`. Volume 6,
Example 4.3.3 of the handbook. -/
theorem example_4_3_3_initialForm' :
    homogeneousComponent 5
      (X 0 * X 1 ^ 2 * X 2 * X 3 ^ 2 + X 0 * X 1 ^ 2 * X 3 ^ 2 + X 1 ^ 2 * X 2 * X 3 ^ 2 +
        X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 3 + X 0 ^ 2 * X 2 ^ 2 * X 3 ^ 3 + X 2 ^ 3 * X 3 ^ 3 +
        X 2 ^ 2 * X 3 ^ 3 : MvPolynomial (Fin 4) k) =
      X 0 * X 1 ^ 2 * X 3 ^ 2 + X 1 ^ 2 * X 2 * X 3 ^ 2 + X 2 ^ 2 * X 3 ^ 3 := by
  simp [X, monomial_pow, monomial_mul_monomial, tie4_hc_monomial]

end Example433Chart

/-! ### Example 4.3.5: the four charts at the origin -/

section Example435

variable {k : Type*} [Field k]

private theorem tie_435_ordG {A : MvPolynomial (Fin 4) k} (hA : (3 : ℕ∞) ≤ ord A) :
    ord (X 1 ^ 2 + A) = ((2 : ℕ) : ℕ∞) :=
  tie4_ord_add (m := 3) (ord_X_pow 1 2) (by exact_mod_cast hA) (by norm_num)

/-- The `x_1`-chart at the origin:
`π(F) = x_1^2 (x_1^2 x_2^2 x_3 + x_1^3 x_3^3 + x_1^3 x_3 x_4^2)`. Volume 6, Example 4.3.5 of the
handbook. -/
theorem example_4_3_5_chart_0 :
    pointChart 0 (0 : Fin 4 → k)
      (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 2) =
      X 0 ^ 2 * (X 0 ^ 2 * X 1 ^ 2 * X 2 + X 0 ^ 3 * X 2 ^ 3 + X 0 ^ 3 * X 2 * X 3 ^ 2) := by
  simp only [map_add, map_mul, map_pow, pointChart_X_self,
    tie4_origin (by decide : (1 : Fin 4) ≠ 0),
    tie4_origin (by decide : (2 : Fin 4) ≠ 0), tie4_origin (by decide : (3 : Fin 4) ≠ 0)]
  ring

/-- The `x_2`-chart at the origin:
`π(F) = x_2^2 (x_1 x_2^2 x_3 + x_1^2 x_2^3 x_3^3 + x_1^2 x_2^3 x_3 x_4^2)`. Volume 6,
Example 4.3.5 of the handbook. -/
theorem example_4_3_5_chart_1 :
    pointChart 1 (0 : Fin 4 → k)
      (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 2) =
      X 1 ^ 2 * (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 3 +
        X 0 ^ 2 * X 1 ^ 3 * X 2 * X 3 ^ 2) := by
  simp only [map_add, map_mul, map_pow, pointChart_X_self,
    tie4_origin (by decide : (0 : Fin 4) ≠ 1),
    tie4_origin (by decide : (2 : Fin 4) ≠ 1), tie4_origin (by decide : (3 : Fin 4) ≠ 1)]
  ring

/-- The `x_3`-chart at the origin:
`π(F) = x_3^2 (x_1 x_2^2 x_3^2 + x_1^2 x_3^3 + x_1^2 x_3^3 x_4^2)`. Volume 6, Example 4.3.5 of the
handbook. -/
theorem example_4_3_5_chart_2 :
    pointChart 2 (0 : Fin 4 → k)
      (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 2) =
      X 2 ^ 2 * (X 0 * X 1 ^ 2 * X 2 ^ 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 2) := by
  simp only [map_add, map_mul, map_pow, pointChart_X_self,
    tie4_origin (by decide : (0 : Fin 4) ≠ 2),
    tie4_origin (by decide : (1 : Fin 4) ≠ 2), tie4_origin (by decide : (3 : Fin 4) ≠ 2)]
  ring

/-- The `x_4`-chart at the origin:
`π(F) = x_4^2 (x_1 x_2^2 x_3 x_4^2 + x_1^2 x_3^3 x_4^3 + x_1^2 x_3 x_4^3)`. Volume 6,
Example 4.3.5 of the handbook. -/
theorem example_4_3_5_chart_3 :
    pointChart 3 (0 : Fin 4 → k)
      (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 2) =
      X 3 ^ 2 * (X 0 * X 1 ^ 2 * X 2 * X 3 ^ 2 + X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 3 +
        X 0 ^ 2 * X 2 * X 3 ^ 3) := by
  simp only [map_add, map_mul, map_pow, pointChart_X_self,
    tie4_origin (by decide : (0 : Fin 4) ≠ 3),
    tie4_origin (by decide : (1 : Fin 4) ≠ 3), tie4_origin (by decide : (2 : Fin 4) ≠ 3)]
  ring

end Example435

/-! ### Example 4.3.5: orders and residual factors -/

section Example435Orders

variable {k : Type*} [Field k]

private theorem tie_435_rest {A B : MvPolynomial (Fin 4) k} (hA : (3 : ℕ∞) ≤ ord A)
    (hB : (3 : ℕ∞) ≤ ord B) : ord (X 1 ^ 2 + A + B) = ((2 : ℕ) : ℕ∞) := by
  rw [add_assoc]
  exact tie4_ord_add (m := 3) (ord_X_pow 1 2) (by exact_mod_cast le_ord_add hA hB) (by norm_num)

private theorem tie_435_two {A B : MvPolynomial (Fin 4) k} (hA : (2 : ℕ∞) ≤ ord A)
    (hB : (2 : ℕ∞) ≤ ord B)
    (hA0 : aeval (![0, X 1, 0, 0] : Fin 4 → MvPolynomial (Fin 4) k) A = 0)
    (hB0 : aeval (![0, X 1, 0, 0] : Fin 4 → MvPolynomial (Fin 4) k) B = 0) :
    ord (X 1 ^ 2 + A + B) = ((2 : ℕ) : ℕ∞) := by
  refine le_antisymm ?_ ?_
  · refine (ord_le_ord_aeval (![0, X 1, 0, 0] : Fin 4 → MvPolynomial (Fin 4) k)
      (fun i => by fin_cases i <;> simp) _).trans ?_
    rw [map_add, map_add, hA0, hB0, add_zero, add_zero, map_pow, aeval_X]
    simp [ord_X_pow]
  · exact le_ord_add (le_ord_add (by rw [ord_X_pow]) hA) hB

private theorem tie_435_G1_ord :
    ord (1 + X 0 * X 1 * X 2 ^ 2 + X 0 * X 1 * X 3 ^ 2 : MvPolynomial (Fin 4) k) =
      ((0 : ℕ) : ℕ∞) := by
  rw [add_assoc]
  exact tie4_ord_add (m := 3) (by rw [ord_one]; rfl)
    (le_ord_add (by simp only [ord_mul, ord_X_pow, ord_X]; norm_num)
      (by simp only [ord_mul, ord_X_pow, ord_X]; norm_num)) (by norm_num)

/-- In the `x_1`-chart, `F' = x_1^2 x_3 G` with `G = x_2^2 + x_1 x_3^2 + x_1 x_4^2`, so
`r' = (2, 0, 1, 0)`. Volume 6, Example 4.3.5 of the handbook. -/
theorem example_4_3_5_residualFactor_0 :
    residualFactor Finset.univ
      (X 0 ^ 2 * X 1 ^ 2 * X 2 + X 0 ^ 3 * X 2 ^ 3 + X 0 ^ 3 * X 2 * X 3 ^ 2 :
        MvPolynomial (Fin 4) k) = X 1 ^ 2 + X 0 * X 2 ^ 2 + X 0 * X 3 ^ 2 := by
  rw [show (X 0 ^ 2 * X 1 ^ 2 * X 2 + X 0 ^ 3 * X 2 ^ 3 + X 0 ^ 3 * X 2 * X 3 ^ 2 :
      MvPolynomial (Fin 4) k) = monomial (single 0 2 + single 2 1) 1 *
        (X 1 ^ 2 + X 0 * X 2 ^ 2 + X 0 * X 3 ^ 2) by
    rw [show (monomial (single 0 2 + single 2 1) 1 : MvPolynomial (Fin 4) k) = X 0 ^ 2 * X 2 by
      simp [X, monomial_pow, monomial_mul_monomial]]
    ring]
  refine residualFactor_monomial_mul (fun i hi => absurd (Finset.mem_univ i) hi) ?_
  intro i _
  fin_cases i
  · exact ⟨single 1 2, MvPolynomial.mem_support_iff.mpr (by
      simp [X, monomial_pow, monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff,
        Fin.forall_fin_succ, Finsupp.single_apply]), by simp⟩
  · exact ⟨single 0 1 + single 2 2, MvPolynomial.mem_support_iff.mpr (by
      simp [X, monomial_pow, monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff,
        Fin.forall_fin_succ, Finsupp.single_apply]), by simp⟩
  all_goals exact ⟨single 1 2, MvPolynomial.mem_support_iff.mpr (by
      simp [X, monomial_pow, monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff,
        Fin.forall_fin_succ, Finsupp.single_apply]), by simp⟩

/-- In the `x_1`-chart, `ord F' = 5` and `ε(x') = 2`. Volume 6, Example 4.3.5 of the handbook. -/
theorem example_4_3_5_ord_0 :
    ord (X 0 ^ 2 * X 1 ^ 2 * X 2 + X 0 ^ 3 * X 2 ^ 3 + X 0 ^ 3 * X 2 * X 3 ^ 2 :
        MvPolynomial (Fin 4) k) = 5 ∧
      ord (residualFactor Finset.univ
        (X 0 ^ 2 * X 1 ^ 2 * X 2 + X 0 ^ 3 * X 2 ^ 3 + X 0 ^ 3 * X 2 * X 3 ^ 2 :
          MvPolynomial (Fin 4) k)) = 2 := by
  have hG := tie_435_rest (k := k) (A := X 0 * X 2 ^ 2) (B := X 0 * X 3 ^ 2)
    (by simp only [ord_mul, ord_X_pow, ord_X]; norm_num)
    (by simp only [ord_mul, ord_X_pow, ord_X]; norm_num)
  refine ⟨?_, by rw [example_4_3_5_residualFactor_0, hG]; rfl⟩
  rw [show (X 0 ^ 2 * X 1 ^ 2 * X 2 + X 0 ^ 3 * X 2 ^ 3 + X 0 ^ 3 * X 2 * X 3 ^ 2 :
      MvPolynomial (Fin 4) k) = X 0 ^ 2 * X 2 * (X 1 ^ 2 + X 0 * X 2 ^ 2 + X 0 * X 3 ^ 2) by ring,
    ord_mul, ord_mul, hG, ord_X_pow, ord_X]
  norm_num

/-- In the `x_2`-chart, `F' = x_1 x_2^2 x_3 G` with `G = 1 + x_1 x_2 x_3^2 + x_1 x_2 x_4^2`, so
`r' = (1, 2, 1, 0)`. Volume 6, Example 4.3.5 of the handbook. -/
theorem example_4_3_5_residualFactor_1 :
    residualFactor Finset.univ
      (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 3 + X 0 ^ 2 * X 1 ^ 3 * X 2 * X 3 ^ 2 :
        MvPolynomial (Fin 4) k) = 1 + X 0 * X 1 * X 2 ^ 2 + X 0 * X 1 * X 3 ^ 2 := by
  rw [show (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 3 + X 0 ^ 2 * X 1 ^ 3 * X 2 * X 3 ^ 2 :
      MvPolynomial (Fin 4) k) = monomial (single 0 1 + single 1 2 + single 2 1) 1 *
        (1 + X 0 * X 1 * X 2 ^ 2 + X 0 * X 1 * X 3 ^ 2) by
    rw [show (monomial (single 0 1 + single 1 2 + single 2 1) 1 : MvPolynomial (Fin 4) k) =
      X 0 * X 1 ^ 2 * X 2 by simp [X, monomial_pow, monomial_mul_monomial]]
    ring]
  refine residualFactor_monomial_mul (fun i hi => absurd (Finset.mem_univ i) hi) ?_
  intro i _
  exact ⟨0, MvPolynomial.mem_support_iff.mpr (by
      simp [X, monomial_pow, monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff,
        Finsupp.single_apply]), rfl⟩

/-- In the `x_2`-chart, `ord F' = 4` and `ε(x') = 0`. Volume 6, Example 4.3.5 of the handbook. -/
theorem example_4_3_5_ord_1 :
    ord (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 3 + X 0 ^ 2 * X 1 ^ 3 * X 2 * X 3 ^ 2 :
        MvPolynomial (Fin 4) k) = 4 ∧
      ord (residualFactor Finset.univ
        (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 3 + X 0 ^ 2 * X 1 ^ 3 * X 2 * X 3 ^ 2 :
          MvPolynomial (Fin 4) k)) = 0 := by
  refine ⟨?_, by rw [example_4_3_5_residualFactor_1, tie_435_G1_ord]; rfl⟩
  rw [show (X 0 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 3 + X 0 ^ 2 * X 1 ^ 3 * X 2 * X 3 ^ 2 :
      MvPolynomial (Fin 4) k) = X 0 * X 1 ^ 2 * X 2 *
        (1 + X 0 * X 1 * X 2 ^ 2 + X 0 * X 1 * X 3 ^ 2) by ring,
    ord_mul, ord_mul, ord_mul, tie_435_G1_ord, ord_X_pow, ord_X, ord_X]
  norm_num

/-- In the `x_3`-chart, `F' = x_1 x_3^2 G` with `G = x_2^2 + x_1 x_3 + x_1 x_3 x_4^2`, so
`r' = (1, 0, 2, 0)`. Volume 6, Example 4.3.5 of the handbook. -/
theorem example_4_3_5_residualFactor_2 :
    residualFactor Finset.univ
      (X 0 * X 1 ^ 2 * X 2 ^ 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 2 :
        MvPolynomial (Fin 4) k) = X 1 ^ 2 + X 0 * X 2 + X 0 * X 2 * X 3 ^ 2 := by
  rw [show (X 0 * X 1 ^ 2 * X 2 ^ 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 2 :
      MvPolynomial (Fin 4) k) = monomial (single 0 1 + single 2 2) 1 *
        (X 1 ^ 2 + X 0 * X 2 + X 0 * X 2 * X 3 ^ 2) by
    rw [show (monomial (single 0 1 + single 2 2) 1 : MvPolynomial (Fin 4) k) = X 0 * X 2 ^ 2 by
      simp [X, monomial_pow, monomial_mul_monomial]]
    ring]
  refine residualFactor_monomial_mul (fun i hi => absurd (Finset.mem_univ i) hi) ?_
  intro i _
  fin_cases i
  · exact ⟨single 1 2, MvPolynomial.mem_support_iff.mpr (by
      simp [X, monomial_pow, monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff,
        Fin.forall_fin_succ, Finsupp.single_apply]), by simp⟩
  · exact ⟨single 0 1 + single 2 1, MvPolynomial.mem_support_iff.mpr (by
      simp [X, monomial_pow, monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff,
        Fin.forall_fin_succ, Finsupp.single_apply]), by simp⟩
  all_goals exact ⟨single 1 2, MvPolynomial.mem_support_iff.mpr (by
      simp [X, monomial_pow, monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff,
        Fin.forall_fin_succ, Finsupp.single_apply]), by simp⟩

/-- In the `x_3`-chart, `ord F' = 5` and `ε(x') = 2`. Volume 6, Example 4.3.5 of the handbook. -/
theorem example_4_3_5_ord_2 :
    ord (X 0 * X 1 ^ 2 * X 2 ^ 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 2 :
        MvPolynomial (Fin 4) k) = 5 ∧
      ord (residualFactor Finset.univ
        (X 0 * X 1 ^ 2 * X 2 ^ 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 2 :
          MvPolynomial (Fin 4) k)) = 2 := by
  have hG := tie_435_two (k := k) (A := X 0 * X 2) (B := X 0 * X 2 * X 3 ^ 2)
    (by simp only [ord_mul, ord_X]; norm_num)
    (by simp only [ord_mul, ord_X_pow, ord_X]; norm_num) (by simp) (by simp)
  refine ⟨?_, by rw [example_4_3_5_residualFactor_2, hG]; rfl⟩
  rw [show (X 0 * X 1 ^ 2 * X 2 ^ 2 + X 0 ^ 2 * X 2 ^ 3 + X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 2 :
      MvPolynomial (Fin 4) k) = X 0 * X 2 ^ 2 * (X 1 ^ 2 + X 0 * X 2 + X 0 * X 2 * X 3 ^ 2) by
      ring,
    ord_mul, ord_mul, hG, ord_X_pow, ord_X]
  norm_num

/-- In the `x_4`-chart, `F' = x_1 x_3 x_4^2 G` with `G = x_2^2 + x_1 x_3^2 x_4 + x_1 x_4`, so
`r' = (1, 0, 1, 2)`. Volume 6, Example 4.3.5 of the handbook. -/
theorem example_4_3_5_residualFactor_3 :
    residualFactor Finset.univ
      (X 0 * X 1 ^ 2 * X 2 * X 3 ^ 2 + X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 3 :
        MvPolynomial (Fin 4) k) = X 1 ^ 2 + X 0 * X 2 ^ 2 * X 3 + X 0 * X 3 := by
  rw [show (X 0 * X 1 ^ 2 * X 2 * X 3 ^ 2 + X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 3 :
      MvPolynomial (Fin 4) k) = monomial (single 0 1 + single 2 1 + single 3 2) 1 *
        (X 1 ^ 2 + X 0 * X 2 ^ 2 * X 3 + X 0 * X 3) by
    rw [show (monomial (single 0 1 + single 2 1 + single 3 2) 1 : MvPolynomial (Fin 4) k) =
      X 0 * X 2 * X 3 ^ 2 by simp [X, monomial_pow, monomial_mul_monomial]]
    ring]
  refine residualFactor_monomial_mul (fun i hi => absurd (Finset.mem_univ i) hi) ?_
  intro i _
  fin_cases i
  · exact ⟨single 1 2, MvPolynomial.mem_support_iff.mpr (by
      simp [X, monomial_pow, monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff,
        Fin.forall_fin_succ, Finsupp.single_apply]), by simp⟩
  · exact ⟨single 0 1 + single 3 1, MvPolynomial.mem_support_iff.mpr (by
      simp [X, monomial_pow, monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff,
        Fin.forall_fin_succ, Finsupp.single_apply]), by simp⟩
  all_goals exact ⟨single 1 2, MvPolynomial.mem_support_iff.mpr (by
      simp [X, monomial_pow, monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff,
        Fin.forall_fin_succ, Finsupp.single_apply]), by simp⟩

/-- In the `x_4`-chart, `ord F' = 6` and `ε(x') = 2`. Volume 6, Example 4.3.5 of the handbook. -/
theorem example_4_3_5_ord_3 :
    ord (X 0 * X 1 ^ 2 * X 2 * X 3 ^ 2 + X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 3 :
        MvPolynomial (Fin 4) k) = 6 ∧
      ord (residualFactor Finset.univ
        (X 0 * X 1 ^ 2 * X 2 * X 3 ^ 2 + X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 3 :
          MvPolynomial (Fin 4) k)) = 2 := by
  have hG := tie_435_two (k := k) (A := X 0 * X 2 ^ 2 * X 3) (B := X 0 * X 3)
    (by simp only [ord_mul, ord_X_pow, ord_X]; norm_num)
    (by simp only [ord_mul, ord_X]; norm_num) (by simp) (by simp)
  refine ⟨?_, by rw [example_4_3_5_residualFactor_3, hG]; rfl⟩
  rw [show (X 0 * X 1 ^ 2 * X 2 * X 3 ^ 2 + X 0 ^ 2 * X 2 ^ 3 * X 3 ^ 3 + X 0 ^ 2 * X 2 * X 3 ^ 3 :
      MvPolynomial (Fin 4) k) = X 0 * X 2 * X 3 ^ 2 *
        (X 1 ^ 2 + X 0 * X 2 ^ 2 * X 3 + X 0 * X 3) by ring,
    ord_mul, ord_mul, ord_mul, hG, ord_X_pow, ord_X, ord_X]
  norm_num

end Example435Orders

end Singularity.Examples
