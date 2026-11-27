/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# The blowup of `z^2 + x^3 + y^5` in characteristic `2`, `3` and `5`

Let `F = z^2 + x^3 + y^5`. Volume 4, Example 2.3.13 of the handbook computes the blowup of `X = V(F)` at the origin in characteristic `p ∈ {2, 3, 5}`. This file proves the algebraic steps of part 2.

* `Singularity.eEight_xChart`, `Singularity.eEight_yChart` and `Singularity.eEight_zChart`: the three charts of the blowup at the origin. In the `x`-chart, `F = x^2 H` with `H = z_1^2 + x + x^3 y_1^5`, and in the `y`-chart, `F = y^2 (z_1^2 + y x_1^3 + y^3)`.
* `Singularity.eEight_xChart_regular`: if `2 = 0`, `3 = 0` or `5 = 0` in `R`, then `H` and its partial derivatives `1 + 3 x^2 y_1^5`, `5 x^3 y_1^4` and `2 z_1` generate the unit ideal. Thus the `x`-chart is regular. The three cases are `Singularity.eEight_xChart_regular_two`, `Singularity.eEight_xChart_regular_three` and `Singularity.eEight_xChart_regular_five`.
* `Singularity.eEight_yChart_exceptional`: on the exceptional curve `y = 0` of the `y`-chart, the equation and its derivative `x_1^3 + 3 y^2` in `y` vanish only at `x_1 = z_1 = 0`. So the origin `Q` of the `y`-chart is the only singular point there.

The identities hold in each commutative ring. The file does not prove part 1, the normality of the blowup, or the claim that `Q` is singular.
-/

namespace Singularity

variable {R : Type*} [CommRing R]

/-- The `x`-chart: `y = x y_1` and `z = x z_1` give `F = x^2 (z_1^2 + x + x^3 y_1^5)` (Volume 4, Example 2.3.13, part 2 of the handbook). -/
theorem eEight_xChart (x y₁ z₁ : R) :
    (x * z₁) ^ 2 + x ^ 3 + (x * y₁) ^ 5 = x ^ 2 * (z₁ ^ 2 + x + x ^ 3 * y₁ ^ 5) := by
  ring

/-- The `y`-chart: `x = y x_1` and `z = y z_1` give `F = y^2 (z_1^2 + y x_1^3 + y^3)` (Volume 4, Example 2.3.13, part 2 of the handbook). -/
theorem eEight_yChart (y x₁ z₁ : R) :
    (y * z₁) ^ 2 + (y * x₁) ^ 3 + y ^ 5 = y ^ 2 * (z₁ ^ 2 + y * x₁ ^ 3 + y ^ 3) := by
  ring

/-- The `z`-chart: `x = z x_1` and `y = z y_1` give `F = z^2 (1 + z x_1^3 + z^3 y_1^5)` (Volume 4, Example 2.3.13, part 2 of the handbook). -/
theorem eEight_zChart (z x₁ y₁ : R) :
    z ^ 2 + (z * x₁) ^ 3 + (z * y₁) ^ 5 = z ^ 2 * (1 + z * x₁ ^ 3 + z ^ 3 * y₁ ^ 5) := by
  ring

/-- If `r a + s b + t c + w d = 1`, then `(a, b, c, d)` is the unit ideal. -/
theorem span_four_eq_top_of_comb {a b c d r s t w : R} (h : r * a + s * b + t * c + w * d = 1) :
    Ideal.span {a, b, c, d} = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← h]
  refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_) ?_ <;>
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

/-- In characteristic `2`, `H = z_1^2 + x + x^3 y_1^5` and its partial derivatives generate the unit ideal (Volume 4, Example 2.3.13, part 2 of the handbook). -/
theorem eEight_xChart_regular_two (h2 : (2 : R) = 0) (x y₁ z₁ : R) :
    Ideal.span {z₁ ^ 2 + x + x ^ 3 * y₁ ^ 5, 1 + 3 * x ^ 2 * y₁ ^ 5, 5 * x ^ 3 * y₁ ^ 4, 2 * z₁} = ⊤ :=
  span_four_eq_top_of_comb (r := 0) (s := 1 - x ^ 2 * y₁ ^ 5 + (x ^ 2 * y₁ ^ 5) ^ 2)
    (t := -(x ^ 3 * y₁ ^ 11)) (w := 0) (by
      linear_combination (x ^ 2 * y₁ ^ 5 - (x ^ 2 * y₁ ^ 5) ^ 2 - (x ^ 2 * y₁ ^ 5) ^ 3) * h2)

/-- In characteristic `3`, `H = z_1^2 + x + x^3 y_1^5` and its partial derivatives generate the unit ideal, since `H_x = 1` (Volume 4, Example 2.3.13, part 2 of the handbook). -/
theorem eEight_xChart_regular_three (h3 : (3 : R) = 0) (x y₁ z₁ : R) :
    Ideal.span {z₁ ^ 2 + x + x ^ 3 * y₁ ^ 5, 1 + 3 * x ^ 2 * y₁ ^ 5, 5 * x ^ 3 * y₁ ^ 4, 2 * z₁} = ⊤ :=
  span_four_eq_top_of_comb (r := 0) (s := 1) (t := 0) (w := 0) (by
    linear_combination (x ^ 2 * y₁ ^ 5) * h3)

/-- In characteristic `5`, `H = z_1^2 + x + x^3 y_1^5` and its partial derivatives generate the unit ideal (Volume 4, Example 2.3.13, part 2 of the handbook). -/
theorem eEight_xChart_regular_five (h5 : (5 : R) = 0) (x y₁ z₁ : R) :
    Ideal.span {z₁ ^ 2 + x + x ^ 3 * y₁ ^ 5, 1 + 3 * x ^ 2 * y₁ ^ 5, 5 * x ^ 3 * y₁ ^ 4, 2 * z₁} = ⊤ :=
  span_four_eq_top_of_comb (r := -27 * x * y₁ ^ 5) (s := 1 + 9 * x ^ 2 * y₁ ^ 5) (t := 0)
    (w := 36 * x * y₁ ^ 5 * z₁) (by
      linear_combination (9 * x * y₁ ^ 5 * z₁ ^ 2 - 3 * x ^ 2 * y₁ ^ 5) * h5)

/-- If `2 = 0`, `3 = 0` or `5 = 0` in `R`, then `H = z_1^2 + x + x^3 y_1^5` and its partial derivatives `1 + 3 x^2 y_1^5`, `5 x^3 y_1^4` and `2 z_1` generate the unit ideal. Thus the `x`-chart of the blowup of `z^2 + x^3 + y^5` at the origin is regular (Volume 4, Example 2.3.13, part 2 of the handbook). -/
theorem eEight_xChart_regular (hp : (2 : R) = 0 ∨ (3 : R) = 0 ∨ (5 : R) = 0) (x y₁ z₁ : R) :
    Ideal.span {z₁ ^ 2 + x + x ^ 3 * y₁ ^ 5, 1 + 3 * x ^ 2 * y₁ ^ 5, 5 * x ^ 3 * y₁ ^ 4, 2 * z₁} = ⊤ := by
  rcases hp with h | h | h
  · exact eEight_xChart_regular_two h x y₁ z₁
  · exact eEight_xChart_regular_three h x y₁ z₁
  · exact eEight_xChart_regular_five h x y₁ z₁

/-- On the exceptional curve `y = 0` of the `y`-chart, `z_1^2 + y x_1^3 + y^3 = 0` and its derivative `x_1^3 + 3 y^2 = 0` in `y` give `x_1 = z_1 = 0` (Volume 4, Example 2.3.13, part 2 of the handbook). -/
theorem eEight_yChart_exceptional [IsDomain R] {y x₁ z₁ : R} (hy : y = 0)
    (hH : z₁ ^ 2 + y * x₁ ^ 3 + y ^ 3 = 0) (hHy : x₁ ^ 3 + 3 * y ^ 2 = 0) : x₁ = 0 ∧ z₁ = 0 := by
  subst hy
  have h1 : z₁ ^ 2 = 0 := by linear_combination hH
  have h2 : x₁ ^ 3 = 0 := by linear_combination hHy
  exact ⟨(pow_eq_zero_iff (n := 3) (by norm_num)).mp h2,
    (pow_eq_zero_iff (n := 2) (by norm_num)).mp h1⟩

end Singularity
