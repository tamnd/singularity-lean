/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The embedded resolution of the two cusps `y^2 = x^3` and `y^2 = x^5`

Let `f = (y^2 - x^3)(y^2 - x^5)`. Volume 4, Example 3.1.10 of the handbook resolves the curve `C = V(f)` with five blowups of points. This file proves the algebraic identities of parts 1, 2 and 4.

* `Singularity.cuspPair_inter`: part 1, the curves `C_1 = V(y^2 - x^3)` and `C_2 = V(y^2 - x^5)` meet only at the origin of `S = A^2 \ V(1 - x^2)`. The statement holds in each ring without zero divisors.
* `Singularity.cuspPair_chart_one`, `Singularity.cuspPair_chart_two_y`, `Singularity.cuspPair_chart_two_x` and `Singularity.cuspPair_chart_three`: the substitutions of part 2 in the charts of the first three blowups.
* `Singularity.cuspPair_order_one` to `Singularity.cuspPair_order_five`: part 4. In a chart of the blowup `i` that contains the generic point of `E_i`, the composite substitution writes `f` as `e^(v_i)` times a polynomial that `e` does not divide, where `e` is the local equation of `E_i`. The exponents are `4, 7, 8, 12, 16`. The identities also give the orders of `f` along the earlier curves that pass through the chart.

The identities hold in each commutative ring. The file does not prove that the factors are not divisible by `e`, the claims on regularity and normal crossings, the value `δ = 9`, or part 3.
-/

namespace Singularity

/-- The curves `y^2 = x^3` and `y^2 = x^5` meet only at the origin of the open set `1 - x^2 ≠ 0` (Volume 4, Example 3.1.10, part 1 of the handbook). -/
theorem cuspPair_inter {R : Type*} [CommRing R] [NoZeroDivisors R] {x y : R}
    (h₁ : y ^ 2 = x ^ 3) (h₂ : y ^ 2 = x ^ 5) (hx : 1 - x ^ 2 ≠ 0) : x = 0 ∧ y = 0 := by
  have h : x ^ 3 * (1 - x ^ 2) = 0 := by
    calc x ^ 3 * (1 - x ^ 2) = x ^ 3 - x ^ 5 := by ring
      _ = 0 := by rw [← h₁, ← h₂, sub_self]
  have hx3 : x ^ 3 = 0 := (mul_eq_zero.mp h).resolve_right hx
  have hx0 : x = 0 := (pow_eq_zero_iff (n := 3) (by norm_num)).mp hx3
  refine ⟨hx0, ?_⟩
  rw [hx0] at h₁
  exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp (h₁.trans (by norm_num))

section Charts

variable {R : Type*} [CommRing R]

/-- The first blowup, chart `y = x y_1`: `f = x^4 (y_1^2 - x)(y_1^2 - x^3)` (Volume 4, Example 3.1.10, part 2 of the handbook). -/
theorem cuspPair_chart_one (x y₁ : R) :
    ((x * y₁) ^ 2 - x ^ 3) * ((x * y₁) ^ 2 - x ^ 5) = x ^ 4 * (y₁ ^ 2 - x) * (y₁ ^ 2 - x ^ 3) := by
  ring

/-- The second blowup, chart `y_1 = x y_2`: the strict transform `(y_1^2 - x)(y_1^2 - x^3)` is `x^3 (x y_2^2 - 1)(y_2^2 - x)` (Volume 4, Example 3.1.10, part 2 of the handbook). -/
theorem cuspPair_chart_two_y (x y₂ : R) :
    ((x * y₂) ^ 2 - x) * ((x * y₂) ^ 2 - x ^ 3) = x ^ 3 * (x * y₂ ^ 2 - 1) * (y₂ ^ 2 - x) := by
  ring

/-- The second blowup, chart `x = y_1 x_2`: the strict transform `(y_1^2 - x)(y_1^2 - x^3)` is `y_1^3 (y_1 - x_2)(1 - y_1 x_2^3)` (Volume 4, Example 3.1.10, part 2 of the handbook). -/
theorem cuspPair_chart_two_x (y₁ x₂ : R) :
    (y₁ ^ 2 - y₁ * x₂) * (y₁ ^ 2 - (y₁ * x₂) ^ 3) = y₁ ^ 3 * (y₁ - x₂) * (1 - y₁ * x₂ ^ 3) := by
  ring

/-- The third blowup, at `Q`, chart `x = y_2 x_3`: `y_2^2 - x` is `y_2 (y_2 - x_3)` (Volume 4, Example 3.1.10, part 2 of the handbook). -/
theorem cuspPair_chart_three (y₂ x₃ : R) : y₂ ^ 2 - y₂ * x₃ = y₂ * (y₂ - x₃) := by
  ring

/-- The function `f = (y^2 - x^3)(y^2 - x^5)`. -/
def cuspPair (x y : R) : R := (y ^ 2 - x ^ 3) * (y ^ 2 - x ^ 5)

/-- The order of `f` along `E_1` is `4`: with `y = x y_1`, `f = x^4 (y_1^2 - x)(y_1^2 - x^3)` (Volume 4, Example 3.1.10, part 4 of the handbook). -/
theorem cuspPair_order_one (x y₁ : R) :
    cuspPair x (x * y₁) = x ^ 4 * ((y₁ ^ 2 - x) * (y₁ ^ 2 - x ^ 3)) := by
  unfold cuspPair
  ring

/-- The order of `f` along `E_2` is `7`, and along `E_1` it is `4`: with `x = y_1 x_2` and `y = y_1^2 x_2`, `f = y_1^7 x_2^4 (y_1 - x_2)(1 - y_1 x_2^3)` (Volume 4, Example 3.1.10, part 4 of the handbook). -/
theorem cuspPair_order_two (y₁ x₂ : R) :
    cuspPair (y₁ * x₂) (y₁ ^ 2 * x₂) = y₁ ^ 7 * x₂ ^ 4 * ((y₁ - x₂) * (1 - y₁ * x₂ ^ 3)) := by
  unfold cuspPair
  ring

/-- The order of `f` along `E_3` is `8`, and along `E_2` it is `7`: with `x = y_2 x_3` and `y = y_2^3 x_3^2`, `f = y_2^8 x_3^7 (y_2^3 x_3 - 1)(y_2 - x_3)` (Volume 4, Example 3.1.10, part 4 of the handbook). -/
theorem cuspPair_order_three (y₂ x₃ : R) :
    cuspPair (y₂ * x₃) (y₂ ^ 3 * x₃ ^ 2) =
      y₂ ^ 8 * x₃ ^ 7 * ((y₂ ^ 3 * x₃ - 1) * (y₂ - x₃)) := by
  unfold cuspPair
  ring

/-- The order of `f` along `E_4` is `12`, and along `E_2` it is `7`: the blowup at `P` with the chart `y_1 = x_2 w` gives `x = x_2^2 w` and `y = x_2^3 w^2`, and `f = x_2^12 w^7 (w - 1)(1 - w x_2^4)` (Volume 4, Example 3.1.10, part 4 of the handbook). -/
theorem cuspPair_order_four (x₂ w : R) :
    cuspPair (x₂ ^ 2 * w) (x₂ ^ 3 * w ^ 2) = x₂ ^ 12 * w ^ 7 * ((w - 1) * (1 - w * x₂ ^ 4)) := by
  unfold cuspPair
  ring

/-- The order of `f` along `E_5` is `16`, and along `E_3` it is `8`: the blowup at `R` with the chart `y_2 = x_3 w` gives `x = x_3^2 w` and `y = x_3^5 w^3`, and `f = x_3^16 w^8 (w^3 x_3^4 - 1)(w - 1)` (Volume 4, Example 3.1.10, part 4 of the handbook). -/
theorem cuspPair_order_five (x₃ w : R) :
    cuspPair (x₃ ^ 2 * w) (x₃ ^ 5 * w ^ 3) =
      x₃ ^ 16 * w ^ 8 * ((w ^ 3 * x₃ ^ 4 - 1) * (w - 1)) := by
  unfold cuspPair
  ring

end Charts

end Singularity
