/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# The blowup of the singularity `E_6`

Let `F = z^2 + x^3 + y^4`. Volume 4, Example 2.3.12 of the handbook resolves `X = V(F)` in characteristic not `2`, with the dual graph `E_6`. This file proves the algebraic steps of part 2.

* `Singularity.eSix_xChart`, `Singularity.eSix_yChart` and `Singularity.eSix_zChart`: the three charts of the blowup at the origin. In the `y`-chart, `F = y^2 H` with `H = z_1^2 + y^2 + y x_1^3`.
* `Singularity.eSix_xChart_regular`: in the `x`-chart, `G = z_1^2 + x + x^2 y_1^4`, `G_x = 1 + 2 x y_1^4` and `G_{z_1} = 2 z_1` generate the unit ideal, in each commutative ring. Thus the `x`-chart is regular.
* `Singularity.eSix_yChart_exceptional`: on the exceptional curve `y = 0` of the `y`-chart, `H = H_y = 0` gives `x_1 = z_1 = 0`. So `Q = (0, 0, 0)` is the only singular point there.
* `Singularity.eSix_complete_square`: let `ι^2 = -1`, `ζ^3 = 2`, `v ζ = 1` and `2 u = 1`. With `Y = y + x_1^3 / 2`, `a = Y + ι z_1`, `b = Y - ι z_1` and `c = x_1 / ζ`, `H = ab - c^6`. So near `Q` the blowup is `X_6 = V(ab - c^6)`.
* `Singularity.eSix_complete_square_inverse`: the inverse map `x_1 = ζ c`, `z_1 = (a - b) / (2ι)`, `y = (a + b)/2 - ζ^3 c^3 / 2`.
* `Singularity.eSix_exceptional_curve`: on `E_0`, where `y = z_1 = 0`, `a = b = c^3`.

The identities hold in each commutative ring. The file does not prove the claims on normality, part 3, or the self-intersections.
-/

namespace Singularity

variable {R : Type*} [CommRing R]

/-- The `x`-chart: `y = x y_1` and `z = x z_1` give `F = x^2 (z_1^2 + x + x^2 y_1^4)` (Volume 4, Example 2.3.12, part 2 of the handbook). -/
theorem eSix_xChart (x y₁ z₁ : R) :
    (x * z₁) ^ 2 + x ^ 3 + (x * y₁) ^ 4 = x ^ 2 * (z₁ ^ 2 + x + x ^ 2 * y₁ ^ 4) := by
  ring

/-- The `y`-chart: `x = y x_1` and `z = y z_1` give `F = y^2 (z_1^2 + y^2 + y x_1^3)` (Volume 4, Example 2.3.12, part 2 of the handbook). -/
theorem eSix_yChart (y x₁ z₁ : R) :
    (y * z₁) ^ 2 + (y * x₁) ^ 3 + y ^ 4 = y ^ 2 * (z₁ ^ 2 + y ^ 2 + y * x₁ ^ 3) := by
  ring

/-- The `z`-chart: `x = z x_1` and `y = z y_1` give `F = z^2 (1 + z x_1^3 + z^2 y_1^4)` (Volume 4, Example 2.3.12, part 2 of the handbook). -/
theorem eSix_zChart (z x₁ y₁ : R) :
    z ^ 2 + (z * x₁) ^ 3 + (z * y₁) ^ 4 = z ^ 2 * (1 + z * x₁ ^ 3 + z ^ 2 * y₁ ^ 4) := by
  ring

/-- The `x`-chart is regular: `G = z_1^2 + x + x^2 y_1^4`, `G_x = 1 + 2 x y_1^4` and `G_{z_1} = 2 z_1` generate the unit ideal, in each commutative ring (Volume 4, Example 2.3.12, part 2 of the handbook). -/
theorem eSix_xChart_regular (x y₁ z₁ : R) :
    Ideal.span {z₁ ^ 2 + x + x ^ 2 * y₁ ^ 4, 1 + 2 * x * y₁ ^ 4, 2 * z₁} = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have e : (1 : R) = (-4 * y₁ ^ 4) * (z₁ ^ 2 + x + x ^ 2 * y₁ ^ 4) +
      (1 + 2 * x * y₁ ^ 4) * (1 + 2 * x * y₁ ^ 4) + (2 * y₁ ^ 4 * z₁) * (2 * z₁) := by
    ring
  rw [e]
  refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_ <;>
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

/-- On the exceptional curve `y = 0` of the `y`-chart, `H = z_1^2 + y^2 + y x_1^3 = 0` and `H_y = 2y + x_1^3 = 0` give `x_1 = z_1 = 0` (Volume 4, Example 2.3.12, part 2 of the handbook). -/
theorem eSix_yChart_exceptional [IsDomain R] {y x₁ z₁ : R} (hy : y = 0)
    (hH : z₁ ^ 2 + y ^ 2 + y * x₁ ^ 3 = 0) (hHy : 2 * y + x₁ ^ 3 = 0) : x₁ = 0 ∧ z₁ = 0 := by
  subst hy
  have h1 : z₁ ^ 2 = 0 := by linear_combination hH
  have h2 : x₁ ^ 3 = 0 := by linear_combination hHy
  exact ⟨(pow_eq_zero_iff (n := 3) (by norm_num)).mp h2,
    (pow_eq_zero_iff (n := 2) (by norm_num)).mp h1⟩

/-- If `ζ^3 = 2`, `v ζ = 1` and `2 u = 1`, then `v^3 = u`, that is, `(1/ζ)^3 = 1/2`. -/
theorem eSix_inv_cube {ζ v u : R} (hζ : ζ ^ 3 = 2) (hv : v * ζ = 1) (hu : 2 * u = 1) :
    v ^ 3 = u := by
  calc v ^ 3 = v ^ 3 * (ζ ^ 3 * u) := by rw [hζ, hu, mul_one]
    _ = (v * ζ) ^ 3 * u := by ring
    _ = u := by rw [hv, one_pow, one_mul]

/-- Completing the square: with `Y = y + x_1^3 u`, `a = Y + ι z_1`, `b = Y - ι z_1` and `c = x_1 v`, where `ι^2 = -1`, `ζ^3 = 2`, `v ζ = 1` and `2 u = 1`, the equation `H = z_1^2 + y^2 + y x_1^3` is `ab - c^6` (Volume 4, Example 2.3.12, part 2 of the handbook). -/
theorem eSix_complete_square {ι ζ v u : R} (hι : ι ^ 2 = -1) (hζ : ζ ^ 3 = 2) (hv : v * ζ = 1)
    (hu : 2 * u = 1) (y x₁ z₁ : R) :
    (y + x₁ ^ 3 * u + ι * z₁) * (y + x₁ ^ 3 * u - ι * z₁) - (x₁ * v) ^ 6 =
      z₁ ^ 2 + y ^ 2 + y * x₁ ^ 3 := by
  have hv3 := eSix_inv_cube hζ hv hu
  linear_combination (y * x₁ ^ 3) * hu - z₁ ^ 2 * hι - x₁ ^ 6 * (v ^ 3 + u) * hv3

/-- The inverse of the change of coordinates of `eSix_complete_square`: `x_1 = ζ c`, `a - b = 2 ι z_1` and `y = (a + b)/2 - ζ^3 c^3 / 2` (Volume 4, Example 2.3.12, part 2 of the handbook). -/
theorem eSix_complete_square_inverse {ι ζ v u : R} (hv : v * ζ = 1) (hu : 2 * u = 1)
    (y x₁ z₁ : R) :
    ζ * (x₁ * v) = x₁ ∧
      (y + x₁ ^ 3 * u + ι * z₁) - (y + x₁ ^ 3 * u - ι * z₁) = 2 * ι * z₁ ∧
      ((y + x₁ ^ 3 * u + ι * z₁) + (y + x₁ ^ 3 * u - ι * z₁)) * u - ζ ^ 3 * (x₁ * v) ^ 3 * u = y := by
  refine ⟨by linear_combination x₁ * hv, by ring, ?_⟩
  linear_combination (y + x₁ ^ 3 * u) * hu - x₁ ^ 3 * u * ((v * ζ) ^ 2 + v * ζ + 1) * hv

/-- On the curve `E_0`, where `y = z_1 = 0`, the coordinates satisfy `a = b = c^3`: both `a` and `b` are `x_1^3 u`, and `c^3 = (x_1 v)^3 = x_1^3 u` (Volume 4, Example 2.3.12, part 2 of the handbook). -/
theorem eSix_exceptional_curve {ζ v u : R} (hζ : ζ ^ 3 = 2) (hv : v * ζ = 1) (hu : 2 * u = 1)
    (x₁ : R) : x₁ ^ 3 * u = (x₁ * v) ^ 3 := by
  rw [mul_pow, eSix_inv_cube hζ hv hu]

end Singularity
