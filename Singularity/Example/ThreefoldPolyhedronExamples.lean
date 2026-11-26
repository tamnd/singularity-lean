/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.CharacteristicPolyhedronClean

/-!
# The computations of Section 3.3

This file proves the ring identities that Examples 3.3.1 to 3.3.4 of Volume 6 of the handbook use.
The variables `u_1, u_2, u_3` are elements `a, b, c` of a commutative ring of characteristic `2`
or `3`, or the variables `X 0, X 1, X 2` of a power series ring.

What the file proves:

* Example 3.3.1: the chart substitution `u_2 ↦ u_1 (u_2 + 1)`, `u_3 ↦ u_1 u_3` sends `f` to
  `u_1^2` times the series of the handbook (`example_3_3_1_chart`), and the translation by
  `u_1^2 u_2 u_3` removes the square (`example_3_3_1_clean`).
* Example 3.3.2: the point `w` is the convex combination `8/15 v_1 + 2/15 v_2 + 1/3 v_3`
  (`example_3_3_2_combination`), the four points lie in the plane `x_1 + x_2 + x_3 = 5/3`
  (`example_3_3_2_plane`), and `3 U_1 U_2 U_3^2 + c U_1^3 U_2 = c U_1^3 U_2` in characteristic `3`
  (`example_3_3_2_derivative`).
* Example 3.3.3: `g^3 + f = u_2^4 + u_3^5` for `g = -u_1 - u_1 u_2` in characteristic `3`
  (`example_3_3_3_clean`), so `X ↦ X + g` gives `X^3 + u_2^4 + u_3^5` (`taylor_example_3_3_3`).
* Example 3.3.4: `(u + t)^3 = u^3 + t u^2 + t^2 u + t^3` in characteristic `2`
  (`add_pow_three_charTwo`), and the chart identity `u_1^{-2} f = u_1 g`
  (`example_3_3_4_chart`).

The invariants `δ`, `ε`, `ω` and `ι` of these examples, condition (E), and the blowups as schemes
are not proved here.
-/

open Polynomial

namespace Singularity.Examples

section CharTwo

variable {R : Type*} [CommRing R] [CharP R 2]

/-- The chart substitution of Example 3.3.1. In characteristic `2`, with `u_2 ↦ u_1 (u_2 + 1)` and
`u_3 ↦ u_1 u_3`, the series `f = u_1 u_2^3 u_3^2 + u_1^3 u_2 u_3^2 + u_1^8 u_2 u_3` becomes
`u_1^2 (u_1^4 u_2^3 u_3^2 + u_1^4 u_2^2 u_3^2 + u_1^8 u_2 u_3 + u_1^8 u_3)`. Volume 6,
Example 3.3.1 of the handbook. -/
theorem example_3_3_1_chart (a b c : R) :
    a * (a * (b + 1)) ^ 3 * (a * c) ^ 2 + a ^ 3 * (a * (b + 1)) * (a * c) ^ 2 +
        a ^ 8 * (a * (b + 1)) * (a * c) =
      a ^ 2 * (a ^ 4 * b ^ 3 * c ^ 2 + a ^ 4 * b ^ 2 * c ^ 2 + a ^ 8 * b * c + a ^ 8 * c) := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  linear_combination (a ^ 6 * c ^ 2 * (b ^ 2 + 2 * b + 1)) * h2

/-- The cleaning step of Example 3.3.1. In characteristic `2`, the translation by
`u_1^2 u_2 u_3` removes the square `u_1^4 u_2^2 u_3^2`. Volume 6, Example 3.3.1 of the
handbook. -/
theorem example_3_3_1_clean (a b c : R) :
    (a ^ 2 * b * c) ^ 2 +
        (a ^ 4 * b ^ 3 * c ^ 2 + a ^ 4 * b ^ 2 * c ^ 2 + a ^ 8 * b * c + a ^ 8 * c) =
      a ^ 4 * b ^ 3 * c ^ 2 + a ^ 8 * b * c + a ^ 8 * c := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  linear_combination (a ^ 4 * b ^ 2 * c ^ 2) * h2

/-- In characteristic `2`, `(u + t)^3 = u^3 + t u^2 + t^2 u + t^3`. Volume 6, Example 3.3.4 of the
handbook. -/
theorem add_pow_three_charTwo (u t : R) :
    (u + t) ^ 3 = u ^ 3 + t * u ^ 2 + t ^ 2 * u + t ^ 3 := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  linear_combination (t * u ^ 2 + t ^ 2 * u) * h2

/-- The chart identity of Example 3.3.4. In characteristic `2`, with `u_2 ↦ u_1 (u_2 + t_2)` and
`u_3 ↦ u_1 (u_3 + t_3)`, the series `f = u_1^3 + u_2^3 + u_3^3` becomes `u_1^2 (u_1 g)`, with
`g = (1 + t_2^3 + t_3^3) + t_2^2 u_2 + t_2 u_2^2 + u_2^3 + t_3^2 u_3 + t_3 u_3^2 + u_3^3`.
Volume 6, Example 3.3.4 of the handbook. -/
theorem example_3_3_4_chart (a b c s t : R) :
    a ^ 3 + (a * (b + s)) ^ 3 + (a * (c + t)) ^ 3 =
      a ^ 2 * (a * ((1 + s ^ 3 + t ^ 3) + s ^ 2 * b + s * b ^ 2 + b ^ 3 + t ^ 2 * c + t * c ^ 2 +
        c ^ 3)) := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  linear_combination (a ^ 3 * (s * b ^ 2 + s ^ 2 * b + t * c ^ 2 + t ^ 2 * c)) * h2

end CharTwo

section CharThree

variable {R : Type*} [CommRing R] [CharP R 3]

theorem three_eq_zero_of_charP : (3 : R) = 0 := by
  have h : ((3 : ℕ) : R) = 0 := CharP.cast_eq_zero R 3
  exact_mod_cast h

/-- In characteristic `3`, `3 U_1 U_2 U_3^2 + c U_1^3 U_2 = c U_1^3 U_2`. This is the derivative
`∂F/∂U_3` of Example 3.3.2. Volume 6, Example 3.3.2 of the handbook. -/
theorem example_3_3_2_derivative (c a b d : R) :
    3 * a * b * d ^ 2 + c * a ^ 3 * b = c * a ^ 3 * b := by
  linear_combination (a * b * d ^ 2) * (three_eq_zero_of_charP (R := R))

/-- The cleaning of Example 3.3.3. In characteristic `3`, for `g = -u_1 - u_1 u_2`,
`g^3 + (u_1^3 + u_1^3 u_2^3 + u_2^4 + u_3^5) = u_2^4 + u_3^5`. Volume 6, Example 3.3.3 of the
handbook. -/
theorem example_3_3_3_clean (a b c : R) :
    (-a - a * b) ^ 3 + (a ^ 3 + a ^ 3 * b ^ 3 + b ^ 4 + c ^ 5) = b ^ 4 + c ^ 5 := by
  linear_combination (-a ^ 3 * b - a ^ 3 * b ^ 2) * (three_eq_zero_of_charP (R := R))

/-- The translation of Example 3.3.3. In characteristic `3`, `X ↦ X - u_1 - u_1 u_2` sends
`X^3 + u_1^3 + u_1^3 u_2^3 + u_2^4 + u_3^5` to `X^3 + u_2^4 + u_3^5`. Volume 6, Example 3.3.3 of
the handbook. -/
theorem taylor_example_3_3_3 {k : Type*} [CommRing k] [CharP k 3] :
    taylor (-MvPowerSeries.X 0 - MvPowerSeries.X 0 * MvPowerSeries.X 1)
      (X ^ 3 + C (MvPowerSeries.X 0 ^ 3 + MvPowerSeries.X 0 ^ 3 * MvPowerSeries.X 1 ^ 3 +
        MvPowerSeries.X 1 ^ 4 + MvPowerSeries.X 2 ^ 5) : (MvPowerSeries (Fin 3) k)[X]) =
      X ^ 3 + C (MvPowerSeries.X 1 ^ 4 + MvPowerSeries.X 2 ^ 5) := by
  have h3 : (3 : MvPowerSeries (Fin 3) k) = 0 := by
    rw [← map_ofNat (MvPowerSeries.C (σ := Fin 3) (R := k)) 3, three_eq_zero_of_charP, map_zero]
  have h := taylor_X_pow_add_C 3 1 (-MvPowerSeries.X 0 - MvPowerSeries.X 0 * MvPowerSeries.X 1)
    (MvPowerSeries.X 0 ^ 3 + MvPowerSeries.X 0 ^ 3 * MvPowerSeries.X 1 ^ 3 +
      MvPowerSeries.X 1 ^ 4 + MvPowerSeries.X 2 ^ 5 : MvPowerSeries (Fin 3) k)
  simp only [pow_one] at h
  rw [h]
  congr 2
  linear_combination (-MvPowerSeries.X 0 ^ 3 * MvPowerSeries.X 1 -
    MvPowerSeries.X 0 ^ 3 * MvPowerSeries.X 1 ^ 2 : MvPowerSeries (Fin 3) k) * h3

end CharThree

/-! ### The convex combination of Example 3.3.2 -/

/-- The point `w = (1, 1/3, 1/3)` is `8/15 v_1 + 2/15 v_2 + 1/3 v_3` with `v_1 = (5/3, 0, 0)`,
`v_2 = (0, 5/3, 0)` and `v_3 = (1/3, 1/3, 1)`, and the weights add up to `1`. Volume 6,
Example 3.3.2 of the handbook. -/
theorem example_3_3_2_combination :
    (![1, 1 / 3, 1 / 3] : Fin 3 → ℚ) =
        (8 / 15 : ℚ) • ![5 / 3, 0, 0] + (2 / 15 : ℚ) • ![0, 5 / 3, 0] +
          (1 / 3 : ℚ) • ![1 / 3, 1 / 3, 1] ∧
      (8 / 15 : ℚ) + 2 / 15 + 1 / 3 = 1 := by
  refine ⟨?_, by norm_num⟩
  ext i
  fin_cases i <;> simp <;> norm_num

/-- The points `v_1, v_2, v_3, w` of Example 3.3.2 lie in the plane `x_1 + x_2 + x_3 = 5/3`.
Volume 6, Example 3.3.2 of the handbook. -/
theorem example_3_3_2_plane :
    (5 / 3 : ℚ) + 0 + 0 = 5 / 3 ∧ (0 : ℚ) + 5 / 3 + 0 = 5 / 3 ∧ (1 / 3 : ℚ) + 1 / 3 + 1 = 5 / 3 ∧
      (1 : ℚ) + 1 / 3 + 1 / 3 = 5 / 3 := by
  norm_num

end Singularity.Examples
