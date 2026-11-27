/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The blowup of the singularity `D_4`

Let `F = z^2 + xy(x + y)`. Volume 4, Example 2.3.11 of the handbook resolves `X = V(F)` in each characteristic, with the dual graph `D_4`. This file proves the algebraic steps of parts 1 and 2.

* `Singularity.dFour_singular_origin`: part 1. In a domain of any characteristic, a common zero of `F`, `F_x = y(2x + y)`, `F_y = x(x + 2y)` and `F_z = 2z` is the origin.
* `Singularity.dFour_xChart`, `Singularity.dFour_yChart` and `Singularity.dFour_zChart`: the three charts of the blowup at the origin. In the `x`-chart, `F = x^2 G` with `G = z_1^2 + x y_1 (1 + y_1)`.
* `Singularity.dFour_xChart_singular_iff`: part 2. In a domain of any characteristic, the common zeros of `G` and its partial derivatives are the two points `(0, 0, 0)` and `(0, -1, 0)`.
* `Singularity.dFour_order_z`: on `V(G)`, `z = x z_1` satisfies `z y_1 (1 + y_1) = -z_1^3`. Where `y_1 (1 + y_1)` is a unit, this gives `v_{E_0}(z) = 3`.

The identities hold in each commutative ring. The file does not prove the claims on normality, the local forms at the singular points, part 3, or the self-intersections.
-/

namespace Singularity

section Charts

variable {R : Type*} [CommRing R]

/-- The `x`-chart: `y = x y_1` and `z = x z_1` give `F = x^2 (z_1^2 + x y_1 (1 + y_1))` (Volume 4, Example 2.3.11, part 2 of the handbook). -/
theorem dFour_xChart (x y₁ z₁ : R) :
    (x * z₁) ^ 2 + x * (x * y₁) * (x + x * y₁) = x ^ 2 * (z₁ ^ 2 + x * y₁ * (1 + y₁)) := by
  ring

/-- The `y`-chart: `x = y x_1` and `z = y z_1` give `F = y^2 (z_1^2 + y x_1 (1 + x_1))` (Volume 4, Example 2.3.11, part 2 of the handbook). -/
theorem dFour_yChart (y x₁ z₁ : R) :
    (y * z₁) ^ 2 + (y * x₁) * y * (y * x₁ + y) = y ^ 2 * (z₁ ^ 2 + y * x₁ * (1 + x₁)) := by
  ring

/-- The `z`-chart: `x = z x_1` and `y = z y_1` give `F = z^2 (1 + z x_1 y_1 (x_1 + y_1))` (Volume 4, Example 2.3.11, part 2 of the handbook). -/
theorem dFour_zChart (z x₁ y₁ : R) :
    z ^ 2 + (z * x₁) * (z * y₁) * (z * x₁ + z * y₁) = z ^ 2 * (1 + z * x₁ * y₁ * (x₁ + y₁)) := by
  ring

/-- On the strict transform `V(G)` of the `x`-chart, `z = x z_1` satisfies `z y_1 (1 + y_1) = -z_1^3` (Volume 4, Example 2.3.11, part 3 of the handbook, the order `v_{E_0}(z) = 3`). -/
theorem dFour_order_z {x y₁ z₁ : R} (hG : z₁ ^ 2 + x * y₁ * (1 + y₁) = 0) :
    (x * z₁) * (y₁ * (1 + y₁)) = -z₁ ^ 3 := by
  linear_combination z₁ * hG

end Charts

section Singular

variable {R : Type*} [CommRing R] [IsDomain R]

/-- In a domain of any characteristic, the only common zero of `F = z^2 + xy(x + y)` and its partial derivatives `y(2x + y)`, `x(x + 2y)` and `2z` is the origin (Volume 4, Example 2.3.11, part 1 of the handbook). -/
theorem dFour_singular_origin {x y z : R} (hF : z ^ 2 + x * y * (x + y) = 0)
    (hx : y * (2 * x + y) = 0) (hy : x * (x + 2 * y) = 0) (hz : 2 * z = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have hxy : x = 0 ∧ y = 0 := by
    rcases mul_eq_zero.mp hx with h | h
    · subst h
      have h2 : x ^ 2 = 0 := by linear_combination hy
      exact ⟨(pow_eq_zero_iff (n := 2) (by norm_num)).mp h2, rfl⟩
    · have hy2 : y = -2 * x := by linear_combination h
      subst hy2
      have h3 : 3 * x ^ 2 = 0 := by linear_combination -hy
      rcases mul_eq_zero.mp h3 with h3 | h3
      · have h2 : (2 : R) ≠ 0 := by
          intro h2
          have h1 : (1 : R) = 0 := by linear_combination h3 - h2
          exact one_ne_zero h1
        have hz0 : z = 0 := (mul_eq_zero.mp hz).resolve_left h2
        subst hz0
        have hx3 : 2 * x ^ 3 = 0 := by linear_combination hF
        have hx0 : x = 0 :=
          (pow_eq_zero_iff (n := 3) (by norm_num)).mp ((mul_eq_zero.mp hx3).resolve_left h2)
        subst hx0
        simp
      · have hx0 : x = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h3
        subst hx0
        simp
  obtain ⟨rfl, rfl⟩ := hxy
  refine ⟨rfl, rfl, ?_⟩
  have h2 : z ^ 2 = 0 := by linear_combination hF
  exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp h2

/-- In a domain of any characteristic, the common zeros of `G = z_1^2 + x y_1 (1 + y_1)` and its partial derivatives `y_1 (1 + y_1)`, `x (1 + 2 y_1)` and `2 z_1` are the points `(0, 0, 0)` and `(0, -1, 0)` (Volume 4, Example 2.3.11, part 2 of the handbook). -/
theorem dFour_xChart_singular_iff {x y₁ z₁ : R} :
    (z₁ ^ 2 + x * y₁ * (1 + y₁) = 0 ∧ y₁ * (1 + y₁) = 0 ∧ x * (1 + 2 * y₁) = 0 ∧ 2 * z₁ = 0) ↔
      x = 0 ∧ z₁ = 0 ∧ (y₁ = 0 ∨ y₁ = -1) := by
  constructor
  · rintro ⟨hG, hx, hy, -⟩
    have hy' : y₁ = 0 ∨ y₁ = -1 := by
      rcases mul_eq_zero.mp hx with h | h
      · exact Or.inl h
      · exact Or.inr (by linear_combination h)
    have hx0 : x = 0 := by
      rcases hy' with h | h
      · subst h
        simpa using hy
      · subst h
        have h1 : -x = 0 := by linear_combination hy
        simpa using h1
    refine ⟨hx0, ?_, hy'⟩
    subst hx0
    have h2 : z₁ ^ 2 = 0 := by linear_combination hG
    exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp h2
  · rintro ⟨rfl, rfl, h | h⟩ <;> subst h <;> norm_num

end Singular

end Singularity
