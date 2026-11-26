/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic.Ring

/-!
# The Whitney umbrella `x^2 = y^2 z`

Let `F = x^2 - y^2 z`. This file proves the algebraic identities of two statements of Volume 4 of the handbook on the Whitney umbrella `X = V(F)`.

Example 1.2.7, part 2: the normalization is `ν : A^2 = Spec k[s, t] → X` with `x ↦ st`, `y ↦ s`, `z ↦ t^2`.

* `Singularity.whitneyNormalization` is the map of `k`-algebras `k[x, y, z] → k[s, t]`, and `Singularity.whitneyNormalization_equation` shows that it sends `F` to `0`.
* `Singularity.whitneyNormalization_X1_mul` and `Singularity.whitneyNormalization_X1_sq`: `t ν(y) = ν(x)` and `t^2 = ν(z)`. Thus `t = x/y` in the function field, and `t` is integral over the image of `ν`.
* `Singularity.whitney_exists_eq_add_mul`: each element of `k[s, t]` is `ν(a) + ν(b) t`. This is `C = A' + A' t` in the proof of the handbook, so `k[s, t]` is a finite module over the image `A'`.

Example 3.1.6, parts 2 and 3: the charts of the blowups of `A^3`.

* `Singularity.whitney_lineChart_x` and `Singularity.whitney_lineChart_y`: the two charts of the blowup along the line `L = V(x, y)`. With `x = y x_2` we get `F = y^2 (x_2^2 - z)`, and with `y = x y_3` we get `F = x^2 (1 - y_3^2 z)`.
* `Singularity.whitney_pointChart_z`: the `z`-chart of the blowup at the origin. With `x = z x_1` and `y = z y_1` we get `F = z^2 (x_1^2 - y_1^2 z)`, which is the same equation as `F`.

The file does not prove that `ν` is injective or that it is the normalization, and it does not prove the claims on regularity and normal crossings.
-/

open MvPolynomial

namespace Singularity

section Normalization

variable (k : Type*) [CommRing k]

/-- The map of `k`-algebras `k[x, y, z] → k[s, t]` with `x ↦ st`, `y ↦ s` and `z ↦ t^2` of Volume 4, Example 1.2.7, part 2 of the handbook. The variables `x, y, z` are `X 0, X 1, X 2`, and `s, t` are `X 0, X 1`. -/
noncomputable def whitneyNormalization : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 2) k :=
  aeval ![X 0 * X 1, X 0, X 1 ^ 2]

variable {k}

theorem whitneyNormalization_X0 : whitneyNormalization k (X 0) = X 0 * X 1 := by
  simp [whitneyNormalization]

theorem whitneyNormalization_X1 : whitneyNormalization k (X 1) = X 0 := by
  simp [whitneyNormalization]

theorem whitneyNormalization_X2 : whitneyNormalization k (X 2) = X 1 ^ 2 := by
  simp [whitneyNormalization]

/-- The map `ν` sends `x^2 - y^2 z` to `0`, so it is defined on the ring of the Whitney umbrella (Volume 4, Example 1.2.7, part 2 of the handbook). -/
theorem whitneyNormalization_equation :
    whitneyNormalization k (X 0 ^ 2 - X 1 ^ 2 * X 2) = 0 := by
  rw [map_sub, map_mul, map_pow, map_pow, whitneyNormalization_X0, whitneyNormalization_X1,
    whitneyNormalization_X2]
  ring

/-- `t ν(y) = ν(x)`, so `t = x/y` in the function field (Volume 4, Example 1.2.7, part 2 of the handbook). -/
theorem whitneyNormalization_X1_mul :
    X 1 * whitneyNormalization k (X 1) = whitneyNormalization k (X 0) := by
  rw [whitneyNormalization_X0, whitneyNormalization_X1]
  ring

/-- `t^2 = ν(z)`, so `t` is integral over the image of `ν` (Volume 4, Example 1.2.7, part 2 of the handbook). -/
theorem whitneyNormalization_X1_sq :
    (X 1 : MvPolynomial (Fin 2) k) ^ 2 = whitneyNormalization k (X 2) :=
  whitneyNormalization_X2.symm

/-- Each element of `k[s, t]` has the form `ν(a) + ν(b) t`. Thus `k[s, t] = A' + A' t` with `A'` the image of `ν` (Volume 4, Example 1.2.7, part 2 of the handbook). -/
theorem whitney_exists_eq_add_mul (g : MvPolynomial (Fin 2) k) :
    ∃ a b : MvPolynomial (Fin 3) k,
      g = whitneyNormalization k a + whitneyNormalization k b * X 1 := by
  induction g using MvPolynomial.induction_on with
  | C c => exact ⟨C c, 0, by simp [whitneyNormalization]⟩
  | add f g hf hg =>
    obtain ⟨a, b, rfl⟩ := hf
    obtain ⟨a', b', rfl⟩ := hg
    exact ⟨a + a', b + b', by rw [map_add, map_add]; ring⟩
  | mul_X f i hf =>
    obtain ⟨a, b, rfl⟩ := hf
    revert i
    rw [Fin.forall_fin_two]
    refine ⟨⟨a * X 1, b * X 1, ?_⟩, ⟨b * X 2, a, ?_⟩⟩ <;>
      simp only [map_mul, whitneyNormalization_X1, whitneyNormalization_X2] <;>
      ring

end Normalization

section Charts

variable {R : Type*} [CommRing R]

/-- The chart `x = y x_2` of the blowup of `A^3` along the line `V(x, y)`: `F = y^2 (x_2^2 - z)` (Volume 4, Example 3.1.6, part 2 of the handbook). -/
theorem whitney_lineChart_x (x₂ y z : R) :
    (y * x₂) ^ 2 - y ^ 2 * z = y ^ 2 * (x₂ ^ 2 - z) := by
  ring

/-- The chart `y = x y_3` of the blowup of `A^3` along the line `V(x, y)`: `F = x^2 (1 - y_3^2 z)` (Volume 4, Example 3.1.6, part 2 of the handbook). -/
theorem whitney_lineChart_y (x y₃ z : R) :
    x ^ 2 - (x * y₃) ^ 2 * z = x ^ 2 * (1 - y₃ ^ 2 * z) := by
  ring

/-- The `z`-chart of the blowup of `A^3` at the origin: `F = z^2 (x_1^2 - y_1^2 z)`, the same equation as `F` (Volume 4, Example 3.1.6, part 3 of the handbook). -/
theorem whitney_pointChart_z (x₁ y₁ z : R) :
    (z * x₁) ^ 2 - (z * y₁) ^ 2 * z = z ^ 2 * (x₁ ^ 2 - y₁ ^ 2 * z) := by
  ring

end Charts

end Singularity
