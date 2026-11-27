/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.Residual
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The blowup of the quadric cone

This file proves the chart computation of Volume 4, Example 3.1.5 of the handbook. Let `k` be a commutative ring and let `F = xy - z^2` in `k[x, y, z]`. The blowup of the origin has three charts, and `pointChart j 0` is the `x_j`-chart.

* In the `x`-chart, `F` goes to `x^2 (y_1 - z_1^2)`, and the change of coordinates `y_2 = y_1 - z_1^2` is an automorphism of `k[x, y_1, z_1]`. So the exceptional divisor `V(x)` and the strict transform `V(y_2)` are two coordinate hyperplanes.
* The `y`-chart is the same, with `x` and `y` exchanged.
* In the `z`-chart, `F` goes to `z^2 (x_1 y_1 - 1)`. The identity `x_1 ∂g/∂x_1 - g = 1` for `g = x_1 y_1 - 1` shows that `∂g/∂x_1` is a unit modulo `g`, and `∂g/∂z = 0`. So the Jacobian matrix of `(g, z)` has rank 2 at each point of `V(g)`.

* `Singularity.quadricCone`: the polynomial `xy - z^2`.
* `Singularity.pointChart_quadricCone_x`, `Singularity.pointChart_quadricCone_y` and `Singularity.pointChart_quadricCone_z`: the three charts.
* `Singularity.quadricConeShift`: the automorphism `y ↦ y - z^2` of `k[x, y, z]`.
* `Singularity.quadricConeShift_strictTransform`: it sends `y_1 - z_1^2` to `y_1`.
* `Singularity.jacobian_quadricCone_zChart`: the Jacobian identity in the `z`-chart.

The file does not prove that the local rings of the blowup are regular, and it does not build the blowup as a scheme. It does the algebra of the charts.
-/

namespace Singularity

open MvPolynomial

section QuadricCone

variable (k : Type*) [CommRing k]

/-- The quadric cone `xy - z^2` in `k[x, y, z]`, with `x = X 0`, `y = X 1` and `z = X 2`. -/
noncomputable def quadricCone : MvPolynomial (Fin 3) k := X 0 * X 1 - X 2 ^ 2

/-- The `x`-chart of the blowup of the origin sends `xy - z^2` to `x^2 (y_1 - z_1^2)`. -/
theorem pointChart_quadricCone_x :
    pointChart (0 : Fin 3) (0 : Fin 3 → k) (quadricCone k) = X 0 ^ 2 * (X 1 - X 2 ^ 2) := by
  simp only [quadricCone, map_sub, map_mul, map_pow, pointChart_X_self,
    pointChart_X_of_ne (0 : Fin 3 → k) (show (1 : Fin 3) ≠ 0 by decide),
    pointChart_X_of_ne (0 : Fin 3 → k) (show (2 : Fin 3) ≠ 0 by decide), Pi.zero_apply, map_zero,
    add_zero]
  ring

/-- The `y`-chart of the blowup of the origin sends `xy - z^2` to `y^2 (x_1 - z_1^2)`. -/
theorem pointChart_quadricCone_y :
    pointChart (1 : Fin 3) (0 : Fin 3 → k) (quadricCone k) = X 1 ^ 2 * (X 0 - X 2 ^ 2) := by
  simp only [quadricCone, map_sub, map_mul, map_pow, pointChart_X_self,
    pointChart_X_of_ne (0 : Fin 3 → k) (show (0 : Fin 3) ≠ 1 by decide),
    pointChart_X_of_ne (0 : Fin 3 → k) (show (2 : Fin 3) ≠ 1 by decide), Pi.zero_apply, map_zero,
    add_zero]
  ring

/-- The `z`-chart of the blowup of the origin sends `xy - z^2` to `z^2 (x_1 y_1 - 1)`. -/
theorem pointChart_quadricCone_z :
    pointChart (2 : Fin 3) (0 : Fin 3 → k) (quadricCone k) = X 2 ^ 2 * (X 0 * X 1 - 1) := by
  simp only [quadricCone, map_sub, map_mul, map_pow, pointChart_X_self,
    pointChart_X_of_ne (0 : Fin 3 → k) (show (0 : Fin 3) ≠ 2 by decide),
    pointChart_X_of_ne (0 : Fin 3 → k) (show (1 : Fin 3) ≠ 2 by decide), Pi.zero_apply, map_zero,
    add_zero]
  ring

/-- The map `y ↦ y + c z^2`, with `x` and `z` fixed. -/
noncomputable def quadricConeShiftHom (c : k) :
    MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 3) k :=
  aeval fun i => if i = 1 then X 1 + C c * X 2 ^ 2 else X i

theorem quadricConeShiftHom_X (c : k) (i : Fin 3) :
    quadricConeShiftHom k c (X i) = if i = 1 then X 1 + C c * X 2 ^ 2 else X i := by
  simp [quadricConeShiftHom]

theorem quadricConeShiftHom_comp (c d : k) :
    (quadricConeShiftHom k c).comp (quadricConeShiftHom k d) = quadricConeShiftHom k (c + d) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, quadricConeShiftHom_X, quadricConeShiftHom_X]
  fin_cases i <;> simp [quadricConeShiftHom_X, map_add, map_mul, map_pow]
  ring

theorem quadricConeShiftHom_zero : quadricConeShiftHom k 0 = AlgHom.id k _ := by
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;> simp [quadricConeShiftHom_X]

/-- The automorphism `y ↦ y - z^2` of `k[x, y, z]`, with `x` and `z` fixed. Its inverse is
`y ↦ y + z^2`. -/
noncomputable def quadricConeShift : MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k :=
  AlgEquiv.ofAlgHom (quadricConeShiftHom k (-1)) (quadricConeShiftHom k 1)
    (by rw [quadricConeShiftHom_comp, neg_add_cancel, quadricConeShiftHom_zero])
    (by rw [quadricConeShiftHom_comp, add_neg_cancel, quadricConeShiftHom_zero])

theorem quadricConeShift_X_zero : quadricConeShift k (X 0) = X 0 := by
  simp [quadricConeShift, quadricConeShiftHom_X]

theorem quadricConeShift_X_two : quadricConeShift k (X 2) = X 2 := by
  simp [quadricConeShift, quadricConeShiftHom_X]

/-- The automorphism sends `y_1` to `y_1 - z_1^2`. So in the `x`-chart the strict transform
`V(y_1 - z_1^2)` and the exceptional divisor `V(x)` are the coordinate hyperplanes `V(y_2)` and
`V(x)` of the coordinates `x, y_2 = y_1 - z_1^2, z_1`. -/
theorem quadricConeShift_strictTransform :
    quadricConeShift k (X 1) = X 1 - X 2 ^ 2 := by
  simp [quadricConeShift, quadricConeShiftHom_X, sub_eq_add_neg]

/-- In the `z`-chart, with `g = x_1 y_1 - 1`, the identity `x_1 ∂g/∂x_1 - g = 1` holds, and
`∂g/∂z = 0`. So `∂g/∂x_1` is a unit modulo `g`, and the Jacobian matrix of `(g, z)` has rank 2 at
each point of `V(g)`. -/
theorem jacobian_quadricCone_zChart :
    X 0 * pderiv 0 (X 0 * X 1 - 1 : MvPolynomial (Fin 3) k) - (X 0 * X 1 - 1) = 1 ∧
      pderiv 2 (X 0 * X 1 - 1 : MvPolynomial (Fin 3) k) = 0 := by
  constructor
  · simp [pderiv_X]
  · simp [pderiv_X]

end QuadricCone

end Singularity
