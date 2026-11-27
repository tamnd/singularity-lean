/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The charts of the blowup of the plane and of the cone

This file proves the computations of Volume 1, Examples 1.10.7 and 1.10.8 of the handbook. All the statements hold in each commutative ring, so they hold in the charts of the handbook.

Example 1.10.7, the blowup of the plane at the origin.

* `Singularity.Example.cusp_chart_x` and `Singularity.Example.cusp_chart_y`: for the cusp `f = y^2 - x^3`, `f(x, xu) = x^2 (u^2 - x)` and `f(yw, y) = y^2 (1 - y w^3)`.
* `Singularity.Example.cusp_strict_inter`: the strict transform `u^2 - x` meets the exceptional divisor `x = 0` in the ideal `(x, u^2)`, a point of length 2.
* `Singularity.Example.cusp_strict_inter_y`: in the other chart, the ideal `(y, 1 - y w^3)` is the unit ideal, so the strict transform does not meet the exceptional divisor.
* `Singularity.Example.node_chart_x` and `Singularity.Example.node_strict_inter`: for the node `f = y^2 - x^2 - x^3`, `f(x, xu) = x^2 (u^2 - 1 - x)`, and the strict transform meets `x = 0` in the ideal `(x, (u - 1)(u + 1))`.

Example 1.10.8, the blowup of the cone `xy = z^2` at its vertex.

* `Singularity.Example.cone_chart_x`: let `x ≠ 0` in a domain with `xy = z^2` and `z = xv`. Then `y = x v^2`, and `(x, y, z) = (x)`.
* `Singularity.Example.cone_chart_z`: let `z ≠ 0` in a domain with `xy = z^2`, `x = za` and `y = zb`. Then `ab = 1`.
* `Singularity.Example.cone_overlap`: let `xy ≠ 0` in a domain with `xy = z^2`, `z = xv` and `z = yw`. Then `vw = 1`.

The handbook also proves that the charts are polynomial rings and that the blowups are regular. This file does not prove these claims.
-/

namespace Singularity.Example

variable {R : Type*} [CommRing R]

/-- The cusp in the chart for `x` (Volume 1, Example 1.10.7 of the handbook): `f(x, xu) = x^2 (u^2 - x)` for `f = y^2 - x^3`. -/
theorem cusp_chart_x (x u : R) : (x * u) ^ 2 - x ^ 3 = x ^ 2 * (u ^ 2 - x) := by ring

/-- The cusp in the chart for `y` (Volume 1, Example 1.10.7 of the handbook): `f(yw, y) = y^2 (1 - y w^3)` for `f = y^2 - x^3`. -/
theorem cusp_chart_y (y w : R) : y ^ 2 - (y * w) ^ 3 = y ^ 2 * (1 - y * w ^ 3) := by ring

/-- The strict transform `u^2 - x` of the cusp meets the exceptional divisor `x = 0` in `Spec R[u]/(u^2)` (Volume 1, Example 1.10.7 of the handbook): `(x, u^2 - x) = (x, u^2)`. -/
theorem cusp_strict_inter (x u : R) :
    Ideal.span {x, u ^ 2 - x} = Ideal.span {x, u ^ 2} := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact Ideal.subset_span (by simp)
    · exact Ideal.mem_span_pair.mpr ⟨-1, 1, by ring⟩
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact Ideal.subset_span (by simp)
    · exact Ideal.mem_span_pair.mpr ⟨1, 1, by ring⟩

/-- In the chart for `y`, the strict transform `1 - y w^3` of the cusp does not meet the exceptional divisor `y = 0` (Volume 1, Example 1.10.7 of the handbook): `(y, 1 - y w^3)` is the unit ideal. -/
theorem cusp_strict_inter_y (y w : R) : Ideal.span {y, 1 - y * w ^ 3} = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  exact Ideal.mem_span_pair.mpr ⟨w ^ 3, 1, by ring⟩

/-- The node in the chart for `x` (Volume 1, Example 1.10.7 of the handbook): `f(x, xu) = x^2 (u^2 - 1 - x)` for `f = y^2 - x^2 - x^3`. -/
theorem node_chart_x (x u : R) :
    (x * u) ^ 2 - x ^ 2 - x ^ 3 = x ^ 2 * (u ^ 2 - 1 - x) := by ring

/-- The strict transform `u^2 - 1 - x` of the node meets the exceptional divisor `x = 0` at the roots of `(u - 1)(u + 1)` (Volume 1, Example 1.10.7 of the handbook): `(x, u^2 - 1 - x) = (x, (u - 1)(u + 1))`. -/
theorem node_strict_inter (x u : R) :
    Ideal.span {x, u ^ 2 - 1 - x} = Ideal.span {x, (u - 1) * (u + 1)} := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact Ideal.subset_span (by simp)
    · exact Ideal.mem_span_pair.mpr ⟨-1, 1, by ring⟩
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact Ideal.subset_span (by simp)
    · exact Ideal.mem_span_pair.mpr ⟨1, 1, by ring⟩

variable [IsDomain R]

/-- The chart for `x` of the blowup of the cone (Volume 1, Example 1.10.8 of the handbook). Let `x ≠ 0`, `xy = z^2` and `z = xv`. Then `y = x v^2`, and the ideal `(x, y, z)` is `(x)`. -/
theorem cone_chart_x {x y z v : R} (hx : x ≠ 0) (hxy : x * y = z ^ 2) (hz : z = x * v) :
    y = x * v ^ 2 ∧ Ideal.span {x, y, z} = Ideal.span {x} := by
  have hy : y = x * v ^ 2 := by
    refine mul_left_cancel₀ hx ?_
    rw [hxy, hz]
    ring
  refine ⟨hy, le_antisymm ?_ (Ideal.span_mono (by simp))⟩
  rw [Ideal.span_le]
  rintro _ (rfl | rfl | rfl)
  · exact Ideal.subset_span (Set.mem_singleton _)
  · rw [hy]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  · rw [hz]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))

/-- The chart for `z` of the blowup of the cone (Volume 1, Example 1.10.8 of the handbook). Let `z ≠ 0`, `xy = z^2`, `x = za` and `y = zb`. Then `ab = 1`. -/
theorem cone_chart_z {x y z a b : R} (hz : z ≠ 0) (hxy : x * y = z ^ 2) (ha : x = z * a)
    (hb : y = z * b) : a * b = 1 := by
  have h : z ^ 2 * (a * b) = z ^ 2 * 1 := by
    calc z ^ 2 * (a * b) = (z * a) * (z * b) := by ring
      _ = x * y := by rw [ha, hb]
      _ = z ^ 2 * 1 := by rw [hxy, mul_one]
  exact mul_left_cancel₀ (pow_ne_zero 2 hz) h

/-- The overlap of the charts for `x` and `y` of the blowup of the cone (Volume 1, Example 1.10.8 of the handbook). Let `xy ≠ 0`, `xy = z^2`, `z = xv` and `z = yw`. Then `vw = 1`, so the exceptional divisor is glued from `Spec k[v]` and `Spec k[w]` along `vw = 1`. -/
theorem cone_overlap {x y z v w : R} (hxy0 : x * y ≠ 0) (hxy : x * y = z ^ 2) (hv : z = x * v)
    (hw : z = y * w) : v * w = 1 := by
  have h : x * y * (v * w) = x * y * 1 := by
    have : x * y * (v * w) = (x * v) * (y * w) := by ring
    rw [this, ← hv, ← hw, mul_one, hxy]
    ring
  exact mul_left_cancel₀ hxy0 h

end Singularity.Example
