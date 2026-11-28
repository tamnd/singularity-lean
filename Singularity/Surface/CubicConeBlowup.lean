/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The cone over a plane cubic, and the blowup of a point of a curve

This file proves algebraic steps of two results of Volume 4 of the handbook.

Example 2.3.14 (the cone over a plane cubic). Let `F_1 = x^3 + y^3 + z^3` and, for
characteristic `3`, let `F_2 = y^2 z - x^3 - x z^2`.

* `Singularity.cubicCone_fermat_xChart`, `Singularity.cubicCone_fermat_yChart`,
  `Singularity.cubicCone_fermat_zChart`, `Singularity.cubicCone_three_xChart`,
  `Singularity.cubicCone_three_yChart` and `Singularity.cubicCone_three_zChart`: part 3, the
  three charts of the blowup at the origin. For instance `F(x, x y_1, x z_1) = x^3 F(1, y_1, z_1)`.
* `Singularity.cubicCone_exceptional_ideal`: part 3, the ideal `(x, x y_1, x z_1)` of the
  origin in the `x`-chart is `(x)`.
* `Singularity.cubicCone_fermat_euler` and `Singularity.cubicCone_three_euler`: the Euler
  relation `x F_x + y F_y + z F_z = 3 F` of the proof of part 1.
* `Singularity.cubicCone_fermat_partials_eq_zero` and
  `Singularity.cubicCone_three_partials_eq_zero`: part 1, in a domain the partial derivatives
  have no common zero on `C` except the origin, so they have no common zero on `P^2`.
* `Singularity.cubicCone_fermat_chart_regular` and `Singularity.cubicCone_three_xChart_regular`,
  `Singularity.cubicCone_three_yChart_regular`, `Singularity.cubicCone_three_zChart_regular`:
  part 1 and part 3. On each affine chart of `C`, the equation and its two partial derivatives
  generate the unit ideal. So each affine chart of `C`, and each chart of the blowup, which is
  the product of an affine chart of `C` with a line, is regular by the Jacobian criterion.
* `Singularity.cubicCone_fermat_finrank` and `Singularity.cubicCone_fermat_zero_of_eq`: part 3,
  the degree. The scheme `C ∩ V_+(X_0)` of the Fermat cubic lies in the chart `Z ≠ 0`, and there
  it is `k[Y]/(Y^3 + 1)`, of dimension `3`.
* `Singularity.cubicCone_three_finrank_z` and `Singularity.cubicCone_three_finrank_y`: the same
  for `F_2`. Here `F_2(0, Y, Z) = Y^2 Z`, which gives `k[Y]/(Y^2)` of dimension `2` on the chart
  `Z ≠ 0` and `k[Z]/(Z)` of dimension `1` on the chart `Y ≠ 0`.
* `Singularity.cubicCone_fermat_charThree`: in characteristic `3`, `F_1 = (x + y + z)^3`.
* `Singularity.cubicCone_three_charTwo_singular`: in characteristic `2`, `F_2` and its partial
  derivatives vanish at `(1 : 0 : 1)`.

Lemma 3.1.7 (the blowup of a point of a curve on a smooth surface), parts 1, 2 and 3, the algebra.

* `Singularity.blowupCurve_chart`: part 1. If `f = ∑_{j ≤ m} a_j u^(m-j) v^j`, then the
  substitution `v = u t` gives `f = u^m ∑_{j ≤ m} a_j t^j`.
* `Singularity.blowupCurve_pow_mem_span`: part 2. If `∑_{j ≤ m} a_j t^j = 0` and `a_m` is a
  unit, then each power of `t` is an `R`-linear combination of `1, t, ..., t^(m-1)`.
* `Singularity.blowupCurve_finrank`: part 3, first claim. If `g = f_m(1, T)` has degree at most
  `m` and its coefficient of `T^m` is not `0`, then `k[T]/(g)` has dimension `m`.
* `Singularity.blowupCurve_length_count`: part 3, the count `m(m-1) - (1 + ... + (m-1)) =
  1 + ... + (m-1)`, together with `1 + ... + (m-1) = m(m-1)/2`.

Not proved. In Example 2.3.14: the cohomology `H^1(C, O_C)`, the regularity and normality of the
schemes, the gluing of the charts, the identification of the conormal sheaf with `O_C(1)`, and
part 4. In Lemma 3.1.7: the scheme statements, the inclusions `O ⊆ O' ⊆ Õ`, the lengths of the
modules, parts 4 and 5. Theorem 3.1.8 and Corollary 3.1.9 are not proved.
-/

namespace Singularity

open Polynomial

section CubicCone

variable {R : Type*} [CommRing R]

/-- The `x`-chart of the blowup of the cone over the Fermat cubic: `y = x y_1` and `z = x z_1`
give `x^3 + y^3 + z^3 = x^3 (1 + y_1^3 + z_1^3)` (Volume 4, Example 2.3.14, part 3 of the
handbook). -/
theorem cubicCone_fermat_xChart (x y₁ z₁ : R) :
    x ^ 3 + (x * y₁) ^ 3 + (x * z₁) ^ 3 = x ^ 3 * (1 + y₁ ^ 3 + z₁ ^ 3) := by
  ring

/-- The `y`-chart of the blowup of the cone over the Fermat cubic (Volume 4, Example 2.3.14,
part 3 of the handbook). -/
theorem cubicCone_fermat_yChart (y x₁ z₁ : R) :
    (y * x₁) ^ 3 + y ^ 3 + (y * z₁) ^ 3 = y ^ 3 * (x₁ ^ 3 + 1 + z₁ ^ 3) := by
  ring

/-- The `z`-chart of the blowup of the cone over the Fermat cubic (Volume 4, Example 2.3.14,
part 3 of the handbook). -/
theorem cubicCone_fermat_zChart (z x₁ y₁ : R) :
    (z * x₁) ^ 3 + (z * y₁) ^ 3 + z ^ 3 = z ^ 3 * (x₁ ^ 3 + y₁ ^ 3 + 1) := by
  ring

/-- The `x`-chart of the blowup of the cone over `y^2 z - x^3 - x z^2` (Volume 4,
Example 2.3.14, part 3 of the handbook). -/
theorem cubicCone_three_xChart (x y₁ z₁ : R) :
    (x * y₁) ^ 2 * (x * z₁) - x ^ 3 - x * (x * z₁) ^ 2 = x ^ 3 * (y₁ ^ 2 * z₁ - 1 - z₁ ^ 2) := by
  ring

/-- The `y`-chart of the blowup of the cone over `y^2 z - x^3 - x z^2` (Volume 4,
Example 2.3.14, part 3 of the handbook). -/
theorem cubicCone_three_yChart (y x₁ z₁ : R) :
    y ^ 2 * (y * z₁) - (y * x₁) ^ 3 - (y * x₁) * (y * z₁) ^ 2 =
      y ^ 3 * (z₁ - x₁ ^ 3 - x₁ * z₁ ^ 2) := by
  ring

/-- The `z`-chart of the blowup of the cone over `y^2 z - x^3 - x z^2` (Volume 4,
Example 2.3.14, part 3 of the handbook). -/
theorem cubicCone_three_zChart (z x₁ y₁ : R) :
    (z * y₁) ^ 2 * z - (z * x₁) ^ 3 - (z * x₁) * z ^ 2 = z ^ 3 * (y₁ ^ 2 - x₁ ^ 3 - x₁) := by
  ring

/-- The ideal of the origin in the `x`-chart is `(x, x y_1, x z_1) = (x)`. So the exceptional
curve is `V(x)` there (Volume 4, Example 2.3.14, part 3 of the handbook). -/
theorem cubicCone_exceptional_ideal (x y₁ z₁ : R) :
    Ideal.span {x, x * y₁, x * z₁} = Ideal.span {x} := by
  apply le_antisymm
  · rw [Ideal.span_le]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact Ideal.subset_span rfl
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · exact Ideal.span_mono (by simp)

/-- The Euler relation `x F_x + y F_y + z F_z = 3 F` for `F = x^3 + y^3 + z^3` (Volume 4,
Example 2.3.14, part 1 of the handbook). -/
theorem cubicCone_fermat_euler (x y z : R) :
    x * (3 * x ^ 2) + y * (3 * y ^ 2) + z * (3 * z ^ 2) = 3 * (x ^ 3 + y ^ 3 + z ^ 3) := by
  ring

/-- The Euler relation `x F_x + y F_y + z F_z = 3 F` for `F = y^2 z - x^3 - x z^2`, with
`F_x = -3 x^2 - z^2`, `F_y = 2 y z` and `F_z = y^2 - 2 x z` (Volume 4, Example 2.3.14, part 1 of
the handbook). -/
theorem cubicCone_three_euler (x y z : R) :
    x * (-3 * x ^ 2 - z ^ 2) + y * (2 * y * z) + z * (y ^ 2 - 2 * x * z) =
      3 * (y ^ 2 * z - x ^ 3 - x * z ^ 2) := by
  ring

/-- In a domain with `3 ≠ 0`, the partial derivatives `3 x^2`, `3 y^2`, `3 z^2` of
`x^3 + y^3 + z^3` vanish only at the origin (Volume 4, Example 2.3.14, part 1 of the
handbook). -/
theorem cubicCone_fermat_partials_eq_zero [IsDomain R] (h3 : (3 : R) ≠ 0) {x y z : R}
    (hx : 3 * x ^ 2 = 0) (hy : 3 * y ^ 2 = 0) (hz : 3 * z ^ 2 = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  simp only [mul_eq_zero, h3, false_or, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true] at hx hy hz
  exact ⟨hx, hy, hz⟩

/-- In a domain of characteristic `3`, a common zero of `F = y^2 z - x^3 - x z^2` and of its
partial derivatives `-3 x^2 - z^2`, `2 y z`, `y^2 - 2 x z` is the origin (Volume 4,
Example 2.3.14, part 1 of the handbook). The derivative `2 y z` is not needed. -/
theorem cubicCone_three_partials_eq_zero [IsDomain R] (h3 : (3 : R) = 0) {x y z : R}
    (hF : y ^ 2 * z - x ^ 3 - x * z ^ 2 = 0) (hx : -3 * x ^ 2 - z ^ 2 = 0)
    (hz : y ^ 2 - 2 * x * z = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have hz2 : z ^ 2 = 0 := by linear_combination -hx - x ^ 2 * h3
  have hz0 : z = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hz2
  subst hz0
  have hy0 : y = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp (by linear_combination hz)
  subst hy0
  have hx0 : x = 0 := pow_eq_zero_iff (three_ne_zero) |>.mp (by linear_combination -hF)
  exact ⟨hx0, rfl, rfl⟩

/-- If `r a + s b + t c = 1`, then `(a, b, c)` is the unit ideal. -/
theorem cubicCone_span_three_eq_top {a b c r s t : R} (h : r * a + s * b + t * c = 1) :
    Ideal.span {a, b, c} = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← h]
  refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_ <;>
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

/-- If `3` is a unit, then `1 + a^3 + b^3` and its partial derivatives `3 a^2`, `3 b^2` generate
the unit ideal. This covers the three affine charts of the Fermat cubic, and the three charts
of the blowup of its cone (Volume 4, Example 2.3.14, parts 1 and 3 of the handbook). -/
theorem cubicCone_fermat_chart_regular {u : R} (hu : 3 * u = 1) (a b : R) :
    Ideal.span {1 + a ^ 3 + b ^ 3, 3 * a ^ 2, 3 * b ^ 2} = ⊤ :=
  cubicCone_span_three_eq_top (r := 1) (s := -u * a) (t := -u * b) (by
    linear_combination (-(a ^ 3 + b ^ 3)) * hu)

/-- In characteristic `3`, `y^2 z - 1 - z^2` and its partial derivatives `2 y z`, `y^2 - 2 z`
generate the unit ideal. This is the chart `X ≠ 0` of `C` (Volume 4, Example 2.3.14, parts 1
and 3 of the handbook). -/
theorem cubicCone_three_xChart_regular (h3 : (3 : R) = 0) (y z : R) :
    Ideal.span {y ^ 2 * z - 1 - z ^ 2, 2 * y * z, y ^ 2 - 2 * z} = ⊤ :=
  cubicCone_span_three_eq_top (r := -1) (s := y) (t := 2 * z) (by
    linear_combination (y ^ 2 * z - z ^ 2) * h3)

/-- In characteristic `3`, `z - x^3 - x z^2` and its partial derivatives `-3 x^2 - z^2`,
`1 - 2 x z` generate the unit ideal. This is the chart `Y ≠ 0` of `C` (Volume 4,
Example 2.3.14, parts 1 and 3 of the handbook). -/
theorem cubicCone_three_yChart_regular (h3 : (3 : R) = 0) (x z : R) :
    Ideal.span {z - x ^ 3 - x * z ^ 2, -3 * x ^ 2 - z ^ 2, 1 - 2 * x * z} = ⊤ :=
  cubicCone_span_three_eq_top (r := 0) (s := -4 * x ^ 2) (t := 1 + 2 * x * z) (by
    linear_combination (4 * x ^ 4) * h3)

/-- In characteristic `3`, `y^2 - x^3 - x` and its partial derivatives `-3 x^2 - 1`, `2 y`
generate the unit ideal. This is the chart `Z ≠ 0` of `C` (Volume 4, Example 2.3.14, parts 1
and 3 of the handbook). -/
theorem cubicCone_three_zChart_regular (h3 : (3 : R) = 0) (x y : R) :
    Ideal.span {y ^ 2 - x ^ 3 - x, -3 * x ^ 2 - 1, 2 * y} = ⊤ :=
  cubicCone_span_three_eq_top (r := 0) (s := -1) (t := 0) (by
    linear_combination x ^ 2 * h3)

/-- In characteristic `3`, the Fermat cubic is a cube: `x^3 + y^3 + z^3 = (x + y + z)^3`. So its
cone is not reduced (Volume 4, the remark after Example 2.3.14 of the handbook). -/
theorem cubicCone_fermat_charThree (h3 : (3 : R) = 0) (x y z : R) :
    x ^ 3 + y ^ 3 + z ^ 3 = (x + y + z) ^ 3 := by
  linear_combination (-(x ^ 2 * y + x ^ 2 * z + y ^ 2 * x + y ^ 2 * z + z ^ 2 * x + z ^ 2 * y
    + 2 * x * y * z)) * h3

/-- In characteristic `2`, the cubic `y^2 z - x^3 - x z^2` and its partial derivatives vanish at
`(1 : 0 : 1)`. So this curve is singular in characteristic `2` (Volume 4, the remark after
Example 2.3.14 of the handbook). -/
theorem cubicCone_three_charTwo_singular (h2 : (2 : R) = 0) :
    (0 : R) ^ 2 * 1 - 1 ^ 3 - 1 * 1 ^ 2 = 0 ∧ -3 * (1 : R) ^ 2 - 1 ^ 2 = 0 ∧
      2 * (0 : R) * 1 = 0 ∧ (0 : R) ^ 2 - 2 * 1 * 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination -h2
  · linear_combination -2 * h2
  · ring
  · linear_combination -h2

/-- In a domain, a point of `C ∩ V_+(X_0)` for the Fermat cubic has `Z ≠ 0`: if
`Y^3 + Z^3 = 0` and `Z = 0`, then `Y = 0` (Volume 4, Example 2.3.14, part 3 of the
handbook). -/
theorem cubicCone_fermat_zero_of_eq [IsDomain R] {y : R} (h : y ^ 3 + 0 ^ 3 = 0) : y = 0 :=
  pow_eq_zero_iff three_ne_zero |>.mp (by simpa using h)

end CubicCone

section BlowupCurve

open Finset

variable {R : Type*} [CommRing R]

/-- Let `f = ∑_{j ≤ m} a_j u^(m-j) v^j`. The substitution `v = u t` gives
`f = u^m ∑_{j ≤ m} a_j t^j`, that is, `f = u^m f'` (Volume 4, Lemma 3.1.7, part 1 of the
handbook). -/
theorem blowupCurve_chart (m : ℕ) (a : ℕ → R) (u t : R) :
    ∑ j ∈ range (m + 1), a j * u ^ (m - j) * (u * t) ^ j =
      u ^ m * ∑ j ∈ range (m + 1), a j * t ^ j := by
  rw [mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [mul_pow, ← pow_sub_mul_pow u hjm]
  ring

/-- Let `t` be an element of an `R`-algebra `A` with `∑_{j ≤ m} a_j t^j = 0`, and let `a_m` be a
unit of `R`. Then each power of `t` lies in the `R`-span of `1, t, ..., t^(m-1)`. This is the
claim that `O' = B/(f')` is generated by `1, t, ..., t^(m-1)` (Volume 4, Lemma 3.1.7, part 2 of
the handbook). -/
theorem blowupCurve_pow_mem_span {A : Type*} [CommRing A] [Algebra R A] (m : ℕ) (a : ℕ → R)
    {b : R} (hb : a m * b = 1) {t : A} (ht : ∑ j ∈ range (m + 1), a j • t ^ j = 0) (n : ℕ) :
    t ^ n ∈ Submodule.span R ((t ^ ·) '' Set.Iio m) := by
  have key : t ^ m = -(b • ∑ j ∈ range m, a j • t ^ j) := by
    rw [sum_range_succ] at ht
    have h1 : a m • t ^ m = -∑ j ∈ range m, a j • t ^ j := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact ht
    calc t ^ m = (b * a m) • t ^ m := by rw [mul_comm, hb, one_smul]
      _ = b • (a m • t ^ m) := mul_smul _ _ _
      _ = -(b • ∑ j ∈ range m, a j • t ^ j) := by rw [h1, smul_neg]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < m
    · exact Submodule.subset_span ⟨n, hn, rfl⟩
    · have hmn : m ≤ n := not_lt.mp hn
      have e : t ^ n = -(b • ∑ j ∈ range m, a j • t ^ (n - m + j)) := by
        rw [← pow_sub_mul_pow t hmn, key, mul_neg, mul_smul_comm, mul_sum]
        simp_rw [mul_smul_comm, ← pow_add]
      rw [e]
      refine Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j hj => ?_))
      exact Submodule.smul_mem _ _ (ih _ (by have := mem_range.mp hj; omega))

/-- Let `k` be a field and let `g ∈ k[T]` have degree at most `m`, with a nonzero coefficient of
`T^m`. Then `k[T]/(g)` has dimension `m` over `k`. For `g = f_m(1, T)` this is
`ℓ(O'/u O') = m` (Volume 4, Lemma 3.1.7, part 3 of the handbook). -/
theorem blowupCurve_finrank {k : Type*} [Field k] {g : k[X]} {m : ℕ} (hg : g.natDegree ≤ m)
    (hm : g.coeff m ≠ 0) : Module.finrank k (AdjoinRoot g) = m := by
  have hdeg : g.natDegree = m := natDegree_eq_of_le_of_coeff_ne_zero hg hm
  have hg0 : g ≠ 0 := fun h => hm (by simp [h])
  rw [(AdjoinRoot.powerBasis hg0).finrank, AdjoinRoot.powerBasis_dim, hdeg]

/-- The count of lengths in Lemma 3.1.7, part 3. With `s = 1 + ... + (m-1)`, we have
`(m - 1) m - s = s` and `2 s = m (m - 1)` (Volume 4, Lemma 3.1.7, part 3 of the handbook). -/
theorem blowupCurve_length_count (m : ℕ) :
    (m - 1) * m - ∑ i ∈ range m, i = ∑ i ∈ range m, i ∧
      (∑ i ∈ range m, i) * 2 = m * (m - 1) := by
  have h := sum_range_id_mul_two m
  refine ⟨?_, h⟩
  rw [Nat.mul_comm (m - 1) m]
  omega

end BlowupCurve

section CubicConeDegree

variable {k : Type*} [Field k]

/-- On the chart `Z ≠ 0`, the scheme `C ∩ V_+(X_0)` of the Fermat cubic is `k[Y]/(Y^3 + 1)`, of
dimension `3`. So `O_C(1)` has degree `3` (Volume 4, Example 2.3.14, part 3 of the
handbook). -/
theorem cubicCone_fermat_finrank :
    Module.finrank k (AdjoinRoot (X ^ 3 + 1 : k[X])) = 3 :=
  blowupCurve_finrank (by compute_degree) (by simp [coeff_one])

/-- On the chart `Z ≠ 0`, the scheme `C ∩ V_+(X_0)` of `y^2 z - x^3 - x z^2` is `k[Y]/(Y^2)`, of
dimension `2` (Volume 4, Example 2.3.14, part 3 of the handbook). -/
theorem cubicCone_three_finrank_z :
    Module.finrank k (AdjoinRoot (X ^ 2 : k[X])) = 2 :=
  blowupCurve_finrank (by compute_degree) (by simp)

/-- On the chart `Y ≠ 0`, the scheme `C ∩ V_+(X_0)` of `y^2 z - x^3 - x z^2` is `k[Z]/(Z)`, of
dimension `1`. Together with `Singularity.cubicCone_three_finrank_z`, the degree is
`2 + 1 = 3`, since the two points `(0 : 0 : 1)` and `(0 : 1 : 0)` lie in one chart each
(Volume 4, Example 2.3.14, part 3 of the handbook). -/
theorem cubicCone_three_finrank_y :
    Module.finrank k (AdjoinRoot (X : k[X])) = 1 :=
  blowupCurve_finrank (by compute_degree) (by simp)

end CubicConeDegree

end Singularity
