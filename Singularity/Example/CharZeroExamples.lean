/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.DerivativeOrder

/-!
# Explicit examples of Volume 2 of the handbook

This file checks the algebraic computations of five examples of Volume 2 of the handbook. The derivative ideal is `Singularity.derivIdeal` and the order at the origin is `Singularity.ord` and `Singularity.idealOrd`.

1. Example 1.2.2. For `I = (x^3 - y^2, x^4 + x z^2 - w^3)`, the chart `y = x_1 y_1`, `z = x_1 z_1`, `w = x_1 w_1` of the blowup of the origin gives `x_1^2 (x_1 - y_1^2)` and `x_1^3 (x_1 + z_1^2 - w_1^3)` (`bm_chart_first`, `bm_chart_second`). The strict transform meets the plane `x_1 = y_1 = 0` in the cuspidal curve `z_1^2 = w_1^3` (`bm_strict_inter`).
2. Example 1.3.2, the cusp. The pullbacks of `y^2 - x^3` in the charts of Steps 2 and 3 (`cusp_step_two`, `cusp_step_two_other`, `cusp_step_three`, `cusp_step_three_other`), and the composite of the three blowups, with the multiplicities `2, 3, 6` (`cusp_total_u`, `cusp_total_v`). On the last exceptional curve the strict transforms do not meet (`cusp_step_three_disjoint`). Step 1 is `Singularity.Example.cusp_chart_x` and `Singularity.Example.cusp_chart_y`.
3. Example 1.3.3, the Whitney umbrella `f = x^2 - y^2 z`. The partial derivatives are `2x`, `-2yz` and `-y^2` (`pderiv_whitneyEq_x`, `pderiv_whitneyEq_y`, `pderiv_whitneyEq_z`). If `2 ≠ 0`, the common zeros of `f` and its partials are the points of `L = (x = y = 0)` (`whitneyEq_singular_iff`). The order of `f` is `2` at the origin (`ord_whitneyEq`), and after the translation `z = c + t` it is `2` at `(0, 0, c)` (`aeval_whitneyEq_translate`, `ord_whitneyEq_translate`). The charts of parts 3 and 4 are `Singularity.whitney_lineChart_x`, `Singularity.whitney_lineChart_y` and `Singularity.whitney_pointChart_z`.
4. Example 2.3.5. Let `I = (y^2 - x^5)`. The curve `y = x` is not of maximal contact: `y - x ∉ (y, x^4)` (`sub_not_mem_mc`). The restriction of `y^2 - x^5` to `y = 0` has order `5`, and its restriction to `y = x` has order `2` (`ord_restrict_H`, `ord_restrict_H'`). After the blowup, `D(y_1^2 - x^3) = (y_1, x^2)` (`derivIdeal_transform`), and `(y_1) ⊆ (y_1, x^3) ⊆ MC(I_1)` (`mc_chain_transform`).
5. Example 3.2.6, the Whitney umbrella again. `D(I) = (x, yz, y^2)` if `2 ≠ 0` (`derivIdeal_whitneyEq`) and `D^2(I) = (1)` (`derivIdeal_derivIdeal_whitneyEq`). On `H = (x = 0)`, `C_H(I) = (y^2 z) + (yz, y^2)^2 = (y^2 z, y^4)` (`coeffIdeal_whitney`), and this is `(y^2) · (z, y^2)` (`coeffIdeal_whitney_eq_mul`). Its order is `3` at the origin (`idealOrd_coeffIdeal_whitney`), and `2` at the point `z = c` of `L` with `c ≠ 0` (`idealOrd_coeffIdeal_whitney_translate`). The transform `(z, y^2)` has order `1` at the origin (`idealOrd_transform_whitney`).

The coordinates are `x = X 0`, `y = X 1`, `z = X 2` on the affine space of dimension 3, and `x = X 0`, `y = X 1` on the plane. On `H = (x = 0)` in Example 3.2.6 the coordinates are `y = X 0` and `z = X 1`.

The file proves the ring identities and the ideal computations. It does not prove the geometric claims on smoothness, normal crossings and the choice of the centers.
-/

open MvPolynomial

namespace Singularity

namespace CharZeroExamples

section Helpers

variable {σ k : Type*} [Field k]

/-- Divide by `2` in an ideal of a polynomial ring over a field with `2 ≠ 0`. -/
theorem mem_of_two_mul_mem {I : Ideal (MvPolynomial σ k)} (h2 : (2 : k) ≠ 0)
    {g : MvPolynomial σ k} (h : 2 * g ∈ I) : g ∈ I := by
  have e : g = C (2⁻¹ : k) * (2 * g) := by
    rw [← mul_assoc, ← map_ofNat (C : k →+* MvPolynomial σ k) 2, ← C_mul, inv_mul_cancel₀ h2,
      C_1, one_mul]
  rw [e]
  exact I.mul_mem_left _ h

/-- Divide by `3` in an ideal of a polynomial ring over a field with `3 ≠ 0`. -/
theorem mem_of_three_mul_mem {I : Ideal (MvPolynomial σ k)} (h3 : (3 : k) ≠ 0)
    {g : MvPolynomial σ k} (h : 3 * g ∈ I) : g ∈ I := by
  have e : g = C (3⁻¹ : k) * (3 * g) := by
    rw [← mul_assoc, ← map_ofNat (C : k →+* MvPolynomial σ k) 3, ← C_mul, inv_mul_cancel₀ h3,
      C_1, one_mul]
  rw [e]
  exact I.mul_mem_left _ h

end Helpers

section Example122

variable {R : Type*} [CommRing R]

/-- **Volume 2, Example 1.2.2 of the handbook**, the first generator. In the chart `y = x_1 y_1`, `x^3 - y^2 = x_1^2 (x_1 - y_1^2)`. -/
theorem bm_chart_first (x₁ y₁ : R) : x₁ ^ 3 - (x₁ * y₁) ^ 2 = x₁ ^ 2 * (x₁ - y₁ ^ 2) := by
  ring

/-- **Volume 2, Example 1.2.2 of the handbook**, the second generator. In the chart `z = x_1 z_1`, `w = x_1 w_1`, `x^4 + x z^2 - w^3 = x_1^3 (x_1 + z_1^2 - w_1^3)`. -/
theorem bm_chart_second (x₁ z₁ w₁ : R) :
    x₁ ^ 4 + x₁ * (x₁ * z₁) ^ 2 - (x₁ * w₁) ^ 3 = x₁ ^ 3 * (x₁ + z₁ ^ 2 - w₁ ^ 3) := by
  ring

/-- **Volume 2, Example 1.2.2 of the handbook**, the intersection. The strict transform `(x_1 - y_1^2, x_1 + z_1^2 - w_1^3)` meets the plane `(x_1, y_1)` in the cuspidal curve `(x_1, y_1, z_1^2 - w_1^3)`. This holds for elements of each commutative ring. -/
theorem bm_strict_inter (x₁ y₁ z₁ w₁ : R) :
    Ideal.span {x₁ - y₁ ^ 2, x₁ + z₁ ^ 2 - w₁ ^ 3, x₁, y₁} =
      Ideal.span {x₁, y₁, z₁ ^ 2 - w₁ ^ 3} := by
  have hx : x₁ ∈ Ideal.span {x₁, y₁, z₁ ^ 2 - w₁ ^ 3} := Ideal.subset_span (by simp)
  have hy : y₁ ∈ Ideal.span {x₁, y₁, z₁ ^ 2 - w₁ ^ 3} := Ideal.subset_span (by simp)
  have hc : z₁ ^ 2 - w₁ ^ 3 ∈ Ideal.span {x₁, y₁, z₁ ^ 2 - w₁ ^ 3} := Ideal.subset_span (by simp)
  have kx : x₁ ∈ Ideal.span {x₁ - y₁ ^ 2, x₁ + z₁ ^ 2 - w₁ ^ 3, x₁, y₁} :=
    Ideal.subset_span (by simp)
  have ky : y₁ ∈ Ideal.span {x₁ - y₁ ^ 2, x₁ + z₁ ^ 2 - w₁ ^ 3, x₁, y₁} :=
    Ideal.subset_span (by simp)
  have kc : x₁ + z₁ ^ 2 - w₁ ^ 3 ∈ Ideal.span {x₁ - y₁ ^ 2, x₁ + z₁ ^ 2 - w₁ ^ 3, x₁, y₁} :=
    Ideal.subset_span (by simp)
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl | rfl | rfl)
    · exact sub_mem hx (Ideal.pow_mem_of_mem _ hy 2 two_pos)
    · rw [add_sub_assoc]
      exact add_mem hx hc
    · exact hx
    · exact hy
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl | rfl)
    · exact kx
    · exact ky
    · have e : z₁ ^ 2 - w₁ ^ 3 = (x₁ + z₁ ^ 2 - w₁ ^ 3) - x₁ := by ring
      rw [e]
      exact sub_mem kc kx

end Example122

section Example132

variable {R : Type*} [CommRing R]

/-- **Volume 2, Example 1.3.2 of the handbook**, Step 2. In the chart `x = x_2 y_1`, the pullback of `x^2 (y_1^2 - x)` is `x_2^2 y_1^3 (y_1 - x_2)`. -/
theorem cusp_step_two (x₂ y₁ : R) :
    (x₂ * y₁) ^ 2 * (y₁ ^ 2 - x₂ * y₁) = x₂ ^ 2 * y₁ ^ 3 * (y₁ - x₂) := by
  ring

/-- **Volume 2, Example 1.3.2 of the handbook**, Step 2, the other chart. In the chart `y_1 = y_2 x`, the pullback of `x^2 (y_1^2 - x)` is `x^3 (y_2^2 x - 1)`. -/
theorem cusp_step_two_other (x y₂ : R) :
    x ^ 2 * ((y₂ * x) ^ 2 - x) = x ^ 3 * (y₂ ^ 2 * x - 1) := by
  ring

/-- **Volume 2, Example 1.3.2 of the handbook**, Step 3. In the chart `y_1 = u x_2`, the pullback of `x_2^2 y_1^3 (y_1 - x_2)` is `x_2^6 u^3 (u - 1)`. -/
theorem cusp_step_three (x₂ u : R) :
    x₂ ^ 2 * (u * x₂) ^ 3 * (u * x₂ - x₂) = x₂ ^ 6 * u ^ 3 * (u - 1) := by
  ring

/-- **Volume 2, Example 1.3.2 of the handbook**, Step 3, the other chart. In the chart `x_2 = v y_1`, the pullback of `x_2^2 y_1^3 (y_1 - x_2)` is `v^2 y_1^6 (1 - v)`. -/
theorem cusp_step_three_other (v y₁ : R) :
    (v * y₁) ^ 2 * y₁ ^ 3 * (y₁ - v * y₁) = v ^ 2 * y₁ ^ 6 * (1 - v) := by
  ring

/-- **Volume 2, Example 1.3.2 of the handbook**, the composite in the chart of `u`. With `x = u x_2^2` and `y = u^2 x_2^3`, `y^2 - x^3 = x_2^6 u^3 (u - 1)`. So `E_3 = (x_2 = 0)` has multiplicity `6`, `E_2 = (u = 0)` has multiplicity `3`, and `C_3 = (u = 1)`. -/
theorem cusp_total_u (x₂ u : R) :
    (u ^ 2 * x₂ ^ 3) ^ 2 - (u * x₂ ^ 2) ^ 3 = x₂ ^ 6 * u ^ 3 * (u - 1) := by
  ring

/-- **Volume 2, Example 1.3.2 of the handbook**, the composite in the chart of `v`. With `x = v y_1^2` and `y = v y_1^3`, `y^2 - x^3 = v^2 y_1^6 (1 - v)`. So `E_1 = (v = 0)` has multiplicity `2`, `E_3 = (y_1 = 0)` has multiplicity `6`, and `C_3 = (v = 1)`. -/
theorem cusp_total_v (v y₁ : R) :
    (v * y₁ ^ 3) ^ 2 - (v * y₁ ^ 2) ^ 3 = v ^ 2 * y₁ ^ 6 * (1 - v) := by
  ring

/-- **Volume 2, Example 1.3.2 of the handbook**, Step 3, the disjointness. In the chart of `u`, `E_2 = (u = 0)` and `C_3 = (u = 1)` do not meet, and in the chart of `v`, `E_1 = (v = 0)` and `C_3 = (v = 1)` do not meet. -/
theorem cusp_step_three_disjoint (u v : R) :
    Ideal.span {u, u - 1} = ⊤ ∧ Ideal.span {v, 1 - v} = ⊤ := by
  refine ⟨?_, ?_⟩ <;> rw [Ideal.eq_top_iff_one]
  · exact Ideal.mem_span_pair.mpr ⟨1, -1, by ring⟩
  · exact Ideal.mem_span_pair.mpr ⟨1, 1, by ring⟩

end Example132

section Whitney

variable (R : Type*) [CommRing R]

/-- The Whitney umbrella `f = x^2 - y^2 z` of Volume 2, Examples 1.3.3 and 3.2.6 of the handbook. -/
noncomputable def whitneyEq : MvPolynomial (Fin 3) R := X 0 ^ 2 - X 1 ^ 2 * X 2

variable {R}

theorem whitneyEq_eq : whitneyEq R = X 0 * X 0 - X 1 * X 1 * X 2 := by
  rw [whitneyEq, sq, sq]

/-- **Volume 2, Example 1.3.3 (1) of the handbook**, the derivative in `x`: `∂f/∂x = 2x`. -/
theorem pderiv_whitneyEq_x : pderiv 0 (whitneyEq R) = 2 * X 0 := by
  rw [whitneyEq_eq]
  simp only [map_sub, pderiv_mul, pderiv_X_self, pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 0),
    pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 0)]
  ring

/-- **Volume 2, Example 1.3.3 (1) of the handbook**, the derivative in `y`: `∂f/∂y = -2yz`. -/
theorem pderiv_whitneyEq_y : pderiv 1 (whitneyEq R) = -(2 * (X 1 * X 2)) := by
  rw [whitneyEq_eq]
  simp only [map_sub, pderiv_mul, pderiv_X_self, pderiv_X_of_ne (by decide : (0 : Fin 3) ≠ 1),
    pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 1)]
  ring

/-- **Volume 2, Example 1.3.3 (1) of the handbook**, the derivative in `z`: `∂f/∂z = -y^2`. -/
theorem pderiv_whitneyEq_z : pderiv 2 (whitneyEq R) = -(X 1 ^ 2) := by
  rw [whitneyEq_eq]
  simp only [map_sub, pderiv_mul, pderiv_X_self, pderiv_X_of_ne (by decide : (0 : Fin 3) ≠ 2),
    pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 2)]
  ring

/-- **Volume 2, Example 1.3.3 (2) of the handbook**, the translation. With `z = c + t`, `f = x^2 - c y^2 - y^2 t`. -/
theorem aeval_whitneyEq_translate (c : R) :
    aeval ![X 0, X 1, C c + X 2] (whitneyEq R) = X 0 ^ 2 - C c * X 1 ^ 2 - X 1 ^ 2 * X 2 := by
  simp only [whitneyEq, map_sub, map_mul, map_pow, aeval_X]
  show (X 0 : MvPolynomial (Fin 3) R) ^ 2 - X 1 ^ 2 * (C c + X 2) = _
  ring

end Whitney

section WhitneyField

variable {k : Type*} [Field k]

/-- **Volume 2, Example 1.3.3 (1) of the handbook**, the singular locus. Let `2 ≠ 0` in `k`. A point `a` is a common zero of `f = x^2 - y^2 z` and of its three partial derivatives if and only if `a` lies on the line `L = (x = y = 0)`. -/
theorem whitneyEq_singular_iff (h2 : (2 : k) ≠ 0) (a : Fin 3 → k) :
    (eval a (whitneyEq k) = 0 ∧ eval a (pderiv 0 (whitneyEq k)) = 0 ∧
        eval a (pderiv 1 (whitneyEq k)) = 0 ∧ eval a (pderiv 2 (whitneyEq k)) = 0) ↔
      a 0 = 0 ∧ a 1 = 0 := by
  have hf : eval a (whitneyEq k) = a 0 ^ 2 - a 1 ^ 2 * a 2 := by simp [whitneyEq]
  have h0 : eval a (pderiv 0 (whitneyEq k)) = 2 * a 0 := by rw [pderiv_whitneyEq_x]; simp
  have h1 : eval a (pderiv 1 (whitneyEq k)) = -(2 * (a 1 * a 2)) := by
    rw [pderiv_whitneyEq_y]; simp
  have h2' : eval a (pderiv 2 (whitneyEq k)) = -(a 1 ^ 2) := by rw [pderiv_whitneyEq_z]; simp
  rw [hf, h0, h1, h2']
  constructor
  · rintro ⟨-, hx, -, hz⟩
    exact ⟨(mul_eq_zero.mp hx).resolve_left h2, by simpa using hz⟩
  · rintro ⟨ha, hb⟩
    rw [ha, hb]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- **Volume 2, Example 1.3.3 (1) of the handbook**, at the origin. The order of `f = x^2 - y^2 z` at the origin is `2`. -/
theorem ord_whitneyEq : ord (whitneyEq k) = 2 := by
  have e1 : ord (X 0 ^ 2 : MvPolynomial (Fin 3) k) = 2 := (ord_X_pow 0 2).trans (by norm_num)
  have e2 : ord (-(X 1 ^ 2 * X 2) : MvPolynomial (Fin 3) k) = 3 := by
    rw [ord_neg, ord_mul, ord_X_pow, ord_X]
    norm_num
  rw [whitneyEq, sub_eq_add_neg, ord_add_of_lt, e1]
  rw [e1, e2]
  exact_mod_cast (by norm_num : (2 : ℕ) < 3)

/-- **Volume 2, Example 1.3.3 (1) and (2) of the handbook**, at the point `(0, 0, c)` of `L`. For each `c`, the translate `x^2 - c y^2 - y^2 t` of `f` has order `2` at the origin. Its part of degree `2` is `x^2 - c y^2`. -/
theorem ord_whitneyEq_translate (c : k) :
    ord (X 0 ^ 2 - C c * X 1 ^ 2 - X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) = 2 := by
  have hX : ∀ i, (X i : MvPolynomial (Fin 3) k) ∈ idealOfVars (Fin 3) k := fun i =>
    mem_idealOfVars_iff.mpr (by simp)
  refine le_antisymm ?_ ?_
  · have hφ : ∀ i, constantCoeff (![X 0, 0, 0] i : MvPolynomial (Fin 3) k) = 0 := by
      intro i
      fin_cases i <;> simp
    have h := ord_le_ord_aeval ![(X 0 : MvPolynomial (Fin 3) k), 0, 0] hφ
      (X 0 ^ 2 - C c * X 1 ^ 2 - X 1 ^ 2 * X 2)
    have e : aeval ![(X 0 : MvPolynomial (Fin 3) k), 0, 0]
        (X 0 ^ 2 - C c * X 1 ^ 2 - X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) = X 0 ^ 2 := by
      simp
    rw [e, ord_X_pow] at h
    exact_mod_cast h
  · have hmem : (X 0 ^ 2 - C c * X 1 ^ 2 - X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) ∈
        idealOfVars (Fin 3) k ^ 2 :=
      sub_mem (sub_mem (Ideal.pow_mem_pow (hX 0) 2)
        (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (hX 1) 2)))
        (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hX 1) 2))
    exact_mod_cast le_ord_iff_mem_pow.mpr hmem

/-- **Volume 2, Example 3.2.6 of the handbook**, the derivative ideal. Let `2 ≠ 0` in `k`. Then `D(x^2 - y^2 z) = (x, yz, y^2)`. -/
theorem derivIdeal_whitneyEq (h2 : (2 : k) ≠ 0) :
    derivIdeal (Ideal.span {whitneyEq k}) = Ideal.span {X 0, X 1 * X 2, X 1 ^ 2} := by
  have hx : (X 0 : MvPolynomial (Fin 3) k) ∈ Ideal.span {X 0, X 1 * X 2, X 1 ^ 2} :=
    Ideal.subset_span (by simp)
  have hyz : (X 1 * X 2 : MvPolynomial (Fin 3) k) ∈ Ideal.span {X 0, X 1 * X 2, X 1 ^ 2} :=
    Ideal.subset_span (by simp)
  have hy2 : (X 1 ^ 2 : MvPolynomial (Fin 3) k) ∈ Ideal.span {X 0, X 1 * X 2, X 1 ^ 2} :=
    Ideal.subset_span (by simp)
  apply le_antisymm
  · rw [derivIdeal_span, Ideal.span_le]
    rintro g (hg | ⟨i, f', hf', rfl⟩)
    · rw [Set.mem_singleton_iff.mp hg]
      have e : whitneyEq k = X 0 * X 0 - X 2 * X 1 ^ 2 := by rw [whitneyEq]; ring
      rw [e]
      exact sub_mem (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_left _ _ hy2)
    · rw [Set.mem_singleton_iff.mp hf']
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
      rcases hi with rfl | rfl | rfl
      · rw [pderiv_whitneyEq_x]
        exact Ideal.mul_mem_left _ _ hx
      · rw [pderiv_whitneyEq_y]
        exact neg_mem (Ideal.mul_mem_left _ _ hyz)
      · rw [pderiv_whitneyEq_z]
        exact neg_mem hy2
  · have hf0 := Ideal.mem_span_singleton_self (whitneyEq k)
    rw [Ideal.span_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · have h := pderiv_mem_derivIdeal hf0 0
      rw [pderiv_whitneyEq_x] at h
      exact mem_of_two_mul_mem h2 h
    · have h := neg_mem (pderiv_mem_derivIdeal hf0 1)
      rw [pderiv_whitneyEq_y, neg_neg] at h
      exact mem_of_two_mul_mem h2 h
    · have h := neg_mem (pderiv_mem_derivIdeal hf0 2)
      rwa [pderiv_whitneyEq_z, neg_neg] at h

/-- **Volume 2, Example 3.2.6 of the handbook**, the second derivative ideal. Let `2 ≠ 0` in `k`. Then `D^2(x^2 - y^2 z)` is the unit ideal. So the maximal order is at most `2`. -/
theorem derivIdeal_derivIdeal_whitneyEq (h2 : (2 : k) ≠ 0) :
    derivIdeal (derivIdeal (Ideal.span {whitneyEq k})) = ⊤ := by
  rw [derivIdeal_whitneyEq h2, Ideal.eq_top_iff_one]
  have h := pderiv_mem_derivIdeal
    (Ideal.subset_span (by simp) :
      (X 0 : MvPolynomial (Fin 3) k) ∈ Ideal.span {X 0, X 1 * X 2, X 1 ^ 2}) 0
  rwa [pderiv_X_self] at h

end WhitneyField

section WhitneyCoefficient

variable {R : Type*} [CommRing R]

/-- **Volume 2, Example 3.2.6 of the handbook**, the coefficient ideal. On `H = (x = 0)` with the coordinates `y = X 0` and `z = X 1`, `C_H(I) = (y^2 z) + (yz, y^2)^2 = (y^2 z, y^4)`. This holds over each commutative ring. -/
theorem coeffIdeal_whitney :
    (Ideal.span {X 0 ^ 2 * X 1} ⊔ Ideal.span {X 0 * X 1, X 0 ^ 2} ^ 2 :
        Ideal (MvPolynomial (Fin 2) R)) = Ideal.span {X 0 ^ 2 * X 1, X 0 ^ 4} := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.subset_span (by simp)
    · rw [sq (Ideal.span {X 0 * X 1, X 0 ^ 2} : Ideal (MvPolynomial (Fin 2) R)), Ideal.mul_le]
      intro r hr s hs
      obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hr
      obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.mp hs
      exact Ideal.mem_span_pair.mpr ⟨a * c * X 1 + (a * d + b * c) * X 0, b * d, by ring⟩
  · rw [Ideal.span_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    · refine Ideal.mem_sup_right ?_
      have e : (X 0 ^ 4 : MvPolynomial (Fin 2) R) = X 0 ^ 2 * X 0 ^ 2 := by ring
      rw [e, sq (Ideal.span {X 0 * X 1, X 0 ^ 2} : Ideal (MvPolynomial (Fin 2) R))]
      exact Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))

/-- **Volume 2, Example 3.2.6 of the handbook**, the factorization. `(y^2 z, y^4) = (y^2) · (z, y^2)`. So the transform of `(C_H(I), 2)` under the blowup of `L = (y = 0)` in `H` is `(z, y^2)`. -/
theorem coeffIdeal_whitney_eq_mul :
    (Ideal.span {X 0 ^ 2 * X 1, X 0 ^ 4} : Ideal (MvPolynomial (Fin 2) R)) =
      Ideal.span {X 0 ^ 2} * Ideal.span {X 1, X 0 ^ 2} := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Ideal.subset_span (by simp))
    · have e : (X 0 ^ 4 : MvPolynomial (Fin 2) R) = X 0 ^ 2 * X 0 ^ 2 := by ring
      rw [e]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Ideal.subset_span (by simp))
  · rw [Ideal.mul_le]
    intro r hr s hs
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    obtain ⟨b, c, rfl⟩ := Ideal.mem_span_pair.mp hs
    exact Ideal.mem_span_pair.mpr ⟨a * b, a * c, by ring⟩

end WhitneyCoefficient

section WhitneyOrder

variable {k : Type*} [Field k]

/-- **Volume 2, Example 3.2.6 of the handbook**, the order at the origin. The ideal `C_H(I) = (y^2 z, y^4)` has order `3` at the origin. -/
theorem idealOrd_coeffIdeal_whitney :
    idealOrd (Ideal.span {X 0 ^ 2 * X 1, X 0 ^ 4} : Ideal (MvPolynomial (Fin 2) k)) = 3 := by
  have e1 : ord (X 0 ^ 2 * X 1 : MvPolynomial (Fin 2) k) = 3 := by
    rw [ord_mul, ord_X_pow, ord_X]
    norm_num
  have e2 : ord (X 0 ^ 4 : MvPolynomial (Fin 2) k) = 4 := (ord_X_pow 0 4).trans (by norm_num)
  rw [Ideal.span_insert, idealOrd_sup, idealOrd_span_singleton, idealOrd_span_singleton, e1, e2]
  exact min_eq_left (by exact_mod_cast (by norm_num : (3 : ℕ) ≤ 4))

/-- **Volume 2, Example 3.2.6 of the handbook**, the order at a point of `L` other than the origin. Let `c ≠ 0`. After the translation `z = c + t`, the ideal `C_H(I)` is `(y^2 (c + t), y^4)`, and it has order `2` at the origin. -/
theorem idealOrd_coeffIdeal_whitney_translate {c : k} (hc : c ≠ 0) :
    idealOrd (Ideal.span {X 0 ^ 2 * (C c + X 1), X 0 ^ 4} :
      Ideal (MvPolynomial (Fin 2) k)) = 2 := by
  have e0 : ord (C c + X 1 : MvPolynomial (Fin 2) k) = 0 := by
    rw [ord_add_of_lt, ord_C hc]
    rw [ord_C hc, ord_X]
    exact zero_lt_one
  have e1 : ord (X 0 ^ 2 * (C c + X 1) : MvPolynomial (Fin 2) k) = 2 := by
    rw [ord_mul, e0, add_zero]
    exact (ord_X_pow 0 2).trans (by norm_num)
  have e2 : ord (X 0 ^ 4 : MvPolynomial (Fin 2) k) = 4 := (ord_X_pow 0 4).trans (by norm_num)
  rw [Ideal.span_insert, idealOrd_sup, idealOrd_span_singleton, idealOrd_span_singleton, e1, e2]
  exact min_eq_left (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 4))

/-- **Volume 2, Example 3.2.6 of the handbook**, the transform. The ideal `(z, y^2)` has order `1` at the origin. -/
theorem idealOrd_transform_whitney :
    idealOrd (Ideal.span {X 1, X 0 ^ 2} : Ideal (MvPolynomial (Fin 2) k)) = 1 := by
  have e2 : ord (X 0 ^ 2 : MvPolynomial (Fin 2) k) = 2 := (ord_X_pow 0 2).trans (by norm_num)
  rw [Ideal.span_insert, idealOrd_sup, idealOrd_span_singleton, idealOrd_span_singleton, ord_X, e2]
  exact min_eq_left (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2))

end WhitneyOrder

section Example235

variable {k : Type*} [Field k]

/-- **Volume 2, Example 2.3.5 of the handbook**, the curve `H' = (y = x)`. The element `y - x` does not lie in `MC(I) = (y, x^4)`. So `H'` is not a curve of maximal contact. -/
theorem sub_not_mem_mc : (X 1 - X 0 : MvPolynomial (Fin 2) k) ∉ Ideal.span {X 1, X 0 ^ 4} := by
  intro h
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp h
  set φ : Fin 2 → MvPolynomial (Fin 2) k := ![X 0, 0]
  have e : aeval φ b * X 0 ^ 4 = -X 0 := by
    have h' := congrArg (aeval φ) hab
    simpa [φ] using h'
  have h4 : (4 : ℕ∞) ≤ ord (-X 0 : MvPolynomial (Fin 2) k) := by
    calc (4 : ℕ∞) = ord (X 0 ^ 4 : MvPolynomial (Fin 2) k) :=
          ((ord_X_pow 0 4).trans (by norm_num)).symm
      _ ≤ ord (aeval φ b) + ord (X 0 ^ 4 : MvPolynomial (Fin 2) k) := le_add_self
      _ ≤ ord (aeval φ b * X 0 ^ 4) := le_ord_mul _ _
      _ = ord (-X 0 : MvPolynomial (Fin 2) k) := by rw [e]
  rw [ord_neg, ord_X] at h4
  have : (4 : ℕ) ≤ 1 := by exact_mod_cast h4
  omega

/-- **Volume 2, Example 2.3.5 of the handbook**, the restriction to `H = (y = 0)`. The restriction of `y^2 - x^5` has order `5`. -/
theorem ord_restrict_H :
    ord (aeval ![(X 0 : MvPolynomial (Fin 2) k), 0]
      (X 1 ^ 2 - X 0 ^ 5 : MvPolynomial (Fin 2) k)) = 5 := by
  have e : aeval ![(X 0 : MvPolynomial (Fin 2) k), 0]
      (X 1 ^ 2 - X 0 ^ 5 : MvPolynomial (Fin 2) k) = -(X 0 ^ 5) := by
    simp
  rw [e, ord_neg]
  exact (ord_X_pow 0 5).trans (by norm_num)

/-- **Volume 2, Example 2.3.5 of the handbook**, the restriction to `H' = (y = x)`. The restriction of `y^2 - x^5` is `x^2 - x^5`, of order `2`. -/
theorem ord_restrict_H' :
    ord (aeval ![(X 0 : MvPolynomial (Fin 2) k), X 0]
      (X 1 ^ 2 - X 0 ^ 5 : MvPolynomial (Fin 2) k)) = 2 := by
  have e : aeval ![(X 0 : MvPolynomial (Fin 2) k), X 0]
      (X 1 ^ 2 - X 0 ^ 5 : MvPolynomial (Fin 2) k) =
      X 0 ^ 2 - X 0 ^ 5 := by
    simp
  have e1 : ord (X 0 ^ 2 : MvPolynomial (Fin 2) k) = 2 := (ord_X_pow 0 2).trans (by norm_num)
  have e2 : ord (-(X 0 ^ 5) : MvPolynomial (Fin 2) k) = 5 := by
    rw [ord_neg]
    exact (ord_X_pow 0 5).trans (by norm_num)
  rw [e, sub_eq_add_neg, ord_add_of_lt, e1]
  rw [e1, e2]
  exact_mod_cast (by norm_num : (2 : ℕ) < 5)

variable {R : Type*} [CommRing R]

/-- **Volume 2, Example 2.3.5 of the handbook**, the chart `y = y_1 x`. The pullback of `y^2 - x^5` is `x^2 (y_1^2 - x^3)`, and the pullback of `y - x` is `x (y_1 - 1)`. -/
theorem chart_example235 (x y₁ : R) :
    (y₁ * x) ^ 2 - x ^ 5 = x ^ 2 * (y₁ ^ 2 - x ^ 3) ∧ y₁ * x - x = x * (y₁ - 1) :=
  ⟨by ring, by ring⟩

theorem transformEq_eq :
    (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k) = X 1 * X 1 - X 0 * X 0 * X 0 := by ring

theorem pderiv_transformEq_x :
    pderiv 0 (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k) = -(3 * X 0 ^ 2) := by
  rw [transformEq_eq]
  simp only [map_sub, pderiv_mul, pderiv_X_self, pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  ring

theorem pderiv_transformEq_y :
    pderiv 1 (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k) = 2 * X 1 := by
  rw [transformEq_eq]
  simp only [map_sub, pderiv_mul, pderiv_X_self, pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  ring

/-- **Volume 2, Example 2.3.5 of the handbook**, after the blowup (and Example 2.2.9). Let `2 ≠ 0` and `3 ≠ 0` in `k`. With `x = X 0` and `y_1 = X 1`, `D(y_1^2 - x^3) = (y_1, x^2)`. This is `MC(I_1)`, since `I_1` has maximal order `2`. -/
theorem derivIdeal_transform (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) :
    derivIdeal (Ideal.span {X 1 ^ 2 - X 0 ^ 3} : Ideal (MvPolynomial (Fin 2) k)) =
      Ideal.span {X 1, X 0 ^ 2} := by
  have hy : (X 1 : MvPolynomial (Fin 2) k) ∈ Ideal.span {X 1, X 0 ^ 2} :=
    Ideal.subset_span (by simp)
  have hx2 : (X 0 ^ 2 : MvPolynomial (Fin 2) k) ∈ Ideal.span {X 1, X 0 ^ 2} :=
    Ideal.subset_span (by simp)
  apply le_antisymm
  · rw [derivIdeal_span, Ideal.span_le]
    rintro g (hg | ⟨i, f', hf', rfl⟩)
    · rw [Set.mem_singleton_iff.mp hg]
      have e : (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k) = X 1 * X 1 - X 0 * X 0 ^ 2 := by
        ring
      rw [e]
      exact sub_mem (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ hx2)
    · rw [Set.mem_singleton_iff.mp hf']
      have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      rcases hi with rfl | rfl
      · rw [pderiv_transformEq_x]
        exact neg_mem (Ideal.mul_mem_left _ _ hx2)
      · rw [pderiv_transformEq_y]
        exact Ideal.mul_mem_left _ _ hy
  · have hf0 := Ideal.mem_span_singleton_self (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k)
    rw [Ideal.span_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · have h := pderiv_mem_derivIdeal hf0 1
      rw [pderiv_transformEq_y] at h
      exact mem_of_two_mul_mem h2 h
    · have h := neg_mem (pderiv_mem_derivIdeal hf0 0)
      rw [pderiv_transformEq_x, neg_neg] at h
      exact mem_of_three_mul_mem h3 h

/-- **Volume 2, Example 2.3.5 of the handbook**, part (1) of Theorem 2.3.3 in the example. Let `2 ≠ 0` and `3 ≠ 0` in `k`. Then `O(-H_1) = (y_1) ⊆ J^(1)_1 = (y_1, x^3) ⊆ MC(I_1) = D(y_1^2 - x^3)`. -/
theorem mc_chain_transform (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) :
    (Ideal.span {X 1} : Ideal (MvPolynomial (Fin 2) k)) ≤ Ideal.span {X 1, X 0 ^ 3} ∧
      Ideal.span {X 1, X 0 ^ 3} ≤
        derivIdeal (Ideal.span {X 1 ^ 2 - X 0 ^ 3} : Ideal (MvPolynomial (Fin 2) k)) := by
  refine ⟨Ideal.span_mono (by simp), ?_⟩
  rw [derivIdeal_transform h2 h3, Ideal.span_le]
  rintro _ (rfl | rfl)
  · exact Ideal.subset_span (by simp)
  · have e : (X 0 ^ 3 : MvPolynomial (Fin 2) k) = X 0 * X 0 ^ 2 := by ring
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

end Example235

end CharZeroExamples

end Singularity
