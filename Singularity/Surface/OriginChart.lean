/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.FinCases

/-!
# The `x`-chart of the blowup of `A^3` at the origin

Let `k` be a domain, let `F ∈ k[x, y, z]`, and let `m` be the least degree of a monomial of `F`. Volume 4, Lemma 1.1.6 of the handbook computes the strict transform of `V(F)` in the `x`-chart `y = x y_1`, `z = x z_1` of the blowup of `A^3` at the origin. This file proves the algebraic part of the lemma. The variables `x, y, z` and `x, y_1, z_1` are the variables `X 0, X 1, X 2` of `MvPolynomial (Fin 3) k`.

* `Singularity.originXChart`: the substitution `F ↦ F(x, x y_1, x z_1)`. It is injective (`Singularity.originXChart_injective`), since it becomes the inclusion of `k[x, y, z]` in its field of fractions after `y_1 ↦ y/x`, `z_1 ↦ z/x`.
* `Singularity.originXChart_of_isHomogeneous`: for `P` homogeneous of degree `d`, `P(x, x y_1, x z_1) = x^d P(1, y_1, z_1)`.
* `Singularity.originXChart_eq_pow_mul_originStrict`, `Singularity.originRestrict_originStrict` and `Singularity.not_X_dvd_originStrict`: Lemma 1.1.6. Let `F_m ≠ 0` be the homogeneous part of degree `m` of `F`, and let the parts of lower degree be `0`. Then `F(x, x y_1, x z_1) = x^m F'` with `F' = originStrict F m`, `F'(0, y_1, z_1) = F_m(1, y_1, z_1)`, and `x` does not divide `F'`.
* `Singularity.exists_originXChart_eq_pow_mul`: the three claims together.

The file does not prove that the chart `R[I/x]` is the polynomial ring `k[x, y_1, z_1]`, and it does not prove the claims on the strict transform and the exceptional divisor as schemes.
-/

open MvPolynomial

namespace Singularity

variable (k : Type*) [CommRing k]

/-- The `x`-chart of the blowup of `A^3` at the origin: `F ↦ F(x, x y_1, x z_1)` (Volume 4, Lemma 1.1.6 of the handbook). -/
noncomputable def originXChart : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 3) k :=
  aeval ![X 0, X 0 * X 1, X 0 * X 2]

/-- The dehomogenization `P ↦ P(1, y_1, z_1)`. -/
noncomputable def originDehom : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 3) k :=
  aeval ![1, X 1, X 2]

/-- The restriction `P ↦ P(0, y_1, z_1)` to the exceptional divisor `V(x)` of the chart. -/
noncomputable def originRestrict : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 3) k :=
  aeval ![0, X 1, X 2]

variable {k}

/-- The strict transform `F' = ∑_d x^(d - m) F_d(1, y_1, z_1)` of `F` in the `x`-chart, with `F_d` the homogeneous part of degree `d` of `F` (Volume 4, Lemma 1.1.6 of the handbook). -/
noncomputable def originStrict (F : MvPolynomial (Fin 3) k) (m : ℕ) : MvPolynomial (Fin 3) k :=
  ∑ d ∈ Finset.range (F.totalDegree + 1),
    X 0 ^ (d - m) * originDehom k (homogeneousComponent d F)

/-- The `x`-chart on a monomial `x^a y^b z^c` gives `x^(a + b + c) y_1^b z_1^c`. -/
theorem originXChart_monomial (s : Fin 3 →₀ ℕ) (c : k) :
    originXChart k (monomial s c) = X 0 ^ (s 0 + s 1 + s 2) * originDehom k (monomial s c) := by
  simp only [originXChart, originDehom, aeval_monomial]
  rw [Finsupp.prod_fintype, Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, one_pow]
    ring
  all_goals intro i; simp

/-- For `P` homogeneous of degree `d`, `P(x, x y_1, x z_1) = x^d P(1, y_1, z_1)` (Volume 4, Lemma 1.1.6 of the handbook). -/
theorem originXChart_of_isHomogeneous {P : MvPolynomial (Fin 3) k} {d : ℕ}
    (hP : P.IsHomogeneous d) : originXChart k P = X 0 ^ d * originDehom k P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hw := hP (mem_support_iff.mp hs)
  have hd : s 0 + s 1 + s 2 = d := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum_fintype]
    · simp [Fin.sum_univ_three]
    · intro i
      simp
  rw [originXChart_monomial, hd]

/-- The map `y_1 ↦ y/x`, `z_1 ↦ z/x` from the chart to the field of fractions of `k[x, y, z]`. -/
noncomputable def originXChartInv [IsDomain k] :
    MvPolynomial (Fin 3) k →+* FractionRing (MvPolynomial (Fin 3) k) :=
  eval₂Hom ((algebraMap (MvPolynomial (Fin 3) k) (FractionRing (MvPolynomial (Fin 3) k))).comp C)
    ![algebraMap _ _ (X 0), algebraMap _ _ (X 1) / algebraMap _ _ (X 0),
      algebraMap _ _ (X 2) / algebraMap _ _ (X 0)]

/-- The composite of the `x`-chart and `y_1 ↦ y/x`, `z_1 ↦ z/x` is the inclusion of `k[x, y, z]` in its field of fractions. -/
theorem originXChartInv_comp [IsDomain k] :
    originXChartInv.comp (originXChart k).toRingHom =
      algebraMap (MvPolynomial (Fin 3) k) (FractionRing (MvPolynomial (Fin 3) k)) := by
  have h0 : algebraMap (MvPolynomial (Fin 3) k) (FractionRing (MvPolynomial (Fin 3) k)) (X 0) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (X_ne_zero 0)
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [originXChartInv, originXChart]
  · intro i
    fin_cases i <;> simp [originXChartInv, originXChart, mul_div_cancel₀ _ h0]

/-- The `x`-chart `F ↦ F(x, x y_1, x z_1)` is injective (Volume 4, Lemma 1.1.6 of the handbook). -/
theorem originXChart_injective [IsDomain k] : Function.Injective (originXChart k) := by
  intro a b hab
  apply IsFractionRing.injective (MvPolynomial (Fin 3) k) (FractionRing (MvPolynomial (Fin 3) k))
  rw [← originXChartInv_comp]
  exact congrArg originXChartInv hab

/-- The restriction to `V(x)` fixes `P(1, y_1, z_1)`. -/
theorem originRestrict_originDehom (P : MvPolynomial (Fin 3) k) :
    originRestrict k (originDehom k P) = originDehom k P := by
  have h : (originRestrict k).comp (originDehom k) = originDehom k := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [originRestrict, originDehom]
  exact DFunLike.congr_fun h P

/-- The restriction to `V(x)` sends `x` to `0`. -/
theorem originRestrict_X_zero : originRestrict k (X 0) = 0 := by
  simp [originRestrict]

/-- Volume 4, Lemma 1.1.6 of the handbook, the factorization. If the homogeneous parts of `F` of degree less than `m` are `0`, then `F(x, x y_1, x z_1) = x^m F'`. -/
theorem originXChart_eq_pow_mul_originStrict (F : MvPolynomial (Fin 3) k) {m : ℕ}
    (hlow : ∀ d < m, homogeneousComponent d F = 0) :
    originXChart k F = X 0 ^ m * originStrict F m := by
  conv_lhs => rw [← sum_homogeneousComponent (φ := F)]
  rw [map_sum, originStrict, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [originXChart_of_isHomogeneous (homogeneousComponent_isHomogeneous d F)]
  by_cases h : m ≤ d
  · rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]
  · simp [hlow d (by omega)]

/-- Volume 4, Lemma 1.1.6 of the handbook: `F'(0, y_1, z_1) = F_m(1, y_1, z_1)`, with `m` the least degree of a monomial of `F`. -/
theorem originRestrict_originStrict (F : MvPolynomial (Fin 3) k) {m : ℕ}
    (hlow : ∀ d < m, homogeneousComponent d F = 0) (hm : homogeneousComponent m F ≠ 0) :
    originRestrict k (originStrict F m) = originDehom k (homogeneousComponent m F) := by
  rw [originStrict, map_sum, Finset.sum_eq_single m]
  · rw [map_mul, map_pow, Nat.sub_self, pow_zero, one_mul, originRestrict_originDehom]
  · intro d _ hdm
    rcases lt_or_gt_of_ne hdm with h | h
    · simp [hlow d h]
    · rw [map_mul, map_pow, originRestrict_X_zero, zero_pow (Nat.sub_ne_zero_of_lt h), zero_mul]
  · intro hmN
    exfalso
    apply hm
    apply homogeneousComponent_eq_zero
    simp only [Finset.mem_range, not_lt] at hmN
    omega

/-- Volume 4, Lemma 1.1.6 of the handbook: `x` does not divide the strict transform `F'`, with `m` the least degree of a monomial of `F`. -/
theorem not_X_dvd_originStrict [IsDomain k] (F : MvPolynomial (Fin 3) k) {m : ℕ}
    (hlow : ∀ d < m, homogeneousComponent d F = 0) (hm : homogeneousComponent m F ≠ 0) :
    ¬ (X 0 ∣ originStrict F m) := by
  rintro ⟨G, hG⟩
  have h := congrArg (originRestrict k) hG
  rw [originRestrict_originStrict F hlow hm, map_mul, originRestrict_X_zero, zero_mul] at h
  apply hm
  apply originXChart_injective
  rw [originXChart_of_isHomogeneous (homogeneousComponent_isHomogeneous m F), h, mul_zero,
    map_zero]

/-- Volume 4, Lemma 1.1.6 of the handbook. Let `k` be a domain and let `m` be the least degree of a monomial of `F`, that is, the homogeneous part `F_m` is not `0` and the parts of lower degree are `0`. Then `F(x, x y_1, x z_1) = x^m F'`, where `x` does not divide `F'` and `F'(0, y_1, z_1) = F_m(1, y_1, z_1)`. -/
theorem exists_originXChart_eq_pow_mul [IsDomain k] (F : MvPolynomial (Fin 3) k) {m : ℕ}
    (hlow : ∀ d < m, homogeneousComponent d F = 0) (hm : homogeneousComponent m F ≠ 0) :
    ∃ F' : MvPolynomial (Fin 3) k, originXChart k F = X 0 ^ m * F' ∧ ¬ (X 0 ∣ F') ∧
      originRestrict k F' = originDehom k (homogeneousComponent m F) :=
  ⟨originStrict F m, originXChart_eq_pow_mul_originStrict F hlow,
    not_X_dvd_originStrict F hlow hm, originRestrict_originStrict F hlow hm⟩

end Singularity
