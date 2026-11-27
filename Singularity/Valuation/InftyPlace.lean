/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.FieldTheory.RatFunc.Valuation
import Singularity.Valuation.Center

/-!
# The valuation at infinity has no center on the affine line

Let `F` be a field and `K = F(x)`. The valuation at infinity is `v(f/g) = deg g - deg f`. Mathlib has it as `RatFunc.inftyValuation F`, written multiplicatively with values in `ℤᵐ⁰`, so that `v(f/g) = exp (deg f - deg g)` and `v(x) = exp 1 > 1`. This file proves the claims on centers of Volume 3, Example 1.4.6 of the handbook.

1. The element `x` is not in the valuation ring `𝒪_v` (`not_mem_inftyValuationSubring_X`). So `v` has no center on `A^1 = Spec F[x]` (`not_exists_center_inftyValuation_polynomial`). This uses the lemma on centers, `Singularity.exists_center_iff`.
2. The ring `F[1/x]` of the other chart of `P^1` lies in `𝒪_v` (`inftyChart_le`). For a polynomial `q`, `v(q(1/x)) ≤ 1` (`inftyValuation_aeval_inv_X_le_one`), and `v(q(1/x)) < 1` if and only if `X ∣ q` (`inftyValuation_aeval_inv_X_lt_one_iff`). So the center of `v` on `Spec F[1/x]` is the ideal `(1/x)`, the point `∞` (`mem_centerIdeal_inftyChart_iff`).

The claims `𝒪_v = F[1/x]_(1/x)`, `Γ_v = ℤ`, `Kv = F` and `dim v = 0` are not proved here.

## Main results

* `Singularity.not_exists_center_inftyValuation_polynomial`: no center on `Spec F[x]`.
* `Singularity.inftyChart_le`: `F[1/x] ⊆ 𝒪_v`.
* `Singularity.mem_centerIdeal_inftyChart_iff`: the center on `Spec F[1/x]` is `(1/x)`.
-/

open Polynomial WithZero

namespace Singularity

variable (F : Type*) [Field F] [DecidableEq (RatFunc F)]

/-- The valuation at infinity sends `1/x` to `exp (-1) < 1`. -/
theorem inftyValuation_X_inv : RatFunc.inftyValuation F (RatFunc.X⁻¹) = exp (-1 : ℤ) := by
  rw [map_inv₀, RatFunc.inftyValuation.X, inv_exp]

theorem inftyValuation_X_inv_lt_one : RatFunc.inftyValuation F (RatFunc.X⁻¹) < 1 := by
  rw [inftyValuation_X_inv, exp_lt_one_iff]
  norm_num

/-- The valuation at infinity is at most `1` on the constants. -/
theorem inftyValuation_algebraMap_le_one (a : F) :
    RatFunc.inftyValuation F (algebraMap F (RatFunc F) a) ≤ 1 := by
  by_cases ha : a = 0
  · rw [ha, map_zero, Valuation.map_zero]
    exact zero_le_one
  · exact (Valuation.IsTrivialOn.eq_one (v := RatFunc.inftyValuation F) a ha).le

/-- The element `x` is not in the valuation ring of the valuation at infinity, since `v(x) = exp 1 > 1` (Volume 3, Example 1.4.6 of the handbook). -/
theorem not_mem_inftyValuationSubring_X :
    (RatFunc.X : RatFunc F) ∉ (RatFunc.inftyValuation F).valuationSubring := by
  rw [Valuation.mem_valuationSubring_iff, RatFunc.inftyValuation.X, exp_le_one_iff]
  norm_num

/-- **No center on the affine line** (Volume 3, Example 1.4.6 of the handbook). The valuation ring of the valuation at infinity has no center on `F[x]`, that is, there is no prime `P` of `F[x]` such that `𝒪_v` dominates `F[x]_P`. -/
theorem not_exists_center_inftyValuation_polynomial :
    ¬ ∃ (P : Ideal (algebraMap F[X] (RatFunc F)).range) (_ : P.IsPrime),
      LocalSubring.ofPrime (algebraMap F[X] (RatFunc F)).range P ≤
        (RatFunc.inftyValuation F).valuationSubring.toLocalSubring := by
  rw [exists_center_iff]
  intro h
  exact not_mem_inftyValuationSubring_X F
    (h (RingHom.mem_range.mpr ⟨Polynomial.X, RatFunc.algebraMap_X⟩))

/-- The valuation at infinity is at most `1` on `q(1/x)` for each polynomial `q`. -/
theorem inftyValuation_aeval_inv_X_le_one (q : F[X]) :
    RatFunc.inftyValuation F (aeval (RatFunc.X⁻¹ : RatFunc F) q) ≤ 1 := by
  refine Polynomial.induction_on q (fun a => ?_) (fun p r hp hr => ?_) (fun n a h => ?_)
  · rw [aeval_C]
    exact inftyValuation_algebraMap_le_one F a
  · rw [map_add]
    exact ((RatFunc.inftyValuation F).map_add _ _).trans (max_le hp hr)
  · rw [pow_succ, ← mul_assoc, map_mul, Valuation.map_mul, aeval_X]
    exact (mul_le_of_le_one_right' (inftyValuation_X_inv_lt_one F).le).trans h

/-- Let `q` be a polynomial. Then `v(q(1/x)) < 1` if and only if `X` divides `q`, that is, `q(1/x)` is in the ideal `(1/x)` of `F[1/x]`. -/
theorem inftyValuation_aeval_inv_X_lt_one_iff (q : F[X]) :
    RatFunc.inftyValuation F (aeval (RatFunc.X⁻¹ : RatFunc F) q) < 1 ↔ X ∣ q := by
  rw [X_dvd_iff]
  have hq : aeval (RatFunc.X⁻¹ : RatFunc F) q = algebraMap F (RatFunc F) (q.coeff 0) +
      RatFunc.X⁻¹ * aeval (RatFunc.X⁻¹ : RatFunc F) q.divX := by
    conv_lhs => rw [← X_mul_divX_add q]
    rw [map_add, map_mul, aeval_X, aeval_C, add_comm]
  have hlt : RatFunc.inftyValuation F
      (RatFunc.X⁻¹ * aeval (RatFunc.X⁻¹ : RatFunc F) q.divX) < 1 := by
    rw [Valuation.map_mul]
    exact (mul_le_of_le_one_right' (inftyValuation_aeval_inv_X_le_one F _)).trans_lt
      (inftyValuation_X_inv_lt_one F)
  rw [hq]
  constructor
  · intro h
    by_contra h0
    have h1 : RatFunc.inftyValuation F (algebraMap F (RatFunc F) (q.coeff 0)) = 1 :=
      Valuation.IsTrivialOn.eq_one (v := RatFunc.inftyValuation F) _ h0
    have h2 : RatFunc.inftyValuation F
        (RatFunc.X⁻¹ * aeval (RatFunc.X⁻¹ : RatFunc F) q.divX) <
          RatFunc.inftyValuation F (algebraMap F (RatFunc F) (q.coeff 0)) := by
      rw [h1]
      exact hlt
    rw [(RatFunc.inftyValuation F).map_add_eq_of_lt_left h2, h1] at h
    exact lt_irrefl _ h
  · intro h0
    rw [h0, map_zero, zero_add]
    exact hlt

/-- The ring `F[1/x]` of the chart of `P^1` at infinity, as a subring of `F(x)`. -/
noncomputable def inftyChart : Subring (RatFunc F) :=
  (aeval (RatFunc.X⁻¹ : RatFunc F) : F[X] →ₐ[F] RatFunc F).range.toSubring

theorem aeval_mem_inftyChart (q : F[X]) :
    aeval (RatFunc.X⁻¹ : RatFunc F) q ∈ inftyChart F :=
  Subalgebra.mem_toSubring.mpr (AlgHom.mem_range_self _ q)

/-- The ring `F[1/x]` lies in the valuation ring of the valuation at infinity (Volume 3, Example 1.4.6 of the handbook). -/
theorem inftyChart_le :
    inftyChart F ≤ (RatFunc.inftyValuation F).valuationSubring.toSubring := by
  intro y hy
  obtain ⟨q, rfl⟩ := AlgHom.mem_range.mp (Subalgebra.mem_toSubring.mp hy)
  exact inftyValuation_aeval_inv_X_le_one F q

/-- **The center at infinity** (Volume 3, Example 1.4.6 of the handbook). The center `m_v ∩ F[1/x]` of the valuation at infinity on `F[1/x]` is the ideal `(1/x)`: the element `q(1/x)` is in the center if and only if `X` divides `q`. So the center of `v` on `P^1` is the point `∞`. -/
theorem mem_centerIdeal_inftyChart_iff (q : F[X]) :
    (⟨aeval (RatFunc.X⁻¹ : RatFunc F) q, aeval_mem_inftyChart F q⟩ : inftyChart F) ∈
      centerIdeal (RatFunc.inftyValuation F).valuationSubring (inftyChart F) (inftyChart_le F) ↔
        X ∣ q := by
  rw [mem_centerIdeal,
    ← ((RatFunc.inftyValuation F).isEquiv_valuation_valuationSubring).lt_one_iff_lt_one]
  exact inftyValuation_aeval_inv_X_lt_one_iff F q

end Singularity
