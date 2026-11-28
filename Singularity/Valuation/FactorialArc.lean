/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.FactorialSeries
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# The arc `(t, ∑ t^{i!})` and its first blowup

This file proves Volume 3, Example 1.6.9 of the handbook. Let `φ = ∑_{i ≥ 1} t^{i!}`, the series
`Singularity.factorialSeries k` of Lemma 1.6.5. The valuation `v = v_φ` of Example 1.6.6 is
`v(f) = ord_t f(t, φ(t))` for `f` in `k[x, y]`. Here it is `arcOrder f`, the order of
`MvPolynomial.aeval ![t, φ] f` in `k[[t]]`. The repository has no other arc valuation.

## Main results

* `order_factorialSeries_sub_sum`: the order of `φ - ∑_{i=1}^N t^{i!}` is `(N + 1)!`.
* `arcOrder_Y_sub_sum`: `v(y - ∑_{i=1}^N x^{i!}) = (N + 1)!`.
* `arcOrder_Y`, `arcOrder_Y_sub_X`, `arcOrder_Y_sub_X_sub_X_sq`,
  `arcOrder_Y_sub_X_sub_X_sq_sub_X_pow_six`: the values `1, 2, 6, 24`.
* `arcOrder_ne_monomial_one_one`: `v(x) = v(y) = 1` and each monomial of `y - x` has weight
  `1`, but `v(y - x) = 2 ≠ 1`. So `v` is not the monomial valuation with weights `(1, 1)`.
* `X_mul_factorialSeriesDivX`: the series `φ / t = 1 + t + t^5 + t^23 + ...` times `t` is `φ`.
* `order_factorialSeriesDivX_sub_sum`: the order of `φ / t - ∑_{i=1}^N t^{i! - 1}` is
  `(N + 1)! - 1`.
* `chartArcEval_comp_blowup`: the arc `(t, φ / t)` in the chart `k[x, y_1]`, `y_1 = y / x`,
  lifts the arc `(t, φ)` through the blowup map `x ↦ x`, `y ↦ x y_1`.
* `chartArcOrder_X`, `chartArcOrder_Y`, `chartArcOrder_Y_sub_one`: in the chart,
  `v(x) = 1`, `v(y_1) = 0` and `v(y_1 - 1) = 1`.

The statements about the center on the blowup and the later blowups are not formalized.

The check on the build server used a copy of this file in which the import
`Singularity.Valuation.FactorialSeries` is replaced by the definitions it needs, since that
module is missing on the server.
-/

open Polynomial
open scoped Nat

namespace Singularity

namespace FactorialSeries

variable {k : Type*} [Field k]

/-- `(N + 1)!` is not of the form `i!` with `1 ≤ i ≤ N`. -/
theorem succ_factorial_notMem_image (N : ℕ) :
    (N + 1)! ∉ (Finset.Icc 1 N).image Nat.factorial := by
  simp only [Finset.mem_image, Finset.mem_Icc, not_exists, not_and]
  intro i hi h
  have := (Nat.factorial_lt (by omega : 0 < i)).mpr (by omega : i < N + 1)
  omega

/-- `(N + 1)!` is an exponent of the series `φ`. -/
theorem succ_factorial_mem_image (N : ℕ) :
    (N + 1)! ∈ (Finset.Icc 1 (N + 1)!).image Nat.factorial :=
  Finset.mem_image.mpr ⟨N + 1, Finset.mem_Icc.mpr ⟨by omega, Nat.self_le_factorial _⟩, rfl⟩

/-- The order of `φ - φ_N` is `(N + 1)!`. -/
theorem order_sub_partialSum (N : ℕ) :
    (factorialSeries k - algebraMap k[X] (PowerSeries k) (partialSum k N)).order =
      ((N + 1)! : ℕ) := by
  rw [PowerSeries.order_eq_nat]
  refine ⟨?_, fun m hm => ?_⟩
  · rw [map_sub, coeff_factorialSeries, coeff_algebraMap, coeff_partialSum,
      if_pos (succ_factorial_mem_image N), if_neg (succ_factorial_notMem_image N)]
    simp
  · rw [map_sub, coeff_factorialSeries, coeff_algebraMap, coeff_partialSum]
    exact sub_eq_zero.mpr (if_congr (exists_iff_of_lt hm) rfl rfl)

/-- The partial sum `φ_N`, seen as a power series, is `∑_{i=1}^N t^{i!}`. -/
theorem algebraMap_partialSum (N : ℕ) :
    algebraMap k[X] (PowerSeries k) (partialSum k N) =
      ∑ i ∈ Finset.Icc 1 N, (PowerSeries.X : PowerSeries k) ^ i ! := by
  ext m
  rw [coeff_algebraMap, coeff_partialSum, map_sum]
  simp only [PowerSeries.coeff_X_pow]
  split_ifs with h
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      rw [if_neg]
      intro hij
      exact hji (factorial_inj_of_one_le (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hi).1
        hij.symm)
    · intro hi'
      exact absurd hi hi'
  · symm
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg]
    intro hmj
    exact h (Finset.mem_image.mpr ⟨j, hj, hmj.symm⟩)

/-- The order of `φ - ∑_{i=1}^N t^{i!}` is `(N + 1)!`. -/
theorem order_factorialSeries_sub_sum (N : ℕ) :
    (factorialSeries k - ∑ i ∈ Finset.Icc 1 N, (PowerSeries.X : PowerSeries k) ^ i !).order =
      ((N + 1)! : ℕ) := by
  rw [← algebraMap_partialSum]
  exact order_sub_partialSum N

/-! ### The arc valuation -/

variable (k) in
/-- The arc `t ↦ (t, φ(t))` of Volume 3, Example 1.6.6 of the handbook, as the substitution
`x ↦ t`, `y ↦ φ` from `k[x, y]` to `k[[t]]`. The variable `x` is `X 0` and `y` is `X 1`. -/
noncomputable def arcEval : MvPolynomial (Fin 2) k →ₐ[k] PowerSeries k :=
  MvPolynomial.aeval ![PowerSeries.X, factorialSeries k]

/-- The value `v_φ(f) = ord_t f(t, φ(t))` of a polynomial `f` in `k[x, y]`. -/
noncomputable def arcOrder (f : MvPolynomial (Fin 2) k) : ℕ∞ :=
  (arcEval k f).order

/-- `v(y - ∑_{i=1}^N x^{i!}) = (N + 1)!`. -/
theorem arcOrder_Y_sub_sum (N : ℕ) :
    arcOrder (MvPolynomial.X 1 - ∑ i ∈ Finset.Icc 1 N, MvPolynomial.X 0 ^ i ! :
      MvPolynomial (Fin 2) k) = ((N + 1)! : ℕ) := by
  rw [arcOrder, arcEval, map_sub, map_sum]
  simp only [map_pow, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact order_factorialSeries_sub_sum N

/-- `v(x) = 1`. -/
theorem arcOrder_X : arcOrder (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) = 1 := by
  simp [arcOrder, arcEval]

/-- `v(y) = 1`. -/
theorem arcOrder_Y : arcOrder (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) = 1 := by
  simpa using arcOrder_Y_sub_sum (k := k) 0

/-- `v(y - x) = 2`. -/
theorem arcOrder_Y_sub_X :
    arcOrder (MvPolynomial.X 1 - MvPolynomial.X 0 : MvPolynomial (Fin 2) k) = 2 := by
  have h := arcOrder_Y_sub_sum (k := k) 1
  simpa [Finset.sum_Icc_succ_top] using h

/-- `v(y - x - x^2) = 6`. -/
theorem arcOrder_Y_sub_X_sub_X_sq :
    arcOrder (MvPolynomial.X 1 - MvPolynomial.X 0 - MvPolynomial.X 0 ^ 2 :
      MvPolynomial (Fin 2) k) = 6 := by
  have h := arcOrder_Y_sub_sum (k := k) 2
  have e : (MvPolynomial.X 1 - ∑ i ∈ Finset.Icc 1 2, MvPolynomial.X 0 ^ i ! :
      MvPolynomial (Fin 2) k) = MvPolynomial.X 1 - MvPolynomial.X 0 - MvPolynomial.X 0 ^ 2 := by
    simp [Finset.sum_Icc_succ_top, Nat.factorial]
    ring
  rw [e] at h
  rw [h]
  rfl

/-- `v(y - x - x^2 - x^6) = 24`. -/
theorem arcOrder_Y_sub_X_sub_X_sq_sub_X_pow_six :
    arcOrder (MvPolynomial.X 1 - MvPolynomial.X 0 - MvPolynomial.X 0 ^ 2 -
      MvPolynomial.X 0 ^ 6 : MvPolynomial (Fin 2) k) = 24 := by
  have h := arcOrder_Y_sub_sum (k := k) 3
  have e : (MvPolynomial.X 1 - ∑ i ∈ Finset.Icc 1 3, MvPolynomial.X 0 ^ i ! :
      MvPolynomial (Fin 2) k) =
      MvPolynomial.X 1 - MvPolynomial.X 0 - MvPolynomial.X 0 ^ 2 - MvPolynomial.X 0 ^ 6 := by
    simp [Finset.sum_Icc_succ_top, Nat.factorial]
    ring
  rw [e] at h
  rw [h]
  rfl

/-- Each monomial of `y - x` has total degree `1`. So the monomial valuation with weights
`(1, 1)` gives `y - x` the value `1`. -/
theorem degree_eq_one_of_mem_support_Y_sub_X {d : Fin 2 →₀ ℕ}
    (hd : d ∈ (MvPolynomial.X 1 - MvPolynomial.X 0 : MvPolynomial (Fin 2) k).support) :
    d 0 + d 1 = 1 := by
  have h := MvPolynomial.support_sub (Fin 2) (MvPolynomial.X 1 : MvPolynomial (Fin 2) k)
    (MvPolynomial.X 0) hd
  rw [Finset.mem_union, MvPolynomial.support_X, MvPolynomial.support_X,
    Finset.mem_singleton, Finset.mem_singleton] at h
  rcases h with rfl | rfl <;> simp

/-- The arc valuation is not the monomial valuation with weights `(1, 1)`. Both give `x` and
`y` the value `1`, and each monomial of `y - x` has weight `1`, but `v(y - x) = 2 ≠ 1`. -/
theorem arcOrder_ne_monomial_one_one :
    arcOrder (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) = 1 ∧
      arcOrder (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) = 1 ∧
      (∀ d ∈ (MvPolynomial.X 1 - MvPolynomial.X 0 : MvPolynomial (Fin 2) k).support,
        d 0 + d 1 = 1) ∧
      arcOrder (MvPolynomial.X 1 - MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ≠ 1 := by
  refine ⟨arcOrder_X, arcOrder_Y, fun d hd => degree_eq_one_of_mem_support_Y_sub_X hd, ?_⟩
  rw [arcOrder_Y_sub_X]
  decide

/-! ### The chart `y_1 = y / x` of the blowup -/

variable (k) in
/-- The series `φ / t = 1 + t + t^5 + t^23 + ...`. Its coefficient of `t^n` is the coefficient
of `t^{n+1}` in `φ`. -/
noncomputable def factorialSeriesDivX : PowerSeries k :=
  PowerSeries.mk fun n => PowerSeries.coeff (n + 1) (factorialSeries k)

/-- `t · (φ / t) = φ`. -/
theorem X_mul_factorialSeriesDivX :
    PowerSeries.X * factorialSeriesDivX k = factorialSeries k := by
  ext n
  rcases n with _ | n
  · rw [PowerSeries.coeff_zero_X_mul, coeff_factorialSeries]
    simp
  · rw [PowerSeries.coeff_succ_X_mul, factorialSeriesDivX, PowerSeries.coeff_mk]

/-- The coefficient of `t^n` in `φ / t` is `1` if `n + 1 = i!` for some `i ≥ 1`, and `0`
otherwise. -/
theorem coeff_factorialSeriesDivX (n : ℕ) :
    PowerSeries.coeff n (factorialSeriesDivX k) =
      if n + 1 ∈ (Finset.Icc 1 (n + 1)).image Nat.factorial then 1 else 0 := by
  rw [factorialSeriesDivX, PowerSeries.coeff_mk, coeff_factorialSeries]

/-- The order of `φ / t - ∑_{i=1}^N t^{i! - 1}` is `(N + 1)! - 1`. -/
theorem order_factorialSeriesDivX_sub_sum (N : ℕ) :
    (factorialSeriesDivX k -
      ∑ i ∈ Finset.Icc 1 N, (PowerSeries.X : PowerSeries k) ^ (Nat.factorial i - 1)).order =
      ((N + 1)! - 1 : ℕ) := by
  have hmul : PowerSeries.X * (factorialSeriesDivX k -
      ∑ i ∈ Finset.Icc 1 N, (PowerSeries.X : PowerSeries k) ^ (Nat.factorial i - 1)) =
      factorialSeries k - ∑ i ∈ Finset.Icc 1 N, (PowerSeries.X : PowerSeries k) ^ i ! := by
    rw [mul_sub, X_mul_factorialSeriesDivX, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_succ']
    congr 1
    have := Nat.factorial_pos i
    omega
  have h := order_factorialSeries_sub_sum (k := k) N
  rw [← hmul, PowerSeries.order_mul, PowerSeries.order_X] at h
  generalize (factorialSeriesDivX k -
      ∑ i ∈ Finset.Icc 1 N, (PowerSeries.X : PowerSeries k) ^ (Nat.factorial i - 1)).order = o
    at h ⊢
  have hpos := Nat.factorial_pos (N + 1)
  induction o using ENat.recTopCoe with
  | top => simp at h
  | coe m =>
    have h' : 1 + m = (N + 1)! := by exact_mod_cast h
    exact_mod_cast (by omega : m = (N + 1)! - 1)

variable (k) in
/-- The arc in the chart `Spec k[x, y_1]` of the blowup of the origin, with `y_1 = y / x`:
`x ↦ t`, `y_1 ↦ φ / t`. The variable `x` is `X 0` and `y_1` is `X 1`. -/
noncomputable def chartArcEval : MvPolynomial (Fin 2) k →ₐ[k] PowerSeries k :=
  MvPolynomial.aeval ![PowerSeries.X, factorialSeriesDivX k]

/-- The value of a polynomial in `k[x, y_1]` along the arc. -/
noncomputable def chartArcOrder (f : MvPolynomial (Fin 2) k) : ℕ∞ :=
  (chartArcEval k f).order

/-- The chart arc lifts the arc: composing with the blowup map `x ↦ x`, `y ↦ x y_1` gives
`arcEval`. -/
theorem chartArcEval_comp_blowup :
    (chartArcEval k).comp
      (MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 0 * MvPolynomial.X 1]) =
      arcEval k := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simp [chartArcEval, arcEval]
  · simp [chartArcEval, arcEval, X_mul_factorialSeriesDivX]

/-- In the chart, `v(x) = 1`. -/
theorem chartArcOrder_X : chartArcOrder (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) = 1 := by
  simp [chartArcOrder, chartArcEval]

/-- In the chart, `v(y_1 - 1) = 1`. -/
theorem chartArcOrder_Y_sub_one :
    chartArcOrder (MvPolynomial.X 1 - 1 : MvPolynomial (Fin 2) k) = 1 := by
  have h := order_factorialSeriesDivX_sub_sum (k := k) 1
  simp only [Finset.Icc_self, Finset.sum_singleton] at h
  rw [chartArcOrder, chartArcEval, map_sub, map_one, MvPolynomial.aeval_X]
  simpa using h

/-- In the chart, `v(y_1) = 0`. -/
theorem chartArcOrder_Y : chartArcOrder (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) = 0 := by
  rw [chartArcOrder, chartArcEval, MvPolynomial.aeval_X,
    show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, PowerSeries.order_eq_nat]
  refine ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  change PowerSeries.coeff 0 (factorialSeriesDivX k) ≠ 0
  rw [coeff_factorialSeriesDivX, if_pos (by decide)]
  exact one_ne_zero

end FactorialSeries

end Singularity
