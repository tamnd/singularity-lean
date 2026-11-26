/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.Polynomial.Roots

/-!
# The series `∑ t^{i!}` is transcendental

Let `k` be a field. This file proves that the power series `φ = ∑_{i ≥ 1} t^{i!}` is transcendental over `k(t)` (Volume 3, Lemma 1.6.5 of the handbook). The series is `Singularity.factorialSeries k`.

The proof is the gap argument of Liouville of the handbook. Let `P ≠ 0` be a polynomial in `Y` with coefficients in `k[t]`, with `P(φ) = 0`. Let `d` be the degree of `P` in `Y`, and let `c` bound the degrees of the coefficients. Let `φ_N = ∑_{i=1}^N t^{i!}`, a polynomial of degree at most `N!`.

1. The difference `φ - φ_N` is divisible by `t^{(N+1)!}`, and `φ - φ_N` divides `P(φ) - P(φ_N) = -P(φ_N)`. So `t^{(N+1)!}` divides the polynomial `P(φ_N)`.
2. The polynomial `P(φ_N)` has degree at most `c + d N!`. If it is not zero, then `(N + 1)! ≤ c + d N!`. This is false for `N > c + d`.
3. So `P(φ_N) = 0` for each `N > c + d`. The polynomials `φ_N` are distinct, so `P` has infinitely many roots in `k[t]`, and `P = 0`.

The handbook uses the minimal polynomial of `φ` to get `P(φ_N) ≠ 0`. The proof here uses step 3 instead: a nonzero polynomial over the domain `k[t]` has only finitely many roots.

The transcendence over `k[t]` is the statement with polynomials: no nonzero polynomial with coefficients in `k[t]` vanishes at `φ`. The transcendence over `k(t)` follows, because `k(t)` is the field of fractions of `k[t]`. For this statement, `φ` is an element of the field of Laurent series, which contains `k(t)`.

## Main results

* `Singularity.factorialSeries`: the series `∑_{i ≥ 1} t^{i!}`.
* `Singularity.transcendental_factorialSeries`: it is transcendental over `k[t]`.
* `Singularity.aeval_factorialSeries_ne_zero`: no nonzero polynomial with coefficients in `k[t]` vanishes at it.
* `Singularity.transcendental_factorialSeries_ratFunc`: as a Laurent series, it is transcendental over `k(t)`.
-/

open Polynomial
open scoped Nat

namespace Singularity

variable (k : Type*) [Field k]

/-- The power series `φ = ∑_{i ≥ 1} t^{i!}` of Volume 3, Lemma 1.6.5 of the handbook. The coefficient of `t^n` is `1` if `n = i!` for some `i ≥ 1`, and `0` otherwise. Such an `i` is at most `n`. -/
noncomputable def factorialSeries : PowerSeries k :=
  PowerSeries.mk fun n => if ∃ i ∈ Finset.Icc 1 n, i ! = n then 1 else 0

namespace FactorialSeries

/-- The partial sum `φ_N = ∑_{i=1}^N t^{i!}`, a polynomial. -/
noncomputable def partialSum (N : ℕ) : k[X] :=
  ∑ i ∈ Finset.Icc 1 N, X ^ i !

variable {k}

/-- The factorial is injective on the integers `≥ 1`. -/
theorem factorial_inj_of_one_le {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (h : i ! = j !) : i = j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd h ((Nat.factorial_lt (by omega)).mpr hlt).ne
  · exact heq
  · exact absurd h ((Nat.factorial_lt (by omega)).mpr hgt).ne'

/-- The coefficients of the partial sum. -/
theorem coeff_partialSum (N m : ℕ) :
    (partialSum k N).coeff m = if ∃ i ∈ Finset.Icc 1 N, i ! = m then 1 else 0 := by
  rw [partialSum, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_X_pow]
  split_ifs with h
  · obtain ⟨i, hi, rfl⟩ := h
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      rw [if_neg]
      intro hij
      exact hji (factorial_inj_of_one_le (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hi).1
        hij.symm)
    · intro hi'
      exact absurd hi hi'
  · apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg]
    intro hmj
    exact h ⟨j, hj, hmj.symm⟩

/-- The coefficients of the series. -/
theorem coeff_factorialSeries (n : ℕ) :
    PowerSeries.coeff n (factorialSeries k) =
      if ∃ i ∈ Finset.Icc 1 n, i ! = n then 1 else 0 := by
  rw [factorialSeries, PowerSeries.coeff_mk]

/-- Below `(N + 1)!`, the series and the partial sum have the same exponents. -/
theorem exists_iff_of_lt {N m : ℕ} (hm : m < (N + 1)!) :
    (∃ i ∈ Finset.Icc 1 m, i ! = m) ↔ ∃ i ∈ Finset.Icc 1 N, i ! = m := by
  constructor
  · rintro ⟨i, hi, him⟩
    have hi1 := (Finset.mem_Icc.mp hi).1
    have hlt : i ! < (N + 1)! := by rw [him]; exact hm
    have hiN : i < N + 1 := (Nat.factorial_lt (by omega)).mp hlt
    exact ⟨i, Finset.mem_Icc.mpr ⟨hi1, by omega⟩, him⟩
  · rintro ⟨i, hi, him⟩
    have hle : i ≤ m := by rw [← him]; exact Nat.self_le_factorial i
    exact ⟨i, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, hle⟩, him⟩

/-- The coefficients of the image of a polynomial in the power series. -/
theorem coeff_algebraMap (p : k[X]) (m : ℕ) :
    PowerSeries.coeff m (algebraMap k[X] (PowerSeries k) p) = p.coeff m := by
  rw [PowerSeries.algebraMap_apply', PowerSeries.coeff_map, Polynomial.coeff_coe]
  rfl

/-- `t^{(N+1)!}` divides `φ - φ_N`. -/
theorem X_pow_dvd_sub_partialSum (N : ℕ) :
    (PowerSeries.X : PowerSeries k) ^ (N + 1)! ∣
      factorialSeries k - algebraMap k[X] (PowerSeries k) (partialSum k N) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  rw [map_sub, coeff_factorialSeries, coeff_algebraMap, coeff_partialSum]
  exact sub_eq_zero.mpr (if_congr (exists_iff_of_lt hm) rfl rfl)

/-- The degree of the partial sum `φ_N` is at most `N!`. -/
theorem natDegree_partialSum_le (N : ℕ) : (partialSum k N).natDegree ≤ N ! := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_X_pow_le _).trans (Nat.factorial_le (Finset.mem_Icc.mp hi).2)

/-- The partial sums are distinct: `φ_M ≠ φ_N` for `M < N`, because the coefficient of `t^{N!}` is `0` in `φ_M` and `1` in `φ_N`. -/
theorem partialSum_ne_of_lt {M N : ℕ} (h : M < N) : partialSum k M ≠ partialSum k N := by
  intro heq
  have h1 : (partialSum k M).coeff N ! = (partialSum k N).coeff N ! := by rw [heq]
  have hpos : ∃ i ∈ Finset.Icc 1 N, i ! = N ! := ⟨N, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, rfl⟩
  have hneg : ¬ ∃ i ∈ Finset.Icc 1 M, i ! = N ! := by
    rintro ⟨i, hi, hiN⟩
    have hi' := Finset.mem_Icc.mp hi
    have := factorial_inj_of_one_le hi'.1 (by omega) hiN
    omega
  rw [coeff_partialSum, coeff_partialSum, if_pos hpos, if_neg hneg] at h1
  exact zero_ne_one h1

/-- The map `N ↦ φ_N` is injective. -/
theorem partialSum_injective : Function.Injective (partialSum k) := by
  intro M N h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact partialSum_ne_of_lt hlt h
  · exact partialSum_ne_of_lt hlt h.symm

/-- A bound for the degrees of the coefficients of a polynomial over `k[t]`. -/
theorem exists_natDegree_coeff_le (P : k[X][X]) : ∃ c : ℕ, ∀ j, (P.coeff j).natDegree ≤ c := by
  refine ⟨(Finset.range (P.natDegree + 1)).sup fun j => (P.coeff j).natDegree, fun j => ?_⟩
  by_cases hj : j ≤ P.natDegree
  · exact Finset.le_sup (f := fun j => (P.coeff j).natDegree)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hj), Polynomial.natDegree_zero]
    exact Nat.zero_le _

/-- The degree of `P(q)` is at most `c + d e`, if `P` has degree `d` in `Y`, its coefficients have degree at most `c`, and `q` has degree at most `e`. -/
theorem natDegree_eval_le (P : k[X][X]) (q : k[X]) {c e : ℕ}
    (hc : ∀ j, (P.coeff j).natDegree ≤ c) (hq : q.natDegree ≤ e) :
    (P.eval q).natDegree ≤ c + P.natDegree * e := by
  rw [Polynomial.eval_eq_sum_range]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have hj' : j ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  calc (P.coeff j * q ^ j).natDegree
      ≤ (P.coeff j).natDegree + (q ^ j).natDegree := Polynomial.natDegree_mul_le
    _ ≤ c + j * e :=
        add_le_add (hc j) (Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul le_rfl hq))
    _ ≤ c + P.natDegree * e := add_le_add le_rfl (Nat.mul_le_mul hj' le_rfl)

/-- A nonzero polynomial over `k` whose coefficients below `n` vanish has degree at least `n`. -/
theorem le_natDegree_of_coeff_eq_zero {Q : k[X]} (hQ : Q ≠ 0) {n : ℕ}
    (h : ∀ m < n, Q.coeff m = 0) : n ≤ Q.natDegree := by
  by_contra hlt
  exact hQ (Polynomial.leadingCoeff_eq_zero.mp (h _ (not_le.mp hlt)))

/-- The gap argument. If `P(φ) = 0`, then `P(φ_N) = 0` for each `N > c + d`. -/
theorem eval_partialSum_eq_zero {P : k[X][X]} (h : aeval (factorialSeries k) P = 0) {c : ℕ}
    (hc : ∀ j, (P.coeff j).natDegree ≤ c) {N : ℕ} (hN : c + P.natDegree < N) :
    P.eval (partialSum k N) = 0 := by
  by_contra hQ
  have h1 : (PowerSeries.X : PowerSeries k) ^ (N + 1)! ∣
      algebraMap k[X] (PowerSeries k) (P.eval (partialSum k N)) := by
    have h2 := Polynomial.sub_dvd_eval_sub (factorialSeries k)
      (algebraMap k[X] (PowerSeries k) (partialSum k N)) (P.map (algebraMap k[X] (PowerSeries k)))
    rw [Polynomial.eval_map_algebraMap, Polynomial.eval_map_algebraMap, h,
      Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, zero_sub] at h2
    exact dvd_neg.mp ((X_pow_dvd_sub_partialSum N).trans h2)
  have h3 : (N + 1)! ≤ (P.eval (partialSum k N)).natDegree := by
    refine le_natDegree_of_coeff_eq_zero hQ fun m hm => ?_
    rw [← coeff_algebraMap]
    exact PowerSeries.X_pow_dvd_iff.mp h1 m hm
  have h4 := natDegree_eval_le P (partialSum k N) hc (natDegree_partialSum_le N)
  have h5 : (N + 1)! = (N + 1) * N ! := Nat.factorial_succ N
  have h6 : 1 ≤ N ! := Nat.factorial_pos N
  have h7 : (c + P.natDegree + 1) * N ! ≤ N * N ! := Nat.mul_le_mul (by omega) le_rfl
  have h8 : c * 1 ≤ c * N ! := Nat.mul_le_mul le_rfl h6
  nlinarith [h3, h4, h5, h6, h7, h8]

end FactorialSeries

open FactorialSeries

/-- **The series `∑ t^{i!}` is transcendental** (Volume 3, Lemma 1.6.5 of the handbook, the form with polynomials). The power series `φ = ∑_{i ≥ 1} t^{i!}` is transcendental over `k[t]`. -/
theorem transcendental_factorialSeries : Transcendental k[X] (factorialSeries k) := by
  rintro ⟨P, hP, h⟩
  obtain ⟨c, hc⟩ := exists_natDegree_coeff_le P
  apply hP
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => partialSum k (n + c + P.natDegree + 1)) ?_ ?_
  · intro m n hmn
    have := partialSum_injective hmn
    omega
  · intro n
    show P.eval (partialSum k (n + c + P.natDegree + 1)) = 0
    exact eval_partialSum_eq_zero h hc (by omega)

/-- No nonzero polynomial `P(t, Y)` with coefficients in `k[t]` vanishes at `Y = φ` (Volume 3, Lemma 1.6.5 of the handbook). -/
theorem aeval_factorialSeries_ne_zero {P : k[X][X]} (hP : P ≠ 0) :
    aeval (factorialSeries k) P ≠ 0 :=
  fun h => transcendental_factorialSeries k ⟨P, hP, h⟩

open scoped RatFunc in
/-- **The series `∑ t^{i!}` is transcendental over `k(t)`** (Volume 3, Lemma 1.6.5 of the handbook). The image of `φ = ∑_{i ≥ 1} t^{i!}` in the field of Laurent series `k((t))` is transcendental over the field of rational functions `k(t)`. -/
theorem transcendental_factorialSeries_ratFunc :
    Transcendental (RatFunc k) (HahnSeries.ofPowerSeries ℤ k (factorialSeries k)) := by
  have h1 : Transcendental k[X] (HahnSeries.ofPowerSeries ℤ k (factorialSeries k)) := by
    haveI : IsScalarTower k[X] (PowerSeries k) (LaurentSeries k) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hinj : Function.Injective (algebraMap (PowerSeries k) (LaurentSeries k)) :=
      HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := k)
    exact (transcendental_algebraMap_iff (R := k[X]) (S := PowerSeries k) (A := LaurentSeries k)
      hinj).mpr (transcendental_factorialSeries k)
  exact (IsFractionRing.isAlgebraic_iff k[X] (RatFunc k) (LaurentSeries k)).not.mp h1

end Singularity
