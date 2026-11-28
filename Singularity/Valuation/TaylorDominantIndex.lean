/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Basic.Real.Basic

/-!
# The Taylor expansion and the dominant index

Let `v` be a valuation on a field `L`, let `f ∈ L[X]`, and let `c, x ∈ L`. Write `f_k` for the `k`-th Hasse derivative `Polynomial.hasseDeriv k f`, so that `f(x) = ∑_k f_k(c) (x - c)^k`. This file proves the elementary valuation lemmas on this expansion that the cone argument of the handbook uses.

The valuations are multiplicative, as in the other files of the repository: `v : Valuation L Γ₀` with `Γ₀` a `LinearOrderedCommGroupWithZero`. A large additive value is a small multiplicative value. So the additive expression `min_k (v(f_k(c)) + k v(x - c))` of the handbook becomes `max_k (v(f_k(c)) * v(x - c)^k)`, the additive inequality `≥` becomes `≤`, and "strictly smaller additive value" becomes "strictly larger multiplicative value".

## Main results

* `Singularity.eval_sub_eval_eq_sum_hasseDeriv`: the Taylor formula `f(x) - f(c) = ∑_{1 ≤ k ≤ n} f_k(c) (x - c)^k` for each `n ≥ deg f`.
* `Singularity.valuation_eval_sub_eval_le`: the Taylor bound. If `v(f_k(c)) * v(x - c)^k ≤ g` for each `1 ≤ k ≤ deg f`, then `v(f(x) - f(c)) ≤ g`. In additive notation, `v(f(x) - f(c)) ≥ min_{k ≥ 1} (v(f_k(c)) + k v(x - c))`.
* `Singularity.valuation_eval_sub_eval_eq_of_dominant`: the dominant index. If the term of index `k_*` has a value strictly larger (multiplicatively) than each other term of index `1 ≤ k ≤ deg f`, then `v(f(x) - f(c)) = v(f_{k_*}(c)) * v(x - c)^{k_*}`.
* `Singularity.valuation_eval_eq_of_constant_dominant`: the case where the constant term dominates. If `v(f_j(c)) * v(x - c)^j < v(f(c))` for each `1 ≤ j ≤ deg f`, then `v(f(x)) = v(f(c))`.
* `Singularity.valuation_eval_hasseDeriv_eq_of_lt`: the stability of the Taylor coefficients, the elementary part of Lemma 4.5.9. Let `k` be an index. If `v(f_{j+k}(c)) * v(c' - c)^j < v(f_k(c))` for each `1 ≤ j ≤ deg f - k`, then `v(f_k(c')) = v(f_k(c))`.
* `Singularity.valuation_eval_hasseDeriv_eq_of_choose_lt`: the same with the weaker hypothesis that uses the true Taylor coefficients `C(j + k, j) f_{j+k}(c)` of `f_k` at `c`.
* `Singularity.exists_dominant_index_window`: the window of Lemma 4.5.11. Let `φ_k` and `Λ` be real numbers, and let `k_*` be the largest index of a finite set `S` where `φ_k + k Λ` has its minimum. Then there is `κ_0 > 0` such that `k_*` is the only index of the minimum of `φ_k + k λ` on `S` for each `λ` in `(Λ - κ_0, Λ)`.

## The proof

The Taylor formula comes from `Polynomial.taylor_eval` and `Polynomial.taylor_coeff`. The bound is the ultrametric inequality `Valuation.map_sum_le`. The general lemma on a finite sum with one strictly dominant term is in Mathlib: `Valuation.map_sum_eq_of_lt`. The dominant index is this lemma applied to the Taylor sum. The stability of `f_k` is the case of a dominant constant term, applied to the polynomial `f_k`. Its Taylor coefficients are `(f_k)_j = C(j + k, j) f_{j+k}` (`Polynomial.hasseDeriv_comp`), and `v(C(j + k, j)) ≤ 1`. The window of Lemma 4.5.11 follows the proof of the handbook: an index `k < k_*` with the same value at `Λ` is larger for each `λ < Λ`, and an index with a strictly larger value at `Λ` stays larger for `λ` near `Λ`. A finite number of windows have a common window.

## What is not proved

* Lemma 4.5.9 of the handbook in full is not proved. Its part 1 uses pseudo Cauchy sequences of transcendental type and the field of admissible series. Part 2 is proved here only pointwise: the file does not prove that the set `E_h` of the exceptional values is finite.
* Lemma 4.5.10 (the dominant index is a power of `p`) is not proved, so the part of Lemma 4.5.11 that says that `k_*` is a power of `p` is not proved. The window of Lemma 4.5.11 is proved for real numbers `φ_k` and `Λ`. The file does not connect these real numbers to the values `v(f_k(x))` and to the supremum `Λ(x)` of the handbook, which need a valuation of rank one and an immediate extension.
* Theorem 4.5.14 (Theorem C) and Theorem 4.5.16 (Theorem MC+) of the handbook are not proved.
* Local uniformization in positive characteristic and dimension 4 or more is open. This file does not prove it, and it does not prove a part of a proof of it.

## References

* The handbook, Volume 5, Chapter 4, the section on the cone argument: Lemma 4.5.9 (stability, part 2, and the stability of the coefficients that the proof of Theorem 4.5.14 uses) and Lemma 4.5.11 (the dominant index).
* I. Kaplansky, "Maximal fields with valuations", Duke Math. J. 9 (1942), for the classical forms.
-/

open Finset Polynomial

namespace Singularity

variable {L Γ₀ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)

/-- The Taylor formula: for each `n ≥ deg f`, `f(x) = ∑_{0 ≤ k ≤ n} f_k(c) (x - c)^k`, with `f_k` the `k`-th Hasse derivative of `f`. -/
theorem eval_eq_sum_hasseDeriv (f : L[X]) {n : ℕ} (hn : f.natDegree ≤ n) (c x : L) :
    f.eval x = ∑ k ∈ Icc 0 n, (hasseDeriv k f).eval c * (x - c) ^ k := by
  have h : (taylor c f).natDegree < n + 1 := by rw [natDegree_taylor]; omega
  rw [← taylor_eval_sub c, eval_eq_sum_range' h, range_eq_Ico, Ico_add_one_right_eq_Icc]
  simp only [taylor_coeff]

/-- The Taylor formula for the difference: for each `n ≥ deg f`, `f(x) - f(c) = ∑_{1 ≤ k ≤ n} f_k(c) (x - c)^k`. -/
theorem eval_sub_eval_eq_sum_hasseDeriv (f : L[X]) {n : ℕ} (hn : f.natDegree ≤ n) (c x : L) :
    f.eval x - f.eval c = ∑ k ∈ Icc 1 n, (hasseDeriv k f).eval c * (x - c) ^ k := by
  rw [eval_eq_sum_hasseDeriv f hn c x, ← insert_Icc_add_one_left_eq_Icc (Nat.zero_le n),
    sum_insert (by simp)]
  simp

/-- **The Taylor bound.** If `v(f_k(c)) * v(x - c)^k ≤ g` for each `1 ≤ k ≤ deg f`, then `v(f(x) - f(c)) ≤ g`. In additive notation: `v(f(x) - f(c)) ≥ min_{k ≥ 1} (v(f_k(c)) + k v(x - c))`. -/
theorem valuation_eval_sub_eval_le (f : L[X]) (c x : L) {g : Γ₀}
    (hg : ∀ k ∈ Icc 1 f.natDegree, v ((hasseDeriv k f).eval c) * v (x - c) ^ k ≤ g) :
    v (f.eval x - f.eval c) ≤ g := by
  rw [eval_sub_eval_eq_sum_hasseDeriv f le_rfl c x]
  exact v.map_sum_le fun k hk => by rw [map_mul, map_pow]; exact hg k hk

/-- **The dominant index.** Let `1 ≤ k_* ≤ deg f`, and assume that the term of index `k_*` has a value strictly larger (multiplicatively) than each other term of index `1 ≤ k ≤ deg f`. Then `v(f(x) - f(c)) = v(f_{k_*}(c)) * v(x - c)^{k_*}`. In additive notation: if the minimum of `v(f_k(c)) + k v(x - c)` is attained only at `k_*`, then `v(f(x) - f(c))` is this minimum. -/
theorem valuation_eval_sub_eval_eq_of_dominant (f : L[X]) (c x : L) {kstar : ℕ}
    (hk : kstar ∈ Icc 1 f.natDegree)
    (hlt : ∀ k ∈ Icc 1 f.natDegree, k ≠ kstar →
      v ((hasseDeriv k f).eval c) * v (x - c) ^ k <
        v ((hasseDeriv kstar f).eval c) * v (x - c) ^ kstar) :
    v (f.eval x - f.eval c) = v ((hasseDeriv kstar f).eval c) * v (x - c) ^ kstar := by
  rw [eval_sub_eval_eq_sum_hasseDeriv f le_rfl c x, v.map_sum_eq_of_lt hk, map_mul, map_pow]
  intro k hk'
  rw [mem_sdiff, mem_singleton] at hk'
  rw [map_mul, map_pow, map_mul, map_pow]
  exact hlt k hk'.1 hk'.2

/-- **A dominant constant term.** If `v(f_j(c)) * v(x - c)^j < v(f(c))` for each `1 ≤ j ≤ deg f`, then `v(f(x)) = v(f(c))`. In additive notation: if `v(f_j(c)) + j v(x - c) > v(f(c))` for each `j ≥ 1`, then `v(f(x)) = v(f(c))`. -/
theorem valuation_eval_eq_of_constant_dominant (f : L[X]) (c x : L)
    (hlt : ∀ j ∈ Icc 1 f.natDegree, v ((hasseDeriv j f).eval c) * v (x - c) ^ j < v (f.eval c)) :
    v (f.eval x) = v (f.eval c) := by
  rw [eval_eq_sum_hasseDeriv f le_rfl c x, v.map_sum_eq_of_lt (j := 0) (by simp)]
  · simp
  intro j hj
  rw [mem_sdiff, mem_singleton, mem_Icc] at hj
  rw [hasseDeriv_zero', pow_zero, mul_one, map_mul, map_pow]
  exact hlt j (mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hj.2, hj.1.2⟩)

/-- The value of a natural number is at most `1`. -/
theorem valuation_natCast_le_one (n : ℕ) : v (n : L) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ]; exact v.map_add_le ih (by rw [map_one])

/-- The Taylor coefficients of `f_k` are the multiples `C(j + k, j) f_{j+k}` of the Taylor coefficients of `f`. -/
theorem hasseDeriv_hasseDeriv_eq (f : L[X]) (j k : ℕ) :
    hasseDeriv j (hasseDeriv k f) = ((j + k).choose j : L[X]) * hasseDeriv (j + k) f := by
  have := congrArg (fun φ => φ f) (hasseDeriv_comp (R := L) j k)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply] at this
  rw [this, nsmul_eq_mul]

/-- **Stability of the Taylor coefficients**, the elementary form with the true Taylor coefficients of `f_k`. Let `k` be an index and `c, c' ∈ L`. If `v(C(j + k, j) f_{j+k}(c)) * v(c' - c)^j < v(f_k(c))` for each `1 ≤ j ≤ deg f - k`, then `v(f_k(c')) = v(f_k(c))`. -/
theorem valuation_eval_hasseDeriv_eq_of_choose_lt (f : L[X]) (k : ℕ) (c c' : L)
    (hlt : ∀ j ∈ Icc 1 (f.natDegree - k),
      v (((j + k).choose j : L) * (hasseDeriv (j + k) f).eval c) * v (c' - c) ^ j <
        v ((hasseDeriv k f).eval c)) :
    v ((hasseDeriv k f).eval c') = v ((hasseDeriv k f).eval c) := by
  have hdeg := natDegree_hasseDeriv_le f k
  rw [eval_eq_sum_hasseDeriv _ hdeg c c', v.map_sum_eq_of_lt (j := 0) (by simp)]
  · simp
  intro j hj
  rw [mem_sdiff, mem_singleton, mem_Icc] at hj
  rw [hasseDeriv_zero', pow_zero, mul_one, map_mul, map_pow, hasseDeriv_hasseDeriv_eq,
    eval_mul, eval_natCast]
  exact hlt j (mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hj.2, hj.1.2⟩)

/-- **Stability of the Taylor coefficients** (the elementary part of Volume 5, Lemma 4.5.9 of the handbook). Let `k` be an index and `c, c' ∈ L`. If `v(f_{j+k}(c)) * v(c' - c)^j < v(f_k(c))` for each `1 ≤ j ≤ deg f - k`, then `v(f_k(c')) = v(f_k(c))`. In additive notation: if `v(f_{j+k}(c)) + j v(c' - c) > v(f_k(c))` for each `j ≥ 1`, then `v(f_k(c')) = v(f_k(c))`. -/
theorem valuation_eval_hasseDeriv_eq_of_lt (f : L[X]) (k : ℕ) (c c' : L)
    (hlt : ∀ j ∈ Icc 1 (f.natDegree - k),
      v ((hasseDeriv (j + k) f).eval c) * v (c' - c) ^ j < v ((hasseDeriv k f).eval c)) :
    v ((hasseDeriv k f).eval c') = v ((hasseDeriv k f).eval c) := by
  refine valuation_eval_hasseDeriv_eq_of_choose_lt v f k c c' fun j hj => ?_
  refine lt_of_le_of_lt ?_ (hlt j hj)
  rw [map_mul]
  exact mul_le_mul_left (mul_le_of_le_one_left' (valuation_natCast_le_one v _)) _

/-- One index of the window. Let `k, k_*` be indices with `φ_{k_*} + k_* Λ ≤ φ_k + k Λ`, and assume `k < k_*` if the two values are equal. Then there is `κ > 0` such that `φ_{k_*} + k_* λ < φ_k + k λ` for each `λ` with `Λ - κ < λ < Λ`. -/
theorem exists_dominant_index_lt (φ : ℕ → ℝ) (Λ : ℝ) {k kstar : ℕ}
    (hmin : φ kstar + kstar * Λ ≤ φ k + k * Λ)
    (hmax : φ k + k * Λ = φ kstar + kstar * Λ → k < kstar) :
    ∃ κ > 0, ∀ μ, Λ - κ < μ → μ < Λ → φ kstar + kstar * μ < φ k + k * μ := by
  rcases lt_or_ge k kstar with hk | hk
  · refine ⟨1, one_pos, fun μ _ hμ => ?_⟩
    have : (k : ℝ) < kstar := by exact_mod_cast hk
    nlinarith
  · have hlt : φ kstar + kstar * Λ < φ k + k * Λ :=
      lt_of_le_of_ne hmin fun h => absurd (hmax h.symm) (not_lt.mpr hk)
    have hk' : (kstar : ℝ) ≤ k := by exact_mod_cast hk
    have hpos : 0 < (k : ℝ) - kstar + 1 := by linarith
    have hδ : 0 < φ k + k * Λ - (φ kstar + kstar * Λ) := by linarith
    refine ⟨(φ k + k * Λ - (φ kstar + kstar * Λ)) / ((k : ℝ) - kstar + 1), div_pos hδ hpos,
      fun μ h1 h2 => ?_⟩
    have h3 : (Λ - μ) * ((k : ℝ) - kstar + 1) < φ k + k * Λ - (φ kstar + kstar * Λ) := by
      rw [← lt_div_iff₀ hpos]; linarith
    nlinarith

/-- A finite number of windows below `Λ` have a common window. -/
theorem exists_common_window (S : Finset ℕ) (Λ : ℝ) (Q : ℕ → ℝ → Prop)
    (h : ∀ k ∈ S, ∃ κ > 0, ∀ μ, Λ - κ < μ → μ < Λ → Q k μ) :
    ∃ κ > 0, ∀ μ, Λ - κ < μ → μ < Λ → ∀ k ∈ S, Q k μ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun _ _ _ k hk => absurd hk (notMem_empty k)⟩
  | insert a s _ ih =>
    obtain ⟨κa, hκa, ha⟩ := h a (mem_insert_self a s)
    obtain ⟨κs, hκs, hs⟩ := ih fun k hk => h k (mem_insert_of_mem hk)
    refine ⟨min κa κs, lt_min hκa hκs, fun μ h1 h2 k hk => ?_⟩
    rcases mem_insert.mp hk with rfl | hk
    · exact ha μ (by linarith [min_le_left κa κs]) h2
    · exact hs μ (by linarith [min_le_right κa κs]) h2 k hk

/-- **The window of the dominant index** (the elementary part of Volume 5, Lemma 4.5.11 of the handbook). Let `S` be a finite set of indices, let `φ_k` and `Λ` be real numbers, and let `k_*` be the largest index of `S` where `φ_k + k Λ` has its minimum on `S`. Then there is `κ_0 > 0` such that `φ_{k_*} + k_* λ < φ_k + k λ` for each `λ` with `Λ - κ_0 < λ < Λ` and each `k ∈ S` with `k ≠ k_*`. -/
theorem exists_dominant_index_window (S : Finset ℕ) (φ : ℕ → ℝ) (Λ : ℝ) {kstar : ℕ}
    (hmin : ∀ k ∈ S, φ kstar + kstar * Λ ≤ φ k + k * Λ)
    (hmax : ∀ k ∈ S, φ k + k * Λ = φ kstar + kstar * Λ → k ≤ kstar) :
    ∃ κ₀ > 0, ∀ μ, Λ - κ₀ < μ → μ < Λ → ∀ k ∈ S, k ≠ kstar →
      φ kstar + kstar * μ < φ k + k * μ :=
  exists_common_window S Λ _ fun k hk => by
    by_cases hne : k = kstar
    · exact ⟨1, one_pos, fun _ _ _ h => absurd hne h⟩
    · obtain ⟨κ, hκ, hw⟩ := exists_dominant_index_lt φ Λ (hmin k hk)
        fun h => lt_of_le_of_ne (hmax k hk h) hne
      exact ⟨κ, hκ, fun μ h1 h2 _ => hw μ h1 h2⟩

end Singularity
