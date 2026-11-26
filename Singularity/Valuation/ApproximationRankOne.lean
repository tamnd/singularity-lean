/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.RingTheory.Valuation.Basic

/-!
# Approximation for valuations of rank 1

Let `w_j` for `j ∈ ι` be finitely many valuations of a field `L` with archimedean value groups. This file proves the second part of the approximation lemma in rank 1 (Volume 3, Lemma 3.1.5 (2) of the handbook) from its first part.

Mathlib writes valuations multiplicatively, so `w(x) < 0` of the handbook is `1 < w(x)` here, and `w(u - 1) > γ` is `w(u - 1) < γ`. The value `γ` is a nonzero element of the value group.

The statement is `exists_approx_one_of_valuation`. Let `x ∈ L` with `1 < w_i(x)` and `w_j(x) < 1` for each `j ≠ i`. Then for each family of nonzero values `γ_j` there is `u ∈ L` with `w_i(u - 1) < γ_i` and `w_j(u) < γ_j` for each `j ≠ i`. The proof follows the handbook, with `u = x^m / (1 + x^m)` for a large `m`.

The file does not prove the first part of Lemma 3.1.5, the existence of `x`. So the hypothesis on `x` stays in the statement.
-/

namespace Singularity

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [MulArchimedean Γ₀]

/-- Let `a > 1` and `γ ≠ 0`. Then `γ⁻¹ < a^m` for each large `m`. -/
theorem exists_forall_inv_lt_pow {a : Γ₀} (ha : 1 < a) (γ : Γ₀) :
    ∃ N : ℕ, ∀ m, N ≤ m → γ⁻¹ < a ^ m := by
  obtain ⟨n, hn⟩ := MulArchimedean.arch γ⁻¹ ha
  refine ⟨n + 1, fun m hm => ?_⟩
  calc γ⁻¹ ≤ a ^ n := hn
    _ < a ^ (n + 1) := pow_lt_pow_right₀ ha (Nat.lt_succ_self n)
    _ ≤ a ^ m := pow_le_pow_right₀ ha.le hm

/-- Let `b < 1` and `γ ≠ 0`. Then `b^m < γ` for each large `m`. -/
theorem exists_forall_pow_lt {b : Γ₀} (hb : b < 1) {γ : Γ₀} (hγ : γ ≠ 0) :
    ∃ N : ℕ, ∀ m, N ≤ m → b ^ m < γ := by
  rcases eq_or_ne b 0 with h0 | h0
  · refine ⟨1, fun m hm => ?_⟩
    rw [h0, zero_pow (by omega)]
    exact zero_lt_iff.mpr hγ
  · have hb0 : 0 < b := zero_lt_iff.mpr h0
    obtain ⟨N, hN⟩ := exists_forall_inv_lt_pow ((one_lt_inv₀ hb0).mpr hb) γ
    refine ⟨N, fun m hm => ?_⟩
    have h := hN m hm
    rw [inv_pow] at h
    exact (inv_lt_inv₀ (zero_lt_iff.mpr hγ) (pow_pos hb0 m)).mp h

variable {L : Type*} [Field L] {ι : Type*} [Fintype ι] {Γ : ι → Type*}
  [∀ j, LinearOrderedCommGroupWithZero (Γ j)] [∀ j, MulArchimedean (Γ j)]

/-- **Approximation in rank 1** (Volume 3, Lemma 3.1.5 (2) of the handbook, from part (1)). Let `w_j` be valuations of `L` with archimedean value groups. Let `x ∈ L` with `1 < w_i(x)` and `w_j(x) < 1` for each `j ≠ i`. Let `γ_j ≠ 0` be values. Then there is `u ∈ L` with `w_i(u - 1) < γ_i` and `w_j(u) < γ_j` for each `j ≠ i`. In the additive notation of the handbook this is `w_i(u - 1) > γ_i` and `w_j(u) > γ_j`. -/
theorem exists_approx_one_of_valuation (w : ∀ j, Valuation L (Γ j)) (i : ι) {x : L}
    (hi : 1 < w i x) (hj : ∀ j, j ≠ i → w j x < 1) (γ : ∀ j, Γ j) (hγ : ∀ j, γ j ≠ 0) :
    ∃ u : L, w i (u - 1) < γ i ∧ ∀ j, j ≠ i → w j u < γ j := by
  classical
  have hN : ∀ j, ∃ N : ℕ, ∀ m, N ≤ m →
      (j = i → (γ j)⁻¹ < w j x ^ m) ∧ (j ≠ i → w j x ^ m < γ j) := by
    intro j
    by_cases hji : j = i
    · subst hji
      obtain ⟨N, hN⟩ := exists_forall_inv_lt_pow hi (γ j)
      exact ⟨N, fun m hm => ⟨fun _ => hN m hm, fun h => absurd rfl h⟩⟩
    · obtain ⟨N, hN⟩ := exists_forall_pow_lt (hj j hji) (hγ j)
      exact ⟨N, fun m hm => ⟨fun h => absurd h hji, fun _ => hN m hm⟩⟩
  choose N hN using hN
  let m := max 1 (Finset.univ.sup N)
  have hm1 : 1 ≤ m := le_max_left _ _
  have hmN : ∀ j, N j ≤ m := fun j =>
    (Finset.le_sup (f := N) (Finset.mem_univ j)).trans (le_max_right _ _)
  have hxi : 1 < w i (x ^ m) := by
    rw [map_pow]
    exact hi.trans_le (by simpa using pow_le_pow_right₀ hi.le hm1)
  have hone : w i (1 + x ^ m) = w i (x ^ m) := by
    rw [add_comm]
    exact (w i).map_add_eq_of_lt_left (by rwa [map_one])
  have hne : 1 + x ^ m ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hone
    rw [← hone] at hxi
    exact lt_irrefl _ (zero_lt_one.trans hxi)
  refine ⟨x ^ m * (1 + x ^ m)⁻¹, ?_, fun j hji => ?_⟩
  · have hu : x ^ m * (1 + x ^ m)⁻¹ - 1 = -(1 + x ^ m)⁻¹ := by
      have hc : (1 + x ^ m) * (1 + x ^ m)⁻¹ = 1 := mul_inv_cancel₀ hne
      linear_combination hc
    rw [hu, Valuation.map_neg, map_inv₀, hone, map_pow]
    exact inv_lt_of_inv_lt₀ (zero_lt_iff.mpr (hγ i)) ((hN i m (hmN i)).1 rfl)
  · have hxj : w j (x ^ m) < 1 := by
      rw [map_pow]
      exact pow_lt_one' (hj j hji) (by omega)
    rw [map_mul, map_inv₀, (w j).map_one_add_of_lt hxj, inv_one, mul_one, map_pow]
    exact (hN j m (hmN j)).2 hji

end Singularity
