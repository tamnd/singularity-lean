/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.Order

/-!
# The order of a sum of powers of ideals

Let `N ≥ 1`, let `B_j` be ideals of `R[x_i : i ∈ σ]`, and let `c_j` be integers that divide `N`. Let `B = ∑_j B_j^(N / c_j)`. This file proves that `B` has order at least `N` at the origin if and only if each `B_j` has order at least `c_j` there (`le_idealOrd_iSup_pow_iff`). This is Volume 2, Lemma 3.2.2 (1) of the handbook, at the origin of the affine space. It is the reason why the coefficient ideal `C(I) = ∑_j D^j(I)^(m!/(m-j))` with the mark `m!` has the same points of order at least the mark as the family of the marked ideals `(D^j(I), m - j)`.

The ring `R` has no zero divisors, so the order of a power is the multiple of the order (`Singularity.idealOrd_pow`). The order of a sum of ideals is the least of the orders. The family of ideals can be infinite.

The handbook asks `c_j ≥ 1`. This follows from `N ≥ 1` and `c_j ∣ N`.
-/

open MvPolynomial

namespace Singularity

variable {σ R : Type*} [CommSemiring R]

/-- The order of a sum of ideals is at least `n` if and only if the order of each ideal is at least `n`. -/
theorem le_idealOrd_iSup_iff {ι : Type*} (I : ι → Ideal (MvPolynomial σ R)) (n : ℕ) :
    (n : ℕ∞) ≤ idealOrd (⨆ j, I j) ↔ ∀ j, (n : ℕ∞) ≤ idealOrd (I j) := by
  simp only [le_idealOrd_iff, iSup_le_iff]

/-- For `N = c q` with `q ≥ 1`, `N ≤ q a` if and only if `c ≤ a`, in `ℕ∞`. -/
theorem natCast_mul_le_nsmul_iff {c q : ℕ} (hq : 0 < q) (a : ℕ∞) :
    ((c * q : ℕ) : ℕ∞) ≤ q • a ↔ (c : ℕ∞) ≤ a := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [succ_nsmul, add_top]
    exact ⟨fun _ => le_top, fun _ => le_top⟩
  · obtain ⟨r, rfl⟩ := ENat.ne_top_iff_exists.mp ha
    rw [nsmul_eq_mul]
    norm_cast
    constructor
    · intro h
      rw [mul_comm q r] at h
      exact Nat.le_of_mul_le_mul_right h hq
    · intro h
      rw [mul_comm q r]
      exact Nat.mul_le_mul_right q h

variable [NoZeroDivisors R] [Nontrivial R]

/-- **Volume 2, Lemma 3.2.2 (1) of the handbook**, at the origin. Let `N ≥ 1`, let `B_j` be ideals, and let `c_j` divide `N`. Then the ideal `B = ∑_j B_j^(N / c_j)` has order at least `N` at the origin if and only if `B_j` has order at least `c_j` there, for each `j`. -/
theorem le_idealOrd_iSup_pow_iff {ι : Type*} (B : ι → Ideal (MvPolynomial σ R)) (c : ι → ℕ)
    {N : ℕ} (hN : 1 ≤ N) (hc : ∀ j, c j ∣ N) :
    (N : ℕ∞) ≤ idealOrd (⨆ j, B j ^ (N / c j)) ↔ ∀ j, (c j : ℕ∞) ≤ idealOrd (B j) := by
  rw [le_idealOrd_iSup_iff]
  refine forall_congr' fun j => ?_
  rw [idealOrd_pow]
  obtain ⟨q, hq⟩ := hc j
  have hcj : 0 < c j := by
    rcases Nat.eq_zero_or_pos (c j) with h | h
    · rw [h, zero_mul] at hq
      omega
    · exact h
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, mul_zero] at hq
      omega
    · exact h
  rw [hq, Nat.mul_div_cancel_left q hcj]
  exact natCast_mul_le_nsmul_iff hq0 _

end Singularity
