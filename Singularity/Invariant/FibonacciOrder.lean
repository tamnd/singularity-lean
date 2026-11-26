/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Fib.Basic

/-!
# The Fibonacci numbers in the naive order reduction

This file checks the arithmetic of Volume 2, Example 3.3.9 of the handbook. Let `E^1` and `E^2` be smooth curves on a smooth surface that meet transversally at one point, and let `I = O(-(m+1)(E^1 + E^2))`. The naive method blows up the intersection point of the last two divisors `E^i` and `E^(i+1)`. The new divisor `E^(i+2)` gets the coefficient `a_i + a_(i+1) - m`, and the order of `I` at the point `E^i ∩ E^(i+1)` is `a_i + a_(i+1)`.

The coefficients are `Singularity.naiveCoeff m i`. The value at `i = 0` is `m`. It is not a coefficient of a divisor, and it only starts the recursion, so that `a_2 = a_0 + a_1 - m = m + 1`.

## Main results

* `Singularity.naiveCoeff_eq`: `a_i = m + F_i`, with `F_i` the Fibonacci numbers `0, 1, 1, 2, 3, 5, ...`.
* `Singularity.naiveCoeff_add`: the order at `E^i ∩ E^(i+1)` is `2m + F_(i+2)`.
* `Singularity.exists_lt_naiveCoeff_add`: the order at the intersection of the last two divisors grows without bound.

The geometric part of the example (the blowups of the surface, and the rule of Theorem 3.3.8 that ends after at most four blowups) is not formalized.
-/

namespace Singularity

/-- The coefficients `a_i` of the divisors `E^i` in the naive order reduction of Volume 2, Example 3.3.9 of the handbook, for the mark `m`. The recursion is `a_(i+2) = a_i + a_(i+1) - m`, with `a_1 = m + 1`, and with the auxiliary value `a_0 = m`. -/
def naiveCoeff (m : ℕ) : ℕ → ℕ
  | 0 => m
  | 1 => m + 1
  | i + 2 => naiveCoeff m i + naiveCoeff m (i + 1) - m

theorem naiveCoeff_add_two (m i : ℕ) :
    naiveCoeff m (i + 2) = naiveCoeff m i + naiveCoeff m (i + 1) - m := rfl

/-- **Volume 2, Example 3.3.9 of the handbook**, the coefficients. The coefficient of `E^i` is `m + F_i`, with `F_i` the Fibonacci numbers. -/
theorem naiveCoeff_eq (m i : ℕ) : naiveCoeff m i = m + Nat.fib i := by
  have key : ∀ i, naiveCoeff m i = m + Nat.fib i ∧ naiveCoeff m (i + 1) = m + Nat.fib (i + 1) := by
    intro i
    induction i with
    | zero => exact ⟨by simp [naiveCoeff], by simp [naiveCoeff]⟩
    | succ i ih =>
      refine ⟨ih.2, ?_⟩
      rw [naiveCoeff_add_two, ih.1, ih.2, Nat.fib_add_two]
      omega
  exact (key i).1

/-- The first two divisors have the coefficient `m + 1`, and the third one has the coefficient `m + 2`. -/
theorem naiveCoeff_one_two_three (m : ℕ) :
    naiveCoeff m 1 = m + 1 ∧ naiveCoeff m 2 = m + 1 ∧ naiveCoeff m 3 = m + 2 := by
  have h3 : Nat.fib 3 = 2 := by
    rw [show 3 = 1 + 2 from rfl, Nat.fib_add_two]
    simp
  rw [naiveCoeff_eq, naiveCoeff_eq, naiveCoeff_eq, h3]
  simp

/-- **Volume 2, Example 3.3.9 of the handbook**, the orders. The order of `I` at `E^i ∩ E^(i+1)` is `2m + F_(i+2)`. For `i = 1, 2, 3` this is `2m + 2`, `2m + 3` and `2m + 5`. -/
theorem naiveCoeff_add (m i : ℕ) :
    naiveCoeff m i + naiveCoeff m (i + 1) = 2 * m + Nat.fib (i + 2) := by
  rw [naiveCoeff_eq, naiveCoeff_eq, Nat.fib_add_two]
  omega

/-- **Volume 2, Example 3.3.9 of the handbook**, the conclusion. The order of `I` at the intersection of the last two divisors grows without bound. -/
theorem exists_lt_naiveCoeff_add (m B : ℕ) :
    ∃ i, B < naiveCoeff m i + naiveCoeff m (i + 1) := by
  refine ⟨B, ?_⟩
  rw [naiveCoeff_add]
  have := Nat.le_fib_add_one (B + 2)
  omega

end Singularity
