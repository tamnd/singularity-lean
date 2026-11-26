/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Valuation.Basic

/-!
# The value of a root of an Artin-Schreier polynomial

Let `v` be a valuation on a ring `L`, and let `η ∈ L` with `η^n - η = b` for an integer `n ≥ 2`. In the handbook `n = p` and this is the Artin-Schreier relation `η^p - η = b`. This file computes the value of `η` from the value of `b` (Volume 3, proof of Lemma 3.2.4 and Example 3.2.6 of the handbook).

Mathlib writes valuations multiplicatively. So `v(b) > 1` here is `v(b) < 0` in the additive notation of the handbook, and `v(η)^n = v(b)` is `n w(η) = v(b)`.

1. If `v(b) > 1`, then `v(η)^n = v(b)` (`valuation_pow_eq_of_one_lt_valuation_pow_sub_self`). With `n = p` and `b = t^(-1/p^m)`, this is the first claim `w(η_m) = -1/p^(m+1)` of Lemma 3.2.4.
2. If `v(b) = 1`, then `v(η) = 1` (`valuation_eq_one_of_valuation_pow_sub_self_eq_one`). This is the first step of Example 3.2.6 (2).
-/

namespace Singularity

variable {L Γ₀ : Type*} [Ring L] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)

/-- If `v(η) ≤ 1`, then `v(η^n - η) ≤ 1`. -/
theorem valuation_pow_sub_self_le_one {n : ℕ} {η : L} (h : v η ≤ 1) : v (η ^ n - η) ≤ 1 :=
  v.map_sub_le (by rw [map_pow]; exact pow_le_one' h n) h

/-- If `v(η) > 1` and `n ≥ 2`, then `v(η^n - η) = v(η)^n`. -/
theorem valuation_pow_sub_self_of_one_lt {n : ℕ} (hn : 2 ≤ n) {η : L} (h : 1 < v η) :
    v (η ^ n - η) = v η ^ n := by
  have h2 : v η < v (η ^ n) := by
    rw [map_pow]
    exact lt_self_pow₀ h (by omega)
  rw [v.map_sub_eq_of_lt_left h2, map_pow]

/-- **The value of an Artin-Schreier root** (Volume 3, proof of Lemma 3.2.4 of the handbook). Let `n ≥ 2` and let `η ∈ L` with `v(η^n - η) > 1`. Then `v(η)^n = v(η^n - η)`. In the additive notation of the handbook, `w(η^p - η) < 0` gives `p w(η) = w(η^p - η)`. -/
theorem valuation_pow_eq_of_one_lt_valuation_pow_sub_self {n : ℕ} (hn : 2 ≤ n) {η : L}
    (h : 1 < v (η ^ n - η)) : v η ^ n = v (η ^ n - η) := by
  have h1 : 1 < v η := by
    by_contra hle
    exact absurd h (not_lt.mpr (valuation_pow_sub_self_le_one v (not_lt.mp hle)))
  rw [valuation_pow_sub_self_of_one_lt v hn h1]

/-- **An Artin-Schreier root of a unit** (Volume 3, Example 3.2.6 (2) of the handbook). Let `n ≥ 2` and let `η ∈ L` with `v(η^n - η) = 1`. Then `v(η) = 1`. In the additive notation of the handbook, `w(η^p - η) = 0` gives `w(η) = 0`. -/
theorem valuation_eq_one_of_valuation_pow_sub_self_eq_one {n : ℕ} (hn : 2 ≤ n) {η : L}
    (h : v (η ^ n - η) = 1) : v η = 1 := by
  rcases lt_trichotomy (v η) 1 with hlt | heq | hgt
  · exfalso
    have h1 : v (η ^ n) < 1 := by
      rw [map_pow]
      exact pow_lt_one' hlt (by omega)
    have h2 : v (η ^ n - η) < 1 := (v.map_sub _ _).trans_lt (max_lt h1 hlt)
    exact absurd h h2.ne
  · exact heq
  · exfalso
    rw [valuation_pow_sub_self_of_one_lt v hn hgt] at h
    have h3 : v η < v η ^ n := lt_self_pow₀ hgt (by omega)
    exact absurd h (ne_of_gt (hgt.trans h3))

end Singularity
