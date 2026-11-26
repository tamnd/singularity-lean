/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Prod

/-!
# The intersection theorem of Krull for a domain

This file proves Volume 1, Corollary 4.1.9 and Example 4.1.10 of the handbook.

* `Singularity.Algebra.iInf_pow_eq_bot_of_isDomain`: let `R` be a Noetherian domain and let `I ≠ R` be an ideal. Then `⋂ I^n = 0` (Corollary 4.1.9). This is `Ideal.iInf_pow_eq_bot_of_isDomain` of Mathlib.
* `Singularity.Algebra.iInf_pow_prod_eq`: the hypotheses are necessary (Example 4.1.10). Let `k` be a field, let `R = k × k` and let `I = k × 0`. Then `I^n = I` for each `n ≥ 1`, so `⋂ I^n = I ≠ 0`. Also `(0, 1) I = 0` (`prod_mul_mem_eq_zero`).
-/

namespace Singularity.Algebra

/-- The intersection theorem of Krull for a domain (Volume 1, Corollary 4.1.9 of the handbook). Let `R` be a Noetherian domain and let `I ≠ R` be an ideal. Then `⋂ I^n = 0`. -/
theorem iInf_pow_eq_bot_of_isDomain {R : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {I : Ideal R} (h : I ≠ ⊤) : ⨅ n : ℕ, I ^ n = ⊥ :=
  Ideal.iInf_pow_eq_bot_of_isDomain I h

variable (k : Type*) [Field k]

/-- The ideal `k × 0` of `k × k`. -/
def prodIdeal : Ideal (k × k) := Ideal.prod ⊤ ⊥

theorem mem_prodIdeal {x : k × k} : x ∈ prodIdeal k ↔ x.2 = 0 := by
  simp [prodIdeal, Ideal.mem_prod]

/-- The ideal `I = k × 0` of `k × k` satisfies `I^2 = I`. -/
theorem prodIdeal_mul_self : prodIdeal k * prodIdeal k = prodIdeal k := by
  refine le_antisymm Ideal.mul_le_left fun x hx => ?_
  have h10 : ((1, 0) : k × k) ∈ prodIdeal k := (mem_prodIdeal k).mpr rfl
  have : x = x * (1, 0) := by
    have hx2 := (mem_prodIdeal k).mp hx
    ext <;> simp [hx2]
  rw [this]
  exact Ideal.mul_mem_mul hx h10

/-- The ideal `I = k × 0` of `k × k` satisfies `I^n = I` for each `n ≥ 1`. -/
theorem prodIdeal_pow {n : ℕ} (hn : 1 ≤ n) : prodIdeal k ^ n = prodIdeal k := by
  induction n, hn using Nat.le_induction with
  | base => exact pow_one _
  | succ n hn ih => rw [pow_succ, ih, prodIdeal_mul_self]

/-- The hypotheses of Corollaries 4.1.8 and 4.1.9 are necessary (Volume 1, Example 4.1.10 of the handbook). Let `k` be a field and let `I = k × 0` in the Noetherian ring `k × k`. Then `⋂ I^n = I`, and `I ≠ 0`. -/
theorem iInf_pow_prod_eq : ⨅ n : ℕ, prodIdeal k ^ n = prodIdeal k ∧ prodIdeal k ≠ ⊥ := by
  refine ⟨le_antisymm (iInf_le_of_le 1 (pow_one _).le) (le_iInf fun n => ?_), ?_⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact (prodIdeal_pow k hn).ge
  · intro h
    have h10 : ((1, 0) : k × k) ∈ prodIdeal k := (mem_prodIdeal k).mpr rfl
    rw [h, Ideal.mem_bot] at h10
    simpa using congrArg Prod.fst h10

/-- In Example 4.1.10, the element `a = (-1, 0)` of `I` gives `1 + a = (0, 1)`, and `(0, 1)` kills `I`. -/
theorem prod_mul_mem_eq_zero {x : k × k} (hx : x ∈ prodIdeal k) :
    (1 + ((-1, 0) : k × k)) * x = 0 := by
  have hx2 := (mem_prodIdeal k).mp hx
  ext <;> simp [hx2]

end Singularity.Algebra
