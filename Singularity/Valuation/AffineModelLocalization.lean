/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Local rings of two affine models at the centers of a valuation

Let `V` be a valuation subring of a field `K`, and let `A ⊆ A'` be subrings of `K` contained in `V`. The center of `V` on `A` is `p = m_V ∩ A`. So an element `s ∈ A` is outside `p` if and only if `v(s) = 1`. The local ring `A_p` is the set of fractions `a / s` with `a, s ∈ A` and `v(s) = 1` (`Singularity.centerLocalization V A`).

This file proves Volume 5, Lemma 1.1.1 of the handbook. If `A' ⊆ A_p`, then `A'_(p') = A_p` (`centerLocalization_eq_of_le`).

The handbook takes affine models of `K/k`, that is, finitely generated `k`-algebras with fraction field `K`. The proof does not use this. It also does not use that `A'` is contained in `V`: the set `centerLocalization V A'` is defined by the condition `v(s) = 1` in each case. When `A'` is contained in `V`, this condition says that `s` is outside the center `p'` of `V` on `A'`.
-/

namespace Singularity

variable {K : Type*} [Field K]

/-- The localization `A_p` of a subring `A` of `K` at the center `p = m_V ∩ A` of a valuation subring `V`, as a subset of `K`. It is the set of the fractions `a / s` with `a, s ∈ A` and `v(s) = 1`. -/
def centerLocalization (V : ValuationSubring K) (A : Subring K) : Set K :=
  {x | ∃ a ∈ A, ∃ s ∈ A, V.valuation s = 1 ∧ x = a / s}

theorem ne_zero_of_valuation_eq_one {V : ValuationSubring K} {s : K} (h : V.valuation s = 1) :
    s ≠ 0 := by
  rintro rfl
  rw [map_zero] at h
  exact zero_ne_one h

/-- **Volume 5, Lemma 1.1.1 of the handbook.** Let `V` be a valuation subring of `K`, and let `A ⊆ A'` be subrings of `K`. Let `p` and `p'` be the centers of `V` on `A` and `A'`. If `A' ⊆ A_p`, then `A'_(p') = A_p`. -/
theorem centerLocalization_eq_of_le (V : ValuationSubring K) {A A' : Subring K} (hAA' : A ≤ A')
    (h : ∀ x ∈ A', x ∈ centerLocalization V A) :
    centerLocalization V A' = centerLocalization V A := by
  ext x
  constructor
  · rintro ⟨a, ha, s, hs, hv, rfl⟩
    obtain ⟨b, hb, t, ht, hvt, rfl⟩ := h a ha
    obtain ⟨c, hc, u, hu, hvu, hsu⟩ := h s hs
    have hs0 := ne_zero_of_valuation_eq_one hv
    have ht0 := ne_zero_of_valuation_eq_one hvt
    have hu0 := ne_zero_of_valuation_eq_one hvu
    have hc_eq : c = s * u := by
      rw [hsu]
      field_simp
    have hvc : V.valuation c = 1 := by
      rw [hc_eq, map_mul, hv, hvu, one_mul]
    refine ⟨b * u, A.mul_mem hb hu, t * c, A.mul_mem ht hc, by rw [map_mul, hvt, hvc, one_mul], ?_⟩
    rw [hc_eq, div_div, div_eq_div_iff (mul_ne_zero ht0 hs0) (mul_ne_zero ht0 (mul_ne_zero hs0 hu0))]
    ring
  · rintro ⟨a, ha, s, hs, hv, rfl⟩
    exact ⟨a, hAA' ha, s, hAA' hs, hv, rfl⟩

end Singularity
