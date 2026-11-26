/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.Chevalley

/-!
# The center of a valuation

Let `A ⊆ K` be a subring and let `V` be a valuation ring of `K` with valuation `v`. A center of `V` on `A` is a prime `P` of `A` such that `V` dominates the localization `A_P`. This file proves the lemma on centers (Volume 3, Lemma 1.4.2 of the handbook).

1. If `V` has a center on `A`, then `A ⊆ V`.
2. If `A ⊆ V`, then `P = {a ∈ A | v(a) < 1}` is a center of `V` on `A`. This is the prime `m_V ∩ A`.
3. The center is unique.

In Mathlib, `LocalSubring.ofPrime A P ≤ V.toLocalSubring` states that `V` dominates `A_P`. The handbook assumes that `K` is the fraction field of `A`. The proof here does not use this hypothesis.

## Main results

* `Singularity.centerIdeal`: the prime `{a ∈ A | v(a) < 1}`.
* `Singularity.le_of_ofPrime_le`: a center exists only if `A ⊆ V`.
* `Singularity.ofPrime_centerIdeal_le`: the prime `centerIdeal` is a center.
* `Singularity.eq_of_ofPrime_le`: the center is unique.
-/

namespace Singularity

variable {K : Type*} [Field K]

/-- Let `A ⊆ V` be a subring of a valuation ring `V` of `K`. This is the ideal `m_V ∩ A = {a ∈ A | v(a) < 1}` of `A`. -/
def centerIdeal (V : ValuationSubring K) (A : Subring K) (hA : A ≤ V.toSubring) : Ideal A where
  carrier := {a | V.valuation (a : K) < 1}
  add_mem' := by
    intro a b ha hb
    show V.valuation ((a : K) + b) < 1
    exact (V.valuation.map_add _ _).trans_lt (max_lt ha hb)
  zero_mem' := by
    show V.valuation ((0 : A) : K) < 1
    rw [ZeroMemClass.coe_zero, Valuation.map_zero]
    exact zero_lt_one
  smul_mem' := by
    intro c a ha
    show V.valuation ((c : K) * a) < 1
    rw [Valuation.map_mul]
    exact (mul_le_of_le_one_left' ((V.valuation_le_one_iff _).mpr (hA c.2))).trans_lt ha

theorem mem_centerIdeal {V : ValuationSubring K} {A : Subring K} {hA : A ≤ V.toSubring} {a : A} :
    a ∈ centerIdeal V A hA ↔ V.valuation (a : K) < 1 :=
  Iff.rfl

/-- An element of `A` outside `centerIdeal` has the value `1`. -/
theorem valuation_eq_one_of_not_mem_centerIdeal {V : ValuationSubring K} {A : Subring K}
    {hA : A ≤ V.toSubring} {a : A} (ha : a ∉ centerIdeal V A hA) : V.valuation (a : K) = 1 :=
  le_antisymm ((V.valuation_le_one_iff _).mpr (hA a.2)) (not_lt.mp ha)

instance (V : ValuationSubring K) (A : Subring K) (hA : A ≤ V.toSubring) :
    (centerIdeal V A hA).IsPrime where
  ne_top' := by
    rw [Ideal.ne_top_iff_one, mem_centerIdeal, OneMemClass.coe_one, Valuation.map_one]
    exact lt_irrefl _
  mem_or_mem' := by
    intro a b hab
    by_contra h
    rw [not_or] at h
    rw [mem_centerIdeal, MulMemClass.coe_mul, Valuation.map_mul,
      valuation_eq_one_of_not_mem_centerIdeal h.1, valuation_eq_one_of_not_mem_centerIdeal h.2,
      mul_one] at hab
    exact lt_irrefl _ hab

/-- If `V` has a center on `A`, then `A ⊆ V` (Volume 3, Lemma 1.4.2 of the handbook, the first part). -/
theorem le_of_ofPrime_le {V : ValuationSubring K} {A : Subring K} {P : Ideal A} [P.IsPrime]
    (h : LocalSubring.ofPrime A P ≤ V.toLocalSubring) : A ≤ V.toSubring :=
  (LocalSubring.le_ofPrime A P).trans h.1

/-- Let `A ⊆ V`, and let `P` be a prime of `A` with `a ∈ P ↔ v(a) < 1`. Then `V` dominates the localization `A_P`. -/
theorem ofPrime_le_of_mem_iff {V : ValuationSubring K} {A : Subring K} {P : Ideal A} [P.IsPrime]
    (hA : A ≤ V.toSubring) (hPv : ∀ a : A, a ∈ P ↔ V.valuation (a : K) < 1) :
    LocalSubring.ofPrime A P ≤ V.toLocalSubring := by
  have hs : ∀ s : P.primeCompl, V.valuation (((s : A) : K)) = 1 := fun s =>
    le_antisymm ((V.valuation_le_one_iff _).mpr (hA (s : A).2))
      (not_lt.mp fun h => Ideal.mem_primeCompl_iff.mp s.2 ((hPv _).mpr h))
  have hval : ∀ y : (LocalSubring.ofPrime A P).toSubring, ∃ a : A,
      V.valuation (y : K) = V.valuation (a : K) ∧ ∃ s : P.primeCompl,
        y * algebraMap A (LocalSubring.ofPrime A P).toSubring s =
          algebraMap A (LocalSubring.ofPrime A P).toSubring a := by
    intro y
    obtain ⟨⟨a, s⟩, hys⟩ := IsLocalization.surj P.primeCompl y
    have hys' : (y : K) * ((s : A) : K) = (a : K) := congrArg Subtype.val hys
    refine ⟨a, ?_, s, hys⟩
    rw [← hys', Valuation.map_mul, hs s, mul_one]
  have hle : (LocalSubring.ofPrime A P).toSubring ≤ V.toLocalSubring.toSubring := by
    intro y hy
    obtain ⟨a, ha, -⟩ := hval ⟨y, hy⟩
    exact (V.valuation_le_one_iff y).mp (ha.trans_le ((V.valuation_le_one_iff _).mpr (hA a.2)))
  refine ⟨hle, ⟨fun y hy => ?_⟩⟩
  obtain ⟨a, ha, s, hys⟩ := hval y
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hy
  have hw' : (y : K) * (w : K) = 1 := congrArg Subtype.val hw
  have hvy : ¬ V.valuation (y : K) < 1 := by
    intro hlt
    have h1 := congrArg V.valuation hw'
    rw [Valuation.map_mul, Valuation.map_one] at h1
    have h2 : V.valuation (y : K) * V.valuation (w : K) < 1 :=
      (mul_le_of_le_one_right' ((V.valuation_le_one_iff _).mpr w.2)).trans_lt hlt
    exact h2.ne h1
  have haP : a ∉ P := by
    rw [hPv, ← ha]
    exact hvy
  have hu : IsUnit (algebraMap A (LocalSubring.ofPrime A P).toSubring a) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff _ P a).mpr (Ideal.mem_primeCompl_iff.mpr haP)
  rw [← hys] at hu
  exact isUnit_of_mul_isUnit_left hu

/-- If `A ⊆ V`, then `V` dominates the localization of `A` at `m_V ∩ A`. So `m_V ∩ A` is a center of `V` on `A` (Volume 3, Lemma 1.4.2 of the handbook, the existence). -/
theorem ofPrime_centerIdeal_le (V : ValuationSubring K) (A : Subring K) (hA : A ≤ V.toSubring) :
    LocalSubring.ofPrime A (centerIdeal V A hA) ≤ V.toLocalSubring :=
  ofPrime_le_of_mem_iff hA fun _ => Iff.rfl

/-- Let `V` dominate `A_P`. Then `P = m_V ∩ A` (Volume 3, Lemma 1.4.2 of the handbook, the formula for the center). -/
theorem eq_centerIdeal_of_ofPrime_le {V : ValuationSubring K} {A : Subring K} {P : Ideal A}
    [P.IsPrime] (h : LocalSubring.ofPrime A P ≤ V.toLocalSubring) :
    P = centerIdeal V A (le_of_ofPrime_le h) :=
  Ideal.ext fun a => (mem_iff_valuation_lt_one_of_le h a).trans mem_centerIdeal.symm

/-- The center of `V` on `A` is unique (Volume 3, Lemma 1.4.2 of the handbook, the uniqueness). -/
theorem eq_of_ofPrime_le {V : ValuationSubring K} {A : Subring K} {P Q : Ideal A} [P.IsPrime]
    [Q.IsPrime] (hP : LocalSubring.ofPrime A P ≤ V.toLocalSubring)
    (hQ : LocalSubring.ofPrime A Q ≤ V.toLocalSubring) : P = Q :=
  Ideal.ext fun a => (mem_iff_valuation_lt_one_of_le hP a).trans
    (mem_iff_valuation_lt_one_of_le hQ a).symm

/-- The lemma on centers (Volume 3, Lemma 1.4.2 of the handbook). The valuation ring `V` has a center on `A` if and only if `A ⊆ V`. Then the center is unique, and it is `m_V ∩ A = {a ∈ A | v(a) < 1}`. -/
theorem exists_center_iff (V : ValuationSubring K) (A : Subring K) :
    (∃ (P : Ideal A) (_ : P.IsPrime), LocalSubring.ofPrime A P ≤ V.toLocalSubring) ↔
      A ≤ V.toSubring :=
  ⟨fun ⟨_, _, h⟩ => le_of_ofPrime_le h,
    fun hA => ⟨centerIdeal V A hA, inferInstance, ofPrime_centerIdeal_le V A hA⟩⟩

end Singularity
