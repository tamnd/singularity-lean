/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Consequences of the theorem of Chevalley

The theorem of Chevalley states that each local subring of a field `K` is dominated by a valuation ring of `K` (Volume 3, Theorem 1.3.2 of the handbook). Mathlib has it as `LocalSubring.exists_le_valuationSubring`. This file proves two consequences.

1. Let `A ⊆ K` be a subring and let `P` be a prime of `A`. Then there is a valuation ring `V` of `K` that contains `A`, with `P = m_V ∩ A` (Volume 3, Corollary 1.3.3 of the handbook). The proof applies the theorem of Chevalley to the localization `A_P`.
2. Let `L/K` be a field extension. Each valuation of `K` extends to a valuation of `L` (Volume 3, Corollary 1.3.5 of the handbook). The proof applies the theorem of Chevalley to the image of the valuation ring in `L`.

In Mathlib, `A ≤ B` for local subrings means that `B` dominates `A`: `A ⊆ B` and `m_B ∩ A = m_A`. The condition `P = m_V ∩ A` is written as `a ∈ P ↔ v(a) < 1`, so the file does not use the maximal ideal of `V`.

## Main results

* `Singularity.mem_iff_valuation_lt_one_of_le`: if `V` dominates `A_P`, then `a ∈ P ↔ v(a) < 1`.
* `Singularity.exists_valuationSubring_of_isPrime`: Corollary 1.3.3.
* `Singularity.ValuationSubring.exists_comap_eq`: Corollary 1.3.5 for valuation rings.
* `Singularity.Valuation.exists_hasExtension`: Corollary 1.3.5 for valuations.
-/

namespace Singularity

variable {K : Type*} [Field K]

/-- Let `A ⊆ K` be a subring, let `P` be a prime of `A`, and let `V` be a valuation ring of `K` that dominates the localization `A_P`. Then `P` is the set of the elements `a ∈ A` with `v(a) < 1`, that is, `P = m_V ∩ A`. -/
theorem mem_iff_valuation_lt_one_of_le {A : Subring K} {P : Ideal A} [P.IsPrime]
    {V : ValuationSubring K} (h : LocalSubring.ofPrime A P ≤ V.toLocalSubring) (a : A) :
    a ∈ P ↔ V.valuation (a : K) < 1 := by
  obtain ⟨hle, hloc⟩ := h
  have hAV : ∀ x : A, (x : K) ∈ V := fun x => hle (LocalSubring.le_ofPrime A P x.2)
  constructor
  · intro ha
    by_contra hlt
    have h1 : V.valuation (a : K) = 1 :=
      le_antisymm ((V.valuation_le_one_iff _).mpr (hAV a)) (not_lt.mp hlt)
    have ha0 : (a : K) ≠ 0 := by
      intro h0
      rw [h0, Valuation.map_zero] at h1
      exact zero_ne_one h1
    have hinv : (a : K)⁻¹ ∈ V := by
      rw [← V.valuation_le_one_iff, map_inv₀, h1, inv_one]
    have hu : IsUnit (Subring.inclusion hle
        (algebraMap A (LocalSubring.ofPrime A P).toSubring a)) :=
      isUnit_iff_exists_inv.mpr ⟨⟨(a : K)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩
    have hb := hloc.map_nonunit _ hu
    exact Ideal.mem_primeCompl_iff.mp
      ((IsLocalization.AtPrime.isUnit_to_map_iff _ P a).mp hb) ha
  · intro hlt
    by_contra ha
    have hb : IsUnit (algebraMap A (LocalSubring.ofPrime A P).toSubring a) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff _ P a).mpr (Ideal.mem_primeCompl_iff.mpr ha)
    obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp (hb.map (Subring.inclusion hle))
    have hc' : (a : K) * (c : K) = 1 := congrArg Subtype.val hc
    have hcle : V.valuation (c : K) ≤ 1 := (V.valuation_le_one_iff _).mpr c.2
    have hlt' : V.valuation ((a : K) * c) < 1 := by
      rw [Valuation.map_mul]
      exact (mul_le_of_le_one_right' hcle).trans_lt hlt
    rw [hc', Valuation.map_one] at hlt'
    exact lt_irrefl _ hlt'

/-- Let `A ⊆ K` be a subring and let `P` be a prime of `A`. Then there is a valuation ring `V` of `K` that dominates `A_P`. So `V` contains `A`, and `P` is the set of the elements `a ∈ A` with `v(a) < 1`, that is, `P = m_V ∩ A` (Volume 3, Corollary 1.3.3 of the handbook). -/
theorem exists_valuationSubring_of_isPrime (A : Subring K) (P : Ideal A) [P.IsPrime] :
    ∃ V : ValuationSubring K, LocalSubring.ofPrime A P ≤ V.toLocalSubring ∧
      A ≤ V.toSubring ∧ ∀ a : A, a ∈ P ↔ V.valuation (a : K) < 1 := by
  obtain ⟨V, hV⟩ := (LocalSubring.ofPrime A P).exists_le_valuationSubring
  exact ⟨V, hV, (LocalSubring.le_ofPrime A P).trans hV.1, mem_iff_valuation_lt_one_of_le hV⟩

/-- Let `L/K` be a field extension and let `A` be a valuation ring of `K`. Then there is a valuation ring `B` of `L` with `B ∩ K = A` (Volume 3, Corollary 1.3.5 of the handbook, in the form of valuation rings). -/
theorem ValuationSubring.exists_comap_eq {L : Type*} [Field L] [Algebra K L]
    (A : ValuationSubring K) : ∃ B : ValuationSubring L, B.comap (algebraMap K L) = A := by
  obtain ⟨B, hle, hloc⟩ := (A.toLocalSubring.map (algebraMap K L)).exists_le_valuationSubring
  refine ⟨B, le_antisymm ?_ ?_⟩
  · intro x hx
    by_contra hxA
    have hinv : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hxA
    have hx0 : x ≠ 0 := fun h => hxA (h ▸ A.zero_mem)
    have hxB : algebraMap K L x ∈ B := hx
    let y : (A.toLocalSubring.map (algebraMap K L)).toSubring :=
      ⟨algebraMap K L x⁻¹, Subring.mem_map.mpr ⟨_, hinv, rfl⟩⟩
    have hu : IsUnit (Subring.inclusion hle y) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K L x, hxB⟩, Subtype.ext ?_⟩
      show algebraMap K L x⁻¹ * algebraMap K L x = 1
      rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp (hloc.map_nonunit y hu)
    obtain ⟨a, ha, haz⟩ := Subring.mem_map.mp z.2
    have hz' : algebraMap K L x⁻¹ * algebraMap K L a = 1 := by
      rw [haz]
      exact congrArg Subtype.val hz
    rw [← map_mul, ← map_one (algebraMap K L)] at hz'
    have hxa := (algebraMap K L).injective hz'
    rw [inv_mul_eq_one₀ hx0] at hxa
    exact hxA (by rw [hxa]; exact ha)
  · intro x hx
    exact hle (Subring.mem_map.mpr ⟨x, hx, rfl⟩)

/-- Let `L/K` be a field extension and let `v` be a valuation of `K`. Then there is a valuation `w` of `L` that extends `v` (Volume 3, Corollary 1.3.5 of the handbook). Here `w` is the valuation of a valuation ring `B` of `L`, and `w` extends `v` in the sense of Mathlib: the restriction of `w` to `K` is equivalent to `v`. -/
theorem Valuation.exists_hasExtension {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (L : Type*) [Field L] [Algebra K L] :
    ∃ B : ValuationSubring L, v.HasExtension B.valuation := by
  obtain ⟨B, hB⟩ := ValuationSubring.exists_comap_eq (L := L) v.valuationSubring
  refine ⟨B, ⟨?_⟩⟩
  rw [_root_.Valuation.isEquiv_iff_valuationSubring, ← hB]
  ext x
  simp only [_root_.Valuation.mem_valuationSubring_iff, _root_.ValuationSubring.mem_comap,
    _root_.Valuation.comap_apply, _root_.ValuationSubring.valuation_le_one_iff]

end Singularity
