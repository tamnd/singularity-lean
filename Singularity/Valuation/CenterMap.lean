/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Singularity.Valuation.Center
import Singularity.Valuation.ZariskiRiemann

/-!
# The center map of the Zariski-Riemann space

This file proves Volume 3, Proposition 1.5.2 of the handbook. Let `K` be a field and let `B ⊆ K` be a subring. The center map `c_B : ZR(K/B) → Spec B` sends `V` to `m_V ∩ B`. It is continuous and surjective.

* `Singularity.ZariskiRiemann.centerMap`: the center map `c_B`.
* `Singularity.ZariskiRiemann.continuous_centerMap`: the map `c_B` is continuous.
* `Singularity.ZariskiRiemann.surjective_centerMap`: the map `c_B` is surjective.
* `Singularity.ZariskiRiemann.continuous_and_surjective_centerMap`: Proposition 1.5.2 of the handbook.

The proof is the proof of the handbook. Let `b ∈ B` with `b ≠ 0`. Then `b ∉ m_V` if and only if `b⁻¹ ∈ V`, so the inverse image of `D(b)` is the open set `U({b⁻¹})`. The inverse image of `D(0)` is empty. The sets `D(b)` are a basis of `Spec B`, so `c_B` is continuous. Surjectivity is the theorem of Chevalley (`Singularity.exists_valuationSubring_of_isPrime`).
-/

namespace Singularity.ZariskiRiemann

variable {K : Type*} [Field K] (B : Subring K)

/-- Each point of `ZR(K/B)` contains the subring `B`. -/
theorem le_toSubring (V : ZariskiRiemann B K) : B ≤ V.toValuationSubring.toSubring :=
  fun x hx => V.algebraMap_mem ⟨x, hx⟩

/-- The center map `c_B : ZR(K/B) → Spec B` with `c_B(V) = m_V ∩ B` (Volume 3, Section 1.5 of the handbook). The prime `c_B(V)` is the ideal `Singularity.centerIdeal` of the elements of `B` with value less than `1`. -/
def centerMap (V : ZariskiRiemann B K) : PrimeSpectrum B :=
  ⟨centerIdeal V.toValuationSubring B (le_toSubring B V), inferInstance⟩

variable {B} in
theorem mem_centerMap {V : ZariskiRiemann B K} {b : B} :
    b ∈ (centerMap B V).asIdeal ↔ V.toValuationSubring.valuation (b : K) < 1 :=
  Iff.rfl

/-- Let `b ∈ B` with `b ≠ 0`. Then `b ∉ m_V` if and only if `b⁻¹ ∈ V`, for each `V` in `ZR(K/B)`. -/
theorem not_mem_centerMap_iff {V : ZariskiRiemann B K} {b : B} (hb : (b : K) ≠ 0) :
    b ∉ (centerMap B V).asIdeal ↔ (b : K)⁻¹ ∈ V.toValuationSubring := by
  rw [mem_centerMap, ← V.toValuationSubring.valuation_le_one_iff]
  have h1 : V.toValuationSubring.valuation (b : K) ≤ 1 :=
    (V.toValuationSubring.valuation_le_one_iff _).mpr (le_toSubring B V b.2)
  have hm : V.toValuationSubring.valuation (b : K) *
      V.toValuationSubring.valuation (b : K)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hb, map_one]
  constructor
  · intro h
    rw [le_antisymm h1 (not_lt.mp h), one_mul] at hm
    rw [hm]
  · intro h h'
    have := mul_lt_one_of_lt_of_le h' h
    rw [hm] at this
    exact lt_irrefl _ this

/-- The inverse image of a basic open set `D(b)` under `c_B` is open. It is empty if `b = 0`, and it is `U({b⁻¹})` if `b ≠ 0`. -/
theorem isOpen_preimage_basicOpen (b : B) :
    IsOpen (centerMap B ⁻¹' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B))) := by
  by_cases hb : (b : K) = 0
  · convert isOpen_empty (X := ZariskiRiemann B K)
    ext V
    simp only [Set.mem_preimage, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
      Set.mem_empty_iff_false, iff_false, not_not, mem_centerMap, hb, Valuation.map_zero]
    exact zero_lt_one
  · convert isOpen_setOf_mem (A := B) (b : K)⁻¹
    ext V
    exact not_mem_centerMap_iff B hb

/-- The center map `c_B` is continuous (Volume 3, Proposition 1.5.2 of the handbook, the first part). -/
theorem continuous_centerMap :
    Continuous (centerMap B : ZariskiRiemann B K → PrimeSpectrum B) := by
  rw [PrimeSpectrum.isTopologicalBasis_basic_opens.continuous_iff]
  rintro _ ⟨b, rfl⟩
  exact isOpen_preimage_basicOpen B b

/-- The center map `c_B` is surjective (Volume 3, Proposition 1.5.2 of the handbook, the second part). This is the theorem of Chevalley, in the form `Singularity.exists_valuationSubring_of_isPrime`. -/
theorem surjective_centerMap :
    Function.Surjective (centerMap B : ZariskiRiemann B K → PrimeSpectrum B) := by
  intro P
  obtain ⟨V, -, hle, hmem⟩ := exists_valuationSubring_of_isPrime B P.asIdeal
  refine ⟨mk V fun a => hle a.2, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩
  exact (hmem a).symm

/-- Volume 3, Proposition 1.5.2 of the handbook. Let `B ⊆ K` be a subring. The center map `c_B : ZR(K/B) → Spec B` is continuous and surjective. -/
theorem continuous_and_surjective_centerMap :
    Continuous (centerMap B : ZariskiRiemann B K → PrimeSpectrum B) ∧
      Function.Surjective (centerMap B : ZariskiRiemann B K → PrimeSpectrum B) :=
  ⟨continuous_centerMap B, surjective_centerMap B⟩

end Singularity.ZariskiRiemann
