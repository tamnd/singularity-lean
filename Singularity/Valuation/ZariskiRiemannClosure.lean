/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.ZariskiRiemann

/-!
# The closure of a point of the Zariski-Riemann space

Let `V` be a point of `ZR(K/A)`. This file proves that the closure of `{V}` is the set of the points `W` with `W ⊆ V` (Volume 3, Proposition 1.5.5 of the handbook). So `ZR(K/A)` is a `T_0` space.

The proof follows the handbook. The sets `U(F)` are a basis of the topology. If `W ⊆ V` and `W ∈ U(F)`, then `F ⊆ W ⊆ V`, so `V ∈ U(F)`. If `f ∈ W` and `f ∉ V`, then `U({f})` contains `W` and does not contain `V`.
-/

namespace Singularity

namespace ZariskiRiemann

variable {A : Type*} {K : Type*} [CommRing A] [Field K] [Algebra A K]

/-- **The closure of a point** (Volume 3, Proposition 1.5.5 of the handbook). A point `W` of `ZR(K/A)` is in the closure of `{V}` if and only if `W ⊆ V`. -/
theorem mem_closure_singleton_iff {V W : ZariskiRiemann A K} :
    W ∈ closure ({V} : Set (ZariskiRiemann A K)) ↔
      W.toValuationSubring ≤ V.toValuationSubring := by
  rw [isTopologicalBasis_basicOpen.mem_closure_iff]
  constructor
  · intro h x hx
    have hW : W ∈ basicOpen ({x} : Finset K) := by
      simpa [mem_basicOpen] using hx
    obtain ⟨U, hU, hUV⟩ := h _ ⟨{x}, rfl⟩ hW
    rw [Set.mem_singleton_iff] at hUV
    subst hUV
    simpa [mem_basicOpen] using hU
  · rintro h _ ⟨F, rfl⟩ hW
    exact ⟨V, Set.mem_inter (mem_basicOpen.mpr fun x hx => h (mem_basicOpen.mp hW x hx))
      (Set.mem_singleton V)⟩

/-- The closure of `{V}` in `ZR(K/A)` is the set of the points `W` with `W ⊆ V` (Volume 3, Proposition 1.5.5 of the handbook). -/
theorem closure_singleton (V : ZariskiRiemann A K) :
    closure ({V} : Set (ZariskiRiemann A K)) =
      {W | W.toValuationSubring ≤ V.toValuationSubring} := by
  ext W
  exact mem_closure_singleton_iff

/-- **The Zariski-Riemann space is `T_0`** (Volume 3, Proposition 1.5.5 of the handbook, the last claim). -/
instance instT0Space : T0Space (ZariskiRiemann A K) := by
  rw [t0Space_iff_inseparable]
  intro V W h
  rw [inseparable_iff_specializes_and, specializes_iff_mem_closure, specializes_iff_mem_closure,
    mem_closure_singleton_iff, mem_closure_singleton_iff] at h
  exact ext (le_antisymm h.2 h.1)

end ZariskiRiemann

end Singularity
