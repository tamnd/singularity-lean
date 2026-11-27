/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Adjoin.FG
import Singularity.Valuation.CenterMap

/-!
# Finitely many affine charts cover the Zariski-Riemann space

This file proves Volume 3, Corollary 1.5.4 of the handbook. For each point `v` of `ZR(K/A)` let `B_v ⊆ 𝒪_v` be a finitely generated `A`-subalgebra of `K`, and let `G_v ⊆ Spec B_v` be an open set that contains the center of `v`. Then there are finitely many points `v₁, ..., v_m` such that each point `w` has a center on some `Spec B_{vᵢ}`, and this center is in `G_{vᵢ}`.

In Lean, "`w` has a center on `Spec B`" is the condition `B ⊆ 𝒪_w`, and the center is `𝔪_w ∩ B`, the value of the center map `Singularity.ZariskiRiemann.centerMap`. If `Frac B = K`, this is the center of Volume 3, Lemma 1.4.2 of the handbook. The hypothesis `Frac B_v = K` of the handbook is not necessary for the statement, so the Lean statement does not use it.

* `Singularity.ZariskiRiemann.centerSet`: the set `W_v` of the points with a center on `Spec B_v` in `G_v`.
* `Singularity.ZariskiRiemann.isOpen_centerSet`: the set `W_v` is open.
* `Singularity.ZariskiRiemann.exists_finset_forall_exists_centerMap_mem`: Corollary 1.5.4 of the handbook.

The proof is the proof of the handbook. Let `B_v = A[s]`. The center map of `ZR(K/B_v)` is continuous (Proposition 1.5.2), so a basic open set `U(F)` of `ZR(K/B_v)` contains `v` and maps into `G_v`. Then `U(F ∪ s)` is a basic open set of `ZR(K/A)` that contains `v` and is contained in `W_v`. So `W_v` is open. The sets `W_v` cover `ZR(K/A)`, and `ZR(K/A)` is quasi-compact (Theorem 1.5.3), so finitely many of them cover it.
-/

namespace Singularity.ZariskiRiemann

open TopologicalSpace

variable {A : Type*} {K : Type*} [CommRing A] [Field K] [Algebra A K]

/-- The point `V` of `ZR(K/A)` as an `A`-subalgebra of `K`. -/
def toSubalgebra (V : ZariskiRiemann A K) : Subalgebra A K :=
  { V.toValuationSubring.toSubring with algebraMap_mem' := V.algebraMap_mem }

/-- Let `B` be an `A`-subalgebra of `K` that is contained in the point `w` of `ZR(K/A)`. Then `w` is also a point of `ZR(K/B)`. -/
def restrict (B : Subalgebra A K) (w : ZariskiRiemann A K)
    (h : (B : Set K) ⊆ w.toValuationSubring) : ZariskiRiemann B.toSubring K :=
  mk w.toValuationSubring fun b => h b.2

/-- Let `B = A[s]` for a finite set `s`. Each point of `U(s)` contains `B`. -/
theorem coe_subset_of_mem_basicOpen {B : Subalgebra A K} {s : Finset K}
    (hs : Algebra.adjoin A (s : Set K) = B) {w : ZariskiRiemann A K} (hw : w ∈ basicOpen s) :
    (B : Set K) ⊆ w.toValuationSubring := by
  rw [← hs]
  intro x hx
  exact Algebra.adjoin_le (S := toSubalgebra w) (fun y hy => hw y hy) hx

/-- The set `W` of the points `w` of `ZR(K/A)` such that `B ⊆ 𝒪_w` and the center `𝔪_w ∩ B` is in `G`. If `Frac B = K`, the first condition says that `w` has a center on `Spec B` (Volume 3, Lemma 1.4.2 of the handbook). -/
def centerSet (B : Subalgebra A K) (G : Set (PrimeSpectrum B.toSubring)) :
    Set (ZariskiRiemann A K) :=
  {w | ∃ h : (B : Set K) ⊆ w.toValuationSubring, centerMap B.toSubring (restrict B w h) ∈ G}

/-- Let `B` be a finitely generated `A`-subalgebra of `K` and let `G` be an open set of `Spec B`. Then the set `centerSet B G` is open in `ZR(K/A)`. -/
theorem isOpen_centerSet {B : Subalgebra A K} (hB : B.FG) {G : Set (PrimeSpectrum B.toSubring)}
    (hG : IsOpen G) : IsOpen (centerSet B G) := by
  classical
  obtain ⟨s, hs⟩ := hB
  rw [isOpen_iff_forall_mem_open]
  rintro w ⟨h, hw⟩
  have hO : IsOpen (centerMap B.toSubring ⁻¹' G) := hG.preimage (continuous_centerMap _)
  obtain ⟨_, ⟨F, rfl⟩, hwF, hFO⟩ := (isTopologicalBasis_basicOpen).isOpen_iff.mp hO _ hw
  refine ⟨basicOpen (F ∪ s), ?_, isOpen_basicOpen _, ?_⟩
  · intro u hu
    have hu' : u ∈ basicOpen s := fun x hx => hu x (Finset.mem_union_right _ hx)
    have hBu := coe_subset_of_mem_basicOpen hs hu'
    refine ⟨hBu, hFO ?_⟩
    intro x hx
    exact hu x (Finset.mem_union_left _ hx)
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hwF x hx
    · exact h (hs ▸ Algebra.subset_adjoin hx)

/-- Volume 3, Corollary 1.5.4 of the handbook. For each point `v` of `ZR(K/A)` let `B_v ⊆ 𝒪_v` be a finitely generated `A`-subalgebra of `K`, and let `G_v` be an open set of `Spec B_v` that contains the center `𝔪_v ∩ B_v` of `v`. Then there are finitely many points `v₁, ..., v_m` such that each point `w` has an `i` with `B_{vᵢ} ⊆ 𝒪_w` and `𝔪_w ∩ B_{vᵢ} ∈ G_{vᵢ}`. -/
theorem exists_finset_forall_exists_centerMap_mem
    (B : ZariskiRiemann A K → Subalgebra A K) (hfg : ∀ v, (B v).FG)
    (hB : ∀ v, (B v : Set K) ⊆ v.toValuationSubring)
    (G : ∀ v, Set (PrimeSpectrum (B v).toSubring)) (hG : ∀ v, IsOpen (G v))
    (hcen : ∀ v, centerMap (B v).toSubring (restrict (B v) v (hB v)) ∈ G v) :
    ∃ t : Finset (ZariskiRiemann A K), ∀ w, ∃ v ∈ t,
      ∃ h : (B v : Set K) ⊆ w.toValuationSubring,
        centerMap (B v).toSubring (restrict (B v) w h) ∈ G v := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun v => centerSet (B v) (G v))
    (fun v => isOpen_centerSet (hfg v) (hG v))
    (fun v _ => Set.mem_iUnion.mpr ⟨v, hB v, hcen v⟩)
  refine ⟨t, fun w => ?_⟩
  obtain ⟨v, hv, h, hc⟩ := by simpa only [Set.mem_iUnion] using ht (Set.mem_univ w)
  exact ⟨v, hv, h, hc⟩

end Singularity.ZariskiRiemann
