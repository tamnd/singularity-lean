/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.SpanRank
import Singularity.Algebra.CohenMap

/-!
# A complete local ring is a quotient of a power series ring

This file proves Volume 1, Corollary 4.4.8 of the handbook, with a coefficient field as a
hypothesis. Let `R` be a Noetherian local ring that is complete for the `𝔪`-adic topology, and
let `K → R` be a field such that the map `K → κ` to the residue field is surjective. Let
`e = spanFinrank 𝔪` be the embedding dimension. Then `R` is a quotient of `K[[X_1, ..., X_e]]`
and of `κ[[X_1, ..., X_e]]`.

The handbook gets the coefficient field from the Cohen structure theorem. Mathlib does not have
this theorem, so the field is a hypothesis here. The statement that `κ[[X_1, ..., X_e]]` is a
regular local ring is not in this file.

## Main results

* `exists_maximalIdeal_eq_span_range_fin`: the maximal ideal has a generating family with
  `spanFinrank 𝔪` members.
* `exists_surjective_mvPowerSeries_of_coefficientField`: a surjective `K`-algebra map
  `K[[X_1, ..., X_e]] → R`.
* `coefficientFieldEquivResidue`: the map `K → κ` is a ring isomorphism.
* `exists_surjective_mvPowerSeries_residueField`: a surjective ring map `κ[[X_1, ..., X_e]] → R`.
-/

namespace Singularity.Algebra

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] {K : Type*} [Field K] [Algebra K R]

/-- If `R` is Noetherian, then the maximal ideal has a generating family `x` with
`spanFinrank 𝔪` members. -/
theorem exists_maximalIdeal_eq_span_range_fin [IsNoetherianRing R] :
    ∃ x : Fin (maximalIdeal R).spanFinrank → R, maximalIdeal R = Ideal.span (Set.range x) := by
  classical
  obtain ⟨t, ht, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (maximalIdeal R).fg_of_isNoetherianRing
  let e : t ≃ Fin (maximalIdeal R).spanFinrank := t.equivFin.trans (finCongr ht)
  refine ⟨fun i => (e.symm i : R), ?_⟩
  have hr : Set.range (fun i => (e.symm i : R)) = (t : Set R) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hy
      exact ⟨e ⟨y, hy⟩, by simp⟩
  rw [hr]
  exact hspan.symm

/-- Volume 1, Corollary 4.4.8 of the handbook, with a coefficient field as a hypothesis.
Let `R` be a Noetherian local ring that is complete for the `𝔪`-adic topology, and let
`K → R` be a field such that `K → κ` is surjective. Let `e = spanFinrank 𝔪`. Then there is a
surjective `K`-algebra map `K[[X_1, ..., X_e]] → R`. -/
theorem exists_surjective_mvPowerSeries_of_coefficientField [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (hK : Function.Surjective fun k : K => residue R (algebraMap K R k)) :
    ∃ φ : MvPowerSeries (Fin (maximalIdeal R).spanFinrank) K →ₐ[K] R,
      Function.Surjective φ := by
  obtain ⟨x, hx⟩ := exists_maximalIdeal_eq_span_range_fin (R := R)
  have hmem : ∀ i, x i ∈ maximalIdeal R := by
    intro i
    rw [hx]
    exact Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨φ, -, -, hsurj⟩ := exists_cohenMap (K := K) x hmem
  exact ⟨φ, hsurj hx hK⟩

/-- The map from a coefficient field `K` to the residue field is a ring isomorphism. -/
noncomputable def coefficientFieldEquivResidue
    (hK : Function.Surjective fun k : K => residue R (algebraMap K R k)) :
    K ≃+* ResidueField R :=
  RingEquiv.ofBijective ((residue R).comp (algebraMap K R))
    ⟨((residue R).comp (algebraMap K R)).injective, hK⟩

/-- Volume 1, Corollary 4.4.8 of the handbook, in the form of the handbook, with a coefficient
field as a hypothesis. Under the hypotheses of
`exists_surjective_mvPowerSeries_of_coefficientField`, the ring `R` is a quotient of
`κ[[X_1, ..., X_e]]`, where `κ` is the residue field and `e = spanFinrank 𝔪`. -/
theorem exists_surjective_mvPowerSeries_residueField [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (hK : Function.Surjective fun k : K => residue R (algebraMap K R k)) :
    ∃ φ : MvPowerSeries (Fin (maximalIdeal R).spanFinrank) (ResidueField R) →+* R,
      Function.Surjective φ := by
  obtain ⟨ψ, hψ⟩ := exists_surjective_mvPowerSeries_of_coefficientField hK
  let e := coefficientFieldEquivResidue hK
  refine ⟨ψ.toRingHom.comp (MvPowerSeries.map (e.symm : ResidueField R →+* K)), ?_⟩
  intro r
  obtain ⟨f, rfl⟩ := hψ r
  refine ⟨MvPowerSeries.map (e : K →+* ResidueField R) f, ?_⟩
  simp only [RingHom.comp_apply, MvPowerSeries.map_map]
  have : (e.symm : ResidueField R →+* K).comp (e : K →+* ResidueField R) = RingHom.id K := by
    ext k
    simp
  rw [this, MvPowerSeries.map_id]
  rfl

end Singularity.Algebra
