/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Known.DimZero
import Singularity.Algebra.Regular
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Normal schemes of dimension at most 1 are regular

This file proves that a locally Noetherian scheme of dimension at most 1 is regular if each local ring is an integrally closed domain. This is Corollary 1.4.3 of Volume 1 of the handbook.

The proof has two steps.

1. The dimension of the local ring at `x` is at most the dimension of `X`.
2. A Noetherian local domain of dimension at most 1 that is integrally closed is regular. In dimension 0 it is a field. In dimension 1 this is `Singularity.Algebra.isRegularLocalRing_iff_isIntegrallyClosed`.

Mathlib has no class for normal schemes yet, so the theorem states the condition on the local rings directly.
-/

open AlgebraicGeometry Order Topology

universe u

namespace Singularity

/-- The dimension of a local ring of a scheme is at most the dimension of the scheme. -/
lemma ringKrullDim_stalk_le_topologicalKrullDim {X : Scheme.{u}} (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  rw [ringKrullDim_stalk_eq_coheight x]
  calc (coheight x : WithBot ℕ∞)
      = coheight ((irreducibleSetEquivPoints (α := X)).symm x) := by
        rw [coheight_orderIso]
    _ ≤ topologicalKrullDim X := coheight_le_krullDim _

/-- A Noetherian local domain of dimension at most 1 that is integrally closed is a regular local ring. -/
theorem isRegularLocalRing_of_isIntegrallyClosed {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (h : ringKrullDim R ≤ 1) :
    IsRegularLocalRing R := by
  obtain ⟨n, hn⟩ := Algebra.exists_ringKrullDim_eq_natCast R
  rw [hn] at h
  have hn1 : n ≤ 1 := by exact_mod_cast h
  interval_cases n
  · have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr (by rw [hn])
    exact isRegularLocalRing_of_isField Ring.KrullDimLE.isField_of_isDomain
  · exact (Algebra.isRegularLocalRing_iff_isIntegrallyClosed (by rw [hn]; rfl)).mpr inferInstance

/-- Let `X` be a locally Noetherian scheme of dimension at most 1. If each local ring of `X` is an integrally closed domain, then `X` is regular. -/
theorem isRegularScheme_of_isIntegrallyClosed_stalk {X : Scheme.{u}} [IsLocallyNoetherian X]
    (h : topologicalKrullDim X ≤ 1)
    (hd : ∀ x : X, IsDomain (X.presheaf.stalk x))
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) : IsRegularScheme X := fun x => by
  have := hd x
  have := hn x
  exact isRegularLocalRing_of_isIntegrallyClosed ((ringKrullDim_stalk_le_topologicalKrullDim x).trans h)

end Singularity
