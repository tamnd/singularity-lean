/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.Main
import Singularity.Fidelity.Positive

/-!
# Resolution in dimension 0

This file proves `resolutionInDim_dim_zero`: each variety of dimension at most 0 over a field has a resolution, in each characteristic. The resolution is the identity.

The proof has three steps.

1. If `X` has dimension at most 0, then each local ring of `X` has dimension 0. The dimension of the local ring at `x` is the coheight of `x` in the specialization order, and the coheight is at most the dimension of `X`.
2. A reduced local ring of dimension 0 is a field.
3. A field is a regular local ring.

Thus a reduced scheme of dimension at most 0 is regular, and its identity is a resolution by check F2. The proof does not use that `X` is of finite type, and it does not use the characteristic.
-/

open AlgebraicGeometry CategoryTheory Order Topology

universe u

namespace Singularity

/-- A field is a regular local ring. -/
lemma isRegularLocalRing_of_isField {R : Type*} [CommRing R] (h : IsField R) :
    IsRegularLocalRing R := by
  let := h.toField
  infer_instance

/-- The local rings of a scheme of dimension at most 0 have dimension 0. -/
lemma krullDimLE_zero_stalk {X : Scheme.{u}} (h : topologicalKrullDim X ≤ 0) (x : X) :
    Ring.KrullDimLE 0 (X.presheaf.stalk x) := by
  rw [Ring.krullDimLE_iff, ringKrullDim_stalk_eq_coheight x]
  calc (coheight x : WithBot ℕ∞)
      = coheight ((irreducibleSetEquivPoints (α := X)).symm x) := by
        rw [coheight_orderIso]
    _ ≤ topologicalKrullDim X := coheight_le_krullDim _
    _ ≤ 0 := h

/-- A reduced scheme of dimension at most 0 is regular. -/
theorem isRegularScheme_of_topologicalKrullDim_le_zero {X : Scheme.{u}} [IsReduced X]
    (h : topologicalKrullDim X ≤ 0) : IsRegularScheme X := fun x => by
  have := krullDimLE_zero_stalk h x
  exact isRegularLocalRing_of_isField Ring.KrullDimLE.isField_of_isReduced

/-- Resolution of singularities in dimension 0, in each characteristic. -/
theorem resolutionInDim_dim_zero (p : ℕ) : ResolutionInDim.{u} p 0 := by
  intro k _ _ X f hX hdim
  have := hX.reduced
  exact ⟨X, 𝟙 X, Fidelity.isResolution_id
    (isRegularScheme_of_topologicalKrullDim_le_zero (by exact_mod_cast hdim))⟩

end Singularity
