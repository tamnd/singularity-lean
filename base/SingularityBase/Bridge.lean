/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import SingularityBase.CharZero
import Singularity.Bridge.FormalConjectures
import Singularity.Known.DimZero
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv

/-!
# The bridge to formal-conjectures

This file proves that the statement of the project implies the statement of google-deepmind/formal-conjectures where they meet: integral varieties over a perfect field.

Let `X` be an integral variety over a perfect field `k`, and let `π : Y ⟶ X` be a resolution in the sense of `IsResolution`. Then `π` is a resolution in the sense of `HasResolution`:

* the generic point of `X` is regular, because its local ring is a field. So the regular locus `U` is a nonempty open set of an irreducible space, and it is dense;
* `π⁻¹(U)` is isomorphic to `U`, so it is irreducible, and it is dense in `Y`. Thus `Y` is irreducible. `Y` is regular, so it is reduced. Thus `Y` is integral;
* `Y` is regular and locally of finite type over the perfect field `k`, so it is smooth over `k` (`Scheme.smooth_iff_isRegular` of the base);
* the isomorphism `π⁻¹(U) ≅ U` is a partial isomorphism over `X`, so `π` is birational over `X`.

As a result, `IntegralResolutionInDim p n` implies the statement of formal-conjectures in dimension `n`, and Hironaka's theorem in the form of formal-conjectures follows from the integral case in characteristic 0. This needs no named hypothesis.
-/

open AlgebraicGeometry CategoryTheory Topology

universe u

namespace Singularity.Base

/-- The generic point of an integral scheme is in its regular locus, because its local ring is a field. -/
lemma genericPoint_mem_regularLocus (X : Scheme.{u}) [IsIntegral X] :
    genericPoint X ∈ regularLocus X :=
  isRegularLocalRing_of_isField (isField_stalk_of_closure_mem_irreducibleComponents X _
    (by simp [irreducibleComponents_eq_singleton]))

/-- A regular scheme is reduced, because a regular local ring is a domain. -/
lemma isReduced_of_isRegularScheme {Y : Scheme.{u}} (h : IsRegularScheme Y) : IsReduced Y := by
  have : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := fun y => by
    have : IsRegularLocalRing (Y.presheaf.stalk y) := h y
    infer_instance
  exact isReduced_of_isReduced_stalk Y

/-- A resolution in the sense of `IsResolution` of an integral variety over a perfect field is a resolution in the sense of `HasResolution` of formal-conjectures. -/
theorem hasResolution_of_isResolution {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX] (π : Y ⟶ X)
    (h : IsResolution π) : Bridge.HasResolution sX := by
  obtain ⟨U, hU, hiso⟩ := h.isIso_over
  have := hiso
  have := h.proper
  have hη : genericPoint X ∈ (U : Set X) := hU ▸ genericPoint_mem_regularLocus X
  have hUd : Dense (U : Set X) := U.isOpen.dense ⟨_, hη⟩
  have hV : ((π ⁻¹ᵁ U : Y.Opens) : Set Y) = π.base ⁻¹' regularLocus X := by
    rw [← hU]
    rfl
  have hVd : Dense ((π ⁻¹ᵁ U : Y.Opens) : Set Y) := hV ▸ h.dense
  -- `Y` is integral
  have : Nonempty U.toScheme := ⟨⟨_, hη⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have : Nonempty (π ⁻¹ᵁ U).toScheme := ⟨(inv (π ∣_ U)) ⟨_, hη⟩⟩
  have : IsIntegral (π ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion (π ∣_ U)
  have hirr : IsIrreducible (Set.range (π ⁻¹ᵁ U).ι) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (π ⁻¹ᵁ U).ι.continuous.continuousOn
  have hrange : Set.range (π ⁻¹ᵁ U).ι = ((π ⁻¹ᵁ U : Y.Opens) : Set Y) :=
    Scheme.Opens.range_ι _
  have : IrreducibleSpace Y := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← hVd.closure_eq, ← hrange]
    exact isIrreducible_iff_closure.mpr hirr
  have : IsReduced Y := isReduced_of_isRegularScheme h.regular
  have : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
  -- `Y` is smooth over `k`
  have hsm : Smooth (π ≫ sX) := (Scheme.smooth_iff_isRegular (π ≫ sX)).mpr ⟨h.regular⟩
  -- `π` is birational over `X`
  let e : Scheme.PartialIso Y X :=
    { source := π ⁻¹ᵁ U
      dense_source := hVd
      target := U
      dense_target := hUd
      iso := asIso (π ∣_ U) }
  have he : e.IsOver π (𝟙 X) := by
    simp [e, Scheme.PartialIso.IsOver, morphismRestrict_ι]
  exact ⟨Y, π, inferInstance, h.proper, hsm, ⟨e, he⟩⟩

/-- The integral case of the statement of the project implies the statement of formal-conjectures in the same characteristic and dimension. -/
theorem fcResolutionInDim_of_integralResolutionInDim {p n : ℕ}
    (h : IntegralResolutionInDim.{u} p n) : Bridge.FCResolutionInDim.{u} p n := by
  intro k _ _ _ X sX _ _ _ _ hX
  have : IsVariety X sX := ⟨inferInstance, ‹_›, ‹_›, ‹_›⟩
  obtain ⟨Y, π, hπ⟩ := h k X sX hX
  exact hasResolution_of_isResolution sX π hπ

/-- The statement of the project implies the statement of formal-conjectures in the same characteristic and dimension. -/
theorem fcResolutionInDim_of_resolutionInDim {p n : ℕ} (h : ResolutionInDim.{u} p n) :
    Bridge.FCResolutionInDim.{u} p n :=
  fcResolutionInDim_of_integralResolutionInDim (integralResolutionInDim_of_resolutionInDim h)

/-- Hironaka's theorem in the form of formal-conjectures (`resolution_of_singularities_of_charZero`). The proof uses Main Theorem I of the base and the bridge of this file. It takes no named hypothesis. -/
theorem fcResolutionCharZero : Bridge.FCResolutionCharZero.{u} := by
  intro k _ _ X sX _ _ _ _
  have : IsVariety X sX := ⟨inferInstance, ‹_›, ‹_›, ‹_›⟩
  obtain ⟨Y, π, hπ⟩ := exists_isResolution_of_isIntegral X sX
  exact hasResolution_of_isResolution sX π hπ

end Singularity.Base
