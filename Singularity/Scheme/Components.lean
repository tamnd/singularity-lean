/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Hypotheses.Integral
import Singularity.Algebra.Regular
import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent

/-!
# The irreducible components of a reduced scheme

Let `X` be a reduced Noetherian scheme. This file proves the facts about the irreducible components of `X` that the reduction to integral varieties uses.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Singularity.Components

/-- Each point lies on an irreducible component. -/
lemma exists_mem_irreducibleComponents {X : Scheme.{u}} (x : X) : ∃ Z ∈ irreducibleComponents X, x ∈ Z := by
  obtain ⟨Z, hZ, h⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x}
    isIrreducible_singleton
  exact ⟨Z, hZ, h rfl⟩

/-- If the local ring at `x` is a domain, then `x` lies on only one irreducible component. -/
lemma eq_of_mem_of_isDomain {X : Scheme.{u}} {x : X} [IsDomain (X.presheaf.stalk x)] {Z₁ Z₂ : Set X}
    (h₁ : Z₁ ∈ irreducibleComponents X) (h₂ : Z₂ ∈ irreducibleComponents X) (hx₁ : x ∈ Z₁)
    (hx₂ : x ∈ Z₂) : Z₁ = Z₂ := by
  have hG : IsIrreducible {y | y ⤳ x} := by
    rw [← Scheme.range_fromSpecStalk, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (X.fromSpecStalk x).continuous.continuousOn
  obtain ⟨Z, hZ, hGZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hG
  have key : ∀ W ∈ irreducibleComponents X, x ∈ W → W = Z := by
    intro W hW hxW
    have hWc : IsClosed W := isClosed_of_mem_irreducibleComponents W hW
    have hη := hW.1.isGenericPoint_genericPoint_closure
    rw [hWc.closure_eq] at hη
    have hηZ : hW.1.genericPoint ∈ Z := hGZ (hη.specializes hxW)
    refine hW.eq_of_subset hZ.1 ?_
    rw [← hη.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hηZ)
      (isClosed_of_mem_irreducibleComponents Z hZ)
  rw [key Z₁ h₁ hx₁, key Z₂ h₂ hx₂]

variable (X : Scheme.{u}) [IsNoetherian X] (Z : Set X) (hZ : Z ∈ irreducibleComponents X)

/-- The subscheme structure on an irreducible component of a reduced Noetherian scheme is reduced. -/
instance isReduced_irreducibleComponent [IsReduced X] : IsReduced (X.irreducibleComponent Z hZ) := by
  let I := X.irreducibleComponentIdeal Z hZ
  have (U : X.affineOpens) : IsReduced (Γ(X, U) ⧸ I.ideal U) := by
    have h : I.ideal U = RingHom.ker ((X.irreducibleComponentOpen Z).ι.app U).hom := by
      rw [show I = (X.irreducibleComponentOpen Z).ι.ker from X.irreducibleComponentIdeal_def Z hZ]
      exact Scheme.Hom.ker_apply _ U
    rw [h]
    exact isReduced_of_injective _ (RingHom.kerLift_injective _)
  have (U : X.affineOpens) : IsReduced (I.subschemeCover.openCover.X U) := by
    have := this U
    exact (inferInstance : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (Γ(X, U) ⧸ I.ideal U))))
  exact @IsReduced.of_openCover (X.irreducibleComponent Z hZ) I.subschemeCover.openCover this

instance isIntegral_irreducibleComponent [IsReduced X] :
    IsIntegral (X.irreducibleComponent Z hZ) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

lemma range_irreducibleComponentι : Set.range (X.irreducibleComponentι Z hZ) = Z := by
  exact (Scheme.IdealSheafData.range_subschemeι _).trans rfl

/-- The complement of the other components is contained in the component. -/
lemma irreducibleComponentOpen_subset : (X.irreducibleComponentOpen Z : Set X) ⊆ Z := by
  intro x hx
  obtain ⟨Z', hZ', hxZ'⟩ := exists_mem_irreducibleComponents x
  by_contra hxZ
  have hne : Z' ≠ Z := by rintro rfl; exact hxZ hxZ'
  exact hx ⟨Z', ⟨hZ', hne⟩, hxZ'⟩

/-- A point of the component that is not on the other components. -/
lemma mem_irreducibleComponentOpen {x : X}
    (h : ∀ Z' ∈ irreducibleComponents X, x ∈ Z' → Z' = Z) : x ∈ X.irreducibleComponentOpen Z := by
  rintro ⟨Z', ⟨hZ', hne⟩, hxZ'⟩
  exact hne (h Z' hZ' hxZ')

/-- Over an open set in the complement of the other components, the inclusion of the component is an isomorphism. -/
lemma isIso_irreducibleComponentι_restrict [IsReduced X] (V : X.Opens)
    (hV : V ≤ X.irreducibleComponentOpen Z) : IsIso (X.irreducibleComponentι Z hZ ∣_ V) := by
  have : Surjective (X.irreducibleComponentι Z hZ ∣_ V) := by
    refine ⟨fun v => ?_⟩
    have hv : v.1 ∈ Set.range (X.irreducibleComponentι Z hZ) := by
      rw [range_irreducibleComponentι]
      exact irreducibleComponentOpen_subset X Z (hV v.2)
    obtain ⟨y, hy⟩ := hv
    refine ⟨⟨y, show _ ∈ V by rw [hy]; exact v.2⟩, ?_⟩
    apply Subtype.ext
    exact (morphismRestrict_base_coe _ _ _).trans hy
  exact isIso_of_isClosedImmersion_of_surjective _

end Singularity.Components
