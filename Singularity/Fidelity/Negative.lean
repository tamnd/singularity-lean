/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.Basic

/-!
# Fidelity check F3: negative instances

A correct statement must reject the maps that are not resolutions. This file proves the first negative instance of spec 06.3.

Let `X` be a scheme with a point in its regular locus, and let `π : X ⨿ X ⟶ X` be the codiagonal. Then `π` is not a resolution of `X`. The proof uses only the condition `isIso_over`: over an open set that contains a regular point `x`, the map `π` would be injective, but the two copies of `x` have the same image.

The codiagonal of a regular scheme satisfies the other conditions of `IsResolution`, so the condition `isIso_over` is necessary. Without it, an alteration of degree 2 counts as a resolution.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Singularity.Fidelity

/-- The codiagonal `X ⨿ X ⟶ X`. -/
noncomputable abbrev codiag (X : Scheme.{u}) : X ⨿ X ⟶ X := coprod.desc (𝟙 X) (𝟙 X)

/-- The two copies of a point of `X` in `X ⨿ X` are different points. -/
lemma inl_ne_inr {X : Scheme.{u}} (x : X) :
    (coprod.inl : X ⟶ X ⨿ X).base x ≠ (coprod.inr : X ⟶ X ⨿ X).base x := by
  intro h
  have := (isCompl_range_inl_inr X X).disjoint.le_bot
    ⟨⟨x, rfl⟩, ⟨x, h.symm⟩⟩
  exact this

/-- The codiagonal of a scheme with a regular point is not a resolution. -/
theorem not_isResolution_codiag {X : Scheme.{u}} (x : X) (hx : x ∈ regularLocus X) :
    ¬ IsResolution (codiag X) := by
  rintro ⟨-, -, ⟨U, hU, hiso⟩, -⟩
  have hxU : x ∈ (U : Set X) := hU ▸ hx
  have hinj : Function.Injective (codiag X ∣_ U).base :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (codiag X ∣_ U)))).injective
  have hl : (codiag X).base ((coprod.inl : X ⟶ X ⨿ X).base x) = x := by
    exact congrArg (fun f : X ⟶ X => f.base x) (coprod.inl_desc (𝟙 X) (𝟙 X))
  have hr : (codiag X).base ((coprod.inr : X ⟶ X ⨿ X).base x) = x := by
    exact congrArg (fun f : X ⟶ X => f.base x) (coprod.inr_desc (𝟙 X) (𝟙 X))
  have ha : (coprod.inl : X ⟶ X ⨿ X).base x ∈ codiag X ⁻¹ᵁ U := by
    rw [Scheme.Hom.mem_preimage, hl]
    exact hxU
  have hb : (coprod.inr : X ⟶ X ⨿ X).base x ∈ codiag X ⁻¹ᵁ U := by
    rw [Scheme.Hom.mem_preimage, hr]
    exact hxU
  have heq : (codiag X ∣_ U).base ⟨_, ha⟩ = (codiag X ∣_ U).base ⟨_, hb⟩ := by
    apply Subtype.ext
    first
      | exact (morphismRestrict_base_coe (codiag X) U ⟨_, ha⟩).trans
          (hl.trans (hr.trans (morphismRestrict_base_coe (codiag X) U ⟨_, hb⟩).symm))
      | (simp only [morphismRestrict_base_coe]; exact hl.trans hr.symm)
  exact inl_ne_inr x (congrArg Subtype.val (hinj heq))

/-- The codiagonal of a nonempty regular scheme is not a resolution. -/
theorem not_isResolution_codiag_of_isRegularScheme {X : Scheme.{u}} (hX : IsRegularScheme X)
    (x : X) : ¬ IsResolution (codiag X) :=
  not_isResolution_codiag x ((regularLocus_eq_univ_iff X).mpr hX ▸ Set.mem_univ x)

end Singularity.Fidelity
