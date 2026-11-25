/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.Basic
import Singularity.Algebra.Regular
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Alterations

This file defines an alteration of an integral scheme, as in [dJ96, 2.20] and Definition 1.1.1 of Volume 8 of the handbook. It proves three basic facts: the identity is an alteration, a composite of two alterations is an alteration, and a proper morphism of integral schemes that is an isomorphism over a nonempty open set is an alteration. A resolution of an integral scheme in the sense of `Singularity.IsResolution` is of this kind, so it is an alteration.

The proof for the composite needs the generic fibre. Let `f : X' ⟶ X` be an alteration that is finite over the nonempty open set `U`. A dominant morphism of irreducible schemes maps the generic point to the generic point. The fibre of the finite morphism `f⁻¹(U) ⟶ U` over the generic point of `X` is discrete, and the generic point of `X'` specializes to each point of this fibre. A discrete space is T1, so the generic fibre is the generic point of `X'` alone (`IsAlteration.eq_genericPoint`). Now let `g : X'' ⟶ X'` be an alteration that is finite over `U'`. The image under `f` of the closed set `X' \ U'` is closed, because `f` is proper, and it does not contain the generic point of `X`. Over the complement `V` of this image in `U`, both `f` and `g` are finite, so `g ≫ f` is finite over `V`.

## Main results

* `Singularity.IsAlteration`: the definition.
* `Singularity.IsAlteration.eq_genericPoint`: the fibre of an alteration over the generic point is the generic point alone.
* `Singularity.IsAlteration.id`: the identity of an integral scheme is an alteration.
* `Singularity.IsAlteration.comp`: a composite of two alterations is an alteration.
* `Singularity.IsAlteration.of_isIso_restrict`: a proper morphism of integral schemes that is an isomorphism over a nonempty open set is an alteration.
* `Singularity.IsResolution.isIntegral` and `Singularity.IsResolution.isAlteration`: a resolution of an integral scheme has an integral source, and it is an alteration.
-/

open AlgebraicGeometry CategoryTheory Topology

universe u

namespace Singularity

/-- The morphism `f : X' ⟶ X` is an alteration (Definition 1.1.1 of Volume 8, [dJ96, 2.20]):
* `X'` and `X` are integral;
* `f` is proper;
* `f` is dominant;
* there is a nonempty open set `U` of `X` such that `f⁻¹(U) ⟶ U` is finite.

De Jong asks that `X` is Noetherian. This definition does not, because none of the basic lemmas needs it, and a variety is Noetherian. Apart from this point it is the definition of [dJ96, 2.20] word for word. A proper dominant morphism has a closed and dense image, so it is surjective. The last condition says that `f` is generically finite. Mathlib has Zariski's main theorem in the form `exists_isFinite_morphismRestrict_of_finite_preimage_singleton`, so for a proper `f` the last condition is equivalent to the condition that the fibre over the generic point of `X` is finite. This file does not need that form. -/
structure IsAlteration {X X' : Scheme.{u}} (f : X' ⟶ X) : Prop where
  integral_source : IsIntegral X'
  integral_target : IsIntegral X
  proper : IsProper f
  dominant : IsDominant f
  finite_over : ∃ U : X.Opens, (U : Set X).Nonempty ∧ IsFinite (f ∣_ U)

section Restrict

variable {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- A finite morphism over `U` is finite over each open set `V ≤ U`. -/
lemma isFinite_restrict_of_le (f : X ⟶ Y) {U V : Y.Opens} (hVU : V ≤ U) [IsFinite (f ∣_ U)] :
    IsFinite (f ∣_ V) := by
  have h1 : IsFinite (f ∣_ U ∣_ U.ι ⁻¹ᵁ V) := inferInstance
  have h2 := (MorphismProperty.arrow_mk_iso_iff @IsFinite
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V))).mp h1
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hVU
  exact (MorphismProperty.arrow_mk_iso_iff @IsFinite (morphismRestrictEq f e)).mp h2

end Restrict

section GenericPoint

variable {X X' : Scheme.{u}}

/-- A dominant morphism of irreducible schemes maps the generic point to the generic point. -/
lemma apply_genericPoint_of_isDominant [IrreducibleSpace X'] [IrreducibleSpace X] (f : X' ⟶ X)
    [IsDominant f] : f (genericPoint X') = genericPoint X := by
  have h := (genericPoint_spec X').image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at h
  exact h.eq (genericPoint_spec X)

/-- The generic point of an irreducible scheme is in each nonempty open set. -/
lemma genericPoint_mem_of_nonempty [IrreducibleSpace X] (U : X.Opens) (hU : (U : Set X).Nonempty) :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)

/-- In a discrete subset, a specialization is an equality. -/
lemma eq_of_specializes_of_isDiscrete {T : Type*} [TopologicalSpace T] {s : Set T}
    (hs : IsDiscrete s) {x y : T} (hx : x ∈ s) (hy : y ∈ s) (h : x ⤳ y) : x = y := by
  have : DiscreteTopology s := isDiscrete_iff_discreteTopology.mp hs
  have h' : (⟨x, hx⟩ : s) ⤳ ⟨y, hy⟩ := IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val h'.eq

/-- The fibre of an alteration over the generic point is the generic point alone. -/
theorem IsAlteration.eq_genericPoint [IsIntegral X] [IsIntegral X'] {f : X' ⟶ X}
    (hf : IsAlteration f) {x : X'} (hx : f x = genericPoint X) : x = genericPoint X' := by
  have := hf.dominant
  obtain ⟨U, hU, hfin⟩ := hf.finite_over
  have hηU : genericPoint X ∈ U := genericPoint_mem_of_nonempty U hU
  have hη' : f (genericPoint X') = genericPoint X := apply_genericPoint_of_isDominant f
  have hxU : x ∈ f ⁻¹ᵁ U := by simpa [hx] using hηU
  have hη'U : genericPoint X' ∈ f ⁻¹ᵁ U := by simpa [hη'] using hηU
  let a : (f ⁻¹ᵁ U : Scheme.{u}) := ⟨x, hxU⟩
  let b : (f ⁻¹ᵁ U : Scheme.{u}) := ⟨genericPoint X', hη'U⟩
  let y : (U : Scheme.{u}) := ⟨genericPoint X, hηU⟩
  have ha : (f ∣_ U) a = y := Subtype.ext (by rw [morphismRestrict_base_coe]; exact hx)
  have hb : (f ∣_ U) b = y := Subtype.ext (by rw [morphismRestrict_base_coe]; exact hη')
  have hs := (f ∣_ U).isDiscrete_preimage_singleton y
  have hspec : b ⤳ a :=
    (f ⁻¹ᵁ U).ι.isOpenEmbedding.isInducing.specializes_iff.mp
      ((genericPoint_spec X').specializes (Set.mem_univ _))
  have := eq_of_specializes_of_isDiscrete hs hb ha hspec
  exact (congrArg Subtype.val this).symm

end GenericPoint

namespace IsAlteration

variable {X X' X'' : Scheme.{u}}

/-- The identity of an integral scheme is an alteration. -/
protected theorem id (X : Scheme.{u}) [IsIntegral X] : IsAlteration (𝟙 X) where
  integral_source := inferInstance
  integral_target := inferInstance
  proper := inferInstance
  dominant := inferInstance
  finite_over := ⟨⊤, ⟨genericPoint X, trivial⟩, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-- A composite of two alterations is an alteration. -/
protected theorem comp {g : X'' ⟶ X'} {f : X' ⟶ X} (hg : IsAlteration g) (hf : IsAlteration f) :
    IsAlteration (g ≫ f) where
  integral_source := hg.integral_source
  integral_target := hf.integral_target
  proper := by
    have := hg.proper
    have := hf.proper
    infer_instance
  dominant := by
    have := hg.dominant
    have := hf.dominant
    infer_instance
  finite_over := by
    have := hf.integral_source
    have := hf.integral_target
    have := hf.proper
    obtain ⟨U, hU, hfU⟩ := hf.finite_over
    obtain ⟨U', hU', hgU'⟩ := hg.finite_over
    have hC : IsClosed (f '' (U' : Set X')ᶜ) := f.isClosedMap _ U'.isOpen.isClosed_compl
    let V : X.Opens := U ⊓ ⟨(f '' (U' : Set X')ᶜ)ᶜ, hC.isOpen_compl⟩
    have hηU' : genericPoint X' ∈ U' := genericPoint_mem_of_nonempty U' hU'
    have hηV : genericPoint X ∈ V := by
      refine ⟨genericPoint_mem_of_nonempty U hU, ?_⟩
      rintro ⟨x, hx, hfx⟩
      exact hx (hf.eq_genericPoint hfx ▸ hηU')
    refine ⟨V, ⟨_, hηV⟩, ?_⟩
    rw [morphismRestrict_comp]
    have h1 : IsFinite (f ∣_ V) := isFinite_restrict_of_le f inf_le_left
    have hle : f ⁻¹ᵁ V ≤ U' := fun x hx => by
      by_contra h
      exact hx.2 ⟨x, h, rfl⟩
    have h2 : IsFinite (g ∣_ f ⁻¹ᵁ V) := isFinite_restrict_of_le g hle
    infer_instance

/-- A proper morphism of integral schemes that is an isomorphism over a nonempty open set is an alteration. This covers the proper birational morphisms of [dJ96, 2.17]. -/
theorem of_isIso_restrict [IsIntegral X] [IsIntegral X'] (f : X' ⟶ X) [IsProper f] (U : X.Opens)
    (hU : (U : Set X).Nonempty) [IsIso (f ∣_ U)] : IsAlteration f where
  integral_source := inferInstance
  integral_target := inferInstance
  proper := inferInstance
  dominant := by
    have hsub : (U : Set X) ⊆ Set.range f := fun x hx => by
      obtain ⟨y, hy⟩ := (f ∣_ U).surjective ⟨x, hx⟩
      exact ⟨y.1, by rw [← morphismRestrict_base_coe, hy]⟩
    exact ⟨(U.isOpen.dense hU).mono hsub⟩
  finite_over := ⟨U, hU, inferInstance⟩

end IsAlteration

namespace IsResolution

variable {X Y : Scheme.{u}}

/-- The generic point of an integral scheme is a regular point: its local ring is the function field. -/
lemma genericPoint_mem_regularLocus [IsIntegral X] : genericPoint X ∈ regularLocus X := by
  change IsRegularLocalRing X.functionField
  infer_instance

/-- A resolution of an integral scheme has an integral source (Lemma 1.1.15 of Volume 8). The source is regular, so it is reduced. The resolution is an isomorphism over the regular locus `U`, which is a nonempty open set, so the preimage of `U` is irreducible. It is dense, so the source is irreducible. -/
theorem isIntegral [IsIntegral X] {π : Y ⟶ X} (h : IsResolution π) : IsIntegral Y := by
  obtain ⟨U, hUeq, hiso⟩ := h.isIso_over
  have hU : (U : Set X).Nonempty := ⟨genericPoint X, hUeq ▸ genericPoint_mem_regularLocus⟩
  have : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := fun y => by
    have := h.regular y
    have := Algebra.isDomain_of_isRegularLocalRing (Y.presheaf.stalk y)
    infer_instance
  have : IsReduced Y := isReduced_of_isReduced_stalk Y
  have : Nonempty U := hU.to_subtype
  let e : (U : Scheme.{u}) ⟶ Y := inv (π ∣_ U) ≫ (π ⁻¹ᵁ U).ι
  have hsub : π.base ⁻¹' (U : Set X) ⊆ Set.range e := fun y hy => by
    refine ⟨(π ∣_ U) ⟨y, hy⟩, ?_⟩
    have h1 := Scheme.hom_inv_apply (asIso (π ∣_ U)) ⟨y, hy⟩
    simp only [asIso_hom, asIso_inv] at h1
    simp [e, h1]
  have hirr : IsIrreducible (Set.range e) := by
    simpa [Set.image_univ] using (IrreducibleSpace.isIrreducible_univ (U : Scheme.{u})).image e
      e.continuous.continuousOn
  have hdense : Dense (Set.range e) := (hUeq ▸ h.dense).mono hsub
  have : IrreducibleSpace Y := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← hdense.closure_eq]
    exact hirr.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

/-- A resolution of an integral scheme is an alteration (Lemma 1.1.15 of Volume 8). -/
theorem isAlteration [IsIntegral X] {π : Y ⟶ X} (h : IsResolution π) : IsAlteration π := by
  have := h.isIntegral
  have := h.proper
  obtain ⟨U, hUeq, hiso⟩ := h.isIso_over
  exact IsAlteration.of_isIso_restrict π U
    ⟨genericPoint X, hUeq ▸ genericPoint_mem_regularLocus⟩

end IsResolution

end Singularity
