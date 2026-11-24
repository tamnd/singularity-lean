/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.Embedded
import Singularity.Algebra.Regular

/-!
# Fidelity of the statement of embedded resolution

The definitions of `Singularity/Statements/Embedded.lean` must not be empty, and they must not hold for each ideal sheaf. This file checks both, in the style of spec 06.3.

* `isSncDivisor_top`: on a regular scheme the unit ideal sheaf, the empty divisor, has simple normal crossings.
* `isEmbeddedResolution_id_top`: for a regular scheme `Z` and the empty subscheme `X = ∅`, the identity of `Z` is an embedded resolution, with the empty exceptional divisor.
* `not_isSncDivisor_bot`: on a nonempty regular scheme the zero ideal sheaf, which defines all of `Z`, is not a divisor with simple normal crossings.

The last check uses that a regular local ring is a domain (Stacks tag 00NP, [Mat89, Theorem 14.3]).

## References

* [Mat89] H. Matsumura, *Commutative ring theory*, 1989.
* [Sta] The Stacks project authors, *The Stacks project*.
-/

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Singularity.Fidelity

variable {Z : Scheme.{u}}

/-- On a regular scheme the unit ideal sheaf has simple normal crossings. -/
theorem isSncDivisor_top (hZ : IsRegularScheme Z) : IsSncDivisor (⊤ : Z.IdealSheafData) := by
  intro z
  have := hZ z
  rw [stalkIdeal_top]
  exact isSncAt_top

/-- The empty subscheme has normal crossings with each divisor, because it has no points. -/
theorem hasNormalCrossings_top (D : Z.IdealSheafData) :
    HasNormalCrossings (⊤ : Z.IdealSheafData) D := by
  intro z hz
  rw [← SetLike.mem_coe, Scheme.IdealSheafData.support_top] at hz
  simp at hz

/-- The strict transform of the empty subscheme is empty. -/
theorem strictTransform_top {Z' : Scheme.{u}} (π : Z' ⟶ Z) (U : Z.Opens) :
    strictTransform (⊤ : Z.IdealSheafData) π U = ⊤ := by
  have h : (⟨closure (π.base ⁻¹' (((⊤ : Z.IdealSheafData).support : Set Z) ∩ U)),
      isClosed_closure⟩ : TopologicalSpace.Closeds Z') = ⊥ := by
    ext x
    simp [Scheme.IdealSheafData.support_top]
  rw [strictTransform, h, Scheme.IdealSheafData.vanishingIdeal_bot]

/-- For a regular scheme `Z` and the empty subscheme, the identity of `Z` is an embedded resolution, with `U = Z` and the empty exceptional divisor. -/
theorem isEmbeddedResolution_id_top (hZ : IsRegularScheme Z) :
    IsEmbeddedResolution (⊤ : Z.IdealSheafData) (𝟙 Z) ⊤ ⊤ where
  regular := hZ
  proper := inferInstance
  compl_subset := by simp
  isIso_over := inferInstance
  support_eq := by simp [Scheme.IdealSheafData.support_top]
  snc := isSncDivisor_top hZ
  normalCrossings := by
    rw [strictTransform_top]
    exact hasNormalCrossings_top ⊤

/-- In a regular local ring the zero ideal does not have simple normal crossings. A product of members of a regular system of parameters is not zero. -/
theorem not_isSncAt_bot {R : Type*} [CommRing R] [IsRegularLocalRing R] :
    ¬ IsSncAt (⊥ : Ideal R) := by
  classical
  rintro ⟨s, hs, t, hts, h⟩
  have := Algebra.isDomain_of_isRegularLocalRing R
  have h0 : ∏ x ∈ t, x = 0 := Ideal.span_singleton_eq_bot.mp h.symm
  obtain ⟨x, hxt, hx0⟩ := Finset.prod_eq_zero_iff.mp h0
  have h0s : (0 : R) ∈ s := hx0 ▸ hts hxt
  have hspan : Ideal.span ((s.erase 0 : Finset R) : Set R) = maximalIdeal R := by
    rw [← hs.1]
    conv_rhs => rw [← Finset.insert_erase h0s]
    rw [Finset.coe_insert, Ideal.span_insert_zero]
  have h1 : (maximalIdeal R).spanFinrank ≤ (s.erase 0).card := by
    rw [← hspan]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)).trans_eq
      (Set.ncard_coe_finset _)
  have h2 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = s.card :=
    IsRegularLocalRing.spanFinrank_maximalIdeal.trans hs.2.symm
  have h2' : (maximalIdeal R).spanFinrank = s.card := by exact_mod_cast h2
  have h3 := Finset.card_erase_of_mem h0s
  have h4 := Finset.card_pos.mpr ⟨0, h0s⟩
  omega

/-- On a nonempty regular scheme the zero ideal sheaf is not a divisor with simple normal crossings. -/
theorem not_isSncDivisor_bot (hZ : IsRegularScheme Z) (z : Z) :
    ¬ IsSncDivisor (⊥ : Z.IdealSheafData) := by
  intro h
  have := hZ z
  have hz := h z
  rw [stalkIdeal_bot] at hz
  exact not_isSncAt_bot hz

end Singularity.Fidelity
