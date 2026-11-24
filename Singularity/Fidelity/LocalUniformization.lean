/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.LocalUniformization

/-!
# Fidelity of the statements of local uniformization

The definition `HasLocalUniformization` of `Singularity/Statements/LocalUniformization.lean` must not be empty, and the condition on the model must not be vacuous. This file checks both, in the style of spec 06.3.

* `hasLocalUniformization_top`: the trivial valuation of a function field has local uniformization. Its center on each affine model is the generic point, and the local ring there is the function field.
* `algebraMap_mem_of_hasLocalUniformization`: a valuation subring with local uniformization over `k` contains `k`.
* `isFunctionField_of_hasLocalUniformization`: if a valuation subring of `K` has local uniformization over `k`, then `K` is finitely generated over `k`. So no valuation of a field that is not finitely generated over `k` has local uniformization.
-/

open IsLocalRing

namespace Singularity.Fidelity

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The trivial valuation `⊤` of a function field `K` over `k` has local uniformization. Take `A = k[s]` for a finite set `s` that generates `K`. The center of `⊤` on `Spec A` is the zero ideal, so the local ring at the center is `K`, a field. -/
theorem hasLocalUniformization_top (hK : IsFunctionField k K) :
    HasLocalUniformization k (⊤ : ValuationSubring K) := by
  obtain ⟨s, hs⟩ := hK
  set A := Algebra.adjoin k (s : Set K)
  have hfrac : IsFractionRing A K := by
    refine IsFractionRing.of_field A K fun z => ?_
    have hz : z ∈ IntermediateField.adjoin k (s : Set K) := by
      rw [hs]
      exact IntermediateField.mem_top
    obtain ⟨x, hx, y, hy, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, rfl⟩
  have h : ∀ a : A, (a : K) ∈ (⊤ : ValuationSubring K) := fun a => ValuationSubring.mem_top _
  refine ⟨A, h, ⟨⟨s, rfl⟩, hfrac⟩, ?_⟩
  have hP : (valuationCenter (⊤ : ValuationSubring K) A h).primeCompl = nonZeroDivisors A := by
    ext a
    rw [Ideal.mem_primeCompl_iff, mem_nonZeroDivisors_iff_ne_zero]
    constructor
    · rintro ha rfl
      exact ha (Ideal.zero_mem _)
    · intro ha hmem
      have hne : (a : K) ≠ 0 := fun h0 => ha (Subtype.ext h0)
      rw [valuationCenter, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff] at hmem
      exact hmem (isUnit_iff_exists_inv.mpr
        ⟨⟨(a : K)⁻¹, ValuationSubring.mem_top _⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩)
  have : IsLocalization (valuationCenter (⊤ : ValuationSubring K) A h).primeCompl K := by
    rw [hP]
    exact hfrac
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv
    (valuationCenter (⊤ : ValuationSubring K) A h).primeCompl K
    (Localization.AtPrime (valuationCenter (⊤ : ValuationSubring K) A h))).toRingEquiv

/-- A valuation subring with local uniformization over `k` contains the image of `k`, because it contains a `k`-subalgebra. -/
theorem algebraMap_mem_of_hasLocalUniformization {V : ValuationSubring K}
    (h : HasLocalUniformization k V) (a : k) : algebraMap k K a ∈ V := by
  obtain ⟨A, hAV, -, -⟩ := h
  exact hAV ⟨algebraMap k K a, A.algebraMap_mem a⟩

/-- If a valuation subring of `K` has local uniformization over `k`, then `K` is a function field over `k`: the generators of the model generate `K` as a field. -/
theorem isFunctionField_of_hasLocalUniformization {V : ValuationSubring K}
    (h : HasLocalUniformization k V) : IsFunctionField k K := by
  obtain ⟨A, -, ⟨⟨s, hs⟩, hA⟩, -⟩ := h
  refine ⟨s, eq_top_iff.mpr fun x _ => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hle : ∀ c : A, (c : K) ∈ IntermediateField.adjoin k (s : Set K) := fun c =>
    IntermediateField.algebra_adjoin_le_adjoin k _ (by rw [hs]; exact c.2)
  exact div_mem (hle a) (hle b)

end Singularity.Fidelity
