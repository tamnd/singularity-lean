/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.Fundamental
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Fidelity of the statements of Section 3.24

The definitions of `Singularity/Statements/Fundamental.lean` must not be empty, and the open statements must not be trivially true. This file checks this, in the style of spec 06.3, and it proves the implications of Section 3.24 that have short proofs.

* `centerLocalRing_subset`: an affine model is contained in its local ring at the center of a valuation.
* `modelDominates_refl`: a model dominates itself.
* `fundamental_self`: the conclusion of `Fund_n` holds when the two models are the same, with `W = M₀`.
* `hasRegularCenterOn_of_hasRegularCenter`: a regular center on an affine model gives a regular center on each model that has this affine model as a chart.
* `weakLocalUniformization_of_affine`: `LU_n` implies `LU_n^-` (Definition 3.24.1).
* `affineLocalUniformization_of_localUniformization`: `LocalUniformizationInDim p n` of `Singularity/Statements/LocalUniformization.lean` implies `LU_n`.
* `pilu_of_affineLocalUniformization`: `LU_n` implies `PILU_n`. This is the second half of the proof of Theorem 3.24.5.
* `pilu_of_localUniformization`: `LocalUniformizationInDim p n` implies `PILU_n`. With the theorem of Cossart-Piltant (`localUniformization_three`) this gives `PILU_3`.
* `pilu_fundamental_of_resolution`: Theorem 3.24.4 implies one direction of Theorem 3.24.5.
* `isRegularModification_id`: the identity of a regular scheme is a regular modification.
-/

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Singularity.Fidelity

section Model

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- An affine model `B ⊆ V` is contained in its local ring at the center of `V`: `b = b / 1`. -/
theorem centerLocalRing_subset (V : ValuationSubring K) (B : Subalgebra k K) :
    (B : Set K) ⊆ centerLocalRing V B :=
  fun b hb => ⟨b, hb, 1, B.one_mem, one_ne_zero, by rw [inv_one]; exact V.one_mem, by simp⟩

/-- A model dominates itself: this is the identity morphism. -/
theorem modelDominates_refl (M : Set (Subalgebra k K)) : ModelDominates M M :=
  fun B hB V _ => ⟨B, hB, centerLocalRing_subset V B⟩

/-- The conclusion of `Fund_n` holds if the two models are the same: take `W = M₀`. Thus the conclusion of `Fund_n` can hold. -/
theorem fundamental_self {M : Set (Subalgebra k K)} (hM : IsCompleteNormalModel k M) :
    ∃ W : Set (Subalgebra k K), IsCompleteNormalModel k W ∧ ModelDominates W M ∧
      ModelDominates W M ∧ ∀ V : ValuationSubring K,
        HasRegularCenterOn V M ∨ HasRegularCenterOn V M → HasRegularCenterOn V W :=
  ⟨M, hM, modelDominates_refl M, modelDominates_refl M, fun _ h => h.elim id id⟩

/-- If `V` has a regular center on an affine model `B`, then `V` has a regular center on each model that has `B` as a chart. -/
theorem hasRegularCenterOn_of_hasRegularCenter {V : ValuationSubring K} {B : Subalgebra k K}
    {M : Set (Subalgebra k K)} (hBM : B ∈ M) (hB : ∀ b : B, (b : K) ∈ V)
    (h : IsRegularLocalRing (Localization.AtPrime (valuationCenter V B hB))) :
    HasRegularCenterOn V M :=
  ⟨B, hBM, hB, h⟩

end Model

/-! ### Local uniformization -/

/-- `LU_n` implies `LU_n^-`: apply `LU_n` to the empty set. -/
theorem weakLocalUniformization_of_affine {p n : ℕ}
    (h : AffineLocalUniformizationInDim.{u} p n) : WeakLocalUniformizationInDim.{u} p n := by
  intro k K _ _ _ _ _ hK htr V hV
  simpa using h k K hK htr V hV ∅ (by simp)

/-- `LocalUniformizationInDim p n`, over all fields of characteristic `p`, implies `LU_n`, over algebraically closed fields of characteristic `p`. A valuation subring that contains the image of `k` has a unique structure of `k`-algebra. -/
theorem affineLocalUniformization_of_localUniformization {p n : ℕ}
    (h : LocalUniformizationInDim.{u} p n) : AffineLocalUniformizationInDim.{u} p n := by
  intro k K _ _ _ _ _ hK htr V hV s hs
  let _ : Algebra k V := ((algebraMap k K).codRestrict V.toSubring hV).toAlgebra
  have _ : IsScalarTower k V K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact h k K hK htr V s hs

/-- A `p`-th root of an element of a valuation subring is in the valuation subring. -/
theorem mem_of_pow_mem {M : Type*} [Field M] {V : ValuationSubring M} {b : M} {p : ℕ}
    (hp : p ≠ 0) (h : b ^ p ∈ V) : b ∈ V := by
  rw [← ValuationSubring.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff hp).mp h

/-- `LU_n` implies `PILU_n`. This is the second half of the proof of Theorem 3.24.5 in the handbook. Apply `LU_n` to the field `M = L(b)`, to `V` and to the finite set of `b` and the generators of `B`. The field `M` is a function field of dimension `n`, because it is finite over `L`. -/
theorem pilu_of_affineLocalUniformization {p n : ℕ} (hp : p.Prime)
    (h : AffineLocalUniformizationInDim.{u} p n) :
    PurelyInseparableLocalUniformizationInDim.{u} p n := by
  classical
  intro k L M _ _ _ _ _ _ _ _ _ hL htr B V hB hmod _ a ha b hb _ hadj
  have hfin : FiniteDimensional L M := by
    have hi : IsIntegral L b :=
      ⟨Polynomial.X ^ p - Polynomial.C a, Polynomial.monic_X_pow_sub_C a hp.ne_zero, by simp [hb]⟩
    have := IntermediateField.adjoin.finiteDimensional hi
    rw [hadj] at this
    exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  have hM : IsFunctionField k M := by
    rw [IsFunctionField, IntermediateField.fg_top_iff] at hL ⊢
    exact Algebra.EssFiniteType.comp k L M
  have htrM : Algebra.trdeg k M = n := by
    rw [← trdeg_add_eq k L (A := M), (trdeg_eq_zero_iff (R := L) (A := M)).mpr inferInstance,
      add_zero, htr]
  have hV : ∀ c : k, algebraMap k M c ∈ V := by
    intro c
    rw [IsScalarTower.algebraMap_apply k L M]
    exact hB ⟨algebraMap k L c, B.algebraMap_mem c⟩
  obtain ⟨t, ht⟩ := hmod.1
  have hbV : b ∈ V := mem_of_pow_mem hp.ne_zero (by rw [hb]; exact hB ⟨a, ha⟩)
  have hs : ∀ x ∈ insert b (t.image (algebraMap L M)), x ∈ V := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hbV
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have hyB : y ∈ B := ht ▸ Algebra.subset_adjoin hy
      exact hB ⟨y, hyB⟩
  obtain ⟨A, hAV, hAmod, hsA, hreg⟩ := h k M hM htrM V hV _ hs
  refine ⟨A, hAV, hAmod, ?_, hreg⟩
  have hBA : B.map (IsScalarTower.toAlgHom k L M) ≤ A := by
    rw [← ht, AlgHom.map_adjoin]
    refine Algebra.adjoin_le fun x hx => hsA ?_
    obtain ⟨y, hy, rfl⟩ := hx
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hy)
  intro x hx
  rcases hx with rfl | ⟨y, hy, rfl⟩
  · exact hsA (by simp)
  · exact hBA ⟨y, hy, rfl⟩

/-- `LocalUniformizationInDim p n` implies `PILU_n`. For example, the theorem of Cossart-Piltant (`localUniformization_three`) gives `PILU_3`. -/
theorem pilu_of_localUniformization {p n : ℕ} (hp : p.Prime)
    (h : LocalUniformizationInDim.{u} p n) : PurelyInseparableLocalUniformizationInDim.{u} p n :=
  pilu_of_affineLocalUniformization hp (affineLocalUniformization_of_localUniformization h)

/-- Theorem 3.24.4 implies one direction of Theorem 3.24.5: `Res_4^pr` implies `PILU_4` and `Fund_4`. This is the proof in the handbook. -/
theorem pilu_fundamental_of_resolution
    (h : resolution_iff_weakLocalUniformization_fundamental_four.{u}) {p : ℕ} (hp : p.Prime)
    (hres : RegularModificationInDim.{u} p 4) :
    PurelyInseparableLocalUniformizationInDim.{u} p 4 ∧ FundamentalTheoremInDim.{u} p 4 :=
  have h' := (h p hp).2 hres
  ⟨pilu_of_affineLocalUniformization hp h'.1, h'.2⟩

/-! ### Regular modifications -/

/-- The identity of a nonempty regular scheme is a regular modification. -/
theorem isRegularModification_id {X : Scheme.{u}} (hX : IsRegularScheme X) [Nonempty X] :
    IsRegularModification (𝟙 X) where
  regular := hX
  proper := inferInstance
  isIso_over := ⟨⊤, Set.univ_nonempty, inferInstance, by simp⟩

end Singularity.Fidelity
