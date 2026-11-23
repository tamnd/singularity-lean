/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.ExtCriterion

/-!
# Toward the converse of the theorem of Serre

Let `R` be a Noetherian local ring with maximal ideal `𝔪` and residue field `k`. The theorem of
Serre states that `R` is regular if and only if `pd k < ∞` ([Ser55], [Mat89, Theorem 19.2]).
This file proves parts of the converse direction.

## Main results

* `lTensor_residueField_injective_of_socle`: let `j : k → R` be injective and let
  `φ : K → F` be an injective map of flat modules. Then `k ⊗ φ` is injective.
* `free_of_hasProjectiveDimensionLT_of_socle`: if some `s ≠ 0` has `𝔪 s = 0`, then each finite
  module of finite projective dimension is free.
* `maximalIdeal_eq_bot_of_socle`: if some `s ≠ 0` has `𝔪 s = 0` and `pd k < ∞`, then `𝔪 = 0`.

## The proof

If `s ≠ 0` and `𝔪 s = 0`, then `a ↦ a s` is an injective map `j : k → R`. Let
`0 → K → F → M → 0` be exact with `K` and `F` free. In the square

  `k ⊗ K → k ⊗ F`
  `R ⊗ K → R ⊗ F`

the vertical maps `j ⊗ K` and `j ⊗ F` are injective, because `K` and `F` are flat. The lower map
is injective. Thus the upper map is injective, and the criterion of Mathlib shows that `M` is free.
Induction on the projective dimension gives the general case. This argument replaces the
minimal resolution in the proof of [Mat89, Theorem 19.2].

## References

* [Ser55] J.-P. Serre, *Sur la dimension homologique des anneaux et des modules noethériens*,
  1956.
* [Mat89] H. Matsumura, *Commutative Ring Theory*, Cambridge University Press, 1989.
-/

universe u

open CategoryTheory Abelian IsLocalRing Module TensorProduct

namespace Singularity.Algebra

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Let `j : k → R` be injective and let `φ : K → F` be an injective map of flat modules. Then
`k ⊗ φ` is injective. -/
theorem lTensor_residueField_injective_of_socle {K F : Type u} [AddCommGroup K] [Module R K]
    [AddCommGroup F] [Module R F] [Module.Flat R K] [Module.Flat R F] (φ : K →ₗ[R] F)
    (hφ : Function.Injective φ) (j : ResidueField R →ₗ[R] R) (hj : Function.Injective j) :
    Function.Injective (φ.lTensor (ResidueField R)) := by
  have hcomm : (φ.lTensor R).comp (j.rTensor K) = (j.rTensor F).comp (φ.lTensor _) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have h1 : Function.Injective ((φ.lTensor R).comp (j.rTensor K)) :=
    (Module.Flat.lTensor_preserves_injective_linearMap φ hφ).comp
      (Module.Flat.rTensor_preserves_injective_linearMap j hj)
  rw [hcomm, LinearMap.coe_comp] at h1
  exact h1.of_comp

/-- If `s ≠ 0` and `𝔪 s = 0`, then `a ↦ a s` is an injective map from the residue field
to `R`. -/
theorem exists_injective_residueField_of_socle {s : R} (hs : s ≠ 0)
    (hm : ∀ a ∈ maximalIdeal R, a * s = 0) :
    ∃ j : ResidueField R →ₗ[R] R, Function.Injective j := by
  have hker : maximalIdeal R = LinearMap.ker (LinearMap.mulRight R s) := by
    ext a
    rw [LinearMap.mem_ker, LinearMap.mulRight_apply]
    refine ⟨hm a, fun h => ?_⟩
    by_contra ha
    exact hs ((IsLocalRing.notMem_maximalIdeal.mp ha).mul_left_cancel (by rw [h, mul_zero]))
  refine ⟨Submodule.liftQ (maximalIdeal R) (LinearMap.mulRight R s) hker.le, ?_⟩
  exact LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ hker.le hker.ge)

variable [IsNoetherianRing R]

/-- If some `s ≠ 0` has `𝔪 s = 0`, then each finite module of finite projective dimension
is free. -/
theorem free_of_hasProjectiveDimensionLT_of_socle {s : R} (hs : s ≠ 0)
    (hm : ∀ a ∈ maximalIdeal R, a * s = 0) (n : ℕ) :
    ∀ (M : ModuleCat.{u} R) [Module.Finite R M], HasProjectiveDimensionLT M n →
      Module.Free R M := by
  obtain ⟨j, hj⟩ := exists_injective_residueField_of_socle hs hm
  induction n with
  | zero =>
    intro M _ h
    have hz := isZero_of_hasProjectiveDimensionLT_zero M
    have : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp hz
    exact Module.Free.of_subsingleton R M
  | succ n ih =>
    intro M _ h
    obtain ⟨P, _, _, _, _, f, surjf⟩ := Module.exists_finite_presentation R M
    let S := f.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer surjf
    cases n with
    | zero =>
      have : Module.Projective R M :=
        (IsProjective.iff_projective (R := R) M).mpr
          (projective_iff_hasProjectiveDimensionLT_one.mpr h)
      exact Module.free_of_flat_of_isLocalRing
    | succ n =>
      have hK : HasProjectiveDimensionLT S.X₁ (n + 1) :=
        (hS.hasProjectiveDimensionLT_X₃_iff n
          (inferInstanceAs (Projective (ModuleCat.of R P)))).mp h
      have : Module.Free R (LinearMap.ker f) := ih S.X₁ hK
      exact Module.free_of_lTensor_residueField_injective (LinearMap.ker f).subtype f surjf
        f.exact_subtype_ker_map
        (lTensor_residueField_injective_of_socle _ Subtype.val_injective j hj)

/-- If some `s ≠ 0` has `𝔪 s = 0` and the residue field has finite projective dimension, then
`𝔪 = 0`. -/
theorem maximalIdeal_eq_bot_of_socle {s : R} (hs : s ≠ 0)
    (hm : ∀ a ∈ maximalIdeal R, a * s = 0) (n : ℕ)
    (h : HasProjectiveDimensionLT (ModuleCat.of R (ResidueField R)) n) :
    maximalIdeal R = ⊥ := by
  have := free_of_hasProjectiveDimensionLT_of_socle hs hm n _ h
  let b := Module.Free.chooseBasis R (ResidueField R)
  obtain ⟨i⟩ : Nonempty (Module.Free.ChooseBasisIndex R (ResidueField R)) := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    have : Subsingleton (ResidueField R) := b.repr.toEquiv.subsingleton
    exact zero_ne_one (Subsingleton.elim (0 : ResidueField R) 1)
  rw [eq_bot_iff]
  intro a ha
  have h0 : a • b i = 0 := by
    rw [Algebra.smul_def, ResidueField.algebraMap_eq, (residue_eq_zero_iff a).mpr ha, zero_mul]
  have := congrArg (fun v => b.repr v i) h0
  simpa using this

end Singularity.Algebra
