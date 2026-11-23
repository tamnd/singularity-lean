/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Regular.ProjectiveDimension
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The Ext criterion for projective dimension over a local ring

Let `R` be a Noetherian local ring with residue field `k`, and let `M` be a finite `R`-module.
This file proves that `pd M ≤ n` if and only if `Ext^(n+1)(M, k) = 0` ([Mat89, Lemma 19.1]).
Mathlib has the criterion with `Ext^n(M, L) = 0` for all finite modules `L`. Here the test
module is only `k`.

## Main results

* `free_of_subsingleton_ext_one_residueField`: if `Ext^1(M, k) = 0`, then `M` is free.
* `hasProjectiveDimensionLT_succ_iff`: `pd M < n + 1` if and only if `Ext^(n+1)(M, k) = 0`.
* `projectiveDimension_le_iff_subsingleton_ext`: the same result for `projectiveDimension`.

## The proof

Let `0 → K → F → M → 0` be a presentation with `F` finite and free. If `Ext^1(M, k) = 0`, then
each map `K → k` extends to `F`. Thus `k ⊗ K → k ⊗ F` is injective, because a linear form on
the `k`-vector space `k ⊗ K` that is not zero on a vector `t` gives a map `K → k`. By the
criterion of Mathlib for a local ring, `M` is free. For `n ≥ 1`, the long exact sequence of
`Ext(-, k)` gives `Ext^(n+1)(M, k) ≅ Ext^n(K, k)`, and induction on `n` completes the proof.

## References

* [Mat89] H. Matsumura, *Commutative Ring Theory*, Cambridge University Press, 1989.
-/

universe u

open CategoryTheory Abelian IsLocalRing Module TensorProduct

namespace Singularity.Algebra

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Let `i : K → F` be a linear map such that each map `K → k` extends along `i`. Then
`k ⊗ i` is injective. -/
theorem lTensor_residueField_injective_of_forall_extend {K F : Type u} [AddCommGroup K]
    [Module R K] [AddCommGroup F] [Module R F] (i : K →ₗ[R] F)
    (h : ∀ g : K →ₗ[R] ResidueField R, ∃ g' : F →ₗ[R] ResidueField R, g' ∘ₗ i = g) :
    Function.Injective (i.lTensor (ResidueField R)) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  refine (Module.forall_dual_apply_eq_zero_iff (ResidueField R) t).mp fun φ => ?_
  let g : K →ₗ[R] ResidueField R :=
    φ.restrictScalars R ∘ₗ TensorProduct.mk R (ResidueField R) K 1
  obtain ⟨g', hg'⟩ := h g
  let ψ : ResidueField R ⊗[R] F →ₗ[R] ResidueField R :=
    TensorProduct.lift ((LinearMap.mul R (ResidueField R)).compl₂ g')
  have key : φ.restrictScalars R = ψ ∘ₗ i.lTensor (ResidueField R) := by
    apply TensorProduct.ext'
    intro a x
    have hx : g' (i x) = φ (1 ⊗ₜ x) := LinearMap.congr_fun hg' x
    have ha : a ⊗ₜ[R] x = a • ((1 : ResidueField R) ⊗ₜ[R] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp only [LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.lTensor_tmul, ψ, TensorProduct.lift.tmul, LinearMap.compl₂_apply,
      LinearMap.mul_apply', hx]
    rw [ha, map_smul, smul_eq_mul]
  have := LinearMap.congr_fun key t
  simpa [ht] using this

variable [IsNoetherianRing R]

/-- Over a Noetherian local ring, a finite module `M` with `Ext^1(M, k) = 0` is free. -/
theorem free_of_subsingleton_ext_one_residueField (M : ModuleCat.{u} R) [Module.Finite R M]
    (h : Subsingleton (Ext M (ModuleCat.of R (ResidueField R)) 1)) : Module.Free R M := by
  obtain ⟨P, _, _, _, _, f, surjf⟩ := Module.exists_finite_presentation R M
  let S := f.shortComplexKer
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer surjf
  have hext : ∀ g : LinearMap.ker f →ₗ[R] ResidueField R,
      ∃ g' : P →ₗ[R] ResidueField R, g' ∘ₗ (LinearMap.ker f).subtype = g := by
    intro g
    obtain ⟨x₂, hx₂⟩ := Ext.contravariant_sequence_exact₁ hS (ModuleCat.of R (ResidueField R))
      (Ext.mk₀ (ModuleCat.ofHom g : S.X₁ ⟶ ModuleCat.of R (ResidueField R))) (n₁ := 1) rfl
      (h.elim _ _)
    obtain ⟨g', rfl⟩ := (Ext.mk₀_bijective _ _).2 x₂
    rw [Ext.mk₀_comp_mk₀, (Ext.mk₀_bijective _ _).1.eq_iff] at hx₂
    refine ⟨g'.hom, ?_⟩
    ext x
    exact congrArg (fun φ => φ.hom x) hx₂
  exact Module.free_of_lTensor_residueField_injective (LinearMap.ker f).subtype f surjf
    f.exact_subtype_ker_map (lTensor_residueField_injective_of_forall_extend _ hext)

/-- Over a Noetherian local ring, a finite module `M` has `pd M < n + 1` if `Ext^(n+1)(M, k)`
is zero. -/
theorem hasProjectiveDimensionLT_of_subsingleton_ext (n : ℕ) :
    ∀ (M : ModuleCat.{u} R) [Module.Finite R M],
      Subsingleton (Ext M (ModuleCat.of R (ResidueField R)) (n + 1)) →
        HasProjectiveDimensionLT M (n + 1) := by
  induction n with
  | zero =>
    intro M _ h
    have := free_of_subsingleton_ext_one_residueField M h
    rw [zero_add, ← projective_iff_hasProjectiveDimensionLT_one]
    exact (IsProjective.iff_projective (R := R) M).mp Module.Projective.of_free
  | succ n ih =>
    intro M _ h
    obtain ⟨P, _, _, _, _, f, surjf⟩ := Module.exists_finite_presentation R M
    let S := f.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer surjf
    rw [hS.hasProjectiveDimensionLT_X₃_iff n inferInstance]
    have hiff : Subsingleton (Ext S.X₁ (ModuleCat.of R (ResidueField R)) (n + 1)) ↔
        Subsingleton (Ext M (ModuleCat.of R (ResidueField R)) (n + 2)) := by
      have (m : ℕ) : Subsingleton (Ext S.X₂ (ModuleCat.of R (ResidueField R)) (m + 1)) :=
        Ext.subsingleton_of_projective S.X₂ _ m
      have isi : IsIso (AddCommGrpCat.ofHom
          (hS.extClass.precomp (ModuleCat.of R (ResidueField R)) (add_comm 1 _))) :=
        (Ext.contravariantSequence_exact hS (ModuleCat.of R (ResidueField R)) (n + 1) (n + 2)
          (add_comm 1 _)).isIso_map' 1 (by decide)
            ((AddCommGrpCat.of _).isZero_of_subsingleton.eq_zero_of_src _)
              ((AddCommGrpCat.of _).isZero_of_subsingleton.eq_zero_of_tgt _)
      exact (asIso (AddCommGrpCat.ofHom (hS.extClass.precomp
        (ModuleCat.of R (ResidueField R)) (add_comm 1 _)))).addCommGroupIsoToAddEquiv.subsingleton_congr
    exact ih S.X₁ (hiff.mpr h)

/-- Over a Noetherian local ring, a finite module `M` has `pd M < n + 1` if and only if
`Ext^(n+1)(M, k)` is zero ([Mat89, Lemma 19.1]). -/
theorem hasProjectiveDimensionLT_succ_iff (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    HasProjectiveDimensionLT M (n + 1) ↔
      Subsingleton (Ext M (ModuleCat.of R (ResidueField R)) (n + 1)) :=
  ⟨fun _ => HasProjectiveDimensionLT.subsingleton M (n + 1) (n + 1) le_rfl _,
    hasProjectiveDimensionLT_of_subsingleton_ext n M⟩

/-- Over a Noetherian local ring, a finite module `M` has `pd M ≤ n` if and only if
`Ext^(n+1)(M, k)` is zero. -/
theorem projectiveDimension_le_iff_subsingleton_ext (M : ModuleCat.{u} R) [Module.Finite R M]
    (n : ℕ) : projectiveDimension M ≤ n ↔
      Subsingleton (Ext M (ModuleCat.of R (ResidueField R)) (n + 1)) := by
  rw [projectiveDimension_le_iff, HasProjectiveDimensionLE, hasProjectiveDimensionLT_succ_iff]

end Singularity.Algebra
