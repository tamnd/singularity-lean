/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.RegularLocalization
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.LocalRing.Module

/-!
# Flat descent of regularity

Let `A → B` be a flat local homomorphism of Noetherian local rings. This file proves that if `B`
is regular, then `A` is regular ([Mat89, Theorem 23.7 (i)]).

## Main results

* `hasProjectiveDimensionLT_of_baseChange`: let `M` be a finite `A`-module. If `B ⊗ M` has
  projective dimension less than `n + 1` over `B`, then `M` has projective dimension less than
  `n + 1` over `A`.
* `isRegularLocalRing_of_flat`: flat descent of regularity.

## The proof

The map `A → B` is faithfully flat, because it is flat and local. The first result is an
induction on `n`. If `n = 0`, then `B ⊗ M` is projective, so flat over `B`. By faithfully flat
descent, `M` is flat over `A`, so free, because `M` is finite and `A` is local. In the other
case, take a presentation `0 → K → F → M → 0` with `F` finite and free. Because `B` is flat over
`A`, the sequence `0 → B ⊗ K → B ⊗ F → B ⊗ M → 0` is exact. Thus `pd (B ⊗ K) < n` over `B`,
the induction hypothesis gives `pd K < n` over `A`, and so `pd M < n + 1` over `A`.

For the second result, let `k` be the residue field of `A`. The module `B ⊗ k` is finite over
the regular ring `B`, so it has finite projective dimension by the theorem of Serre. By the first
result, `k` has finite projective dimension over `A`, and by the converse of the theorem of
Serre, `A` is regular.

## References

* [Mat89] H. Matsumura, *Commutative Ring Theory*, Cambridge University Press, 1989.
-/

universe u

open CategoryTheory Abelian IsLocalRing Module TensorProduct

namespace Singularity.Algebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Let `A → B` be a flat local homomorphism of local rings, with `A` Noetherian. Let `M` be a
finite `A`-module. If `B ⊗ M` has projective dimension less than `n + 1` over `B`, then `M` has
projective dimension less than `n + 1` over `A`. -/
theorem hasProjectiveDimensionLT_of_baseChange [IsLocalRing A] [IsNoetherianRing A]
    [IsLocalRing B] [Module.Flat A B] [IsLocalHom (algebraMap A B)] (n : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M],
      HasProjectiveDimensionLT (ModuleCat.of B (B ⊗[A] M)) (n + 1) →
        HasProjectiveDimensionLT (ModuleCat.of A M) (n + 1) := by
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  induction n with
  | zero =>
    intro M _ _ _ h
    have : Module.Projective B (B ⊗[A] M) :=
      (IsProjective.iff_projective (R := B) (ModuleCat.of B (B ⊗[A] M))).mpr
        (projective_iff_hasProjectiveDimensionLT_one.mpr h)
    have : Module.Flat A M := Module.Flat.of_flat_tensorProduct A M B
    have : Module.Free A M := Module.free_of_flat_of_isLocalRing
    rw [zero_add, ← projective_iff_hasProjectiveDimensionLT_one]
    exact (IsProjective.iff_projective (R := A) _).mp inferInstance
  | succ n ih =>
    intro M _ _ _ h
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation A M
    let S := f.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hf
    refine (hS.hasProjectiveDimensionLT_X₃_iff n
      (inferInstanceAs (Projective (ModuleCat.of A P)))).mpr ?_
    have hzero : f ∘ₗ (LinearMap.ker f).subtype = 0 := by ext z; exact z.2
    let T : ShortComplex (ModuleCat.{u} B) :=
      { X₁ := ModuleCat.of B (B ⊗[A] LinearMap.ker f)
        X₂ := ModuleCat.of B (B ⊗[A] P)
        X₃ := ModuleCat.of B (B ⊗[A] M)
        f := ModuleCat.ofHom ((LinearMap.ker f).subtype.baseChange B)
        g := ModuleCat.ofHom (f.baseChange B)
        zero := by
          rw [← ModuleCat.ofHom_comp, ← LinearMap.baseChange_comp, hzero,
            LinearMap.baseChange_zero]
          rfl }
    have hT : T.ShortExact :=
      { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (by
          change Function.Exact ((LinearMap.ker f).subtype.baseChange B) (f.baseChange B)
          rw [LinearMap.baseChange_eq_lTensor, LinearMap.baseChange_eq_lTensor]
          exact lTensor_exact (f := (LinearMap.ker f).subtype) (g := f) B f.exact_subtype_ker_map hf)
        mono_f := (ModuleCat.mono_iff_injective _).mpr (by
          change Function.Injective ((LinearMap.ker f).subtype.baseChange B)
          rw [LinearMap.baseChange_eq_lTensor]
          exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
        epi_g := (ModuleCat.epi_iff_surjective _).mpr (by
          change Function.Surjective (f.baseChange B)
          rw [LinearMap.baseChange_eq_lTensor]
          exact LinearMap.lTensor_surjective B hf) }
    have hP : Projective T.X₂ :=
      (IsProjective.iff_projective (R := B) _).mp inferInstance
    exact ih (LinearMap.ker f) ((hT.hasProjectiveDimensionLT_X₃_iff n hP).mp h)

/-- Flat descent of regularity ([Mat89, Theorem 23.7 (i)]). Let `A → B` be a flat local
homomorphism of local rings, where `A` is Noetherian. If `B` is a regular local ring, then `A` is
a regular local ring. -/
theorem isRegularLocalRing_of_flat [IsLocalRing A] [IsNoetherianRing A] [IsRegularLocalRing B]
    [Module.Flat A B] [IsLocalHom (algebraMap A B)] : IsRegularLocalRing A := by
  obtain ⟨d, hd⟩ := exists_ringKrullDim_eq_natCast B
  have h := hasProjectiveDimensionLT_of_isRegularLocalRing d B hd (B ⊗[A] ResidueField A)
  exact isRegularLocalRing_of_hasProjectiveDimensionLT A (d + 1)
    (hasProjectiveDimensionLT_of_baseChange d (ResidueField A) h)

end Singularity.Algebra
