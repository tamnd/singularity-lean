/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Generically étale finite algebras

This file proves Volume 8, Lemma 1.1.5 of the handbook in part, in its affine algebraic form.
Let `A` be a domain with field of fractions `K`, and let `B` be a domain that is an `A`-algebra of
finite presentation, with field of fractions `L`. Assume that `L` is a finite extension of `K`.

## Main results

* `Singularity.discr_ne_zero_of_isSeparable`: the discriminant of a `K`-basis of a finite
  separable extension `L/K` is not zero. This is the step `δ ≠ 0` of the proof.
* `Singularity.exists_free_localizedModule_away_of_isDomain`: generic freeness. A finitely
  presented module `M` over a domain `A` becomes free over `A_a` for some `a ≠ 0`, of rank the
  dimension of `M ⊗ K` over `K`. This is the step "after we invert one nonzero element of `A`,
  the module `B` is free" of the proof.
* `Singularity.isEtaleAt_bot_iff_isSeparable`: `B` is étale over `A` at the generic point of
  `Spec B` if and only if `L/K` is separable.
* `Singularity.exists_etale_away_iff_isSeparable`: there is `f ≠ 0` in `B` such that `B_f` is
  étale over `A` if and only if `L/K` is separable.
* `Singularity.exists_etale_away_algebraMap_iff_isSeparable`: if moreover `B` is a finite
  `A`-module, then there is `a ≠ 0` in `A` such that `B_a` is étale over `A` if and only if `L/K`
  is separable. This is Lemma 1.1.5 over the affine open `Spec A` of `X`.

## What is not proved

The handbook proves the converse with the discriminant: `B_δ` is finite free over `A_δ` with a
unit discriminant, so it is étale. Mathlib has no lemma that a finite free algebra with a unit
discriminant is étale, and this file does not prove it. The proof here uses instead that the
étale locus of a finitely presented algebra is open (`Algebra.isOpen_etaleLocus`). The statements
say that `B_a` is étale over `A`. Since `A → A_a` is a localization, this is the same as étale
over `A_a`, but the file does not state that form. The passage from schemes to rings (the choice
of the affine open sets `Spec A ⊆ X` and `Spec B`) is not in this file.
-/

namespace Singularity

open Algebra

/-- The step `δ ≠ 0` in the proof of Volume 8, Lemma 1.1.5 of the handbook: the discriminant
`det(Tr_{L/K}(e_i e_j))` of a basis `e` of a finite separable extension `L/K` is not zero. -/
theorem discr_ne_zero_of_isSeparable {ι K L : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (e : Module.Basis ι K L) : Algebra.discr K e ≠ 0 :=
  Algebra.discr_not_zero_of_basis K e

/-- Generic freeness, the second step in the proof of Volume 8, Lemma 1.1.5 of the handbook.
Let `M` be a finitely presented module over a domain `A`. Then there is `a ≠ 0` in `A` such
that `M_a` is a free `A_a`-module, of rank the dimension of `M ⊗ K` over the field of fractions
`K` of `A`. Over a Noetherian domain every finite module is finitely presented. -/
theorem exists_free_localizedModule_away_of_isDomain {A M : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] :
    ∃ a : A, a ≠ 0 ∧
      Module.Free (Localization (.powers a)) (LocalizedModule.Away a M) ∧
      Module.finrank (Localization (.powers a)) (LocalizedModule.Away a M) =
        Module.finrank (FractionRing A) (LocalizedModule (nonZeroDivisors A) M) := by
  obtain ⟨a, ha, hfree, hrank⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors A) (LocalizedModule.mkLinearMap (nonZeroDivisors A) M) (FractionRing A)
  exact ⟨a, nonZeroDivisors.ne_zero ha, hfree, hrank⟩

section Etale

variable {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L] [IsDomain B]
  [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
  [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L]

include K in
/-- The generic point of `Spec B` is in the étale locus of `B` over `A` if and only if `L/K` is
separable. Here `A` and `B` are domains with fields of fractions `K` and `L`, and `L/K` is
finite. -/
theorem isEtaleAt_bot_iff_isSeparable [IsDomain A] [FiniteDimensional K L] :
    IsEtaleAt A (⊥ : Ideal B) ↔ Algebra.IsSeparable K L := by
  have : IsFractionRing B (Localization.AtPrime (⊥ : Ideal B)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal B).primeCompl)
  let e : Localization.AtPrime (⊥ : Ideal B) ≃ₐ[B] L :=
    IsLocalization.algEquiv (nonZeroDivisors B) _ L
  have hK : FormallyEtale A K := FormallyEtale.of_isLocalization (nonZeroDivisors A)
  rw [IsEtaleAt, FormallyEtale.iff_of_equiv (e.restrictScalars A),
    FormallyEtale.iff_restrictScalars (R := A) (A := K) (B := L), FormallyEtale.iff_isSeparable]

include K in
/-- Volume 8, Lemma 1.1.5 of the handbook, local form on `X'`. Let `A` and `B` be domains with
fields of fractions `K` and `L`, let `B` be a finitely presented `A`-algebra, and let `L/K` be
finite. Then there is `f ≠ 0` in `B` such that `B_f` is étale over `A` if and only if `L/K` is
separable. -/
theorem exists_etale_away_iff_isSeparable [IsDomain A] [FiniteDimensional K L]
    [Algebra.FinitePresentation A B] :
    (∃ f : B, f ≠ 0 ∧ Algebra.Etale A (Localization.Away f)) ↔ Algebra.IsSeparable K L := by
  rw [← isEtaleAt_bot_iff_isSeparable (A := A) (B := B) (K := K) (L := L)]
  constructor
  · rintro ⟨f, hf, hfe⟩
    have h := basicOpen_subset_etaleLocus_iff (R := A) (f := f) |>.mpr hfe.formallyEtale
    exact h (show (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ∈ PrimeSpectrum.basicOpen f
      from hf)
  · intro h
    obtain ⟨f, hf, hfe⟩ := exists_etale_of_isEtaleAt (R := A) (⊥ : Ideal B)
    exact ⟨f, hf, hfe⟩

include K in
/-- Volume 8, Lemma 1.1.5 of the handbook over an affine open `Spec A` of `X`. Let `A` and `B`
be domains with fields of fractions `K` and `L`, and let `B` be a finitely presented `A`-algebra
that is a finite `A`-module, with `L/K` finite. Then there is `a ≠ 0` in `A` such that `B_a` is
étale over `A` if and only if `L/K` is separable. -/
theorem exists_etale_away_algebraMap_iff_isSeparable [IsDomain A] [FiniteDimensional K L]
    [Algebra.FinitePresentation A B] [Module.Finite A B] :
    (∃ a : A, a ≠ 0 ∧ Algebra.Etale A (Localization.Away (algebraMap A B a))) ↔
      Algebra.IsSeparable K L := by
  have hinj : Function.Injective (algebraMap A B) := by
    have h : Function.Injective (algebraMap A L) := by
      rw [IsScalarTower.algebraMap_eq A K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
    rw [IsScalarTower.algebraMap_eq A B L, RingHom.coe_comp] at h
    exact h.of_comp
  rw [← exists_etale_away_iff_isSeparable (A := A) (B := B) (K := K) (L := L)]
  constructor
  · rintro ⟨a, ha, h⟩
    exact ⟨algebraMap A B a, (map_ne_zero_iff _ hinj).mpr ha, h⟩
  · rintro ⟨f, hf, hfe⟩
    have hI := Ideal.under_ne_bot_of_integral_mem (R := A) hf (Ideal.mem_span_singleton_self f)
      (Algebra.IsIntegral.isIntegral f)
    obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp haI)
    have hU := basicOpen_subset_etaleLocus_iff (R := A) (f := f) |>.mpr hfe.formallyEtale
    have hV : ↑(PrimeSpectrum.basicOpen (algebraMap A B a)) ⊆ etaleLocus A B := by
      refine subset_trans ?_ hU
      rw [← hg, PrimeSpectrum.basicOpen_mul]
      exact Set.inter_subset_right
    refine ⟨a, ha, basicOpen_subset_etaleLocus_iff.mp hV, ?_⟩
    exact .of_isLocalizationAway (algebraMap A B a)

end Etale

end Singularity
