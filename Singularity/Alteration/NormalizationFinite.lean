/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Alteration.GenericEtale
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.FieldTheory.Perfect

/-!
# The normalization of a domain in a finite extension of its fraction field

This file proves Volume 8, Lemma 1.1.7 of the handbook in part, in its affine algebraic form.
Let `A` be a domain with field of fractions `K`, let `L` be a finite extension of `K`, and let
`B = integralClosure A L` be the integral closure of `A` in `L`.

## Main results

* `Singularity.isIntegrallyClosed_and_isFractionRing_integralClosure`: `B` is an integrally
  closed domain with field of fractions `L`. So the function field of `X_L` is `L`, and the
  degree of `X_L → X` is `[L : K]`.
* `Singularity.moduleFinite_integralClosure_of_finite_of_isSeparable`: let `P → A` be a finite
  injective map from a Noetherian integrally closed domain `P` with field of fractions `F`. If
  `L` is separable over `F`, then `B` is a finite `A`-module. This is the proof of the handbook,
  with `P` a Noether normalization of `A`.
* `Singularity.moduleFinite_integralClosure_of_charZero`: if `A` is a finitely generated algebra
  over a field `k` of characteristic zero, then `B` is a finite `A`-module.
* `Singularity.exists_etale_away_integralClosure_iff_isSeparable`: if `A` is Noetherian and `B`
  is a finite `A`-module, then there is `a ≠ 0` in `A` such that `B_a` is étale over `A` if and
  only if `L/K` is separable.

## What is not proved

The finiteness of `B` over `A` is proved only when `L` is separable over the field of fractions
of some Noetherian integrally closed domain `P` over which `A` is finite, for instance in
characteristic zero. The theorem of E. Noether in characteristic `p` (finiteness of the integral
closure of a finitely generated domain over a field in an inseparable extension) is not in
Mathlib and is not proved here. The gluing of the rings `B` to the scheme `X_L`, and the
properness and surjectivity of `X_L → X`, are not in this file.
-/

namespace Singularity

open Algebra

section Closure

variable {A K L : Type*} [CommRing A] [IsDomain A] [Field K] [Field L] [Algebra A K]
  [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]

variable (K) in
include K in
/-- Part of Volume 8, Lemma 1.1.7 of the handbook. The integral closure `B` of a domain `A` in a
finite extension `L` of the field of fractions `K` of `A` is an integrally closed domain with
field of fractions `L`. -/
theorem isIntegrallyClosed_and_isFractionRing_integralClosure :
    IsDomain (integralClosure A L) ∧ IsIntegrallyClosed (integralClosure A L) ∧
      IsFractionRing (integralClosure A L) L :=
  ⟨inferInstance, integralClosure.isIntegrallyClosedOfFiniteExtension K,
    integralClosure.isFractionRing_of_finite_extension K L⟩

end Closure

/-- Volume 8, Lemma 1.1.7 of the handbook, the finiteness step, separable form. Let `P → A` be
a finite map of rings, where `P` is a Noetherian integrally closed domain with field of
fractions `F`. Let `L` be a field over `A` and `F`, finite and separable over `F`. Then the
integral closure of `A` in `L` is a finite `A`-module. -/
theorem moduleFinite_integralClosure_of_finite_of_isSeparable {P A F L : Type*} [CommRing P]
    [IsDomain P] [IsIntegrallyClosed P] [IsNoetherianRing P] [CommRing A] [Field F] [Field L]
    [Algebra P A] [Algebra P F] [IsFractionRing P F] [Algebra A L] [Algebra P L] [Algebra F L]
    [IsScalarTower P A L] [IsScalarTower P F L] [Module.Finite P A] [FiniteDimensional F L]
    [Algebra.IsSeparable F L] : Module.Finite A (integralClosure A L) := by
  have : IsIntegralClosure (integralClosure A L) P L :=
    { algebraMap_injective := Subtype.val_injective
      isIntegral_iff := fun {x} =>
        ⟨fun hx => ⟨⟨x, hx.tower_top⟩, rfl⟩, by
          rintro ⟨y, rfl⟩
          exact isIntegral_trans (R := P) (A := A) _ y.2⟩ }
  have := IsIntegralClosure.finite P F L (integralClosure A L)
  exact Module.Finite.of_restrictScalars_finite P A _

/-- Volume 8, Lemma 1.1.7 of the handbook, the finiteness step in characteristic zero. Let `A`
be a domain that is a finitely generated algebra over a field `k` of characteristic zero, with
field of fractions `K`, and let `L` be a finite extension of `K`. Then the integral closure of
`A` in `L` is a finite `A`-module. -/
theorem moduleFinite_integralClosure_of_charZero {k A K L : Type*} [Field k] [CharZero k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] : Module.Finite A (integralClosure A L) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin s) k
  let : Algebra P A := g.toRingHom.toAlgebra
  have : Module.Finite P A := hfin
  have hPA : Function.Injective (algebraMap P A) := hinj
  let : Algebra P K := ((algebraMap A K).comp (algebraMap P A)).toAlgebra
  let : Algebra P L := ((algebraMap A L).comp (algebraMap P A)).toAlgebra
  have : IsScalarTower P A K := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower P A L := IsScalarTower.of_algebraMap_eq' rfl
  have hPK : Function.Injective (algebraMap P K) :=
    (IsFractionRing.injective A K).comp hPA
  let F := FractionRing P
  let : Algebra F K := (IsFractionRing.lift hPK).toAlgebra
  have : IsScalarTower P F K := IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap hPK x).symm
  let : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  have : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower P F L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply F K L, ← IsScalarTower.algebraMap_apply P F K,
      IsScalarTower.algebraMap_apply P A K, ← IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply P A L]
  have : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors P)) K := by
    refine (IsLocalization.iff_of_le_of_exists_dvd
      (M := Algebra.algebraMapSubmonoid A (nonZeroDivisors P)) (S := K) (nonZeroDivisors A)
      ?_ ?_).mpr inferInstance
    · rintro _ ⟨p, hp, rfl⟩
      exact mem_nonZeroDivisors_of_ne_zero
        ((map_ne_zero_iff _ hPA).mpr (nonZeroDivisors.ne_zero hp))
    · intro n hn
      have hI := Ideal.under_ne_bot_of_integral_mem (R := P) (nonZeroDivisors.ne_zero hn)
        (Ideal.mem_span_singleton_self n) (Algebra.IsIntegral.isIntegral n)
      obtain ⟨p, hpI, hp⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      exact ⟨algebraMap P A p, ⟨p, mem_nonZeroDivisors_of_ne_zero hp, rfl⟩,
        Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp hpI)⟩
  have : FiniteDimensional F K := .of_isLocalization P A (nonZeroDivisors P)
  have : FiniteDimensional F L := Module.Finite.trans K L
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  have : Algebra.IsSeparable F L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact moduleFinite_integralClosure_of_finite_of_isSeparable (P := P) (F := F)

/-- Volume 8, Lemma 1.1.7 of the handbook, the last claim. Let `A` be a Noetherian domain with
field of fractions `K`, let `L` be a finite extension of `K`, and assume that the integral
closure `B` of `A` in `L` is a finite `A`-module. Then there is `a ≠ 0` in `A` such that `B_a`
is étale over `A` if and only if `L/K` is separable. -/
theorem exists_etale_away_integralClosure_iff_isSeparable {A K L : Type*} [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    [Module.Finite A (integralClosure A L)] :
    (∃ a : A, a ≠ 0 ∧
      Algebra.Etale A (Localization.Away (algebraMap A (integralClosure A L) a))) ↔
      Algebra.IsSeparable K L := by
  have : IsFractionRing (integralClosure A L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  have : Algebra.FinitePresentation A (integralClosure A L) :=
    (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  exact exists_etale_away_algebraMap_iff_isSeparable (K := K) (L := L)

end Singularity
