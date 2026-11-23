/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.FieldTheory.Perfect

/-!
# Finiteness of the normalization, the separable case

Let `A` be a domain that is a finitely generated algebra over a field `k`. E. Noether proved that the integral closure of `A` in its field of fractions is a finite `A`-module. This file proves the theorem when the field of fractions of `A` is separable over the field of fractions of a Noether normalization of `A`. In particular it proves the theorem in characteristic 0.

The proof has three steps.

1. Noether normalization gives a polynomial ring `P = k[X₁, ..., Xₛ]` and a finite injective map `P → A` (`exists_finite_inj_algHom_of_fg` in Mathlib).
2. The ring `P` is Noetherian and integrally closed, because it is a unique factorization domain. If `Frac A` is separable over `Frac P`, then the integral closure of `P` in `Frac A` is a finite `P`-module (`IsIntegralClosure.finite` in Mathlib, by the trace form).
3. An element of `Frac A` that is integral over `A` is integral over `P`, because `A` is integral over `P`. Thus the integral closure of `A` is a `P`-submodule of a Noetherian `P`-module, so it is finite over `P`, and so it is finite over `A`.

The general case in characteristic `p` needs a purely inseparable extension of `Frac P`. It is in `Singularity/Algebra/NormalizationCharP.lean`, which uses `finite_integralClosure_of_finite_of_finite` from this file.
-/

open Module
open scoped nonZeroDivisors

universe u

namespace Singularity.Algebra

attribute [local instance] FractionRing.liftAlgebra

/-- Let `P → A` be a finite injective map of domains, with `P` Noetherian. If the integral closure of `P` in `Frac A` is a finite `P`-module, then the integral closure of `A` in `Frac A` is a finite `A`-module. -/
theorem finite_integralClosure_of_finite_of_finite (P A : Type*) [CommRing P] [IsDomain P]
    [IsNoetherianRing P] [CommRing A] [IsDomain A] [Algebra P A] [IsTorsionFree P A]
    [Module.Finite P A] (hC : Module.Finite P (integralClosure P (FractionRing A))) :
    Module.Finite A (integralClosure A (FractionRing A)) := by
  have hN : IsNoetherian P (integralClosure P (FractionRing A)) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  have hN' : IsNoetherian P (Subalgebra.toSubmodule
      ((integralClosure P (FractionRing A)).restrictScalars P)) := hN
  have hle : (Subalgebra.toSubmodule (integralClosure A (FractionRing A))).restrictScalars P ≤
      Subalgebra.toSubmodule ((integralClosure P (FractionRing A)).restrictScalars P) :=
    fun x hx => isIntegral_trans (R := P) x hx
  have hfg : ((Subalgebra.toSubmodule (integralClosure A (FractionRing A))).restrictScalars P).FG :=
    Module.Finite.iff_fg.mp (isNoetherian_of_le hle).finite
  exact Module.Finite.iff_fg.mpr (Submodule.FG.of_restrictScalars P hfg)

/-- Let `P → A` be a finite injective map of domains, with `P` Noetherian and integrally closed. If `Frac A` is separable over `Frac P`, then the integral closure of `A` in `Frac A` is a finite `A`-module. -/
theorem finite_integralClosure_of_finite (P A : Type*) [CommRing P] [IsDomain P]
    [IsIntegrallyClosed P] [IsNoetherianRing P] [CommRing A] [IsDomain A] [Algebra P A]
    [IsTorsionFree P A] [Module.Finite P A]
    [Algebra.IsSeparable (FractionRing P) (FractionRing A)] :
    Module.Finite A (integralClosure A (FractionRing A)) :=
  finite_integralClosure_of_finite_of_finite P A
    (IsIntegralClosure.finite P (FractionRing P) (FractionRing A) (integralClosure P (FractionRing A)))

/-- Let `A` be a domain that is a finitely generated algebra over a field `k` of characteristic 0. Then the integral closure of `A` in `Frac A` is a finite `A`-module. -/
theorem finite_integralClosure_of_charZero (k A : Type u) [Field k] [CharZero k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    Module.Finite A (integralClosure A (FractionRing A)) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have : Module.Finite (MvPolynomial (Fin s) k) A := hfin
  have : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hinj
  have : IsTorsionFree (MvPolynomial (Fin s) k) A :=
    Module.IsTorsionFree.trans_faithfulSMul (R := MvPolynomial (Fin s) k) (A := A) (M := A)
  have : CharZero (FractionRing (MvPolynomial (Fin s) k)) :=
    charZero_of_injective_algebraMap (algebraMap k (FractionRing (MvPolynomial (Fin s) k))).injective
  have : Algebra.IsSeparable (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact finite_integralClosure_of_finite (MvPolynomial (Fin s) k) A

end Singularity.Algebra
