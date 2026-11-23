/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.NormalizationCharP
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.FiniteType

/-!
# The normalization of an affine curve

Let `k` be a field and let `A` be a domain that is a finitely generated `k`-algebra of dimension at most 1. This file proves that the normalization `Ã` of `A` is a Dedekind domain. Thus each local ring of `Ã` is regular. This is Corollary 2.3.6 of Volume 1 of the handbook in characteristic 0, and Corollary 2.4.8 in each characteristic. It is the affine part of the resolution of curves.

The proof has three parts.

1. `Ã` is a finite `A`-module (`finite_integralClosure`), and `A` is Noetherian, so `Ã` is Noetherian.
2. `Ã` is integrally closed, because it is the integral closure of `A` in `Frac A`.
3. `Ã` is integral over `A`, so it has dimension at most 1.

The dimension hypothesis is the class `Ring.DimensionLEOne A` of Mathlib: each nonzero prime ideal of `A` is maximal.
-/

universe u

namespace Singularity.Curves

open Singularity.Algebra

/-- Let `A` be a domain that is a finitely generated algebra of dimension at most 1 over a field. Then the normalization of `A` is a Dedekind domain. -/
theorem isDedekindDomain_integralClosure (k A : Type u) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] [Ring.DimensionLEOne A] :
    IsDedekindDomain (integralClosure A (FractionRing A)) := by
  have : Module.Finite A (integralClosure A (FractionRing A)) := finite_integralClosure k A
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : IsNoetherianRing (integralClosure A (FractionRing A)) :=
    IsNoetherianRing.of_finite A (integralClosure A (FractionRing A))
  have : IsIntegrallyClosed (integralClosure A (FractionRing A)) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing A)
  have : IsDedekindRing (integralClosure A (FractionRing A)) :=
    (isDedekindRing_iff _ (FractionRing (integralClosure A (FractionRing A)))).mpr
      ⟨inferInstance, inferInstance,
        fun hx => (isIntegrallyClosed_iff (FractionRing _)).mp inferInstance hx⟩
  infer_instance

/-- Let `A` be a domain that is a finitely generated algebra of dimension at most 1 over a field. Then the normalization of `A` is a regular ring: its localization at each prime ideal is a regular local ring. -/
theorem isRegularRing_integralClosure (k A : Type u) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] [Ring.DimensionLEOne A] :
    IsRegularRing (integralClosure A (FractionRing A)) := by
  have := isDedekindDomain_integralClosure k A
  infer_instance

/-- Let `A` be a domain that is a finitely generated algebra of dimension at most 1 over a field of characteristic 0. Then the normalization of `A` is a Dedekind domain. -/
theorem isDedekindDomain_integralClosure_of_charZero (k A : Type u) [Field k] [CharZero k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [Ring.DimensionLEOne A] :
    IsDedekindDomain (integralClosure A (FractionRing A)) :=
  isDedekindDomain_integralClosure k A

/-- Let `A` be a domain that is a finitely generated algebra of dimension at most 1 over a field of characteristic 0. Then the normalization of `A` is a regular ring: its localization at each prime ideal is a regular local ring. -/
theorem isRegularRing_integralClosure_of_charZero (k A : Type u) [Field k] [CharZero k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [Ring.DimensionLEOne A] :
    IsRegularRing (integralClosure A (FractionRing A)) :=
  isRegularRing_integralClosure k A

end Singularity.Curves
