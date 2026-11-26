/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The trace of an integral element

Let `A` be a normal domain with field of fractions `K`, and let `L` be a finite extension of `K`. This file proves that the trace `Tr_{L/K}(b)` of an element `b` of `L` that is integral over `A` is in `A` (Volume 8, Lemma 1.3.1 of the handbook).

The handbook asks that `A` is Noetherian. The statement here does not need this condition. The proof uses `Algebra.isIntegral_trace` of Mathlib: the trace of an integral element is integral. Mathlib proves it with the sum of the conjugates of `b` in an algebraic closure. Since `A` is integrally closed, an element of `K` that is integral over `A` is in `A`.

## Main results

* `Singularity.exists_algebraMap_eq_trace`: there is `a ∈ A` with `a = Tr_{L/K}(b)` in `K`.
-/

namespace Singularity

/-- Volume 8, Lemma 1.3.1 of the handbook: let `A` be a normal domain with field of fractions `K`, let `L/K` be a finite extension, and let `b ∈ L` be integral over `A`. Then `Tr_{L/K}(b) ∈ A`. The handbook also asks that `A` is Noetherian. -/
theorem exists_algebraMap_eq_trace {A K L : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] {b : L} (hb : IsIntegral A b) :
    ∃ a : A, algebraMap A K a = Algebra.trace K L b :=
  IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace hb)

end Singularity
