/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Alteration.Trace

/-!
# The trace splitting of a finite alteration

This file proves the affine case of Volume 8, Proposition 1.3.2 of the handbook. Let `A` be a normal domain with field of fractions `K`, let `L/K` be a finite extension of degree `d`, and let `B ⊆ L` be an `A`-subalgebra whose elements are integral over `A`. If `d` is a unit of `A`, then `b ↦ d⁻¹ Tr_{L/K}(b)` is an `A`-linear map `B → A` that is a left inverse of `A → B`.

The proof is the proof of the handbook. By Lemma 1.3.1 (`Singularity.exists_algebraMap_eq_trace`), the trace sends `B` into `A`, and `Tr_{L/K}(a) = d a` for `a ∈ A`.

The handbook asks that `A` is Noetherian, and it states the result for a finite alteration `X' → X` with `X` normal. Here only the ring of an affine open subset of `X` and the ring of its inverse image are covered. The gluing of these maps is not proved. The ring `B` of the handbook is a domain finite over `A` with fraction field `L`, so it is an `A`-subalgebra of `L` whose elements are integral over `A`.

## Main results

* `Singularity.traceToBase`: the `A`-linear map `B → A` given by `Tr_{L/K}`.
* `Singularity.traceToBase_algebraMap`: `Tr_{L/K}(a) = d a` for `a ∈ A`.
* `Singularity.exists_leftInverse_algebraMap_of_isUnit_finrank`: the affine case of Proposition 1.3.2.
-/

open Module

namespace Singularity

variable {A K L : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [FiniteDimensional K L]

theorem exists_algebraMap_eq_trace_of_le {B : Subalgebra A L} (hB : B ≤ integralClosure A L)
    (b : B) : ∃ a : A, algebraMap A K a = Algebra.trace K L b :=
  exists_algebraMap_eq_trace (hB b.2)

/-- The trace `Tr_{L/K}` as a function from `B` to `A`. -/
noncomputable def traceToBaseFun {B : Subalgebra A L} (hB : B ≤ integralClosure A L) (b : B) : A :=
  (exists_algebraMap_eq_trace_of_le (K := K) hB b).choose

theorem algebraMap_traceToBaseFun {B : Subalgebra A L} (hB : B ≤ integralClosure A L) (b : B) :
    algebraMap A K (traceToBaseFun (K := K) hB b) = Algebra.trace K L b :=
  (exists_algebraMap_eq_trace_of_le (K := K) hB b).choose_spec

/-- The trace `Tr_{L/K}` as an `A`-linear map from `B` to `A`, for an `A`-subalgebra `B` of `L` whose elements are integral over `A`. -/
noncomputable def traceToBase {B : Subalgebra A L} (hB : B ≤ integralClosure A L) : B →ₗ[A] A where
  toFun := traceToBaseFun (K := K) hB
  map_add' x y := by
    apply IsFractionRing.injective A K
    rw [map_add, algebraMap_traceToBaseFun, algebraMap_traceToBaseFun, algebraMap_traceToBaseFun]
    change Algebra.trace K L ((x : L) + (y : L)) = _
    rw [map_add]
  map_smul' c x := by
    apply IsFractionRing.injective A K
    rw [RingHom.id_apply, smul_eq_mul, map_mul, algebraMap_traceToBaseFun,
      algebraMap_traceToBaseFun]
    change Algebra.trace K L (c • (x : L)) = _
    rw [← algebraMap_smul K c (x : L), map_smul, smul_eq_mul]

theorem algebraMap_traceToBase {B : Subalgebra A L} (hB : B ≤ integralClosure A L) (b : B) :
    algebraMap A K (traceToBase (K := K) hB b) = Algebra.trace K L b :=
  algebraMap_traceToBaseFun hB b

/-- `Tr_{L/K}(a) = [L : K] a` for `a ∈ A`. -/
theorem traceToBase_algebraMap {B : Subalgebra A L} (hB : B ≤ integralClosure A L) (a : A) :
    traceToBase (K := K) hB (algebraMap A B a) = finrank K L * a := by
  apply IsFractionRing.injective A K
  rw [algebraMap_traceToBase, map_mul, map_natCast]
  have h : ((algebraMap A B a : B) : L) = algebraMap K L (algebraMap A K a) := by
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  rw [h, Algebra.trace_algebraMap, nsmul_eq_mul]

/-- Volume 8, Proposition 1.3.2 of the handbook, the affine case. Let `A` be a normal domain with field of fractions `K`, let `L/K` be finite of degree `d`, and let `B ⊆ L` be an `A`-subalgebra whose elements are integral over `A`. If `d` is a unit of `A`, then `A → B` has an `A`-linear left inverse, namely `d⁻¹ Tr_{L/K}`. -/
theorem exists_leftInverse_algebraMap_of_isUnit_finrank {B : Subalgebra A L}
    (hB : B ≤ integralClosure A L) (hd : IsUnit (finrank K L : A)) :
    ∃ ρ : B →ₗ[A] A, ∀ a : A, ρ (algebraMap A B a) = a := by
  refine ⟨(↑hd.unit⁻¹ : A) • traceToBase (K := K) hB, fun a => ?_⟩
  rw [LinearMap.smul_apply, traceToBase_algebraMap, smul_eq_mul, ← mul_assoc, hd.val_inv_mul,
    one_mul]

end Singularity
