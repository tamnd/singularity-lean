/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.AdjoinRootRegular
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.SetTheory.Cardinal.ENat

/-!
# The dimension of an affine domain is its transcendence degree

This file proves the affine case of map node SG0000002Y: for a field `k` and a finitely
generated `k`-algebra `A` that is a domain, the Krull dimension of `A` equals the
transcendence degree of `A` over `k`.

The proof uses Noether normalization: there is an injective integral `k`-algebra map
`k[X_1, ..., X_s] → A`. An integral extension with injective structure map has the same Krull
dimension as the base (`Singularity.Algebra.ringKrullDim_eq_of_isIntegral`). The Krull dimension of
`k[X_1, ..., X_s]` is `s`. The transcendence degree of `A` is `s` by additivity of the
transcendence degree in towers, since `A` is algebraic over `k[X_1, ..., X_s]`.

## Main results

* `Singularity.exists_ringKrullDim_eq_and_trdeg_eq`: for a finitely generated domain `A` over a
  field `k` there is a natural number `n` with `dim A = n` and `trdeg_k A = n`.
* `Singularity.ringKrullDim_eq_toENat_trdeg`: for such `A`, `dim A` is the transcendence degree
  of `A` over `k`, seen in `WithBot ℕ∞`.
-/

namespace Singularity

universe u v

open Cardinal

section Affine

variable (k : Type u) (A : Type v) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- Let `A` be a finitely generated domain over a field `k`. Then there is a natural number
`n` such that the Krull dimension of `A` is `n` and the transcendence degree of `A` over `k`
is `n`. -/
theorem exists_ringKrullDim_eq_and_trdeg_eq :
    ∃ n : ℕ, ringKrullDim A = n ∧ Algebra.trdeg k A = n := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  let : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) A :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (g.commutes x).symm
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
  have : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine ⟨s, ?_, ?_⟩
  · rw [Singularity.Algebra.ringKrullDim_eq_of_isIntegral (R := MvPolynomial (Fin s) k) (B := A),
      MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
  · have h := lift_trdeg_add_eq k (MvPolynomial (Fin s) k) A
    rw [trdeg_eq_zero (R := MvPolynomial (Fin s) k) (A := A), MvPolynomial.trdeg_of_isDomain] at h
    simpa using h.symm

/-- The Krull dimension of a finitely generated domain `A` over a field `k` equals the
transcendence degree of `A` over `k`, seen in `WithBot ℕ∞`. -/
theorem ringKrullDim_eq_toENat_trdeg :
    ringKrullDim A = ((Algebra.trdeg k A).toENat : WithBot ℕ∞) := by
  obtain ⟨n, h1, h2⟩ := exists_ringKrullDim_eq_and_trdeg_eq k A
  rw [h1, h2, Cardinal.toENat_nat]
  all_goals norm_cast

end Affine

end Singularity
