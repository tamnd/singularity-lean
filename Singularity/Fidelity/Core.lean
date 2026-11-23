/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.Main
import Singularity.Statements.Core
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.FiniteType

/-!
# Fidelity of the core problem P1

The core problem `PurelyInseparableHypersurfaceResolution p n` must be a special case of `ResolutionInDim p n`. Else a proof of P1 tells us nothing about the main problem. This file proves that it is a special case, for `p ≠ 0`.

The steps are these.

1. The equation `z ^ p + g` is not zero, because its coefficient at `z ^ p` is 1.
2. Thus the equation is a nonzerodivisor of the polynomial ring in `n + 1` variables, and the quotient has dimension at most `n`.
3. The hypersurface is affine and of finite type over `k`, so it is a variety when it is reduced.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial

universe u

namespace Singularity

variable {k : Type u} [Field k] {p n : ℕ}

/-- The equation `z ^ p + g` of P1 is not zero when `p ≠ 0`. -/
lemma p1_equation_ne_zero (hp : p ≠ 0) (g : MvPolynomial (Fin n) k) :
    (X none : MvPolynomial (Option (Fin n)) k) ^ p + rename some g ≠ 0 := by
  classical
  intro h
  have h0 : (rename some g).coeff (Finsupp.single none p) = 0 := by
    apply coeff_rename_eq_zero
    intro u hu
    exfalso
    have h2 := congrArg (fun d => d none) hu
    simp only [Finsupp.single_eq_same] at h2
    rw [Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨y, hy⟩; exact Option.some_ne_none y hy)]
      at h2
    exact hp h2.symm
  have h1 := congrArg (fun q : MvPolynomial (Option (Fin n)) k => q.coeff (Finsupp.single none p)) h
  simp [coeff_X_pow, h0] at h1

/-- If `d + 1 ≤ m + 1` in `WithBot ℕ∞`, then `d ≤ m`. -/
lemma le_of_add_one_le_add_one {d : WithBot ℕ∞} {m : ℕ} (h : d + 1 ≤ (m : WithBot ℕ∞) + 1) :
    d ≤ m := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    have h' : e + 1 ≤ (m : ℕ∞) + 1 := by exact_mod_cast h
    have he : e ≤ m := by
      induction e using ENat.recTopCoe with
      | top => simp at h'
      | coe a =>
        have : a + 1 ≤ m + 1 := by exact_mod_cast h'
        exact_mod_cast Nat.le_of_succ_le_succ this
    exact_mod_cast he

/-- The ring of P1 has dimension at most `n` when `p ≠ 0`. -/
lemma ringKrullDim_p1Ring_le (hp : p ≠ 0) (g : MvPolynomial (Fin n) k) :
    ringKrullDim (P1Ring k p n g) ≤ n := by
  have hr : ((X none : MvPolynomial (Option (Fin n)) k) ^ p + rename some g) ∈
      nonZeroDivisors (MvPolynomial (Option (Fin n)) k) :=
    mem_nonZeroDivisors_of_ne_zero (p1_equation_ne_zero hp g)
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin, zero_add, Nat.cast_add,
    Nat.cast_one] at h1
  exact le_of_add_one_le_add_one h1

/-- The hypersurface of P1 has dimension at most `n` when `p ≠ 0`. -/
lemma topologicalKrullDim_p1Hypersurface_le (hp : p ≠ 0) (g : MvPolynomial (Fin n) k) :
    topologicalKrullDim (P1Hypersurface k p n g) ≤ n := by
  change topologicalKrullDim (PrimeSpectrum (P1Ring k p n g)) ≤ n
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_p1Ring_le hp g

/-- The structure morphism of the hypersurface of P1. -/
noncomputable abbrev p1Structure (k : Type u) [Field k] (p n : ℕ) (g : MvPolynomial (Fin n) k) :
    P1Hypersurface k p n g ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (P1Ring k p n g)))

/-- A reduced hypersurface of P1 is a variety. -/
lemma isVariety_p1Hypersurface (g : MvPolynomial (Fin n) k) (hred : IsReduced (P1Hypersurface k p n g)) :
    IsVariety (P1Hypersurface k p n g) (p1Structure k p n g) where
  reduced := hred
  finiteType := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  quasiCompact := inferInstance
  separated := inferInstance

/-- P1 is a special case of the main statement: if each variety of dimension at most `n` over a field of characteristic `p ≠ 0` has a resolution, then so does each reduced hypersurface `z ^ p + g(x_1, ..., x_n) = 0`. -/
theorem purelyInseparableHypersurfaceResolution_of_resolutionInDim (hp : p ≠ 0)
    (h : ResolutionInDim.{u} p n) : PurelyInseparableHypersurfaceResolution.{u} p n := by
  intro k _ _ g hred
  haveI := isVariety_p1Hypersurface g hred
  exact h k (P1Hypersurface k p n g) (p1Structure k p n g)
    (topologicalKrullDim_p1Hypersurface_le hp g)

/-- The first open case implies P1 in dimension 4. -/
theorem purelyInseparableHypersurfaceResolution_four (h : ResolutionDimFourCharP.{u}) (p : ℕ)
    (hp : p.Prime) : PurelyInseparableHypersurfaceResolution.{u} p 4 :=
  purelyInseparableHypersurfaceResolution_of_resolutionInDim hp.ne_zero (h p hp)

end Singularity
