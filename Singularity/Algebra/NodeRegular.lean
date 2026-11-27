/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Singularity.Algebra.Regular
import Singularity.Algebra.MonomialParameter

/-!
# The node over a regular local ring

This file proves Volume 8, Lemma 2.1.3 of the handbook, with the regularity of `A[[u, v]]` as a hypothesis. Let `(A, 𝔪_A)` be a local ring, let `h ∈ 𝔪_A`, and let `B = A[[u, v]] / (uv - h)`. If `A[[u, v]]` is a regular local ring, then `B` is a regular local ring if and only if `h ∉ 𝔪_A²`.

* `Singularity.Algebra.isRegularLocalRing_quotient_span_singleton_iff`: let `(P, 𝔫)` be a regular local ring and let `f ∈ 𝔫` be nonzero. Then `P / (f)` is regular if and only if `f ∉ 𝔫²`. If `f ∈ 𝔫²`, the maximal ideal of `P / (f)` needs as many generators as `𝔫`, but the dimension goes down by 1.
* `Singularity.Algebra.X_mul_X_sub_C_mem_sq_iff`: in `A[[u, v]]`, the element `uv - h` is in `𝔫²` if and only if `h ∈ 𝔪_A²`. The proof applies the constant coefficient map.
* `Singularity.Algebra.isRegularLocalRing_quotient_X_mul_X_sub_C_iff`: Lemma 2.1.3.
* `Singularity.Algebra.isRegularLocalRing_quotient_X_mul_X_sub_C_monomial_iff`: Corollary 2.1.4 for `h = ε t₁^n₁ ⋯ t_r^n_r`.

The power series are in a type `σ` of variables, and `u` and `v` are `X i` and `X j`. The fact that `A[[u, v]]` is a regular local ring of dimension `dim A + 2` when `A` is regular [Mat89, Theorem 19.5] is not in Lean, so the last two theorems take it as a hypothesis.
-/

open IsLocalRing Ideal

namespace Singularity.Algebra

universe u

section Hypersurface

variable (P : Type u) [CommRing P] [IsRegularLocalRing P]

/-- The quotient map from a local ring to a local quotient is a local homomorphism. -/
theorem isLocalHom_algebraMap_quotient_span_singleton (f : P)
    [IsLocalRing (P ⧸ span {f})] : IsLocalHom (algebraMap P (P ⧸ span {f})) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hm : a ∈ maximalIdeal P := (IsLocalRing.mem_maximalIdeal a).mpr hna
  have : algebraMap P (P ⧸ span {f}) a ∈ maximalIdeal (P ⧸ span {f}) := by
    rw [maximalIdeal_quotient_eq_map]
    exact Ideal.mem_map_of_mem _ hm
  exact (IsLocalRing.mem_maximalIdeal _).mp this ha

/-- Let `P` be a regular local ring and let `f ∈ 𝔫²` be nonzero. Then the maximal ideal of
`P / (f)` needs as many generators as the maximal ideal of `P`. -/
theorem spanFinrank_maximalIdeal_quotient_eq_of_mem_sq {f : P} (hf : f ∈ maximalIdeal P ^ 2)
    [IsLocalRing (P ⧸ span {f})] :
    (maximalIdeal (P ⧸ span {f})).spanFinrank = (maximalIdeal P).spanFinrank := by
  have := isLocalHom_algebraMap_quotient_span_singleton P f
  have key := IsLocalRing.spanFinrank_maximalIdeal_add_finrank_eq_of_surjective
    (R := P) (S := P ⧸ span {f}) Ideal.Quotient.mk_surjective
  have hW : (Submodule.comap (maximalIdeal P).subtype
      (RingHom.ker (algebraMap P (P ⧸ span {f})))).map (toCotangentSpace P) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [Submodule.mem_bot, toCotangentSpace_eq_toCotangent, Ideal.toCotangent_eq_zero]
    have hx' : (x : P) ∈ span {f} := by
      simpa [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] using hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx'
    rw [← ha]
    exact Ideal.mul_mem_left _ a hf
  rw [hW, finrank_bot, add_zero] at key
  exact key

/-- Volume 8, Lemma 2.1.3 of the handbook, the general step. Let `(P, 𝔫)` be a regular local ring
and let `f ∈ 𝔫` be nonzero. Then `P / (f)` is a regular local ring if and only if `f ∉ 𝔫²`. -/
theorem isRegularLocalRing_quotient_span_singleton_iff {f : P} (hf : f ∈ maximalIdeal P)
    (hf0 : f ≠ 0) : IsRegularLocalRing (P ⧸ span {f}) ↔ f ∉ maximalIdeal P ^ 2 := by
  constructor
  · intro hreg hsq
    have := isDomain_of_isRegularLocalRing P
    have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hf0) hf
    have hP : ((maximalIdeal P).spanFinrank : WithBot ℕ∞) = ringKrullDim P :=
      IsRegularLocalRing.spanFinrank_maximalIdeal (R := P)
    have hS : ((maximalIdeal (P ⧸ span {f})).spanFinrank : WithBot ℕ∞) =
        ringKrullDim (P ⧸ span {f}) :=
      IsRegularLocalRing.spanFinrank_maximalIdeal (R := P ⧸ span {f})
    rw [spanFinrank_maximalIdeal_quotient_eq_of_mem_sq P hsq] at hS
    rw [← hS, ← hP] at hdim
    have h1 : (maximalIdeal P).spanFinrank + 1 = (maximalIdeal P).spanFinrank := by
      exact_mod_cast hdim
    omega
  · intro hn
    exact (quotient_span_singleton hf hn).1

end Hypersurface

section PowerSeries

open MvPowerSeries

variable {σ A : Type u} [CommRing A] [IsLocalRing A]

theorem mem_maximalIdeal_mvPowerSeries_iff {φ : MvPowerSeries σ A} :
    φ ∈ maximalIdeal (MvPowerSeries σ A) ↔ constantCoeff φ ∈ maximalIdeal A := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, isUnit_iff_constantCoeff]

theorem X_mem_maximalIdeal_mvPowerSeries (s : σ) :
    (X s : MvPowerSeries σ A) ∈ maximalIdeal (MvPowerSeries σ A) := by
  rw [mem_maximalIdeal_mvPowerSeries_iff, constantCoeff_X]
  exact zero_mem _

theorem constantCoeff_mem_sq_of_mem_sq {φ : MvPowerSeries σ A}
    (hφ : φ ∈ maximalIdeal (MvPowerSeries σ A) ^ 2) :
    constantCoeff φ ∈ maximalIdeal A ^ 2 := by
  have hmap : (maximalIdeal (MvPowerSeries σ A)).map (constantCoeff (σ := σ) (R := A)) ≤
      maximalIdeal A := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact mem_maximalIdeal_mvPowerSeries_iff.mp hx
  have : constantCoeff φ ∈ ((maximalIdeal (MvPowerSeries σ A)) ^ 2).map
      (constantCoeff (σ := σ) (R := A)) := Ideal.mem_map_of_mem _ hφ
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono hmap 2 this

/-- In `A[[u, v]]` with maximal ideal `𝔫`, the element `uv - h` is in `𝔫²` if and only if
`h ∈ 𝔪_A²`. -/
theorem X_mul_X_sub_C_mem_sq_iff (i j : σ) (h : A) :
    (X i * X j - C h : MvPowerSeries σ A) ∈ maximalIdeal (MvPowerSeries σ A) ^ 2 ↔ h ∈ maximalIdeal A ^ 2 := by
  constructor
  · intro hm
    have := constantCoeff_mem_sq_of_mem_sq hm
    simp only [map_sub, map_mul, constantCoeff_X, constantCoeff_C, zero_mul, zero_sub,
      neg_mem_iff] at this
    exact this
  · intro hm
    refine Ideal.sub_mem _ ?_ ?_
    · rw [pow_two]
      exact Ideal.mul_mem_mul (X_mem_maximalIdeal_mvPowerSeries i)
        (X_mem_maximalIdeal_mvPowerSeries j)
    · have : C h ∈ (maximalIdeal A).map (C (σ := σ) (R := A)) ^ 2 := by
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hm
      refine Ideal.pow_right_mono ?_ 2 this
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap]
      rw [mem_maximalIdeal_mvPowerSeries_iff, constantCoeff_C]
      exact hx

theorem X_mul_X_sub_C_mem_maximalIdeal (i j : σ) {h : A} (hh : h ∈ maximalIdeal A) :
    (X i * X j - C h : MvPowerSeries σ A) ∈ maximalIdeal (MvPowerSeries σ A) := by
  rw [mem_maximalIdeal_mvPowerSeries_iff]
  simpa using hh

theorem X_mul_X_sub_C_ne_zero (i j : σ) (h : A) : (X i * X j - C h : MvPowerSeries σ A) ≠ 0 := by
  classical
  intro h0
  have hc := congrArg (coeff (Finsupp.single i 1 + Finsupp.single j 1)) h0
  have hne : Finsupp.single i 1 + Finsupp.single j 1 ≠ 0 := by
    intro he
    have := congrArg (fun m => m i) he
    simp at this
  simp only [X_def, monomial_mul_monomial, map_sub, coeff_monomial, coeff_C, hne,
    ↓reduceIte, mul_one, sub_zero, map_zero] at hc
  exact one_ne_zero hc

/-- Volume 8, Lemma 2.1.3 of the handbook, with the regularity of `A[[u, v]]` as a hypothesis.
Let `(A, 𝔪_A)` be a local ring, let `h ∈ 𝔪_A`, and assume that `P = A[[u, v]]` is a regular local
ring. Then `B = P / (uv - h)` is a regular local ring if and only if `h ∉ 𝔪_A²`. -/
theorem isRegularLocalRing_quotient_X_mul_X_sub_C_iff (i j : σ)
    [IsRegularLocalRing (MvPowerSeries σ A)] {h : A} (hh : h ∈ maximalIdeal A) :
    IsRegularLocalRing (MvPowerSeries σ A ⧸ span {(X i * X j - C h : MvPowerSeries σ A)}) ↔
      h ∉ maximalIdeal A ^ 2 := by
  rw [isRegularLocalRing_quotient_span_singleton_iff _ (X_mul_X_sub_C_mem_maximalIdeal i j hh)
    (X_mul_X_sub_C_ne_zero i j h), X_mul_X_sub_C_mem_sq_iff]

/-- Volume 8, Corollary 2.1.4 of the handbook, with the regularity of `A[[u, v]]` as a
hypothesis. Let `t₁, ..., t_r` be a minimal set of generators of `𝔪_A`, let `ε` be a unit, let
`n₁, ..., n_r` be natural numbers, not all 0, and let `h = ε t₁^n₁ ⋯ t_r^n_r`. Then
`A[[u, v]] / (uv - h)` is a regular local ring if and only if `n₁ + ... + n_r = 1`. -/
theorem isRegularLocalRing_quotient_X_mul_X_sub_C_monomial_iff [IsNoetherianRing A] (i j : σ)
    [IsRegularLocalRing (MvPowerSeries σ A)] {r : ℕ} (t : Fin r → A)
    (ht : span (Set.range t) = maximalIdeal A) (hr : (maximalIdeal A).spanFinrank = r)
    {ε : A} (hε : IsUnit ε) (n : Fin r → ℕ) (hn : ∑ k, n k ≠ 0) :
    IsRegularLocalRing (MvPowerSeries σ A ⧸
        span {(X i * X j - C (ε * ∏ k, t k ^ n k) : MvPowerSeries σ A)}) ↔
      ∑ k, n k = 1 := by
  have htm : ∀ k, t k ∈ maximalIdeal A := fun k => ht ▸ subset_span ⟨k, rfl⟩
  have hh : ε * ∏ k, t k ^ n k ∈ maximalIdeal A :=
    Ideal.mul_mem_left _ ε (Ideal.pow_le_self hn
      (prod_pow_mem_ideal_pow_sum _ t (fun k _ => htm k) n))
  exact iff_sum_eq_one_of_iff_notMem_sq t ht hr hε n hn
    (isRegularLocalRing_quotient_X_mul_X_sub_C_iff i j hh)

end PowerSeries

end Singularity.Algebra
