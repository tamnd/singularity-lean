/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.MvPowerSeries.Evaluation
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The map from a power series ring to a complete local ring

This file proves Volume 1, Theorem 4.4.6 of the handbook. Let `(R, m, κ)` be a local ring that is complete and separated for the `m`-adic topology, let `K` be a field with a `K`-algebra structure on `R`, and let `x_1, ..., x_n ∈ m`. Then there is a homomorphism of `K`-algebras `φ : K[[X_1, ..., X_n]] → R` with `φ (X_i) = x_i` and `φ ((X_1, ..., X_n)^j) ⊆ m^j` for each `j`. If the map `K → κ` is surjective and `x_1, ..., x_n` generate `m`, then `φ` is surjective.

The handbook asks that `R` is Noetherian and that `K` is a coefficient field. The proof here does not use the Noetherian hypothesis. For the surjectivity it uses only that `K → κ` is surjective.

* `Singularity.Algebra.exists_homogeneous_sub_mem_pow_succ`: if `x_1, ..., x_n` generate `m` and `K → κ` is surjective, then each `y ∈ m^j` is a homogeneous polynomial of degree `j` in the `x_i` with coefficients in `K`, modulo `m^(j+1)`.
* `Singularity.Algebra.exists_cohenMap`: Theorem 4.4.6 of the handbook.

The map `φ` is `MvPowerSeries.aeval` of Mathlib, for the `m`-adic topology on `R` and the topology of `K` with the basis `{0}`.
-/

open IsLocalRing

namespace Singularity.Algebra

variable {R : Type*} [CommRing R] [IsLocalRing R] {K : Type*} [Field K] [Algebra K R]
  {σ : Type*} [Fintype σ]

/-- If `x_1, ..., x_n` generate `m` and `K → κ` is surjective, then for each `y ∈ m^j` there is a homogeneous polynomial `p` of degree `j` over `K` with `y - p (x) ∈ m^(j+1)`. -/
theorem exists_homogeneous_sub_mem_pow_succ (x : σ → R)
    (hgen : maximalIdeal R = Ideal.span (Set.range x))
    (hres : Function.Surjective fun k : K => residue R (algebraMap K R k)) (j : ℕ) :
    ∀ y ∈ maximalIdeal R ^ j, ∃ p : MvPolynomial σ K,
      p.IsHomogeneous j ∧ y - MvPolynomial.aeval x p ∈ maximalIdeal R ^ (j + 1) := by
  induction j with
  | zero =>
    intro y _
    obtain ⟨k, hk⟩ := hres (residue R y)
    have hk' : residue R (algebraMap K R k) = residue R y := hk
    refine ⟨MvPolynomial.C k, MvPolynomial.isHomogeneous_C _ _, ?_⟩
    rw [zero_add, pow_one, MvPolynomial.aeval_C, ← residue_eq_zero_iff, map_sub, hk', sub_self]
  | succ j ih =>
    intro y hy
    rw [pow_succ, hgen, ← Ideal.smul_eq_mul, Submodule.mem_ideal_smul_span_iff_exists_sum] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    choose q hq hqm using fun i => ih (a i) (by rw [hgen]; exact ha i)
    refine ⟨∑ i, MvPolynomial.X i * q i, ?_, ?_⟩
    · apply MvPolynomial.IsHomogeneous.sum
      intro i _
      rw [add_comm]
      exact (MvPolynomial.isHomogeneous_X K i).mul (hq i)
    · rw [Finsupp.sum_fintype a (fun i c => c • x i) (fun i => zero_smul _ _), map_sum, ← Finset.sum_sub_distrib]
      apply Ideal.sum_mem
      intro i _
      have hx : x i ∈ maximalIdeal R := hgen ▸ Ideal.subset_span ⟨i, rfl⟩
      have := Ideal.mul_mem_mul (hqm i) hx
      rw [← pow_succ] at this
      have e : a i • x i - MvPolynomial.aeval x (MvPolynomial.X i * q i) =
          (a i - MvPolynomial.aeval x (q i)) * x i := by
        rw [smul_eq_mul, map_mul, MvPolynomial.aeval_X]
        ring
      rw [e]
      exact this

open MvPowerSeries.WithPiTopology in
/-- Volume 1, Theorem 4.4.6 of the handbook. Let `R` be a local ring that is complete and separated for the `m`-adic topology, and let `x : σ → R` take values in `m`, with `σ` finite. Then there is a homomorphism of `K`-algebras `φ : K[[X_σ]] → R` with `φ (X_i) = x_i` and `φ ((X)^j) ⊆ m^j` for each `j`. If the `x_i` generate `m` and `K → κ` is surjective, then `φ` is surjective. -/
theorem exists_cohenMap [IsAdicComplete (maximalIdeal R) R] (x : σ → R)
    (hx : ∀ i, x i ∈ maximalIdeal R) :
    ∃ φ : MvPowerSeries σ K →ₐ[K] R, (∀ i, φ (MvPowerSeries.X i) = x i) ∧
      (∀ j : ℕ, Ideal.map φ (Ideal.span (Set.range (MvPowerSeries.X (R := K))) ^ j) ≤
        maximalIdeal R ^ j) ∧
      (maximalIdeal R = Ideal.span (Set.range x) →
        (Function.Surjective fun k : K => residue R (algebraMap K R k)) →
        Function.Surjective φ) := by
  classical
  let iR : WithIdeal R := ⟨maximalIdeal R⟩
  let iK : WithIdeal K := ⟨⊥⟩
  have hadic : IsAdic (maximalIdeal R) := rfl
  obtain ⟨hcomp, ht2⟩ := (hadic.isAdicComplete_iff).mp inferInstance
  have hcont : Continuous (algebraMap K R) :=
    (WithIdeal.uniformContinuous_of_map_le (f := algebraMap K R)
      (by change Ideal.map _ ⊥ ≤ _; rw [Ideal.map_bot]; exact bot_le)).continuous
  have : ContinuousSMul K R := continuousSMul_of_algebraMap K R hcont
  have hev : MvPowerSeries.HasEval x :=
    ⟨fun i => WithIdeal.isTopologicallyNilpotent_of_mem (hx i), by
      rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩
  refine ⟨MvPowerSeries.aeval hev, fun i => ?_, fun j => ?_, fun hgen hres => ?_⟩
  · rw [MvPowerSeries.coe_aeval, MvPowerSeries.eval₂_X]
  · rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp]
    apply Ideal.pow_right_mono
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [Function.comp_apply, MvPowerSeries.coe_aeval, MvPowerSeries.eval₂_X]
    exact hx i
  · intro r
    choose P hPh hP using fun j y => exists_homogeneous_sub_mem_pow_succ (K := K) x hgen hres j y
    let rem : (j : ℕ) → {y : R // y ∈ maximalIdeal R ^ j} :=
      fun j => Nat.rec (motive := fun j => {y : R // y ∈ maximalIdeal R ^ j})
        ⟨r, by simp⟩
        (fun j y => ⟨y.1 - MvPolynomial.aeval x (P j y.1 y.2), hP j y.1 y.2⟩) j
    let Q : ℕ → MvPolynomial σ K := fun j => P j (rem j).1 (rem j).2
    have hQ : ∀ j, (Q j).IsHomogeneous j := fun j => hPh j _ _
    let s : ℕ → MvPolynomial σ K := fun j => ∑ i ∈ Finset.range j, Q i
    have hs : ∀ j, r - MvPolynomial.aeval x (s j) = (rem j).1 := by
      intro j
      induction j with
      | zero => simp [s, rem]
      | succ j ih =>
        simp only [s, Finset.sum_range_succ, map_add] at ih ⊢
        rw [← sub_sub, ih]
    let f : MvPowerSeries σ K := fun d => (Q d.degree).coeff d
    have hcoeff : ∀ d : σ →₀ ℕ, ∀ j, d.degree < j →
        MvPowerSeries.coeff d (s j : MvPowerSeries σ K) = MvPowerSeries.coeff d f := by
      intro d j hj
      rw [MvPolynomial.coeff_coe]
      simp only [s, MvPolynomial.coeff_sum]
      rw [Finset.sum_eq_single_of_mem d.degree (Finset.mem_range.mpr hj)
        (fun i _ hi => (hQ i).coeff_eq_zero (Ne.symm hi))]
      rw [MvPowerSeries.coeff_apply]
    have h1 : Filter.Tendsto (fun j => (s j : MvPowerSeries σ K)) Filter.atTop (nhds f) := by
      rw [tendsto_iff_coeff_tendsto]
      intro d
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop (d.degree + 1)] with j hj
      exact (hcoeff d j hj).symm
    have h2 := ((MvPowerSeries.continuous_aeval hev).tendsto f).comp h1
    have h3 : Filter.Tendsto (fun j => MvPolynomial.aeval x (s j)) Filter.atTop (nhds r) := by
      rw [(hadic.hasBasis_nhds r).tendsto_right_iff]
      intro n _
      filter_upwards [Filter.eventually_ge_atTop n] with j hj
      refine ⟨-(rem j).1, neg_mem (Ideal.pow_le_pow_right hj (rem j).2), ?_⟩
      rw [← hs j]
      ring
    refine ⟨f, tendsto_nhds_unique h2 ?_⟩
    refine h3.congr fun j => ?_
    simp only [Function.comp_apply, MvPowerSeries.aeval_coe]

end Singularity.Algebra
