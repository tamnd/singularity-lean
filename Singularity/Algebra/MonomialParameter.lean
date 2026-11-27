/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.Algebra.Module.SpanRank
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Monomials in a regular system of parameters

This file proves the part on `𝔪²` of Volume 8, Corollary 2.1.4 of the handbook. Let `(R, 𝔪)` be a Noetherian local ring and let `t₁, ..., t_r` be a minimal set of generators of `𝔪`. For a regular local ring of dimension `r`, these are the regular systems of parameters. Let `ε` be a unit and let `n₁, ..., n_r` be natural numbers, not all 0. Then `ε t₁^n₁ ⋯ t_r^n_r ∉ 𝔪²` if and only if `n₁ + ... + n_r = 1`.

* `Singularity.Algebra.notMem_maximalIdeal_sq_of_span_eq`: no element of a minimal set of generators of `𝔪` is in `𝔪²`. The proof is Nakayama's lemma.
* `Singularity.Algebra.mul_prod_pow_mem_sq`: if `n₁ + ... + n_r ≥ 2`, then the monomial is in `𝔪²`.
* `Singularity.Algebra.mul_prod_pow_notMem_sq_iff`: the equivalence above.
* `Singularity.Algebra.iff_sum_eq_one_of_iff_notMem_sq`: Corollary 2.1.4, with Lemma 2.1.3 as a hypothesis.

Lemma 2.1.3 says that `A[[u, v]] / (uv - h)` is regular if and only if `h ∉ 𝔪²`. It is not in Lean, so the last theorem takes it as a hypothesis.
-/

open IsLocalRing Ideal

namespace Singularity.Algebra

variable {R : Type*} [CommRing R]

/-- If each `t i` is in the ideal `I`, then `∏ t_i ^ n_i` is in `I ^ (∑ n_i)`. -/
theorem prod_pow_mem_ideal_pow_sum {ι : Type*} (s : Finset ι) {I : Ideal R} (t : ι → R)
    (ht : ∀ i ∈ s, t i ∈ I) (n : ι → ℕ) :
    ∏ i ∈ s, t i ^ n i ∈ I ^ (∑ i ∈ s, n i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i hi => Ideal.pow_mem_pow (ht i hi) (n i)

/-- Let `t₁, ..., t_r` be elements of `𝔪`. If `n₁ + ... + n_r ≥ 2`, then `ε t₁^n₁ ⋯ t_r^n_r ∈ 𝔪²` (one half of Volume 8, Corollary 2.1.4 of the handbook). -/
theorem mul_prod_pow_mem_sq [IsLocalRing R] {r : ℕ} (t : Fin r → R)
    (ht : ∀ i, t i ∈ maximalIdeal R) (ε : R) (n : Fin r → ℕ) (hn : 2 ≤ ∑ i, n i) :
    ε * ∏ i, t i ^ n i ∈ maximalIdeal R ^ 2 :=
  Ideal.mul_mem_left _ ε
    (Ideal.pow_le_pow_right hn (prod_pow_mem_ideal_pow_sum _ t (fun i _ => ht i) n))

/-- Let `(R, 𝔪)` be a Noetherian local ring and let `t₁, ..., t_r` be a minimal set of generators of `𝔪`, that is `r` generators with `r` the least number of generators of `𝔪`. Then no `t_i` is in `𝔪²`. For a regular local ring of dimension `r`, these are the regular systems of parameters. -/
theorem notMem_maximalIdeal_sq_of_span_eq [IsLocalRing R] [IsNoetherianRing R] {r : ℕ}
    (t : Fin r → R) (ht : span (Set.range t) = maximalIdeal R)
    (hr : (maximalIdeal R).spanFinrank = r) (i : Fin r) : t i ∉ maximalIdeal R ^ 2 := by
  classical
  intro hi
  set N : Ideal R := span (((Finset.univ.erase i).image t : Finset R) : Set R) with hN
  have hle : maximalIdeal R ≤ N ⊔ maximalIdeal R • maximalIdeal R := by
    rw [← ht, span_le]
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i
    · subst hj
      refine Submodule.mem_sup_right ?_
      rw [smul_eq_mul, ← pow_two, ht]
      exact hi
    · refine Submodule.mem_sup_left (subset_span ?_)
      simp only [Finset.coe_image, Finset.coe_erase, Finset.coe_univ]
      exact ⟨j, ⟨trivial, hj⟩, rfl⟩
  have hNm : maximalIdeal R ≤ N :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (maximalIdeal R).fg_of_isNoetherianRing
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) hle
  have hNm' : N ≤ maximalIdeal R := by
    rw [hN, span_le, ← ht]
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨j, _, rfl⟩ := hx
    exact subset_span ⟨j, rfl⟩
  have hEq : N = maximalIdeal R := le_antisymm hNm' hNm
  have h1 : (maximalIdeal R).spanFinrank ≤ r - 1 := by
    rw [← hEq, hN]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)).trans ?_
    rw [Set.ncard_coe_finset]
    refine Finset.card_image_le.trans ?_
    simp [Finset.card_erase_of_mem]
  have : 0 < r := Fin.pos i
  omega

/-- Volume 8, Corollary 2.1.4 of the handbook, the part on `𝔪²`. Let `(R, 𝔪)` be a Noetherian local ring, let `t₁, ..., t_r` be a minimal set of generators of `𝔪` (for example a regular system of parameters of a regular local ring), let `ε` be a unit and let `n₁, ..., n_r` be natural numbers, not all 0. Then `ε t₁^n₁ ⋯ t_r^n_r ∉ 𝔪²` if and only if `n₁ + ... + n_r = 1`. -/
theorem mul_prod_pow_notMem_sq_iff [IsLocalRing R] [IsNoetherianRing R] {r : ℕ}
    (t : Fin r → R) (ht : span (Set.range t) = maximalIdeal R)
    (hr : (maximalIdeal R).spanFinrank = r) {ε : R} (hε : IsUnit ε) (n : Fin r → ℕ)
    (hn : ∑ i, n i ≠ 0) :
    ε * ∏ i, t i ^ n i ∉ maximalIdeal R ^ 2 ↔ ∑ i, n i = 1 := by
  classical
  have htm : ∀ i, t i ∈ maximalIdeal R := fun i => ht ▸ subset_span ⟨i, rfl⟩
  constructor
  · intro h
    by_contra h1
    exact h (mul_prod_pow_mem_sq t htm ε n (by omega))
  · intro h1 hmem
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    have hle : ∀ j, j ≠ i → n j = 0 := by
      intro j hj
      have : n i + n j ≤ ∑ k, n k := by
        rw [← Finset.sum_pair hj.symm]
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      omega
    have hni : n i = 1 := by
      have : n i ≤ ∑ k, n k :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    have hprod : ∏ j, t j ^ n j = t i := by
      rw [Finset.prod_eq_single i (fun j _ hj => by rw [hle j hj, pow_zero])
        (fun h => absurd (Finset.mem_univ i) h), hni, pow_one]
    rw [hprod] at hmem
    obtain ⟨u, rfl⟩ := hε
    have : t i = ↑u⁻¹ * (↑u * t i) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    exact notMem_maximalIdeal_sq_of_span_eq t ht hr i (this ▸ Ideal.mul_mem_left _ _ hmem)

/-- Volume 8, Corollary 2.1.4 of the handbook, given Lemma 2.1.3. Let `regular` be the statement that `B = A[[u, v]] / (uv - h)` is regular, and assume Lemma 2.1.3 in the form `regular ↔ h ∉ 𝔪²`. Then for `h = ε t₁^n₁ ⋯ t_r^n_r` with the `t_i` a minimal set of generators of `𝔪`, `ε` a unit and the `n_i` not all 0, `B` is regular if and only if `n₁ + ... + n_r = 1`. Lemma 2.1.3 itself is not in Lean. -/
theorem iff_sum_eq_one_of_iff_notMem_sq [IsLocalRing R] [IsNoetherianRing R] {r : ℕ}
    (t : Fin r → R) (ht : span (Set.range t) = maximalIdeal R)
    (hr : (maximalIdeal R).spanFinrank = r) {ε : R} (hε : IsUnit ε) (n : Fin r → ℕ)
    (hn : ∑ i, n i ≠ 0) {regular : Prop}
    (lemma_2_1_3 : regular ↔ ε * ∏ i, t i ^ n i ∉ maximalIdeal R ^ 2) :
    regular ↔ ∑ i, n i = 1 :=
  lemma_2_1_3.trans (mul_prod_pow_notMem_sq_iff t ht hr hε n hn)

end Singularity.Algebra

