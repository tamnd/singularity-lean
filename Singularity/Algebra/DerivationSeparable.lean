/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib

/-!
# Derivations kill separable elements and are continuous

This file proves Volume 2, Lemma 2.1.1 of the handbook in part: the statements about
derivations used in its proof.

* A `k`-derivation `D : A → M` kills each root `b` of a polynomial `Q` over `k` for which
  `Q'(b)` acts injectively on `M`, in particular when `Q'(b)` is a unit. So a `k`-derivation
  of a field `L` kills each element of `L` that is separable over `k`, and it is zero when
  `L / k` is separable.
* A derivation maps `I^(r+1)` into `I^r • M`. For a local ring this gives
  `D(𝔪^(r+1)) ⊆ 𝔪^r`, and so a derivation of a ring is continuous for the `I`-adic topology.
* A `K`-derivation of `K[x_1, ..., x_n]` with `D(x_j) = δ_ij` is the partial derivative
  `∂/∂x_i`. The same holds for the power series ring `K[[x_1, ..., x_n]]`. There no
  continuity hypothesis is needed: the proof writes a power series as a polynomial plus a
  sum of terms `x_j^(d_j+1) h_j`, and `D` kills `x_j`.

Not proved here: the existence and uniqueness of the coefficient field in the completion
(this needs Hensel's lemma) and the identification of the completion with
`K[[x_1, ..., x_n]]`. The power series statement is for a finite set of variables.
The repo already has `Singularity.derivation_mem_pow_pred` (Volume 6, Lemma 1.2.4) for
`M` equal to the ring. The version here allows a module `M` and adds continuity.
-/

open Polynomial

namespace Singularity

section Root

variable {k A M : Type*} [CommRing k] [CommRing A] [Algebra k A]
  [AddCommGroup M] [Module A M] [Module k M]

/-- Let `b` be a root of `Q ∈ k[X]` such that `Q'(b)` acts injectively on `M`. Then a
`k`-derivation `D : A → M` kills `b`. -/
theorem derivation_eq_zero_of_aeval_eq_zero_of_smul_injective (D : Derivation k A M)
    {b : A} {Q : k[X]} (hQ : aeval b Q = 0)
    (hreg : ∀ m : M, aeval b (derivative Q) • m = 0 → m = 0) : D b = 0 := by
  apply hreg
  rw [← D.map_aeval, hQ, D.map_zero]

/-- Let `b` be a root of `Q ∈ k[X]` such that `Q'(b)` is a unit. Then a `k`-derivation kills
`b`. -/
theorem derivation_eq_zero_of_aeval_eq_zero_of_isUnit (D : Derivation k A M)
    {b : A} {Q : k[X]} (hQ : aeval b Q = 0) (hu : IsUnit (aeval b (derivative Q))) :
    D b = 0 :=
  derivation_eq_zero_of_aeval_eq_zero_of_smul_injective D hQ fun m hm =>
    hu.smul_left_cancel.1 (by rw [hm, smul_zero])

end Root

section Field

variable {k L M : Type*} [Field k] [Field L] [Algebra k L]
  [AddCommGroup M] [Module L M] [Module k M]

/-- A `k`-derivation of a field `L` kills each element of `L` that is separable over `k`. -/
theorem derivation_eq_zero_of_isSeparable (D : Derivation k L M) {x : L}
    (hx : IsSeparable k x) : D x = 0 :=
  derivation_eq_zero_of_aeval_eq_zero_of_isUnit D (minpoly.aeval k x)
    (hx.aeval_derivative_ne_zero (minpoly.aeval k x)).isUnit

/-- A `k`-derivation of a separable field extension `L` of `k` is zero. -/
theorem derivation_eq_zero_of_algebra_isSeparable [Algebra.IsSeparable k L]
    (D : Derivation k L M) : D = 0 :=
  Derivation.ext fun x => derivation_eq_zero_of_isSeparable D (Algebra.IsSeparable.isSeparable k x)

end Field

section Adic

variable {R A M : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M]

/-- A derivation `D : A → M` maps `I^(r+1)` into `I^r • M`. -/
theorem derivation_mem_pow_smul_top_of_mem_pow_succ (D : Derivation R A M) (I : Ideal A) :
    ∀ r : ℕ, ∀ x ∈ I ^ (r + 1), D x ∈ I ^ r • (⊤ : Submodule A M)
  | 0 => fun _ _ => by simp
  | r + 1 => by
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz]
      refine add_mem (Submodule.smul_mem_smul (pow_succ I r ▸ ha) Submodule.mem_top) ?_
      rw [pow_succ', mul_smul]
      exact Submodule.smul_mem_smul hb (derivation_mem_pow_smul_top_of_mem_pow_succ D I r a ha)
    · intro y z hy hz
      rw [map_add]
      exact add_mem hy hz

/-- A derivation of `A` maps `I^(r+1)` into `I^r`. -/
theorem derivation_mem_pow_of_mem_pow_succ (D : Derivation R A A) (I : Ideal A) (r : ℕ)
    {x : A} (hx : x ∈ I ^ (r + 1)) : D x ∈ I ^ r := by
  have := derivation_mem_pow_smul_top_of_mem_pow_succ D I r x hx
  rwa [smul_eq_mul, Ideal.mul_top] at this

/-- A derivation of a local ring maps `𝔪^(r+1)` into `𝔪^r`. -/
theorem derivation_mem_maximalIdeal_pow [IsLocalRing A] (D : Derivation R A A) (r : ℕ)
    {x : A} (hx : x ∈ IsLocalRing.maximalIdeal A ^ (r + 1)) :
    D x ∈ IsLocalRing.maximalIdeal A ^ r :=
  derivation_mem_pow_of_mem_pow_succ D _ r hx

/-- A derivation of `A` is continuous for the `I`-adic topology. -/
theorem continuous_derivation_adic (D : Derivation R A A) (I : Ideal A) :
    @Continuous A A I.adicTopology I.adicTopology D := by
  let := I.adicTopology
  rw [continuous_iff_continuousAt]
  intro x
  refine ((I.hasBasis_nhds_adic x).tendsto_iff (I.hasBasis_nhds_adic (D x))).2 ?_
  intro n _
  refine ⟨n + 1, trivial, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨D y, derivation_mem_pow_of_mem_pow_succ D I n hy, by simp⟩

end Adic

section MvPolynomial

variable {σ K : Type*} [CommRing K]

/-- A `K`-derivation of `K[X_j]` with `D(X_j) = δ_ij` is the partial derivative in `X_i`. -/
theorem MvPolynomial.derivation_eq_pderiv [DecidableEq σ]
    (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K)) (i : σ)
    (hD : ∀ j, D (MvPolynomial.X j) = Pi.single (M := fun _ => MvPolynomial σ K) i 1 j) :
    D = MvPolynomial.pderiv i :=
  MvPolynomial.derivation_ext fun j => by rw [hD, MvPolynomial.pderiv_X]

end MvPolynomial

open MvPowerSeries in
/-- A `K`-derivation of `K[[X_j]]`, for finitely many variables, with `D(X_j) = δ_ij` is the
partial derivative in `X_i`. No continuity hypothesis is needed. -/
theorem MvPowerSeries.derivation_eq_pderiv {σ K : Type*} [CommRing K] [Fintype σ]
    [DecidableEq σ]
    (D : Derivation K (MvPowerSeries σ K) (MvPowerSeries σ K)) (i : σ)
    (hD : ∀ j, D (X j) = Pi.single (M := fun _ => MvPowerSeries σ K) i 1 j) : D = pderiv i := by
  classical
  set E := D - pderiv i with hE
  have hEX : ∀ j, E (X j) = 0 := fun j => by
    rw [hE, Derivation.coe_sub, Pi.sub_apply, hD, pderiv_X, sub_self]
  have hEC : ∀ a : K, E (C a) = 0 := fun a => by
    have : (C a : MvPowerSeries σ K) = a • 1 := by rw [MvPowerSeries.smul_eq_C_mul, mul_one]
    rw [this, Derivation.map_smul, Derivation.map_one_eq_zero, smul_zero]
  have hEpoly : ∀ p : MvPolynomial σ K, E (p : MvPowerSeries σ K) = 0 := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => rw [MvPolynomial.coe_C, hEC]
    | add p q hp hq => rw [MvPolynomial.coe_add, map_add, hp, hq, add_zero]
    | mul_X p j hp => rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, Derivation.leibniz, hp,
        hEX, smul_zero, smul_zero, add_zero]
  have hEmon : ∀ (j : σ) (k : ℕ) (h : MvPowerSeries σ K),
      E (monomial (Finsupp.single j k) 1 * h) = monomial (Finsupp.single j k) 1 * E h := by
    intro j k h
    rw [← X_pow_eq, Derivation.leibniz, Derivation.leibniz_pow, hEX]
    simp only [smul_zero, add_zero, smul_eq_mul, mul_zero]
  have hE0 : E = 0 := by
    ext f d
    -- the tail of `f` beyond the box `≤ d`
    set g := f - (trunc' K d f : MvPowerSeries σ K) with hg
    have hgc : ∀ e, coeff e g ≠ 0 → ∃ j, d j + 1 ≤ e j := by
      intro e he
      by_contra hne
      push Not at hne
      apply he
      have hle : e ≤ d := fun j => Nat.lt_succ_iff.mp (hne j)
      rw [hg, map_sub, MvPolynomial.coeff_coe, coeff_trunc', ite_eq_left hle, sub_self]
    let h : σ → MvPowerSeries σ K := fun j e' =>
      let e := e' + Finsupp.single j (d j + 1)
      if hx : ∃ j', d j' + 1 ≤ e j' then (if hx.choose = j then coeff e g else 0) else 0
    have hh : ∀ (j : σ) (e : σ →₀ ℕ), d j + 1 ≤ e j →
        coeff (e - Finsupp.single j (d j + 1)) (h j) =
          if hx : ∃ j', d j' + 1 ≤ e j' then (if hx.choose = j then coeff e g else 0)
          else 0 := by
      intro j e hj
      have he : e - Finsupp.single j (d j + 1) + Finsupp.single j (d j + 1) = e :=
        tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hj)
      change h j (e - Finsupp.single j (d j + 1)) = _
      simp only [h, he]
    have hdec : g = ∑ j, monomial (Finsupp.single j (d j + 1)) 1 * h j := by
      ext e
      rw [map_sum]
      simp_rw [MvPowerSeries.coeff_monomial_mul, Finsupp.single_le_iff, one_mul]
      by_cases hx : ∃ j', d j' + 1 ≤ e j'
      · rw [Finset.sum_eq_single hx.choose]
        · rw [ite_eq_left hx.choose_spec, hh _ _ hx.choose_spec, dite_eq_left hx, ite_eq_left rfl]
        · intro j _ hj
          split_ifs with hje
          · rw [hh _ _ hje, dite_eq_left hx, ite_eq_right (Ne.symm hj)]
          · rfl
        · simp
      · rw [Finset.sum_eq_zero]
        · by_contra hne
          exact hx (hgc e hne)
        · intro j _
          rw [ite_eq_right (fun hj => hx ⟨j, hj⟩)]
    have hf : f = (trunc' K d f : MvPowerSeries σ K) + g := by rw [hg]; ring
    rw [hf, map_add, hEpoly, zero_add, hdec, map_sum, map_sum]
    simp_rw [hEmon, MvPowerSeries.coeff_monomial_mul, Finsupp.single_le_iff]
    simp
  exact sub_eq_zero.mp hE0


end Singularity
