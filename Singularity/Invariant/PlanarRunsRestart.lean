/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Singularity.Invariant.PlanarRuns
import Singularity.Invariant.PlanarRunsCondition

/-!
# The run seen from a later point

This file proves the algebraic part of Lemma 3.19.2 of Volume 7 of the handbook (Lemma 2.1 of
research note 74), the restart identities, and part 2 of Corollary 3.19.3.

## The model

`K` is a field, the field `𝕂` of the handbook, and `g ∈ K[X_i : i ∈ σ]` is a polynomial. The
handbook has `σ = Fin 2` and the variables `(x, w)`. Let `φ : σ → K` be the point `Φ_m`, let `M`
be the monomial `M_m`, and let `Δ : σ → K` be the tail `Δ_m = Φ_∞ - Φ_m`. So `φ + Δ` is `Φ_∞`.

* `chart φ M g` is the chart substitution `g̃_m = g(φ_i + M X_i)`, written with `aeval`. Its
  coefficients are `A_k = M^{|k|} g^{[k]}(φ)` (`coeff_chart`).
* The classes of the Hahn field are kept only through two objects: a subring `K0` (the elements
  whose terms all have the class `0`) and an additive map `cl : K →+ K` (the part of nonzero
  class). The predicate `IsClassPart p K0 cl` holds facts 2 and 3 of the setting of Section 3.19:
  `x ^ p ∈ K0`, `cl (a x) = a cl x` for `a ∈ K0`, `cl a = 0` for `a ∈ K0`, and
  `x - cl x ∈ K0`.
* `clean p cl h` replaces the coefficient `c` of each monomial `X^k` with `p ∣ k_i` for all `i` by
  `cl c`. This is the cleaning, which acts monomial by monomial.
* `restart p cl φ M g = M^{-p} clean (chart φ M g)` is the function `g^{(m)}` of `P_m`, given by
  the formula of Lemma 3.17.1.

## Main results

* `eq_cornerSum_add_cornerMono_mul` (Lemma 3.17.1, part 1): if `x_m = L_m (x_{m+1} + a_m)` for
  each `m`, then `x_0 = φ_m + M_m x_m`, with `M_{m+1} = M_m L_m` and
  `φ_{m+1} = φ_m + a_m M_{m+1}`.
* `coeff_clean_chart` (Lemma 3.17.1, part 3): the coefficient of `X^k` in `cl(g̃_m)` is
  `A_k = M^{|k|} g^{[k]}(φ)` if some `k_i` is not divisible by `p`, and `cl A_k` otherwise.
* `hasse_single_clean_chart` (Lemma 3.17.1, part 4): in characteristic `p`,
  `∂_{X_i} cl(g̃_m) = M g_{X_i}(φ + M X)`.
* `eval_hasse_single_restart` (Lemma 3.19.2, part 1): in characteristic `p`,
  `g^{(m)}_{X_i}(Δ / M) = M^{1 - p} g_{X_i}(φ + Δ)`.
* `cl_eval_restart` (Lemma 3.19.2, part 2): `cl g^{(m)}(Δ / M) = M^{-p} cl g(φ + Δ)`.
* `eval_hasse_restart_eq_sum` and `eval_hasse_pow_restart_eq_sum` (Lemma 3.19.2, part 3, the
  identity (19.1)): for each `j`,
  `(g^{(m)})^{[j]}(Δ / M) = M^{|j| - p} Σ_k (Π_i C(k_i, j_i)) [g^{[k]}(φ)]' Δ^{k - j}`, with the
  factor `M^{p^e - p}` for `j = p^e e_i`.
* `restart_sub_mem` (Corollary 3.19.3, part 2): if `p ∣ j_i` for each `i`, then
  `M^{p - |j|} (g^{(m)})^{[j]}(Δ / M) - g^{[j]}(φ + Δ)` lies in `K0`, that is, it has only terms
  of class `0`.
* `map_hasse_single_restart_add` (Corollary 3.19.3, part 1): for a valuation `v` with
  `v(M) = r`, `v(g^{(m)}_{X_i}(Δ / M)) + (Θ - r) + p r = v(g_{X_i}(φ + Δ)) + Θ`, that is,
  `Λ^{(m)}_0 + p v(M_m) = Λ_0` for each first derivative.
* `map_cl_eval_restart_add` (Corollary 3.19.3, part 3):
  `v(cl g^{(m)}(Δ / M)) + p v(M) = v(cl g(φ + Δ))`.
* `totalDegree_restart` (Lemma 3.19.1, part 3): if `g` is clean (`IsClean`), that is, `cl c = c`
  for each coefficient `c` of a monomial `X^k` with `p ∣ k_i` for each `i`, and `M ≠ 0`, then
  `g^{(m)}` has the same total degree as `g`.

Part 1 of Lemma 3.19.2 and part 4 of Lemma 3.17.1 use the characteristic. They use no property
of `cl`.

## What is not proved

The file does not build the corner runs, the Hahn field and its classes. So it does not prove
that `restart p cl φ M g` is the function of `P_m` (Lemma 3.17.1, part 2), and it does not
prove parts 1, 2 and 4 of Lemma 3.19.1. The bound on the values of the terms of class `0` in
part 4 of Lemma 3.19.2 is not proved.

## References

* Volume 7, Section 3.19 of the handbook: Lemma 3.19.2 and Corollary 3.19.3.
* Research note 74, Lemma 2.1 and Corollary 2.2.
-/

open MvPolynomial Finsupp

namespace Singularity

namespace PlanarRuns

section CornerCoordinates

variable {R : Type*} [CommRing R]

/-- The monomial `M_m` of a run, with `M_0 = 1` and `M_{m+1} = M_m L_m`. -/
def cornerMono (L : ℕ → R) : ℕ → R
  | 0 => 1
  | m + 1 => cornerMono L m * L m

/-- The sum `φ_m` of a run, with `φ_0 = 0` and `φ_{m+1} = φ_m + a_m M_{m+1}`. -/
def cornerSum (L a : ℕ → R) : ℕ → R
  | 0 => 0
  | m + 1 => cornerSum L a m + a m * cornerMono L (m + 1)

/-- Lemma 3.17.1, part 1: if `x_m = L_m (x_{m+1} + a_m)` for each `m`, then
`x_0 = φ_m + M_m x_m`. -/
theorem eq_cornerSum_add_cornerMono_mul (L a x : ℕ → R) (hx : ∀ m, x m = L m * (x (m + 1) + a m))
    (m : ℕ) : x 0 = cornerSum L a m + cornerMono L m * x m := by
  induction m with
  | zero => simp [cornerSum, cornerMono]
  | succ m ih =>
    rw [ih, hx m, cornerSum, cornerMono]
    ring

end CornerCoordinates

section HasseLinear

variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]

theorem hasse_sub (k : σ →₀ ℕ) (f g : MvPolynomial σ R) :
    hasse k (f - g) = hasse k f - hasse k g := by
  ext m
  simp only [coeff_hasse, coeff_sub, smul_sub]

theorem hasse_C_mul (k : σ →₀ ℕ) (a : R) (f : MvPolynomial σ R) :
    hasse k (C a * f) = C a * hasse k f := by
  ext m
  simp only [coeff_hasse, coeff_C_mul, nsmul_eq_mul]
  ring

end HasseLinear

section Restart

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

/-- The chart substitution `g̃ = g(φ_i + M X_i)`. -/
noncomputable def chart (φ : σ → K) (M : K) (g : MvPolynomial σ K) : MvPolynomial σ K :=
  aeval (fun i => C (φ i) + C M * X i) g

omit [Fintype σ] [DecidableEq σ] in
theorem eval_chart (φ x : σ → K) (M : K) (g : MvPolynomial σ K) :
    eval x (chart φ M g) = eval (fun i => φ i + M * x i) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [chart]
  | add f g hf hg =>
    simp only [chart] at hf hg ⊢
    simp [hf, hg]
  | mul_X f i hf =>
    simp only [chart] at hf ⊢
    simp [hf]

omit [Fintype σ] [DecidableEq σ] in
theorem eval₂_C_C (φ : σ → K) (f : MvPolynomial σ K) :
    eval₂ C (fun i => C (φ i)) f = (C (eval φ f) : MvPolynomial σ K) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [eval₂_add, hf, hg]
  | mul_X f i hf => simp [eval₂_mul, hf]

omit [DecidableEq σ] in
theorem prod_C_mul_X_pow (M : K) (k : σ →₀ ℕ) :
    ∏ i, (C M * X i : MvPolynomial σ K) ^ k i = monomial k (M ^ ord k) := by
  simp_rw [mul_pow, ← C_pow, C_mul_X_pow_eq_monomial]
  rw [← monomial_sum_prod, univ_sum_single, ord, Finset.prod_pow_eq_pow_sum]

theorem hasse_eq_zero_of_lt {g : MvPolynomial σ K} {N : ℕ} (hN : ∀ i, degreeOf i g ≤ N)
    {k : σ →₀ ℕ} {i : σ} (hi : N < k i) : hasse k g = 0 := by
  by_contra h0
  have h1 := le_degreeOf_of_hasse_ne_zero h0 i
  have h2 := hN i
  omega

/-- The coefficients of the chart substitution: `A_k = M^{|k|} g^{[k]}(φ)`. -/
theorem coeff_chart (φ : σ → K) (M : K) (g : MvPolynomial σ K) (k : σ →₀ ℕ) :
    (chart φ M g).coeff k = M ^ ord k * eval φ (hasse k g) := by
  set N := ∑ i, degreeOf i g with hNdef
  have hN : ∀ i, degreeOf i g ≤ N := fun i =>
    Finset.single_le_sum (f := fun i => degreeOf i g) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have h : chart φ M g = ∑ j ∈ box σ N, monomial j (M ^ ord j * eval φ (hasse j g)) := by
    have hfun : (fun i => C (φ i) + C M * X i) =
        (fun i => (C (φ i) : MvPolynomial σ K)) + fun i => C M * X i := rfl
    rw [chart, aeval_def, algebraMap_eq, hfun, eval₂_add_eq_sum C _ _ g hN]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval₂_C_C, prod_C_mul_X_pow, C_mul_monomial, mul_comm (eval φ _)]
  rw [h, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hk
  · rfl
  · rw [mem_box] at hk
    push Not at hk
    obtain ⟨i, hi⟩ := hk
    rw [hasse_eq_zero_of_lt hN hi, map_zero, mul_zero]

/-- The chain rule for the chart: `(g̃)^{[j]} = M^{|j|} (g^{[j]})~`. -/
theorem hasse_chart (φ : σ → K) (M : K) (g : MvPolynomial σ K) (j : σ →₀ ℕ) :
    hasse j (chart φ M g) = C (M ^ ord j) * chart φ M (hasse j g) := by
  ext m
  have hord : ord (m + j) = ord m + ord j := by
    simp [ord, Finset.sum_add_distrib]
  have hc : ∏ i, (j i + m i).choose (j i) = ∏ i, (m i + j i).choose (j i) :=
    Finset.prod_congr rfl fun i _ => by rw [Nat.add_comm]
  rw [coeff_hasse, coeff_C_mul, coeff_chart, coeff_chart, hasse_hasse, hc, add_comm j m, hord]
  simp only [nsmul_eq_mul, map_mul, map_natCast, pow_add]
  ring

/-- The coefficient of `X^k` after the cleaning: `cl c` if `p ∣ k_i` for each `i`, and `c`
otherwise. This is `[c]'` of (19.1). -/
noncomputable def clCoeff (p : ℕ) (cl : K →+ K) (k : σ →₀ ℕ) (c : K) : K :=
  if ∀ i, p ∣ k i then cl c else c

omit [DecidableEq σ] in
theorem clCoeff_zero (p : ℕ) (cl : K →+ K) (k : σ →₀ ℕ) : clCoeff p cl k 0 = 0 := by
  simp [clCoeff]

/-- The cleaning, monomial by monomial. -/
noncomputable def clean (p : ℕ) (cl : K →+ K) (h : MvPolynomial σ K) : MvPolynomial σ K :=
  ∑ k ∈ h.support, monomial k (clCoeff p cl k (h.coeff k))

theorem coeff_clean (p : ℕ) (cl : K →+ K) (h : MvPolynomial σ K) (k : σ →₀ ℕ) :
    (clean p cl h).coeff k = clCoeff p cl k (h.coeff k) := by
  simp only [clean, coeff_sum, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hk
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hk, clCoeff_zero]

/-- The function `g^{(m)} = M^{-p} cl(g(φ + M X))` of the point `P_m`, by the formula of
Lemma 3.17.1. -/
noncomputable def restart (p : ℕ) (cl : K →+ K) (φ : σ → K) (M : K) (g : MvPolynomial σ K) :
    MvPolynomial σ K :=
  C (M ^ p)⁻¹ * clean p cl (chart φ M g)

/-- The part removed by the cleaning. -/
noncomputable def removed (p : ℕ) (cl : K →+ K) (h : MvPolynomial σ K) : MvPolynomial σ K :=
  h - clean p cl h

theorem coeff_removed_ne_zero {p : ℕ} {cl : K →+ K} {h : MvPolynomial σ K} {k : σ →₀ ℕ}
    (hk : (removed p cl h).coeff k ≠ 0) :
    (∀ i, p ∣ k i) ∧ (removed p cl h).coeff k = h.coeff k - cl (h.coeff k) := by
  rw [removed, coeff_sub, coeff_clean, clCoeff] at hk ⊢
  by_cases hc : ∀ i, p ∣ k i
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    exact ⟨hc, rfl⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), sub_self] at hk
    exact absurd rfl hk

omit [DecidableEq σ] in
theorem restart_eq (p : ℕ) (cl : K →+ K) (φ : σ → K) (M : K) (g : MvPolynomial σ K) :
    restart p cl φ M g =
      C (M ^ p)⁻¹ * chart φ M g - C (M ^ p)⁻¹ * removed p cl (chart φ M g) := by
  rw [restart, removed]
  ring

theorem eval_hasse_restart (p : ℕ) (cl : K →+ K) (φ Δ : σ → K) {M : K} (hM : M ≠ 0)
    (g : MvPolynomial σ K) (j : σ →₀ ℕ) :
    eval (fun l => Δ l / M) (hasse j (restart p cl φ M g)) =
      (M ^ p)⁻¹ * (M ^ ord j * eval (φ + Δ) (hasse j g) -
        eval (fun l => Δ l / M) (hasse j (removed p cl (chart φ M g)))) := by
  have hφ : (fun l => φ l + M * (Δ l / M)) = φ + Δ := by
    funext l
    rw [Pi.add_apply]
    field_simp
  rw [restart_eq, hasse_sub, hasse_C_mul, hasse_C_mul, hasse_chart, eval_sub, eval_mul, eval_mul,
    eval_mul, eval_C, eval_C, eval_chart, hφ]
  ring

/-- In characteristic `p`, the first derivatives of the removed part are `0`. -/
theorem hasse_single_removed {p : ℕ} [CharP K p] (cl : K →+ K) (h : MvPolynomial σ K) (i : σ) :
    hasse (single i 1) (removed p cl h) = 0 := by
  ext m
  rw [coeff_hasse, show (0 : MvPolynomial σ K).coeff m = 0 from rfl]
  by_cases h0 : (removed p cl h).coeff (m + single i 1) = 0
  · rw [h0, smul_zero]
  · have hd := (coeff_removed_ne_zero h0).1 i
    have hprod : ∏ l, (m l + single i 1 l).choose (single i 1 l) = m i + 1 := by
      rw [Finset.prod_eq_single i]
      · simp
      · intro l _ hl
        simp [Ne.symm hl]
      · simp
    rw [hprod, nsmul_eq_mul]
    have hz : ((m i + 1 : ℕ) : K) = 0 := by
      rw [CharP.cast_eq_zero_iff K p]
      simpa [Finsupp.add_apply] using hd
    rw [hz, zero_mul]

/-- Lemma 3.19.2, part 1: `g^{(m)}_{X_i}(Δ / M) = M^{1 - p} g_{X_i}(φ + Δ)`. -/
theorem eval_hasse_single_restart {p : ℕ} [CharP K p] (cl : K →+ K) (φ Δ : σ → K) {M : K}
    (hM : M ≠ 0) (g : MvPolynomial σ K) (i : σ) :
    eval (fun l => Δ l / M) (hasse (single i 1) (restart p cl φ M g)) =
      M ^ (1 - p : ℤ) * eval (φ + Δ) (hasse (single i 1) g) := by
  have hord : ord (single i 1 : σ →₀ ℕ) = 1 := by
    simp [ord, single_apply]
  rw [eval_hasse_restart p cl φ Δ hM, hasse_single_removed, map_zero, sub_zero, hord, pow_one,
    ← mul_assoc, zpow_sub₀ hM, zpow_one, zpow_natCast, div_eq_inv_mul]

/-- The facts on the classes that the restart identities use. `K0` is the subring of the
elements with only terms of class `0`, and `cl x` is the part of `x` of nonzero class. -/
structure IsClassPart (p : ℕ) (K0 : Subring K) (cl : K →+ K) : Prop where
  pow_mem : ∀ x : K, x ^ p ∈ K0
  map_mul : ∀ a ∈ K0, ∀ x, cl (a * x) = a * cl x
  map_eq_zero : ∀ a ∈ K0, cl a = 0
  sub_mem : ∀ x, x - cl x ∈ K0

variable {p : ℕ} {K0 : Subring K} {cl : K →+ K}

omit [Fintype σ] [DecidableEq σ] in
theorem IsClassPart.pow_mul_mem (hcl : IsClassPart p K0 cl) (x : K) {n : ℕ} (hn : p ∣ n) :
    x ^ n ∈ K0 := by
  obtain ⟨c, rfl⟩ := hn
  rw [pow_mul']
  exact hcl.pow_mem _

/-- The derivatives of order divisible by `p` of the removed part have only terms of class
`0` at each point. -/
theorem eval_hasse_removed_mem (hcl : IsClassPart p K0 cl) (h : MvPolynomial σ K)
    {j : σ →₀ ℕ} (hj : ∀ i, p ∣ j i) (x : σ → K) :
    eval x (hasse j (removed p cl h)) ∈ K0 := by
  rw [hasse, map_sum]
  refine Subring.sum_mem _ fun e he => ?_
  have he0 := MvPolynomial.mem_support_iff.mp he
  obtain ⟨hd, hc⟩ := coeff_removed_ne_zero he0
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  refine Subring.mul_mem _ ?_ ?_
  · rw [nsmul_eq_mul, hc]
    exact Subring.mul_mem _ (natCast_mem K0 _) (hcl.sub_mem _)
  · refine Subring.prod_mem _ fun i _ => hcl.pow_mul_mem _ ?_
    rw [Finsupp.tsub_apply]
    exact Nat.dvd_sub (hd i) (hj i)

omit [Fintype σ] [DecidableEq σ] in
theorem IsClassPart.inv_pow_mem (hcl : IsClassPart p K0 cl) (M : K) {n : ℕ} (hn : p ∣ n) :
    (M ^ n)⁻¹ ∈ K0 := by
  rw [← inv_pow]
  exact hcl.pow_mul_mem _ hn

/-- Lemma 3.19.2, part 2: `cl g^{(m)}(Δ / M) = M^{-p} cl g(φ + Δ)`. -/
theorem cl_eval_restart (hcl : IsClassPart p K0 cl) (φ Δ : σ → K) {M : K} (hM : M ≠ 0)
    (g : MvPolynomial σ K) :
    cl (eval (fun l => Δ l / M) (restart p cl φ M g)) = (M ^ p)⁻¹ * cl (eval (φ + Δ) g) := by
  have h := eval_hasse_restart p cl φ Δ hM g 0
  rw [hasse_zero, hasse_zero, hasse_zero] at h
  have hq := eval_hasse_removed_mem hcl (chart φ M g) (j := 0) (fun _ => dvd_zero p)
    (fun l => Δ l / M)
  rw [hasse_zero] at hq
  rw [h, hcl.map_mul _ (hcl.inv_pow_mem M (dvd_refl p)), map_sub, hcl.map_eq_zero _ hq,
    sub_zero]
  simp [ord]

/-- Lemma 3.19.2, part 3, the identity (19.1) for each order `j`:
`(g^{(m)})^{[j]}(Δ / M) = M^{|j| - p} Σ_k (Π_i C(k_i, j_i)) [g^{[k]}(φ)]' Δ^{k - j}`. -/
theorem eval_hasse_restart_eq_sum (hcl : IsClassPart p K0 cl) (φ Δ : σ → K) {M : K}
    (hM : M ≠ 0) (g : MvPolynomial σ K) {N : ℕ} (hN : ∀ i, degreeOf i g ≤ N) (j : σ →₀ ℕ) :
    eval (fun l => Δ l / M) (hasse j (restart p cl φ M g)) =
      M ^ ((ord j : ℤ) - p) * ∑ k ∈ box σ N, ((∏ i, (k i).choose (j i) : ℕ) : K) *
        clCoeff p cl k (eval φ (hasse k g)) * ∏ i, Δ i ^ (k i - j i) := by
  -- the coefficients of `g^{(m)}`
  have hcoeff : ∀ k, (restart p cl φ M g).coeff k =
      (M ^ p)⁻¹ * (M ^ ord k * clCoeff p cl k (eval φ (hasse k g))) := by
    intro k
    rw [restart, coeff_C_mul, coeff_clean, coeff_chart]
    congr 1
    unfold clCoeff
    split_ifs with hk
    · exact hcl.map_mul _ (hcl.pow_mul_mem M (Finset.dvd_sum fun i _ => hk i)) _
    · rfl
  have hsupp : (restart p cl φ M g).support ⊆ box σ N := by
    intro k hk
    rw [mem_box]
    intro i
    by_contra hi
    rw [MvPolynomial.mem_support_iff, hcoeff, hasse_eq_zero_of_lt hN (not_le.mp hi), map_zero,
      clCoeff_zero, mul_zero, mul_zero] at hk
    exact hk rfl
  -- the derivative as a sum over the coefficients
  rw [hasse, map_sum, Finset.sum_subset hsupp, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _), nsmul_eq_mul, hcoeff]
    simp only [Finsupp.tsub_apply]
    by_cases hjk : j ≤ k
    · have hsum : ∑ i, (k i - j i) + ord j = ord k := by
        rw [ord, ord, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        have := Finsupp.le_def.mp hjk i
        omega
      have hpow : ∏ i, (Δ i / M) ^ (k i - j i) =
          (∏ i, Δ i ^ (k i - j i)) / M ^ (∑ i, (k i - j i)) := by
        simp_rw [div_pow]
        rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
      rw [hpow, ← hsum, zpow_sub₀ hM, zpow_natCast, zpow_natCast, pow_add]
      field_simp
    · obtain ⟨i, hi⟩ : ∃ i, k i < j i := by
        by_contra hc
        push Not at hc
        exact hjk (Finsupp.le_def.mpr hc)
      have h0 : ∏ l, (k l).choose (j l) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (Nat.choose_eq_zero_of_lt hi)
      rw [h0]
      simp
  · intro k _ hk
    rw [MvPolynomial.notMem_support_iff.mp hk]
    simp

/-- Lemma 3.19.2, part 3, the identity (19.1) for the order `p^e` in the variable `i`, with the
factor `M^{p^e - p}`. -/
theorem eval_hasse_pow_restart_eq_sum (hcl : IsClassPart p K0 cl) (φ Δ : σ → K) {M : K}
    (hM : M ≠ 0) (g : MvPolynomial σ K) {N : ℕ} (hN : ∀ i, degreeOf i g ≤ N) (i : σ) (e : ℕ) :
    eval (fun l => Δ l / M) (hasse (single i (p ^ e)) (restart p cl φ M g)) =
      M ^ (((p ^ e : ℕ) : ℤ) - p) * ∑ k ∈ box σ N, (((k i).choose (p ^ e) : ℕ) : K) *
        clCoeff p cl k (eval φ (hasse k g)) * ∏ l, Δ l ^ (k l - single i (p ^ e) l) := by
  have hord : ord (single i (p ^ e) : σ →₀ ℕ) = p ^ e := by
    simp [ord, single_apply]
  rw [eval_hasse_restart_eq_sum hcl φ Δ hM g hN, hord]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 3
  rw [Finset.prod_eq_single i]
  · simp
  · intro l _ hl
    simp [Ne.symm hl]
  · simp

/-- Corollary 3.19.3, part 2: if `p ∣ j_i` for each `i`, then
`M^{p - |j|} (g^{(m)})^{[j]}(Δ / M) - g^{[j]}(φ + Δ)` has only terms of class `0`. -/
theorem restart_sub_mem (hcl : IsClassPart p K0 cl) (φ Δ : σ → K) {M : K} (hM : M ≠ 0)
    (g : MvPolynomial σ K) {j : σ →₀ ℕ} (hj : ∀ i, p ∣ j i) :
    M ^ ((p : ℤ) - ord j) * eval (fun l => Δ l / M) (hasse j (restart p cl φ M g)) -
      eval (φ + Δ) (hasse j g) ∈ K0 := by
  rw [eval_hasse_restart p cl φ Δ hM]
  have hq := eval_hasse_removed_mem hcl (chart φ M g) hj (fun l => Δ l / M)
  set q := eval (fun l => Δ l / M) (hasse j (removed p cl (chart φ M g)))
  have hdiv : p ∣ ord j := Finset.dvd_sum fun i _ => hj i
  have hMj : M ^ ord j ≠ 0 := pow_ne_zero _ hM
  have hMp : M ^ p ≠ 0 := pow_ne_zero _ hM
  have heq : M ^ ((p : ℤ) - ord j) * ((M ^ p)⁻¹ * (M ^ ord j * eval (φ + Δ) (hasse j g) - q)) -
      eval (φ + Δ) (hasse j g) = -((M ^ ord j)⁻¹ * q) := by
    rw [zpow_sub₀ hM, zpow_natCast, zpow_natCast]
    field_simp
    ring
  rw [heq]
  exact Subring.neg_mem _ (Subring.mul_mem _ (hcl.inv_pow_mem M hdiv) hq)

omit [DecidableEq σ] in
theorem clean_eq_sub_removed (p : ℕ) (cl : K →+ K) (h : MvPolynomial σ K) :
    clean p cl h = h - removed p cl h := by
  rw [removed, sub_sub_cancel]

/-- Lemma 3.17.1, part 3: the coefficient of `X^k` in `g_m = cl(g̃_m)` is `A_k = M^{|k|} g^{[k]}(φ)`
if some `k_i` is not divisible by `p`, and `cl A_k` otherwise. -/
theorem coeff_clean_chart (p : ℕ) (cl : K →+ K) (φ : σ → K) (M : K) (g : MvPolynomial σ K)
    (k : σ →₀ ℕ) :
    (clean p cl (chart φ M g)).coeff k = clCoeff p cl k (M ^ ord k * eval φ (hasse k g)) := by
  rw [coeff_clean, coeff_chart]

/-- Lemma 3.17.1, part 4: in characteristic `p`, `∂_{X_i} g_m = M g_{X_i}(φ + M X)`. -/
theorem hasse_single_clean_chart {p : ℕ} [CharP K p] (cl : K →+ K) (φ : σ → K) (M : K)
    (g : MvPolynomial σ K) (i : σ) :
    hasse (single i 1) (clean p cl (chart φ M g)) =
      C M * chart φ M (hasse (single i 1) g) := by
  have hord : ord (single i 1 : σ →₀ ℕ) = 1 := by
    simp [ord, single_apply]
  rw [clean_eq_sub_removed, hasse_sub, hasse_single_removed, sub_zero, hasse_chart, hord, pow_one]

theorem map_zpow_one_sub (v : AddValuation K (WithTop ℝ)) {M : K} (hM : M ≠ 0) {r : ℝ}
    (hr : v M = r) (p : ℕ) : v (M ^ (1 - p : ℤ)) = (((1 - p : ℝ) * r : ℝ) : WithTop ℝ) := by
  rw [zpow_sub₀ hM, zpow_one, zpow_natCast, AddValuation.map_div, AddValuation.map_pow, hr,
    ← WithTop.coe_nsmul, ← WithTop.LinearOrderedAddCommGroup.coe_sub, nsmul_eq_mul]
  congr 1
  ring

theorem map_inv_pow (v : AddValuation K (WithTop ℝ)) {M : K} {r : ℝ} (hr : v M = r) (p : ℕ) :
    v (M ^ p)⁻¹ = ((-((p : ℝ) * r) : ℝ) : WithTop ℝ) := by
  rw [AddValuation.map_inv, AddValuation.map_pow, hr, ← WithTop.coe_nsmul, nsmul_eq_mul]
  rfl

/-- Corollary 3.19.3, part 1: `Λ^{(m)}_0 + p v(M_m) = Λ_0`, for each first derivative. Here
`v(M) = r`, so `δ_m = Θ - r`. -/
theorem map_hasse_single_restart_add {p : ℕ} [CharP K p] (v : AddValuation K (WithTop ℝ))
    (cl : K →+ K) (φ Δ : σ → K) {M : K} (hM : M ≠ 0) {r : ℝ} (hr : v M = r) (Θ : ℝ)
    (g : MvPolynomial σ K) (i : σ) :
    v (eval (fun l => Δ l / M) (hasse (single i 1) (restart p cl φ M g))) +
        ((Θ - r + p * r : ℝ) : WithTop ℝ) =
      v (eval (φ + Δ) (hasse (single i 1) g)) + (Θ : WithTop ℝ) := by
  rw [eval_hasse_single_restart cl φ Δ hM, AddValuation.map_mul, map_zpow_one_sub v hM hr,
    add_comm (((1 - p : ℝ) * r : ℝ) : WithTop ℝ), add_assoc, ← WithTop.coe_add]
  congr 2
  ring

/-- Corollary 3.19.3, part 3: `v(cl g^{(m)}(Δ / M)) + p v(M) = v(cl g(φ + Δ))`. -/
theorem map_cl_eval_restart_add {p : ℕ} {K0 : Subring K} {cl : K →+ K}
    (hcl : IsClassPart p K0 cl) (v : AddValuation K (WithTop ℝ)) (φ Δ : σ → K) {M : K}
    (hM : M ≠ 0) {r : ℝ} (hr : v M = r) (g : MvPolynomial σ K) :
    v (cl (eval (fun l => Δ l / M) (restart p cl φ M g))) + (((p : ℝ) * r : ℝ) : WithTop ℝ) =
      v (cl (eval (φ + Δ) g)) := by
  rw [cl_eval_restart hcl φ Δ hM, AddValuation.map_mul, map_inv_pow v hr,
    add_comm (((-((p : ℝ) * r)) : ℝ) : WithTop ℝ), add_assoc, ← WithTop.coe_add, neg_add_cancel,
    WithTop.coe_zero, add_zero]

end Restart

section Degree

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]
variable {p : ℕ} {K0 : Subring K} {cl : K →+ K}

omit [DecidableEq σ] in
theorem ord_eq_degree (k : σ →₀ ℕ) : ord k = degree k := by
  rw [ord, degree_apply]
  exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
    simpa using hi).symm

/-- The condition that `g` is clean: each coefficient of a monomial `X^k` with `p ∣ k_i` for
each `i` has only terms of nonzero class. -/
def IsClean (p : ℕ) (cl : K →+ K) (g : MvPolynomial σ K) : Prop :=
  ∀ k : σ →₀ ℕ, (∀ i, p ∣ k i) → cl (g.coeff k) = g.coeff k

theorem hasse_eq_zero_of_totalDegree_lt {g : MvPolynomial σ K} {k : σ →₀ ℕ}
    (h : g.totalDegree < ord k) : hasse k g = 0 := by
  ext m
  rw [ord_eq_degree] at h
  rw [coeff_hasse_eq_zero_of_totalDegree_lt (by omega)]
  simp

theorem hasse_eq_C_of_totalDegree_eq {g : MvPolynomial σ K} {k : σ →₀ ℕ}
    (h : ord k = g.totalDegree) : hasse k g = C (g.coeff k) := by
  ext m
  rw [coeff_C]
  split_ifs with hm
  · subst hm
    exact coeff_zero_hasse k g
  · apply coeff_hasse_eq_zero_of_totalDegree_lt
    rw [ord_eq_degree] at h
    have : degree m ≠ 0 := fun h0 => hm ((degree_eq_zero_iff m).mp h0).symm
    omega

theorem coeff_restart (p : ℕ) (cl : K →+ K) (φ : σ → K) (M : K) (g : MvPolynomial σ K)
    (k : σ →₀ ℕ) :
    (restart p cl φ M g).coeff k =
      (M ^ p)⁻¹ * clCoeff p cl k (M ^ ord k * eval φ (hasse k g)) := by
  rw [restart, coeff_C_mul, coeff_clean_chart]

/-- Lemma 3.19.1, part 3: for a clean `g`, the function `g^{(m)}` of `P_m` has the same degree
as `g`. -/
theorem totalDegree_restart (hcl : IsClassPart p K0 cl) (φ : σ → K) {M : K} (hM : M ≠ 0)
    {g : MvPolynomial σ K} (hg : IsClean p cl g) :
    (restart p cl φ M g).totalDegree = g.totalDegree := by
  apply le_antisymm
  · rw [totalDegree]
    refine Finset.sup_le fun k hk => ?_
    rw [MvPolynomial.mem_support_iff, coeff_restart] at hk
    by_contra hlt
    have hlt' : g.totalDegree < ord k := by
      rw [ord_eq_degree, degree_apply]
      exact lt_of_not_ge hlt
    rw [hasse_eq_zero_of_totalDegree_lt hlt', map_zero, mul_zero, clCoeff_zero, mul_zero] at hk
    exact hk rfl
  · rcases eq_or_ne g 0 with h0 | h0
    · simp [h0]
    obtain ⟨k, hk, hkmax⟩ := Finset.exists_mem_eq_sup g.support (support_nonempty.mpr h0)
      fun s => s.sum fun _ e => e
    have hD : ord k = g.totalDegree := by
      rw [totalDegree, hkmax, ord_eq_degree, degree_apply]
      rfl
    have hc : (restart p cl φ M g).coeff k ≠ 0 := by
      rw [coeff_restart, hasse_eq_C_of_totalDegree_eq hD, eval_C]
      have hgk : g.coeff k ≠ 0 := MvPolynomial.mem_support_iff.mp hk
      refine mul_ne_zero (inv_ne_zero (pow_ne_zero _ hM)) ?_
      rw [clCoeff]
      split_ifs with hdiv
      · have hmem : M ^ ord k ∈ K0 := hcl.pow_mul_mem M (Finset.dvd_sum fun i _ => hdiv i)
        rw [hcl.map_mul _ hmem, hg k hdiv]
        exact mul_ne_zero (pow_ne_zero _ hM) hgk
      · exact mul_ne_zero (pow_ne_zero _ hM) hgk
    have := le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
    rw [← hD, ord_eq_degree]
    simpa [Finsupp.sum, degree_apply] using this

end Degree

end PlanarRuns

end Singularity
