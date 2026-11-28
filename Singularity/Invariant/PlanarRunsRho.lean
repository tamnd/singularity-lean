/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.PlanarRunsFrobenius

/-!
# The points of a corner run in four variables and the invariant `ρ` in the Hahn model

This file models the steps of a corner run in four variables of Section 3.17 of Volume 7 of the
handbook in the Hahn model of `PlanarRunsHahn`, and defines `ρ` (Definition 3.1.3) at the points
`P_m`.

## The model

* The free coordinates are the variables of `MvPolynomial σ 𝕂` (for the run of Section 3.17,
  `σ = Fin 2` and the variables are `x_m, w_m`). The coordinates `y_m, z_m` of the divisor are
  not variables: they are the monomials of the Hahn field `𝕂 = HahnSeries (CornerExp θ) k`, with
  the exponents `expY w m` and `expZ w m` in the exponents of `y_N, z_N`.
* One step from `P_m` is the chart `x_m = L_m (x_{m+1} + a_m)` for each free coordinate, followed
  by the factor `L_m^{-p}` and the cleaning. This is `restart p cl (fun i => a_m i * L_m) L_m` of
  `PlanarRunsRestart`. The chart in `y_m, z_m` is the change of the basis of the exponents, from
  `(expY w m, expZ w m)` to `(expY w (m + 1), expZ w (m + 1))`.
* `runFn p cl L a g m` is the function of `P_m`, the formula `M_m^{-p} cl g(φ_m + M_m X)` of
  Lemma 3.17.1. `runFn_succ` says that it is the function given by `m` single steps, so the
  formula and the step by step definition agree. `cornerRunFn` is the run of the Hahn model, with
  the cleaning `hahnCl p`.
* `coordY w m r` and `coordZ w m r` are the exponents of `y_m` and `z_m` in the monomial of
  exponent `r`. They exist since `det(y_m, z_m) = 1` (`det_expY_expZ`).
* `ordAt w m h` is the order of `h` at `P_m`: the least `|k| + a + b` over the terms
  `c y_m^a z_m^b X^k` of `h`. `IsRegularAt w m h` says that `a, b ≥ 0` for each term, that is,
  the coefficients of `h` are power series in `y_m, z_m`. For a regular `h` the order is the
  order at the point.
* `divY w m h` and `divZ w m h` are the exponents `r_y, r_z` of the monomial factor
  `y_m^{r_y} z_m^{r_z}` of `h`, and `resid w m h` is the residual factor `G`.
* `rhoAt w m h` is `ρ`: the least order at `P_m` of the generators `r_y G + y_m ∂_{y_m} G`,
  `r_z G + z_m ∂_{z_m} G` and `∂_{X_i} G` of the ideal `Θ̃(G)` of Definition 3.1.3. The
  logarithmic derivation `y_m ∂_{y_m}` multiplies the term of exponent `r` by `coordY w m r`.
* `KeepsRho` says that the run keeps a fixed `ρ ≥ 1`, with regular functions.

## What is not modeled

* The coordinates are fixed: the free coordinates are `x_m, w_m` and the divisor coordinates are
  the monomials `y_m, z_m`. A change of the free coordinates by series, as in Lemma 3.17.2, is not
  in the model, and `rhoAt` is not shown to be independent of the free coordinates.
* The order of the ideal `Θ̃(G)` in the power series ring is taken as the least order of its
  generators. This is the order of the ideal, since each element of the ideal is a combination of
  the generators with coefficients of order at least `0`, but the ideal is not built.
* The cleaning removes each term of class `0`, as in `PlanarRunsHahn`. This is the cleaning of the
  handbook for a perfect `k`.

## Main results

* `chart_chart` and `restart_restart`: two charts and two restarts compose.
* `runFn_succ` and `cornerRunFn_succ`: the function of `P_{m+1}` is the step from `P_m`.
* `coordY_succ` and `coordZ_succ`: the chart in `y_m, z_m`.
* `IsRegularAt.succ`: a function that is regular at `P_m` has regular coefficients at `P_{m+1}`.
* `rhoAt_eq_zero_of_unit_y` and `rhoAt_eq_zero_of_unit_z`: if `G` is a unit and `p ∤ r_y` or
  `p ∤ r_z`, then `ρ = 0`.

## References

* Volume 7, Sections 3.1 and 3.17 of the handbook: Definition 3.1.3, Lemma 3.17.1.
-/

open MvPolynomial Finsupp

namespace Singularity

namespace PlanarRuns

/-! ### Composition of the charts -/

section Compose

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

omit [Fintype σ] [DecidableEq σ] in
/-- Two charts compose: `g(φ + M (φ' + M' X)) = g((φ + M φ') + M M' X)`. -/
theorem chart_chart (φ φ' : σ → K) (M M' : K) (g : MvPolynomial σ K) :
    chart φ' M' (chart φ M g) = chart (fun i => φ i + M * φ' i) (M * M') g := by
  simp only [chart]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 1
  exact congrArg aeval (funext fun i => by
    simp only [map_add, map_mul, aeval_C, aeval_X, algebraMap_eq]
    ring)

omit [Fintype σ] [DecidableEq σ] in
theorem chart_C_mul (φ : σ → K) (M a : K) (f : MvPolynomial σ K) :
    chart φ M (C a * f) = C a * chart φ M f := by
  simp only [chart, map_mul, aeval_C, algebraMap_eq]

omit [Fintype σ] [DecidableEq σ] in
theorem chart_sub (φ : σ → K) (M : K) (f g : MvPolynomial σ K) :
    chart φ M (f - g) = chart φ M f - chart φ M g := by
  simp only [chart, map_sub]

omit [Fintype σ] [DecidableEq σ] in
theorem chart_zero_one (g : MvPolynomial σ K) : chart 0 1 g = g := by
  have h : (fun i => C ((0 : σ → K) i) + C 1 * X i : σ → MvPolynomial σ K) = X := by
    funext i
    simp
  rw [chart, h, aeval_X_left_apply]

variable {p : ℕ} {K0 : Subring K} {cl : K →+ K}

/-- The polynomials with only monomials `c X^k` with `p ∣ k_i` for each `i` and `c ∈ K0`. These
are the polynomials that the cleaning removes. -/
def powerForm (p : ℕ) (K0 : Subring K) : Subring (MvPolynomial σ K) where
  carrier := {h | ∀ k, h.coeff k ≠ 0 → (∀ i, p ∣ k i) ∧ h.coeff k ∈ K0}
  mul_mem' {f g} hf hg k hk := by
    rw [coeff_mul] at hk ⊢
    obtain ⟨⟨a, b⟩, hab, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
    have ha := hf a (left_ne_zero_of_mul hne)
    have hb := hg b (right_ne_zero_of_mul hne)
    have hab' : a + b = k := by simpa using hab
    refine ⟨fun i => ?_, Subring.sum_mem _ fun x _ => ?_⟩
    · rw [← hab', Finsupp.add_apply]
      exact dvd_add (ha.1 i) (hb.1 i)
    · by_cases h1 : f.coeff x.1 = 0
      · rw [h1, zero_mul]
        exact Subring.zero_mem _
      by_cases h2 : g.coeff x.2 = 0
      · rw [h2, mul_zero]
        exact Subring.zero_mem _
      exact Subring.mul_mem _ (hf _ h1).2 (hg _ h2).2
  one_mem' k hk := by
    rw [coeff_one] at hk ⊢
    split_ifs at hk ⊢ with h
    · exact ⟨fun i => by simp [← h], Subring.one_mem _⟩
    · exact absurd rfl hk
  add_mem' {f g} hf hg k hk := by
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hk ⊢
    by_cases h1 : f.coeff k = 0
    · rw [h1, zero_add] at hk ⊢
      exact hg k hk
    by_cases h2 : g.coeff k = 0
    · rw [h2, add_zero] at hk ⊢
      exact hf k hk
    exact ⟨(hf k h1).1, Subring.add_mem _ (hf k h1).2 (hg k h2).2⟩
  zero_mem' k hk := absurd (by simp) hk
  neg_mem' {f} hf k hk := by
    rw [coeff_neg, neg_ne_zero] at hk
    rw [coeff_neg]
    exact ⟨(hf k hk).1, Subring.neg_mem _ (hf k hk).2⟩

omit [Fintype σ] in
theorem mem_powerForm {h : MvPolynomial σ K} :
    h ∈ powerForm p K0 ↔ ∀ k, h.coeff k ≠ 0 → (∀ i, p ∣ k i) ∧ h.coeff k ∈ K0 := Iff.rfl

omit [Fintype σ] in
theorem C_mem_powerForm {a : K} (ha : a ∈ K0) : (C a : MvPolynomial σ K) ∈ powerForm p K0 := by
  intro k hk
  rw [coeff_C] at hk ⊢
  split_ifs at hk ⊢ with h
  · exact ⟨fun i => by simp [← h], ha⟩
  · exact absurd rfl hk

omit [Fintype σ] in
theorem X_pow_mem_powerForm (i : σ) : (X i ^ p : MvPolynomial σ K) ∈ powerForm p K0 := by
  intro k hk
  rw [X_pow_eq_monomial, coeff_monomial] at hk ⊢
  split_ifs at hk ⊢ with h
  · refine ⟨fun l => ?_, Subring.one_mem _⟩
    rw [← h, Finsupp.single_apply]
    split_ifs
    · exact dvd_refl p
    · exact dvd_zero p
  · exact absurd rfl hk

theorem removed_mem_powerForm (hcl : IsClassPart p K0 cl) (h : MvPolynomial σ K) :
    removed p cl h ∈ powerForm p K0 := by
  intro k hk
  obtain ⟨hdvd, heq⟩ := coeff_removed_ne_zero hk
  exact ⟨hdvd, heq ▸ hcl.sub_mem _⟩

theorem clean_eq_zero_of_mem (hcl : IsClassPart p K0 cl) {h : MvPolynomial σ K}
    (hh : h ∈ powerForm p K0) : clean p cl h = 0 := by
  ext k
  rw [coeff_clean, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_cases h0 : h.coeff k = 0
  · rw [h0, clCoeff_zero]
  · obtain ⟨hdvd, hmem⟩ := hh k h0
    rw [clCoeff, ite_eq_left_of_eq_true _ _ (eq_true hdvd)]
    exact hcl.map_eq_zero _ hmem

theorem clean_sub (p : ℕ) (cl : K →+ K) (f g : MvPolynomial σ K) :
    clean p cl (f - g) = clean p cl f - clean p cl g := by
  ext k
  rw [coeff_sub, coeff_clean, coeff_clean, coeff_clean, coeff_sub, clCoeff, clCoeff, clCoeff]
  split_ifs <;> simp

theorem clean_C_mul (hcl : IsClassPart p K0 cl) {a : K} (ha : a ∈ K0) (f : MvPolynomial σ K) :
    clean p cl (C a * f) = C a * clean p cl f := by
  ext k
  rw [coeff_C_mul, coeff_clean, coeff_clean, coeff_C_mul, clCoeff, clCoeff]
  split_ifs
  · exact hcl.map_mul a ha _
  · rfl

omit [Fintype σ] in
/-- A chart sends the polynomials that the cleaning removes to such polynomials, since
`(φ + M X)^p = φ^p + M^p X^p` in characteristic `p`. -/
theorem chart_mem_powerForm [CharP K p] (hp : p.Prime) (hcl : IsClassPart p K0 cl)
    (φ : σ → K) (M : K) {h : MvPolynomial σ K} (hh : h ∈ powerForm p K0) :
    chart φ M h ∈ powerForm p K0 := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (MvPolynomial σ K) p := charP_of_injective_algebraMap (C_injective σ K) p
  rw [as_sum h, chart, map_sum]
  refine Subring.sum_mem _ fun k hk => ?_
  have hk' := hh k (MvPolynomial.mem_support_iff.mp hk)
  rw [aeval_monomial, algebraMap_eq, Finsupp.prod]
  refine Subring.mul_mem _ (C_mem_powerForm hk'.2) (Subring.prod_mem _ fun i _ => ?_)
  obtain ⟨c, hc⟩ := hk'.1 i
  rw [hc, pow_mul, add_pow_char, mul_pow, ← C_pow, ← C_pow]
  refine Subring.pow_mem _ (Subring.add_mem _ (C_mem_powerForm (hcl.pow_mem _))
    (Subring.mul_mem _ (C_mem_powerForm (hcl.pow_mem _)) (X_pow_mem_powerForm i))) _

/-- The cleaning before a chart does not change the cleaning after it. -/
theorem clean_chart_clean [CharP K p] (hp : p.Prime) (hcl : IsClassPart p K0 cl) (φ : σ → K)
    (M : K) (h : MvPolynomial σ K) :
    clean p cl (chart φ M (clean p cl h)) = clean p cl (chart φ M h) := by
  rw [clean_eq_sub_removed p cl h, chart_sub, clean_sub,
    clean_eq_zero_of_mem hcl (chart_mem_powerForm hp hcl φ M (removed_mem_powerForm hcl h)),
    sub_zero]

/-- Two restarts compose: the restart at `φ', M'` of the restart at `φ, M` is the restart at
`φ + M φ', M M'`. -/
theorem restart_restart [CharP K p] (hp : p.Prime) (hcl : IsClassPart p K0 cl)
    (φ φ' : σ → K) (M M' : K) (g : MvPolynomial σ K) :
    restart p cl φ' M' (restart p cl φ M g) =
      restart p cl (fun i => φ i + M * φ' i) (M * M') g := by
  rw [restart, restart, chart_C_mul, clean_C_mul hcl (hcl.inv_pow_mem M (dvd_refl p)),
    clean_chart_clean hp hcl, chart_chart, restart, ← mul_assoc, ← C_mul, mul_pow, mul_inv,
    mul_comm (M' ^ p)⁻¹]

end Compose

/-! ### The points of a run -/

section Run

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

/-- The function of the point `P_m` of a run with the chart variables `L` and the translations
`a`: `M_m^{-p} cl g(φ_m + M_m X)` (Lemma 3.17.1). -/
noncomputable def runFn (p : ℕ) (cl : K →+ K) (L : ℕ → K) (a : ℕ → σ → K) (g : MvPolynomial σ K)
    (m : ℕ) : MvPolynomial σ K :=
  restart p cl (fun i => cornerSum L (fun j => a j i) m) (cornerMono L m) g

omit [DecidableEq σ] in
theorem runFn_zero (p : ℕ) (cl : K →+ K) (L : ℕ → K) (a : ℕ → σ → K) (g : MvPolynomial σ K) :
    runFn p cl L a g 0 = clean p cl g := by
  have h0 : (fun i => cornerSum L (fun j => a j i) 0) = 0 := rfl
  rw [runFn, restart, h0, cornerMono, chart_zero_one, one_pow, inv_one, C_1, one_mul]

/-- The function of `P_{m+1}` is the step from `P_m`: the chart `x_m = L_m (x_{m+1} + a_m)`,
the factor `L_m^{-p}` and the cleaning. -/
theorem runFn_succ {p : ℕ} [CharP K p] (hp : p.Prime) {K0 : Subring K} {cl : K →+ K}
    (hcl : IsClassPart p K0 cl) (L : ℕ → K) (a : ℕ → σ → K) (g : MvPolynomial σ K) (m : ℕ) :
    runFn p cl L a g (m + 1) =
      restart p cl (fun i => a m i * L m) (L m) (runFn p cl L a g m) := by
  rw [runFn, runFn, restart_restart hp hcl]
  congr 1
  funext i
  rw [cornerSum, cornerMono]
  ring

end Run

/-! ### The run of the Hahn model -/

section HahnRun

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {θ : ℝ} {k : Type*} [Field k]

/-- The function of `P_m` for the corner run of the Hahn model with the word `w` and the
translations `t`. -/
noncomputable def cornerRunFn (p : ℕ) (w : ℕ → Bool) (t : ℕ → σ → k)
    (g : MvPolynomial σ (HahnSeries (CornerExp θ) k)) (m : ℕ) :
    MvPolynomial σ (HahnSeries (CornerExp θ) k) :=
  runFn p (hahnCl p) (cornerL θ k w) (fun j i => HahnSeries.C (t j i)) g m

omit [DecidableEq σ] in
/-- The function of `P_m` is the formula of `conjectureP_cornerRun`. -/
theorem cornerRunFn_eq (p : ℕ) (w : ℕ → Bool) (t : ℕ → σ → k)
    (g : MvPolynomial σ (HahnSeries (CornerExp θ) k)) (m : ℕ) :
    cornerRunFn p w t g m =
      restart p (hahnCl p) (fun l => cornerPoint (w := w) t m l) (cornerM θ k w m) g := by
  rw [cornerRunFn, runFn, cornerMono_cornerL]
  rfl

/-- One step of the run of the Hahn model. -/
theorem cornerRunFn_succ {p : ℕ} [Fact p.Prime] [CharP k p] (w : ℕ → Bool) (t : ℕ → σ → k)
    (g : MvPolynomial σ (HahnSeries (CornerExp θ) k)) (m : ℕ) :
    cornerRunFn p w t g (m + 1) =
      restart p (hahnCl p) (fun i => HahnSeries.C (t m i) * cornerL θ k w m) (cornerL θ k w m)
        (cornerRunFn p w t g m) := by
  rw [cornerRunFn, cornerRunFn, runFn_succ (Fact.out : p.Prime) isClassPart_hahn]

end HahnRun

/-! ### The coordinates of the divisor at `P_m` -/

section Coordinates

variable {θ : ℝ}

open CornerExp

/-- The exponent of `y_m` in the monomial of exponent `r` at `P_m`. -/
def coordY (w : ℕ → Bool) (m : ℕ) (r : CornerExp θ) : ℤ :=
  fst r * snd (expZ w m : CornerExp θ) - snd r * fst (expZ w m : CornerExp θ)

/-- The exponent of `z_m` in the monomial of exponent `r` at `P_m`. -/
def coordZ (w : ℕ → Bool) (m : ℕ) (r : CornerExp θ) : ℤ :=
  fst (expY w m : CornerExp θ) * snd r - snd (expY w m : CornerExp θ) * fst r

/-- The exponent of the monomial `y_m^a z_m^b`. -/
def expAt (w : ℕ → Bool) (m : ℕ) (a b : ℤ) : CornerExp θ :=
  mk (a * fst (expY w m : CornerExp θ) + b * fst (expZ w m : CornerExp θ))
    (a * snd (expY w m : CornerExp θ) + b * snd (expZ w m : CornerExp θ))

theorem coordY_add (w : ℕ → Bool) (m : ℕ) (r s : CornerExp θ) :
    coordY w m (r + s) = coordY w m r + coordY w m s := by
  simp only [coordY, fst_add, snd_add]
  ring

theorem coordZ_add (w : ℕ → Bool) (m : ℕ) (r s : CornerExp θ) :
    coordZ w m (r + s) = coordZ w m r + coordZ w m s := by
  simp only [coordZ, fst_add, snd_add]
  ring

@[simp] theorem coordY_zero (w : ℕ → Bool) (m : ℕ) : coordY w m (0 : CornerExp θ) = 0 := by
  simp [coordY]

@[simp] theorem coordZ_zero (w : ℕ → Bool) (m : ℕ) : coordZ w m (0 : CornerExp θ) = 0 := by
  simp [coordZ]

@[simp] theorem coordY_expAt (w : ℕ → Bool) (m : ℕ) (a b : ℤ) :
    coordY w m (expAt (θ := θ) w m a b) = a := by
  have h := det_expY_expZ (θ := θ) w m
  simp only [coordY, expAt, fst_mk, snd_mk]
  linear_combination a * h

@[simp] theorem coordZ_expAt (w : ℕ → Bool) (m : ℕ) (a b : ℤ) :
    coordZ w m (expAt (θ := θ) w m a b) = b := by
  have h := det_expY_expZ (θ := θ) w m
  simp only [coordZ, expAt, fst_mk, snd_mk]
  linear_combination b * h

/-- Each exponent is the exponent of the monomial `y_m^a z_m^b` with `a = coordY w m r` and
`b = coordZ w m r`. -/
theorem expAt_coord (w : ℕ → Bool) (m : ℕ) (r : CornerExp θ) :
    expAt w m (coordY w m r) (coordZ w m r) = r := by
  have h := det_expY_expZ (θ := θ) w m
  refine ext ?_ ?_
  · simp only [expAt, coordY, coordZ, fst_mk]
    linear_combination (fst r) * h
  · simp only [expAt, coordY, coordZ, snd_mk]
    linear_combination (snd r) * h

theorem expAt_add (w : ℕ → Bool) (m : ℕ) (a b a' b' : ℤ) :
    (expAt w m (a + a') (b + b') : CornerExp θ) = expAt w m a b + expAt w m a' b' := by
  refine ext ?_ ?_ <;> simp only [expAt, fst_mk, snd_mk, fst_add, snd_add] <;> ring

/-- The chart in `y_m, z_m`: `y_m^a z_m^b = y_{m+1}^{a+b} z_{m+1}^b` in a `y`-step, and
`y_m^a z_m^b = y_{m+1}^a z_{m+1}^{a+b}` in a `z`-step. -/
theorem coordY_succ (w : ℕ → Bool) (m : ℕ) (r : CornerExp θ) :
    coordY w (m + 1) r =
      if w m then coordY w m r + coordZ w m r else coordY w m r := by
  simp only [coordY, coordZ, expZ_succ]
  split_ifs
  · simp only [fst_sub, snd_sub]
    ring
  · rfl

theorem coordZ_succ (w : ℕ → Bool) (m : ℕ) (r : CornerExp θ) :
    coordZ w (m + 1) r =
      if w m then coordZ w m r else coordY w m r + coordZ w m r := by
  simp only [coordY, coordZ, expY_succ]
  split_ifs
  · rfl
  · simp only [fst_sub, snd_sub]
    ring

/-- The chart variable `L_m` is `y_{m+1}` in a `y`-step and `z_{m+1}` in a `z`-step. -/
theorem coord_expL (w : ℕ → Bool) (m : ℕ) :
    coordY w (m + 1) (expL w m : CornerExp θ) = (if w m then 1 else 0) ∧
      coordZ w (m + 1) (expL w m : CornerExp θ) = (if w m then 0 else 1) := by
  have h := det_expY_expZ (θ := θ) w m
  have hy : coordY w m (expY w m : CornerExp θ) = 1 := by
    simp only [coordY]; linear_combination h
  have hz : coordZ w m (expZ w m : CornerExp θ) = 1 := by
    simp only [coordZ]; linear_combination h
  have hyz : coordZ w m (expY w m : CornerExp θ) = 0 := by simp only [coordZ]; ring
  have hzy : coordY w m (expZ w m : CornerExp θ) = 0 := by simp only [coordY]; ring
  rw [coordY_succ, coordZ_succ, expL]
  cases w m <;> simp [hy, hz, hyz, hzy]

end Coordinates

/-! ### The order at `P_m` and `ρ` -/

section Rho

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {θ : ℝ} {k : Type*} [Field k]

/-- The series with the coefficient `f r * x_r` at `r`. -/
noncomputable def weightMul (f : CornerExp θ → k) :
    HahnSeries (CornerExp θ) k →+ HahnSeries (CornerExp θ) k where
  toFun x :=
    { coeff := fun r => f r * x.coeff r
      isPWO_support' := x.isPWO_support.mono fun r hr => by
        simp only [Function.mem_support, ne_eq] at hr ⊢
        exact right_ne_zero_of_mul hr }
  map_zero' := by ext r; simp
  map_add' x y := by ext r; simp [mul_add]

@[simp] theorem coeff_weightMul (f : CornerExp θ → k) (x : HahnSeries (CornerExp θ) k)
    (r : CornerExp θ) : (weightMul f x).coeff r = f r * x.coeff r := rfl

/-- The logarithmic derivation `y_m ∂_{y_m}` of the Hahn field. -/
noncomputable def logDerY (w : ℕ → Bool) (m : ℕ) :
    HahnSeries (CornerExp θ) k →+ HahnSeries (CornerExp θ) k :=
  weightMul fun r => (coordY w m r : k)

/-- The logarithmic derivation `z_m ∂_{z_m}` of the Hahn field. -/
noncomputable def logDerZ (w : ℕ → Bool) (m : ℕ) :
    HahnSeries (CornerExp θ) k →+ HahnSeries (CornerExp θ) k :=
  weightMul fun r => (coordZ w m r : k)

variable {R : Type*} [CommRing R]

/-- An additive map applied to each coefficient. -/
noncomputable def mapCoeff (f : R →+ R) (h : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ k ∈ h.support, monomial k (f (h.coeff k))

omit [Fintype σ] in
@[simp] theorem coeff_mapCoeff (f : R →+ R) (h : MvPolynomial σ R) (k : σ →₀ ℕ) :
    (mapCoeff f h).coeff k = f (h.coeff k) := by
  simp only [mapCoeff, coeff_sum, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hk
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hk, map_zero]

/-- The coefficients of `h` are power series in `y_m, z_m`. -/
def IsRegularAt (w : ℕ → Bool) (m : ℕ) (h : MvPolynomial σ (HahnSeries (CornerExp θ) k)) :
    Prop :=
  ∀ q, ∀ r ∈ (h.coeff q).support, 0 ≤ coordY w m r ∧ 0 ≤ coordZ w m r

/-- The order of the term `c y_m^a z_m^b X^q`: `|q| + a + b`, as a natural number. -/
def termOrd (w : ℕ → Bool) (m : ℕ) (q : σ →₀ ℕ) (r : CornerExp θ) : ℕ :=
  ((ord q : ℤ) + coordY w m r + coordZ w m r).toNat

/-- The order of `h` at `P_m`: the least order of its terms. -/
noncomputable def ordAt (w : ℕ → Bool) (m : ℕ) (h : MvPolynomial σ (HahnSeries (CornerExp θ) k)) :
    ℕ∞ :=
  ⨅ q ∈ h.support, ⨅ r ∈ (h.coeff q).support, ((termOrd w m q r : ℕ) : ℕ∞)

/-- The exponent `r_y` of `y_m` in the monomial factor of `h`. -/
noncomputable def divY (w : ℕ → Bool) (m : ℕ) (h : MvPolynomial σ (HahnSeries (CornerExp θ) k)) :
    ℕ :=
  (⨅ q ∈ h.support, ⨅ r ∈ (h.coeff q).support, (((coordY w m r).toNat : ℕ) : ℕ∞)).toNat

/-- The exponent `r_z` of `z_m` in the monomial factor of `h`. -/
noncomputable def divZ (w : ℕ → Bool) (m : ℕ) (h : MvPolynomial σ (HahnSeries (CornerExp θ) k)) :
    ℕ :=
  (⨅ q ∈ h.support, ⨅ r ∈ (h.coeff q).support, (((coordZ w m r).toNat : ℕ) : ℕ∞)).toNat

/-- The residual factor `G = y_m^{-r_y} z_m^{-r_z} h`. -/
noncomputable def resid (w : ℕ → Bool) (m : ℕ) (h : MvPolynomial σ (HahnSeries (CornerExp θ) k)) :
    MvPolynomial σ (HahnSeries (CornerExp θ) k) :=
  C (HahnSeries.single (expAt w m (-(divY w m h : ℤ)) (-(divZ w m h : ℤ))) 1) * h

/-- The generator `r_y G + y_m ∂_{y_m} G` of `Θ̃(G)`. -/
noncomputable def logGenY (w : ℕ → Bool) (m : ℕ)
    (h : MvPolynomial σ (HahnSeries (CornerExp θ) k)) :
    MvPolynomial σ (HahnSeries (CornerExp θ) k) :=
  C (divY w m h : HahnSeries (CornerExp θ) k) * resid w m h + mapCoeff (logDerY w m) (resid w m h)

/-- The generator `r_z G + z_m ∂_{z_m} G` of `Θ̃(G)`. -/
noncomputable def logGenZ (w : ℕ → Bool) (m : ℕ)
    (h : MvPolynomial σ (HahnSeries (CornerExp θ) k)) :
    MvPolynomial σ (HahnSeries (CornerExp θ) k) :=
  C (divZ w m h : HahnSeries (CornerExp θ) k) * resid w m h + mapCoeff (logDerZ w m) (resid w m h)

/-- `ρ` at `P_m` (Definition 3.1.3): the least order at `P_m` of the generators
`r_y G + y_m ∂_{y_m} G`, `r_z G + z_m ∂_{z_m} G` and `∂_{X_i} G` of `Θ̃(G)`. -/
noncomputable def rhoAt (w : ℕ → Bool) (m : ℕ) (h : MvPolynomial σ (HahnSeries (CornerExp θ) k)) :
    ℕ∞ :=
  ordAt w m (logGenY w m h) ⊓ ordAt w m (logGenZ w m h) ⊓
    ⨅ i, ordAt w m (hasse (single i 1) (resid w m h))

omit [DecidableEq σ] in
theorem ordAt_le_termOrd {w : ℕ → Bool} {m : ℕ} {h : MvPolynomial σ (HahnSeries (CornerExp θ) k)}
    {q : σ →₀ ℕ} {r : CornerExp θ} (hr : (h.coeff q).coeff r ≠ 0) :
    ordAt w m h ≤ termOrd w m q r := by
  have hq : q ∈ h.support := by
    rw [MvPolynomial.mem_support_iff]
    rintro h0
    rw [h0, HahnSeries.coeff_zero] at hr
    exact hr rfl
  exact (iInf₂_le q hq).trans (iInf₂_le r hr)

omit [DecidableEq σ] in
@[simp] theorem termOrd_zero (w : ℕ → Bool) (m : ℕ) :
    termOrd (σ := σ) w m 0 (0 : CornerExp θ) = 0 := by
  simp [termOrd, ord]

/-- If the residual factor `G` is a unit, that is, its term of exponent `0` is not `0`, and
`p ∤ r_y`, then `ρ = 0`. -/
theorem rhoAt_eq_zero_of_unit_y {p : ℕ} [CharP k p] {w : ℕ → Bool} {m : ℕ}
    {h : MvPolynomial σ (HahnSeries (CornerExp θ) k)}
    (hG : ((resid w m h).coeff 0).coeff 0 ≠ 0) (hdiv : ¬ p ∣ divY w m h) :
    rhoAt w m h = 0 := by
  have hne : ((logGenY w m h).coeff 0).coeff 0 ≠ 0 := by
    rw [logGenY, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C_mul, coeff_mapCoeff,
      HahnSeries.coeff_add, logDerY, coeff_weightMul, coordY_zero, Int.cast_zero, zero_mul,
      add_zero, ← nsmul_eq_mul, HahnSeries.coeff_smul, nsmul_eq_mul]
    refine mul_ne_zero ?_ hG
    rwa [Ne, CharP.cast_eq_zero_iff k p]
  have h1 : ordAt w m _ ≤ termOrd w m 0 0 := ordAt_le_termOrd hne
  rw [termOrd_zero] at h1
  exact nonpos_iff_eq_zero.mp (inf_le_left.trans (inf_le_left.trans (by exact_mod_cast h1)))

/-- If the residual factor `G` is a unit and `p ∤ r_z`, then `ρ = 0`. -/
theorem rhoAt_eq_zero_of_unit_z {p : ℕ} [CharP k p] {w : ℕ → Bool} {m : ℕ}
    {h : MvPolynomial σ (HahnSeries (CornerExp θ) k)}
    (hG : ((resid w m h).coeff 0).coeff 0 ≠ 0) (hdiv : ¬ p ∣ divZ w m h) :
    rhoAt w m h = 0 := by
  have hne : ((logGenZ w m h).coeff 0).coeff 0 ≠ 0 := by
    rw [logGenZ, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C_mul, coeff_mapCoeff,
      HahnSeries.coeff_add, logDerZ, coeff_weightMul, coordZ_zero, Int.cast_zero, zero_mul,
      add_zero, ← nsmul_eq_mul, HahnSeries.coeff_smul, nsmul_eq_mul]
    refine mul_ne_zero ?_ hG
    rwa [Ne, CharP.cast_eq_zero_iff k p]
  have h1 : ordAt w m _ ≤ termOrd w m 0 0 := ordAt_le_termOrd hne
  rw [termOrd_zero] at h1
  exact nonpos_iff_eq_zero.mp (inf_le_left.trans (inf_le_right.trans (by exact_mod_cast h1)))

/-- The run keeps `ρ`: at each point `P_m` the function is regular and has `ρ = ρ₀`, with
`ρ₀ ≥ 1`. -/
structure KeepsRho (p : ℕ) (w : ℕ → Bool) (t : ℕ → σ → k)
    (g : MvPolynomial σ (HahnSeries (CornerExp θ) k)) (ρ₀ : ℕ∞) : Prop where
  one_le : 1 ≤ ρ₀
  regular : ∀ m, IsRegularAt w m (cornerRunFn p w t g m)
  rho_eq : ∀ m, rhoAt w m (cornerRunFn p w t g m) = ρ₀

omit [Fintype σ] [DecidableEq σ] in
/-- A function that is regular at `P_m` has coefficients that are regular at `P_{m+1}`. -/
theorem IsRegularAt.succ {w : ℕ → Bool} {m : ℕ} {h : MvPolynomial σ (HahnSeries (CornerExp θ) k)}
    (hh : IsRegularAt w m h) : IsRegularAt w (m + 1) h := by
  intro q r hr
  obtain ⟨h1, h2⟩ := hh q r hr
  rw [coordY_succ, coordZ_succ]
  split_ifs <;> constructor <;> omega

end Rho

end PlanarRuns

end Singularity
