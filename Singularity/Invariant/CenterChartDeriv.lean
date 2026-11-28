/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib

/-!
# Derivatives in a chart of a blowup

This file proves Volume 2, Lemma 2.2.6 of the handbook for polynomial rings.

Let `R` be a commutative ring and let `σ` be a finite index type. The center `Z` is given by a
finset `S` of variables, with ideal `I_Z = (x_i : i ∈ S)`. Fix `c ∈ S`. The chart map
`chartSubst S c` is the algebra map `x_i ↦ y_i y_c` for `i ∈ S`, `i ≠ c`, and `x_i ↦ y_i`
otherwise. The handbook indices `i < c` correspond to `i ∈ S.erase c`, and `i > c` to `i ∉ S`.

* `Singularity.pderiv_aeval_eq_sum`: the chain rule for a substitution,
  `∂_j (φ f) = ∑ i, φ(∂_i f) ∂_j (φ x_i)`.
* `Singularity.pderiv_mem_pow_of_mem_pow_succ`: a derivation maps `I^(n+1)` into `I^n`.
* `Singularity.exists_chartSubst_eq_X_pow_mul`: for `f ∈ I_Z^m` there is `g` with
  `π f = y_c^m g`.
* `Singularity.chartSubst_pderiv_of_mem_erase`, `chartSubst_pderiv_of_not_mem`,
  `chartSubst_pderiv_center`: the three formulas of Lemma 2.2.6, in the form
  `π(∂_i f) = y_c^(m-1) * (expression)`, with `m = n + 1`.
* `Singularity.chartSubst_eq_X_pow_mul_X_mul`: `π f = y_c^(m-1) (y_c g)`.

The case `i ∈ S.erase c` cancels a factor `y_c` and assumes `R` is a domain. The other cases
hold over any commutative ring. The membership `∂_i f ∈ I_Z^(m-1)` holds for any ideal.
The file treats the algebraic chart of affine space. Local coordinates on a smooth variety
(the étale reduction of Lemma 2.2.2) are not formalized.
-/

open MvPolynomial

namespace Singularity

variable {σ R : Type*} [CommRing R]

/-- The chain rule for a substitution of polynomials:
`∂_j (φ f) = ∑ i, φ(∂_i f) * ∂_j (φ x_i)`. -/
theorem pderiv_aeval_eq_sum [Fintype σ] (φ : σ → MvPolynomial σ R) (j : σ)
    (f : MvPolynomial σ R) :
    pderiv j (aeval φ f) = ∑ i, aeval φ (pderiv i f) * pderiv j (φ i) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq]
    simp only [map_add, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hp, pderiv_X, map_add,
      add_mul, Finset.sum_add_distrib, Pi.single_apply]
    simp [Finset.mul_sum, mul_comm, mul_left_comm]

/-- A derivation maps `I^(n+1)` into `I^n`. -/
theorem pderiv_mem_pow_of_mem_pow_succ (I : Ideal (MvPolynomial σ R)) (i : σ) (n : ℕ)
    {f : MvPolynomial σ R} (hf : f ∈ I ^ (n + 1)) : pderiv i f ∈ I ^ n := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ ?_ ?_
      · exact Ideal.mul_mem_right _ _ ha
      · rw [pow_succ']
        exact Ideal.mul_mem_mul hb (ih ha)
    · intro a b ha hb
      rw [map_add]
      exact Ideal.add_mem _ ha hb

variable [DecidableEq σ]

/-- The images of the variables under the chart map: `x_i ↦ y_i y_c` for `i ∈ S`, `i ≠ c`,
and `x_i ↦ y_i` otherwise. -/
noncomputable def chartImage (S : Finset σ) (c : σ) (i : σ) : MvPolynomial σ R :=
  if i ∈ S.erase c then X i * X c else X i

/-- The chart map of the blowup of `(x_i : i ∈ S)` in the `x_c`-chart. -/
noncomputable def chartSubst (S : Finset σ) (c : σ) :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval (chartImage S c)

/-- The ideal `(x_i : i ∈ S)` of the center. -/
noncomputable def chartCenterIdeal (S : Finset σ) : Ideal (MvPolynomial σ R) :=
  Ideal.span (X '' (S : Set σ))

theorem chartSubst_X (S : Finset σ) (c i : σ) :
    chartSubst S c (X i : MvPolynomial σ R) = chartImage S c i := by
  simp [chartSubst]

/-- For `f ∈ I_Z^m` the image `π f` is divisible by `y_c^m`. -/
theorem exists_chartSubst_eq_X_pow_mul {S : Finset σ} {c : σ} {m : ℕ}
    {f : MvPolynomial σ R} (hf : f ∈ chartCenterIdeal S ^ m) :
    ∃ g, chartSubst S c f = X c ^ m * g := by
  have hle : (chartCenterIdeal S).map (chartSubst S c : MvPolynomial σ R →ₐ[R] _) ≤
      Ideal.span {X c} := by
    rw [chartCenterIdeal, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    simp only [chartSubst_X, chartImage]
    split_ifs with h
    · exact Dvd.intro_left _ rfl
    · have : i = c := by
        by_contra hne
        exact h (Finset.mem_erase.mpr ⟨hne, hi⟩)
      rw [this]
  have hmap : chartSubst S c f ∈ (Ideal.span {(X c : MvPolynomial σ R)}) ^ m := by
    have := Ideal.mem_map_of_mem (chartSubst S c : MvPolynomial σ R →ₐ[R] _) hf
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hle m this
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmap
  obtain ⟨g, hg⟩ := hmap
  exact ⟨g, hg⟩

/-- The partial derivatives of the chart images. -/
theorem pderiv_chartImage (S : Finset σ) (c j i : σ) :
    pderiv j (chartImage (R := R) S c i) =
      (if i ∈ S.erase c then (if j = i then X c else 0) + (if j = c then X i else 0)
        else if j = i then 1 else 0) := by
  unfold chartImage
  split_ifs <;> simp_all [Derivation.leibniz, pderiv_X, Pi.single_apply, eq_comm]

variable [Fintype σ]

/-- The chain rule in the chart for `j ∈ S`, `j ≠ c`: `∂_{y_j} (π f) = y_c π(∂_j f)`. -/
theorem pderiv_chartSubst_of_mem_erase {S : Finset σ} {c j : σ} (hj : j ∈ S.erase c)
    (f : MvPolynomial σ R) :
    pderiv j (chartSubst S c f) = chartSubst S c (pderiv j f) * X c := by
  have hjc : j ≠ c := Finset.ne_of_mem_erase hj
  rw [chartSubst, pderiv_aeval_eq_sum, Finset.sum_eq_single j]
  · rw [pderiv_chartImage]
    simp [hj, hjc]
  · intro i _ hij
    rw [pderiv_chartImage]
    split_ifs <;> simp_all
  · simp

/-- The chain rule in the chart for `j ∉ S`: `∂_{y_j} (π f) = π(∂_j f)`. -/
theorem pderiv_chartSubst_of_not_mem {S : Finset σ} {c j : σ} (hc : c ∈ S) (hj : j ∉ S)
    (f : MvPolynomial σ R) :
    pderiv j (chartSubst S c f) = chartSubst S c (pderiv j f) := by
  have hjc : j ≠ c := fun h => hj (h ▸ hc)
  rw [chartSubst, pderiv_aeval_eq_sum, Finset.sum_eq_single j]
  · rw [pderiv_chartImage]
    have hj' : j ∉ S.erase c := fun h => hj (Finset.mem_of_mem_erase h)
    simp [hj']
  · intro i _ hij
    rw [pderiv_chartImage]
    split_ifs <;> simp_all
  · simp

/-- The chain rule in the chart for `y_c`:
`∂_{y_c} (π f) = π(∂_c f) + ∑_{l ∈ S, l ≠ c} y_l π(∂_l f)`. -/
theorem pderiv_chartSubst_center (S : Finset σ) (c : σ) (f : MvPolynomial σ R) :
    pderiv c (chartSubst S c f) =
      chartSubst S c (pderiv c f) + ∑ l ∈ S.erase c, X l * chartSubst S c (pderiv l f) := by
  rw [chartSubst, pderiv_aeval_eq_sum]
  have hterm : ∀ i, aeval (chartImage S c) (pderiv i f) * pderiv c (chartImage (R := R) S c i)
      = (if i = c then aeval (chartImage S c) (pderiv c f) else 0) +
        (if i ∈ S.erase c then X i * aeval (chartImage S c) (pderiv i f) else 0) := by
    intro i
    rw [pderiv_chartImage]
    by_cases hi : i ∈ S.erase c
    · have hic : i ≠ c := Finset.ne_of_mem_erase hi
      simp [hi, hic, Ne.symm hic, mul_comm]
    · by_cases hic : i = c
      · subst hic; simp [hi]
      · simp [hi, hic, Ne.symm hic]
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_filter]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext; simp

omit [DecidableEq σ] [Fintype σ] in
/-- Volume 2, Lemma 2.2.6 of the handbook, the membership: for `f ∈ I_Z^(n+1)` and any `i`,
`∂_i f ∈ I_Z^n`. -/
theorem pderiv_mem_centerIdeal_pow (S : Finset σ) (i : σ) {n : ℕ} {f : MvPolynomial σ R}
    (hf : f ∈ chartCenterIdeal S ^ (n + 1)) : pderiv i f ∈ chartCenterIdeal S ^ n :=
  pderiv_mem_pow_of_mem_pow_succ _ i n hf

omit [Fintype σ] in
/-- Lemma 2.2.6, the formula `y_c^(-(m-1)) π f = y_c g`, with `m = n + 1`. -/
theorem chartSubst_eq_X_pow_mul_X_mul {S : Finset σ} {c : σ} {n : ℕ}
    {f g : MvPolynomial σ R} (hg : chartSubst S c f = X c ^ (n + 1) * g) :
    chartSubst S c f = X c ^ n * (X c * g) := by
  rw [hg, pow_succ, mul_assoc]

/-- Volume 2, Lemma 2.2.6 of the handbook, the case `i > c` (here `i ∉ S`): if
`π f = y_c^(n+1) g`, then `π(∂_i f) = y_c^n (y_c ∂_{y_i} g)`. -/
theorem chartSubst_pderiv_of_not_mem {S : Finset σ} {c i : σ} (hc : c ∈ S) (hi : i ∉ S)
    {n : ℕ} {f g : MvPolynomial σ R} (hg : chartSubst S c f = X c ^ (n + 1) * g) :
    chartSubst S c (pderiv i f) = X c ^ n * (X c * pderiv i g) := by
  have hic : i ≠ c := fun h => hi (h ▸ hc)
  rw [← pderiv_chartSubst_of_not_mem hc hi, hg, Derivation.leibniz, pderiv_pow,
    pderiv_X_of_ne (Ne.symm hic)]
  simp only [smul_eq_mul, mul_zero, add_zero]
  ring

/-- Volume 2, Lemma 2.2.6 of the handbook, the case `i < c` (here `i ∈ S`, `i ≠ c`): if
`π f = y_c^(n+1) g`, then `π(∂_i f) = y_c^n ∂_{y_i} g`. -/
theorem chartSubst_pderiv_of_mem_erase [IsDomain R] {S : Finset σ} {c i : σ}
    (hi : i ∈ S.erase c) {n : ℕ} {f g : MvPolynomial σ R}
    (hg : chartSubst S c f = X c ^ (n + 1) * g) :
    chartSubst S c (pderiv i f) = X c ^ n * pderiv i g := by
  have hic : i ≠ c := Finset.ne_of_mem_erase hi
  have h := pderiv_chartSubst_of_mem_erase hi f
  rw [hg, Derivation.leibniz, pderiv_pow, pderiv_X_of_ne (Ne.symm hic)] at h
  simp only [smul_eq_mul, mul_zero, add_zero] at h
  apply mul_right_cancel₀ (X_ne_zero c : (X c : MvPolynomial σ R) ≠ 0)
  rw [← h]
  ring

/-- Volume 2, Lemma 2.2.6 of the handbook, the case `i = c`: if `π f = y_c^(n+1) g`, then
`π(∂_c f) = y_c^n ((n+1) g + y_c ∂_{y_c} g - ∑_{l ∈ S, l ≠ c} y_l ∂_{y_l} g)`. -/
theorem chartSubst_pderiv_center [IsDomain R] {S : Finset σ} {c : σ} {n : ℕ}
    {f g : MvPolynomial σ R} (hg : chartSubst S c f = X c ^ (n + 1) * g) :
    chartSubst S c (pderiv c f) = X c ^ n * (((n + 1 : ℕ) : MvPolynomial σ R) * g +
      X c * pderiv c g - ∑ l ∈ S.erase c, X l * pderiv l g) := by
  have h := pderiv_chartSubst_center S c f
  have hsum : ∑ l ∈ S.erase c, X l * chartSubst S c (pderiv l f) =
      X c ^ n * ∑ l ∈ S.erase c, X l * pderiv l g := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [chartSubst_pderiv_of_mem_erase hl hg]
    ring
  rw [hsum, hg, Derivation.leibniz, pderiv_pow, pderiv_X_self] at h
  simp only [smul_eq_mul, mul_one] at h
  rw [eq_sub_of_add_eq h.symm]
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

end Singularity
