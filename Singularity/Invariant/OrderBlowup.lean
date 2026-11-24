/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.Residual

/-!
# The order does not go up under a point blowup

Let `k` be a field and let `f` be a polynomial in `k[x_i : i ∈ σ]` with `ord f = m`. Look at the
`x_j`-chart of the blowup of the origin with translations `t`: `x_j ↦ x_j` and
`x_i ↦ x_j (x_i + t_i)` for `i ≠ j` (`pointChart j t`). Then the image of `f` is `x_j^m f'`, and
`ord f' ≤ m` [Hau03].

The proof. Each variable goes to `x_j` times its image under the substitution `ρ`: `x_j ↦ 1`,
`x_i ↦ x_i + t_i`. So a monomial `x^a` goes to `x_j^|a| ρ(x^a)`, and
`f' = ∑ x_j^(|a| - m) ρ(c_a x^a)` (`chartTransform`). The substitution `x_j ↦ 0` does not lower the
order, and it sends `f'` to `ρ(f_m)`, with `f_m` the part of `f` of degree `m`. The map `ρ` is the
substitution `x_j ↦ 1` followed by the translation `x_i ↦ x_i + t_i`. The substitution `x_j ↦ 1`
keeps `f_m ≠ 0`, because two monomials of the same degree that agree outside `x_j` are equal. The
translation is injective and does not raise the total degree. So `ρ(f_m)` is a nonzero polynomial
of total degree at most `m`, and its order is at most `m`.

## Main results

* `exists_pointChart_eq_X_pow_mul`: if `m ≤ ord f`, then `pointChart j t f = x_j^m f'` for a
  polynomial `f'`.
* `ord_le_of_pointChart`: if `ord f = m` and `pointChart j t f = x_j^m f'`, then `ord f' ≤ m`.
* `pointChart_ne_zero`, `pointChart_injective`, `ne_zero_of_pointChart_eq_X_pow_mul`: the chart is
  injective, so `f' ≠ 0` when `f ≠ 0`.

## References

* [Hau03] H. Hauser, *The Hironaka theorem on resolution of singularities*, Bull. AMS 40 (2003),
  Proposition 6.
-/

open MvPolynomial Finsupp

namespace Singularity

variable {σ k : Type*} [Field k] [DecidableEq σ]

/-- The substitution `x_j ↦ 1` and `x_i ↦ x_i + t_i` for `i ≠ j`. The chart of the blowup is
`x_i ↦ x_j · chartRest j t (x_i)` for each `i` (`pointChart_X_eq`). -/
noncomputable def chartRest (j : σ) (t : σ → k) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval fun i => if i = j then 1 else X i + C (t i)

/-- The translation `x_j ↦ x_j` and `x_i ↦ x_i + t_i` for `i ≠ j`. -/
noncomputable def chartShift (j : σ) (t : σ → k) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval fun i => if i = j then X j else X i + C (t i)

/-- The substitution `x_j ↦ 1`, the other variables are fixed. -/
noncomputable def dehomogenize (j : σ) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval fun i => if i = j then 1 else X i

/-- The substitution `x_j ↦ 0`, the other variables are fixed. -/
noncomputable def killVar (j : σ) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval fun i => if i = j then 0 else X i

/-- The factor `f'` in `pointChart j t f = x_j^m f'`: `∑ x_j^(|a| - m) ρ(c_a x^a)`. -/
noncomputable def chartTransform (j : σ) (t : σ → k) (m : ℕ) (f : MvPolynomial σ k) :
    MvPolynomial σ k :=
  ∑ a ∈ f.support, X j ^ (degree a - m) * chartRest j t (monomial a (f.coeff a))

theorem pointChart_X_eq (j : σ) (t : σ → k) (i : σ) :
    pointChart j t (X i) = X j * chartRest j t (X i) := by
  by_cases h : i = j
  · subst h
    simp [pointChart, chartRest]
  · simp [pointChart, chartRest, h]

/-- The chart sends `c x^a` to `x_j^|a| ρ(c x^a)`. -/
theorem pointChart_monomial (j : σ) (t : σ → k) (a : σ →₀ ℕ) (c : k) :
    pointChart j t (monomial a c) = X j ^ degree a * chartRest j t (monomial a c) := by
  rw [monomial_eq, map_mul, map_mul, Finsupp.prod, map_prod, map_prod, algHom_C, algHom_C]
  simp_rw [map_pow, pointChart_X_eq, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    degree_apply]
  ring

theorem pointChart_eq_sum (j : σ) (t : σ → k) (f : MvPolynomial σ k) :
    pointChart j t f =
      ∑ a ∈ f.support, X j ^ degree a * chartRest j t (monomial a (f.coeff a)) := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun a _ => pointChart_monomial j t a _

omit [DecidableEq σ] in
theorem le_degree_of_mem_support {m : ℕ} {f : MvPolynomial σ k} (hf : (m : ℕ∞) ≤ ord f)
    {a : σ →₀ ℕ} (ha : a ∈ f.support) : m ≤ degree a := by
  have := hf.trans (ord_le (MvPolynomial.mem_support_iff.mp ha))
  exact_mod_cast this

theorem pointChart_eq_X_pow_mul_chartTransform (j : σ) (t : σ → k) {m : ℕ}
    {f : MvPolynomial σ k} (hf : (m : ℕ∞) ≤ ord f) :
    pointChart j t f = X j ^ m * chartTransform j t m f := by
  rw [pointChart_eq_sum, chartTransform, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' (le_degree_of_mem_support hf ha)]

/-- If `m ≤ ord f`, the image of `f` under the chart is divisible by `x_j^m`. -/
theorem exists_pointChart_eq_X_pow_mul {j : σ} {t : σ → k} {m : ℕ} {f : MvPolynomial σ k}
    (hf : (m : ℕ∞) ≤ ord f) : ∃ f', pointChart j t f = X j ^ m * f' :=
  ⟨_, pointChart_eq_X_pow_mul_chartTransform j t hf⟩

theorem ord_le_ord_killVar (j : σ) (g : MvPolynomial σ k) : ord g ≤ ord (killVar j g) :=
  ord_le_ord_aeval _ (fun i => by split_ifs <;> simp) g

theorem killVar_comp_chartRest (j : σ) (t : σ → k) :
    (killVar j).comp (chartRest j t) = chartRest j t := by
  refine algHom_ext fun i => ?_
  by_cases h : i = j
  · subst h
    simp [killVar, chartRest]
  · simp [killVar, chartRest, h]

/-- The substitution `x_j ↦ 0` sends `f'` to `ρ(f_m)`, with `f_m` the part of degree `m`. -/
theorem killVar_chartTransform (j : σ) (t : σ → k) {m : ℕ} {f : MvPolynomial σ k}
    (hf : (m : ℕ∞) ≤ ord f) :
    killVar j (chartTransform j t m f) =
      chartRest j t (∑ a ∈ f.support with degree a = m, monomial a (f.coeff a)) := by
  rw [chartTransform, map_sum, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hm := le_degree_of_mem_support hf ha
  have hX : killVar j (X j : MvPolynomial σ k) = 0 := by simp [killVar]
  rw [map_mul, map_pow, ← AlgHom.comp_apply, killVar_comp_chartRest, hX]
  split_ifs with h
  · simp [h]
  · rw [zero_pow (by omega), zero_mul]

theorem dehomogenize_monomial (j : σ) (a : σ →₀ ℕ) (c : k) :
    dehomogenize j (monomial a c) = monomial (a.erase j) c := by
  conv_lhs => rw [← Finsupp.single_add_erase j a, ← one_mul c, ← monomial_mul_monomial,
    ← X_pow_eq_monomial]
  have hb : ∀ i ∈ (a.erase j).support, i ≠ j := by
    intro i hi h
    subst h
    simp at hi
  have h1 : dehomogenize j (X j : MvPolynomial σ k) = 1 := by simp [dehomogenize]
  rw [map_mul, map_pow, h1, one_pow, one_mul, dehomogenize, aeval_monomial, monomial_eq,
    algebraMap_eq]
  congr 1
  exact Finsupp.prod_congr fun i hi => by simp [hb i hi]

theorem chartShift_comp_dehomogenize (j : σ) (t : σ → k) :
    (chartShift j t).comp (dehomogenize j) = chartRest j t := by
  refine algHom_ext fun i => ?_
  by_cases h : i = j
  · subst h
    simp [chartShift, dehomogenize, chartRest]
  · simp [chartShift, dehomogenize, chartRest, h]

theorem chartShift_neg_comp (j : σ) (t : σ → k) :
    (chartShift j (-t)).comp (chartShift j t) = AlgHom.id k _ := by
  refine algHom_ext fun i => ?_
  by_cases h : i = j
  · subst h
    simp [chartShift]
  · simp [chartShift, h]

theorem chartShift_injective (j : σ) (t : σ → k) : Function.Injective (chartShift j t) :=
  fun p q h => by
    have := congrArg (chartShift j (-t)) h
    rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, chartShift_neg_comp, AlgHom.id_apply,
      AlgHom.id_apply] at this

omit [DecidableEq σ] in
/-- A substitution of polynomials of total degree at most `1` does not raise the total degree. -/
theorem totalDegree_aeval_le {φ : σ → MvPolynomial σ k} (hφ : ∀ i, (φ i).totalDegree ≤ 1)
    (p : MvPolynomial σ k) : (aeval φ p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun a ha => ?_)
  rw [aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add, Finsupp.prod]
  refine (totalDegree_finsetProd _ _).trans ((Finset.sum_le_sum fun i _ => ?_).trans
    (le_totalDegree ha))
  exact (totalDegree_pow _ _).trans ((Nat.mul_le_mul_left (a i) (hφ i)).trans_eq (mul_one _))

theorem totalDegree_chartShift_le (j : σ) (t : σ → k) (p : MvPolynomial σ k) :
    (chartShift j t p).totalDegree ≤ p.totalDegree := by
  refine totalDegree_aeval_le (fun i => ?_) p
  split_ifs
  · simp
  · exact (totalDegree_add _ _).trans (by simp)

omit [DecidableEq σ] in
/-- The order of a nonzero polynomial is at most its total degree. -/
theorem ord_le_totalDegree {p : MvPolynomial σ k} (hp : p ≠ 0) :
    ord p ≤ (p.totalDegree : ℕ∞) := by
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hp
  exact (ord_le hd).trans
    (by exact_mod_cast le_totalDegree (MvPolynomial.mem_support_iff.mpr hd))

omit [DecidableEq σ] in
theorem degree_eq_add_degree_erase (j : σ) (c : σ →₀ ℕ) :
    degree c = c j + degree (c.erase j) := by
  conv_lhs => rw [← Finsupp.single_add_erase j c]
  rw [map_add, degree_single]

theorem ord_chartTransform_le (j : σ) (t : σ → k) {m : ℕ} {f : MvPolynomial σ k}
    (hf : ord f = m) : ord (chartTransform j t m f) ≤ m := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hf
  obtain ⟨a0, ha0, hdeg⟩ := exists_coeff_ne_zero_and_ord_eq hf0
  have ha0m : degree a0 = m := by
    rw [hf] at hdeg
    exact_mod_cast hdeg.symm
  set q : MvPolynomial σ k :=
    ∑ a ∈ f.support with degree a = m, monomial (a.erase j) (f.coeff a) with hq_def
  have hE : killVar j (chartTransform j t m f) = chartShift j t q := by
    rw [killVar_chartTransform j t hf.ge, ← chartShift_comp_dehomogenize, AlgHom.comp_apply,
      map_sum, hq_def]
    simp_rw [dehomogenize_monomial]
  have hq : q.coeff (a0.erase j) = f.coeff a0 := by
    rw [hq_def, coeff_sum, Finset.sum_eq_single a0]
    · simp [coeff_monomial]
    · intro b hb hne
      rw [coeff_monomial, ite_eq_right_iff]
      intro he
      refine absurd ?_ hne
      have hbm : degree b = m := (Finset.mem_filter.mp hb).2
      have h1 := degree_eq_add_degree_erase j b
      have h2 := degree_eq_add_degree_erase j a0
      rw [he] at h1
      have hj : b j = a0 j := by omega
      rw [← Finsupp.single_add_erase j b, ← Finsupp.single_add_erase j a0, hj, he]
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨MvPolynomial.mem_support_iff.mpr ha0, ha0m⟩) h
  have hq0 : q ≠ 0 := fun h => ha0 (by rw [← hq, h]; simp)
  have hdq : q.totalDegree ≤ m := by
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun a ha => ?_)
    refine (totalDegree_monomial_le _ _).trans ?_
    have h1 := degree_eq_add_degree_erase j a
    have hm : degree a = m := (Finset.mem_filter.mp ha).2
    show degree (a.erase j) ≤ m
    omega
  have hs0 : chartShift j t q ≠ 0 := fun h =>
    hq0 (chartShift_injective j t (by rw [h, map_zero]))
  calc ord (chartTransform j t m f) ≤ ord (killVar j (chartTransform j t m f)) :=
        ord_le_ord_killVar _ _
    _ = ord (chartShift j t q) := by rw [hE]
    _ ≤ ((chartShift j t q).totalDegree : ℕ∞) := ord_le_totalDegree hs0
    _ ≤ m := by exact_mod_cast (totalDegree_chartShift_le j t q).trans hdq

/-- **The order does not go up under a point blowup** [Hau03]. If `ord f = m`
and the `x_j`-chart sends `f` to `x_j^m f'`, then `ord f' ≤ m`. -/
theorem ord_le_of_pointChart {j : σ} {t : σ → k} {f f' : MvPolynomial σ k} {m : ℕ}
    (hf : ord f = m) (h : pointChart j t f = X j ^ m * f') : ord f' ≤ m := by
  have h' := pointChart_eq_X_pow_mul_chartTransform j t hf.ge
  rw [h] at h'
  rw [mul_left_cancel₀ (pow_ne_zero m (X_ne_zero j)) h']
  exact ord_chartTransform_le j t hf

/-- The chart sends a nonzero polynomial to a nonzero polynomial. -/
theorem pointChart_ne_zero {j : σ} {t : σ → k} {f : MvPolynomial σ k} (hf : f ≠ 0) :
    pointChart j t f ≠ 0 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ord f = n := ⟨(ord f).toNat, (ENat.natCast_toNat (ord_ne_top hf)).symm⟩
  rw [pointChart_eq_X_pow_mul_chartTransform j t hn.ge]
  refine mul_ne_zero (pow_ne_zero _ (X_ne_zero j)) fun h0 => ?_
  have := ord_chartTransform_le j t hn
  rw [h0, ord_zero] at this
  exact absurd this (by simp)

theorem pointChart_injective (j : σ) (t : σ → k) : Function.Injective (pointChart j t) :=
  (injective_iff_map_eq_zero (pointChart j t)).mpr fun _ h =>
    by_contra fun hf => pointChart_ne_zero hf h

/-- If `f ≠ 0` and the chart sends `f` to `x_j^m f'`, then `f' ≠ 0`. -/
theorem ne_zero_of_pointChart_eq_X_pow_mul {j : σ} {t : σ → k} {f f' : MvPolynomial σ k} {m : ℕ}
    (hf : f ≠ 0) (h : pointChart j t f = X j ^ m * f') : f' ≠ 0 := by
  rintro rfl
  rw [mul_zero] at h
  exact pointChart_ne_zero hf h

end Singularity
