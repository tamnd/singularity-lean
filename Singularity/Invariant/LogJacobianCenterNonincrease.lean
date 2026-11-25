/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianCenter
import Singularity.Invariant.LogJacobianNonincrease

/-!
# The order `ρ` does not go up under the blowup of a regular center

Let `k` be a field of characteristic `p`, let `g` be a polynomial in `k[x_i : i ∈ σ]`, and let `Δ`
give the divisor `E = V(∏_{i ∈ Δ} x_i)`. Let `S` give the coordinate center `C = V(x_i : i ∈ S)`
with the ideal `I_C = (x_i : i ∈ S)`, and let `g ∈ I_C^p`. In the `x_j`-chart of the blowup of `C`
with translations `t` (`centerChart S j t`), with `j ∈ S`, write `π(g) = x_j^p g'`, and let `Δ'` be
the new divisor (`centerDivisor Δ S j t`). Let `r` be the divisor exponent of `g` and let `ρ` be the
order of the log-Jacobian ideal of `g`. This file proves Theorem 3.4.5 and Example 3.4.6 of
Volume 7, Section 3.4 of the handbook.

The handbook states the two conditions of Theorem 3.4.5 with the residual ideals.

* (H1) `Θ(g) ⊆ x^r I_C^ρ`.
* (H2) `Θ_C(g) ⊆ x^r I_C^(ρ+1)`, or `Θ_C(g)` contains an element `x^r h₀` with `ord h₀ = ρ`.

The file states these conditions in this elementary form. Each element of `Θ(g)` is `x^r` times an
element of `I_C^ρ`. Each element of `Θ_C(g)` is `x^r` times an element of `I_C^(ρ+1)`, or
`Θ_C(g)` has an element `x^r h₀` with `ord h₀ = ρ`. Since `I_C Θ(g) ⊆ Θ_C(g) ⊆ Θ(g)`, these forms
are equivalent to the conditions of the handbook. Under (H1) and (H2), the clean part `g'_c` of
`g'` is not `0`, and `ρ(g'_c) ≤ ρ(g)` for the new divisor `Δ'`.

The proof follows the handbook. Let `σ` be `ρ + 1` in the first case of (H2) and `ρ` in the second
case.

* Each element of `Θ_C(g)` is `x^r q` with `q ∈ I_C^σ`. Its image under `π` is divisible by
  `x_j^N x^e`, with `N = ∑_{i ∈ S} r_i + σ` and `e = centerExponent S j t r`. The factor
  `x_j^(∑_{i ∈ S} r_i) x^e` comes from `π(x^r)` (`centerChart_monomial_one`), and the factor
  `x_j^σ` comes from `π(q)` (`exists_centerChart_eq_X_pow_mul`).
* Since `g ∈ I_C^p`, each monomial of an element of `Θ_C(g)` has degree at least `p` in the
  variables of `S` (`logJacobianCenter_le_centerDegreeIdeal`). So `p ≤ N`.
* By the law `(x_j^p u) Θ'(g') ⊆ π(Θ_C(g))`, each element of `Θ'(g')` is divisible by `x^b`
  with `x_j^p x^b = x_j^N x^e`, after the cancellation of `x_j^p` and of the factor
  `u = centerUnit Δ S j t` (`monomial_one_dvd_of_dvd_mul`). The monomial `x^b` uses only variables
  of `Δ'`.
* There is an element `x^r q ∈ Θ_C(g)` with `ord q = σ` and `ord π(q) ≤ σ + ρ`. In the first case
  `q = x_j h₁` with `x^r h₁ ∈ Θ(g)` of order `|r| + ρ`, and in the second case `q = h₀`. The lemma
  on the equimultiple weak transform (`ord_le_of_centerChart`) gives the bound on `ord π(q)`.
  The law `π(Θ_C(g)) ⊆ (x_j^p) Θ'(g')` gives `π(x^r q) = x_j^p φ` with `φ ∈ Θ'(g')` and
  `ord φ ≤ |b| + ρ`.
* For a clean `g'_c ≠ 0`, `x^b` divides `x^{r'}` (Theorem 3.1.4, part 1), and the bound on
  `ord φ` gives `ρ(g'_c) ≤ ρ` (`logJacobianOrder_le_of_mem`).

The handbook works in the power series ring, where `u` is a unit. The proof here stays in `k[x]`.

Example 3.4.6 shows that (H2) is necessary. Over `𝔽₂`, with the coordinates `(x, y, w)`, let
`g = y^2 w + y^3`, `Δ = {w}` and `C = V(x, y)`. Then (H1) holds and (H2) fails. In the `x`-chart,
`g' = y^2 w + x y^3`, and `ρ(g'_c) = 3 > 2 = ρ(g)`.

## Main definitions

* `Singularity.centerRest S j t`: the substitution `x_j ↦ 1`, `x_i ↦ x_i + t_i` for `i ∈ S`,
  `i ≠ j`, and `x_i ↦ x_i` for `i ∉ S`. The chart sends `x^a` to `x_j^(∑_{i ∈ S} a_i)` times the
  image of `x^a` under this substitution (`centerChart_monomial`).
* `Singularity.centerExponent S j t r`: the exponents of the factors `x_l` of the image of `x^r`
  for `l ≠ j` with `l ∉ S` or `t_l = 0`.
* `Singularity.centerChartUnit S j t r`: the unit factor `∏ (x_l + t_l)^(r_l)` of the image of
  `x^r`, over the `l ∈ S`, `l ≠ j`, with `t_l ≠ 0`.

## Main results

* `logJacobianCenter_le_centerDegreeIdeal`: if each monomial of `g` has degree at least `n` in the
  variables of `S`, then the same holds for each element of `Θ_C(g)`.
* `centerChart_monomial_one`: `π(x^r) = x_j^(∑_{i ∈ S} r_i) x^e v` with `e = centerExponent S j t r`
  and `v = centerChartUnit S j t r`.
* `logJacobianOrder_cleanPart_le_of_mem_center`: the core of the proof, for a general exponent
  `σ`.
* `logJacobianOrder_cleanPart_le_center`: Theorem 3.4.5, `g'_c ≠ 0` and `ρ(g'_c) ≤ ρ(g)`.
* `exists_logJacobianOrder_eq`: for a clean `g ≠ 0`, the order `ρ(g)` is finite.
* `centerExample_hyp`, `centerExample_centerChart`, `centerExample_H1`, `centerExample_not_H2`,
  `centerExample_logJacobianOrder`, `centerExample_logJacobianOrder_cleanPart`: Example 3.4.6.

## References

* [Cos87] V. Cossart, *Polyèdre caractéristique d'une singularité*, thèse d'État, Orsay 1987.
* Volume 7, Section 3.4 of the handbook: Theorem 3.4.5 and Example 3.4.6.
-/

open MvPolynomial Finsupp

namespace Singularity

/-! ### The degree in the variables of the center -/

section DegreeIdeal

variable {σ k : Type*} [Field k] [DecidableEq σ]

theorem centerDegreeIdeal_mono {S : Finset σ} {m n : ℕ} (h : m ≤ n) :
    (centerDegreeIdeal S n : Ideal (MvPolynomial σ k)) ≤ centerDegreeIdeal S m :=
  fun _ hf a ha => h.trans (mem_centerDegreeIdeal.mp hf a ha)

/-- The derivative `∂_l` lowers the degree in the variables of `S` by `1` if `l ∈ S`, and it keeps
this degree if `l ∉ S`. -/
theorem pderiv_mem_centerDegreeIdeal {S : Finset σ} {n : ℕ} {f : MvPolynomial σ k}
    (hf : f ∈ centerDegreeIdeal S n) (l : σ) :
    pderiv l f ∈ centerDegreeIdeal S (n - if l ∈ S then 1 else 0) := by
  intro a ha
  have hc := MvPolynomial.mem_support_iff.mp ha
  rw [coeff_pderiv] at hc
  have h := mem_centerDegreeIdeal.mp hf (a + single l 1)
    (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hc))
  simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, Finsupp.single_apply,
    Finset.sum_ite_eq] at h
  split_ifs at h ⊢ <;> omega

theorem X_mem_centerDegreeIdeal_ite (S : Finset σ) (i : σ) :
    (X i : MvPolynomial σ k) ∈ centerDegreeIdeal S (if i ∈ S then 1 else 0) := by
  split_ifs with hi
  · exact X_mem_centerDegreeIdeal hi
  · exact fun _ _ => Nat.zero_le _

/-- The product `x_m ∂_l f` keeps the degree in the variables of `S` if `m = l` or `m ∈ S`. -/
theorem X_mul_pderiv_mem_centerDegreeIdeal {S : Finset σ} {n : ℕ} {f : MvPolynomial σ k}
    (hf : f ∈ centerDegreeIdeal S n) {m l : σ} (hml : m = l ∨ m ∈ S) :
    X m * pderiv l f ∈ centerDegreeIdeal S n := by
  refine centerDegreeIdeal_mono ?_ (mul_mem_centerDegreeIdeal (X_mem_centerDegreeIdeal_ite S m)
    (pderiv_mem_centerDegreeIdeal hf l))
  rcases hml with rfl | hm
  · split_ifs <;> omega
  · rw [ite_eq_left hm]
    split_ifs <;> omega

/-- If each monomial of `g` has degree at least `n` in the variables of `S`, then each element of
`Θ_C(g)` has the same property. The generators `x_i ∂_i g`, `∂_l g` with `l ∉ S`, and `x_m ∂_l g`
with `m ∈ S` keep this degree. -/
theorem logJacobianCenter_le_centerDegreeIdeal {Δ S : Finset σ} {n : ℕ} {g : MvPolynomial σ k}
    (hg : g ∈ centerDegreeIdeal S n) : logJacobianCenter Δ S g ≤ centerDegreeIdeal S n := by
  refine Ideal.span_le.mpr ?_
  rintro s ((⟨i, -, rfl⟩ | ⟨l, ⟨-, hl⟩, rfl⟩) | ⟨⟨m, l⟩, ⟨-, -, hm⟩, rfl⟩)
  · exact X_mul_pderiv_mem_centerDegreeIdeal hg (Or.inl rfl)
  · have := pderiv_mem_centerDegreeIdeal hg l
    rwa [ite_eq_right hl, Nat.sub_zero] at this
  · exact X_mul_pderiv_mem_centerDegreeIdeal hg (Or.inr hm)

end DegreeIdeal

/-! ### The chart of a monomial -/

section ChartMonomial

variable {σ k : Type*} [Field k] [DecidableEq σ]

/-- The substitution `x_j ↦ 1`, `x_i ↦ x_i + t_i` for `i ∈ S`, `i ≠ j`, and `x_i ↦ x_i` for
`i ∉ S`. The chart of the blowup of the center sends `x^a` to `x_j^(∑_{i ∈ S} a_i)` times the
image of `x^a` under this substitution (`centerChart_monomial`). -/
noncomputable def centerRest (S : Finset σ) (j : σ) (t : σ → k) :
    MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval fun i => if i = j then 1 else if i ∈ S then X i + C (t i) else X i

theorem centerChart_X_eq {S : Finset σ} {j : σ} (hj : j ∈ S) (t : σ → k) (i : σ) :
    centerChart S j t (X i) = X j ^ (if i ∈ S then 1 else 0) * centerRest S j t (X i) := by
  by_cases hij : i = j
  · subst hij
    simp [centerChart, centerRest, hj]
  · by_cases hi : i ∈ S
    · simp [centerChart, centerRest, hi, hij]
    · simp [centerChart, centerRest, hi, hij]

/-- The chart sends `c x^a` to `x_j^(∑_{i ∈ S} a_i)` times the image of `c x^a` under
`centerRest S j t`. -/
theorem centerChart_monomial {S : Finset σ} {j : σ} (hj : j ∈ S) (t : σ → k) (a : σ →₀ ℕ)
    (c : k) :
    centerChart S j t (monomial a c) = X j ^ (∑ i ∈ S, a i) * centerRest S j t (monomial a c) := by
  have hsum : ∑ i ∈ a.support, (if i ∈ S then 1 else 0) * a i = ∑ i ∈ S, a i := by
    simp_rw [ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter]
    refine Finset.sum_subset (fun i hi => (Finset.mem_filter.mp hi).2) fun i hiS hi => ?_
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr h, hiS⟩)
  rw [monomial_eq, map_mul, map_mul, Finsupp.prod, map_prod, map_prod, algHom_C, algHom_C]
  simp_rw [map_pow, centerChart_X_eq hj, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum, hsum]
  ring

variable [DecidableEq k]

/-- The exponents of the factors `x_l` of `centerRest S j t (x^r)`: the `r_l` for `l ≠ j` with
`l ∉ S` or `t_l = 0`. -/
noncomputable def centerExponent (S : Finset σ) (j : σ) (t : σ → k) (r : σ →₀ ℕ) : σ →₀ ℕ :=
  r.filter fun l => l ≠ j ∧ (l ∉ S ∨ t l = 0)

/-- The unit factor of `centerRest S j t (x^r)`: the product of the `(x_l + t_l)^(r_l)` over the
`l ∈ S`, `l ≠ j`, with `t_l ≠ 0`. -/
noncomputable def centerChartUnit (S : Finset σ) (j : σ) (t : σ → k) (r : σ →₀ ℕ) :
    MvPolynomial σ k :=
  (r.filter fun l => ¬(l ≠ j ∧ (l ∉ S ∨ t l = 0))).prod fun l e =>
    (if l = j then 1 else if l ∈ S then X l + C (t l) else X l) ^ e

theorem centerRest_monomial_one (S : Finset σ) (j : σ) (t : σ → k) (r : σ →₀ ℕ) :
    centerRest S j t (monomial r 1) =
      monomial (centerExponent S j t r) 1 * centerChartUnit S j t r := by
  rw [centerRest, aeval_monomial, map_one, one_mul,
    ← Finsupp.prod_filter_mul_prod_filter_not (p := fun l => l ≠ j ∧ (l ∉ S ∨ t l = 0))]
  congr 1
  rw [centerExponent, ← prod_X_pow_eq_monomial, Finsupp.prod]
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [Finsupp.support_filter, Finset.mem_filter] at hl
  obtain ⟨hlj, hl'⟩ := hl.2
  rw [ite_eq_right hlj]
  split_ifs with hlS
  · rw [hl'.resolve_left (not_not.mpr hlS), C_0, add_zero]
  · rfl

theorem constantCoeff_centerChartUnit_ne_zero (S : Finset σ) (j : σ) (t : σ → k) (r : σ →₀ ℕ) :
    constantCoeff (centerChartUnit S j t r) ≠ 0 := by
  rw [centerChartUnit, Finsupp.prod, map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun l hl => ?_
  rw [Finsupp.support_filter, Finset.mem_filter] at hl
  rw [map_pow]
  refine pow_ne_zero _ ?_
  by_cases hlj : l = j
  · simp [hlj]
  · have hlS : l ∈ S := by
      by_contra h
      exact hl.2 ⟨hlj, Or.inl h⟩
    have ht : t l ≠ 0 := fun h0 => hl.2 ⟨hlj, Or.inr h0⟩
    simpa [hlj, hlS] using ht

theorem ord_centerChartUnit (S : Finset σ) (j : σ) (t : σ → k) (r : σ →₀ ℕ) :
    ord (centerChartUnit S j t r) = 0 := by
  refine le_antisymm ?_ (by simp)
  have h : (centerChartUnit S j t r).coeff 0 ≠ 0 := constantCoeff_centerChartUnit_ne_zero S j t r
  simpa using ord_le h

/-- **The chart of a monomial.** For `j ∈ S`, the chart sends `x^r` to
`x_j^(∑_{i ∈ S} r_i) x^e v`, with `e = centerExponent S j t r` and `v = centerChartUnit S j t r`.
The constant term of `v` is not `0`. -/
theorem centerChart_monomial_one {S : Finset σ} {j : σ} (hj : j ∈ S) (t : σ → k) (r : σ →₀ ℕ) :
    centerChart S j t (monomial r 1) =
      X j ^ (∑ i ∈ S, r i) * monomial (centerExponent S j t r) 1 * centerChartUnit S j t r := by
  rw [centerChart_monomial hj, centerRest_monomial_one, mul_assoc]

/-- The constant term of `u = centerUnit Δ S j t` is the product of the `t_i ≠ 0`, so it is not
`0`. -/
theorem constantCoeff_centerUnit_ne_zero (Δ S : Finset σ) (j : σ) (t : σ → k) :
    constantCoeff (centerUnit Δ S j t) ≠ 0 := by
  rw [centerUnit, map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  rw [map_add, constantCoeff_X, constantCoeff_C, zero_add]
  exact (Finset.mem_filter.mp hi).2.2.2

/-- The monomial `x_j^c x^e`, with `e = centerExponent S j t r`, uses only variables of the new
divisor `Δ'`, if `r` uses only variables of `Δ`. -/
theorem single_add_centerExponent_eq_zero {Δ S : Finset σ} {j : σ} {t : σ → k} {r : σ →₀ ℕ}
    (hr : ∀ i, i ∉ Δ → r i = 0) (c : ℕ) {i : σ} (hi : i ∉ centerDivisor Δ S j t) :
    (single j c + centerExponent S j t r) i = 0 := by
  rw [mem_centerDivisor, not_or] at hi
  rw [Finsupp.add_apply, Finsupp.single_apply, ite_eq_right fun h => hi.1 h.symm, zero_add,
    centerExponent, Finsupp.filter_apply]
  split_ifs with h
  · exact hr i fun hΔ => hi.2 ⟨hΔ, h⟩
  · rfl

end ChartMonomial

/-! ### The theorem -/

section Nonincrease

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ S : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

omit [Fintype σ] in
/-- **The core of Theorem 3.4.5.** Let `j ∈ S`, `g ∈ I_C^p` and `π(g) = x_j^p g'`. Let `r` use only
variables of `Δ`, and let each element of `Θ_C(g)` be `x^r` times an element of `I_C^s`. If
`Θ_C(g)` contains an element `x^r q` with `ord q = s` and `ord π(q) ≤ s + ρ`, then the clean part
`g'_c` of `g'` is not `0`, and `ρ(g'_c) ≤ ρ` for the new divisor `Δ'`. -/
theorem logJacobianOrder_cleanPart_le_of_mem_center (hj : j ∈ S)
    (hgS : g ∈ Ideal.span (X '' (S : Set σ)) ^ p) (h : centerChart S j t g = X j ^ p * g')
    {r : σ →₀ ℕ} (hr : ∀ i, i ∉ Δ → r i = 0) {s ρ : ℕ}
    (hs : ∀ f ∈ logJacobianCenter Δ S g, ∃ q ∈ Ideal.span (X '' (S : Set σ)) ^ s,
      f = monomial r 1 * q)
    {q : MvPolynomial σ k} (hq : monomial r 1 * q ∈ logJacobianCenter Δ S g) (hqo : ord q = s)
    (hqc : ord (centerChart S j t q) ≤ ((s + ρ : ℕ) : ℕ∞)) :
    cleanPart p g' ≠ 0 ∧ logJacobianOrder (centerDivisor Δ S j t) (cleanPart p g') ≤ ρ := by
  obtain ⟨N, hN⟩ : ∃ N, ∑ i ∈ S, r i + s = N := ⟨_, rfl⟩
  -- `p ≤ N`, since each monomial of `x^r q ∈ Θ_C(g)` has degree at least `p` in `S`.
  have hpN : p ≤ N := by
    have hΘ := logJacobianCenter_le_centerDegreeIdeal (Δ := Δ)
      (span_X_pow_le_centerDegreeIdeal S p hgS)
    have hq0 : q ≠ 0 := by
      rintro rfl
      rw [ord_zero] at hqo
      exact ENat.top_ne_natCast _ hqo
    obtain ⟨c, hc, hdeg⟩ := exists_coeff_ne_zero_and_ord_eq hq0
    have hcs : degree c = s := by
      rw [hqo] at hdeg
      exact_mod_cast hdeg.symm
    have hmem : r + c ∈ (monomial r (1 : k) * q).support := by
      rw [MvPolynomial.mem_support_iff, coeff_monomial_mul, one_mul]
      exact hc
    have h1 := mem_centerDegreeIdeal.mp (hΘ hq) (r + c) hmem
    simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib] at h1
    have h2 := sum_le_degree S c
    omega
  -- `π(Θ_C(g)) ⊆ (x_j^N x^e)`.
  have hB1 : Ideal.map (centerChart S j t) (logJacobianCenter Δ S g) ≤
      Ideal.span {X j ^ N * monomial (centerExponent S j t r) (1 : k)} := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    obtain ⟨q₂, hq₂, rfl⟩ := hs f hf
    obtain ⟨q₂', hq₂'⟩ := exists_centerChart_eq_X_pow_mul (j := j) t hq₂
    rw [Ideal.mem_comap, Ideal.mem_span_singleton, map_mul, centerChart_monomial_one hj, hq₂',
      ← hN, pow_add]
    exact ⟨centerChartUnit S j t r * q₂', by ring⟩
  -- The monomial `x^b` with `x_j^p x^b = x_j^N x^e`.
  have hXb : X j ^ N * monomial (centerExponent S j t r) (1 : k) =
      X j ^ p * monomial (single j (N - p) + centerExponent S j t r) 1 := by
    rw [monomial_single_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hpN]
  have hb : ∀ i, i ∉ centerDivisor Δ S j t → (single j (N - p) + centerExponent S j t r) i = 0 :=
    fun i hi => single_add_centerExponent_eq_zero hr (N - p) hi
  have hdb : degree (single j (N - p) + centerExponent S j t r) =
      N - p + degree (centerExponent S j t r) := by
    rw [map_add, degree_single]
  -- `Θ'(g') ⊆ (x^b)`.
  have hB : logJacobian (centerDivisor Δ S j t) g' ≤
      Ideal.span {monomial (single j (N - p) + centerExponent S j t r) 1} := by
    intro φ hφ
    have h2 := span_mul_logJacobian_le_map_centerChart p (Δ := Δ) hj h
      (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hφ)
    have h3 := Ideal.mem_span_singleton.mp (hB1 h2)
    rw [hXb, mul_assoc] at h3
    have h4 := (mul_dvd_mul_iff_left (pow_ne_zero p (X_ne_zero j))).mp h3
    exact Ideal.mem_span_singleton.mpr
      (monomial_one_dvd_of_dvd_mul (constantCoeff_centerUnit_ne_zero Δ S j t) h4)
  -- `ord π(x^r q) ≤ N + |e| + ρ`.
  have hfo : ord (centerChart S j t (monomial r 1 * q)) ≤
      ((N + degree (centerExponent S j t r) + ρ : ℕ) : ℕ∞) := by
    rw [map_mul, centerChart_monomial_one hj, ord_mul, ord_mul, ord_mul, ord_X_pow,
      ord_monomial one_ne_zero, ord_centerChartUnit, add_zero]
    calc _ ≤ ((∑ i ∈ S, r i : ℕ) : ℕ∞) + ((degree (centerExponent S j t r) : ℕ) : ℕ∞) +
          ((s + ρ : ℕ) : ℕ∞) := by gcongr
      _ = _ := by
        rw [← hN]
        push_cast
        ring
  -- `π(x^r q) = x_j^p φ` with `φ ∈ Θ'(g')` and `ord φ ≤ |b| + ρ`.
  obtain ⟨φ, hφ, hφeq⟩ := Ideal.mem_span_singleton_mul.mp
    (map_centerChart_logJacobianCenter_le_span_mul p (Δ := Δ) hj h (Ideal.mem_map_of_mem _ hq))
  have h5 : ord (centerChart S j t (monomial r 1 * q)) = p + ord φ := by
    rw [← hφeq, ord_mul, ord_X_pow]
  have hφo : ord φ ≤
      ((degree (single j (N - p) + centerExponent S j t r) + ρ : ℕ) : ℕ∞) := by
    have h6 : (p : ℕ∞) + ord φ ≤ (p : ℕ∞) +
        ((degree (single j (N - p) + centerExponent S j t r) + ρ : ℕ) : ℕ∞) := by
      rw [← h5]
      refine hfo.trans ?_
      rw [← Nat.cast_add, hdb]
      exact_mod_cast (by omega : N + degree (centerExponent S j t r) + ρ ≤
        p + (N - p + degree (centerExponent S j t r) + ρ))
    exact (ENat.add_le_add_iff_left (ENat.natCast_ne_top p)).mp h6
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    rw [ord_zero, top_le_iff] at hφo
    exact ENat.natCast_ne_top _ hφo
  -- `g'_c ≠ 0`, since `Θ'(g'_c) = Θ'(g')` contains `φ ≠ 0`.
  have hcl : cleanPart p g' ≠ 0 := by
    intro h0
    have h7 : logJacobian (centerDivisor Δ S j t) g' = ⊥ := by
      rw [← logJacobian_cleanPart p, h0, logJacobian_zero]
    rw [h7, Ideal.mem_bot] at hφ
    exact hφ0 hφ
  refine ⟨hcl, ?_⟩
  refine logJacobianOrder_le_of_mem p hcl (isClean_cleanPart p g') hb (φ := φ) ?_ ?_ ?_
  · rw [logJacobian_cleanPart]
    exact hB
  · rw [logJacobian_cleanPart]
    exact hφ
  · rw [Nat.cast_add] at hφo
    exact hφo

omit [DecidableEq σ] [DecidableEq k] [Fintype σ] in
/-- For a clean `g ≠ 0`, the order `ρ` is finite. So the hypothesis `logJacobianOrder Δ g = ρ` of
Theorem 3.4.5 only gives a name to `ρ`. -/
theorem exists_logJacobianOrder_eq (hg : g ≠ 0) (hc : IsClean p g) :
    ∃ ρ : ℕ, logJacobianOrder Δ g = ρ := by
  have hG : residualFactor Δ g ≠ 0 := by
    intro h0
    apply hg
    rw [← monomial_mul_residualFactor Δ g, h0, mul_zero]
  obtain ⟨ρ, hρ⟩ := ENat.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ord_ne_top hG) (logJacobianOrder_le p hc))
  exact ⟨ρ, hρ.symm⟩

omit [Fintype σ] in
/-- **`ρ` does not go up under the blowup of a regular center** (Volume 7, Section 3.4 of the
handbook, Theorem 3.4.5). Let `j ∈ S`, let `g ∈ I_C^p` with `I_C = (x_i : i ∈ S)`, and let
`π(g) = x_j^p g'` in the chart `π = centerChart S j t`. Let `r` be the divisor exponent of `g`, and
let `ρ = logJacobianOrder Δ g`. Assume the two conditions of the handbook in this elementary form.

* (H1) Each element of `Θ(g)` is `x^r` times an element of `I_C^ρ`.
* (H2) Each element of `Θ_C(g)` is `x^r` times an element of `I_C^(ρ+1)`, or `Θ_C(g)` has an
  element `x^r h₀` with `ord h₀ = ρ`.

Since `I_C Θ(g) ⊆ Θ_C(g) ⊆ Θ(g)`, these forms are equivalent to the conditions
`Θ(g) ⊆ x^r I_C^ρ` and `Θ_C(g) ⊆ x^r I_C^(ρ+1)` or `ord(x^(-r) Θ_C(g)) = ρ` of the handbook. Then
the clean part `g'_c` of `g'` is not `0`, and `ρ(g'_c) ≤ ρ(g)` for the new divisor
`Δ' = centerDivisor Δ S j t`. The handbook asks that `g ≠ 0` is clean. Then `ρ` is finite
(`exists_logJacobianOrder_eq`). The proof uses only that `ρ` is finite. The point of the chart can
be translated (`t ≠ 0`). -/
theorem logJacobianOrder_cleanPart_le_center (hj : j ∈ S)
    (hgS : g ∈ Ideal.span (X '' (S : Set σ)) ^ p) (h : centerChart S j t g = X j ^ p * g')
    {ρ : ℕ} (hρ : logJacobianOrder Δ g = ρ)
    (H1 : ∀ f ∈ logJacobian Δ g, ∃ q ∈ Ideal.span (X '' (S : Set σ)) ^ ρ,
      f = monomial (divisorExponent Δ g) 1 * q)
    (H2 : (∀ f ∈ logJacobianCenter Δ S g, ∃ q ∈ Ideal.span (X '' (S : Set σ)) ^ (ρ + 1),
        f = monomial (divisorExponent Δ g) 1 * q) ∨
      ∃ q, monomial (divisorExponent Δ g) 1 * q ∈ logJacobianCenter Δ S g ∧ ord q = ρ) :
    cleanPart p g' ≠ 0 ∧
      logJacobianOrder (centerDivisor Δ S j t) (cleanPart p g') ≤ logJacobianOrder Δ g := by
  have hr : ∀ i, i ∉ Δ → divisorExponent Δ g i = 0 := fun i hi => divisorExponent_eq_zero hi
  have hm0 : monomial (divisorExponent Δ g) (1 : k) ≠ 0 := by
    rw [Ne, monomial_eq_zero]
    exact one_ne_zero
  rw [hρ]
  rcases H2 with H2 | ⟨q, hq, hqo⟩
  · -- `σ = ρ + 1`: the element `x_j h₁` with `h₁ ∈ Θ(g)` of order `|r| + ρ`.
    obtain ⟨h₁, hh₁, hord₁⟩ := exists_mem_ord_eq_idealOrd (logJacobian Δ g)
    rw [idealOrd_logJacobian, hρ] at hord₁
    obtain ⟨q₁, hq₁I, rfl⟩ := H1 h₁ hh₁
    have hq₁o : ord q₁ = ρ := by
      rw [ord_mul, ord_monomial one_ne_zero] at hord₁
      have hne := ENat.natCast_ne_top (degree (divisorExponent Δ g))
      exact le_antisymm ((ENat.add_le_add_iff_left hne).mp hord₁.le)
        ((ENat.add_le_add_iff_left hne).mp hord₁.ge)
    obtain ⟨q₁', hq₁'⟩ := exists_centerChart_eq_X_pow_mul (j := j) t hq₁I
    have hq₁'o := ord_le_of_centerChart hj hq₁I hq₁o hq₁'
    refine logJacobianOrder_cleanPart_le_of_mem_center p hj hgS h hr H2 (q := X j * q₁) ?_ ?_ ?_
    · rw [mul_left_comm]
      exact span_X_mul_logJacobian_le Δ S g
        (Ideal.mul_mem_mul (Ideal.subset_span ⟨j, hj, rfl⟩) hh₁)
    · rw [ord_mul, ord_X, hq₁o]
      push_cast
      ring
    · rw [map_mul, centerChart_X_self, hq₁', ord_mul, ord_mul, ord_X, ord_X_pow]
      calc (1 : ℕ∞) + (ρ + ord q₁') ≤ 1 + (ρ + ρ) := by gcongr
        _ = _ := by
          push_cast
          ring
  · -- `σ = ρ`: the element `x^r h₀` with `ord h₀ = ρ`.
    have hqI : q ∈ Ideal.span (X '' (S : Set σ)) ^ ρ := by
      obtain ⟨q₂, hq₂, he⟩ := H1 _ (logJacobianCenter_le Δ S g hq)
      rwa [mul_left_cancel₀ hm0 he]
    obtain ⟨q', hq'⟩ := exists_centerChart_eq_X_pow_mul (j := j) t hqI
    have hq'o := ord_le_of_centerChart hj hqI hqo hq'
    refine logJacobianOrder_cleanPart_le_of_mem_center p hj hgS h hr
      (fun f hf => H1 f (logJacobianCenter_le Δ S g hf)) hq hqo ?_
    rw [hq', ord_mul, ord_X_pow]
    push_cast
    gcongr

end Nonincrease

/-! ### Example 3.4.6 -/

section Example

section General

variable {σ k : Type*} [Field k]

/-- If each variable `x_i` of `Δ` is missing from some monomial of `P`, then the divisor exponent
of `P` is `0`. -/
theorem divisorExponent_eq_zero_of {Δ : Finset σ} {P : MvPolynomial σ k}
    (h : ∀ i ∈ Δ, ∃ β ∈ P.support, β i = 0) : divisorExponent Δ P = 0 := by
  ext i
  rw [Finsupp.coe_zero, Pi.zero_apply]
  by_cases hi : i ∈ Δ
  · obtain ⟨β, hβ, h0⟩ := h i hi
    exact Nat.eq_zero_of_le_zero ((divisorExponent_le hβ i).trans h0.le)
  · exact divisorExponent_eq_zero hi

/-- If the divisor exponent of `g` is `0`, then `ρ(g)` is the order of `Θ(g)`. -/
theorem logJacobianOrder_eq_idealOrd {Δ : Finset σ} {g : MvPolynomial σ k}
    (h : divisorExponent Δ g = 0) : logJacobianOrder Δ g = idealOrd (logJacobian Δ g) := by
  rw [idealOrd_logJacobian, h, map_zero, Nat.cast_zero, zero_add]

/-- The order of `x_m f` is at least the order of `f`. -/
theorem le_ord_X_mul {f : MvPolynomial σ k} {n : ℕ∞} (h : n ≤ ord f) (m : σ) :
    n ≤ ord (X m * f) :=
  h.trans (le_add_self.trans (le_ord_mul _ _))

/-- If the order of `f` is at least `n`, then the order of `x_m f` is at least `n + 1`. -/
theorem natCast_succ_le_ord_X_mul {f : MvPolynomial σ k} {n : ℕ} (h : (n : ℕ∞) ≤ ord f)
    (m : σ) : ((n + 1 : ℕ) : ℕ∞) ≤ ord (X m * f) := by
  rw [ord_mul, ord_X, Nat.cast_succ, add_comm (n : ℕ∞) 1]
  exact add_le_add le_rfl h

/-- The order of `x_i x_j^n` is `n + 1`. -/
theorem ord_X_mul_X_pow (i j : σ) (n : ℕ) :
    ord (X i * X j ^ n : MvPolynomial σ k) = ((n + 1 : ℕ) : ℕ∞) := by
  rw [ord_mul, ord_X, ord_X_pow, Nat.cast_succ, add_comm (n : ℕ∞) 1]

/-- The exponent `a` is in the support of `x^a + x^b` if `a ≠ b`. -/
theorem mem_support_monomial_add_left {a b : σ →₀ ℕ} (h : a ≠ b) :
    a ∈ (monomial a (1 : k) + monomial b 1).support := by
  classical
  rw [MvPolynomial.mem_support_iff, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_monomial,
    coeff_monomial, ite_eq_left rfl, ite_eq_right h.symm, add_zero]
  exact one_ne_zero

/-- The exponent `b` is in the support of `x^a + x^b` if `a ≠ b`. -/
theorem mem_support_monomial_add_right {a b : σ →₀ ℕ} (h : a ≠ b) :
    b ∈ (monomial a (1 : k) + monomial b 1).support := by
  classical
  rw [MvPolynomial.mem_support_iff, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_monomial,
    coeff_monomial, ite_eq_right h, ite_eq_left rfl, zero_add]
  exact one_ne_zero

/-- The sum `c x^a + c' x^b` is clean if `a` and `b` are not in `q ℕ^σ`. -/
theorem isClean_monomial_add {q : ℕ} {a b : σ →₀ ℕ} (ha : ¬ ∀ i, q ∣ a i)
    (hb : ¬ ∀ i, q ∣ b i) (c c' : k) : IsClean q (monomial a c + monomial b c') := by
  classical
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · obtain rfl := Finset.mem_singleton.mp (support_monomial_subset h)
    exact ha
  · obtain rfl := Finset.mem_singleton.mp (support_monomial_subset h)
    exact hb

/-- In characteristic `2`, the constant `2` is `0`. -/
theorem two_eq_zero_mvPolynomial_zmod (τ : Type*) : (2 : MvPolynomial τ (ZMod 2)) = 0 := by
  rw [show (2 : MvPolynomial τ (ZMod 2)) = C 2 from (map_ofNat C 2).symm,
    show (2 : ZMod 2) = 0 from rfl, C_0]

end General

/-! The data of Example 3.4.6. The coordinates `(x, y, w)` are `X 0`, `X 1` and `X 2`. -/

private theorem ex_g_eq : (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) =
    monomial (single 1 2 + single 2 1) 1 + monomial (single 1 3) 1 := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial,
    show (X 2 : MvPolynomial (Fin 3) (ZMod 2)) = monomial (single 2 1) 1 from rfl]
  simp only [monomial_mul_monomial, one_mul]

private theorem ex_g'_eq : (X 1 ^ 2 * X 2 + X 0 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) =
    monomial (single 1 2 + single 2 1) 1 + monomial (single 0 1 + single 1 3) 1 := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial,
    show (X 2 : MvPolynomial (Fin 3) (ZMod 2)) = monomial (single 2 1) 1 from rfl,
    show (X 0 : MvPolynomial (Fin 3) (ZMod 2)) = monomial (single 0 1) 1 from rfl]
  simp only [monomial_mul_monomial, one_mul]

private theorem ex_ne : (single 1 2 + single 2 1 : Fin 3 →₀ ℕ) ≠ single 1 3 := by
  intro h
  have := DFunLike.congr_fun h 2
  simp at this

private theorem ex_ne' : (single 1 2 + single 2 1 : Fin 3 →₀ ℕ) ≠ single 0 1 + single 1 3 := by
  intro h
  have := DFunLike.congr_fun h 2
  simp at this

private theorem ex_not_dvd : ¬ ∀ i, 2 ∣ (single 1 2 + single 2 1 : Fin 3 →₀ ℕ) i :=
  fun h => absurd (h 2) (by simp)

private theorem ex_pderiv_g_zero :
    pderiv 0 (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) = 0 := by
  simp [pderiv_X]

private theorem ex_pderiv_g_one :
    pderiv 1 (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) = X 1 ^ 2 := by
  simp [pderiv_X]
  linear_combination (X 1 * X 2 + X 1 ^ 2 : MvPolynomial (Fin 3) (ZMod 2)) *
    two_eq_zero_mvPolynomial_zmod (Fin 3)

private theorem ex_pderiv_g_two :
    pderiv 2 (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) = X 1 ^ 2 := by
  simp [pderiv_X]

private theorem ex_pderiv_g'_zero :
    pderiv 0 (X 1 ^ 2 * X 2 + X 0 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) = X 1 ^ 3 := by
  simp [pderiv_X]

private theorem ex_pderiv_g'_one :
    pderiv 1 (X 1 ^ 2 * X 2 + X 0 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) = X 0 * X 1 ^ 2 := by
  simp [pderiv_X]
  linear_combination (X 1 * X 2 + X 0 * X 1 ^ 2 : MvPolynomial (Fin 3) (ZMod 2)) *
    two_eq_zero_mvPolynomial_zmod (Fin 3)

private theorem ex_pderiv_g'_two :
    pderiv 2 (X 1 ^ 2 * X 2 + X 0 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) = X 1 ^ 2 := by
  simp [pderiv_X]

private theorem ex_pderiv_g_cases (l : Fin 3) :
    pderiv l (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) = 0 ∨
      pderiv l (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) = X 1 ^ 2 := by
  fin_cases l
  · exact Or.inl ex_pderiv_g_zero
  · exact Or.inr ex_pderiv_g_one
  · exact Or.inr ex_pderiv_g_two

private theorem ex_pderiv_g'_cases (l : Fin 3) :
    pderiv l (X 1 ^ 2 * X 2 + X 0 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) = X 1 ^ 3 ∨
      pderiv l (X 1 ^ 2 * X 2 + X 0 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) = X 0 * X 1 ^ 2 ∨
      pderiv l (X 1 ^ 2 * X 2 + X 0 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) = X 1 ^ 2 := by
  fin_cases l
  · exact Or.inl ex_pderiv_g'_zero
  · exact Or.inr (Or.inl ex_pderiv_g'_one)
  · exact Or.inr (Or.inr ex_pderiv_g'_two)

private theorem ex_two_le_ord_pderiv_g (l : Fin 3) :
    ((2 : ℕ) : ℕ∞) ≤ ord (pderiv l (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2))) := by
  rcases ex_pderiv_g_cases l with h | h <;> rw [h] <;> simp

private theorem ex_two_le_ord_pderiv_g' (l : Fin 3) :
    ((2 : ℕ) : ℕ∞) ≤
      ord (pderiv l (X 1 ^ 2 * X 2 + X 0 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2))) := by
  rcases ex_pderiv_g'_cases l with h | h | h <;> rw [h]
  · norm_num
  · rw [ord_X_mul_X_pow]
    norm_num
  · norm_num

private theorem ex_X_one_sq_mem :
    (X 1 ^ 2 : MvPolynomial (Fin 3) (ZMod 2)) ∈
      Ideal.span (X '' (({0, 1} : Finset (Fin 3)) : Set (Fin 3))) ^ 2 :=
  Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_image_of_mem X (by simp))) 2

/-- **Example 3.4.6, the data.** Over `𝔽₂`, the polynomial `g = y^2 w + y^3` is not `0`, is clean
for `p = 2`, and is in `I_C^2` for the center `C = V(x, y)`. -/
theorem centerExample_hyp :
    (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) ≠ 0 ∧
      IsClean 2 (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) ∧
      (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) ∈
        Ideal.span (X '' (({0, 1} : Finset (Fin 3)) : Set (Fin 3))) ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ex_g_eq]
    exact MvPolynomial.ne_zero_iff.mpr
      ⟨_, MvPolynomial.mem_support_iff.mp (mem_support_monomial_add_right ex_ne)⟩
  · rw [ex_g_eq]
    exact isClean_monomial_add ex_not_dvd
      (fun h => absurd (h 1) (by simp)) 1 1
  · rw [show (X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) = X 1 ^ 2 * X 1 by ring]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ex_X_one_sq_mem)
      (Ideal.mul_mem_right _ _ ex_X_one_sq_mem)

/-- **Example 3.4.6, the chart.** In the `x`-chart of the blowup of `C = V(x, y)`, the polynomial
`g = y^2 w + y^3` goes to `x^2 g'` with `g' = y^2 w + x y^3`. -/
theorem centerExample_centerChart :
    centerChart {0, 1} 0 (0 : Fin 3 → ZMod 2) (X 1 ^ 2 * X 2 + X 1 ^ 3) =
      X 0 ^ 2 * (X 1 ^ 2 * X 2 + X 0 * X 1 ^ 3) := by
  simp [centerChart]
  ring

private theorem ex_divisorExponent :
    divisorExponent {2} (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) = 0 := by
  rw [ex_g_eq]
  refine divisorExponent_eq_zero_of fun i hi => ⟨_, mem_support_monomial_add_right ex_ne, ?_⟩
  rw [Finset.mem_singleton.mp hi]
  simp

/-- **Example 3.4.6, the order `ρ(g)`.** For `g = y^2 w + y^3` and the divisor `V(w)`, the
divisor exponent is `0`, and `ρ(g) = 2`. -/
theorem centerExample_logJacobianOrder :
    logJacobianOrder {2} (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) = 2 := by
  rw [logJacobianOrder_eq_idealOrd ex_divisorExponent]
  refine le_antisymm ?_ ?_
  · refine (idealOrd_le_ord (pderiv_mem_logJacobian (j := 1) (by decide) _)).trans ?_
    rw [ex_pderiv_g_one]
    norm_num
  · refine le_idealOrd_span ?_
    rintro s (⟨i, -, rfl⟩ | ⟨l, -, rfl⟩)
    · exact le_ord_X_mul (le_trans (by norm_num) (ex_two_le_ord_pderiv_g i)) i
    · exact le_trans (by norm_num) (ex_two_le_ord_pderiv_g l)

/-- **Example 3.4.6, condition (H1).** For `g = y^2 w + y^3`, the divisor `V(w)` and the center
`C = V(x, y)`, each element of `Θ(g)` is `x^r` times an element of `I_C^ρ`, with `ρ = 2`. -/
theorem centerExample_H1 :
    ∀ f ∈ logJacobian {2} (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)),
      ∃ q ∈ Ideal.span (X '' (({0, 1} : Finset (Fin 3)) : Set (Fin 3))) ^ 2,
        f = monomial (divisorExponent {2} (X 1 ^ 2 * X 2 + X 1 ^ 3 :
          MvPolynomial (Fin 3) (ZMod 2))) 1 * q := by
  have hmem : ∀ l : Fin 3, pderiv l (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) ∈
      Ideal.span (X '' (({0, 1} : Finset (Fin 3)) : Set (Fin 3))) ^ 2 := fun l => by
    rcases ex_pderiv_g_cases l with h | h <;> rw [h]
    · exact Ideal.zero_mem _
    · exact ex_X_one_sq_mem
  have hle : logJacobian {2} (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) ≤
      Ideal.span (X '' (({0, 1} : Finset (Fin 3)) : Set (Fin 3))) ^ 2 := by
    refine Ideal.span_le.mpr ?_
    rintro s (⟨i, -, rfl⟩ | ⟨l, -, rfl⟩)
    · exact Ideal.mul_mem_left _ _ (hmem i)
    · exact hmem l
  intro f hf
  exact ⟨f, hle hf, by rw [ex_divisorExponent, monomial_zero', C_1, one_mul]⟩

private theorem ex_three_le_idealOrd_logJacobianCenter :
    ((2 + 1 : ℕ) : ℕ∞) ≤ idealOrd (logJacobianCenter {2} {0, 1}
      (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2))) := by
  refine le_idealOrd_span ?_
  rintro s ((⟨i, -, rfl⟩ | ⟨l, ⟨hlΔ, hlS⟩, rfl⟩) | ⟨⟨m, l⟩, -, rfl⟩)
  · exact natCast_succ_le_ord_X_mul (ex_two_le_ord_pderiv_g i) i
  · exfalso
    revert hlΔ hlS
    fin_cases l <;> decide
  · exact natCast_succ_le_ord_X_mul (ex_two_le_ord_pderiv_g l) m

/-- **Example 3.4.6, condition (H2) fails.** For `g = y^2 w + y^3`, the divisor `V(w)` and the
center `C = V(x, y)`, with `ρ = 2`, the element `x_w ∂_w g = y^2 w` of `Θ_C(g)` is not in
`I_C^(ρ+1)`, and each element of `Θ_C(g)` has order at least `ρ + 1`. -/
theorem centerExample_not_H2 :
    ¬ ((∀ f ∈ logJacobianCenter {2} {0, 1}
          (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)),
        ∃ q ∈ Ideal.span (X '' (({0, 1} : Finset (Fin 3)) : Set (Fin 3))) ^ (2 + 1),
          f = monomial (divisorExponent {2} (X 1 ^ 2 * X 2 + X 1 ^ 3 :
            MvPolynomial (Fin 3) (ZMod 2))) 1 * q) ∨
      ∃ q, monomial (divisorExponent {2} (X 1 ^ 2 * X 2 + X 1 ^ 3 :
          MvPolynomial (Fin 3) (ZMod 2))) 1 * q ∈ logJacobianCenter {2} {0, 1}
            (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) ∧ ord q = (2 : ℕ)) := by
  rw [ex_divisorExponent, monomial_zero', C_1]
  rintro (h | ⟨q, hq, hqo⟩)
  · obtain ⟨q, hq, he⟩ :=
      h _ (X_mul_pderiv_mem_logJacobianCenter {0, 1} (i := 2) (by decide) _)
    rw [one_mul, ex_pderiv_g_two, X_pow_eq_monomial,
      show (X 2 : MvPolynomial (Fin 3) (ZMod 2)) = monomial (single 2 1) 1 from rfl,
      monomial_mul_monomial, one_mul] at he
    rw [← he] at hq
    have h3 := mem_centerDegreeIdeal.mp (span_X_pow_le_centerDegreeIdeal _ _ hq)
      (single 2 1 + single 1 2) (MvPolynomial.mem_support_iff.mpr (by
        rw [coeff_monomial, ite_eq_left rfl]
        exact one_ne_zero))
    simp [Finsupp.single_apply] at h3
  · rw [one_mul] at hq
    have h3 := ex_three_le_idealOrd_logJacobianCenter.trans (idealOrd_le_ord hq)
    rw [hqo] at h3
    exact absurd (Nat.cast_le.mp h3) (by norm_num)

/-- The new divisor of Example 3.4.6 is `V(x w)`. -/
private theorem ex_centerDivisor :
    centerDivisor ({2} : Finset (Fin 3)) {0, 1} 0 (0 : Fin 3 → ZMod 2) = {0, 2} := by
  decide

private theorem ex_isClean_g' :
    IsClean 2 (X 1 ^ 2 * X 2 + X 0 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) := by
  rw [ex_g'_eq]
  exact isClean_monomial_add ex_not_dvd
    (fun h => absurd (h 1) (by simp)) 1 1

private theorem ex_divisorExponent_g' :
    divisorExponent {0, 2} (X 1 ^ 2 * X 2 + X 0 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) = 0 := by
  rw [ex_g'_eq]
  refine divisorExponent_eq_zero_of fun i hi => ?_
  rcases Finset.mem_insert.mp hi with rfl | hi
  · exact ⟨_, mem_support_monomial_add_left ex_ne', by simp⟩
  · rw [Finset.mem_singleton.mp hi]
    exact ⟨_, mem_support_monomial_add_right ex_ne', by simp⟩

/-- **Example 3.4.6, the order `ρ(g'_c)`.** The polynomial `g' = y^2 w + x y^3` is clean. For the
new divisor `V(x w)`, its divisor exponent is `0`, and `ρ(g'_c) = 3`. So `ρ` goes up from `2` to
`3` when (H2) fails. -/
theorem centerExample_logJacobianOrder_cleanPart :
    logJacobianOrder (centerDivisor ({2} : Finset (Fin 3)) {0, 1} 0 (0 : Fin 3 → ZMod 2))
      (cleanPart 2 (X 1 ^ 2 * X 2 + X 0 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2))) = 3 := by
  rw [ex_centerDivisor, cleanPart_eq_self ex_isClean_g',
    logJacobianOrder_eq_idealOrd ex_divisorExponent_g']
  refine le_antisymm ?_ ?_
  · refine (idealOrd_le_ord (pderiv_mem_logJacobian (j := 1) (by decide) _)).trans ?_
    rw [ex_pderiv_g'_one, ord_X_mul_X_pow]
    norm_num
  · refine le_idealOrd_span ?_
    rintro s (⟨i, -, rfl⟩ | ⟨l, hl, rfl⟩)
    · exact le_trans (by norm_num) (natCast_succ_le_ord_X_mul (ex_two_le_ord_pderiv_g' i) i)
    · have hl1 : l = 1 := by
        revert hl
        fin_cases l <;> decide
      rw [hl1]
      dsimp only
      rw [ex_pderiv_g'_one, ord_X_mul_X_pow]
      norm_num

end Example

end Singularity
