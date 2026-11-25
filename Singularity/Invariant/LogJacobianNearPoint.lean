/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.CossartPiltantOmega
import Singularity.Invariant.Directrix

/-!
# The near points of the log-Jacobian order

Let `k` be a field of characteristic `p`, let `g ≠ 0` be a clean polynomial in `k[x_i : i ∈ σ]`
with `ord g ≥ p`, and let `Δ` give the divisor `E = V(∏_{i ∈ Δ} x_i)`. Write `g = x^r G`, with
`r = divisorExponent Δ g`, and let `ρ = logJacobianOrder Δ g`. In the `x_j`-chart of the blowup of
the origin with translations `t` (`pointChart j t`), write `π(g) = x_j^p g'`, and let `ρ'` be the
order `ρ` of the clean part `g'_c` of `g'` for the new divisor `Δ' = blowupDivisor Δ j t`. Then
`ρ' ≤ ρ` (Volume 7, Section 3.2 of the handbook, Theorem 3.2.4). This file proves that the points
where `ρ` stays lie in a linear subspace (Volume 7, Section 3.7 of the handbook, Theorem 3.7.1).
This is the analogue for `ρ` of the theorem of Hironaka on the near points of the order [Hir67].

Let `v` be the vector of the chart (`chartVector j t`), with `v_j = 1` and `v_i = t_i` for
`i ≠ j`, and let `T(F)` be the directrix of a form `F` (`directrix`). Let `Θ₀(g)` be the ideal
`logJacobianTangent Δ g`. Let `ρ' = ρ = m`.

1. For each `ψ` with `x^r ψ ∈ Θ₀(g)` and `ord ψ = m`, the vector `v` lies in `T(ψ_m)`, with `ψ_m`
   the part of `ψ` of degree `m`.
2. If `ord Θ₀(g) = |r| + m + 1`, then the same holds for each `ψ` with `x^r ψ ∈ Θ(g)` and
   `ord ψ = m`.

The proof. Let `f = x^r ψ` in part 1 and `f = x_j x^r ψ` in part 2. In both cases `f ∈ Θ₀(g)`, and
`ord f` is the order `τ` of `Θ₀(g)`. The chart sends `x^r` to `x_j^|r| x^e U`, with
`e = chartExponent j t r` and a factor `U` with a nonzero constant term (`chartRest_monomial_one`),
and it sends `ψ` to `x_j^m ψ'`. So `π(f) = x_j^τ x^e U ψ'`. As in the proof of Theorem 3.2.4, each
element of `Θ'(g')` is divisible by `x^b`, with `x_j^p x^b = x_j^τ x^e`, and `π(f) = x_j^p φ` with
`φ ∈ Θ'(g')`. Then `ρ' ≤ ord φ - |b| = ord ψ'`
(`logJacobianOrder_cleanPart_le_of_ord_pointChart_le`). So `m ≤ ord ψ'`, and `v` lies in the
directrix of `ψ_m` by the argument of Hironaka (`mem_directrix_of_le_ord_pointChart`).

Part 1 cannot use `Θ(g)` in the place of `Θ₀(g)`. Over `𝔽₃`, for `g = x^3 y^2 + x^4` and
`E = V(x)`, the order `ρ` stays `1` at the origin of the `y`-chart, and `ψ = 2 y` has
`x^r ψ = ∂_y g ∈ Θ(g)` and `ord ψ = 1`, but `v = (0, 1)` is not in `T(2 y)` (Example 3.7.4).

## Main results

* `logJacobianOrder_cleanPart_le_of_ord_pointChart_le`: the bound `ρ' ≤ n` from an element `f` of
  `Θ₀(g)` with `ord π(f) ≤ τ + |e| + n`. The proof of Theorem 3.2.4 uses the same bound.
* `chartVector_mem_directrix_of_logJacobianOrder_eq`: Theorem 3.7.1, part 1.
* `chartVector_mem_directrix_of_logJacobianOrder_eq_of_idealOrd`: Theorem 3.7.1, part 2.
* `logJacobianOrder_cleanPart_lt_of_directrix_eq_bot`,
  `logJacobianOrder_cleanPart_lt_of_directrix_eq_bot_of_idealOrd`: Corollary 3.7.2, if the
  directrix of `ψ_m` is `0`, then `ρ` goes down at each point of the exceptional divisor.
* `chartVector_mem_directrix_initialForm_of_logJacobianOrder_eq`,
  `chartVector_mem_directrix_pderiv_initialForm_of_logJacobianOrder_eq`: Corollary 3.7.3, the
  directrices of the initial form `in(G)` of `G` and of its derivatives `∂_l in(G)`, `l ∉ Δ`.
* `nearPointExample_hyp`, `nearPointExample_pointChart`, `nearPointExample_tangent`,
  `nearPointExample_not_mem_directrix`: Example 3.7.4.

## References

* [Hir67] H. Hironaka, *Characteristic polyhedra of singularities*, J. Math. Kyoto Univ. 7 (1967).
* Volume 7, Section 3.7 of the handbook: Theorem 3.7.1, Corollaries 3.7.2 and 3.7.3, and
  Example 3.7.4.
-/

open MvPolynomial Finsupp

namespace Singularity

/-! ### The bound from an element of `Θ₀(g)` -/

section Bound

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- **The bound on `ρ'` from an element of `Θ₀(g)`.** Let `g ≠ 0` be clean with `ord g ≥ p`, let
`π(g) = x_j^p g'`, and let `τ` be the order of `Θ₀(g)`. If `f ∈ Θ₀(g)` and
`ord π(f) ≤ τ + |e| + n`, with `e = chartExponent j t r`, then `ρ(g'_c) ≤ n`. The proof is the
proof of Theorem 3.2.4 (Volume 7, Section 3.2 of the handbook): each element of `Θ'(g')` is
divisible by `x^b` with `x_j^p x^b = x_j^τ x^e`, and `π(f) = x_j^p φ` with `φ ∈ Θ'(g')` and
`ord φ ≤ |b| + n`. -/
theorem logJacobianOrder_cleanPart_le_of_ord_pointChart_le (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {τ : ℕ}
    (hτ : idealOrd (logJacobianTangent Δ g) = τ) {f : MvPolynomial σ k}
    (hf : f ∈ logJacobianTangent Δ g) {n : ℕ∞}
    (hn : ord (pointChart j t f) ≤
      ((τ + degree (chartExponent j t (divisorExponent Δ g)) : ℕ) : ℕ∞) + n) :
    logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') ≤ n := by
  -- Each element of `Θ₀(g)` is divisible by `x^r`.
  have hdvd₀ : ∀ f ∈ logJacobianTangent Δ g, monomial (divisorExponent Δ g) (1 : k) ∣ f :=
    fun f hf => Ideal.mem_span_singleton.mp
      (logJacobian_le_span_monomial Δ g (logJacobianTangent_le Δ g hf))
  -- `p ≤ τ` and `|r| ≤ τ`.
  have hpτ : p ≤ τ := by
    have := le_idealOrd_logJacobianTangent (Δ := Δ) hord
    rw [hτ] at this
    exact_mod_cast this
  have hrτ : degree (divisorExponent Δ g) ≤ τ := by
    obtain ⟨h₀, hh₀, hord₀⟩ := exists_mem_ord_eq_idealOrd (logJacobianTangent Δ g)
    rw [hτ] at hord₀
    obtain ⟨q, hq⟩ := hdvd₀ h₀ hh₀
    have : ((degree (divisorExponent Δ g) : ℕ) : ℕ∞) ≤ τ := by
      rw [← hord₀, hq, ord_mul, ord_monomial one_ne_zero]
      exact le_self_add
    exact_mod_cast this
  -- `π(Θ₀(g)) ⊆ (x_j^τ x^e)`.
  have hB1 : Ideal.map (pointChart j t) (logJacobianTangent Δ g) ≤
      Ideal.span {X j ^ τ * monomial (chartExponent j t (divisorExponent Δ g)) (1 : k)} := by
    have := map_pointChart_span_le (j := j) (t := t) (S := (logJacobianTangent Δ g : Set _))
      (c := τ - degree (divisorExponent Δ g)) fun s hs => ⟨hdvd₀ s hs, by
        rw [Nat.add_sub_cancel' hrτ, ← hτ]
        exact idealOrd_le_ord hs⟩
    rwa [Ideal.span_eq, Nat.add_sub_cancel' hrτ] at this
  -- The monomial `x^b` with `x_j^p x^b = x_j^τ x^e`.
  have hXb : X j ^ τ * monomial (chartExponent j t (divisorExponent Δ g)) (1 : k) =
      X j ^ p * monomial (single j (τ - p) + chartExponent j t (divisorExponent Δ g)) 1 := by
    rw [monomial_single_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hpτ]
  have hb : ∀ i, i ∉ blowupDivisor Δ j t →
      (single j (τ - p) + chartExponent j t (divisorExponent Δ g)) i = 0 :=
    fun i hi => chartN_eq_zero (fun l hl => divisorExponent_eq_zero hl) (τ - p) hi
  have hdb : degree (single j (τ - p) + chartExponent j t (divisorExponent Δ g)) =
      τ - p + degree (chartExponent j t (divisorExponent Δ g)) := by
    rw [map_add, degree_single]
  -- `Θ'(g') ⊆ (x^b)`.
  have hB : logJacobian (blowupDivisor Δ j t) g' ≤
      Ideal.span {monomial (single j (τ - p) + chartExponent j t (divisorExponent Δ g)) 1} := by
    intro φ hφ
    have h2 := span_mul_logJacobian_le_map_pointChart p (Δ := Δ) h
      (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hφ)
    have h3 := Ideal.mem_span_singleton.mp (hB1 h2)
    rw [hXb, mul_assoc] at h3
    have h4 := (mul_dvd_mul_iff_left (pow_ne_zero p (X_ne_zero j))).mp h3
    exact Ideal.mem_span_singleton.mpr
      (monomial_one_dvd_of_dvd_mul (constantCoeff_blowupUnit_ne_zero Δ j t) h4)
  -- `π(f) = x_j^p φ` with `φ ∈ Θ'(g')` and `ord φ ≤ |b| + n`.
  obtain ⟨φ, hφ, hφeq⟩ := Ideal.mem_span_singleton_mul.mp
    (map_pointChart_logJacobianTangent_le_span_mul p (Δ := Δ) h (Ideal.mem_map_of_mem _ hf))
  have h5 : ord (pointChart j t f) = p + ord φ := by
    rw [← hφeq, ord_mul, ord_X_pow]
  have hφo : ord φ ≤
      ((τ - p + degree (chartExponent j t (divisorExponent Δ g)) : ℕ) : ℕ∞) + n := by
    have h6 : (p : ℕ∞) + ord φ ≤ (p : ℕ∞) +
        (((τ - p + degree (chartExponent j t (divisorExponent Δ g)) : ℕ) : ℕ∞) + n) := by
      rw [← h5, ← add_assoc, ← Nat.cast_add,
        show p + (τ - p + degree (chartExponent j t (divisorExponent Δ g))) =
          τ + degree (chartExponent j t (divisorExponent Δ g)) by omega]
      exact hn
    exact (ENat.add_le_add_iff_left (ENat.natCast_ne_top p)).mp h6
  have hcl := (logJacobianOrder_cleanPart_le p (Δ := Δ) hg hc hord h).1
  refine logJacobianOrder_le_of_mem p hcl (isClean_cleanPart p g') hb (φ := φ) ?_ ?_ ?_
  · rw [logJacobian_cleanPart]
    exact hB
  · rw [logJacobian_cleanPart]
    exact hφ
  · rw [hdb]
    exact hφo

/-- If `f ∈ Θ₀(g)` and `π(f) = x_j^τ x^e U ψ'`, with `τ` the order of `Θ₀(g)`,
`e = chartExponent j t r` and `U = chartUnit j t r`, then `ρ(g'_c) ≤ ord ψ'`. -/
theorem logJacobianOrder_cleanPart_le_ord_of_pointChart_eq (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {τ : ℕ}
    (hτ : idealOrd (logJacobianTangent Δ g) = τ) {f ψ' : MvPolynomial σ k}
    (hf : f ∈ logJacobianTangent Δ g)
    (hπ : pointChart j t f = X j ^ τ * (monomial (chartExponent j t (divisorExponent Δ g)) 1 *
      (chartUnit j t (divisorExponent Δ g) * ψ'))) :
    logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') ≤ ord ψ' := by
  refine logJacobianOrder_cleanPart_le_of_ord_pointChart_le p hg hc hord h hτ hf (le_of_eq ?_)
  rw [hπ, ord_mul, ord_mul, ord_mul, ord_X_pow, ord_monomial one_ne_zero, ord_chartUnit, zero_add,
    Nat.cast_add, add_assoc]

end Bound

/-! ### The theorem -/

section NearPoint

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

omit [Fintype σ] in
/-- The chart sends `x^r ψ` to `x_j^(|r| + m) x^e U ψ'` if it sends `ψ` to `x_j^m ψ'`. -/
theorem pointChart_monomial_mul_eq {r : σ →₀ ℕ} {m : ℕ} {ψ ψ' : MvPolynomial σ k}
    (hψ' : pointChart j t ψ = X j ^ m * ψ') :
    pointChart j t (monomial r 1 * ψ) = X j ^ (degree r + m) *
      (monomial (chartExponent j t r) 1 * (chartUnit j t r * ψ')) := by
  rw [map_mul, pointChart_monomial, chartRest_monomial_one, hψ', pow_add]
  ring

/-- **The near points of `ρ`, part 1** (Volume 7, Section 3.7 of the handbook, Theorem 3.7.1).
Let `g ≠ 0` be clean with `ord g ≥ p`, let `π(g) = x_j^p g'` in the chart `π = pointChart j t`,
and let `ρ(g'_c) = ρ(g) = m` for the new divisor `Δ' = blowupDivisor Δ j t`. Then for each `ψ`
with `x^r ψ ∈ Θ₀(g)` and `ord ψ = m`, the vector of the chart lies in the directrix of the part
`ψ_m` of `ψ` of degree `m`. -/
theorem chartVector_mem_directrix_of_logJacobianOrder_eq (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m) {ψ : MvPolynomial σ k}
    (hψ : monomial (divisorExponent Δ g) 1 * ψ ∈ logJacobianTangent Δ g) (hψo : ord ψ = m) :
    chartVector j t ∈ directrix (homogeneousComponent m ψ) := by
  -- The order of `Θ₀(g)` is `|r| + m`.
  have hτ : idealOrd (logJacobianTangent Δ g) = ((degree (divisorExponent Δ g) + m : ℕ) : ℕ∞) := by
    refine le_antisymm ((idealOrd_le_ord hψ).trans (le_of_eq ?_)) ?_
    · rw [ord_mul, ord_monomial one_ne_zero, hψo, Nat.cast_add]
    · rw [Nat.cast_add, ← hρ, ← idealOrd_logJacobian]
      exact idealOrd_anti (logJacobianTangent_le Δ g)
  obtain ⟨ψ', hψ'⟩ := exists_pointChart_eq_X_pow_mul (j := j) (t := t) hψo.ge
  have hle := logJacobianOrder_cleanPart_le_ord_of_pointChart_eq p hg hc hord h hτ hψ
    (pointChart_monomial_mul_eq hψ')
  rw [hρ'] at hle
  exact mem_directrix_of_le_ord_pointChart hψo.ge hψ' hle

/-- **The near points of `ρ`, part 2** (Volume 7, Section 3.7 of the handbook, Theorem 3.7.1).
Let `g ≠ 0` be clean with `ord g ≥ p`, let `π(g) = x_j^p g'` in the chart `π = pointChart j t`, let
`ρ(g'_c) = m` for the new divisor `Δ' = blowupDivisor Δ j t`, and let the order of `Θ₀(g)` be
`|r| + m + 1`. Then for each `ψ` with `x^r ψ ∈ Θ(g)` and `ord ψ = m`, the vector of the chart lies
in the directrix of the part `ψ_m` of `ψ` of degree `m`. The hypotheses give `ρ(g) = m`: the
element `x^r ψ` of `Θ(g)` gives `ρ(g) ≤ m`, and `ord Θ₀(g) ≤ |r| + ρ(g) + 1` gives `m ≤ ρ(g)`. -/
theorem chartVector_mem_directrix_of_logJacobianOrder_eq_of_idealOrd (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m)
    (hτ : idealOrd (logJacobianTangent Δ g) = ((degree (divisorExponent Δ g) + m + 1 : ℕ) : ℕ∞))
    {ψ : MvPolynomial σ k} (hψ : monomial (divisorExponent Δ g) 1 * ψ ∈ logJacobian Δ g)
    (hψo : ord ψ = m) :
    chartVector j t ∈ directrix (homogeneousComponent m ψ) := by
  have hf : X j * (monomial (divisorExponent Δ g) 1 * ψ) ∈ logJacobianTangent Δ g :=
    span_range_X_mul_logJacobian_le Δ g (Ideal.mul_mem_mul (Ideal.subset_span ⟨j, rfl⟩) hψ)
  obtain ⟨ψ', hψ'⟩ := exists_pointChart_eq_X_pow_mul (j := j) (t := t) hψo.ge
  have hπ : pointChart j t (X j * (monomial (divisorExponent Δ g) 1 * ψ)) =
      X j ^ (degree (divisorExponent Δ g) + m + 1) *
        (monomial (chartExponent j t (divisorExponent Δ g)) 1 *
          (chartUnit j t (divisorExponent Δ g) * ψ')) := by
    rw [map_mul, pointChart_X_self, pointChart_monomial_mul_eq hψ', pow_succ]
    ring
  have hle := logJacobianOrder_cleanPart_le_ord_of_pointChart_eq p hg hc hord h hτ hf hπ
  rw [hρ'] at hle
  exact mem_directrix_of_le_ord_pointChart hψo.ge hψ' hle

omit [DecidableEq k] [Fintype σ] in
/-- The vector of a chart is not `0`: its entry at `j` is `1`. -/
theorem chartVector_ne_zero (j : σ) (t : σ → k) : chartVector j t ≠ 0 := by
  intro h0
  have := congrFun h0 j
  simp [chartVector] at this

/-- **`ρ` goes down if the directrix is `0`, case A** (Volume 7, Section 3.7 of the handbook,
Corollary 3.7.2). Let `g ≠ 0` be clean with `ord g ≥ p` and `ρ(g) = m`. If some `ψ` with
`x^r ψ ∈ Θ₀(g)` and `ord ψ = m` has a directrix `T(ψ_m) = 0`, then `ρ(g'_c) < m` in each chart
`π = pointChart j t` with `π(g) = x_j^p g'`. -/
theorem logJacobianOrder_cleanPart_lt_of_directrix_eq_bot (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m) {ψ : MvPolynomial σ k}
    (hψ : monomial (divisorExponent Δ g) 1 * ψ ∈ logJacobianTangent Δ g) (hψo : ord ψ = m)
    (hT : directrix (homogeneousComponent m ψ) = ⊥) :
    logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') < m := by
  have hle := (logJacobianOrder_cleanPart_le p (Δ := Δ) hg hc hord h).2
  rw [hρ] at hle
  refine lt_of_le_of_ne hle fun heq => chartVector_ne_zero j t ?_
  have := chartVector_mem_directrix_of_logJacobianOrder_eq p hg hc hord h hρ heq hψ hψo
  rwa [hT, Submodule.mem_bot] at this

/-- **`ρ` goes down if the directrix is `0`, case B** (Volume 7, Section 3.7 of the handbook,
Corollary 3.7.2). Let `g ≠ 0` be clean with `ord g ≥ p`, and let the order of `Θ₀(g)` be
`|r| + m + 1`. If some `ψ` with `x^r ψ ∈ Θ(g)` and `ord ψ = m` has a directrix `T(ψ_m) = 0`, then
`ρ(g'_c) < m` in each chart `π = pointChart j t` with `π(g) = x_j^p g'`. -/
theorem logJacobianOrder_cleanPart_lt_of_directrix_eq_bot_of_idealOrd (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hτ : idealOrd (logJacobianTangent Δ g) = ((degree (divisorExponent Δ g) + m + 1 : ℕ) : ℕ∞))
    {ψ : MvPolynomial σ k} (hψ : monomial (divisorExponent Δ g) 1 * ψ ∈ logJacobian Δ g)
    (hψo : ord ψ = m) (hT : directrix (homogeneousComponent m ψ) = ⊥) :
    logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') < m := by
  -- `ρ(g) ≤ m`, from the element `x^r ψ` of `Θ(g)`.
  have hρ : logJacobianOrder Δ g ≤ m := by
    have h1 : ((degree (divisorExponent Δ g) : ℕ) : ℕ∞) + logJacobianOrder Δ g ≤
        degree (divisorExponent Δ g) + m := by
      rw [← idealOrd_logJacobian]
      refine (idealOrd_le_ord hψ).trans (le_of_eq ?_)
      rw [ord_mul, ord_monomial one_ne_zero, hψo]
    exact (ENat.add_le_add_iff_left (ENat.natCast_ne_top _)).mp h1
  have hle := (logJacobianOrder_cleanPart_le p (Δ := Δ) hg hc hord h).2.trans hρ
  refine lt_of_le_of_ne hle fun heq => chartVector_ne_zero j t ?_
  have := chartVector_mem_directrix_of_logJacobianOrder_eq_of_idealOrd p hg hc hord h heq hτ hψ hψo
  rwa [hT, Submodule.mem_bot] at this

end NearPoint

/-! ### The initial forms -/

section InitialForm

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

omit [DecidableEq σ] [DecidableEq k] [Fintype σ] in
/-- The directrix of `c F` is the directrix of `F` for a constant `c ≠ 0`. -/
theorem directrix_smul {c : k} (hc : c ≠ 0) (F : MvPolynomial σ k) :
    directrix (c • F) = directrix F := by
  ext v
  rw [mem_directrix_iff, mem_directrix_iff, map_smul, map_smul]
  exact (smul_right_injective _ hc).eq_iff

omit [DecidableEq σ] [DecidableEq k] [Fintype σ] in
/-- If the part of `f` of degree `m` is not `0`, then `ord f ≤ m`. -/
theorem ord_le_of_homogeneousComponent_ne_zero {f : MvPolynomial σ k} {m : ℕ}
    (h : homogeneousComponent m f ≠ 0) : ord f ≤ m := by
  obtain ⟨a, ha⟩ := MvPolynomial.ne_zero_iff.mp h
  rw [coeff_homogeneousComponent] at ha
  split_ifs at ha with hdeg
  · rw [← hdeg]
    exact ord_le ha
  · exact absurd rfl ha

omit [DecidableEq σ] [DecidableEq k] [Fintype σ] in
/-- The part of degree `d - 1` of `∂_l G` is `∂_l` of the part of degree `d` of `G`, for
`d ≥ 1`. -/
theorem homogeneousComponent_pderiv {d : ℕ} (hd : 1 ≤ d) (l : σ) (G : MvPolynomial σ k) :
    homogeneousComponent (d - 1) (pderiv l G) = pderiv l (homogeneousComponent d G) := by
  classical
  ext a
  simp only [coeff_homogeneousComponent, coeff_pderiv, map_add (Finsupp.degree (σ := σ) (R := ℕ)),
    degree_single]
  by_cases ha : degree a = d - 1
  · rw [ite_eq_left ha, ite_eq_left (by omega)]
  · rw [ite_eq_right ha, ite_eq_right (by omega), zero_mul]

omit [DecidableEq σ] [DecidableEq k] in
/-- The Euler sum of `g = x^r G`: `∑_i x_i ∂_i (x^r G) = x^r ∑_i (r_i G + x_i ∂_i G)`. -/
theorem sum_X_mul_pderiv_monomial_mul (r : σ →₀ ℕ) (G : MvPolynomial σ k) :
    ∑ i, X i * pderiv i (monomial r 1 * G) =
      monomial r 1 * ∑ i, ((r i : k) • G + X i * pderiv i G) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : X i * pderiv i (monomial r (1 : k)) = (r i : k) • monomial r 1 := by
    rw [X_mul_pderiv_monomial, Nat.cast_smul_eq_nsmul]
  calc X i * pderiv i (monomial r 1 * G)
      = X i * pderiv i (monomial r 1) * G + monomial r 1 * (X i * pderiv i G) := by
        rw [pderiv_mul]
        ring
    _ = monomial r 1 * ((r i : k) • G + X i * pderiv i G) := by
        rw [h1, smul_mul_assoc, ← mul_smul_comm, ← mul_add]

omit [DecidableEq σ] [DecidableEq k] in
/-- The polynomial `∑_i (r_i G + x_i ∂_i G)` multiplies the monomial `x^a` of `G` by
`|r| + |a|`. -/
theorem coeff_sum_smul_add_X_mul_pderiv (r : σ →₀ ℕ) (G : MvPolynomial σ k) (a : σ →₀ ℕ) :
    (∑ i, ((r i : k) • G + X i * pderiv i G)).coeff a =
      ((degree r + degree a : ℕ) : k) * G.coeff a := by
  rw [coeff_sum]
  simp_rw [coeff_smul_add_X_mul_pderiv]
  rw [← Finset.sum_mul, degree_eq_sum r, degree_eq_sum a, ← Finset.sum_add_distrib]
  push_cast
  rfl

/-- **The directrix of the initial form, case `ρ = ord G`** (Volume 7, Section 3.7 of the
handbook, Corollary 3.7.3). Let `g ≠ 0` be clean with `ord g ≥ p`, let `π(g) = x_j^p g'` in the
chart `π = pointChart j t`, let `d = ord G` with `G = residualFactor Δ g`, and let
`ρ(g'_c) = ρ(g) = d`. If `|r| + d` is not `0` in `k`, then the vector of the chart lies in the
directrix of the initial form `in(G)`, the part of `G` of degree `d`. The proof applies part 1 of
Theorem 3.7.1 to `ψ = ∑_i (r_i G + x_i ∂_i G)`: then `x^r ψ = ∑_i x_i ∂_i g ∈ Θ₀(g)`, and
`ψ_d = (|r| + d) in(G)` by the Euler identity. -/
theorem chartVector_mem_directrix_initialForm_of_logJacobianOrder_eq (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hG : ord (residualFactor Δ g) = d) (hρ : logJacobianOrder Δ g = d)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d)
    (hpd : ((degree (divisorExponent Δ g) + d : ℕ) : k) ≠ 0) :
    chartVector j t ∈ directrix (homogeneousComponent d (residualFactor Δ g)) := by
  have hmem : monomial (divisorExponent Δ g) 1 * ∑ i, ((divisorExponent Δ g i : k) •
      residualFactor Δ g + X i * pderiv i (residualFactor Δ g)) ∈ logJacobianTangent Δ g := by
    rw [← sum_X_mul_pderiv_monomial_mul, monomial_mul_residualFactor]
    exact Ideal.sum_mem _ fun i _ => X_mul_pderiv_mem_logJacobianTangent' Δ i g
  have hcoeff := coeff_sum_smul_add_X_mul_pderiv (divisorExponent Δ g) (residualFactor Δ g)
  have hG0 : residualFactor Δ g ≠ 0 := by
    rintro h0
    rw [h0, ord_zero] at hG
    exact ENat.top_ne_natCast d hG
  have hψo : ord (∑ i, ((divisorExponent Δ g i : k) • residualFactor Δ g +
      X i * pderiv i (residualFactor Δ g))) = d := by
    refine le_antisymm ?_ (le_ord_iff.mpr fun a ha => ?_)
    · obtain ⟨a, ha, had⟩ := exists_coeff_ne_zero_and_ord_eq hG0
      have hda : degree a = d := by
        rw [hG] at had
        exact_mod_cast had.symm
      refine (ord_le (d := a) ?_).trans (le_of_eq (by rw [hda]))
      rw [hcoeff, hda]
      exact mul_ne_zero hpd ha
    · rw [hcoeff, coeff_eq_zero_of_lt_ord (by rw [hG]; exact_mod_cast ha), mul_zero]
  have hhc : homogeneousComponent d (∑ i, ((divisorExponent Δ g i : k) • residualFactor Δ g +
      X i * pderiv i (residualFactor Δ g))) =
      ((degree (divisorExponent Δ g) + d : ℕ) : k) •
        homogeneousComponent d (residualFactor Δ g) := by
    ext a
    rw [coeff_homogeneousComponent, coeff_smul, coeff_homogeneousComponent, hcoeff, smul_eq_mul]
    split_ifs with ha
    · rw [ha]
    · rw [mul_zero]
  have := chartVector_mem_directrix_of_logJacobianOrder_eq p hg hc hord h hρ hρ' hmem hψo
  rwa [hhc, directrix_smul hpd] at this

/-- **The directrix of the derivatives of the initial form, case `ρ = ord G - 1`** (Volume 7,
Section 3.7 of the handbook, Corollary 3.7.3). Let `g ≠ 0` be clean with `ord g ≥ p`, let
`π(g) = x_j^p g'` in the chart `π = pointChart j t`, and let `d = ord G` with
`G = residualFactor Δ g`. Let `l ∉ Δ` with `∂_l in(G) ≠ 0`, so that `ρ(g) = d - 1`. If
`ρ(g'_c) = d - 1`, then the vector of the chart lies in the directrix of `∂_l in(G)`. The proof
applies part 2 of Theorem 3.7.1 to `ψ = ∂_l G`: then `x^r ψ = ∂_l g ∈ Θ(g)`, and the order of
`Θ₀(g)` is `ord g = |r| + d`. -/
theorem chartVector_mem_directrix_pderiv_initialForm_of_logJacobianOrder_eq (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hG : ord (residualFactor Δ g) = d) {l : σ} (hl : l ∉ Δ)
    (hne : pderiv l (homogeneousComponent d (residualFactor Δ g)) ≠ 0)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = (d - 1 : ℕ)) :
    chartVector j t ∈ directrix (pderiv l (homogeneousComponent d (residualFactor Δ g))) := by
  have hd1 : 1 ≤ d := by
    by_contra hd0
    obtain rfl : d = 0 := by omega
    rw [homogeneousComponent_zero, pderiv_C] at hne
    exact hne rfl
  have hhc := homogeneousComponent_pderiv hd1 l (residualFactor Δ g)
  have hψ : monomial (divisorExponent Δ g) 1 * pderiv l (residualFactor Δ g) ∈ logJacobian Δ g := by
    rw [← pderiv_monomial_mul_of_eq_zero (divisorExponent_eq_zero hl), monomial_mul_residualFactor]
    exact pderiv_mem_logJacobian hl g
  have hψo : ord (pderiv l (residualFactor Δ g)) = (d - 1 : ℕ) := by
    refine le_antisymm ?_ (le_ord_pderiv hG.ge l)
    refine ord_le_of_homogeneousComponent_ne_zero ?_
    rwa [hhc]
  have hgo : ord g = ((degree (divisorExponent Δ g) + d : ℕ) : ℕ∞) := by
    conv_lhs => rw [← monomial_mul_residualFactor Δ g]
    rw [ord_mul, ord_monomial one_ne_zero, hG, Nat.cast_add]
  have hτ : idealOrd (logJacobianTangent Δ g) =
      ((degree (divisorExponent Δ g) + (d - 1) + 1 : ℕ) : ℕ∞) := by
    rw [show degree (divisorExponent Δ g) + (d - 1) + 1 = degree (divisorExponent Δ g) + d by
      omega]
    refine le_antisymm ?_ (le_idealOrd_logJacobianTangent hgo.ge)
    refine (idealOrd_le_ord (X_mul_pderiv_mem_logJacobianTangent_of_notMem hl l g)).trans
      (le_of_eq ?_)
    have hpl : pderiv l g = monomial (divisorExponent Δ g) 1 * pderiv l (residualFactor Δ g) := by
      conv_lhs => rw [← monomial_mul_residualFactor Δ g]
      rw [pderiv_monomial_mul_of_eq_zero (divisorExponent_eq_zero hl)]
    rw [hpl, ord_mul, ord_mul, ord_X, ord_monomial one_ne_zero, hψo]
    exact_mod_cast (by omega : 1 + (degree (divisorExponent Δ g) + (d - 1)) =
      degree (divisorExponent Δ g) + d)
  have := chartVector_mem_directrix_of_logJacobianOrder_eq_of_idealOrd p hg hc hord h hρ' hτ hψ hψo
  rwa [hhc] at this

end InitialForm

/-! ### Example 3.7.4 -/

section Example

/-- In characteristic `3`, the constant `3` is `0`. -/
theorem three_eq_zero_mvPolynomial_zmod (τ : Type*) : (3 : MvPolynomial τ (ZMod 3)) = 0 := by
  rw [show (3 : MvPolynomial τ (ZMod 3)) = C 3 from (map_ofNat C 3).symm,
    show (3 : ZMod 3) = 0 from rfl, C_0]

private theorem nex_g_eq : (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3)) =
    monomial (single 0 3 + single 1 2) 1 + monomial (single 0 4) 1 := by
  simp only [X_pow_eq_monomial, monomial_mul_monomial, one_mul]

private theorem nex_g'_eq : (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 * X 1 : MvPolynomial (Fin 2) (ZMod 3)) =
    monomial (single 0 3 + single 1 2) 1 + monomial (single 0 4 + single 1 1) 1 := by
  simp only [X_pow_eq_monomial]
  rw [show (X 1 : MvPolynomial (Fin 2) (ZMod 3)) = monomial (single 1 1) 1 from rfl]
  simp only [monomial_mul_monomial, one_mul]

private theorem nex_ne : (single 0 3 + single 1 2 : Fin 2 →₀ ℕ) ≠ single 0 4 := by
  intro h
  have := DFunLike.congr_fun h 1
  simp at this

private theorem nex_ne' : (single 0 3 + single 1 2 : Fin 2 →₀ ℕ) ≠ single 0 4 + single 1 1 := by
  intro h
  have := DFunLike.congr_fun h 1
  simp at this

private theorem nex_isClean (b : Fin 2 →₀ ℕ) (hb : ¬ ∀ i, 3 ∣ b i) :
    IsClean 3 (monomial (single 0 3 + single 1 2) (1 : ZMod 3) + monomial b 1) :=
  isClean_monomial_add (fun h => absurd (h 1) (by norm_num)) hb 1 1

/-- **Example 3.7.4, the data.** Over `𝔽₃`, the polynomial `g = x^3 y^2 + x^4` is not `0`, is
clean for `p = 3`, and has order at least `3`. -/
theorem nearPointExample_hyp :
    (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3)) ≠ 0 ∧
      IsClean 3 (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3)) ∧
      ((3 : ℕ) : ℕ∞) ≤ ord (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [nex_g_eq]
    exact MvPolynomial.ne_zero_iff.mpr
      ⟨_, MvPolynomial.mem_support_iff.mp (mem_support_monomial_add_right nex_ne)⟩
  · rw [nex_g_eq]
    exact nex_isClean (single 0 4) fun h => absurd (h 0) (by norm_num)
  · refine le_ord_add ?_ ?_
    · rw [ord_mul, ord_X_pow, ord_X_pow]
      norm_num
    · rw [ord_X_pow]
      norm_num

/-- **Example 3.7.4, the chart.** In the `y`-chart of the blowup of the origin, the polynomial
`g = x^3 y^2 + x^4` goes to `y^3 g'` with `g' = x^3 y^2 + x^4 y`. -/
theorem nearPointExample_pointChart :
    pointChart 1 (0 : Fin 2 → ZMod 3) (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4) =
      X 1 ^ 3 * (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 * X 1) := by
  simp [pointChart]
  ring

/-- **Example 3.7.4, the divisor exponent.** For `g = x^3 y^2 + x^4` and `E = V(x)`,
`r = (3, 0)`. -/
theorem nearPointExample_divisorExponent :
    divisorExponent {0} (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3)) =
      single 0 3 := by
  have hg0 := nearPointExample_hyp.1
  rw [nex_g_eq] at hg0 ⊢
  have h1 := divisorExponent_le (Δ := {0}) (mem_support_monomial_add_left (k := ZMod 3) nex_ne)
  have h2 : (single 0 3 : Fin 2 →₀ ℕ) ≤ divisorExponent ({0} : Finset (Fin 2))
      (monomial (single 0 3 + single 1 2) (1 : ZMod 3) + monomial (single 0 4) 1) := by
    refine le_divisorExponent hg0 (fun i hi => ?_) fun β hβ => ?_
    · rw [Finset.mem_singleton] at hi
      simp [Ne.symm hi]
    · rcases Finset.mem_union.mp (MvPolynomial.support_add hβ) with h | h <;>
        obtain rfl := Finset.mem_singleton.mp (support_monomial_subset h) <;>
        intro i <;> fin_cases i <;> simp
  ext i
  fin_cases i
  · exact le_antisymm (by simpa using h1 0) (by simpa using h2 0)
  · simpa using divisorExponent_eq_zero (Δ := {0}) (P := monomial (single 0 3 + single 1 2)
      (1 : ZMod 3) + monomial (single 0 4) 1) (i := 1) (by decide)

private theorem nex_two : (2 : MvPolynomial (Fin 2) (ZMod 3)) = C 2 := (map_ofNat C 2).symm

private theorem nex_ord_two_X : ord (2 * X 1 : MvPolynomial (Fin 2) (ZMod 3)) = 1 := by
  rw [nex_two, ord_mul, ord_C (by decide), ord_X, zero_add]

private theorem nex_pderiv_g_zero :
    pderiv 0 (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3)) = X 0 ^ 3 := by
  simp [pderiv_X]
  linear_combination (X 0 ^ 2 * X 1 ^ 2 + X 0 ^ 3 : MvPolynomial (Fin 2) (ZMod 3)) *
    three_eq_zero_mvPolynomial_zmod (Fin 2)

private theorem nex_pderiv_g_one :
    pderiv 1 (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3)) =
      monomial (single 0 3) 1 * (2 * X 1) := by
  rw [← X_pow_eq_monomial]
  simp [pderiv_X]

private theorem nex_ord_g :
    ((4 : ℕ) : ℕ∞) ≤ ord (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3)) := by
  refine le_ord_add ?_ ?_
  · rw [ord_mul, ord_X_pow, ord_X_pow]
    norm_num
  · exact (ord_X_pow _ _).ge

private theorem nex_ord_g' :
    ((5 : ℕ) : ℕ∞) ≤ ord (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 * X 1 : MvPolynomial (Fin 2) (ZMod 3)) := by
  refine le_ord_add ?_ ?_
  · rw [ord_mul, ord_X_pow, ord_X_pow]
    norm_num
  · rw [ord_mul, ord_X_pow, ord_X]
    norm_num

/-- **Example 3.7.4, the order `ρ(g)`.** For `g = x^3 y^2 + x^4` and `E = V(x)`, `ρ(g) = 1`. -/
theorem nearPointExample_logJacobianOrder :
    logJacobianOrder {0} (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3)) = 1 := by
  have hI := idealOrd_logJacobian {0} (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3))
  rw [nearPointExample_divisorExponent, degree_single] at hI
  have h4 : idealOrd (logJacobian {0}
      (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3))) = ((4 : ℕ) : ℕ∞) := by
    refine le_antisymm ?_ ?_
    · refine (idealOrd_le_ord (pderiv_mem_logJacobian (j := 1) (by decide) _)).trans ?_
      rw [nex_pderiv_g_one, ord_mul, ord_monomial one_ne_zero, nex_ord_two_X, degree_single]
      norm_num
    · refine le_idealOrd_span ?_
      rintro s (⟨i, -, rfl⟩ | ⟨l, hl, rfl⟩)
      · have := le_ord_smul_add_X_mul_pderiv nex_ord_g 0 i
        rwa [Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_smul, zero_add] at this
      · have hl1 : l = 1 := by
          revert hl
          fin_cases l <;> decide
        rw [hl1]
        dsimp only
        rw [nex_pderiv_g_one, ord_mul, ord_monomial one_ne_zero, nex_ord_two_X, degree_single]
        norm_num
  rw [h4] at hI
  cases h : logJacobianOrder {0} (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3))
    using ENat.recTopCoe with
  | top =>
    rw [h, add_top] at hI
    exact absurd hI (ENat.natCast_ne_top 4)
  | coe a =>
    rw [h] at hI
    have : 4 = 3 + a := by exact_mod_cast hI
    exact_mod_cast (by omega : a = 1)

/-- The divisor exponent of `g' = x^3 y^2 + x^4 y` for the new divisor `V(x y)` is `(3, 1)`. -/
private theorem nex_divisorExponent' :
    divisorExponent {0, 1} (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 * X 1 : MvPolynomial (Fin 2) (ZMod 3)) =
      single 0 3 + single 1 1 := by
  rw [nex_g'_eq]
  have ha := mem_support_monomial_add_left (k := ZMod 3) nex_ne'
  have hb := mem_support_monomial_add_right (k := ZMod 3) nex_ne'
  have hg0 : monomial (single (0 : Fin 2) 3 + single 1 2) (1 : ZMod 3) +
      monomial (single 0 4 + single 1 1) 1 ≠ 0 :=
    MvPolynomial.ne_zero_iff.mpr ⟨_, MvPolynomial.mem_support_iff.mp ha⟩
  have h1 := divisorExponent_le (Δ := {0, 1}) ha
  have h1' := divisorExponent_le (Δ := {0, 1}) hb
  have h2 : (single 0 3 + single 1 1 : Fin 2 →₀ ℕ) ≤ divisorExponent ({0, 1} : Finset (Fin 2))
      (monomial (single 0 3 + single 1 2) (1 : ZMod 3) + monomial (single 0 4 + single 1 1) 1) := by
    refine le_divisorExponent hg0 (fun i hi => ?_) fun β hβ => ?_
    · exfalso
      revert hi
      fin_cases i <;> decide
    · rcases Finset.mem_union.mp (MvPolynomial.support_add hβ) with h | h <;>
        obtain rfl := Finset.mem_singleton.mp (support_monomial_subset h) <;>
        intro i <;> fin_cases i <;> simp
  ext i
  fin_cases i
  · exact le_antisymm (by simpa using h1 0) (by simpa using h2 0)
  · exact le_antisymm (by simpa using h1' 1) (by simpa using h2 1)

/-- **Example 3.7.4, the order `ρ(g'_c)`.** In the `y`-chart, the new divisor is `V(x y)`, the
polynomial `g' = x^3 y^2 + x^4 y` is clean, and `ρ(g'_c) = 1`. So `ρ` stays `1`. -/
theorem nearPointExample_logJacobianOrder_cleanPart :
    logJacobianOrder (blowupDivisor {0} 1 (0 : Fin 2 → ZMod 3))
      (cleanPart 3 (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 * X 1 : MvPolynomial (Fin 2) (ZMod 3))) = 1 := by
  obtain ⟨hg, hc, hord⟩ := nearPointExample_hyp
  have hle := (logJacobianOrder_cleanPart_le 3 (Δ := {0}) hg hc hord
    nearPointExample_pointChart).2
  rw [nearPointExample_logJacobianOrder] at hle
  refine le_antisymm hle ?_
  have hD : blowupDivisor ({0} : Finset (Fin 2)) 1 (0 : Fin 2 → ZMod 3) = {0, 1} := by decide
  have hcl : cleanPart 3 (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 * X 1 : MvPolynomial (Fin 2) (ZMod 3)) =
      X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 * X 1 := by
    refine cleanPart_eq_self ?_
    rw [nex_g'_eq]
    exact nex_isClean (single 0 4 + single 1 1) fun h => absurd (h 1) (by norm_num)
  rw [hD, hcl]
  have hI := idealOrd_logJacobian {0, 1}
    (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 * X 1 : MvPolynomial (Fin 2) (ZMod 3))
  rw [nex_divisorExponent', map_add (Finsupp.degree (σ := Fin 2) (R := ℕ)), degree_single,
    degree_single] at hI
  have h5 : ((5 : ℕ) : ℕ∞) ≤ idealOrd (logJacobian {0, 1}
      (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 * X 1 : MvPolynomial (Fin 2) (ZMod 3))) := by
    refine le_idealOrd_span ?_
    rintro s (⟨i, -, rfl⟩ | ⟨l, hl, rfl⟩)
    · have := le_ord_smul_add_X_mul_pderiv nex_ord_g' 0 i
      rwa [Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_smul, zero_add] at this
    · exfalso
      revert hl
      fin_cases l <;> decide
  rw [hI] at h5
  cases h : logJacobianOrder {0, 1}
      (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 * X 1 : MvPolynomial (Fin 2) (ZMod 3)) using ENat.recTopCoe with
  | top => exact le_top
  | coe a =>
    rw [h] at h5
    have : 5 ≤ 3 + 1 + a := by exact_mod_cast h5
    exact_mod_cast (by omega : 1 ≤ a)

/-- **Example 3.7.4, case A.** For `g = x^3 y^2 + x^4` and `E = V(x)`, the element
`x^r x = x ∂_x g` is in `Θ₀(g)`, and the order of `Θ₀(g)` is `4 = |r| + ρ(g)`. -/
theorem nearPointExample_tangent :
    monomial (divisorExponent {0} (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3))) 1 *
        X 0 ∈ logJacobianTangent {0} (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3)) ∧
      idealOrd (logJacobianTangent {0}
        (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3))) = ((4 : ℕ) : ℕ∞) := by
  have he : monomial (single 0 3) 1 * X 0 =
      X 0 * pderiv 0 (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3)) := by
    rw [nex_pderiv_g_zero, ← X_pow_eq_monomial]
    ring
  have hmem : monomial (single 0 3) 1 * X 0 ∈ logJacobianTangent {0}
      (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3)) := by
    rw [he]
    exact X_mul_pderiv_mem_logJacobianTangent (by decide) _
  rw [nearPointExample_divisorExponent]
  refine ⟨hmem, le_antisymm ((idealOrd_le_ord hmem).trans (le_of_eq ?_))
    (le_idealOrd_logJacobianTangent nex_ord_g)⟩
  rw [ord_mul, ord_monomial one_ne_zero, ord_X, degree_single]
  norm_num

/-- **Example 3.7.4: part 1 of Theorem 3.7.1 fails with `Θ(g)` in the place of `Θ₀(g)`.** Over
`𝔽₃`, let `g = x^3 y^2 + x^4` and `E = V(x)`. Then `ρ(g) = 1`, and in the `y`-chart
`ρ(g'_c) = 1`. The polynomial `ψ = 2 y` has `x^r ψ = ∂_y g ∈ Θ(g)` and `ord ψ = 1`, but the vector
`(0, 1)` of the chart is not in the directrix of `ψ`. -/
theorem nearPointExample_not_mem_directrix :
    logJacobianOrder {0} (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3)) = 1 ∧
      logJacobianOrder (blowupDivisor {0} 1 (0 : Fin 2 → ZMod 3))
        (cleanPart 3 (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 * X 1 : MvPolynomial (Fin 2) (ZMod 3))) = 1 ∧
      monomial (divisorExponent {0} (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 :
          MvPolynomial (Fin 2) (ZMod 3))) 1 * (2 * X 1) ∈
        logJacobian {0} (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3)) ∧
      ord (2 * X 1 : MvPolynomial (Fin 2) (ZMod 3)) = 1 ∧
      chartVector 1 (0 : Fin 2 → ZMod 3) ∉
        directrix (homogeneousComponent 1 (2 * X 1 : MvPolynomial (Fin 2) (ZMod 3))) := by
  refine ⟨nearPointExample_logJacobianOrder, nearPointExample_logJacobianOrder_cleanPart, ?_,
    nex_ord_two_X, ?_⟩
  · rw [nearPointExample_divisorExponent, ← nex_pderiv_g_one]
    exact pderiv_mem_logJacobian (by decide) _
  · rw [nex_two, homogeneousComponent_C_mul, homogeneousComponent_eq_self (isHomogeneous_X _ 1),
      ← smul_eq_C_mul, directrix_smul (by decide), mem_directrix_iff]
    intro h
    simp [translate, chartVector] at h

end Example

end Singularity
