/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianBlowup

/-!
# The order `ρ` does not go up under a point blowup

Let `k` be a field of characteristic `p`, let `g ≠ 0` be a clean polynomial in `k[x_i : i ∈ σ]`
with `ord g ≥ p`, and let `Δ` give the divisor `E = V(∏_{i ∈ Δ} x_i)`. In the `x_j`-chart of the
blowup of the origin with translations `t` (`pointChart j t`), write `π(g) = x_j^p g'`, and let
`Δ'` be the new divisor (`blowupDivisor Δ j t`). This file proves that the order `ρ` of the
log-Jacobian ideal does not go up (Volume 7, Section 3.2 of the handbook, Theorem 3.2.4): the clean
part `g'_c` of `g'` is not `0`, and `ρ(g'_c) ≤ ρ(g)`. With the dichotomy `d - 1 ≤ ρ ≤ d`, this gives
`d' ≤ ρ(g'_c) + 1 ≤ ρ + 1 ≤ d + 1` for the residual orders `d` of `g` and `d'` of `g'_c`
(Corollary 3.2.5).

The handbook works in the power series ring, where `u = blowupUnit Δ j t` is a unit, and it uses
that the power series ring is a unique factorization domain. The proof here stays in `k[x]`.

* Write `g = x^r G` and let `τ` be the order of `Θ₀(g)`. Each element of `Θ₀(g)` is divisible by
  `x^r` and has order at least `τ`, so its image under `π` is divisible by
  `x_j^τ x^e` (`dvd_pointChart_of_monomial_one_dvd`), with `e = chartExponent j t r`. The same
  holds for the ideal `π(Θ₀(g))` (`map_pointChart_span_le`).
* By the law `(x_j^p u) Θ'(g') ⊆ π(Θ₀(g))` of Theorem 3.2.3, each element of `Θ'(g')` is
  divisible by `x^b` with `x_j^p x^b = x_j^τ x^e`, after the cancellation of `x_j^p` and of the
  factor `u` (`monomial_one_dvd_of_dvd_mul`). The monomial `x^b` uses only variables of `Δ'`.
* The ideal `Θ₀(g)` contains an element `h` with `ord π(h) ≤ τ + |e| + ρ`, and
  `π(h) = x_j^p φ` with `φ ∈ Θ'(g')` by the law `π(Θ₀(g)) ⊆ (x_j^p) Θ'(g')`. So
  `ord φ ≤ |b| + ρ`.
* For a clean `g'_c ≠ 0`, `x^b` divides `x^{r'}` (Theorem 3.1.4, part 1), and the bound on
  `ord φ` gives `ρ(g'_c) ≤ ρ` (`logJacobianOrder_le_of_mem`).

## Main results

* `monomial_one_dvd_iff`, `monomial_one_dvd_of_dvd_mul`: divisibility by a monomial, and the
  cancellation of a factor with a nonzero constant term.
* `dvd_pointChart_of_monomial_one_dvd`, `map_pointChart_span_le`: the image under `π` of an ideal
  whose generators are divisible by `x^r` and have order at least `|r| + c` is contained in
  `(x_j^(|r| + c) x^e)`.
* `le_idealOrd_logJacobianTangent`: `ord Θ₀(g) ≥ ord g`.
* `logJacobianOrder_le_of_mem`: for a clean `g ≠ 0`, if `x^b` divides `Θ(g)` with `b` supported
  in `Δ`, then each `φ ∈ Θ(g)` with `ord φ ≤ |b| + n` gives `ρ(g) ≤ n`.
* `logJacobianOrder_cleanPart_le`: Theorem 3.2.4, `g'_c ≠ 0` and `ρ(g'_c) ≤ ρ(g)`.
* `residualOrderAlong_pointChart_le_logJacobianOrder`,
  `residualOrderAlong_pointChart_le_add_one`:
  Corollary 3.2.5, `d' ≤ ρ(g'_c) + 1 ≤ ρ + 1 ≤ d + 1`.

## References

* V. Cossart, *Polyèdre caractéristique d'une singularité*, thèse d'État, Orsay 1987.
* Volume 7, Section 3.2 of the handbook: Theorem 3.2.4 and Corollary 3.2.5.
-/

open MvPolynomial Finsupp

namespace Singularity

/-! ### Divisibility by a monomial -/

section Divisibility

variable {σ k : Type*} [Field k]

/-- The monomial `x^b` divides `f` if and only if each monomial of `f` is divisible by `x^b`. -/
theorem monomial_one_dvd_iff {b : σ →₀ ℕ} {f : MvPolynomial σ k} :
    monomial b (1 : k) ∣ f ↔ ∀ a ∈ f.support, b ≤ a := by
  rw [← Ideal.mem_span_singleton, ← Set.image_singleton (f := fun s => monomial s (1 : k)),
    mem_ideal_span_monomial_image]
  simp

/-- **The cancellation of a unit factor.** If `x^b` divides `u f` and the constant term of `u` is
not `0`, then `x^b` divides `f`. In the power series ring `u` is a unit. In `k[x]` the proof uses
that each variable `x_i` is prime and does not divide `u`. -/
theorem monomial_one_dvd_of_dvd_mul {b : σ →₀ ℕ} {u f : MvPolynomial σ k}
    (hu : constantCoeff u ≠ 0) (h : monomial b (1 : k) ∣ u * f) : monomial b (1 : k) ∣ f := by
  rw [monomial_one_dvd_iff]
  intro a ha i
  have hXu : ¬ X i ∣ u := by
    rintro ⟨v, rfl⟩
    exact hu (by rw [map_mul, constantCoeff_X, zero_mul])
  have hXb : X i ^ b i ∣ monomial b (1 : k) := by
    rw [X_pow_eq_monomial, monomial_one_dvd_iff]
    intro a' ha'
    obtain rfl : b = a' := by
      classical
      by_contra hne
      refine MvPolynomial.mem_support_iff.mp ha' ?_
      rw [coeff_monomial, ite_eq_right_iff]
      exact fun h => absurd h hne
    exact Finsupp.single_le_iff.mpr le_rfl
  have hdvd := (X_prime : Prime (X i : MvPolynomial σ k)).pow_dvd_of_dvd_mul_left (b i) hXu
    (hXb.trans h)
  rw [X_pow_eq_monomial, monomial_one_dvd_iff] at hdvd
  exact Finsupp.single_le_iff.mp (hdvd a ha)

end Divisibility

/-! ### The image of an ideal under the chart -/

section Chart

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k]

/-- If `x^r` divides `h` and `ord h ≥ |r| + c`, then `x_j^(|r| + c) x^e` divides `π(h)`, with
`e = chartExponent j t r`. The factor `x_j^|r| x^e` comes from `π(x^r)`, and the factor `x_j^c`
comes from the order of `h / x^r`. -/
theorem dvd_pointChart_of_monomial_one_dvd {j : σ} {t : σ → k} {r : σ →₀ ℕ} {c : ℕ}
    {h : MvPolynomial σ k} (hr : monomial r (1 : k) ∣ h)
    (hc : ((degree r + c : ℕ) : ℕ∞) ≤ ord h) :
    X j ^ (degree r + c) * monomial (chartExponent j t r) (1 : k) ∣ pointChart j t h := by
  obtain ⟨h', rfl⟩ := hr
  have hc' : (c : ℕ∞) ≤ ord h' := by
    rw [ord_mul, ord_monomial one_ne_zero, Nat.cast_add] at hc
    exact (ENat.add_le_add_iff_left (ENat.natCast_ne_top _)).mp hc
  obtain ⟨f', hf'⟩ := exists_pointChart_eq_X_pow_mul (j := j) (t := t) hc'
  refine ⟨chartUnit j t r * f', ?_⟩
  rw [map_mul, pointChart_monomial, chartRest_monomial_one, hf', pow_add]
  ring

/-- **The image of an ideal under the chart, through its generators.** If each generator of `I`
is divisible by `x^r` and has order at least `|r| + c`, then `π(I)` is contained in the ideal
generated by `x_j^(|r| + c) x^e`, with `e = chartExponent j t r`. In particular each element of
`π(I)` has order at least `|r| + c + |e|`. -/
theorem map_pointChart_span_le {j : σ} {t : σ → k} {S : Set (MvPolynomial σ k)} {r : σ →₀ ℕ}
    {c : ℕ} (hS : ∀ s ∈ S, monomial r (1 : k) ∣ s ∧ ((degree r + c : ℕ) : ℕ∞) ≤ ord s) :
    Ideal.map (pointChart j t) (Ideal.span S) ≤
      Ideal.span {X j ^ (degree r + c) * monomial (chartExponent j t r) (1 : k)} := by
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨s, hs, rfl⟩
  exact Ideal.mem_span_singleton.mpr
    (dvd_pointChart_of_monomial_one_dvd (hS s hs).1 (hS s hs).2)

/-- The constant term of `u = blowupUnit Δ j t` is the product of the `t_i ≠ 0`, so it is not
`0`. -/
theorem constantCoeff_blowupUnit_ne_zero (Δ : Finset σ) (j : σ) (t : σ → k) :
    constantCoeff (blowupUnit Δ j t) ≠ 0 := by
  rw [blowupUnit, map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  rw [map_add, constantCoeff_X, constantCoeff_C, zero_add]
  exact (Finset.mem_filter.mp hi).2.2

end Chart

/-! ### Orders of the log-Jacobian ideals -/

section Order

variable {σ k : Type*} [Field k] {Δ : Finset σ} {g : MvPolynomial σ k}

/-- `ord Θ₀(g) ≥ ord g`: each generator `x_i ∂_i g` or `x_m ∂_l g` of `Θ₀(g)` has order at least
`ord g`. -/
theorem le_idealOrd_logJacobianTangent {n : ℕ} (hn : (n : ℕ∞) ≤ ord g) :
    (n : ℕ∞) ≤ idealOrd (logJacobianTangent Δ g) := by
  refine le_idealOrd_span ?_
  rintro s (⟨i, -, rfl⟩ | ⟨⟨m, l⟩, -, rfl⟩)
  · simpa using le_ord_smul_add_X_mul_pderiv hn 0 i
  · refine le_trans ?_ (le_ord_mul _ _)
    have h1 : (1 : ℕ∞) ≤ ord (X m : MvPolynomial σ k) := one_le_ord_iff.mpr (by simp)
    calc (n : ℕ∞) ≤ 1 + ((n - 1 : ℕ) : ℕ∞) := by norm_cast; omega
      _ ≤ _ := add_le_add h1 (le_ord_pderiv hn l)

variable (p : ℕ) [CharP k p]

/-- **The cancellation of a monomial factor in the residual ideal.** Let `g ≠ 0` be clean, and let
`x^b` divide each element of `Θ(g)`, with `b` supported in `Δ`. If `φ ∈ Θ(g)` has
`ord φ ≤ |b| + n`, then `ρ(g) ≤ n`. The proof uses `b ≤ r` (Theorem 3.1.4, part 1) and
`ord Θ(g) = |r| + ρ(g)`. -/
theorem logJacobianOrder_le_of_mem (hg : g ≠ 0) (hc : IsClean p g) {b : σ →₀ ℕ}
    (hb : ∀ i, i ∉ Δ → b i = 0) (hle : logJacobian Δ g ≤ Ideal.span {monomial b 1})
    {φ : MvPolynomial σ k} (hφ : φ ∈ logJacobian Δ g) {n : ℕ∞} (hn : ord φ ≤ degree b + n) :
    logJacobianOrder Δ g ≤ n := by
  have hbr := le_divisorExponent_of_logJacobian_le p hg hc hb hle
  have h1 : ((degree (divisorExponent Δ g) : ℕ) : ℕ∞) + logJacobianOrder Δ g ≤
      degree (divisorExponent Δ g) + n := by
    rw [← idealOrd_logJacobian]
    refine (idealOrd_le_ord hφ).trans (hn.trans ?_)
    gcongr
    exact_mod_cast degree_mono hbr
  exact (ENat.add_le_add_iff_left (ENat.natCast_ne_top _)).mp h1

end Order

/-! ### The theorem -/

section Nonincrease

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

omit [DecidableEq σ] [DecidableEq k] [Fintype σ] [CharP k p] in
/-- `Θ(0) = 0`: each generator of the log-Jacobian ideal of `0` is `0`. -/
theorem logJacobian_zero (Δ : Finset σ) : logJacobian Δ (0 : MvPolynomial σ k) = ⊥ := by
  refine le_bot_iff.mp (Ideal.span_le.mpr ?_)
  rintro s (⟨i, -, rfl⟩ | ⟨l, -, rfl⟩) <;> simp

/-- **`ρ` does not go up** (Volume 7, Section 3.2 of the handbook, Theorem 3.2.4). Let `g ≠ 0` be
clean with `ord g ≥ p`, and let `π(g) = x_j^p g'` in the chart `π = pointChart j t`. Then the clean
part `g'_c` of `g'` is not `0`, and `ρ(g'_c) ≤ ρ(g)` for the new divisor `Δ' = blowupDivisor Δ j t`.
The point of the chart can be translated (`t ≠ 0`). -/
theorem logJacobianOrder_cleanPart_le (hg : g ≠ 0) (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g)
    (h : pointChart j t g = X j ^ p * g') :
    cleanPart p g' ≠ 0 ∧
      logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') ≤ logJacobianOrder Δ g := by
  -- `ρ` is finite.
  have hG : residualFactor Δ g ≠ 0 := by
    intro h0
    apply hg
    rw [← monomial_mul_residualFactor Δ g, h0, mul_zero]
  obtain ⟨ρ, hρ⟩ := ENat.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ord_ne_top hG) (logJacobianOrder_le p hc))
  -- Each element of `Θ(g)` is divisible by `x^r`.
  have hdvd : ∀ f ∈ logJacobian Δ g, monomial (divisorExponent Δ g) (1 : k) ∣ f :=
    fun f hf => Ideal.mem_span_singleton.mp (logJacobian_le_span_monomial Δ g hf)
  have hdvd₀ : ∀ f ∈ logJacobianTangent Δ g, monomial (divisorExponent Δ g) (1 : k) ∣ f :=
    fun f hf => hdvd f (logJacobianTangent_le Δ g hf)
  -- An element `h₁` of `Θ(g)` of order `|r| + ρ`, and `x_j h₁ ∈ Θ₀(g)`.
  obtain ⟨h₁, hh₁, hord₁⟩ := exists_mem_ord_eq_idealOrd (logJacobian Δ g)
  rw [idealOrd_logJacobian, ← hρ] at hord₁
  have hXh₁ : X j * h₁ ∈ logJacobianTangent Δ g :=
    span_range_X_mul_logJacobian_le Δ g (Ideal.mul_mem_mul (Ideal.subset_span ⟨j, rfl⟩) hh₁)
  -- The order `τ` of `Θ₀(g)` is finite, with `p ≤ τ`, `|r| ≤ τ` and `τ ≤ |r| + ρ + 1`.
  obtain ⟨h₀, hh₀, hord₀⟩ := exists_mem_ord_eq_idealOrd (logJacobianTangent Δ g)
  have hτ1 : idealOrd (logJacobianTangent Δ g) ≤
      ((degree (divisorExponent Δ g) + ρ + 1 : ℕ) : ℕ∞) := by
    refine (idealOrd_le_ord hXh₁).trans ?_
    rw [ord_mul, ord_X, hord₁]
    push_cast
    exact le_of_eq (by ring)
  obtain ⟨τ, hτ⟩ := ENat.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hτ1)
  rw [← hτ] at hord₀ hτ1
  have hτ1' : τ ≤ degree (divisorExponent Δ g) + ρ + 1 := by exact_mod_cast hτ1
  have hpτ : p ≤ τ := by
    have := le_idealOrd_logJacobianTangent (Δ := Δ) hord
    rw [← hτ] at this
    exact_mod_cast this
  have hrτ : degree (divisorExponent Δ g) ≤ τ := by
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
        rw [Nat.add_sub_cancel' hrτ, hτ]
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
  -- An element `f ∈ Θ₀(g)` with `ord π(f) ≤ τ + |e| + ρ`.
  have key : ∃ f ∈ logJacobianTangent Δ g, ord (pointChart j t f) ≤
      ((τ + degree (chartExponent j t (divisorExponent Δ g)) + ρ : ℕ) : ℕ∞) := by
    by_cases hcase : τ ≤ degree (divisorExponent Δ g) + ρ
    · refine ⟨h₀, hh₀, ?_⟩
      have hsupp := monomial_one_dvd_iff.mp (hdvd₀ h₀ hh₀)
      have := ord_pointChart_le (j := j) (t := t) (d := τ - degree (divisorExponent Δ g)) hsupp
        (by rw [hord₀, Nat.add_sub_cancel' hrτ])
      refine this.trans ?_
      exact_mod_cast (by omega : degree (divisorExponent Δ g) +
        degree (chartExponent j t (divisorExponent Δ g)) + (τ - degree (divisorExponent Δ g)) +
        (τ - degree (divisorExponent Δ g)) ≤
        τ + degree (chartExponent j t (divisorExponent Δ g)) + ρ)
    · refine ⟨X j * h₁, hXh₁, ?_⟩
      have hsupp := monomial_one_dvd_iff.mp (hdvd h₁ hh₁)
      have := ord_pointChart_le (j := j) (t := t) (d := ρ) hsupp (by rw [hord₁, Nat.cast_add])
      rw [map_mul, pointChart_X_self, ord_mul, ord_X]
      calc (1 : ℕ∞) + ord (pointChart j t h₁) ≤
            1 + ((degree (divisorExponent Δ g) + degree (chartExponent j t (divisorExponent Δ g)) +
              ρ + ρ : ℕ) : ℕ∞) := add_le_add le_rfl this
        _ ≤ _ := by
          exact_mod_cast (by omega : 1 + (degree (divisorExponent Δ g) +
            degree (chartExponent j t (divisorExponent Δ g)) + ρ + ρ) ≤
            τ + degree (chartExponent j t (divisorExponent Δ g)) + ρ)
  -- `π(f) = x_j^p φ` with `φ ∈ Θ'(g')` and `ord φ ≤ |b| + ρ`.
  obtain ⟨f, hf, hfo⟩ := key
  obtain ⟨φ, hφ, hφeq⟩ := Ideal.mem_span_singleton_mul.mp
    (map_pointChart_logJacobianTangent_le_span_mul p (Δ := Δ) h (Ideal.mem_map_of_mem _ hf))
  have h5 : ord (pointChart j t f) = p + ord φ := by
    rw [← hφeq, ord_mul, ord_X_pow]
  have hφo : ord φ ≤
      ((degree (single j (τ - p) + chartExponent j t (divisorExponent Δ g)) + ρ : ℕ) : ℕ∞) := by
    have h6 : (p : ℕ∞) + ord φ ≤ (p : ℕ∞) +
        ((degree (single j (τ - p) + chartExponent j t (divisorExponent Δ g)) + ρ : ℕ) : ℕ∞) := by
      rw [← h5]
      refine hfo.trans ?_
      rw [← Nat.cast_add, hdb]
      exact_mod_cast (by omega : τ + degree (chartExponent j t (divisorExponent Δ g)) + ρ ≤
        p + (τ - p + degree (chartExponent j t (divisorExponent Δ g)) + ρ))
    exact (ENat.add_le_add_iff_left (ENat.natCast_ne_top p)).mp h6
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    rw [ord_zero, top_le_iff] at hφo
    exact ENat.natCast_ne_top _ hφo
  -- `g'_c ≠ 0`, since `Θ'(g'_c) = Θ'(g')` contains `φ ≠ 0`.
  have hcl : cleanPart p g' ≠ 0 := by
    intro h0
    have h7 : logJacobian (blowupDivisor Δ j t) g' = ⊥ := by
      rw [← logJacobian_cleanPart p, h0, logJacobian_zero]
    rw [h7, Ideal.mem_bot] at hφ
    exact hφ0 hφ
  refine ⟨hcl, ?_⟩
  rw [← hρ]
  refine logJacobianOrder_le_of_mem p hcl (isClean_cleanPart p g') hb (φ := φ) ?_ ?_ ?_
  · rw [logJacobian_cleanPart]
    exact hB
  · rw [logJacobian_cleanPart]
    exact hφ
  · rw [Nat.cast_add] at hφo
    exact hφo

/-- **The residual order goes up by at most one** (Volume 7, Section 3.2 of the handbook,
Corollary 3.2.5). In the situation of Theorem 3.2.4, let `d` be the residual order of `g` along `Δ`
and `d'` the residual order of `g'_c` along `Δ'`. Then `d' ≤ ρ(g'_c) + 1 ≤ ρ + 1 ≤ d + 1`. -/
theorem residualOrderAlong_pointChart_le_logJacobianOrder (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') :
    residualOrderAlong (blowupDivisor Δ j t) p g' ≤
        logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') + 1 ∧
      logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') + 1 ≤ logJacobianOrder Δ g + 1 ∧
      logJacobianOrder Δ g + 1 ≤ residualOrderAlong Δ p g + 1 := by
  refine ⟨ord_residualFactor_le_logJacobianOrder_add_one _ _, ?_, ?_⟩
  · gcongr
    exact (logJacobianOrder_cleanPart_le p hg hc hord h).2
  · gcongr
    exact logJacobianOrder_le_residualOrderAlong p hc

/-- Moh's bound for `q = p` at each point of the exceptional divisor (Volume 7, Section 3.2 of the
handbook, Corollary 3.2.5): the residual order goes up by at most one, `d' ≤ d + 1`. -/
theorem residualOrderAlong_pointChart_le_add_one (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') :
    residualOrderAlong (blowupDivisor Δ j t) p g' ≤ residualOrderAlong Δ p g + 1 := by
  obtain ⟨h1, h2, h3⟩ := residualOrderAlong_pointChart_le_logJacobianOrder p hg hc hord h
  exact h1.trans (h2.trans h3)

end Nonincrease

end Singularity
