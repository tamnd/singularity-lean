/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianNoLeave
import Singularity.Invariant.CossartPiltantOmega

/-!
# The case is the type, and the triple of `ρ`, `d` and `τ_ρ` does not get worse

Let `k` be a field of characteristic `p`, and let `g = x^r G` be clean for the divisor
`E = V(∏_{i ∈ Δ} x_i)`, with `r = divisorExponent Δ g` and `G = residualFactor Δ g`. Let
`d = ord G` be the residual order (`residualOrderAlong`) and `ρ = logJacobianOrder Δ g`. The order
of `Θ₀(g)` (`logJacobianTangent`) is `|r| + σ`. Case A is `σ = ρ`, and case B is `σ = ρ + 1`
(`logJacobianCaseIdeal`). The type of `g` is `d - ρ`, and it is `0` or `1` (Theorem 3.1.4).

This file proves two results (Volume 7, Section 3.10 of the handbook).

* Lemma 3.10.1. If `g ≠ 0` is clean, then the order of `Θ₀(g)` is `ord g`. So `σ = d`. Thus case A
  is the type `0` (`ρ = d`), and case B is the type `1` (`ρ = d - 1`).
* Theorem 3.10.3. Let the chart send `g` to `x_j^p g'`, let `ρ(g'_c) = ρ(g)`, and let no
  component of `Δ` leave. Then `d' ≤ d`, with `d'` the residual order of `g'_c` along the new
  divisor. If `d' = d`, then `τ_ρ(g) ≤ τ_ρ(g'_c)`.

The proof of Lemma 3.10.1. Each generator of `Θ₀(g)` has order at least `ord g`
(`le_idealOrd_logJacobianTangent`). Take a monomial `x^a` of `g` of degree `ord g`. Since `g` is
clean, some exponent `a_k` is not divisible by `p`. The coefficient of `x^a` in `x_k ∂_k g` is
`a_k c_a ≠ 0`, and `x_k ∂_k g` is in `Θ₀(g)` for `k ∈ Δ` and for `k ∉ Δ`.

The proof of Theorem 3.10.3. If `g` is of case A, then `ρ = d`. Theorem 3.9.10 keeps case A, so
`d' = ρ = d`, and Theorem 3.9.11 gives the bound on `τ_ρ`. If `g` is of case B, then
`d = ρ + 1`, and `d' ≤ ρ(g'_c) + 1 = d`. If `d' = d`, then the new point is of case B, and
Proposition 3.8.2 gives the bound on `τ_ρ`.

## Main results

* `idealOrd_logJacobianTangent_eq_ord`: Lemma 3.10.1, the order of `Θ₀(g)` is `ord g`.
* `idealOrd_logJacobianTangent_eq_degree_add_iff`: case A is the type `0`.
* `idealOrd_logJacobianTangent_eq_degree_add_add_one_iff`: case B is the type `1`.
* `residualOrderAlong_cleanPart_le_of_forall_eq_zero`: Theorem 3.10.3, `d' ≤ d`.
* `logJacobianDirectrixCodim_le_cleanPart_of_residualOrderAlong_eq`: Theorem 3.10.3, if `d' = d`,
  then `τ_ρ(g) ≤ τ_ρ(g'_c)`.

## References

* Volume 7, Section 3.10 of the handbook: Lemma 3.10.1 and Theorem 3.10.3.
* Volume 7, Sections 3.1, 3.8 and 3.9 of the handbook: Theorem 3.1.4, Proposition 3.8.2,
  Theorem 3.9.10 and Theorem 3.9.11.
-/

open MvPolynomial Finsupp

namespace Singularity

/-! ### Lemma 3.10.1 -/

section LemmaA

variable {σ k : Type*} [Field k] (p : ℕ) [CharP k p] {Δ : Finset σ} {g : MvPolynomial σ k}

omit [CharP k p] in
/-- The order of `g = x^r G` is `|r| + ord G`. -/
theorem ord_eq_degree_divisorExponent_add (Δ : Finset σ) (g : MvPolynomial σ k) :
    ord g = degree (divisorExponent Δ g) + ord (residualFactor Δ g) := by
  conv_lhs => rw [← monomial_mul_residualFactor Δ g]
  rw [ord_mul, ord_monomial one_ne_zero]

/-- **The order of `Θ₀(g)` is `ord g`** (Volume 7, Section 3.10 of the handbook, Lemma 3.10.1).
Let `g ≠ 0` be clean. Then the order of `Θ₀(g)` is `ord g`. So `σ = d`, with `d = ord G`. The
proof: take a monomial `x^a` of `g` of degree `ord g`. Some `a_k` is not divisible by `p`, and the
coefficient of `x^a` in `x_k ∂_k g` is `a_k c_a ≠ 0`. -/
theorem idealOrd_logJacobianTangent_eq_ord (hg : g ≠ 0) (hc : IsClean p g) :
    idealOrd (logJacobianTangent Δ g) = ord g := by
  refine le_antisymm ?_ (ENat.forall_natCast_le_iff_le.mp fun n hn =>
    le_idealOrd_logJacobianTangent hn)
  obtain ⟨a, ha, hdeg⟩ := exists_coeff_ne_zero_and_ord_eq hg
  obtain ⟨l, hl⟩ := not_forall.mp (hc a (MvPolynomial.mem_support_iff.mpr ha))
  have hne : (X l * pderiv l g).coeff a ≠ 0 := by
    rw [coeff_X_mul_pderiv]
    exact mul_ne_zero ((CharP.cast_eq_zero_iff k p _).not.mpr hl) ha
  rw [hdeg]
  exact (idealOrd_le_ord (X_mul_pderiv_mem_logJacobianTangent' Δ l g)).trans (ord_le hne)

/-- **The order of `Θ₀(g)` is `|r| + d`** (Volume 7, Section 3.10 of the handbook,
Lemma 3.10.1). Let `g ≠ 0` be clean. Then the order of `Θ₀(g)` is `|r| + d`, with `d` the residual
order of `g` along `Δ`. -/
theorem idealOrd_logJacobianTangent_eq_degree_add_residualOrderAlong (hg : g ≠ 0)
    (hc : IsClean p g) :
    idealOrd (logJacobianTangent Δ g) =
      degree (divisorExponent Δ g) + residualOrderAlong Δ p g := by
  rw [idealOrd_logJacobianTangent_eq_ord p hg hc, ord_eq_degree_divisorExponent_add Δ g,
    residualOrderAlong, cleanPart_eq_self hc]

/-- Let `g ≠ 0` be clean. Then the order of `Θ₀(g)` is `|r| + n` if and only if `n = d`, with `d`
the residual order of `g` along `Δ`. -/
private theorem idealOrd_eq_degree_add_iff (hg : g ≠ 0) (hc : IsClean p g)
    {n : ℕ∞} :
    idealOrd (logJacobianTangent Δ g) = degree (divisorExponent Δ g) + n ↔
      n = residualOrderAlong Δ p g := by
  rw [idealOrd_logJacobianTangent_eq_degree_add_residualOrderAlong p hg hc]
  constructor
  · intro h
    exact (WithTop.add_left_cancel (ENat.natCast_ne_top _) h).symm
  · rintro rfl
    rfl

/-- **Case A is the type `0`** (Volume 7, Section 3.10 of the handbook, Lemma 3.10.1). Let
`g ≠ 0` be clean. Then the order of `Θ₀(g)` is `|r| + ρ` if and only if `ρ = d`, with `d` the
residual order of `g` along `Δ`. -/
theorem idealOrd_logJacobianTangent_eq_degree_add_iff (hg : g ≠ 0) (hc : IsClean p g) :
    idealOrd (logJacobianTangent Δ g) = degree (divisorExponent Δ g) + logJacobianOrder Δ g ↔
      logJacobianOrder Δ g = residualOrderAlong Δ p g :=
  idealOrd_eq_degree_add_iff p hg hc

/-- **Case B is the type `1`** (Volume 7, Section 3.10 of the handbook, Lemma 3.10.1). Let
`g ≠ 0` be clean. Then the order of `Θ₀(g)` is `|r| + ρ + 1` if and only if `ρ + 1 = d`, with `d`
the residual order of `g` along `Δ`. -/
theorem idealOrd_logJacobianTangent_eq_degree_add_add_one_iff (hg : g ≠ 0) (hc : IsClean p g) :
    idealOrd (logJacobianTangent Δ g) =
        degree (divisorExponent Δ g) + logJacobianOrder Δ g + 1 ↔
      logJacobianOrder Δ g + 1 = residualOrderAlong Δ p g := by
  rw [add_assoc]
  exact idealOrd_eq_degree_add_iff p hg hc

end LemmaA

/-! ### Theorem 3.10.3 -/

section TheoremB

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

omit [DecidableEq σ] [DecidableEq k] [Fintype σ] [CharP k p] in
/-- If `ρ(g'_c)` is finite, then `g'_c ≠ 0`. -/
private theorem cleanPart_ne_zero_of_logJacobianOrder_eq {Δ' : Finset σ} {m : ℕ}
    (hρ' : logJacobianOrder Δ' (cleanPart p g') = m) : cleanPart p g' ≠ 0 := by
  intro h0
  rw [h0, logJacobianOrder_zero] at hρ'
  exact ENat.top_ne_natCast m hρ'

omit [DecidableEq σ] [DecidableEq k] [Fintype σ] [CharP k p] in
/-- The residual order of `z^p + F` is the residual order of `z^p + F_c`. -/
private theorem residualOrderAlong_cleanPart_eq (Δ' : Finset σ) (F : MvPolynomial σ k) :
    residualOrderAlong Δ' p (cleanPart p F) = residualOrderAlong Δ' p F := by
  rw [residualOrderAlong, residualOrderAlong, cleanPart_eq_self (isClean_cleanPart p F)]

omit [DecidableEq σ] [DecidableEq k] [Fintype σ] in
/-- The two cases of the old point. Let `g` be clean with `ρ(g) = m`. Then either `d = m` and the
order of `Θ₀(g)` is `|r| + m`, or `d = m + 1`. -/
private theorem caseA_or_eq_add_one (hg : g ≠ 0) (hc : IsClean p g) {m : ℕ}
    (hρ : logJacobianOrder Δ g = m) :
    (ord (residualFactor Δ g) = m ∧
        idealOrd (logJacobianTangent Δ g) = ((degree (divisorExponent Δ g) + m : ℕ) : ℕ∞)) ∨
      ord (residualFactor Δ g) = ((m + 1 : ℕ) : ℕ∞) := by
  have hd : residualOrderAlong Δ p g = ord (residualFactor Δ g) := by
    rw [residualOrderAlong, cleanPart_eq_self hc]
  rcases logJacobianOrder_eq_or p (Δ := Δ) hc with h1 | h1
  · refine Or.inl ⟨by rw [← hd, ← h1, hρ], ?_⟩
    rw [Nat.cast_add, ← hρ]
    exact (idealOrd_logJacobianTangent_eq_degree_add_iff p hg hc).mpr h1
  · refine Or.inr ?_
    rw [← hd, ← h1, hρ, Nat.cast_succ]

/-- **The residual order does not go up** (Volume 7, Section 3.10 of the handbook,
Theorem 3.10.3). Let `g ≠ 0` be clean with `ord g ≥ p`, let `π(g) = x_j^p g'` in the chart
`π = pointChart j t`, and let `ρ(g) = ρ(g'_c) = m` for the new divisor `Δ' = blowupDivisor Δ j t`.
If `t_i = 0` for each `i ∈ Δ` with `i ≠ j`, then `d' ≤ d`, with `d` the residual order of `g`
along `Δ` and `d'` the residual order of `g'_c` along `Δ'`. If `g` is of case A, then `d' = d`. If
`g` is of case B, then `d' ≤ ρ(g'_c) + 1 = d`. -/
theorem residualOrderAlong_cleanPart_le_of_forall_eq_zero (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m)
    (ht : ∀ i ∈ Δ, i ≠ j → t i = 0) :
    residualOrderAlong (blowupDivisor Δ j t) p g' ≤ residualOrderAlong Δ p g := by
  have hd : residualOrderAlong Δ p g = ord (residualFactor Δ g) := by
    rw [residualOrderAlong, cleanPart_eq_self hc]
  rw [hd]
  rcases caseA_or_eq_add_one p hg hc hρ with ⟨hG, hA⟩ | hG
  · -- The old point is of case A, and the new point is of case A (Theorem 3.9.10).
    have hA' := idealOrd_logJacobianTangent_cleanPart_of_forall_eq_zero p hg hc hord h hρ hA hρ'
      ht
    rw [Nat.cast_add, ← hρ', idealOrd_logJacobianTangent_eq_degree_add_iff p
      (cleanPart_ne_zero_of_logJacobianOrder_eq p hρ') (isClean_cleanPart p g')] at hA'
    rw [hG, ← hρ', hA', residualOrderAlong_cleanPart_eq]
  · -- The old point is of case B: `d' ≤ ρ(g'_c) + 1 = m + 1 = d`.
    rw [hG, Nat.cast_succ, ← hρ']
    exact ord_residualFactor_le_logJacobianOrder_add_one _ _

/-- **`τ_ρ` does not go down if `d` stays** (Volume 7, Section 3.10 of the handbook,
Theorem 3.10.3). Let `g ≠ 0` be clean with `ord g ≥ p`, let `π(g) = x_j^p g'` in the chart
`π = pointChart j t`, and let `ρ(g) = ρ(g'_c) = m` for the new divisor `Δ' = blowupDivisor Δ j t`.
Let `t_i = 0` for each `i ∈ Δ` with `i ≠ j`. If `d' = d`, with `d` the residual order of `g` along
`Δ` and `d'` the residual order of `g'_c` along `Δ'`, then `τ_ρ(g) ≤ τ_ρ(g'_c)`. If `g` is of case
A, this is Theorem 3.9.11. If `g` is of case B, then the new point is of case B, and this is
Proposition 3.8.2. -/
theorem logJacobianDirectrixCodim_le_cleanPart_of_residualOrderAlong_eq (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m)
    (ht : ∀ i ∈ Δ, i ≠ j → t i = 0)
    (hdd : residualOrderAlong (blowupDivisor Δ j t) p g' = residualOrderAlong Δ p g) :
    logJacobianDirectrixCodim Δ g ≤
      logJacobianDirectrixCodim (blowupDivisor Δ j t) (cleanPart p g') := by
  rcases caseA_or_eq_add_one p hg hc hρ with ⟨hG, hA⟩ | hG
  · exact logJacobianDirectrixCodim_le_cleanPart_of_forall_eq_zero p hg hc hord h hG hρ hA hρ' ht
  · -- The old point is of case B, and `d' = m + 1`. So the new point is of case B.
    refine logJacobianDirectrixCodim_le_cleanPart p hg hc hord h hρ hρ' ?_
    have hd' : residualOrderAlong (blowupDivisor Δ j t) p (cleanPart p g') =
        ((m + 1 : ℕ) : ℕ∞) := by
      rw [residualOrderAlong_cleanPart_eq, hdd, residualOrderAlong, cleanPart_eq_self hc, hG]
    rw [idealOrd_logJacobianTangent_eq_degree_add_residualOrderAlong p
      (cleanPart_ne_zero_of_logJacobianOrder_eq p hρ') (isClean_cleanPart p g'), hd']
    norm_cast

end TheoremB

end Singularity
