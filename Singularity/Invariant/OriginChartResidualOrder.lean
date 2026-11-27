/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.OriginRuns
import Singularity.Invariant.CossartPiltantOmega

/-!
# The residual order and `ω` at the origin of a chart

This file proves parts 3 and 4 of Proposition 4.3.4 of Volume 6, Section 4.3 of the handbook, the
part on `ω`. Let `k` be a field, let `g ∈ k[x_i : i ∈ σ]` with `σ` finite and `ord g ≥ p`, and let
`Δ` give the divisor `E = V(∏_{i ∈ Δ} x_i)`. The origin of the `x_j`-chart of the blowup of the
origin sends `g` to `x_j^p g'`, with `g' = originTransform p j g`
(`OriginRuns.pointChart_eq_X_pow_mul_originTransform`). The exponent `a` of a monomial becomes
`a'` with `a'_j = |a| - p` and `a'_i = a_i` for `i ≠ j` (`OriginRuns.expStep`).

Parts 1 and 2 of the proposition are in `Singularity/Invariant/OriginRuns.lean`: the support map
is a bijection that keeps the coefficients (`OriginRuns.support_originTransform`,
`OriginRuns.coeff_originTransform_expStep`), `g'` is clean if `g` is clean
(`OriginRuns.isClean_originTransform`), and the new divisor is `Δ ∪ {j}`
(`OriginRuns.blowupDivisor_zero`).

Part 3. Let `ε = ord G` and `ε' = ord G'` be the residual orders, with `G = residualFactor Δ g` and
`G' = residualFactor (Δ ∪ {j}) g'`, and let `r = divisorExponent Δ g`. For each monomial `x^a` of
`g` of degree `ord g`, `ε' + a_j ≤ ε + r_j` (`ord_residualFactor_originTransform_add_le`). Here
`r_j = 0` if `j ∉ Δ`. So `ε' ≤ ε - (a_j - r_j)` if `j ∈ Δ`, and `ε' ≤ ε - a_j` if `j ∉ Δ`
(`ord_residualFactor_originTransform_add_le_of_notMem`), and `ε' ≤ ε`
(`ord_residualFactor_originTransform_le`). The proof is the one of the handbook. The order of `g'`
is at most `|a'| = 2|a| - a_j - p`, and each exponent of `g'` has the entry `j` at least
`ord g - p` and the entries `i ∈ Δ`, `i ≠ j`, at least `r_i`.

Part 4, the part on `ω`. For a clean `g ≠ 0`, `ω(g') ≤ ω(g)`, with `ω = cpOmega` of Volume 6,
Definition 3.2.5 and the new divisor `Δ ∪ {j}` (`cpOmega_originTransform_le`). The proof is not the
elementary one of the handbook. It is the special case `t = 0` of `cpOmega_cleanPart_le`, which
comes from `ω = ρ` and Volume 7, Theorem 3.2.4.

The handbook works with the strict transform `h' = Z'^p + F'` and sets `ω(x') = 0` when
`m(x') < p`. The statement here compares `cpOmega` of `g'` and of `g` in all cases, and this gives
the statement of the handbook when `m(x') = p`. The invariant `ι` and the claim `ι(x') ≤ ι(x)` are
not formalized.

## Main results

* `ord_residualFactor_originTransform_add_le`: part 3, `ε' + a_j ≤ ε + r_j`.
* `ord_residualFactor_originTransform_add_le_of_notMem`: part 3 for `j ∉ Δ`, `ε' + a_j ≤ ε`.
* `ord_residualFactor_originTransform_le`: part 3, `ε' ≤ ε`.
* `cpOmega_originTransform_le`: part 4, `ω(g') ≤ ω(g)`.

## References

* Volume 6, Section 4.3 of the handbook: Proposition 4.3.4.
-/

open MvPolynomial Finsupp

namespace Singularity

open OriginRuns

section ResidualOrder

variable {σ k : Type*} [Fintype σ] [DecidableEq σ] [Field k] {p : ℕ} {Δ : Finset σ} {j : σ}
  {g : MvPolynomial σ k}

omit [Fintype σ] in
/-- A lower bound for the entry `i ∈ Δ` of `divisorExponent Δ P`: if `n ≤ β_i` for each exponent
`β` of `P ≠ 0`, then `n ≤ r_i`. -/
theorem le_divisorExponent_apply_of_forall {P : MvPolynomial σ k} (hP : P ≠ 0) {i : σ}
    (hi : i ∈ Δ) {n : ℕ} (h : ∀ β ∈ P.support, n ≤ β i) : n ≤ divisorExponent Δ P i := by
  rw [divisorExponent_apply, if_pos hi]
  obtain ⟨β, hβ⟩ := Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hP)
  exact le_csInf ⟨_, β, hβ, rfl⟩ (by rintro _ ⟨β', hβ', rfl⟩; exact h β' hβ')

omit [Fintype σ] [DecidableEq σ] in
/-- The residual order of a polynomial `f ≠ 0` is finite. -/
theorem exists_ord_residualFactor_eq_natCast (Δ : Finset σ) {f : MvPolynomial σ k} (hf : f ≠ 0) :
    ∃ e : ℕ, ord (residualFactor Δ f) = e := by
  have hG : residualFactor Δ f ≠ 0 := by
    intro h0
    apply hf
    rw [← monomial_mul_residualFactor Δ f, h0, mul_zero]
  exact ⟨(ord (residualFactor Δ f)).toNat, (ENat.natCast_toNat (ord_ne_top hG)).symm⟩

omit [Fintype σ] [DecidableEq σ] in
/-- The order of `f = x^r G` is `|r| + ord G`. -/
theorem ord_eq_degree_divisorExponent_add_ord (Δ : Finset σ) (f : MvPolynomial σ k) :
    ord f = ((divisorExponent Δ f).degree : ℕ∞) + ord (residualFactor Δ f) := by
  conv_lhs => rw [← monomial_mul_residualFactor Δ f]
  rw [ord_mul, ord_monomial one_ne_zero]

/-- The degree of the new exponent: `|a'| + p + a_j = 2 |a|`, for `|a| ≥ p`. -/
theorem degree_expStep_add_add (j : σ) {e : σ →₀ ℕ} (he : p ≤ e.degree) :
    (expStep p j e).degree + p + e j = 2 * e.degree := by
  have h1 : e.degree = e j + ∑ i ∈ Finset.univ.erase j, e i := by
    rw [degree_eq_sum']
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  have h2 : (expStep p j e).degree =
      expStep p j e j + ∑ i ∈ Finset.univ.erase j, expStep p j e i := by
    rw [degree_eq_sum']
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  have h3 : ∑ i ∈ Finset.univ.erase j, expStep p j e i = ∑ i ∈ Finset.univ.erase j, e i :=
    Finset.sum_congr rfl fun i hi => expStep_apply_of_ne p (Finset.ne_of_mem_erase hi) e
  rw [h3, expStep_apply_self] at h2
  omega

/-- **Proposition 4.3.4, part 3** (Volume 6, Section 4.3 of the handbook). Let `ord g ≥ p`, let
`g' = originTransform p j g` be the polynomial at the origin of the `x_j`-chart, and let `x^a` be a
monomial of `g` of degree `ord g`. Then `ε' + a_j ≤ ε + r_j`, with `ε = ord G` along `Δ`,
`ε' = ord G'` along `Δ ∪ {j}` and `r = divisorExponent Δ g`. -/
theorem ord_residualFactor_originTransform_add_le (hg : g ≠ 0) (hp : (p : ℕ∞) ≤ ord g)
    {a : σ →₀ ℕ} (ha : a ∈ g.support) (hda : ord g = (a.degree : ℕ∞)) :
    ord (residualFactor (insert j Δ) (originTransform p j g)) + (a j : ℕ∞) ≤
      ord (residualFactor Δ g) + (divisorExponent Δ g j : ℕ∞) := by
  have hD : DegreeGe p g := degreeGe_of_le_ord hp
  have hg' : originTransform p j g ≠ 0 := originTransform_ne_zero j hD hg
  obtain ⟨e, he⟩ := exists_ord_residualFactor_eq_natCast Δ hg
  obtain ⟨e', he'⟩ := exists_ord_residualFactor_eq_natCast (insert j Δ) hg'
  have hpd : p ≤ a.degree := hD a ha
  have h0 : a.degree = (divisorExponent Δ g).degree + e := by
    have h := ord_eq_degree_divisorExponent_add_ord Δ g
    rw [hda, he] at h
    exact_mod_cast h
  have hcoeff : (originTransform p j g).coeff (expStep p j a) ≠ 0 := by
    rw [coeff_originTransform_expStep j hD hpd]
    exact MvPolynomial.mem_support_iff.mp ha
  have h1 : (divisorExponent (insert j Δ) (originTransform p j g)).degree + e' ≤
      (expStep p j a).degree := by
    have h := ord_le hcoeff
    rw [ord_eq_degree_divisorExponent_add_ord (insert j Δ), he'] at h
    exact_mod_cast h
  have h2 := degree_expStep_add_add j hpd
  have hlow : ∀ i ∈ insert j Δ, (if i = j then a.degree - p else divisorExponent Δ g i) ≤
      divisorExponent (insert j Δ) (originTransform p j g) i := by
    intro i hi
    refine le_divisorExponent_apply_of_forall hg' hi fun β hβ => ?_
    rw [support_originTransform j hD, Finset.mem_image] at hβ
    obtain ⟨b, hb, rfl⟩ := hβ
    have hdb : a.degree ≤ b.degree := by
      have h := ord_le (MvPolynomial.mem_support_iff.mp hb)
      rw [hda] at h
      exact_mod_cast h
    split_ifs with hij
    · rw [hij, expStep_apply_self]
      omega
    · rw [expStep_apply_of_ne p hij]
      exact divisorExponent_le hb i
  have hsum : ∑ i ∈ insert j Δ, (if i = j then a.degree - p else divisorExponent Δ g i) ≤
      (divisorExponent (insert j Δ) (originTransform p j g)).degree := by
    calc _ ≤ ∑ i ∈ insert j Δ, divisorExponent (insert j Δ) (originTransform p j g) i :=
          Finset.sum_le_sum hlow
      _ ≤ ∑ i, divisorExponent (insert j Δ) (originTransform p j g) i :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = _ := (degree_eq_sum' _).symm
  have hsplit : ∑ i ∈ insert j Δ, (if i = j then a.degree - p else divisorExponent Δ g i) =
      (a.degree - p) + ∑ i ∈ Δ.erase j, divisorExponent Δ g i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_insert_self j Δ), Finset.erase_insert_eq_erase]
    exact congrArg₂ (· + ·) (by simp)
      (Finset.sum_congr rfl fun i hi => if_neg (Finset.ne_of_mem_erase hi))
  have hr : (divisorExponent Δ g).degree =
      divisorExponent Δ g j + ∑ i ∈ Δ.erase j, divisorExponent Δ g i := by
    rw [degree_eq_sum', ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    congr 1
    symm
    refine Finset.sum_subset (fun i hi => ?_) fun i hi hni => ?_
    · exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hi, Finset.mem_univ i⟩
    · exact divisorExponent_eq_zero fun hiΔ =>
        hni (Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hi, hiΔ⟩)
  rw [hsplit] at hsum
  rw [he, he']
  have key : e' + a j ≤ e + divisorExponent Δ g j := by omega
  exact_mod_cast key

/-- **Proposition 4.3.4, part 3, for `j ∉ Δ`** (Volume 6, Section 4.3 of the handbook). If
`j ∉ Δ`, then `ε' + a_j ≤ ε` for each monomial `x^a` of `g` of degree `ord g`. -/
theorem ord_residualFactor_originTransform_add_le_of_notMem (hj : j ∉ Δ) (hg : g ≠ 0)
    (hp : (p : ℕ∞) ≤ ord g) {a : σ →₀ ℕ} (ha : a ∈ g.support) (hda : ord g = (a.degree : ℕ∞)) :
    ord (residualFactor (insert j Δ) (originTransform p j g)) + (a j : ℕ∞) ≤
      ord (residualFactor Δ g) := by
  have h := ord_residualFactor_originTransform_add_le (Δ := Δ) (j := j) hg hp ha hda
  rwa [divisorExponent_eq_zero hj, Nat.cast_zero, add_zero] at h

/-- **Proposition 4.3.4, part 3, `ε' ≤ ε`** (Volume 6, Section 4.3 of the handbook). At the origin
of the `x_j`-chart, the residual order along `Δ ∪ {j}` of `g'` is at most the residual order along
`Δ` of `g`. -/
theorem ord_residualFactor_originTransform_le (hg : g ≠ 0) (hp : (p : ℕ∞) ≤ ord g) :
    ord (residualFactor (insert j Δ) (originTransform p j g)) ≤ ord (residualFactor Δ g) := by
  obtain ⟨a, ha, hda⟩ := exists_coeff_ne_zero_and_ord_eq hg
  have ha' : a ∈ g.support := MvPolynomial.mem_support_iff.mpr ha
  have h := ord_residualFactor_originTransform_add_le (Δ := Δ) (j := j) hg hp ha' hda
  have hra : divisorExponent Δ g j ≤ a j := divisorExponent_le ha' j
  have hg' : originTransform p j g ≠ 0 := originTransform_ne_zero j (degreeGe_of_le_ord hp) hg
  obtain ⟨e, he⟩ := exists_ord_residualFactor_eq_natCast Δ hg
  obtain ⟨e', he'⟩ := exists_ord_residualFactor_eq_natCast (insert j Δ) hg'
  rw [he, he'] at h ⊢
  have h' : e' + a j ≤ e + divisorExponent Δ g j := by exact_mod_cast h
  exact_mod_cast (show e' ≤ e by omega)

end ResidualOrder

section Omega

variable {σ k : Type*} [Fintype σ] [DecidableEq σ] [Field k] [DecidableEq k] {p : ℕ} [CharP k p]
  {Δ : Finset σ} {j : σ} {g : MvPolynomial σ k}

/-- **Proposition 4.3.4, part 4, the part on `ω`** (Volume 6, Section 4.3 of the handbook). Let
`g ≠ 0` be clean with `ord g ≥ p`. At the origin of the `x_j`-chart, with the new divisor
`Δ ∪ {j}`, `ω(g') ≤ ω(g)` for `ω = cpOmega` (Volume 6, Definition 3.2.5). No cleaning is needed,
since `g'` is clean. This is the case `t = 0` of `cpOmega_cleanPart_le`. -/
theorem cpOmega_originTransform_le (hg : g ≠ 0) (hc : IsClean p g) (hp : (p : ℕ∞) ≤ ord g) :
    cpOmega (insert j Δ) (originTransform p j g) ≤ cpOmega Δ g := by
  have hD : DegreeGe p g := degreeGe_of_le_ord hp
  have h := cpOmega_cleanPart_le p (Δ := Δ) hg hc hp (pointChart_eq_X_pow_mul_originTransform j hD)
  rwa [cleanPart_eq_self (isClean_originTransform j hD hc), blowupDivisor_zero] at h

end Omega

end Singularity
