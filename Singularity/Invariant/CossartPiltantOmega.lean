/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianCenterNonincrease

/-!
# The invariant `ω` of Cossart and Piltant is the log-Jacobian order `ρ`

Let `k` be a field of characteristic `p`, let `g` be a polynomial in `k[x_i : i ∈ σ]`, and let `Δ`
give the divisor `E = V(∏_{i ∈ Δ} x_i)`. Write `g = x^r G`, with `r = divisorExponent Δ g` and
`G = residualFactor Δ g`. The residual order is `ε = ord G`. Let `F` be the initial form of `g`,
that is, the homogeneous component of `g` of degree `ord g`. Volume 6, Definition 3.2.5 of the
handbook defines the invariant `ω` of Cossart and Piltant [CP19, Definition 2.68] for the purely
inseparable equation `z^p + g`:

* `ω = ε - 1` if `∂_j F ≠ 0` for some free coordinate `x_j`, `j ∉ Δ`,
* `ω = ε` otherwise.

The definition `cpOmega Δ g` encodes this. The initial form is `homogeneousComponent n g` with
`n = (ord g).toNat`. For `g ≠ 0`, the order `ord g` is finite, so `n = ord g`.

For a clean `g ≠ 0`, `ω = ρ`, with `ρ = logJacobianOrder Δ g` the order of the residual
log-Jacobian ideal (Volume 7, Section 3.6 of the handbook, Proposition 3.6.1). The proof is short.
Since `r` is supported in `Δ`, the initial form of `g` is `F = x^r in(G)`
(`homogeneousComponent_monomial_mul`), and `∂_j F = x^r ∂_j in(G)` for `j ∉ Δ`
(`pderiv_monomial_mul_of_eq_zero`). So the condition of Definition 3.2.5 is the condition of the
dichotomy of Volume 7, Theorem 3.1.4 (`logJacobianOrder_add_one_eq_iff`,
`logJacobianOrder_eq_iff`).

So `ω` does not depend on the coordinates that keep `E`, because `ρ` does not depend on them. This
is a direct proof of [CP19, Remark 2.69] for the purely inseparable equations. The theorems on `ρ`
also give these results.

* `ω` does not go up under a point blowup (Corollary 3.6.2, from Volume 7, Theorem 3.2.4).
* `ω` does not go up under the blowup of a regular center with the conditions (H1) and (H2)
  (Corollary 3.6.3, from Volume 7, Theorem 3.4.5).
* In Volume 7, Example 3.4.6, `ω` goes up from `2` to `3` (Example 3.6.4). Condition (H2) fails
  there. Condition (E) of [CP19] also fails, so this does not contradict [CP19, Theorem 3.13].

## Main definitions

* `Singularity.cpOmega Δ g`: the invariant `ω` of Volume 6, Definition 3.2.5.

## Main results

* `cpOmega_eq_logJacobianOrder`: Proposition 3.6.1, `ω = ρ` for a clean `g ≠ 0`.
* `cpOmega_cleanPart_le`: Corollary 3.6.2, `ω(g'_c) ≤ ω(g)` under a point blowup.
* `cpOmega_cleanPart_le_center`: Corollary 3.6.3, `ω(g'_c) ≤ ω(g)` under the blowup of a regular
  center with (H1) and (H2).
* `centerExample_cpOmega`, `centerExample_cpOmega_cleanPart`, `centerExample_cpOmega_lt`:
  Example 3.6.4, `ω` goes up from `2` to `3`.

## References

* [CP19] V. Cossart, O. Piltant, *Resolution of singularities of arithmetical threefolds*,
  J. Algebra 529 (2019), arXiv:1412.0868, Definition 2.68 and Remark 2.69.
* Volume 6, Section 3.2 of the handbook: Definition 3.2.5.
* Volume 7, Section 3.6 of the handbook: Proposition 3.6.1, Corollaries 3.6.2 and 3.6.3, and
  Example 3.6.4.
-/

open MvPolynomial Finsupp

namespace Singularity

/-! ### The definition -/

section Def

variable {σ k : Type*} [CommSemiring k]

open Classical in
/-- The invariant `ω` of Cossart and Piltant (Volume 6, Definition 3.2.5 of the handbook,
[CP19, Definition 2.68]) for the purely inseparable equation `z^p + g` along the divisor
`E = V(∏_{i ∈ Δ} x_i)`. Let `ε = ord G` be the residual order, with `G = residualFactor Δ g`, and
let `F` be the initial form of `g`, the homogeneous component of `g` of degree `ord g`. Then
`ω = ε - 1` if `∂_j F ≠ 0` for some `j ∉ Δ`, and `ω = ε` otherwise. For `g = 0`, `ω = ⊤`. -/
noncomputable def cpOmega (Δ : Finset σ) (g : MvPolynomial σ k) : ℕ∞ :=
  if ∃ j ∉ Δ, pderiv j (homogeneousComponent (ord g).toNat g) ≠ 0 then
    ord (residualFactor Δ g) - 1
  else ord (residualFactor Δ g)

/-- The first case of Definition 3.2.5: if `∂_j F ≠ 0` for some `j ∉ Δ`, then `ω = ε - 1`. -/
theorem cpOmega_of_exists {Δ : Finset σ} {g : MvPolynomial σ k}
    (h : ∃ j ∉ Δ, pderiv j (homogeneousComponent (ord g).toNat g) ≠ 0) :
    cpOmega Δ g = ord (residualFactor Δ g) - 1 := by
  rw [cpOmega, ite_eq_left h]

/-- The second case of Definition 3.2.5: if `∂_j F = 0` for each `j ∉ Δ`, then `ω = ε`. -/
theorem cpOmega_of_forall {Δ : Finset σ} {g : MvPolynomial σ k}
    (h : ∀ j ∉ Δ, pderiv j (homogeneousComponent (ord g).toNat g) = 0) :
    cpOmega Δ g = ord (residualFactor Δ g) := by
  rw [cpOmega, ite_eq_right fun ⟨j, hj, hne⟩ => hne (h j hj)]

end Def

/-! ### The initial form of `x^r G` -/

section InitialForm

variable {σ k : Type*} [CommSemiring k]

/-- The homogeneous component of degree `|r| + m` of `x^r G` is `x^r` times the homogeneous
component of degree `m` of `G`. -/
theorem homogeneousComponent_monomial_mul (r : σ →₀ ℕ) (m : ℕ) (G : MvPolynomial σ k) :
    homogeneousComponent (degree r + m) (monomial r 1 * G) =
      monomial r 1 * homogeneousComponent m G := by
  classical
  ext b
  rw [coeff_homogeneousComponent, coeff_monomial_mul', coeff_monomial_mul']
  by_cases hrb : r ≤ b
  · obtain ⟨c, rfl⟩ : ∃ c, b = r + c := ⟨b - r, (add_tsub_cancel_of_le hrb).symm⟩
    rw [ite_eq_left hrb, ite_eq_left hrb, add_tsub_cancel_left, coeff_homogeneousComponent, map_add]
    simp only [one_mul, Nat.add_left_cancel_iff]
  · rw [ite_eq_right hrb, ite_eq_right hrb, ite_self]

/-- If `r_j = 0`, then `∂_j (x^r G) = x^r ∂_j G`. -/
theorem pderiv_monomial_mul_of_eq_zero {r : σ →₀ ℕ} {j : σ} (hj : r j = 0)
    (G : MvPolynomial σ k) : pderiv j (monomial r 1 * G) = monomial r 1 * pderiv j G := by
  rw [pderiv_mul, pderiv_monomial, hj, Nat.cast_zero, mul_zero, monomial_zero, zero_mul, zero_add]

end InitialForm

/-! ### `ω = ρ` -/

section Main

variable {σ k : Type*} [Field k] (p : ℕ) [CharP k p] {Δ : Finset σ} {g : MvPolynomial σ k}

omit [CharP k p] in
/-- The order `ρ` of `0` is `⊤`. -/
theorem logJacobianOrder_zero (Δ : Finset σ) : logJacobianOrder Δ (0 : MvPolynomial σ k) = ⊤ := by
  have h := idealOrd_logJacobian Δ (0 : MvPolynomial σ k)
  rw [logJacobian_zero, idealOrd_bot] at h
  rcases WithTop.add_eq_top.mp h.symm with h1 | h1
  · exact absurd h1 (ENat.natCast_ne_top _)
  · exact h1

omit [CharP k p] in
/-- If the order `ρ` of `g` is finite, then `g ≠ 0`. -/
theorem ne_zero_of_logJacobianOrder_ne_top (h : logJacobianOrder Δ g ≠ ⊤) : g ≠ 0 := by
  rintro rfl
  exact h (logJacobianOrder_zero Δ)

omit [CharP k p] in
/-- For `j ∉ Δ`, `∂_j F = x^r ∂_j in(G)`, with `F` the initial form of `g = x^r G` and `in(G)` the
homogeneous component of degree `ord G` of `G`. So `∂_j F ≠ 0` if and only if
`∂_j in(G) ≠ 0`. -/
theorem exists_pderiv_initialForm_ne_zero_iff {d : ℕ}
    (hd : ord (residualFactor Δ g) = d) :
    (∃ j ∉ Δ, pderiv j (homogeneousComponent (ord g).toNat g) ≠ 0) ↔
      ∃ j ∉ Δ, pderiv j (homogeneousComponent d (residualFactor Δ g)) ≠ 0 := by
  have hfac := monomial_mul_residualFactor Δ g
  have hord : ord g = ((degree (divisorExponent Δ g) + d : ℕ) : ℕ∞) := by
    conv_lhs => rw [← hfac]
    rw [ord_mul, ord_monomial one_ne_zero, hd, Nat.cast_add]
  have hin : homogeneousComponent (ord g).toNat g =
      monomial (divisorExponent Δ g) 1 * homogeneousComponent d (residualFactor Δ g) := by
    rw [hord, ENat.toNat_natCast, ← homogeneousComponent_monomial_mul, hfac]
  have hm0 : monomial (divisorExponent Δ g) (1 : k) ≠ 0 := by
    rw [Ne, monomial_eq_zero]
    exact one_ne_zero
  rw [hin]
  refine exists_congr fun j => and_congr_right fun hj => ?_
  rw [pderiv_monomial_mul_of_eq_zero (divisorExponent_eq_zero hj), Ne, mul_eq_zero, not_or]
  exact ⟨fun h => h.2, fun h => ⟨hm0, h⟩⟩

/-- **`ω = ρ`** (Volume 7, Section 3.6 of the handbook, Proposition 3.6.1). For a clean `g ≠ 0`,
the invariant `ω` of Cossart and Piltant (Volume 6, Definition 3.2.5, [CP19, Definition 2.68]) is
the order `ρ` of the residual log-Jacobian ideal. The initial form of `g = x^r G` is `x^r in(G)`,
and `∂_j (x^r in(G)) = x^r ∂_j in(G)` for `j ∉ Δ`. So the two cases of Definition 3.2.5 are the
two cases of the dichotomy of Volume 7, Theorem 3.1.4. Since `ρ` does not depend on the coordinates
that keep `E`, neither does `ω` [CP19, Remark 2.69]. -/
theorem cpOmega_eq_logJacobianOrder (hg : g ≠ 0) (hc : IsClean p g) :
    cpOmega Δ g = logJacobianOrder Δ g := by
  have hG : residualFactor Δ g ≠ 0 := by
    intro h0
    apply hg
    rw [← monomial_mul_residualFactor Δ g, h0, mul_zero]
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ord (residualFactor Δ g) = d :=
    ⟨(ord (residualFactor Δ g)).toNat, (ENat.natCast_toNat (ord_ne_top hG)).symm⟩
  have hiff := exists_pderiv_initialForm_ne_zero_iff hd
  by_cases hex : ∃ j ∉ Δ, pderiv j (homogeneousComponent d (residualFactor Δ g)) ≠ 0
  · rw [cpOmega_of_exists (hiff.mpr hex), hd]
    have h := (logJacobianOrder_add_one_eq_iff p hc hd).mpr hex
    cases hρ : logJacobianOrder Δ g using ENat.recTopCoe with
    | top =>
      rw [hρ, top_add] at h
      exact absurd h.symm (ENat.natCast_ne_top d)
    | coe m =>
      rw [hρ] at h
      have h' : m + 1 = d := by exact_mod_cast h
      have h'' : d - 1 = m := by omega
      exact_mod_cast h''
  · rw [cpOmega_of_forall fun j hj => ?_, hd]
    · refine ((logJacobianOrder_eq_iff p hc hd).mpr fun j hj => ?_).symm
      by_contra hne
      exact hex ⟨j, hj, hne⟩
    · by_contra hne
      exact hex (hiff.mp ⟨j, hj, hne⟩)

end Main

/-! ### `ω` does not go up -/

section PointBlowup

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- **`ω` does not go up under a point blowup** (Volume 7, Section 3.6 of the handbook,
Corollary 3.6.2). Let `g ≠ 0` be clean with `ord g ≥ p`, and let `π(g) = x_j^p g'` in the chart
`π = pointChart j t`. Then `ω(g'_c) ≤ ω(g)` for the clean part `g'_c` of `g'` and the new divisor
`Δ' = blowupDivisor Δ j t`. This follows from `ω = ρ` and Volume 7, Theorem 3.2.4
(`logJacobianOrder_cleanPart_le`). -/
theorem cpOmega_cleanPart_le (hg : g ≠ 0) (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g)
    (h : pointChart j t g = X j ^ p * g') :
    cpOmega (blowupDivisor Δ j t) (cleanPart p g') ≤ cpOmega Δ g := by
  obtain ⟨hne, hle⟩ := logJacobianOrder_cleanPart_le p (Δ := Δ) hg hc hord h
  rw [cpOmega_eq_logJacobianOrder p hne (isClean_cleanPart p g'),
    cpOmega_eq_logJacobianOrder p hg hc]
  exact hle

end PointBlowup

section CenterBlowup

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] (p : ℕ) [CharP k p]
  {Δ S : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- **`ω` does not go up under the blowup of a regular center** (Volume 7, Section 3.6 of the
handbook, Corollary 3.6.3). Let `j ∈ S`, let `g ∈ I_C^p` with `I_C = (x_i : i ∈ S)` be clean, and
let `π(g) = x_j^p g'` in the chart `π = centerChart S j t`. Assume the conditions (H1) and (H2) of
Volume 7, Theorem 3.4.5, in the elementary form of `logJacobianOrder_cleanPart_le_center`. Then
`ω(g'_c) ≤ ω(g)` for the clean part `g'_c` of `g'` and the new divisor
`Δ' = centerDivisor Δ S j t`. Since `ρ` is finite, `g ≠ 0`. -/
theorem cpOmega_cleanPart_le_center (hc : IsClean p g) (hj : j ∈ S)
    (hgS : g ∈ Ideal.span (X '' (S : Set σ)) ^ p) (h : centerChart S j t g = X j ^ p * g')
    {ρ : ℕ} (hρ : logJacobianOrder Δ g = ρ)
    (H1 : ∀ f ∈ logJacobian Δ g, ∃ q ∈ Ideal.span (X '' (S : Set σ)) ^ ρ,
      f = monomial (divisorExponent Δ g) 1 * q)
    (H2 : (∀ f ∈ logJacobianCenter Δ S g, ∃ q ∈ Ideal.span (X '' (S : Set σ)) ^ (ρ + 1),
        f = monomial (divisorExponent Δ g) 1 * q) ∨
      ∃ q, monomial (divisorExponent Δ g) 1 * q ∈ logJacobianCenter Δ S g ∧ ord q = ρ) :
    cpOmega (centerDivisor Δ S j t) (cleanPart p g') ≤ cpOmega Δ g := by
  have hg : g ≠ 0 := ne_zero_of_logJacobianOrder_ne_top (by rw [hρ]; exact ENat.natCast_ne_top ρ)
  obtain ⟨hne, hle⟩ := logJacobianOrder_cleanPart_le_center p hj hgS h hρ H1 H2
  rw [cpOmega_eq_logJacobianOrder p hne (isClean_cleanPart p g'),
    cpOmega_eq_logJacobianOrder p hg hc]
  exact hle

end CenterBlowup

/-! ### The example: `ω` goes up from `2` to `3` -/

section Example

/-- **Example 3.6.4, `ω(g) = 2`** (Volume 7, Section 3.6 of the handbook). Over `𝔽₂`, with the
coordinates `(x, y, w)`, let `g = y^2 w + y^3` and `Δ = {w}`, as in Volume 7, Example 3.4.6. Then
`ω(g) = ρ(g) = 2`. -/
theorem centerExample_cpOmega :
    cpOmega {2} (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) = 2 := by
  rw [cpOmega_eq_logJacobianOrder 2 centerExample_hyp.1 centerExample_hyp.2.1]
  exact centerExample_logJacobianOrder

/-- **Example 3.6.4, `ω(g'_c) = 3`** (Volume 7, Section 3.6 of the handbook). In the `x`-chart of
the blowup of `C = V(x, y)`, `g' = y^2 w + x y^3`, and the new divisor is `V(x w)`. Then
`ω(g'_c) = ρ(g'_c) = 3`. -/
theorem centerExample_cpOmega_cleanPart :
    cpOmega (centerDivisor ({2} : Finset (Fin 3)) {0, 1} 0 (0 : Fin 3 → ZMod 2))
      (cleanPart 2 (X 1 ^ 2 * X 2 + X 0 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2))) = 3 := by
  have hρ := centerExample_logJacobianOrder_cleanPart
  have hne : cleanPart 2 (X 1 ^ 2 * X 2 + X 0 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) ≠ 0 :=
    ne_zero_of_logJacobianOrder_ne_top (by rw [hρ]; exact ENat.natCast_ne_top 3)
  rw [cpOmega_eq_logJacobianOrder 2 hne (isClean_cleanPart 2 _)]
  exact hρ

/-- **Example 3.6.4, `ω` goes up** (Volume 7, Section 3.6 of the handbook). For the blowup of
`C = V(x, y)` in Volume 7, Example 3.4.6, `ω` goes up from `2` to `3`. The blowup is
Hironaka-permissible, (H1) holds and (H2) fails (`centerExample_H1`, `centerExample_not_H2`).
Condition (E) of [CP19] fails, so this does not contradict [CP19, Theorem 3.13]. -/
theorem centerExample_cpOmega_lt :
    cpOmega {2} (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) <
      cpOmega (centerDivisor ({2} : Finset (Fin 3)) {0, 1} 0 (0 : Fin 3 → ZMod 2))
        (cleanPart 2 (X 1 ^ 2 * X 2 + X 0 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2))) := by
  rw [centerExample_cpOmega, centerExample_cpOmega_cleanPart]
  norm_num

end Example

end Singularity
