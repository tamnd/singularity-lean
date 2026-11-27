/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianBlowupLocal

/-!
# The transformation law at a point of the chart that is not the origin

Let `k` be a field of characteristic `p`, and let `π₀ = pointChart j 0` be the chart of `x_j` of
the blowup of the origin, with no translation. A `k`-rational point `x'` of the exceptional
divisor in this chart has the coordinates `t : σ → k` with `t_j = 0`. In general `x'` is not the
origin of the chart. Let `π₀(g) = x_j^p g'`.

Theorem 3.11 of research note 03 says that at `x'`,

  `Θ_{E'}(g') = x_j^(-p) π^*Θ_C(g) O_{x'}`,

with `E' = {j} ∪ {i ∈ E : t_i = 0}` the new divisor. The library has this equality in the local
ring of the origin of the chart, for the chart `pointChart j t` that contains the translation
(`map_logJacobian_eq_map_pointChart`). This file proves the equality in the local ring `O_{x'}` of
`k[x]` at the point `t` itself, for the chart `π₀` with no translation:

  `(x_j^p) Θ'(g') O_{x'} = π₀(Θ₀(g)) O_{x'}`,

with `Θ'` the log-Jacobian ideal for `Δ' = blowupDivisor Δ j t`.

The proof. Let `τ_t` be the translation `x_i ↦ x_i + t_i` (`translateBy t`). It commutes with
each partial derivative (`pderiv_translateBy`), and it fixes `x_i` for `t_i = 0`. So it sends
`Θ'(h)` to `Θ'(τ_t h)` (`map_translateBy_logJacobian`). Since `t_j = 0`,
`pointChart j t = τ_t ∘ π₀` (`pointChart_eq_translateBy_comp`). The translation `τ_(-t)` is the
inverse of `τ_t`. So the two inclusions of the law for `pointChart j t` and `τ_t g'` give, after
`τ_(-t)`, the two inclusions for `π₀` and `g'`
(`map_pointChart_zero_logJacobianTangent_le_span_mul`,
`span_mul_logJacobian_le_map_pointChart_zero`). The factor of the second inclusion is
`τ_(-t)(blowupUnit Δ j t) = ∏ x_i`, over the `i ∈ Δ` with `i ≠ j` and `t_i ≠ 0`. Its value at
`t` is not `0`, so it is a unit in `O_{x'}`.

## Main definitions

* `translateBy t`: the translation `x_i ↦ x_i + t_i` of `k[x]`.
* `chartPointIdeal t`: the maximal ideal of the point `t`, the kernel of the evaluation at `t`.
* `ChartPointLocalRing t`: the localization of `k[x]` at `chartPointIdeal t`.

## Main results

* `pderiv_translateBy`: `∂_i τ_t(h) = τ_t(∂_i h)`.
* `pointChart_eq_translateBy_comp`: `pointChart j t = τ_t ∘ pointChart j 0` if `t_j = 0`.
* `map_translateBy_logJacobian`: `τ_t(Θ(h)) = Θ(τ_t h)` if `t_i = 0` for each `i ∈ Δ`.
* `map_pointChart_zero_logJacobianTangent_le_span_mul`,
  `span_mul_logJacobian_le_map_pointChart_zero`: the two inclusions of the law in `k[x]`.
* `map_logJacobian_eq_map_pointChart_zero`: Theorem 3.11 of research note 03 as an equality of
  ideals of the local ring of `k[x]` at the point `t`.

## References

* Research note 03, Section 3.5: Definition 3.10 and Theorem 3.11.
* Volume 7, Section 3.2 of the handbook: Theorem 3.2.3.
-/

open MvPolynomial

namespace Singularity

section Translate

variable {σ k : Type*} [CommRing k]

/-- **The translation** `x_i ↦ x_i + t_i` of `k[x_i : i ∈ σ]`. It sends the point `t` to the
origin: `τ_t(h)(0) = h(t)` (`constantCoeff_translateBy`). -/
noncomputable def translateBy (t : σ → k) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval fun i => X i + C (t i)

theorem translateBy_X (t : σ → k) (i : σ) : translateBy t (X i) = X i + C (t i) := by
  simp [translateBy]

theorem translateBy_X_of_eq_zero {t : σ → k} {i : σ} (hi : t i = 0) :
    translateBy t (X i) = X i := by
  rw [translateBy_X, hi, map_zero, add_zero]

/-- `τ_(-t) ∘ τ_t` is the identity. -/
theorem translateBy_neg_comp (t : σ → k) :
    (translateBy (-t)).comp (translateBy t) = AlgHom.id k (MvPolynomial σ k) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp only [AlgHom.comp_apply, translateBy, aeval_X, map_add, aeval_C, algebraMap_eq,
    Pi.neg_apply, map_neg, AlgHom.id_apply]
  ring

theorem translateBy_neg_apply (t : σ → k) (h : MvPolynomial σ k) :
    translateBy (-t) (translateBy t h) = h := by
  rw [← AlgHom.comp_apply, translateBy_neg_comp, AlgHom.id_apply]

theorem translateBy_apply_neg (t : σ → k) (h : MvPolynomial σ k) :
    translateBy t (translateBy (-t) h) = h := by
  simpa using translateBy_neg_apply (-t) h

/-- The constant term of `τ_t(h)` is the value of `h` at `t`. -/
theorem constantCoeff_translateBy (t : σ → k) (h : MvPolynomial σ k) :
    constantCoeff (translateBy t h) = eval t h := by
  induction h using MvPolynomial.induction_on with
  | C a => simp [translateBy]
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ, map_add]
  | mul_X P l hP => simp [hP, translateBy_X]

/-- **The translation commutes with the partial derivatives**: `∂_i τ_t(h) = τ_t(∂_i h)`. -/
theorem pderiv_translateBy [DecidableEq σ] (t : σ → k) (i : σ) (h : MvPolynomial σ k) :
    pderiv i (translateBy t h) = translateBy t (pderiv i h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp [translateBy]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P l hP =>
    have hl : pderiv i (translateBy t (X l)) = translateBy t (pderiv i (X l)) := by
      rw [translateBy_X, map_add, pderiv_C, add_zero]
      by_cases hli : l = i
      · subst hli
        rw [pderiv_X_self, map_one]
      · rw [pderiv_X_of_ne hli, map_zero]
    rw [map_mul, pderiv_mul, pderiv_mul, hP, hl, map_add, map_mul, map_mul]

/-- `τ_t(x_i ∂_i h) = x_i ∂_i τ_t(h)` if `t_i = 0`. -/
theorem translateBy_X_mul_pderiv [DecidableEq σ] {t : σ → k} {i : σ} (hi : t i = 0)
    (h : MvPolynomial σ k) :
    translateBy t (X i * pderiv i h) = X i * pderiv i (translateBy t h) := by
  rw [map_mul, translateBy_X_of_eq_zero hi, pderiv_translateBy]

/-- **The translation and the log-Jacobian ideal**: if `t_i = 0` for each `i ∈ Δ`, then
`τ_t(Θ(h)) = Θ(τ_t h)`. -/
theorem map_translateBy_logJacobian [DecidableEq σ] {Δ : Finset σ} {t : σ → k}
    (ht : ∀ i ∈ Δ, t i = 0) (h : MvPolynomial σ k) :
    Ideal.map (translateBy t) (logJacobian Δ h) = logJacobian Δ (translateBy t h) := by
  rw [logJacobian, logJacobian, Ideal.map_span, Set.image_union, Set.image_image,
    Set.image_image]
  congr 2
  · exact Set.image_congr fun i hi => translateBy_X_mul_pderiv (ht i hi) h
  · exact Set.image_congr fun i _ => (pderiv_translateBy t i h).symm

/-- **The chart with a translation**: if `t_j = 0`, then `pointChart j t = τ_t ∘ pointChart j 0`.
-/
theorem pointChart_eq_translateBy_comp [DecidableEq σ] {j : σ} {t : σ → k} (ht : t j = 0) :
    pointChart j t = (translateBy t).comp (pointChart j 0) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply]
  by_cases hij : i = j
  · subst hij
    rw [pointChart_X_self, pointChart_X_self, translateBy_X_of_eq_zero ht]
  · rw [pointChart_X_of_ne t hij, pointChart_X_of_ne 0 hij, Pi.zero_apply, map_zero, add_zero,
      map_mul, translateBy_X_of_eq_zero ht, translateBy_X]

end Translate

section Law

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

omit [Fintype σ] in
/-- The translation `τ_(-t)` fixes `x_i` for each `i` of the new divisor `blowupDivisor Δ j t`, if
`t_j = 0`. -/
theorem neg_apply_eq_zero_of_mem_blowupDivisor (ht : t j = 0) {i : σ}
    (hi : i ∈ blowupDivisor Δ j t) : (-t) i = 0 := by
  rw [Pi.neg_apply, neg_eq_zero]
  rcases mem_blowupDivisor.mp hi with rfl | ⟨_, _, hi⟩
  · exact ht
  · exact hi

omit [DecidableEq k] [Fintype σ] [CharP k p] in
/-- The new function at the point `t` and at the origin: if `π₀(g) = x_j^p g'` and `t_j = 0`, then
`pointChart j t g = x_j^p τ_t(g')`. -/
theorem pointChart_eq_X_pow_mul_translateBy (ht : t j = 0) (hg : pointChart j 0 g = X j ^ p * g') :
    pointChart j t g = X j ^ p * translateBy t g' := by
  rw [pointChart_eq_translateBy_comp ht, AlgHom.comp_apply, hg, map_mul, map_pow,
    translateBy_X_of_eq_zero ht]

omit [DecidableEq k] [Fintype σ] in
/-- `τ_(-t) ∘ pointChart j t = pointChart j 0` if `t_j = 0`. -/
theorem translateBy_neg_comp_pointChart (ht : t j = 0) :
    (translateBy (-t)).comp (pointChart j t) = pointChart j 0 := by
  rw [pointChart_eq_translateBy_comp ht, ← AlgHom.comp_assoc, translateBy_neg_comp,
    AlgHom.id_comp]

omit [DecidableEq σ] [DecidableEq k] [Fintype σ] in
/-- `(-t)_j = 0` if `t_j = 0`. -/
theorem neg_apply_self_eq_zero (ht : t j = 0) : (-t) j = 0 := by
  rw [Pi.neg_apply, ht, neg_zero]

omit [DecidableEq k] [Fintype σ] in
/-- `τ_(-t)(pointChart j t (I)) = pointChart j 0 (I)` if `t_j = 0`. -/
theorem map_translateBy_neg_map_pointChart (ht : t j = 0) (I : Ideal (MvPolynomial σ k)) :
    Ideal.map (translateBy (-t)) (Ideal.map (pointChart j t) I) = Ideal.map (pointChart j 0) I := by
  rw [← translateBy_neg_comp_pointChart ht]
  exact Ideal.map_map (pointChart j t).toRingHom (translateBy (-t)).toRingHom

omit [Fintype σ] in
/-- The image of the ideal of the new point under `τ_(-t)`. -/
theorem map_translateBy_neg_span_mul (ht : t j = 0) (a : MvPolynomial σ k) :
    Ideal.map (translateBy (-t)) (Ideal.span {a} * logJacobian (blowupDivisor Δ j t)
        (translateBy t g')) =
      Ideal.span {translateBy (-t) a} * logJacobian (blowupDivisor Δ j t) g' := by
  rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton,
    map_translateBy_logJacobian (fun i hi => neg_apply_eq_zero_of_mem_blowupDivisor ht hi),
    translateBy_neg_apply]

/-- **The transformation law at the point `t`** (research note 03, Theorem 3.11, first inclusion):
if `t_j = 0` and `π₀(g) = x_j^p g'` for `π₀ = pointChart j 0`, then
`π₀(Θ₀(g)) ⊆ (x_j^p) Θ'(g')`, with `Θ'` the log-Jacobian ideal for `blowupDivisor Δ j t`. -/
theorem map_pointChart_zero_logJacobianTangent_le_span_mul (ht : t j = 0)
    (hg : pointChart j 0 g = X j ^ p * g') :
    Ideal.map (pointChart j 0) (logJacobianTangent Δ g) ≤
      Ideal.span {X j ^ p} * logJacobian (blowupDivisor Δ j t) g' := by
  have h := Ideal.map_mono (f := translateBy (-t))
    (map_pointChart_logJacobianTangent_le_span_mul (Δ := Δ) p
      (pointChart_eq_X_pow_mul_translateBy p ht hg))
  rwa [map_translateBy_neg_map_pointChart ht, map_translateBy_neg_span_mul ht, map_pow,
    translateBy_X_of_eq_zero (neg_apply_self_eq_zero ht)] at h

omit [Fintype σ] in
/-- The factor of the second inclusion at the point `t`: `τ_(-t)(blowupUnit Δ j t)`, the product of
the `x_i` over the `i ∈ Δ` with `i ≠ j` and `t_i ≠ 0`. Its value at `t` is not `0`. -/
theorem eval_translateBy_neg_blowupUnit_ne_zero (Δ : Finset σ) (j : σ) (t : σ → k) :
    eval t (translateBy (-t) (blowupUnit Δ j t)) ≠ 0 := by
  rw [← constantCoeff_translateBy, translateBy_apply_neg]
  exact constantCoeff_blowupUnit_ne_zero Δ j t

/-- **The transformation law at the point `t`** (research note 03, Theorem 3.11, second
inclusion): if `t_j = 0` and `π₀(g) = x_j^p g'`, then `(x_j^p v) Θ'(g') ⊆ π₀(Θ₀(g))`, with
`v = τ_(-t)(blowupUnit Δ j t)`. The value of `v` at `t` is not `0`
(`eval_translateBy_neg_blowupUnit_ne_zero`). -/
theorem span_mul_logJacobian_le_map_pointChart_zero (ht : t j = 0)
    (hg : pointChart j 0 g = X j ^ p * g') :
    Ideal.span {X j ^ p * translateBy (-t) (blowupUnit Δ j t)} *
        logJacobian (blowupDivisor Δ j t) g' ≤
      Ideal.map (pointChart j 0) (logJacobianTangent Δ g) := by
  have h := Ideal.map_mono (f := translateBy (-t))
    (span_mul_logJacobian_le_map_pointChart (Δ := Δ) p
      (pointChart_eq_X_pow_mul_translateBy p ht hg))
  rwa [map_translateBy_neg_map_pointChart ht, map_translateBy_neg_span_mul ht, map_mul, map_pow,
    translateBy_X_of_eq_zero (neg_apply_self_eq_zero ht)] at h

end Law

section Local

variable {σ k : Type*} [Field k]

variable (k) in
/-- **The maximal ideal of the point `t`** of `k[x_i : i ∈ σ]`: the kernel of the evaluation at
`t`. -/
noncomputable def chartPointIdeal (t : σ → k) : Ideal (MvPolynomial σ k) :=
  RingHom.ker (eval t)

instance chartPointIdeal_isPrime (t : σ → k) : (chartPointIdeal k t).IsPrime :=
  RingHom.ker_isPrime _

variable (k) in
/-- **The local ring of the point `t`**: the localization of `k[x_i : i ∈ σ]` at the maximal ideal
of `t`. -/
abbrev ChartPointLocalRing (t : σ → k) : Type _ :=
  Localization.AtPrime (chartPointIdeal k t)

/-- A polynomial with a nonzero value at `t` is a unit in the local ring of `t`. -/
theorem isUnit_algebraMap_of_eval_ne_zero {t : σ → k} {f : MvPolynomial σ k} (hf : eval t f ≠ 0) :
    IsUnit (algebraMap (MvPolynomial σ k) (ChartPointLocalRing k t) f) :=
  IsLocalization.map_units (ChartPointLocalRing k t)
    (⟨f, fun h => hf (RingHom.mem_ker.mp h)⟩ : (chartPointIdeal k t).primeCompl)

variable [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p] {Δ : Finset σ} {j : σ}
  {t : σ → k} {g g' : MvPolynomial σ k}

/-- **The transformation law as an equality at the point `t`** (research note 03, Theorem 3.11;
Volume 7, Section 3.2 of the handbook, Theorem 3.2.3). Let `π₀ = pointChart j 0`, let `t` be a
point of the exceptional divisor `x_j = 0` of the chart, and let `π₀(g) = x_j^p g'`. In the local
ring `O_{x'}` of `k[x]` at `t`, `(x_j^p) Θ'(g') O_{x'} = π₀(Θ₀(g)) O_{x'}`, with `Θ'` the
log-Jacobian ideal for the new divisor `blowupDivisor Δ j t`. -/
theorem map_logJacobian_eq_map_pointChart_zero (ht : t j = 0)
    (hg : pointChart j 0 g = X j ^ p * g') :
    Ideal.map (algebraMap (MvPolynomial σ k) (ChartPointLocalRing k t))
        (Ideal.span {X j ^ p} * logJacobian (blowupDivisor Δ j t) g') =
      Ideal.map (algebraMap (MvPolynomial σ k) (ChartPointLocalRing k t))
        (Ideal.map (pointChart j 0) (logJacobianTangent Δ g)) := by
  set L := algebraMap (MvPolynomial σ k) (ChartPointLocalRing k t)
  refine le_antisymm ?_
    (Ideal.map_mono (map_pointChart_zero_logJacobianTangent_le_span_mul p ht hg))
  have hu : Ideal.map L (Ideal.span {translateBy (-t) (blowupUnit Δ j t)}) = ⊤ := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top]
    exact isUnit_algebraMap_of_eval_ne_zero (eval_translateBy_neg_blowupUnit_ne_zero Δ j t)
  calc Ideal.map L (Ideal.span {X j ^ p} * logJacobian (blowupDivisor Δ j t) g')
      = Ideal.map L (Ideal.span {X j ^ p} * Ideal.span {translateBy (-t) (blowupUnit Δ j t)} *
          logJacobian (blowupDivisor Δ j t) g') := by
        rw [Ideal.map_mul, Ideal.map_mul, Ideal.map_mul, hu, Ideal.mul_top]
    _ = Ideal.map L (Ideal.span {X j ^ p * translateBy (-t) (blowupUnit Δ j t)} *
          logJacobian (blowupDivisor Δ j t) g') := by
        rw [Ideal.span_singleton_mul_span_singleton]
    _ ≤ Ideal.map L (Ideal.map (pointChart j 0) (logJacobianTangent Δ g)) :=
        Ideal.map_mono (span_mul_logJacobian_le_map_pointChart_zero p ht hg)

end Local

end Singularity
