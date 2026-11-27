/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.DerivativeOrder
import Singularity.Invariant.LogJacobianBlowup
import Singularity.Invariant.MaxOrderChart

/-!
# Derivatives and transforms under a point blowup

This file proves Volume 2, Theorem 2.2.7 of the handbook for one blowup of the origin of affine space, in the `x_j`-chart with translations `t` (`pointChart j t`). Let `k` be a field, let `σ` be finite, and let `I` be an ideal of `k[x_i : i ∈ σ]` with `m ≤ ord I` at the origin. So the origin is in the cosupport of the marked ideal `(I, m)`. The controlled transform of `(I, m)` in the chart is `chartTransformIdeal j t m I`.

* `Singularity.le_idealOrd_derivIdeal_iterate_sub`: `m - l ≤ ord D^l(I)`, so the origin is in the cosupport of `(D^l(I), m - l)` and the transform of this marked ideal is defined.
* `Singularity.pointChart_pderiv_of_ne`: if `π(f) = x_j^(n+1) g` and `i ≠ j`, then `π(∂_i f) = x_j^n ∂_i g` (Lemma 2.2.6, the case `i ≠ c`).
* `Singularity.chartTransformIdeal_derivIdeal_le`: the inclusion (2.2.1) of the handbook. If `1 ≤ m ≤ ord I`, the transform of `(D(I), m - 1)` is contained in `D` of the transform of `(I, m)`.
* `Singularity.chartTransformIdeal_derivIdeal_iterate_le`: Theorem 2.2.7 for this blowup. For `l ≤ m` the transform of `(D^l(I), m - l)` is contained in `D^l` of the transform of `(I, m)`.

The proof of (2.2.1) takes `f ∈ I` and writes `π(f) = x_j^m g`. Then `g`, `x_j g`, and `π(∂_i f) / x_j^(m-1)` for `i ≠ j` are in `D` of the transform. For `i = j` the chain rule `x_j ∂_j π(f) = π(∑_i x_i ∂_i f)` (`X_mul_pderiv_pointChart`) gives `x_j π(∂_j f)` as `x_j ∂_j π(f)` minus a sum of `x_j (x_i + t_i) π(∂_i f)` with `i ≠ j`. The theorem then follows by induction on `l`, with the lower bound `ord D(J) ≥ ord J - 1`.

The proof does not use the characteristic. In characteristic `p` the inclusion holds, but `D^m(I)` need not be the unit ideal, so Corollary 2.2.8 does not follow.

The handbook states Theorem 2.2.7 for blowup sequences with smooth centers. This file proves the case of one blowup of a point, at the points of the exceptional divisor in the `x_j`-chart, which are the origins of the translated charts. Centers of positive dimension and sequences of blowups are not in Lean.
-/

open MvPolynomial

namespace Singularity

variable {σ k : Type*} [Field k] [DecidableEq σ]

omit [DecidableEq σ] in
/-- The lower bound for the order of the iterated derivative ideal: if `m ≤ ord I`, then `m - l ≤ ord D^l(I)` for each `l`. This holds in every characteristic. -/
theorem le_idealOrd_derivIdeal_iterate_sub {I : Ideal (MvPolynomial σ k)} {m : ℕ}
    (hI : (m : ℕ∞) ≤ idealOrd I) (l : ℕ) :
    ((m - l : ℕ) : ℕ∞) ≤ idealOrd (derivIdeal^[l] I) := by
  induction l with
  | zero => simpa using hI
  | succ l ih =>
    rw [Function.iterate_succ_apply', ← Nat.sub_sub]
    exact le_idealOrd_derivIdeal ih

/-- Let `m ≤ ord f` with `m = n + 1`, and write `π(f) = x_j^m g`. For `i ≠ j`, the image of `∂_i f` under the chart is `x_j^n ∂_i g` (Volume 2, Lemma 2.2.6 of the handbook, the case `i ≠ c`). -/
theorem pointChart_pderiv_of_ne {i j : σ} (hij : i ≠ j) (t : σ → k) {n : ℕ}
    {f g : MvPolynomial σ k} (hg : pointChart j t f = X j ^ (n + 1) * g) :
    pointChart j t (pderiv i f) = X j ^ n * pderiv i g := by
  have h := pderiv_pointChart_of_ne hij t f
  rw [hg, pderiv_mul, pderiv_pow, pderiv_X_of_ne (Ne.symm hij), mul_zero, zero_mul, zero_add]
    at h
  have hX : (X j : MvPolynomial σ k) ≠ 0 := X_ne_zero j
  apply mul_left_cancel₀ hX
  rw [← h, pow_succ]
  ring

/-- Volume 2, the inclusion (2.2.1) of the handbook, for the blowup of the origin of affine space, in the `x_j`-chart with translations `t`. Let `1 ≤ m ≤ ord I`. Then the controlled transform of `(D(I), m - 1)` is contained in the derivative ideal of the controlled transform of `(I, m)`. -/
theorem chartTransformIdeal_derivIdeal_le [Fintype σ] (j : σ) (t : σ → k) {m : ℕ} (hm : 1 ≤ m)
    {I : Ideal (MvPolynomial σ k)} (hI : (m : ℕ∞) ≤ idealOrd I) :
    chartTransformIdeal j t (m - 1) (derivIdeal I) ≤
      derivIdeal (chartTransformIdeal j t m I) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  set T := chartTransformIdeal j t (n + 1) I
  set K : Ideal (MvPolynomial σ k) := Ideal.span {X j ^ n} * derivIdeal T
  have hX : (X j : MvPolynomial σ k) ≠ 0 := X_ne_zero j
  -- the factor `g` of an element `f` of `I`
  have hfac : ∀ f ∈ I, ∃ g ∈ T, pointChart j t f = X j ^ (n + 1) * g := by
    intro f hf
    obtain ⟨g, hg⟩ := exists_pointChart_eq_X_pow_mul (j := j) (t := t)
      (hI.trans (idealOrd_le_ord hf))
    refine ⟨g, ?_, hg⟩
    rw [mem_chartTransformIdeal, ← hg]
    exact Ideal.mem_map_of_mem _ hf
  have hmemK : ∀ u ∈ derivIdeal T, X j ^ n * u ∈ K := fun u hu =>
    Ideal.mem_span_singleton_mul.mpr ⟨u, hu, rfl⟩
  have h0 : ∀ f ∈ I, pointChart j t f ∈ K := by
    intro f hf
    obtain ⟨g, hgT, hg⟩ := hfac f hf
    rw [hg, pow_succ, mul_assoc]
    exact hmemK _ (Ideal.mul_mem_left _ _ (le_derivIdeal T hgT))
  have hne : ∀ f ∈ I, ∀ i, i ≠ j → pointChart j t (pderiv i f) ∈ K := by
    intro f hf i hij
    obtain ⟨g, hgT, hg⟩ := hfac f hf
    rw [pointChart_pderiv_of_ne hij t hg]
    exact hmemK _ (pderiv_mem_derivIdeal hgT i)
  have hself : ∀ f ∈ I, pointChart j t (pderiv j f) ∈ K := by
    intro f hf
    obtain ⟨g, hgT, hg⟩ := hfac f hf
    -- `∂_j π(f) ∈ K`
    have hd : pderiv j (pointChart j t f) ∈ K := by
      rw [hg, pderiv_mul, pderiv_pow, pderiv_X_self, mul_one, Nat.add_sub_cancel, pow_succ]
      have : (↑(n + 1) : MvPolynomial σ k) * X j ^ n * g + X j ^ n * X j * pderiv j g =
          X j ^ n * ((↑(n + 1) : MvPolynomial σ k) * g + X j * pderiv j g) := by ring
      rw [this]
      exact hmemK _ (add_mem (Ideal.mul_mem_left _ _ (le_derivIdeal T hgT))
        (Ideal.mul_mem_left _ _ (pderiv_mem_derivIdeal hgT j)))
    -- `x_j π(∂_j f) ∈ x_j K`
    have hsum := X_mul_pderiv_pointChart j t f
    rw [map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), map_mul, pointChart_X_self]
      at hsum
    have hmem : X j * pointChart j t (pderiv j f) ∈ Ideal.span {X j} * K := by
      have e : X j * pointChart j t (pderiv j f) = X j * pderiv j (pointChart j t f) -
          ∑ i ∈ Finset.univ.erase j, pointChart j t (X i * pderiv i f) := by
        rw [hsum]; ring
      rw [e]
      refine sub_mem (Ideal.mem_span_singleton_mul.mpr ⟨_, hd, rfl⟩) (sum_mem fun i hi => ?_)
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      rw [map_mul, pointChart_X_of_ne t hij, mul_assoc]
      exact Ideal.mem_span_singleton_mul.mpr
        ⟨_, Ideal.mul_mem_left _ _ (hne f hf i hij), rfl⟩
    obtain ⟨z, hz, hz'⟩ := Ideal.mem_span_singleton_mul.mp hmem
    rwa [mul_left_cancel₀ hX hz'] at hz
  have hmap : (derivIdeal I).map (pointChart j t) ≤ K := by
    rw [Ideal.map_le_iff_le_comap]
    refine sup_le (fun f hf => h0 f hf) ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, f, hf, rfl⟩
    by_cases hij : i = j
    · subst hij
      exact hself f hf
    · exact hne f hf i hij
  intro u hu
  rw [mem_chartTransformIdeal] at hu
  obtain ⟨z, hz, hz'⟩ := Ideal.mem_span_singleton_mul.mp (hmap hu)
  rwa [mul_left_cancel₀ (pow_ne_zero n hX) hz'] at hz

/-- Volume 2, Theorem 2.2.7 of the handbook, for one blowup of the origin of affine space, in the `x_j`-chart with translations `t`. Let `m ≤ ord I`, so that the origin is in the cosupport of `(I, m)`. Then for each `l ≤ m` the controlled transform of `(D^l(I), m - l)` is contained in `D^l` of the controlled transform of `(I, m)`. The proof holds in every characteristic. -/
theorem chartTransformIdeal_derivIdeal_iterate_le [Fintype σ] (j : σ) (t : σ → k) {m : ℕ}
    {I : Ideal (MvPolynomial σ k)} (hI : (m : ℕ∞) ≤ idealOrd I) {l : ℕ} (hl : l ≤ m) :
    chartTransformIdeal j t (m - l) (derivIdeal^[l] I) ≤
      derivIdeal^[l] (chartTransformIdeal j t m I) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← Nat.sub_sub]
    exact (chartTransformIdeal_derivIdeal_le j t (by omega)
      (le_idealOrd_derivIdeal_iterate_sub hI l)).trans (derivIdeal_mono (ih (by omega)))

end Singularity
