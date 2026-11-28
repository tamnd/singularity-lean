/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.MarkedTransform
import Singularity.Invariant.DerivativeOrder
import Singularity.Invariant.LogJacobianBlowupPoint
import Singularity.Invariant.OrderAlong
import Singularity.Algebra.DerivationIdealPow

/-!
# Restriction, tuning and maximal contact on affine space

This file proves the algebraic core of several results of Volume 2 of the handbook. We work in
the polynomial ring `MvPolynomial σ k` over a field `k`, and in characteristic `0` where it is
needed. Centers are coordinate centers `Z = V(x_i : i ∈ S)`, with ideal
`I_Z = chartCenterIdeal S = varsIdeal S`. The hypersurface of maximal contact is a coordinate
hyperplane `S = V(x_h)`, and restriction to it is `hyperplaneRestrict h`, which sends `x_h`
to `0`. Points are `k`-points `a : σ → k`, and the order at `a` is `ordAtPoint a`, the order
of the translate `f(x + a)`.

## Main declarations

* `ordAtPoint`, `ordAtPointIdeal`: the order at a `k`-point and its ideal.
* `derivIdeal_iterate_le_ordAtPointIdeal`: `ord_a I ≥ m` gives `ord_a D^j(I) ≥ m - j`.
* `eval_eq_zero_of_mem_derivIdeal_iterate`: `ord_a I ≥ m` gives `D^(m-1)(I) ⊆ m_a`.
* `mem_varsIdeal_pow_of_le_ordAtPoint`: Proposition 2.1.7. In characteristic `0`, if `f`
  has order at least `r` at every point of `Z`, then `f ∈ I_Z^r`.
  `le_ordAtPoint_of_mem_varsIdeal_pow` is the converse, and
  `forall_le_ordAtPoint_iff_le_varsIdeal_pow` is the version for ideals.
* `eq_zero_of_X_mem_derivIdeal_iterate`: Theorem 2.3.3 (2) for `i = 0`. If
  `x_h ∈ D^(m-1)(I)`, then `x_h` vanishes on the points of order at least `m`.
* `chartSubst_X_of_ne`, `X_mem_centerChartTransformIdeal_one`: Theorem 2.3.3 (1) in one chart.
  The strict transform of `x_h` in the `x_c`-chart is again a coordinate, so `(x_h)` transforms
  to `(x_h)`.
* `hyperplaneRestrict_comp_chartSubst`: Lemma 3.1.2 (1). Restriction to `S` commutes with the
  chart map of a center `Z ⊆ S`, in every chart `x_c` with `c ≠ h`.
* `map_hyperplaneRestrict_le`, `map_hyperplaneRestrict_centerChartTransformIdeal`:
  Lemma 3.1.2 (2). `A ⊆ I_Z^a` gives `A|_S ⊆ I_Z'^a`, and the restriction of the transform
  of `(A, a)` is the transform of `(A|_S, a)`.
* `le_ord_of_hyperplaneRestrict_pderiv_iterate`: the `k!` step of the proof of
  Theorem 3.1.3 (2).
* `le_idealOrd_of_restrict_le`: Theorem 3.1.3 (2) at the origin, from the claim (3.1.3)
  for given ideals `T_j` on `S`.
* `le_idealOrd_iff_restrict_derivIdeal_iterate`: Theorem 3.1.3 (2) for `i = 0`. `I` has order
  at least `m` at the origin if and only if each `D^j(I)|_S` has order at least `m - j`.
* `tuningIdeal`: Kollár's tuned ideal `W_s(I)` of Remark 3.2.12.
* `le_idealOrd_iff_le_idealOrd_tuningIdeal`, `le_pow_iff_tuningIdeal_le_pow`:
  Remark 3.2.12, the cosupport at the origin and the first centers. For `m ∣ s`,
  `(I, m)` and `(W_s(I), s)` have the same points of maximal order there and the same
  coordinate centers.
* `centerChartTransformIdeal_span_X_of_mem`, `centerChartTransformIdeal_span_X_of_not_mem`,
  `centerChartTransformIdeal_span_X_self`: the chart computation behind Lemma 3.3.3 (2).
  A coordinate hyperplane transforms to a coordinate hyperplane or to the unit ideal, and the
  exceptional divisor of the chart is `V(x_c)`.

## Not proved

* Lemma 3.3.2 (localization of a log resolution) and Lemma 3.3.4 (the order reduction step).
  These need blowup sequences and the induction on `M_(n-1)`.
* Lemma 3.3.3 (1) and (3), the snc criterion. Only the chart computation of part (2) is done.
* Theorem 3.1.3 for whole blowup sequences. The induction of the claim (3.1.3) across the
  blowups, and part (1) for sequences, are not formalized. Part (2) is done at the origin for
  the first step.
* Theorem 2.3.3 (3), and the statements of Theorem 2.3.3 for sequences of blowups.
* Remark 3.2.12: invariance under maximal contact, the claim that the maximal order is `s`,
  uniqueness up to étale maps.
* Smooth varieties and local coordinates in general. Only affine space, coordinate centers,
  coordinate hyperplanes and `k`-points are treated.
-/

open MvPolynomial Finsupp

namespace Singularity

/-! ### The order at a point (Proposition 2.1.7) -/

section OrderAtPoint

variable {σ k : Type*} [Field k] [DecidableEq σ]

/-- The order of `f` at the point `a` of the affine space: the order at the origin of the
translate `f(x + a)`. -/
noncomputable def ordAtPoint (a : σ → k) (f : MvPolynomial σ k) : ℕ∞ :=
  ord (translateBy a f)

/-- The ideal of the polynomials with order at least `n` at the point `a`. -/
noncomputable def ordAtPointIdeal (a : σ → k) (n : ℕ) : Ideal (MvPolynomial σ k) :=
  (idealOfVars σ k ^ n).comap (translateBy a)

omit [DecidableEq σ] in
theorem le_ordAtPoint_iff {a : σ → k} {f : MvPolynomial σ k} {n : ℕ} :
    (n : ℕ∞) ≤ ordAtPoint a f ↔ f ∈ ordAtPointIdeal a n := by
  rw [ordAtPoint, le_ord_iff_mem_pow]
  rfl

omit [DecidableEq σ] in
/-- At the origin the order at a point is the order. -/
theorem ordAtPoint_zero (f : MvPolynomial σ k) : ordAtPoint 0 f = ord f := by
  have : translateBy (0 : σ → k) = AlgHom.id k _ :=
    MvPolynomial.algHom_ext fun i => by simp [translateBy_X]
  rw [ordAtPoint, this, AlgHom.id_apply]

omit [DecidableEq σ] in
theorem ordAtPointIdeal_anti (a : σ → k) {n n' : ℕ} (h : n ≤ n') :
    ordAtPointIdeal a n' ≤ ordAtPointIdeal a n :=
  Ideal.comap_mono (Ideal.pow_le_pow_right h)

omit [DecidableEq σ] in
/-- A polynomial with order at least `1` at `a` vanishes at `a`. -/
theorem eval_eq_zero_of_mem_ordAtPointIdeal_one {a : σ → k} {f : MvPolynomial σ k}
    (hf : f ∈ ordAtPointIdeal a 1) : eval a f = 0 := by
  rw [← le_ordAtPoint_iff, Nat.cast_one, ordAtPoint, one_le_ord_iff,
    constantCoeff_translateBy] at hf
  exact hf

/-- A partial derivative lowers the order at a point by at most one. -/
theorem pderiv_mem_ordAtPointIdeal {a : σ → k} {n : ℕ} {f : MvPolynomial σ k}
    (hf : f ∈ ordAtPointIdeal a (n + 1)) (i : σ) : pderiv i f ∈ ordAtPointIdeal a n := by
  show translateBy a (pderiv i f) ∈ idealOfVars σ k ^ n
  rw [← pderiv_translateBy]
  simpa using derivation_mem_pow_pred (pderiv i) (idealOfVars σ k) (n + 1) _ hf

/-- The derivative ideal lowers the order at a point by at most one. -/
theorem derivIdeal_le_ordAtPointIdeal {a : σ → k} {n : ℕ} {I : Ideal (MvPolynomial σ k)}
    (h : I ≤ ordAtPointIdeal a (n + 1)) : derivIdeal I ≤ ordAtPointIdeal a n := by
  refine sup_le (h.trans (ordAtPointIdeal_anti a (Nat.le_succ n))) ?_
  rw [Ideal.span_le]
  rintro _ ⟨i, f, hf, rfl⟩
  exact pderiv_mem_ordAtPointIdeal (h hf) i

/-- **Volume 2, Lemma 3.1.2 (3) of the handbook**, at any point of the affine space. If `I` has
order at least `m` at `a`, then `D^j(I)` has order at least `m - j` at `a`. -/
theorem derivIdeal_iterate_le_ordAtPointIdeal {a : σ → k} {m : ℕ}
    {I : Ideal (MvPolynomial σ k)} (h : I ≤ ordAtPointIdeal a m) (j : ℕ) :
    derivIdeal^[j] I ≤ ordAtPointIdeal a (m - j) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    rcases Nat.lt_or_ge j m with hj | hj
    · exact derivIdeal_le_ordAtPointIdeal (by rwa [show m - j = m - (j + 1) + 1 by omega] at ih)
    · rw [show m - (j + 1) = 0 by omega]
      intro g _
      show translateBy a g ∈ idealOfVars σ k ^ 0
      simp

/-- **Volume 2, Corollary 2.1.5 (1) of the handbook**, one direction, at any point. If `I` has
order at least `m ≥ 1` at `a`, then each element of `D^(m-1)(I)` vanishes at `a`. -/
theorem eval_eq_zero_of_mem_derivIdeal_iterate {a : σ → k} {m : ℕ} (hm : 1 ≤ m)
    {I : Ideal (MvPolynomial σ k)} (h : ∀ f ∈ I, (m : ℕ∞) ≤ ordAtPoint a f)
    {g : MvPolynomial σ k} (hg : g ∈ derivIdeal^[m - 1] I) : eval a g = 0 := by
  have hI : I ≤ ordAtPointIdeal a m := fun f hf => le_ordAtPoint_iff.mp (h f hf)
  have := derivIdeal_iterate_le_ordAtPointIdeal hI (m - 1) hg
  rw [show m - (m - 1) = 1 by omega] at this
  exact eval_eq_zero_of_mem_ordAtPointIdeal_one this

/-- The substitution `x_i ↦ 0` for `i ∈ S`. -/
noncomputable def killVars (S : Finset σ) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval fun i => if i ∈ S then 0 else X i

theorem killVars_X (S : Finset σ) (i : σ) :
    killVars S (X i : MvPolynomial σ k) = if i ∈ S then 0 else X i := by
  simp [killVars]

/-- `f - f|_{x_S = 0}` lies in the ideal `(x_i : i ∈ S)`. -/
theorem sub_killVars_mem_varsIdeal (S : Finset σ) (f : MvPolynomial σ k) :
    f - killVars S f ∈ varsIdeal S := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [killVars]
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul]
    have : p * X i - killVars S p * killVars S (X i) =
        (p - killVars S p) * X i + killVars S p * (X i - killVars S (X i)) := by ring
    rw [this]
    refine add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    by_cases hi : i ∈ S
    · simp only [killVars_X, hi, ↓reduceIte, sub_zero]
      exact Ideal.subset_span ⟨i, hi, rfl⟩
    · simp only [killVars_X, hi, ↓reduceIte, sub_self]
      exact zero_mem _

theorem eval_killVars (S : Finset σ) (a : σ → k) (f : MvPolynomial σ k) :
    eval a (killVars S f) = eval (fun i => if i ∈ S then 0 else a i) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [killVars]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, killVars_X, eval_mul, eval_X]
    by_cases hi : i ∈ S <;> simp [hi]

/-- Over an infinite field, a polynomial that vanishes at each point of `V(x_i : i ∈ S)` lies in
the ideal `(x_i : i ∈ S)`. -/
theorem mem_varsIdeal_of_eval_eq_zero [Infinite k] {S : Finset σ} {f : MvPolynomial σ k}
    (h : ∀ a : σ → k, (∀ i ∈ S, a i = 0) → eval a f = 0) : f ∈ varsIdeal S := by
  have h0 : killVars S f = 0 := by
    refine MvPolynomial.funext fun a => ?_
    rw [eval_killVars, map_zero]
    exact h _ fun i hi => by simp [hi]
  simpa [h0] using sub_killVars_mem_varsIdeal S f

/-- The algebraic step of Proposition 2.1.7. In characteristic `0`, if `f ∈ I_Z` and each
`∂_i f` with `i ∈ S` lies in `I_Z^r`, then `f ∈ I_Z^(r+1)`. Here `I_Z = (x_i : i ∈ S)`. -/
theorem mem_varsIdeal_pow_succ_of_pderiv [CharZero k] {S : Finset σ} {r : ℕ}
    {f : MvPolynomial σ k} (hf : f ∈ varsIdeal S)
    (hd : ∀ i ∈ S, pderiv i f ∈ varsIdeal S ^ r) : f ∈ varsIdeal S ^ (r + 1) := by
  rw [← le_ordAlong_iff_mem_pow]
  refine le_ordAlong fun d hd' => ?_
  have h1 : (1 : ℕ∞) ≤ ((∑ i ∈ S, d i : ℕ) : ℕ∞) := by
    have := (le_ordAlong_iff_mem_pow (n := 1)).mpr (by rwa [pow_one])
    rw [Nat.cast_one] at this
    exact this.trans (ordAlong_le (MvPolynomial.mem_support_iff.mp hd'))
  have h1' : 1 ≤ ∑ i ∈ S, d i := by exact_mod_cast h1
  obtain ⟨i, hiS, hi⟩ : ∃ i ∈ S, d i ≠ 0 := Finset.exists_ne_zero_of_sum_ne_zero (by omega)
  have hle : single i 1 ≤ d := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
  obtain ⟨e, rfl⟩ : ∃ e, d = e + single i 1 :=
    ⟨d - single i 1, (tsub_add_cancel_of_le hle).symm⟩
  have hc : (pderiv i f).coeff e ≠ 0 := by
    rw [coeff_pderiv]
    refine mul_ne_zero (MvPolynomial.mem_support_iff.mp hd') ?_
    exact_mod_cast Nat.succ_ne_zero (e i)
  have hr := ((le_ordAlong_iff_mem_pow (n := r)).mpr (hd i hiS)).trans (ordAlong_le hc)
  have hr' : r ≤ ∑ j ∈ S, e j := by exact_mod_cast hr
  have hsum : ∑ j ∈ S, (e + single i 1 : σ →₀ ℕ) j = ∑ j ∈ S, e j + 1 := by
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply,
      Finset.sum_ite_eq, hiS, ↓reduceIte]
  rw [hsum]
  exact_mod_cast Nat.succ_le_succ hr'

/-- **Volume 2, Proposition 2.1.7 of the handbook** (order along a smooth subvariety), for a
coordinate subvariety `Z = V(x_i : i ∈ S)` of the affine space over a field of characteristic
`0`. If `f` has order at least `r` at each point of `Z`, then `f ∈ I_Z^r`. -/
theorem mem_varsIdeal_pow_of_le_ordAtPoint [CharZero k] (S : Finset σ) (r : ℕ)
    {f : MvPolynomial σ k} (h : ∀ a : σ → k, (∀ i ∈ S, a i = 0) → (r : ℕ∞) ≤ ordAtPoint a f) :
    f ∈ varsIdeal S ^ r := by
  have : Infinite k := Infinite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective
  induction r generalizing f with
  | zero => simp
  | succ r ih =>
    refine mem_varsIdeal_pow_succ_of_pderiv ?_ fun i _ => ih fun a ha => ?_
    · refine mem_varsIdeal_of_eval_eq_zero fun a ha => ?_
      refine eval_eq_zero_of_mem_ordAtPointIdeal_one
        (ordAtPointIdeal_anti a (Nat.le_add_left 1 r) (le_ordAtPoint_iff.mp (h a ha)))
    · exact le_ordAtPoint_iff.mpr (pderiv_mem_ordAtPointIdeal (le_ordAtPoint_iff.mp (h a ha)) i)

omit [DecidableEq σ] in
/-- The converse of Proposition 2.1.7: an element of `I_Z^r` has order at least `r` at each
point of `Z`. This holds over each field. -/
theorem le_ordAtPoint_of_mem_varsIdeal_pow {S : Finset σ} {r : ℕ} {f : MvPolynomial σ k}
    (hf : f ∈ varsIdeal S ^ r) {a : σ → k} (ha : ∀ i ∈ S, a i = 0) :
    (r : ℕ∞) ≤ ordAtPoint a f := by
  have hle : varsIdeal (R := k) S ≤ (idealOfVars σ k).comap (translateBy a) := by
    rw [varsIdeal, Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    show translateBy a (X i) ∈ idealOfVars σ k
    rw [translateBy_X_of_eq_zero (ha i hi)]
    exact Ideal.subset_span (Set.mem_range_self i)
  rw [ordAtPoint, le_ord_iff_mem_pow]
  exact Ideal.le_comap_pow _ r (Ideal.pow_right_mono hle r hf)

/-- **Volume 2, Proposition 2.1.7 of the handbook**, the form for ideals. In characteristic `0`,
`Z = V(x_i : i ∈ S)` lies in the cosupport of `(I, m)` if and only if `I ⊆ I_Z^m`. -/
theorem forall_le_ordAtPoint_iff_le_varsIdeal_pow [CharZero k] (S : Finset σ) (m : ℕ)
    (I : Ideal (MvPolynomial σ k)) :
    (∀ a : σ → k, (∀ i ∈ S, a i = 0) → ∀ f ∈ I, (m : ℕ∞) ≤ ordAtPoint a f) ↔
      I ≤ varsIdeal S ^ m :=
  ⟨fun h f hf => mem_varsIdeal_pow_of_le_ordAtPoint S m fun a ha => h a ha f hf,
    fun h _ ha _f hf => le_ordAtPoint_of_mem_varsIdeal_pow (h hf) ha⟩

end OrderAtPoint

/-! ### Maximal contact (Theorem 2.3.3) -/

section MaximalContact

variable {σ k : Type*} [Field k] [DecidableEq σ]

/-- **Volume 2, Theorem 2.3.3 (2) of the handbook**, for `i = 0` on the affine space. Let
`m ≥ 1` and let the hypersurface `H = V(x_h)` satisfy `x_h ∈ D^(m-1)(I)`. Then each point where
`I` has order at least `m` lies on `H`. -/
theorem eq_zero_of_X_mem_derivIdeal_iterate {m : ℕ} (hm : 1 ≤ m) {I : Ideal (MvPolynomial σ k)}
    {h : σ} (hH : X h ∈ derivIdeal^[m - 1] I) {a : σ → k}
    (ha : ∀ f ∈ I, (m : ℕ∞) ≤ ordAtPoint a f) : a h = 0 := by
  simpa using eval_eq_zero_of_mem_derivIdeal_iterate hm ha hH

variable {R : Type*} [CommRing R]

/-- **Volume 2, formula (2.3.1) of the handbook**, in the `x_c`-chart with `c ≠ h`: the pullback
of the equation `x_h` of `H` is `y_c y_h`, the product of the equations of `F` and `H'`. -/
theorem chartSubst_X_of_ne {S : Finset σ} {c h : σ} (hS : h ∈ S) (hc : h ≠ c) :
    chartSubst S c (X h : MvPolynomial σ R) = X c * X h := by
  rw [chartSubst_X, chartImage]
  split_ifs with hm
  · exact mul_comm _ _
  · exact absurd (Finset.mem_erase.mpr ⟨hc, hS⟩) hm

/-- **Volume 2, formula (2.3.1) of the handbook**, in the `x_h`-chart: the pullback of `x_h` is
`y_h`, the equation of the exceptional divisor. So `H'` does not meet this chart. -/
theorem chartSubst_X_self (S : Finset σ) (h : σ) :
    chartSubst S h (X h : MvPolynomial σ R) = X h := by
  rw [chartSubst_X, chartImage]
  split_ifs with hm
  · simp at hm
  · rfl

/-- **Volume 2, Theorem 2.3.3 (1) of the handbook**, the step from `i` to `i + 1`, in the
`x_c`-chart of the blowup of the coordinate center `(x_i : i ∈ S)` with `h ∈ S` and `c ≠ h`.
If the equation `x_h` of `H` lies in `J`, then the equation `y_h` of `H'` lies in the transform
of `(J, 1)`. With `J = J^(m-1)_i` this is `O(-H_{i+1}) ⊆ J^(m-1)_{i+1}`. -/
theorem X_mem_centerChartTransformIdeal_one {S : Finset σ} {c h : σ} (hS : h ∈ S) (hc : h ≠ c)
    {J : Ideal (MvPolynomial σ R)} (hJ : X h ∈ J) :
    X h ∈ centerChartTransformIdeal S c 1 J := by
  rw [centerChartTransformIdeal, mem_markedTransform, pow_one, ← chartSubst_X_of_ne hS hc]
  exact Ideal.mem_map_of_mem _ hJ

end MaximalContact

/-! ### Restriction to a hyperplane (Lemma 3.1.2 and Theorem 3.1.3) -/

section Restriction

variable {σ R : Type*} [CommRing R] [DecidableEq σ]

/-- The restriction to the hyperplane `S = V(x_h)`: the substitution `x_h ↦ 0`. Its image is
the ring `k[x_i : i ≠ h]` of `S`. -/
noncomputable def hyperplaneRestrict (h : σ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i => if i = h then 0 else X i

theorem hyperplaneRestrict_X (h i : σ) :
    hyperplaneRestrict h (X i : MvPolynomial σ R) = if i = h then 0 else X i := by
  simp [hyperplaneRestrict]

/-- **Volume 2, Lemma 3.1.2 (1) of the handbook**, in a chart. Let `S = V(x_h)` and let the
center be `(x_i : i ∈ T)`. In the `x_c`-chart with `c ≠ h`, the restriction to `S' = V(y_h)` of
the chart map of the blowup of `X` is the chart map of the blowup of `S` along the center
`(x_i : i ∈ T \ {h})`, followed by the restriction. -/
theorem hyperplaneRestrict_comp_chartSubst (T : Finset σ) {c h : σ} (hc : c ≠ h) :
    (hyperplaneRestrict h).comp (chartSubst T c) =
      (chartSubst (T.erase h) c).comp (hyperplaneRestrict (R := R) h) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, chartSubst_X, hyperplaneRestrict_X (R := R) h i]
  by_cases hi : i = h
  · subst hi
    simp only [chartImage]
    split_ifs <;> simp [hyperplaneRestrict_X]
  · simp only [hi, ↓reduceIte, chartSubst_X, chartImage, Finset.mem_erase]
    split_ifs <;> simp_all [hyperplaneRestrict_X]

theorem hyperplaneRestrict_chartSubst (T : Finset σ) {c h : σ} (hc : c ≠ h)
    (f : MvPolynomial σ R) :
    hyperplaneRestrict h (chartSubst T c f) =
      chartSubst (T.erase h) c (hyperplaneRestrict h f) := by
  rw [← AlgHom.comp_apply, hyperplaneRestrict_comp_chartSubst T hc, AlgHom.comp_apply]

/-- **The remark after Lemma 3.1.2 of Volume 2 of the handbook**, in a chart: if
`π φ = y_c^a g`, then `π_S(φ|_S) = y_c^a (g|_{S'})`. -/
theorem chartSubst_hyperplaneRestrict_eq {T : Finset σ} {c h : σ} (hc : c ≠ h) {a : ℕ}
    {φ g : MvPolynomial σ R} (hg : chartSubst T c φ = X c ^ a * g) :
    chartSubst (T.erase h) c (hyperplaneRestrict h φ) = X c ^ a * hyperplaneRestrict h g := by
  rw [← hyperplaneRestrict_chartSubst T hc, hg, map_mul, map_pow]
  simp only [hyperplaneRestrict_X, hc, ↓reduceIte]

/-- **Volume 2, Lemma 3.1.2 (2) of the handbook**, the first claim: if `A ⊆ I_Z^a`, then
`A|_S ⊆ I_{Z ∩ S}^a`. -/
theorem map_hyperplaneRestrict_le {T : Finset σ} {h : σ} {a : ℕ} {A : Ideal (MvPolynomial σ R)}
    (hA : A ≤ chartCenterIdeal T ^ a) :
    A.map (hyperplaneRestrict h) ≤ chartCenterIdeal (T.erase h) ^ a := by
  have h1 : (chartCenterIdeal (R := R) T).map (hyperplaneRestrict h) ≤
      chartCenterIdeal (T.erase h) := by
    rw [chartCenterIdeal, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    rw [hyperplaneRestrict_X]
    split_ifs with hih
    · exact zero_mem _
    · exact Ideal.subset_span ⟨i, Finset.mem_erase.mpr ⟨hih, hi⟩, rfl⟩
  calc A.map (hyperplaneRestrict h) ≤ (chartCenterIdeal T ^ a).map (hyperplaneRestrict h) :=
        Ideal.map_mono hA
    _ = ((chartCenterIdeal T).map (hyperplaneRestrict h)) ^ a := Ideal.map_pow _ _ _
    _ ≤ chartCenterIdeal (T.erase h) ^ a := Ideal.pow_right_mono h1 a

/-- **Volume 2, Lemma 3.1.2 (2) of the handbook**, the second claim, in the `x_c`-chart with
`c ≠ h`. If `A ⊆ I_Z^a`, then the restriction to `S'` of the transform of `(A, a)` is the
transform of `(A|_S, a)` under the blowup of `S`. -/
theorem map_hyperplaneRestrict_centerChartTransformIdeal [IsDomain R] {T : Finset σ} {c h : σ}
    (hc : c ≠ h) {a : ℕ} {A : Ideal (MvPolynomial σ R)} (hA : A ≤ chartCenterIdeal T ^ a) :
    (centerChartTransformIdeal T c a A).map (hyperplaneRestrict h) =
      centerChartTransformIdeal (T.erase h) c a (A.map (hyperplaneRestrict h)) := by
  symm
  apply markedTransform_eq_of_map_eq (X_ne_zero c)
  have hmap := map_eq_span_mul_markedTransform (map_chartSubst_le_span (c := c) hA)
  have e1 : (A.map (hyperplaneRestrict h)).map (chartSubst (T.erase h) c) =
      (A.map (chartSubst T c)).map (hyperplaneRestrict (R := R) h) := by
    change (A.map (hyperplaneRestrict (R := R) h).toRingHom).map
        (chartSubst (R := R) (T.erase h) c).toRingHom =
      (A.map (chartSubst (R := R) T c).toRingHom).map (hyperplaneRestrict (R := R) h).toRingHom
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    refine RingHom.ext fun f => ?_
    exact (hyperplaneRestrict_chartSubst T hc f).symm
  rw [e1, hmap, Ideal.map_mul, Ideal.map_span, Set.image_singleton, map_pow]
  simp only [hyperplaneRestrict_X, hc, ↓reduceIte]

variable {k : Type*} [Field k]

/-- The restriction does not lower the order at the origin, a point of `S`. -/
theorem ord_le_ord_hyperplaneRestrict (h : σ) (f : MvPolynomial σ k) :
    ord f ≤ ord (hyperplaneRestrict h f) := by
  refine ord_le_ord_aeval _ (fun i => ?_) f
  split_ifs <;> simp

/-- The restriction keeps the coefficients of the monomials without `x_h`. -/
theorem coeff_hyperplaneRestrict {h : σ} {d : σ →₀ ℕ} (hd : d h = 0) (f : MvPolynomial σ k) :
    (hyperplaneRestrict h f).coeff d = f.coeff d := by
  induction f using MvPolynomial.induction_on generalizing d with
  | C a => simp [hyperplaneRestrict]
  | add p q hp hq =>
    rw [map_add]
    simp [hp hd, hq hd]
  | mul_X p i hp =>
    rw [map_mul, hyperplaneRestrict_X]
    by_cases hi : i = h
    · subst hi
      simp [coeff_mul_X', hd]
    · simp only [hi, ↓reduceIte]
      rw [coeff_mul_X', coeff_mul_X']
      split_ifs with hs
      · refine hp ?_
        simp [Finsupp.tsub_apply, hd]
      · rfl

/-- The last step of the proof of **Volume 2, Theorem 3.1.3 (2) of the handbook**, at the
origin, a point of `S = V(x_h)`. In characteristic `0`, if `(∂_h^j f)|_S` has order at least
`m - j` for each `j < m`, then `f` has order at least `m`. This is the division by `j!` in the
expansion `f = ∑ a_j x_h^j`. -/
theorem le_ord_of_hyperplaneRestrict_pderiv_iterate [CharZero k] (h : σ) (m : ℕ)
    (f : MvPolynomial σ k)
    (hf : ∀ j < m, ((m - j : ℕ) : ℕ∞) ≤ ord (hyperplaneRestrict h ((pderiv h)^[j] f))) :
    (m : ℕ∞) ≤ ord f := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
    have hd : (m : ℕ∞) ≤ ord (pderiv h f) := by
      refine ih _ fun j hj => ?_
      have := hf (j + 1) (by omega)
      rwa [Function.iterate_succ_apply, show m + 1 - (j + 1) = m - j by omega] at this
    have h0 := hf 0 (by omega)
    simp only [Function.iterate_zero, id, Nat.sub_zero] at h0
    refine le_ord_iff.mpr fun d hdeg => ?_
    by_cases hdh : d h = 0
    · rw [← coeff_hyperplaneRestrict hdh]
      exact coeff_eq_zero_of_lt_ord (lt_of_lt_of_le (by exact_mod_cast hdeg) h0)
    · have hle : single h 1 ≤ d := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hdh)
      obtain ⟨e, rfl⟩ : ∃ e, d = e + single h 1 :=
        ⟨d - single h 1, (tsub_add_cancel_of_le hle).symm⟩
      have hdeg' : degree e < m := by
        rw [map_add, degree_single] at hdeg
        omega
      have hz := coeff_eq_zero_of_lt_ord (lt_of_lt_of_le (by exact_mod_cast hdeg') hd)
      rw [coeff_pderiv] at hz
      rcases mul_eq_zero.mp hz with hz | hz
      · exact hz
      · exact absurd hz (by exact_mod_cast Nat.succ_ne_zero (e h))

omit [DecidableEq σ] in
theorem pderiv_iterate_mem_derivIdeal_iterate {I : Ideal (MvPolynomial σ R)} (i : σ)
    {f : MvPolynomial σ R} (hf : f ∈ I) (j : ℕ) : (pderiv i)^[j] f ∈ derivIdeal^[j] I := by
  induction j with
  | zero => exact hf
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact pderiv_mem_derivIdeal ih i

omit [DecidableEq σ] in
theorem derivIdeal_iterate_le_pow {I : Ideal (MvPolynomial σ R)} {m : ℕ}
    (h : I ≤ idealOfVars σ R ^ m) (j : ℕ) : derivIdeal^[j] I ≤ idealOfVars σ R ^ (m - j) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [Function.iterate_succ_apply', Nat.sub_succ]
    exact derivIdeal_le_pow ih

theorem map_hyperplaneRestrict_idealOfVars_pow_le (h : σ) (n : ℕ) :
    (idealOfVars σ k ^ n).map (hyperplaneRestrict h) ≤ idealOfVars σ k ^ n := by
  intro f hf
  rw [Ideal.map_pow] at hf
  refine Ideal.pow_right_mono ?_ n hf
  rw [idealOfVars, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  rw [hyperplaneRestrict_X]
  split_ifs
  · exact zero_mem _
  · exact Ideal.subset_span (Set.mem_range_self i)

/-- **Volume 2, Theorem 3.1.3 (2) of the handbook**, from the claim (3.1.3), at the origin, a
point of `S = V(x_h)`. Let `T_j` be ideals with order at least `m - j` for `j < m`, and assume
the claim `D^k(I)|_S ⊆ ∑_{j ≤ k} D^(k-j)(T_j)` for `k < m`. In characteristic `0`, `I` has order
at least `m`. -/
theorem le_idealOrd_of_restrict_le [CharZero k] (h : σ) (m : ℕ) (I : Ideal (MvPolynomial σ k))
    (T : ℕ → Ideal (MvPolynomial σ k)) (hT : ∀ j < m, ((m - j : ℕ) : ℕ∞) ≤ idealOrd (T j))
    (hc : ∀ l < m, (derivIdeal^[l] I).map (hyperplaneRestrict h) ≤
      ⨆ j ∈ Finset.range (l + 1), derivIdeal^[l - j] (T j)) :
    (m : ℕ∞) ≤ idealOrd I := by
  refine le_idealOrd fun f hf => le_ord_of_hyperplaneRestrict_pderiv_iterate h m f fun l hl => ?_
  have hmem := hc l hl (Ideal.mem_map_of_mem _ (pderiv_iterate_mem_derivIdeal_iterate h hf l))
  have hle : (⨆ j ∈ Finset.range (l + 1), derivIdeal^[l - j] (T j)) ≤
      idealOfVars σ k ^ (m - l) := by
    refine iSup₂_le fun j hj => ?_
    have hj' : j < m := by have := Finset.mem_range.mp hj; omega
    have := derivIdeal_iterate_le_pow (le_idealOrd_iff.mp (hT j hj')) (l - j)
    rwa [show m - j - (l - j) = m - l by have := Finset.mem_range.mp hj; omega] at this
  exact le_ord_iff_mem_pow.mpr (hle hmem)

/-- **Volume 2, Theorem 3.1.3 (2) of the handbook**, for `i = 0`, at the origin, a point of
`S = V(x_h)`. In characteristic `0`, `I` has order at least `m` at the origin if and only if
`D^j(I)|_S` has order at least `m - j` for each `j < m`. -/
theorem le_idealOrd_iff_restrict_derivIdeal_iterate [CharZero k] (h : σ) (m : ℕ)
    (I : Ideal (MvPolynomial σ k)) :
    (m : ℕ∞) ≤ idealOrd I ↔
      ∀ j < m, ((m - j : ℕ) : ℕ∞) ≤ idealOrd ((derivIdeal^[j] I).map (hyperplaneRestrict h)) := by
  constructor
  · intro hI j _
    refine le_idealOrd_iff.mpr ((Ideal.map_mono ?_).trans
      (map_hyperplaneRestrict_idealOfVars_pow_le h (m - j)))
    exact derivIdeal_iterate_le_pow (le_idealOrd_iff.mp hI) j
  · intro hT
    refine le_idealOrd_of_restrict_le h m I
      (fun j => (derivIdeal^[j] I).map (hyperplaneRestrict h)) hT fun l _ => ?_
    refine le_trans ?_ (le_iSup₂_of_le l (Finset.self_mem_range_succ l) le_rfl)
    simp

end Restriction

/-! ### Tuning (Remark 3.2.12) -/

section Tuning

variable {σ R : Type*} [CommRing R]

/-- Kollár's tuned ideal `W_s(I) = ∑ {∏_{j ≤ m} D^j(I)^(c_j) : ∑_j (m - j) c_j ≥ s}` of Volume 2,
Remark 3.2.12 of the handbook. -/
noncomputable def tuningIdeal (m s : ℕ) (I : Ideal (MvPolynomial σ R)) :
    Ideal (MvPolynomial σ R) :=
  ⨆ (c : Fin (m + 1) → ℕ) (_ : s ≤ ∑ j, (m - j.val) * c j),
    ∏ j, (derivIdeal^[j.val] I) ^ c j

/-- If `D^j(I) ⊆ Q^(m-j)` for each `j ≤ m`, then `W_s(I) ⊆ Q^s`. -/
theorem tuningIdeal_le_pow {m s : ℕ} {I Q : Ideal (MvPolynomial σ R)}
    (h : ∀ j ≤ m, derivIdeal^[j] I ≤ Q ^ (m - j)) : tuningIdeal m s I ≤ Q ^ s := by
  refine iSup₂_le fun c hc => ?_
  calc ∏ j, (derivIdeal^[j.val] I) ^ c j ≤ ∏ j : Fin (m + 1), (Q ^ (m - j.val)) ^ c j :=
        Finset.prod_le_prod' fun j _ => Ideal.pow_right_mono (h j.val (Nat.lt_succ_iff.mp j.2)) _
    _ = Q ^ (∑ j : Fin (m + 1), (m - j.val) * c j) := by
        rw [← Finset.prod_pow_eq_pow_sum]
        exact Finset.prod_congr rfl fun j _ => (pow_mul _ _ _).symm
    _ ≤ Q ^ s := Ideal.pow_le_pow_right hc

/-- If `m ∣ s`, then `I^(s/m) ⊆ W_s(I)`. -/
theorem pow_le_tuningIdeal {m s : ℕ} (hs : m ∣ s) (I : Ideal (MvPolynomial σ R)) :
    I ^ (s / m) ≤ tuningIdeal m s I := by
  have hc : s ≤ ∑ j : Fin (m + 1), (m - j.val) * (Pi.single 0 (s / m) : Fin (m + 1) → ℕ) j := by
    rw [Fintype.sum_eq_single (0 : Fin (m + 1)) fun j hj => by
      rw [Pi.single_eq_of_ne hj, mul_zero]]
    simp only [Pi.single_eq_same, Fin.val_zero, Nat.sub_zero, Nat.mul_div_cancel' hs, le_refl]
  have hp : ∏ j : Fin (m + 1), (derivIdeal^[j.val] I) ^
      (Pi.single 0 (s / m) : Fin (m + 1) → ℕ) j = I ^ (s / m) := by
    rw [Fintype.prod_eq_single (0 : Fin (m + 1)) fun j hj => by
      rw [Pi.single_eq_of_ne hj, pow_zero]]
    simp only [Pi.single_eq_same, Fin.val_zero, Function.iterate_zero, id]
  rw [← hp]
  unfold tuningIdeal
  exact le_iSup₂_of_le (Pi.single 0 (s / m) : Fin (m + 1) → ℕ) hc le_rfl

variable {k : Type*} [Field k]

/-- **Volume 2, Remark 3.2.12 of the handbook**, the cosupport at the origin. Let `m ≥ 1`, and
let `s > 0` be a multiple of `m`. Then `I` has order at least `m` at the origin if and only if
`W_s(I)` has order at least `s`. -/
theorem le_idealOrd_iff_le_idealOrd_tuningIdeal {m s : ℕ} (hm : 1 ≤ m) (hs : m ∣ s) (hs0 : 0 < s)
    (I : Ideal (MvPolynomial σ k)) :
    (m : ℕ∞) ≤ idealOrd I ↔ (s : ℕ∞) ≤ idealOrd (tuningIdeal m s I) := by
  constructor
  · intro hI
    exact le_idealOrd_iff.mpr
      (tuningIdeal_le_pow fun j _ => derivIdeal_iterate_le_pow (le_idealOrd_iff.mp hI) j)
  · intro hW
    have h1 := hW.trans (idealOrd_anti (pow_le_tuningIdeal hs I))
    rw [idealOrd_pow] at h1
    obtain ⟨t, rfl⟩ := hs
    have ht : 0 < t := Nat.pos_of_mul_pos_left hs0
    rw [Nat.mul_div_cancel_left t (by omega)] at h1
    rcases eq_or_ne (idealOrd I) ⊤ with htop | htop
    · rw [htop]; exact le_top
    obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hr] at h1 ⊢
    have : m * t ≤ t * r := by exact_mod_cast (by simpa using h1 : ((m * t : ℕ) : ℕ∞) ≤ t * r)
    exact_mod_cast (by nlinarith : m ≤ r)

variable [DecidableEq σ]

theorem ordAlong_pow (S : Finset σ) (f : MvPolynomial σ k) (n : ℕ) :
    ordAlong S (f ^ n) = n * ordAlong S f := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, ← C_1, ← monomial_zero', ordAlong_monomial S one_ne_zero]
    simp
  | succ n ih => rw [pow_succ, ordAlong_mul, ih, Nat.cast_succ, add_mul, one_mul]

/-- **Volume 2, Remark 3.2.12 of the handbook**, the centers. Let `m ≥ 1`, and let `s > 0` be a
multiple of `m`. A coordinate center `Z = V(x_i : i ∈ S)` satisfies `I ⊆ I_Z^m` if and only if
`W_s(I) ⊆ I_Z^s`. So the first centers allowed for `(I, m)` and for `(W_s(I), s)` agree. -/
theorem le_pow_iff_tuningIdeal_le_pow {m s : ℕ} (hm : 1 ≤ m) (hs : m ∣ s) (hs0 : 0 < s)
    (S : Finset σ) (I : Ideal (MvPolynomial σ k)) :
    I ≤ chartCenterIdeal S ^ m ↔ tuningIdeal m s I ≤ chartCenterIdeal S ^ s := by
  constructor
  · intro hI
    exact tuningIdeal_le_pow fun j _ => derivIdeal_iterate_le_chartCenterIdeal_pow hI j
  · intro hW f hf
    have h1 := hW (pow_le_tuningIdeal hs I (Ideal.pow_mem_pow hf (s / m)))
    change f ^ (s / m) ∈ varsIdeal S ^ s at h1
    change f ∈ varsIdeal S ^ m
    rw [← le_ordAlong_iff_mem_pow] at h1 ⊢
    rw [ordAlong_pow] at h1
    obtain ⟨t, rfl⟩ := hs
    have ht : 0 < t := Nat.pos_of_mul_pos_left hs0
    rw [Nat.mul_div_cancel_left t (by omega)] at h1
    rcases eq_or_ne (ordAlong S f) ⊤ with htop | htop
    · rw [htop]; exact le_top
    obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hr] at h1 ⊢
    have : m * t ≤ t * r := by exact_mod_cast h1
    exact_mod_cast (by nlinarith : m ≤ r)

end Tuning

/-! ### Divisors in a chart (Lemma 3.3.3 (2)) -/

section Divisors

variable {σ R : Type*} [CommRing R] [IsDomain R] [DecidableEq σ]

/-- **Volume 2, Lemma 3.3.3 (2) of the handbook**, in the `x_c`-chart of the blowup of the
coordinate center `(x_i : i ∈ S)`. For `l ∈ S` with `l ≠ c`, the transform of the divisor
`(x_l = 0)`, which contains the center, is `(y_l = 0)`. -/
theorem centerChartTransformIdeal_span_X_of_mem {S : Finset σ} {c l : σ} (hl : l ∈ S)
    (hc : l ≠ c) :
    centerChartTransformIdeal S c 1 (Ideal.span {(X l : MvPolynomial σ R)}) =
      Ideal.span {X l} := by
  apply markedTransform_eq_of_map_eq (X_ne_zero c)
  rw [Ideal.map_span, Set.image_singleton, chartSubst_X_of_ne hl hc, pow_one,
    Ideal.span_singleton_mul_span_singleton]

/-- **Volume 2, Lemma 3.3.3 (2) of the handbook**, in the `x_c`-chart. For `l ∉ S`, the pullback
of the divisor `(x_l = 0)` is `(y_l = 0)`. -/
theorem centerChartTransformIdeal_span_X_of_not_mem {S : Finset σ} (c : σ) {l : σ}
    (hl : l ∉ S) :
    centerChartTransformIdeal S c 0 (Ideal.span {(X l : MvPolynomial σ R)}) =
      Ideal.span {X l} := by
  apply markedTransform_eq_of_map_eq (X_ne_zero c)
  have hX : chartSubst S c (X l : MvPolynomial σ R) = X l := by
    rw [chartSubst_X, chartImage]
    split_ifs with hm
    · exact absurd (Finset.mem_of_mem_erase hm) hl
    · rfl
  rw [Ideal.map_span, Set.image_singleton, hX, pow_zero, Ideal.span_singleton_one,
    Ideal.top_mul]

/-- **Volume 2, Lemma 3.3.3 (2) of the handbook**, in the `x_c`-chart. The birational transform
of the divisor `(x_c = 0)` does not meet the chart: the transform of `((x_c), 1)` is the unit
ideal. -/
theorem centerChartTransformIdeal_span_X_self (S : Finset σ) (c : σ) :
    centerChartTransformIdeal S c 1 (Ideal.span {(X c : MvPolynomial σ R)}) = ⊤ := by
  apply markedTransform_eq_of_map_eq (X_ne_zero c)
  rw [Ideal.map_span, Set.image_singleton, chartSubst_X_self, pow_one, Ideal.mul_top]

end Divisors

end Singularity
