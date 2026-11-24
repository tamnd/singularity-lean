/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Order.Interval.Set.Infinite

/-!
# Functions that are eventually polynomial

Let `f : ℕ → ℤ` be a function. We say that `f` is eventually polynomial of degree less than `d`
if there is a polynomial `P` with rational coefficients and degree less than `d` such that
`f n = P(n)` for all large `n`. This file gives the link of this property with the forward
difference operator `Δ_[1]` of Mathlib. The main result is that `f` is eventually polynomial of
degree less than `d` if and only if `Δ^d f` is eventually zero.

We use "degree less than `d`" and not "degree at most `d`", because then the case of an
eventually zero function is the case `d = 0`.

## Main results

* `Singularity.Algebra.IsEventuallyPolynomial`: the property.
* `Singularity.Algebra.isEventuallyPolynomial_iff_fwdDiff`: the property holds for `d` if and only
  if `Δ^d f` is eventually zero.
* `Singularity.Algebra.isEventuallyPolynomial_succ_iff`: the form with `natDegree P ≤ d`.
* `Singularity.Algebra.isEventuallyPolynomial_fwdDiff_iff`: `Δ f` has the property for `d` if and
  only if `f` has it for `d + 1`.
* `Singularity.Algebra.IsEventuallyPolynomial.add`, `sub`, `neg`, `smul`, `sum_range`,
  `comp_add`: closure properties.
* `Singularity.Algebra.eq_of_eventually_eval_eq`: the polynomial is unique.
* `Singularity.Algebra.IsEventuallyPolynomial.eventually_fwdDiff_iter_eq`: if the property holds
  for `d + 1`, then `Δ^d f` is eventually the constant `d! * P.coeff d`.
* `Singularity.Algebra.eventualValue`: the eventual value of an eventually constant function.
* `Singularity.Algebra.eventualValue_fwdDiff_iter_nonneg`: if `f` is eventually nonnegative and
  `Δ^d f` is eventually constant, then this constant is nonnegative.

## References

* [AM69] M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*, Chapter 11.
* [Mat89] H. Matsumura, *Commutative Ring Theory*, Section 13.
-/

namespace Singularity.Algebra

open Polynomial Filter Finset fwdDiff

/-- The function `f` agrees for all large `n` with a polynomial of degree less than `d` with
rational coefficients. -/
def IsEventuallyPolynomial (f : ℕ → ℤ) (d : ℕ) : Prop :=
  ∃ P : ℚ[X], P.degree < d ∧ ∀ᶠ n in atTop, (f n : ℚ) = P.eval (n : ℚ)

/-- If `f n = g n` for all `n ≥ N`, then the iterated forward differences of `f` and `g` agree at
each `n ≥ N`. -/
theorem cast_fwdDiff_iter_eq (f : ℕ → ℤ) (g : ℚ → ℚ) {N : ℕ}
    (h : ∀ n, N ≤ n → (f n : ℚ) = g n) (d : ℕ) {n : ℕ} (hn : N ≤ n) :
    ((Δ_[1]^[d] f n : ℤ) : ℚ) = (Δ_[1]^[d] g) (n : ℚ) := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift, Int.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul, Int.cast_mul, h (n + k • 1) (by omega), zsmul_eq_mul]
  congr 2
  push_cast
  simp

/-- A polynomial is determined by its values at all large natural numbers. -/
theorem eq_of_eventually_eval_eq {P Q : ℚ[X]}
    (h : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = Q.eval (n : ℚ)) : P = Q := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  apply Polynomial.eq_of_infinite_eval_eq
  have : ((fun n : ℕ => (n : ℚ)) '' Set.Ici N).Infinite :=
    (Set.Ici_infinite N).image Nat.cast_injective.injOn
  refine this.mono ?_
  rintro _ ⟨n, hn, rfl⟩
  exact hN n hn

/-- The polynomial in `IsEventuallyPolynomial` is unique. -/
theorem IsEventuallyPolynomial.unique {f : ℕ → ℤ} {P Q : ℚ[X]}
    (hP : ∀ᶠ n in atTop, (f n : ℚ) = P.eval (n : ℚ))
    (hQ : ∀ᶠ n in atTop, (f n : ℚ) = Q.eval (n : ℚ)) : P = Q :=
  eq_of_eventually_eval_eq ((hP.and hQ).mono fun _ h => h.1.symm.trans h.2)

/-- The `d`-th forward difference of a polynomial function of degree less than `d` is zero. -/
theorem fwdDiff_iter_eval_eq_zero {P : ℚ[X]} {d : ℕ} (hP : P.degree < d) :
    Δ_[1]^[d] P.eval = 0 := by
  rcases eq_or_ne P 0 with rfl | hP0
  · have h0 : (fun x => eval x (0 : ℚ[X])) = (0 : ℚ → ℚ) := funext fun _ => eval_zero
    rw [h0]
    exact Function.iterate_fixed (by ext; simp [fwdDiff]) d
  · exact Polynomial.fwdDiff_iter_eq_zero_of_degree_lt ((natDegree_lt_iff_degree_lt hP0).mpr hP)

/-- If `Δ^d g` vanishes at each `n ≥ N`, then so does `Δ^k g` for each `k ≥ d`. -/
theorem fwdDiff_iter_eq_zero_of_le {g : ℕ → ℤ} {d N : ℕ}
    (h : ∀ n, N ≤ n → Δ_[1]^[d] g n = 0) {k : ℕ} (hk : d ≤ k) {n : ℕ} (hn : N ≤ n) :
    Δ_[1]^[k] g n = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [add_comm, Function.iterate_add_apply, fwdDiff_iter_eq_sum_shift]
  exact Finset.sum_eq_zero fun i _ => by rw [h _ (by omega), smul_zero]

/-- If `Δ^d f` is eventually zero, then `f` is eventually polynomial of degree less than `d`. -/
theorem isEventuallyPolynomial_of_fwdDiff {f : ℕ → ℤ} {d : ℕ}
    (h : ∀ᶠ n in atTop, (Δ_[1]^[d] f) n = 0) : IsEventuallyPolynomial f d := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  let a : ℕ → ℤ := fun k => Δ_[1]^[k] f N
  have ha : ∀ k, d ≤ k → a k = 0 := fun k hk => fwdDiff_iter_eq_zero_of_le hN hk le_rfl
  refine ⟨∑ k ∈ range d, C ((a k : ℚ) / k.factorial) *
    (descPochhammer ℚ k).comp (X - C (N : ℚ)), ?_, ?_⟩
  · rw [← mem_degreeLT]
    refine Submodule.sum_mem _ fun k hk => ?_
    rw [mem_degreeLT]
    refine lt_of_le_of_lt degree_le_natDegree ?_
    have h1 := natDegree_C_mul_le ((a k : ℚ) / k.factorial)
      ((descPochhammer ℚ k).comp (X - C (N : ℚ)))
    rw [natDegree_comp, descPochhammer_natDegree, natDegree_X_sub_C, mul_one] at h1
    exact_mod_cast lt_of_le_of_lt h1 (mem_range.mp hk)
  · rw [eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hf := shift_eq_sum_fwdDiff_iter (1 : ℕ) f m N
    rw [smul_eq_mul, mul_one] at hf
    rw [hf, eval_finsetSum]
    have h1 : ∑ k ∈ range (m + 1), m.choose k • a k =
        ∑ k ∈ range (m + 1 + d), m.choose k • a k := by
      refine Finset.sum_subset (range_subset_range.mpr (by omega)) fun k _ hk => ?_
      rw [Nat.choose_eq_zero_of_lt (by simp at hk; omega), zero_smul]
    have h2 : ∑ k ∈ range d, m.choose k • a k =
        ∑ k ∈ range (m + 1 + d), m.choose k • a k := by
      refine Finset.sum_subset (range_subset_range.mpr (by omega)) fun k _ hk => ?_
      rw [ha k (by simp at hk; omega), smul_zero]
    change (((∑ k ∈ range (m + 1), m.choose k • a k : ℤ)) : ℚ) = _
    rw [h1, ← h2, Int.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hfac : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    simp only [eval_mul, eval_C, eval_comp, eval_sub, eval_X, Nat.cast_add, add_sub_cancel_left,
      descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose,
      nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    rw [← mul_assoc, div_mul_cancel₀ _ hfac, mul_comm]

/-- The basic criterion: `f` is eventually polynomial of degree less than `d` if and only if
`Δ^d f` is eventually zero. -/
theorem isEventuallyPolynomial_iff_fwdDiff {f : ℕ → ℤ} {d : ℕ} :
    IsEventuallyPolynomial f d ↔ ∀ᶠ n in atTop, (Δ_[1]^[d] f) n = 0 := by
  refine ⟨fun ⟨P, hP, hf⟩ => ?_, isEventuallyPolynomial_of_fwdDiff⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hf
  rw [eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have := cast_fwdDiff_iter_eq f P.eval hN d hn
  rw [fwdDiff_iter_eval_eq_zero hP, Pi.zero_apply] at this
  exact_mod_cast this

/-- For a polynomial `P`, `degree P < d + 1` if and only if `degree P ≤ d`. -/
theorem degree_lt_succ_iff {P : ℚ[X]} {d : ℕ} : P.degree < (d + 1 : ℕ) ↔ P.degree ≤ d := by
  generalize P.degree = e
  induction e using WithBot.recBotCoe with
  | bot => simp
  | coe k => simp only [Nat.cast_withBot, WithBot.coe_lt_coe, WithBot.coe_le_coe]; omega

/-- The form of the property with `natDegree P ≤ d`. -/
theorem isEventuallyPolynomial_succ_iff {f : ℕ → ℤ} {d : ℕ} :
    IsEventuallyPolynomial f (d + 1) ↔
      ∃ P : ℚ[X], P.natDegree ≤ d ∧ ∀ᶠ n in atTop, (f n : ℚ) = P.eval (n : ℚ) := by
  refine exists_congr fun P => and_congr_left fun _ => ?_
  rw [natDegree_le_iff_degree_le]
  exact degree_lt_succ_iff

/-- A bound on the degree can be made larger. -/
theorem IsEventuallyPolynomial.mono {f : ℕ → ℤ} {d e : ℕ} (h : IsEventuallyPolynomial f d)
    (hde : d ≤ e) : IsEventuallyPolynomial f e := by
  obtain ⟨P, hP, hf⟩ := h
  exact ⟨P, lt_of_lt_of_le hP (by exact_mod_cast hde), hf⟩

/-- The property only depends on the values at large `n`. -/
theorem IsEventuallyPolynomial.congr {f g : ℕ → ℤ} {d : ℕ} (h : IsEventuallyPolynomial f d)
    (hfg : ∀ᶠ n in atTop, f n = g n) : IsEventuallyPolynomial g d := by
  obtain ⟨P, hP, hf⟩ := h
  exact ⟨P, hP, (hf.and hfg).mono fun n h => by rw [← h.2]; exact h.1⟩

/-- A function that is eventually zero is eventually polynomial of degree less than `0`. -/
theorem isEventuallyPolynomial_of_eventually_zero {f : ℕ → ℤ} {d : ℕ}
    (h : ∀ᶠ n in atTop, f n = 0) : IsEventuallyPolynomial f d :=
  ⟨0, by rw [degree_zero]; exact WithBot.bot_lt_coe d,
    h.mono fun n h => by rw [h, eval_zero, Int.cast_zero]⟩

/-- A constant function is eventually polynomial of degree less than `1`. -/
theorem isEventuallyPolynomial_const (c : ℤ) : IsEventuallyPolynomial (fun _ => c) 1 :=
  ⟨C (c : ℚ), lt_of_le_of_lt (degree_C_le) (by exact_mod_cast Nat.zero_lt_one),
    Eventually.of_forall fun _ => by rw [eval_C]⟩

/-- The sum of two eventually polynomial functions is eventually polynomial. -/
theorem IsEventuallyPolynomial.add {f g : ℕ → ℤ} {d : ℕ} (hf : IsEventuallyPolynomial f d)
    (hg : IsEventuallyPolynomial g d) : IsEventuallyPolynomial (f + g) d := by
  obtain ⟨P, hP, hf⟩ := hf
  obtain ⟨Q, hQ, hg⟩ := hg
  refine ⟨P + Q, mem_degreeLT.mp (add_mem (mem_degreeLT.mpr hP) (mem_degreeLT.mpr hQ)), ?_⟩
  exact (hf.and hg).mono fun n h => by rw [Pi.add_apply, Int.cast_add, h.1, h.2, eval_add]

/-- An integer multiple of an eventually polynomial function is eventually polynomial. -/
theorem IsEventuallyPolynomial.smul {f : ℕ → ℤ} {d : ℕ} (hf : IsEventuallyPolynomial f d)
    (c : ℤ) : IsEventuallyPolynomial (c • f) d := by
  obtain ⟨P, hP, hf⟩ := hf
  refine ⟨(c : ℚ) • P, mem_degreeLT.mp (Submodule.smul_mem _ _ (mem_degreeLT.mpr hP)), ?_⟩
  exact hf.mono fun n h => by
    rw [Pi.smul_apply, smul_eq_mul, Int.cast_mul, h, eval_smul, smul_eq_mul]

/-- The negative of an eventually polynomial function is eventually polynomial. -/
theorem IsEventuallyPolynomial.neg {f : ℕ → ℤ} {d : ℕ} (hf : IsEventuallyPolynomial f d) :
    IsEventuallyPolynomial (-f) d := by
  simpa using hf.smul (-1)

/-- The difference of two eventually polynomial functions is eventually polynomial. -/
theorem IsEventuallyPolynomial.sub {f g : ℕ → ℤ} {d : ℕ} (hf : IsEventuallyPolynomial f d)
    (hg : IsEventuallyPolynomial g d) : IsEventuallyPolynomial (f - g) d := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

/-- `Δ f` is eventually polynomial of degree less than `d` if and only if `f` is eventually
polynomial of degree less than `d + 1`. -/
theorem isEventuallyPolynomial_fwdDiff_iff {f : ℕ → ℤ} {d : ℕ} :
    IsEventuallyPolynomial (Δ_[1] f) d ↔ IsEventuallyPolynomial f (d + 1) := by
  rw [isEventuallyPolynomial_iff_fwdDiff, isEventuallyPolynomial_iff_fwdDiff,
    Function.iterate_succ_apply]

/-- A shift of an eventually polynomial function is eventually polynomial of the same degree. -/
theorem IsEventuallyPolynomial.comp_add {f : ℕ → ℤ} {d : ℕ} (hf : IsEventuallyPolynomial f d)
    (k : ℕ) : IsEventuallyPolynomial (fun n => f (n + k)) d := by
  rw [isEventuallyPolynomial_iff_fwdDiff] at hf ⊢
  obtain ⟨N, hN⟩ := eventually_atTop.mp hf
  rw [eventually_atTop]
  exact ⟨N, fun n hn => by rw [fwdDiff_iter_comp_add]; exact hN _ (by omega)⟩

/-- The partial sums of an eventually polynomial function of degree less than `d` are eventually
polynomial of degree less than `d + 1`. -/
theorem IsEventuallyPolynomial.sum_range {f : ℕ → ℤ} {d : ℕ} (hf : IsEventuallyPolynomial f d) :
    IsEventuallyPolynomial (fun n => ∑ k ∈ range n, f k) (d + 1) := by
  rw [← isEventuallyPolynomial_fwdDiff_iff]
  have : Δ_[1] (fun n => ∑ k ∈ range n, f k) = f := by
    ext n
    simp [fwdDiff, Finset.sum_range_succ]
  rwa [this]

/-- If `f` is eventually polynomial of degree less than `d + 1` with polynomial `P`, then
`Δ^d f` is eventually the constant `d! * P.coeff d`. -/
theorem IsEventuallyPolynomial.eventually_fwdDiff_iter_eq {f : ℕ → ℤ} {d : ℕ} {P : ℚ[X]}
    (hP : P.degree < (d + 1 : ℕ)) (hf : ∀ᶠ n in atTop, (f n : ℚ) = P.eval (n : ℚ)) :
    ∀ᶠ n in atTop, ((Δ_[1]^[d] f n : ℤ) : ℚ) = d.factorial * P.coeff d := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hf
  rw [eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  rw [cast_fwdDiff_iter_eq f P.eval hN d hn]
  have hle : P.natDegree ≤ d := by
    rw [natDegree_le_iff_degree_le]
    exact degree_lt_succ_iff.mp hP
  rcases hle.lt_or_eq with hlt | heq
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hlt, coeff_eq_zero_of_natDegree_lt hlt]
    simp
  · rw [← heq, Polynomial.fwdDiff_iter_degree_eq_factorial, ← leadingCoeff]
    simp [mul_comm]

/-- The value of a function `g : ℕ → ℤ` at all large `n`, if `g` is eventually constant, and `0`
otherwise. -/
noncomputable def eventualValue (g : ℕ → ℤ) : ℤ :=
  by classical exact if h : ∃ c, ∀ᶠ n in atTop, g n = c then h.choose else 0

/-- If `g` is eventually equal to `c`, then `eventualValue g = c`. -/
theorem eventualValue_eq {g : ℕ → ℤ} {c : ℤ} (h : ∀ᶠ n in atTop, g n = c) :
    eventualValue g = c := by
  have hex : ∃ c, ∀ᶠ n in atTop, g n = c := ⟨c, h⟩
  simp only [eventualValue, hex, ↓reduceDIte]
  obtain ⟨n, hn⟩ := (hex.choose_spec.and h).exists
  exact hn.1.symm.trans hn.2

/-- If `Δ^k f` is eventually at most `-1`, then `f` is eventually at most `-1`. -/
theorem eventually_le_neg_one_of_fwdDiff_iter {f : ℕ → ℤ} (k : ℕ)
    (h : ∀ᶠ n in atTop, Δ_[1]^[k] f n ≤ -1) : ∀ᶠ n in atTop, f n ≤ -1 := by
  induction k generalizing f with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply] at h
    obtain ⟨N, hN⟩ := eventually_atTop.mp (ih h)
    have hstep : ∀ m, f (N + m) ≤ f N - m := by
      intro m
      induction m with
      | zero => simp
      | succ m ihm =>
        have := hN (N + m) (by omega)
        simp only [fwdDiff] at this
        push_cast
        rw [← add_assoc]
        omega
    rw [eventually_atTop]
    refine ⟨N + (f N).toNat + 1, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (le_trans (by omega) hn : N ≤ n)
    have h1 := hstep m
    have h2 := Int.self_le_toNat (f N)
    omega

/-- If `f` is eventually nonnegative and `Δ^d f` is eventually the constant `c`, then
`0 ≤ c`. -/
theorem nonneg_of_eventually_fwdDiff_iter_eq {f : ℕ → ℤ} {d : ℕ} {c : ℤ}
    (hf : ∀ᶠ n in atTop, 0 ≤ f n) (hc : ∀ᶠ n in atTop, Δ_[1]^[d] f n = c) : 0 ≤ c := by
  by_contra hneg
  have := eventually_le_neg_one_of_fwdDiff_iter d (hc.mono fun n h => by rw [h]; omega)
  obtain ⟨n, hn⟩ := (hf.and this).exists
  omega

/-- If `f` is eventually nonnegative and `Δ^d f` is eventually constant, then the eventual value
of `Δ^d f` is nonnegative. -/
theorem eventualValue_fwdDiff_iter_nonneg {f : ℕ → ℤ} {d : ℕ}
    (hf : ∀ᶠ n in atTop, 0 ≤ f n) (hc : ∃ c, ∀ᶠ n in atTop, Δ_[1]^[d] f n = c) :
    0 ≤ eventualValue (Δ_[1]^[d] f) := by
  obtain ⟨c, hc⟩ := hc
  rw [eventualValue_eq hc]
  exact nonneg_of_eventually_fwdDiff_iter_eq hf hc

/-- The iterated forward difference is additive: `Δ^d (f - g) = Δ^d f - Δ^d g`. -/
theorem fwdDiff_iter_sub (f g : ℕ → ℤ) (d : ℕ) :
    Δ_[1]^[d] (f - g) = Δ_[1]^[d] f - Δ_[1]^[d] g := by
  simpa only [fwdDiff_aux.coe_fwdDiffₗ_pow] using
    map_sub (fwdDiff_aux.fwdDiffₗ ℕ ℤ 1 ^ d) f g

/-- Let `f ≤ g` eventually, and let `Δ^d f` and `Δ^d g` be eventually constant. Then the eventual
value of `Δ^d f` is at most the eventual value of `Δ^d g`. -/
theorem eventualValue_fwdDiff_iter_mono {f g : ℕ → ℤ} {d : ℕ}
    (hfg : ∀ᶠ n in atTop, f n ≤ g n) (hf : ∃ c, ∀ᶠ n in atTop, Δ_[1]^[d] f n = c)
    (hg : ∃ c, ∀ᶠ n in atTop, Δ_[1]^[d] g n = c) :
    eventualValue (Δ_[1]^[d] f) ≤ eventualValue (Δ_[1]^[d] g) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  rw [eventualValue_eq ha, eventualValue_eq hb]
  have h := nonneg_of_eventually_fwdDiff_iter_eq (f := g - f) (d := d) (c := b - a)
    (hfg.mono fun n h => by simp only [Pi.sub_apply]; omega)
    ((ha.and hb).mono fun n h => by rw [fwdDiff_iter_sub, Pi.sub_apply, h.1, h.2])
  omega

end Singularity.Algebra
