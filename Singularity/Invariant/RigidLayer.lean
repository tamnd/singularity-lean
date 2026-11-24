/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.Polynomial.Basic

/-!
# The rigid layer of a translation in characteristic `p`

Let `R` be a commutative ring of exponential characteristic `p`, and let `f = z^m + a_1 z^(m-1) + ... + a_m` be a polynomial in `z` over `R`. Here `a_i` is the coefficient `f.coeff (m - i)` of `z^(m-i)`. A translation `z ↦ z + c` changes `f` into `f(z + c) = Polynomial.taylor c f`. This file computes how the translation changes the coefficients `a_i` (Lemmas 10.3, 10.4 and 10.5 of Volume 7, Chapter 4 of the handbook).

In characteristic `0` the translation `z ↦ z - a_1 / m` kills `a_1`. This is the step of Tschirnhausen. After it, the hypersurface `z = 0` has maximal contact with `f`. The same step works in characteristic `p` if `p` does not divide `m`. Now let `m = p^e m_0` with `e ≥ 1`. Then no translation changes `a_1, ..., a_(p^e - 1)` modulo the earlier coefficients: if `a_1 = ... = a_(i-1) = 0` and `i < p^e`, then `a_i` is the same for each `c`. In particular `a_1` never changes. So these coefficients are invariants of the equation under translations. A resolution algorithm cannot make them vanish with a change of coordinates. It must make them small with blowups. This is why multiplicities divisible by `p` are hard.

The first coefficient that a translation can change is `a_(p^e)`. If `a_1 = ... = a_(p^e - 1) = 0`, then the translation adds `m_0 c^(p^e)` to `a_(p^e)`. This is the step of Tschirnhausen in the variable `z^(p^e)`.

The proofs do not use the theorem of Lucas on binomial coefficients. They use the Frobenius identity `(z + c)^(p^e m_0) = (z^(p^e) + c^(p^e))^(m_0)`. So the coefficient of `z^n` in `(z + c)^m` is `0` if `p^e` does not divide `n`.

## Main results

* `Singularity.X_add_C_pow_pow_mul`: the Frobenius identity `(X + c)^(p^e m_0) = (X^(p^e) + c^(p^e))^(m_0)`.
* `Singularity.coeff_X_add_C_pow_pow_mul_eq_zero`, `Singularity.cast_choose_pow_mul_eq_zero`: the coefficient of `X^n` in `(X + c)^(p^e m_0)`, and the binomial coefficient `binom(p^e m_0, n)` in `R`, are `0` if `p^e` does not divide `n`.
* `Singularity.coeff_taylor_natDegree_sub`: the translation formula `a'_i = ∑_(j ≤ i) binom(m - j, i - j) a_j c^(i-j)` for `i ≤ m`.
* `Singularity.coeff_taylor_sub_of_lt_pow`: the inseparable layer is rigid (Lemma 10.4). For `0 < i < p^e`, `a'_i = a_i + ∑_(0 < j < i) binom(m - j, i - j) a_j c^(i-j)`.
* `Singularity.coeff_taylor_sub_of_lt_pow_of_eq_zero`, `Singularity.coeff_taylor_natDegree_sub_one`: if `a_1 = ... = a_(i-1) = 0` and `0 < i < p^e`, then `a'_i = a_i`. If `p` divides `m`, then `a'_1 = a_1`.
* `Singularity.coeff_taylor_sub_pow`, `Singularity.coeff_taylor_sub_pow_of_eq_zero`: the step of Lucas and Tschirnhausen (Lemma 10.3). For monic `f`, `a'_(p^e) = a_(p^e) + m_0 c^(p^e) + ∑_(0 < j < p^e) binom(m - j, p^e - j) a_j c^(p^e - j)`.
* `Singularity.X_pow_add_C_mem_pow_iff`: the lifting test (Lemma 10.5). Let `q = p^e`, let `I` be an ideal of `R`, and let `J = (z - h) + I R[z]`. Then `z^q + g ∈ J^q` if and only if `g + h^q ∈ I^q`.
-/

open Polynomial

namespace Singularity

/-! ### The Frobenius form of the translation -/

section Frobenius

variable {R : Type*} [CommSemiring R] (p : ℕ) [ExpChar R p]

/-- The Frobenius form of the translation. In exponential characteristic `p`, `(X + c)^(p^e m_0) = (X^(p^e) + c^(p^e))^(m_0)`. -/
theorem X_add_C_pow_pow_mul (c : R) (e m₀ : ℕ) :
    (X + C c) ^ (p ^ e * m₀) = (X ^ p ^ e + C (c ^ p ^ e)) ^ m₀ := by
  rw [pow_mul, add_pow_expChar_pow, C_pow]

/-- The power `(X + c)^(p^e m_0)` is the expansion by `X ↦ X^(p^e)` of `(X + c^(p^e))^(m_0)`. -/
theorem X_add_C_pow_pow_mul_eq_expand (c : R) (e m₀ : ℕ) :
    (X + C c) ^ (p ^ e * m₀) = expand R (p ^ e) ((X + C (c ^ p ^ e)) ^ m₀) := by
  rw [X_add_C_pow_pow_mul, map_pow (expand R (p ^ e)), map_add (expand R (p ^ e)), expand_X,
    expand_C]

/-- The coefficient of `X^n` in `(X + c)^(p^e m_0)`. It is `0` if `p^e` does not divide `n`. If `n = p^e k`, then it is `binom(m_0, k) c^(p^e (m_0 - k))`. -/
theorem coeff_X_add_C_pow_pow_mul (c : R) (e m₀ n : ℕ) :
    ((X + C c) ^ (p ^ e * m₀)).coeff n =
      if p ^ e ∣ n then (c ^ p ^ e) ^ (m₀ - n / p ^ e) * (m₀.choose (n / p ^ e) : R) else 0 := by
  rw [X_add_C_pow_pow_mul_eq_expand, coeff_expand (expChar_pow_pos R p e), coeff_X_add_C_pow]

/-- If `p^e` does not divide `n`, then the coefficient of `X^n` in `(X + c)^(p^e m_0)` is `0`. -/
theorem coeff_X_add_C_pow_pow_mul_eq_zero (c : R) {e m₀ n : ℕ} (hn : ¬ p ^ e ∣ n) :
    ((X + C c) ^ (p ^ e * m₀)).coeff n = 0 := by
  simp only [coeff_X_add_C_pow_pow_mul, hn, ↓reduceIte]

/-- If `p^e` does not divide `n`, then `binom(p^e m_0, n) = 0` in a ring of exponential characteristic `p`. This replaces the theorem of Lucas. -/
theorem cast_choose_pow_mul_eq_zero {e m₀ n : ℕ} (hn : ¬ p ^ e ∣ n) :
    (((p ^ e * m₀).choose n : ℕ) : R) = 0 := by
  have h := coeff_X_add_C_pow_pow_mul_eq_zero p (1 : R) (m₀ := m₀) hn
  rwa [coeff_X_add_C_pow, one_pow, one_mul] at h

/-- In a ring of exponential characteristic `p`, `binom(p^e m_0, p^e) = m_0`. -/
theorem cast_choose_pow_mul_pow (e m₀ : ℕ) :
    (((p ^ e * m₀).choose (p ^ e) : ℕ) : R) = m₀ := by
  have h := coeff_X_add_C_pow_pow_mul p (1 : R) e m₀ (p ^ e)
  simp only [coeff_X_add_C_pow, one_pow, one_mul, dvd_refl, ↓reduceIte,
    Nat.div_self (expChar_pow_pos R p e), Nat.choose_one_right] at h
  exact h

end Frobenius

/-! ### The translation formula -/

section Translation

variable {R : Type*} [CommSemiring R]

/-- The translation formula for the coefficients `a_i = f.coeff (m - i)`, with `m` the degree of `f`. Let `a'_i` be the coefficients of `f(z + c)`. For `i ≤ m`, `a'_i = ∑_(j ≤ i) binom(m - j, i - j) a_j c^(i-j)`. -/
theorem coeff_taylor_natDegree_sub (f : R[X]) (c : R) {i : ℕ} (hi : i ≤ f.natDegree) :
    (taylor c f).coeff (f.natDegree - i) =
      ∑ j ∈ Finset.range (i + 1),
        ((f.natDegree - j).choose (i - j) : R) * f.coeff (f.natDegree - j) * c ^ (i - j) := by
  have hsum : ∀ d, (taylor c f).coeff d = ∑ k ∈ Finset.range (f.natDegree + 1),
      (k.choose d : R) * f.coeff k * c ^ (k - d) := by
    intro d
    conv_lhs => rw [f.as_sum_range' (f.natDegree + 1) (Nat.lt_succ_self _)]
    simp only [map_sum, taylor_monomial, finsetSum_coeff, coeff_C_mul, coeff_X_add_C_pow]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsum, ← Finset.sum_range_reflect]
  have hsub : Finset.range (i + 1) ⊆ Finset.range (f.natDegree + 1) :=
    Finset.range_subset_range.2 (by omega)
  refine (Finset.sum_subset hsub ?_).symm.trans ?_
  · intro j hj hj'
    simp only [Finset.mem_range] at hj hj' ⊢
    rw [Nat.choose_eq_zero_of_lt (by omega : f.natDegree + 1 - 1 - j < f.natDegree - i)]
    simp
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [show f.natDegree + 1 - 1 - j = f.natDegree - j by omega,
      show f.natDegree - j - (f.natDegree - i) = i - j by omega,
      Nat.choose_symm_of_eq_add (show f.natDegree - j = (i - j) + (f.natDegree - i) by omega)]

/-- The translation formula with the terms `j = 0` and `j = i` apart. For `0 < i ≤ m`, `a'_i = a_i + binom(m, i) a_0 c^i + ∑_(0 < j < i) binom(m - j, i - j) a_j c^(i-j)`. -/
theorem coeff_taylor_natDegree_sub_eq (f : R[X]) (c : R) {i : ℕ} (hi₀ : 0 < i)
    (hi : i ≤ f.natDegree) :
    (taylor c f).coeff (f.natDegree - i) =
      f.coeff (f.natDegree - i) + (f.natDegree.choose i : R) * f.coeff f.natDegree * c ^ i +
        ∑ j ∈ Finset.Ioo 0 i,
          ((f.natDegree - j).choose (i - j) : R) * f.coeff (f.natDegree - j) * c ^ (i - j) := by
  have hsplit : Finset.range (i + 1) = insert 0 (insert i (Finset.Ioo 0 i)) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [coeff_taylor_natDegree_sub f c hi, hsplit, Finset.sum_insert (by simp; omega),
    Finset.sum_insert (by simp)]
  simp only [Nat.sub_zero, Nat.sub_self, Nat.choose_zero_right, pow_zero, Nat.cast_one, one_mul,
    mul_one]
  ring

end Translation

/-! ### The inseparable layer is rigid -/

section Rigid

variable {R : Type*} [CommSemiring R] (p : ℕ) [ExpChar R p]

/-- If `f` has degree `0`, then the translation formula holds for each `i > 0` with the convention `m - i = 0`. This is the degenerate case `m_0 = 0` of the lemmas below. -/
private theorem coeff_taylor_of_natDegree_eq_zero {f : R[X]} (hf : f.natDegree = 0) (c : R)
    (i : ℕ) (b : R) :
    (taylor c f).coeff (0 - i) = f.coeff (0 - i) + 0 * b +
      ∑ j ∈ Finset.Ioo 0 i, ((0 - j).choose (i - j) : R) * f.coeff (0 - j) * c ^ (i - j) := by
  rw [eq_C_of_natDegree_eq_zero hf, taylor_C, zero_mul, add_zero, Finset.sum_eq_zero, add_zero]
  intro j hj
  rw [Finset.mem_Ioo] at hj
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

/-- The inseparable layer is rigid (Lemma 10.4 of Volume 7, Chapter 4 of the handbook). Let `f` have degree `m = p^e m_0`, and let `a_i = f.coeff (m - i)`. Let `a'_i` be the coefficients of `f(z + c)`. For `0 < i < p^e`, `a'_i = a_i + ∑_(0 < j < i) binom(m - j, i - j) a_j c^(i-j)`. So the term `binom(m, i) c^i` of `a_0` is `0`. -/
theorem coeff_taylor_sub_of_lt_pow {f : R[X]} {e m₀ m : ℕ} (hm : m = p ^ e * m₀)
    (hf : f.natDegree = m) (c : R) {i : ℕ} (hi₀ : 0 < i) (hi : i < p ^ e) :
    (taylor c f).coeff (m - i) = f.coeff (m - i) +
      ∑ j ∈ Finset.Ioo 0 i, ((m - j).choose (i - j) : R) * f.coeff (m - j) * c ^ (i - j) := by
  rcases Nat.eq_zero_or_pos m₀ with rfl | hm₀
  · rw [mul_zero] at hm
    subst hm
    simpa using coeff_taylor_of_natDegree_eq_zero hf c i 0
  · have hle : p ^ e ≤ p ^ e * m₀ := Nat.le_mul_of_pos_right _ hm₀
    have him : i ≤ f.natDegree := by omega
    have h := coeff_taylor_natDegree_sub_eq f c hi₀ him
    rw [hf] at h
    rw [h, hm, cast_choose_pow_mul_eq_zero p (Nat.not_dvd_of_pos_of_lt hi₀ hi), zero_mul, zero_mul,
      add_zero]

/-- If `a_1 = ... = a_(i-1) = 0` and `0 < i < p^e`, then the translation does not change `a_i` (Lemma 10.4 of Volume 7, Chapter 4 of the handbook). -/
theorem coeff_taylor_sub_of_lt_pow_of_eq_zero {f : R[X]} {e m₀ m : ℕ} (hm : m = p ^ e * m₀)
    (hf : f.natDegree = m) (c : R) {i : ℕ} (hi₀ : 0 < i) (hi : i < p ^ e)
    (h : ∀ j, 0 < j → j < i → f.coeff (m - j) = 0) :
    (taylor c f).coeff (m - i) = f.coeff (m - i) := by
  rw [coeff_taylor_sub_of_lt_pow p hm hf c hi₀ hi, Finset.sum_eq_zero, add_zero]
  intro j hj
  rw [Finset.mem_Ioo] at hj
  rw [h j hj.1 hj.2, mul_zero, zero_mul]

/-- If the prime `p` divides the degree `m` of `f`, then the translation `z ↦ z + c` does not change the coefficient `a_1` of `z^(m-1)` (Lemma 10.4 of Volume 7, Chapter 4 of the handbook). In characteristic `0` the translation by `c = -a_1 / m` kills `a_1`. -/
theorem coeff_taylor_natDegree_sub_one [Fact p.Prime] {f : R[X]} (hdvd : p ∣ f.natDegree)
    (c : R) : (taylor c f).coeff (f.natDegree - 1) = f.coeff (f.natDegree - 1) := by
  obtain ⟨m₀, hm₀⟩ := hdvd
  exact coeff_taylor_sub_of_lt_pow_of_eq_zero p (e := 1) (m₀ := m₀) (by rw [pow_one, hm₀]) rfl c one_pos
    (by rw [pow_one]; exact (Fact.out : p.Prime).one_lt) fun j hj hj' => by omega

/-- The step of Lucas and Tschirnhausen (Lemma 10.3 of Volume 7, Chapter 4 of the handbook). Let `f` be monic of degree `m = p^e m_0`, and let `a_i = f.coeff (m - i)`. Let `a'_i` be the coefficients of `f(z + c)`. Then `a'_(p^e) = a_(p^e) + m_0 c^(p^e) + ∑_(0 < j < p^e) binom(m - j, p^e - j) a_j c^(p^e - j)`. -/
theorem coeff_taylor_sub_pow {f : R[X]} (hmonic : f.Monic) {e m₀ m : ℕ} (hm : m = p ^ e * m₀)
    (hf : f.natDegree = m) (c : R) :
    (taylor c f).coeff (m - p ^ e) = f.coeff (m - p ^ e) + m₀ * c ^ p ^ e +
      ∑ j ∈ Finset.Ioo 0 (p ^ e),
        ((m - j).choose (p ^ e - j) : R) * f.coeff (m - j) * c ^ (p ^ e - j) := by
  have hq := expChar_pow_pos R p e
  rcases Nat.eq_zero_or_pos m₀ with rfl | hm₀
  · rw [mul_zero] at hm
    subst hm
    simpa using coeff_taylor_of_natDegree_eq_zero hf c (p ^ e) (c ^ p ^ e)
  · have hle : p ^ e ≤ p ^ e * m₀ := Nat.le_mul_of_pos_right _ hm₀
    have him : p ^ e ≤ f.natDegree := by omega
    have h := coeff_taylor_natDegree_sub_eq f c hq him
    rw [hmonic.coeff_natDegree, hf] at h
    rw [h, hm, cast_choose_pow_mul_pow, mul_one]

/-- If `a_1 = ... = a_(p^e - 1) = 0`, then the translation `z ↦ z + c` adds `m_0 c^(p^e)` to `a_(p^e)` (Lemma 10.3 of Volume 7, Chapter 4 of the handbook). -/
theorem coeff_taylor_sub_pow_of_eq_zero {f : R[X]} (hmonic : f.Monic) {e m₀ m : ℕ}
    (hm : m = p ^ e * m₀) (hf : f.natDegree = m) (c : R)
    (h : ∀ j, 0 < j → j < p ^ e → f.coeff (m - j) = 0) :
    (taylor c f).coeff (m - p ^ e) = f.coeff (m - p ^ e) + m₀ * c ^ p ^ e := by
  rw [coeff_taylor_sub_pow p hmonic hm hf c, Finset.sum_eq_zero, add_zero]
  intro j hj
  rw [Finset.mem_Ioo] at hj
  rw [h j hj.1 hj.2, mul_zero, zero_mul]

end Rigid

/-! ### The lifting test -/

section Lift

variable {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p]

/-- The lifting test (Lemma 10.5 of Volume 7, Chapter 4 of the handbook). Let `q = p^e`, let `I` be an ideal of `R`, let `g, h ∈ R`, and let `J = (z - h) + I R[z]` be the ideal of the centre `z = h` over `V(I)`. Then `z^q + g ∈ J^q` if and only if `g + h^q ∈ I^q`. -/
theorem X_pow_add_C_mem_pow_iff (I : Ideal R) (g h : R) (e : ℕ) :
    X ^ p ^ e + C g ∈ (Ideal.span {X - C h} ⊔ I.map (C : R →+* R[X])) ^ p ^ e ↔
      g + h ^ p ^ e ∈ I ^ p ^ e := by
  constructor
  · intro hmem
    have hJ : (Ideal.span {X - C h} ⊔ I.map (C : R →+* R[X])).map (evalRingHom h) ≤ I := by
      rw [Ideal.map_le_iff_le_comap]
      refine sup_le ?_ ?_
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
        simp
      · rw [Ideal.map_le_iff_le_comap]
        intro x hx
        simpa using hx
    have h₁ := Ideal.mem_map_of_mem (evalRingHom h) hmem
    rw [Ideal.map_pow] at h₁
    have h₂ := Ideal.pow_right_mono hJ _ h₁
    rwa [coe_evalRingHom, eval_add, eval_pow, eval_X, eval_C, add_comm] at h₂
  · intro hmem
    have key : X ^ p ^ e + C g = (X - C h) ^ p ^ e + C (g + h ^ p ^ e) := by
      rw [sub_pow_expChar_pow, map_add, map_pow]
      ring
    rw [key]
    refine Ideal.add_mem _ ?_ ?_
    · exact Ideal.pow_right_mono le_sup_left _
        (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _)
    · refine Ideal.pow_right_mono le_sup_right _ ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem C hmem

end Lift

end Singularity
