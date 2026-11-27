/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.Order

/-!
# The classical coefficient ideal example

This file formalizes Example 3.2.7 of Volume 2 of the handbook, the coefficient ideal of a
function in Weierstrass form.

We use the polynomial ring `MvPolynomial (Option σ) R`. The variable `X none`
is `z`. The variables `X (some i)` are the `x_i`. The function is

  `f = z ^ m + ∑ j ∈ [2, m], a j * z ^ (m - j)`,

where each `a j` is a polynomial in the `x` variables only.

We prove these statements of the example:

* Part 1. If `ord (a j) ≥ j` for each `j`, then `ord f = m`.
* Part 2. At the origin, `ord f ≥ m` if and only if `ord (a j) ≥ j` for each
  `j`. Thus the condition `ord (a j) ≥ j` is the cosupport condition for the
  pair `(f, m)` at the origin.
* Part 3. Let the center be `z` together with the variables `x_i` for `i ∈ S`,
  and let `l ∈ S`. In the chart `U_l` of the blowup, the map is
  `z ↦ x_l * z1`, `x_i ↦ x_l * y_i` for `i ∈ S`, `i ≠ l`, and the other
  variables do not change. If `a j ∈ (x_i : i ∈ S) ^ j` for each `j`, then the
  pullback of `f` is `x_l ^ m * f1`, where `f1` has the same form as `f` with
  new coefficients `b j`. Each `b j` satisfies `π^* a j = x_l ^ j * b j`.
-/

open MvPolynomial

namespace Singularity

variable {σ R : Type*} [CommRing R]

/-- The function `z ^ m + ∑ j ∈ [2, m], a j * z ^ (m - j)`. The variable `z` is
`X none`. Each `a j` is a polynomial in the `x` variables. -/
noncomputable def classicalF (m : ℕ) (a : ℕ → MvPolynomial σ R) :
    MvPolynomial (Option σ) R :=
  X none ^ m + ∑ j ∈ Finset.Icc 2 m, rename some (a j) * X none ^ (m - j)

/-- The order does not decrease when we add the variable `z`. -/
theorem classical_ord_le_ord_rename (p : MvPolynomial σ R) :
    ord p ≤ ord (rename (some : σ → Option σ) p) := by
  have e : (aeval fun i : σ => (X (some i) : MvPolynomial (Option σ) R)) p =
      rename some p := by
    induction p using MvPolynomial.induction_on with
    | C r => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp => simp only [map_mul, hp, aeval_X, rename_X]
  have h := ord_le_ord_aeval (fun i : σ => (X (some i) : MvPolynomial (Option σ) R))
    (fun i => by simp) p
  rwa [e] at h

/-- Part 1, the lower bound. If `ord (a j) ≥ j` for each `j`, then
`ord f ≥ m`. -/
theorem le_ord_classicalF {m : ℕ} {a : ℕ → MvPolynomial σ R}
    (h : ∀ j ∈ Finset.Icc 2 m, (j : ℕ∞) ≤ ord (a j)) :
    (m : ℕ∞) ≤ ord (classicalF m a) := by
  rw [le_ord_iff_mem_pow]
  have hz : (X none : MvPolynomial (Option σ) R) ∈ idealOfVars (Option σ) R := by
    rw [mem_idealOfVars_iff]; simp
  refine Ideal.add_mem _ (Ideal.pow_mem_pow hz m) (Ideal.sum_mem _ fun j hj => ?_)
  have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
  have ha : rename (some : σ → Option σ) (a j) ∈ idealOfVars (Option σ) R ^ j := by
    rw [← le_ord_iff_mem_pow]
    exact le_trans (h j hj) (classical_ord_le_ord_rename (a j))
  have hmem := Ideal.mul_mem_mul ha (Ideal.pow_mem_pow hz (m - j))
  rwa [← pow_add, Nat.add_sub_cancel' hjm] at hmem

/-- Part 1. If `ord (a j) ≥ j` for each `j`, then `ord f = m`. -/
theorem ord_classicalF_eq [Nontrivial R] {m : ℕ} {a : ℕ → MvPolynomial σ R}
    (h : ∀ j ∈ Finset.Icc 2 m, (j : ℕ∞) ≤ ord (a j)) :
    ord (classicalF m a) = m := by
  refine le_antisymm ?_ (le_ord_classicalF h)
  have hc : ∀ j ∈ Finset.Icc 2 m, constantCoeff (a j) = 0 := by
    intro j hj
    have h2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    have h1 : (1 : ℕ∞) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
    exact one_le_ord_iff.mp (le_trans h1 (h j hj))
  let φ : Option σ → MvPolynomial (Option σ) R :=
    fun i => Option.elim i (X none) (fun _ => 0)
  have hφ : ∀ i, constantCoeff (φ i) = 0 := by
    intro i; cases i <;> simp [φ]
  have hsome : φ ∘ some = 0 := by funext i; rfl
  have h0 : ∀ j ∈ Finset.Icc 2 m, aeval φ (rename some (a j)) = 0 := by
    intro j hj
    rw [aeval_rename, hsome, aeval_zero, hc j hj, map_zero]
  have himg : aeval φ (classicalF m a) = X none ^ m := by
    rw [classicalF, map_add, map_sum,
      Finset.sum_eq_zero (fun j hj => by rw [map_mul, h0 j hj, zero_mul]),
      add_zero, map_pow, aeval_X]
    rfl
  have := ord_le_ord_aeval φ hφ (classicalF m a)
  rwa [himg, ord_X_pow] at this

/-- Adding the variable `z` and then reading `f` as a polynomial in `z` gives a
constant polynomial. -/
theorem classical_optionEquivLeft_rename (p : MvPolynomial σ R) :
    optionEquivLeft R σ (rename some p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [optionEquivLeft_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, Polynomial.C_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, rename_X, optionEquivLeft_X_some, Polynomial.C_mul]

/-- The coefficient of `z ^ (m - j)` in `f` is `a j`. -/
theorem optionEquivLeft_classicalF_coeff {m j : ℕ} (a : ℕ → MvPolynomial σ R)
    (hj : j ∈ Finset.Icc 2 m) :
    (optionEquivLeft R σ (classicalF m a)).coeff (m - j) = a j := by
  have h2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
  simp only [classicalF, map_add, map_sum, map_mul, map_pow, optionEquivLeft_X_none,
    classical_optionEquivLeft_rename, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_X_pow]
  rw [if_neg (by omega), zero_add, Finset.sum_eq_single j]
  · rw [if_pos rfl]
  · intro k hk hkj
    have := Finset.mem_Icc.mp hk
    rw [if_neg (by omega)]
  · intro hn; exact absurd hj hn

/-- The degree of the monomial `x ^ d * z ^ k`. -/
theorem degree_optionElim (d : σ →₀ ℕ) (k : ℕ) :
    (d.optionElim k).degree = d.degree + k := by
  have : d.optionElim k = d.mapDomain some + Finsupp.single none k := by
    ext i
    cases i with
    | none =>
      simp [Finsupp.mapDomain_of_notMem_range]
    | some i =>
      simp [Finsupp.mapDomain_apply_of_injective (Option.some_injective σ)]
  rw [this, map_add, Finsupp.degree_mapDomain, Finsupp.degree_single]

/-- Part 2, the converse at the origin. If `ord f ≥ m`, then
`ord (a j) ≥ j` for each `j`. -/
theorem le_ord_coeff_of_le_ord_classicalF {m : ℕ} {a : ℕ → MvPolynomial σ R}
    (h : (m : ℕ∞) ≤ ord (classicalF m a)) :
    ∀ j ∈ Finset.Icc 2 m, (j : ℕ∞) ≤ ord (a j) := by
  intro j hj
  have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
  rw [le_ord_iff] at h ⊢
  intro d hd
  have hdeg : (d.optionElim (m - j)).degree < m := by
    rw [degree_optionElim]; omega
  have hf := h _ hdeg
  rw [← optionEquivLeft_coeff_coeff, optionEquivLeft_classicalF_coeff a hj] at hf
  exact hf

/-- Part 2. At the origin, `ord f ≥ m` if and only if `ord (a j) ≥ j` for each
`j`. -/
theorem le_ord_classicalF_iff {m : ℕ} {a : ℕ → MvPolynomial σ R} :
    (m : ℕ∞) ≤ ord (classicalF m a) ↔ ∀ j ∈ Finset.Icc 2 m, (j : ℕ∞) ≤ ord (a j) :=
  ⟨le_ord_coeff_of_le_ord_classicalF, le_ord_classicalF⟩

open Classical in
/-- The chart `U_l` of the blowup on the `x` variables. The variable `x_i` goes
to `x_l * x_i` for `i ∈ S`, `i ≠ l`. The other variables do not change. -/
noncomputable def classicalChartX (S : Set σ) (l : σ) : σ → MvPolynomial σ R :=
  fun i => if i ∈ S ∧ i ≠ l then X l * X i else X i

/-- The chart `U_l` of the blowup on all variables. The variable `z` goes to
`x_l * z1`. -/
noncomputable def classicalChart (S : Set σ) (l : σ) :
    Option σ → MvPolynomial (Option σ) R :=
  fun i => Option.elim i (X (some l) * X none)
    (fun i => rename some (classicalChartX (R := R) S l i))

/-- In the chart `U_l`, the ideal `(x_i : i ∈ S) ^ j` goes into the ideal
`(x_l ^ j)`. -/
theorem exists_pullback_eq_mul {S : Set σ} {l : σ} (hl : l ∈ S) {j : ℕ}
    {p : MvPolynomial σ R}
    (hp : p ∈ Ideal.span ((X : σ → MvPolynomial σ R) '' S) ^ j) :
    ∃ b : MvPolynomial σ R, aeval (classicalChartX (R := R) S l) p = X l ^ j * b := by
  have hle : Ideal.map (aeval (classicalChartX (R := R) S l))
      (Ideal.span ((X : σ → MvPolynomial σ R) '' S)) ≤ Ideal.span {X l} := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    simp only [aeval_X, SetLike.mem_coe]
    by_cases hil : i = l
    · subst hil
      simp only [classicalChartX, hi, ne_eq, not_true_eq_false, and_false, if_false]
      exact Ideal.subset_span rfl
    · simp only [classicalChartX, hi, ne_eq, hil, not_false_eq_true, and_self, if_true]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hmem : aeval (classicalChartX (R := R) S l) p ∈ Ideal.span {(X l : MvPolynomial σ R) ^ j} := by
    rw [← Ideal.span_singleton_pow]
    refine Ideal.pow_right_mono hle j ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hp
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨b, by rw [← hb, mul_comm]⟩

/-- Part 3, the factorization. If `π^* a j = x_l ^ j * b j` for each `j`, then
`π^* f = x_l ^ m * f1`, where `f1` has the same form as `f` with the
coefficients `b j`. -/
theorem aeval_classicalChart_classicalF {S : Set σ} {l : σ} {m : ℕ}
    {a b : ℕ → MvPolynomial σ R}
    (hab : ∀ j ∈ Finset.Icc 2 m, aeval (classicalChartX (R := R) S l) (a j) = X l ^ j * b j) :
    aeval (classicalChart (R := R) S l) (classicalF m a) = X (some l) ^ m * classicalF m b := by
  have hcomp : classicalChart (R := R) S l ∘ some =
      fun i => rename some (classicalChartX (R := R) S l i) := rfl
  have hren : ∀ p : MvPolynomial σ R,
      aeval (classicalChart (R := R) S l) (rename some p) =
        rename some (aeval (classicalChartX (R := R) S l) p) := by
    intro p
    rw [aeval_rename, hcomp]
    induction p using MvPolynomial.induction_on with
    | C r => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp => simp only [map_mul, hp, aeval_X]
  have hz : aeval (classicalChart (R := R) S l) (X none : MvPolynomial (Option σ) R) =
      X (some l) * X none := by
    rw [aeval_X]; rfl
  rw [classicalF, classicalF, map_add, map_sum, mul_add, Finset.mul_sum, map_pow, hz, mul_pow]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
  have hsplit : (X (some l) : MvPolynomial (Option σ) R) ^ m =
      X (some l) ^ j * X (some l) ^ (m - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hjm]
  rw [map_mul, map_pow, hz, hren, hab j hj, map_mul, map_pow, rename_X, mul_pow, hsplit]
  ring

/-- Part 3. Let `l ∈ S`. If `a j ∈ (x_i : i ∈ S) ^ j` for each `j`, then in the
chart `U_l` we have `π^* f = x_l ^ m * f1`, where `f1` has the same form as `f`
and `π^* a j = x_l ^ j * b j`. -/
theorem exists_classicalChart_classicalF {S : Set σ} {l : σ} (hl : l ∈ S) {m : ℕ}
    {a : ℕ → MvPolynomial σ R}
    (ha : ∀ j ∈ Finset.Icc 2 m, a j ∈ Ideal.span ((X : σ → MvPolynomial σ R) '' S) ^ j) :
    ∃ b : ℕ → MvPolynomial σ R,
      (∀ j ∈ Finset.Icc 2 m, aeval (classicalChartX (R := R) S l) (a j) = X l ^ j * b j) ∧
      aeval (classicalChart (R := R) S l) (classicalF m a) = X (some l) ^ m * classicalF m b := by
  classical
  let b : ℕ → MvPolynomial σ R := fun j =>
    if hj : j ∈ Finset.Icc 2 m then (exists_pullback_eq_mul hl (ha j hj)).choose else 0
  have hb : ∀ j ∈ Finset.Icc 2 m, aeval (classicalChartX (R := R) S l) (a j) = X l ^ j * b j := by
    intro j hj
    simp only [b, dif_pos hj]
    exact (exists_pullback_eq_mul hl (ha j hj)).choose_spec
  exact ⟨b, hb, aeval_classicalChart_classicalF hb⟩

end Singularity
