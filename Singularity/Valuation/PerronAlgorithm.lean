/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Singularity.Valuation.PerronStep

/-!
# The Perron algorithm with elementary steps

Let `w : ι → ℝ` be a weight with `w i > 0` for each `i`, and assume that the entries of `w` are linearly independent over `ℤ`. Let `D : ι → ℤ` be an exponent with value `∑ i, D i * w i > 0`. The Perron algorithm finds a run of valid steps (see `Singularity.Valuation.PerronStep`) such that the exponent after the run has all entries `≥ 0`. In geometry: after a finite sequence of blowups of strata of codimension 2, each followed by the localization at the center of the valuation, the Laurent monomial `x^D` becomes a monomial.

Two corollaries follow. One run can make all the exponents of a finite set nonnegative. And if `B` has a smaller value than `C`, then after a valid run, `x^B` divides `x^C`. For a finite set of monomials, the monomial of least value divides all the others after a valid run, so a monomial ideal becomes principal.

## The proof

Let `P` be the set of the indices `i` with `D i > 0`, and `N` the set of the indices `j` with `D j < 0`. Let `ν(D) = ∑ j, max(-D j, 0)`. The value `c` does not change under the steps. The rule is as follows. If `N` is empty, stop.

1. Step (a). If there are `i ∈ P` and `j ∈ N` with `w j < w i`, do the step `(j, i)`. Then `ν` goes down.
2. Step (b1). Otherwise `w i < w j` for all `i ∈ P` and `j ∈ N`. If there are `i ∈ P` and `j ∈ N` with `-D j ≤ D i`, do the step `(i, j)`. The entry `i` stays `≥ 0`.
3. Step (b2). Otherwise let `i₀` and `a` be the indices of `P` with the least and the largest weight. They are different, because else the value is negative. Do the step `(i₀, a)`.

The proof is an induction on `ν`. For a fixed `ν`, the steps (b1) and (b2) do not change `ν` and the entries in `N`. They keep a bound `D i ≤ b` and `2 (-D j) ≤ b + 2` for `j ∈ N`. In such a state, the largest weight `U` of `P` satisfies `c ≤ n b U`, where `n` is the number of indices. Let `κ₀ = c / (2 n b)`, so `U ≥ 2 κ₀`. The steps (b1) and (b2) make the triple `(|P|, m₂, ⌊W / κ⌋)` smaller in the lexicographic order. Here `W` is the sum of the weights, `κ` is the minimum of `κ₀` and the weights of `P`, and `m₂` is `1` if all the weights of `P` are `> κ₀` and `0` if not. An inner well-founded induction on this triple completes the proof.

## Main definitions

This file has no public definitions. It uses the steps and runs of `Singularity.Valuation.PerronStep`. The private definitions `posSet`, `negPart`, `Good` and `measure` give the data of the inner induction.

## Main results

* `Singularity.Perron.exists_isValidRun_runExp_nonneg`: the Perron algorithm.
* `Singularity.Perron.exists_isValidRun_forall_runExp_nonneg`: one valid run for a finite set of exponents of positive value.
* `Singularity.Perron.exists_isValidRun_forall_runExp_nonneg_of_nonneg`: the same for exponents of value `≥ 0`.
* `Singularity.Perron.exists_isValidRun_runExp_le`: divisibility of monomials after a valid run.
* `Singularity.Perron.exists_isValidRun_forall_runExp_le`: the monomial of least value in a finite set divides the others after a valid run.

## References

* Volume 5, Section 2.3 of the handbook.
-/

namespace Singularity.Perron

open Finset

variable {ι : Type*} [DecidableEq ι]

/-! ### The data of the inner induction -/

/-- **The positive indices.** The set of the indices `i` with `D i > 0`. -/
private def posSet [Fintype ι] (D : ι → ℤ) : Finset ι := univ.filter fun i => 0 < D i

/-- **The negative part.** The natural number `ν(D) = ∑ i, max(-D i, 0)`. -/
private def negPart [Fintype ι] (D : ι → ℤ) : ℕ := ∑ i, (-D i).toNat

/-- **The good states.** The weight is positive and independent, the value is `c`, the negative part is `ν₀`, and `D` is `b`-bounded. -/
private def Good [Fintype ι] (b : ℤ) (c : ℝ) (ν₀ : ℕ) (w : ι → ℝ) (D : ι → ℤ) : Prop :=
  (∀ i, 0 < w i) ∧ (∀ a : ι → ℤ, ∑ i, (a i : ℝ) * w i = 0 → a = 0) ∧
    ∑ i, (D i : ℝ) * w i = c ∧ negPart D = ν₀ ∧ (∀ i, D i ≤ b) ∧ ∀ j, D j < 0 → 2 * -D j ≤ b + 2

/-- **The inner measure.** The triple `(|P|, m₂, ⌊W / κ⌋)` in the lexicographic order. -/
private noncomputable def measure [Fintype ι] (κ₀ : ℝ) (w : ι → ℝ) (D : ι → ℤ) : ℕ ×ₗ ℕ ×ₗ ℕ :=
  toLex ((posSet D).card, toLex ((if ∀ i ∈ posSet D, κ₀ < w i then 1 else 0),
    ⌊(∑ i, w i) / (posSet D).fold min κ₀ w⌋₊))

omit [DecidableEq ι] in
/-- **The indices of the positive set.** -/
private theorem mem_posSet [Fintype ι] {D : ι → ℤ} {i : ι} : i ∈ posSet D ↔ 0 < D i := by
  simp [posSet]

/-- **Step (a) lowers the negative part.** -/
private theorem negPart_stepExp_lt [Fintype ι] {D : ι → ℤ} {i j : ι} (hj : D j < 0)
    (hi : 0 < D i) : negPart (stepExp (j, i) D) < negPart D := by
  apply sum_lt_sum
  · intro l _
    rw [stepExp_apply]
    split_ifs with h
    · subst h
      dsimp only
      omega
    · exact le_rfl
  · refine ⟨j, mem_univ j, ?_⟩
    rw [stepExp_apply, ite_eq_left rfl]
    dsimp only
    omega

/-- **The steps (b) keep a good state good.** -/
private theorem good_step [Fintype ι] {b : ℤ} {c : ℝ} {ν₀ : ℕ} {w : ι → ℝ} {D : ι → ℤ}
    (h : Good b c ν₀ w D) {s : ι × ι} (hs : w s.1 < w s.2) (h1 : 0 < D s.1)
    (h2 : 0 ≤ D s.1 + D s.2) (h3 : D s.1 + D s.2 ≤ b) :
    Good b c ν₀ (stepWeight w s) (stepExp s D) := by
  obtain ⟨hw, hind, hc, hν, hb, hN⟩ := h
  have hne := fst_ne_snd_of_lt hs
  refine ⟨stepWeight_pos hw hs, stepWeight_independent hind hne, ?_, ?_, ?_, ?_⟩
  · rw [sum_stepExp_mul_stepWeight w hne, hc]
  · rw [← hν]
    apply sum_congr rfl
    intro l _
    rw [stepExp_apply]
    split_ifs with hl
    · subst hl
      omega
    · rfl
  · intro l
    rw [stepExp_apply]
    split_ifs
    · exact h3
    · exact hb l
  · intro l hl
    rw [stepExp_apply] at hl ⊢
    split_ifs at hl ⊢
    · omega
    · exact hN l hl

/-- **The steps (b) do not make the positive set larger.** -/
private theorem posSet_stepExp_subset [Fintype ι] {D : ι → ℤ} {s : ι × ι} (h1 : 0 < D s.1) :
    posSet (stepExp s D) ⊆ posSet D := by
  intro l hl
  rw [mem_posSet, stepExp_apply] at hl
  rw [mem_posSet]
  split_ifs at hl with h
  · rw [h]
    exact h1
  · exact hl

/-- **Step (b2) keeps the positive set.** -/
private theorem posSet_stepExp_eq [Fintype ι] {D : ι → ℤ} {s : ι × ι} (h1 : 0 < D s.1)
    (h2 : 0 < D s.1 + D s.2) : posSet (stepExp s D) = posSet D := by
  ext l
  rw [mem_posSet, mem_posSet, stepExp_apply]
  split_ifs with h
  · subst h
    exact ⟨fun _ => h1, fun _ => h2⟩
  · exact Iff.rfl

/-- **The sum of the weights after a step.** The sum goes down by `w s.1`. -/
private theorem sum_stepWeight [Fintype ι] (w : ι → ℝ) (s : ι × ι) :
    ∑ l, stepWeight w s l = ∑ l, w l - w s.1 := by
  have h : ∀ l, stepWeight w s l = w l - if l = s.2 then w s.1 else 0 := by
    intro l
    rw [stepWeight_apply]
    split_ifs with h
    · subst h
      ring
    · ring
  simp only [h, sum_sub_distrib, sum_ite_eq', mem_univ, ite_true]

omit [DecidableEq ι] in
/-- **The minimum is `κ₀`** if all the weights are `≥ κ₀`. -/
private theorem fold_min_eq_left {s : Finset ι} {κ₀ : ℝ} {w : ι → ℝ} (h : ∀ i ∈ s, κ₀ ≤ w i) :
    s.fold min κ₀ w = κ₀ :=
  le_antisymm ((fold_min_le _).mpr (Or.inl le_rfl)) ((le_fold_min _).mpr ⟨le_rfl, h⟩)

omit [DecidableEq ι] in
/-- **The minimum is the least weight** if the least weight is `≤ κ₀`. -/
private theorem fold_min_eq_of_le {s : Finset ι} {κ₀ : ℝ} {w : ι → ℝ} {i₀ : ι} (hi₀ : i₀ ∈ s)
    (h₀ : w i₀ ≤ κ₀) (h : ∀ i ∈ s, w i₀ ≤ w i) : s.fold min κ₀ w = w i₀ :=
  le_antisymm ((fold_min_le _).mpr (Or.inr ⟨i₀, hi₀, le_rfl⟩)) ((le_fold_min _).mpr ⟨h₀, h⟩)

/-- **The floor goes down** if the sum goes down by at least `κ`. -/
private theorem floor_div_lt {W W' d κ : ℝ} (hκ : 0 < κ) (hd : κ ≤ d) (hW' : 0 ≤ W')
    (h : W' + d ≤ W) : ⌊W' / κ⌋₊ < ⌊W / κ⌋₊ := by
  have h1 : W' / κ + 1 ≤ W / κ := by
    rw [div_add_one hκ.ne', div_le_div_iff_of_pos_right hκ]
    linarith
  have h2 := Nat.floor_le_floor h1
  rw [Nat.floor_add_one (div_nonneg hW' hκ.le)] at h2
  omega

omit [DecidableEq ι] in
/-- **The key inequality.** In a `b`-bounded state, `c ≤ n b U`, where `U` is the largest weight of the positive set. -/
private theorem sum_le_card_mul [Fintype ι] {b : ℤ} (hb : 0 < b) {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    {D : ι → ℤ} (hD : ∀ i, D i ≤ b) {a : ι} (ha : ∀ i ∈ posSet D, w i ≤ w a) :
    ∑ i, (D i : ℝ) * w i ≤ Fintype.card ι * (b * w a) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h : ∀ i, (D i : ℝ) * w i ≤ b * w a := by
    intro i
    by_cases hi : 0 < D i
    · have h1 : w i ≤ w a := ha i (mem_posSet.mpr hi)
      have h2 : (D i : ℝ) ≤ b := by exact_mod_cast hD i
      have h3 : (0 : ℝ) < D i := by exact_mod_cast hi
      nlinarith [hw i]
    · have h1 : (D i : ℝ) ≤ 0 := by exact_mod_cast not_lt.mp hi
      nlinarith [hw i, hw a]
  calc ∑ i, (D i : ℝ) * w i ≤ ∑ _i : ι, (b : ℝ) * w a := sum_le_sum fun i _ => h i
    _ = _ := by simp

/-- **Step (b1) lowers the measure.** -/
private theorem measure_step_b1 [Fintype ι] {κ₀ : ℝ} (hκ₀ : 0 < κ₀) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) {D : ι → ℤ} {i j : ι} (hi : 0 < D i) (hj : D j < 0) (hs : w i < w j) :
    measure κ₀ (stepWeight w (i, j)) (stepExp (i, j) D) < measure κ₀ w D := by
  have hsub : posSet (stepExp (i, j) D) ⊆ posSet D := posSet_stepExp_subset hi
  unfold measure
  simp only [Prod.Lex.toLex_lt_toLex]
  by_cases hP : posSet (stepExp (i, j) D) = posSet D
  · right
    rw [hP]
    refine ⟨rfl, Or.inr ?_⟩
    have hjP : j ∉ posSet D := by
      rw [mem_posSet]
      omega
    have hwP : ∀ l ∈ posSet D, stepWeight w (i, j) l = w l := by
      intro l hl
      rw [stepWeight_apply, ite_eq_right]
      rintro rfl
      exact hjP hl
    have hiff : (∀ l ∈ posSet D, κ₀ < stepWeight w (i, j) l) ↔ ∀ l ∈ posSet D, κ₀ < w l := by
      constructor
      · intro h l hl
        rw [← hwP l hl]
        exact h l hl
      · intro h l hl
        rw [hwP l hl]
        exact h l hl
    refine ⟨by simp only [hiff], ?_⟩
    rw [fold_congr hwP]
    have hiP : i ∈ posSet D := mem_posSet.mpr hi
    apply floor_div_lt (d := w i)
    · exact (lt_fold_min _).mpr ⟨hκ₀, fun l _ => hw l⟩
    · exact (fold_min_le _).mpr (Or.inr ⟨i, hiP, le_rfl⟩)
    · exact sum_nonneg fun l _ => (stepWeight_pos hw hs l).le
    · rw [sum_stepWeight]
      linarith
  · left
    exact card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hP⟩)

/-- **Step (b2) lowers the measure.** -/
private theorem measure_step_b2 [Fintype ι] {κ₀ : ℝ} (hκ₀ : 0 < κ₀) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) {D : ι → ℤ} {i₀ a : ι} (hi₀ : i₀ ∈ posSet D) (ha : a ∈ posSet D)
    (hne : i₀ ≠ a) (hmin : ∀ i ∈ posSet D, w i₀ ≤ w i) (hU : 2 * κ₀ ≤ w a) (hs : w i₀ < w a) :
    measure κ₀ (stepWeight w (i₀, a)) (stepExp (i₀, a) D) < measure κ₀ w D := by
  have hD0 : 0 < D i₀ := mem_posSet.mp hi₀
  have hDa : 0 < D a := mem_posSet.mp ha
  have hP : posSet (stepExp (i₀, a) D) = posSet D :=
    posSet_stepExp_eq hD0 (show 0 < D i₀ + D a by omega)
  have hW : ∑ l, stepWeight w (i₀, a) l + w i₀ ≤ ∑ l, w l := by
    rw [sum_stepWeight]
    linarith
  have hW' : 0 ≤ ∑ l, stepWeight w (i₀, a) l := sum_nonneg fun l _ => (stepWeight_pos hw hs l).le
  have hw0 : stepWeight w (i₀, a) i₀ = w i₀ := by
    rw [stepWeight_apply, ite_eq_right hne]
  unfold measure
  rw [hP]
  apply Prod.Lex.toLex_lt_toLex.mpr
  refine Or.inr ⟨rfl, ?_⟩
  apply Prod.Lex.toLex_lt_toLex.mpr
  dsimp only
  by_cases h1 : ∀ i ∈ posSet D, κ₀ < w i
  · rw [ite_eq_left h1, fold_min_eq_left fun i hi => (h1 i hi).le]
    by_cases h2 : ∀ i ∈ posSet D, κ₀ < stepWeight w (i₀, a) i
    · rw [ite_eq_left h2, fold_min_eq_left fun i hi => (h2 i hi).le]
      exact Or.inr ⟨rfl, floor_div_lt hκ₀ (h1 i₀ hi₀).le hW' hW⟩
    · rw [ite_eq_right h2]
      exact Or.inl zero_lt_one
  · rw [ite_eq_right h1]
    have hi₀κ : w i₀ ≤ κ₀ := by
      push Not at h1
      obtain ⟨i, hi, hle⟩ := h1
      exact (hmin i hi).trans hle
    have h2 : ¬ ∀ i ∈ posSet D, κ₀ < stepWeight w (i₀, a) i := by
      intro h
      have := h i₀ hi₀
      rw [hw0] at this
      linarith
    have hmin' : ∀ i ∈ posSet D, stepWeight w (i₀, a) i₀ ≤ stepWeight w (i₀, a) i := by
      intro i hi
      rw [hw0, stepWeight_apply]
      split_ifs
      · dsimp only
        linarith
      · exact hmin i hi
    rw [ite_eq_right h2, fold_min_eq_of_le hi₀ hi₀κ hmin,
      fold_min_eq_of_le hi₀ (by rw [hw0]; exact hi₀κ) hmin', hw0]
    exact Or.inr ⟨rfl, floor_div_lt (hw i₀) le_rfl hW' hW⟩

/-- **The inner induction.** For a fixed negative part `ν₀`, assume the theorem for all states with a smaller negative part. Then the theorem holds for all good states with negative part `ν₀`, by well-founded induction on the measure. -/
private theorem inner [Fintype ι] (ν₀ : ℕ)
    (IH : ∀ (w : ι → ℝ) (D : ι → ℤ), (∀ i, 0 < w i) →
      (∀ a : ι → ℤ, ∑ i, (a i : ℝ) * w i = 0 → a = 0) → 0 < ∑ i, (D i : ℝ) * w i →
      negPart D < ν₀ → ∃ l, IsValidRun w l ∧ ∀ i, 0 ≤ runExp l D i)
    {b : ℤ} (hb : 0 < b) {c κ₀ : ℝ} (hc : 0 < c) (hκ₀ : 0 < κ₀)
    (hκ₀c : 2 * κ₀ * (Fintype.card ι * b) ≤ c) (m : ℕ ×ₗ ℕ ×ₗ ℕ) :
    ∀ (w : ι → ℝ) (D : ι → ℤ), measure κ₀ w D = m → Good b c ν₀ w D →
      ∃ l, IsValidRun w l ∧ ∀ i, 0 ≤ runExp l D i := by
  induction m using WellFoundedLT.induction with
  | _ m IHm =>
  intro w D hm hgood
  obtain ⟨hw, hind, hcD, hν, hbD, hN⟩ := hgood
  by_cases hdone : ∀ i, 0 ≤ D i
  · exact ⟨[], trivial, hdone⟩
  push Not at hdone
  obtain ⟨j₀, hj₀⟩ := hdone
  -- a step of type (b) and the inner hypothesis
  have step : ∀ s : ι × ι, w s.1 < w s.2 → 0 < D s.1 → 0 ≤ D s.1 + D s.2 →
      D s.1 + D s.2 ≤ b → measure κ₀ (stepWeight w s) (stepExp s D) < measure κ₀ w D →
      ∃ l, IsValidRun w l ∧ ∀ i, 0 ≤ runExp l D i := by
    intro s hs h1 h2 h3 hlt
    obtain ⟨l, hl, hl'⟩ := IHm _ (hm ▸ hlt) _ _ rfl
      (good_step ⟨hw, hind, hcD, hν, hbD, hN⟩ hs h1 h2 h3)
    exact ⟨s :: l, ⟨hs, hl⟩, hl'⟩
  -- step (a)
  by_cases ha : ∃ i j, 0 < D i ∧ D j < 0 ∧ w j < w i
  · obtain ⟨i, j, hi, hj, hji⟩ := ha
    have hne : (j, i).1 ≠ (j, i).2 := fst_ne_snd_of_lt (w := w) hji
    obtain ⟨l, hl, hl'⟩ := IH (stepWeight w (j, i)) (stepExp (j, i) D)
      (stepWeight_pos hw hji) (stepWeight_independent hind hne)
      (by rw [sum_stepExp_mul_stepWeight w hne, hcD]; exact hc) (hν ▸ negPart_stepExp_lt hj hi)
    exact ⟨(j, i) :: l, ⟨hji, hl⟩, hl'⟩
  push Not at ha
  have hlt : ∀ i j, 0 < D i → D j < 0 → w i < w j := fun i j hi hj =>
    lt_of_le_of_ne (ha i j hi hj) (ne_of_independent hind (by rintro rfl; omega))
  -- step (b1)
  by_cases hb1 : ∃ i j, 0 < D i ∧ D j < 0 ∧ -D j ≤ D i
  · obtain ⟨i, j, hi, hj, hij⟩ := hb1
    exact step (i, j) (hlt i j hi hj) hi (show 0 ≤ D i + D j by omega)
      (show D i + D j ≤ b by linarith [hbD i]) (measure_step_b1 hκ₀ hw hi hj (hlt i j hi hj))
  push Not at hb1
  -- step (b2)
  have hPne : (posSet D).Nonempty := by
    by_contra hcon
    rw [not_nonempty_iff_eq_empty] at hcon
    have hle : ∑ i, (D i : ℝ) * w i ≤ 0 := by
      refine sum_nonpos fun i _ => ?_
      have h0 : D i ≤ 0 := by
        by_contra h
        have hi : i ∈ posSet D := mem_posSet.mpr (by omega)
        simp [hcon] at hi
      have h0' : (D i : ℝ) ≤ 0 := by exact_mod_cast h0
      nlinarith [hw i]
    linarith
  obtain ⟨i₀, hi₀, hmin⟩ := (posSet D).exists_min_image w hPne
  obtain ⟨a, ha', hmax⟩ := (posSet D).exists_max_image w hPne
  have hD0 : 0 < D i₀ := mem_posSet.mp hi₀
  have hDa : 0 < D a := mem_posSet.mp ha'
  have hne : i₀ ≠ a := by
    rintro rfl
    have hP1 : ∀ i, 0 < D i → i = i₀ := fun i hi => by
      have hiP : i ∈ posSet D := mem_posSet.mpr hi
      by_contra hne
      exact ne_of_independent hind hne (le_antisymm (hmax i hiP) (hmin i hiP))
    have hj₀i₀ : i₀ ≠ j₀ := by
      rintro rfl
      omega
    have hsum : ∑ l, (D l : ℝ) * w l ≤ ∑ l, ((if l = i₀ then (D i₀ : ℝ) * w i₀ else 0) +
        (if l = j₀ then (D j₀ : ℝ) * w j₀ else 0)) := by
      apply sum_le_sum
      intro l _
      by_cases h1 : l = i₀
      · subst h1
        simp [hj₀i₀]
      · by_cases h2 : l = j₀
        · subst h2
          simp [h1]
        · simp only [h1, h2, ite_false, add_zero]
          have h0 : D l ≤ 0 := by
            by_contra h
            exact h1 (hP1 l (by omega))
          have h0' : (D l : ℝ) ≤ 0 := by exact_mod_cast h0
          nlinarith [hw l]
    simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true] at hsum
    have h1 : (D i₀ : ℝ) < -D j₀ := by exact_mod_cast hb1 i₀ j₀ hD0 hj₀
    have h2 := hlt i₀ j₀ hD0 hj₀
    have h3 : (0 : ℝ) < D i₀ := by exact_mod_cast hD0
    nlinarith [hw i₀]
  have hs : w i₀ < w a := lt_of_le_of_ne (hmin a ha') (ne_of_independent hind hne)
  have hU : 2 * κ₀ ≤ w a := by
    have hk := sum_le_card_mul hb hw hbD hmax
    rw [hcD] at hk
    have hn : (0 : ℝ) < Fintype.card ι * b := by
      have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i₀⟩
      have : (0 : ℝ) < b := by exact_mod_cast hb
      positivity
    have h4 : 2 * κ₀ * (Fintype.card ι * b) ≤ w a * (Fintype.card ι * b) := by linarith
    exact le_of_mul_le_mul_right h4 hn
  have h5 := hb1 i₀ j₀ hD0 hj₀
  have h6 := hb1 a j₀ hDa hj₀
  have h7 := hN j₀ hj₀
  exact step (i₀, a) hs hD0 (show 0 ≤ D i₀ + D a by omega) (show D i₀ + D a ≤ b by omega)
    (measure_step_b2 hκ₀ hw hi₀ ha' hne hmin hU hs)

/-! ### The theorem -/

/-- **The Perron algorithm** (Volume 5, Section 2.3 of the handbook). Let `w` be a positive weight whose entries are linearly independent over `ℤ`, and let `D` be an exponent with `∑ i, D i * w i > 0`. Then there is a valid run `l` for `w` such that the exponent after the run has all entries `≥ 0`. -/
theorem exists_isValidRun_runExp_nonneg [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * w i = 0 → a = 0) (D : ι → ℤ)
    (hD : 0 < ∑ i, (D i : ℝ) * w i) :
    ∃ l : List (ι × ι), IsValidRun w l ∧ ∀ i, 0 ≤ runExp l D i := by
  suffices H : ∀ n : ℕ, ∀ (w : ι → ℝ) (D : ι → ℤ), (∀ i, 0 < w i) →
      (∀ a : ι → ℤ, ∑ i, (a i : ℝ) * w i = 0 → a = 0) → 0 < ∑ i, (D i : ℝ) * w i →
      negPart D = n → ∃ l, IsValidRun w l ∧ ∀ i, 0 ≤ runExp l D i from
    H _ w D hw hind hD rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IHn =>
  intro w D hw hind hD hn
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hD
  have hn0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set b : ℤ := 2 * ∑ i, |D i| + 1 with hb
  have hsum : ∀ i, |D i| ≤ ∑ l, |D l| := fun i =>
    single_le_sum (fun l _ => abs_nonneg (D l)) (mem_univ i)
  have hs0 : 0 ≤ ∑ l, |D l| := sum_nonneg fun l _ => abs_nonneg (D l)
  have hb0 : 0 < b := by omega
  have hb0' : (0 : ℝ) < b := by exact_mod_cast hb0
  have hX : (Fintype.card ι : ℝ) * b ≠ 0 := by positivity
  set κ₀ : ℝ := (∑ i, (D i : ℝ) * w i) / (2 * (Fintype.card ι * b)) with hκ₀
  have hκ₀0 : 0 < κ₀ := by positivity
  have hκ₀c : 2 * κ₀ * (Fintype.card ι * b) ≤ ∑ i, (D i : ℝ) * w i := by
    rw [hκ₀]
    field_simp
    exact le_rfl
  refine inner n (fun w' D' hw' hind' hD' hlt => IHn _ (hn ▸ hlt) w' D' hw' hind' hD' rfl)
    hb0 hD hκ₀0 hκ₀c _ w D rfl ⟨hw, hind, rfl, hn, fun i => ?_, fun j _ => ?_⟩
  · linarith [le_abs_self (D i), hsum i]
  · linarith [neg_le_abs (D j), hsum j]

/-- **One run for a finite set of exponents** (Volume 5, Section 2.3 of the handbook). Let `E` be a finite set of exponents of positive value. Then one valid run makes all the exponents of `E` nonnegative. The proof is an induction on `E`. A run keeps the nonnegative exponents nonnegative. -/
theorem exists_isValidRun_forall_runExp_nonneg [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * w i = 0 → a = 0) (E : Finset (ι → ℤ))
    (hE : ∀ D ∈ E, 0 < ∑ i, (D i : ℝ) * w i) :
    ∃ l : List (ι × ι), IsValidRun w l ∧ ∀ D ∈ E, ∀ i, 0 ≤ runExp l D i := by
  induction E using Finset.induction_on with
  | empty => exact ⟨[], trivial, by simp⟩
  | insert D E _ ih =>
    obtain ⟨l₁, hl₁, h₁⟩ := ih fun D' hD' => hE D' (mem_insert_of_mem hD')
    obtain ⟨l₂, hl₂, h₂⟩ := exists_isValidRun_runExp_nonneg (runWeight w l₁)
      (runWeight_pos hw hl₁) (runWeight_independent hind hl₁) (runExp l₁ D)
      (by rw [sum_runExp_mul_runWeight hl₁]; exact hE D (mem_insert_self D E))
    refine ⟨l₁ ++ l₂, (isValidRun_append w l₁ l₂).mpr ⟨hl₁, hl₂⟩, fun D' hD' i => ?_⟩
    rw [runExp_append]
    rcases mem_insert.mp hD' with rfl | hD'
    · exact h₂ i
    · exact runExp_nonneg l₂ (h₁ D' hD') i

/-- **One run for a finite set of exponents of value `≥ 0`** (Volume 5, Section 2.3 of the handbook). An exponent of value `0` is `0`, because the weight is independent, and a run maps `0` to `0`. -/
theorem exists_isValidRun_forall_runExp_nonneg_of_nonneg [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * w i = 0 → a = 0)
    (E : Finset (ι → ℤ)) (hE : ∀ D ∈ E, 0 ≤ ∑ i, (D i : ℝ) * w i) :
    ∃ l : List (ι × ι), IsValidRun w l ∧ ∀ D ∈ E, ∀ i, 0 ≤ runExp l D i := by
  obtain ⟨l, hl, h⟩ := exists_isValidRun_forall_runExp_nonneg w hw hind (E.filter (· ≠ 0))
    (fun D hD => by
      rw [mem_filter] at hD
      exact lt_of_le_of_ne (hE D hD.1) fun h0 => hD.2 (hind D h0.symm))
  refine ⟨l, hl, fun D hD i => ?_⟩
  by_cases h0 : D = 0
  · rw [h0, runExp_zero]
    exact le_rfl
  · exact h D (mem_filter.mpr ⟨hD, h0⟩) i

/-- **Divisibility of monomials** (Volume 5, Section 2.3 of the handbook). If `B` has a smaller value than `C`, then after a valid run, `x^B` divides `x^C`. Apply the Perron algorithm to `C - B`. -/
theorem exists_isValidRun_runExp_le [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * w i = 0 → a = 0) (B C : ι → ℤ)
    (hBC : ∑ i, (B i : ℝ) * w i < ∑ i, (C i : ℝ) * w i) :
    ∃ l : List (ι × ι), IsValidRun w l ∧ ∀ i, runExp l B i ≤ runExp l C i := by
  obtain ⟨l, hl, h⟩ := exists_isValidRun_runExp_nonneg w hw hind (C - B) (by
    simp only [Pi.sub_apply, Int.cast_sub, sub_mul, sum_sub_distrib]
    linarith)
  refine ⟨l, hl, fun i => ?_⟩
  have h' := h i
  rw [runExp_sub, Pi.sub_apply] at h'
  omega

/-- **The monomial of least value divides the others** (Volume 5, Section 2.3 of the handbook). Let `S` be a finite set of exponents, and let `B` have a value `≤` the value of each element of `S`. Then after one valid run, `x^B` divides `x^C` for each `C ∈ S`. So a monomial ideal becomes principal. -/
theorem exists_isValidRun_forall_runExp_le [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * w i = 0 → a = 0) (S : Finset (ι → ℤ)) (B : ι → ℤ)
    (hS : ∀ C ∈ S, ∑ i, (B i : ℝ) * w i ≤ ∑ i, (C i : ℝ) * w i) :
    ∃ l : List (ι × ι), IsValidRun w l ∧ ∀ C ∈ S, ∀ i, runExp l B i ≤ runExp l C i := by
  obtain ⟨l, hl, h⟩ := exists_isValidRun_forall_runExp_nonneg_of_nonneg w hw hind
    (S.image (· - B)) (fun D hD => by
      obtain ⟨C, hC, rfl⟩ := mem_image.mp hD
      simp only [Pi.sub_apply, Int.cast_sub, sub_mul, sum_sub_distrib]
      linarith [hS C hC])
  refine ⟨l, hl, fun C hC i => ?_⟩
  have h' := h (C - B) (mem_image_of_mem _ hC) i
  rw [runExp_sub, Pi.sub_apply] at h'
  omega

end Singularity.Perron
