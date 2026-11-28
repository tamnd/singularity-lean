/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Elementary steps of the Perron algorithm

Let `ι` be a finite index set. A weight is a function `w : ι → ℝ`, and an exponent is a function `D : ι → ℤ`. The value of `D` is `∑ i, D i * w i`. In the application, `x_i` is a regular system of parameters, `v` is a valuation with `v(x_i) = w i`, and the Laurent monomial `x^D` has the value `∑ i, D i * w i`.

A step is a pair `s = (i, j)` of indices. It is valid for `w` if `w i < w j`. The step replaces the entry `j` of the weight by `w j - w i`, and the entry `i` of each exponent by `D i + D j`. In geometry, this is the blowup of the stratum `V(x_i, x_j)`, followed by the localization at the center of `v`. The new parameters are `x_l` for `l ≠ j` and `x_j / x_i`, and the monomial `x^D` has the new exponent.

A run is a list of steps. This file proves the basic facts about steps and runs. A step does not change the value. A valid step keeps the weight positive. A step with `i ≠ j` keeps the weight independent over `ℤ`. The step is linear in the exponent and keeps exponents `≥ 0`. Two distinct entries of an independent weight are different.

## Main definitions

* `Singularity.Perron.stepWeight`: the weight after a step.
* `Singularity.Perron.stepExp`: the exponent after a step.
* `Singularity.Perron.runWeight`: the weight after a run.
* `Singularity.Perron.runExp`: the exponent after a run.
* `Singularity.Perron.IsValidRun`: each step of the run is valid for the weight before it.

## Main results

* `Singularity.Perron.sum_stepExp_mul_stepWeight`: a step does not change the value.
* `Singularity.Perron.stepWeight_pos`: a valid step keeps the weight positive.
* `Singularity.Perron.stepWeight_independent`: a step keeps the weight independent.
* `Singularity.Perron.ne_of_independent`: distinct entries of an independent weight are different.
* `Singularity.Perron.isValidRun_append`: runs concatenate.
* `Singularity.Perron.sum_runExp_mul_runWeight`, `Singularity.Perron.runWeight_pos`, `Singularity.Perron.runWeight_independent`, `Singularity.Perron.runExp_nonneg`: the facts for valid runs.

## References

* Volume 5, Section 2.3 of the handbook.
-/

namespace Singularity.Perron

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- **The weight after a step** (Volume 5, Section 2.3 of the handbook). For the step `s = (i, j)`, the entry `j` of `w` becomes `w j - w i`. -/
def stepWeight (w : ι → ℝ) (s : ι × ι) : ι → ℝ := Function.update w s.2 (w s.2 - w s.1)

/-- **The exponent after a step** (Volume 5, Section 2.3 of the handbook). For the step `s = (i, j)`, the entry `i` of `D` becomes `D i + D j`. -/
def stepExp (s : ι × ι) (D : ι → ℤ) : ι → ℤ := Function.update D s.1 (D s.1 + D s.2)

/-- **The weight after a run** (Volume 5, Section 2.3 of the handbook). The steps of the list act on the weight in order. -/
def runWeight (w : ι → ℝ) : List (ι × ι) → ι → ℝ
  | [] => w
  | s :: l => runWeight (stepWeight w s) l

/-- **The exponent after a run** (Volume 5, Section 2.3 of the handbook). The steps of the list act on the exponent in order. -/
def runExp : List (ι × ι) → (ι → ℤ) → ι → ℤ
  | [], D => D
  | s :: l, D => runExp l (stepExp s D)

/-- **Valid runs** (Volume 5, Section 2.3 of the handbook). Each step `(i, j)` of the run has `w i < w j` for the weight `w` before the step. -/
def IsValidRun (w : ι → ℝ) : List (ι × ι) → Prop
  | [] => True
  | s :: l => w s.1 < w s.2 ∧ IsValidRun (stepWeight w s) l

/-! ### Steps -/

/-- **The entries of the new weight.** -/
theorem stepWeight_apply (w : ι → ℝ) (s : ι × ι) (l : ι) :
    stepWeight w s l = if l = s.2 then w s.2 - w s.1 else w l := by
  simp [stepWeight, Function.update_apply]

/-- **The entries of the new exponent.** -/
theorem stepExp_apply (s : ι × ι) (D : ι → ℤ) (l : ι) :
    stepExp s D l = if l = s.1 then D s.1 + D s.2 else D l := by
  simp [stepExp, Function.update_apply]

/-- **The value does not change** (Volume 5, Section 2.3 of the handbook). Only the entries `i` and `j` change, and `w i (D i + D j) + (w j - w i) D j = w i D i + w j D j`. -/
theorem sum_stepExp_mul_stepWeight [Fintype ι] (w : ι → ℝ) {s : ι × ι} (hs : s.1 ≠ s.2)
    (D : ι → ℤ) :
    ∑ i, (stepExp s D i : ℝ) * stepWeight w s i = ∑ i, (D i : ℝ) * w i := by
  have h : ∀ l, (stepExp s D l : ℝ) * stepWeight w s l = (D l : ℝ) * w l +
      ((if l = s.1 then (D s.2 : ℝ) * w s.1 else 0) +
        (if l = s.2 then -((D s.2 : ℝ) * w s.1) else 0)) := by
    intro l
    rw [stepExp_apply, stepWeight_apply]
    by_cases h1 : l = s.1
    · subst h1
      simp [hs]
      ring
    · by_cases h2 : l = s.2
      · subst h2
        simp [h1]
        ring
      · simp [h1, h2]
  simp only [h, sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
  ring

/-- **A valid step keeps the weight positive** (Volume 5, Section 2.3 of the handbook). -/
theorem stepWeight_pos {w : ι → ℝ} (hw : ∀ i, 0 < w i) {s : ι × ι} (hs : w s.1 < w s.2) (i : ι) :
    0 < stepWeight w s i := by
  rw [stepWeight_apply]
  split_ifs
  · linarith
  · exact hw i

/-- **The step undoes the transposed step.** If `s.1 ≠ s.2`, then the step `s` maps `a` with the entry `s.1` replaced by `a s.1 - a s.2` back to `a`. -/
theorem stepExp_update_sub {s : ι × ι} (hs : s.1 ≠ s.2) (a : ι → ℤ) :
    stepExp s (Function.update a s.1 (a s.1 - a s.2)) = a := by
  funext l
  rw [stepExp_apply]
  split_ifs with h
  · subst h
    simp [Function.update_of_ne hs.symm]
  · simp [Function.update_of_ne h]

/-- **A step keeps the weight independent** (Volume 5, Section 2.3 of the handbook). We have `∑ a l * w' l = ∑ a' l * w l`, where `a'` is `a` with the entry `i` replaced by `a i - a j`. So `a' = 0`, and then `a = 0`. -/
theorem stepWeight_independent [Fintype ι] {w : ι → ℝ}
    (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * w i = 0 → a = 0) {s : ι × ι} (hs : s.1 ≠ s.2) :
    ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * stepWeight w s i = 0 → a = 0 := by
  intro a ha
  set a' := Function.update a s.1 (a s.1 - a s.2) with ha'
  have h0 : a' = 0 := by
    apply hind
    rw [← sum_stepExp_mul_stepWeight w hs a', ha', stepExp_update_sub hs]
    exact ha
  rw [← stepExp_update_sub hs a, ← ha', h0]
  funext l
  simp [stepExp_apply]

/-- **A step is additive in the exponent** (Volume 5, Section 2.3 of the handbook). -/
theorem stepExp_add (s : ι × ι) (D E : ι → ℤ) : stepExp s (D + E) = stepExp s D + stepExp s E := by
  funext l
  simp only [stepExp_apply, Pi.add_apply]
  split_ifs <;> ring

/-- **A step commutes with subtraction** (Volume 5, Section 2.3 of the handbook). -/
theorem stepExp_sub (s : ι × ι) (D E : ι → ℤ) : stepExp s (D - E) = stepExp s D - stepExp s E := by
  funext l
  simp only [stepExp_apply, Pi.sub_apply]
  split_ifs <;> ring

/-- **A step maps zero to zero.** -/
theorem stepExp_zero (s : ι × ι) : stepExp s (0 : ι → ℤ) = 0 := by
  funext l
  simp [stepExp_apply]

/-- **A step keeps exponents nonnegative** (Volume 5, Section 2.3 of the handbook). -/
theorem stepExp_nonneg (s : ι × ι) {D : ι → ℤ} (hD : ∀ i, 0 ≤ D i) (i : ι) : 0 ≤ stepExp s D i := by
  rw [stepExp_apply]
  split_ifs
  · exact add_nonneg (hD _) (hD _)
  · exact hD i

/-- **Distinct entries of an independent weight are different** (Volume 5, Section 2.3 of the handbook). Take `a = e_i - e_j`. -/
theorem ne_of_independent [Fintype ι] {w : ι → ℝ}
    (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * w i = 0 → a = 0) {i j : ι} (hij : i ≠ j) :
    w i ≠ w j := by
  intro h
  have h0 := hind (Pi.single i 1 - Pi.single j 1) (by
    have e : ∀ l, (((Pi.single i 1 - Pi.single j 1 : ι → ℤ) l : ℤ) : ℝ) * w l =
        (if l = i then w i else 0) - (if l = j then w j else 0) := by
      intro l
      by_cases h1 : l = i
      · subst h1
        simp [hij]
      · by_cases h2 : l = j
        · subst h2
          simp [h1]
        · simp [h1, h2]
    simp only [e, sum_sub_distrib, sum_ite_eq', mem_univ, ite_true, h, sub_self])
  have := congrFun h0 i
  simp [hij] at this

omit [DecidableEq ι] in
/-- **A valid step has distinct indices.** -/
theorem fst_ne_snd_of_lt {w : ι → ℝ} {s : ι × ι} (hs : w s.1 < w s.2) : s.1 ≠ s.2 := by
  intro h
  rw [h] at hs
  exact lt_irrefl _ hs

/-! ### Runs -/

/-- **The weight after a concatenated run** (Volume 5, Section 2.3 of the handbook). -/
theorem runWeight_append (w : ι → ℝ) (l₁ l₂ : List (ι × ι)) :
    runWeight w (l₁ ++ l₂) = runWeight (runWeight w l₁) l₂ := by
  induction l₁ generalizing w with
  | nil => rfl
  | cons s l ih => exact ih _

/-- **The exponent after a concatenated run** (Volume 5, Section 2.3 of the handbook). -/
theorem runExp_append (l₁ l₂ : List (ι × ι)) (D : ι → ℤ) :
    runExp (l₁ ++ l₂) D = runExp l₂ (runExp l₁ D) := by
  induction l₁ generalizing D with
  | nil => rfl
  | cons s l ih => exact ih _

/-- **Runs concatenate** (Volume 5, Section 2.3 of the handbook). The run `l₁ ++ l₂` is valid for `w` if and only if `l₁` is valid for `w` and `l₂` is valid for the weight after `l₁`. -/
theorem isValidRun_append (w : ι → ℝ) (l₁ l₂ : List (ι × ι)) :
    IsValidRun w (l₁ ++ l₂) ↔ IsValidRun w l₁ ∧ IsValidRun (runWeight w l₁) l₂ := by
  induction l₁ generalizing w with
  | nil => simp [IsValidRun, runWeight]
  | cons s l ih =>
    simp only [List.cons_append, IsValidRun, runWeight, ih]
    tauto

/-- **A valid run does not change the value** (Volume 5, Section 2.3 of the handbook). -/
theorem sum_runExp_mul_runWeight [Fintype ι] {w : ι → ℝ} {l : List (ι × ι)} (hl : IsValidRun w l)
    (D : ι → ℤ) : ∑ i, (runExp l D i : ℝ) * runWeight w l i = ∑ i, (D i : ℝ) * w i := by
  induction l generalizing w D with
  | nil => rfl
  | cons s l ih =>
    rw [runExp, runWeight, ih hl.2, sum_stepExp_mul_stepWeight w (fst_ne_snd_of_lt hl.1)]

/-- **A valid run keeps the weight positive** (Volume 5, Section 2.3 of the handbook). -/
theorem runWeight_pos {w : ι → ℝ} (hw : ∀ i, 0 < w i) {l : List (ι × ι)} (hl : IsValidRun w l)
    (i : ι) : 0 < runWeight w l i := by
  induction l generalizing w with
  | nil => exact hw i
  | cons s l ih => exact ih (stepWeight_pos hw hl.1) hl.2

/-- **A valid run keeps the weight independent** (Volume 5, Section 2.3 of the handbook). -/
theorem runWeight_independent [Fintype ι] {w : ι → ℝ}
    (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * w i = 0 → a = 0) {l : List (ι × ι)}
    (hl : IsValidRun w l) : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * runWeight w l i = 0 → a = 0 := by
  induction l generalizing w with
  | nil => exact hind
  | cons s l ih => exact ih (stepWeight_independent hind (fst_ne_snd_of_lt hl.1)) hl.2

/-- **A run is additive in the exponent** (Volume 5, Section 2.3 of the handbook). -/
theorem runExp_add (l : List (ι × ι)) (D E : ι → ℤ) :
    runExp l (D + E) = runExp l D + runExp l E := by
  induction l generalizing D E with
  | nil => rfl
  | cons s l ih => rw [runExp, runExp, runExp, stepExp_add, ih]

/-- **A run commutes with subtraction** (Volume 5, Section 2.3 of the handbook). -/
theorem runExp_sub (l : List (ι × ι)) (D E : ι → ℤ) :
    runExp l (D - E) = runExp l D - runExp l E := by
  induction l generalizing D E with
  | nil => rfl
  | cons s l ih => rw [runExp, runExp, runExp, stepExp_sub, ih]

/-- **A run maps zero to zero.** -/
theorem runExp_zero (l : List (ι × ι)) : runExp l (0 : ι → ℤ) = 0 := by
  induction l with
  | nil => rfl
  | cons s l ih => rw [runExp, stepExp_zero, ih]

/-- **A run keeps exponents nonnegative** (Volume 5, Section 2.3 of the handbook). -/
theorem runExp_nonneg (l : List (ι × ι)) {D : ι → ℤ} (hD : ∀ i, 0 ≤ D i) (i : ι) :
    0 ≤ runExp l D i := by
  induction l generalizing D with
  | nil => exact hD i
  | cons s l ih => exact ih (stepExp_nonneg s hD)

end Singularity.Perron
