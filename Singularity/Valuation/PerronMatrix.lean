/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Transvection
import Singularity.Valuation.PerronAlgorithm

/-!
# The matrix of a run of the Perron algorithm

Let `ι` be a finite index set. A step `s = (i, j)` of the Perron algorithm (see `Singularity.Valuation.PerronStep`) replaces the entry `i` of an exponent `D` by `D i + D j`. This map is linear. Its matrix is the elementary matrix `1 + e_{ij}`, the transvection with the entry `1` at the position `(i, j)`. The matrix of a run is the product of the matrices of its steps, in the reverse order. It is an integer matrix with entries `≥ 0` and determinant `1`.

Let `A` be the matrix of a valid run for the weight `γ`, and let `γ'` be the weight after the run. The value of an exponent does not change, so `γ = Aᵀ γ'`. Let `B` be the inverse of `Aᵀ` over `ℤ`. Then the rows of `B` have the values `γ' i > 0`, and an exponent `a` has the coefficients `a ᵥ* Aᵀ = A *ᵥ a` in the basis of the rows of `B`. With the Perron algorithm, this gives a second proof of the lattice lemma for positive real weights (`Singularity.latticeLemma_real_of_pos`), with one more property: the matrix `C = Aᵀ` has entries `≥ 0`.

## Main definitions

* `Singularity.Perron.stepMatrix`: the matrix of a step.
* `Singularity.Perron.runMatrix`: the matrix of a run.

## Main results

* `Singularity.Perron.runMatrix_mulVec`: the matrix of a run acts on exponents as the run.
* `Singularity.Perron.runMatrix_nonneg`: the matrix of a run has entries `≥ 0`.
* `Singularity.Perron.det_runMatrix`: the matrix of a valid run has determinant `1`.
* `Singularity.Perron.sum_runMatrix_mul_runWeight`: the relation `γ = Aᵀ γ'` between the weights.
* `Singularity.Perron.exists_isValidRun_matrix`: the lattice lemma from the Perron algorithm.
* `Singularity.Perron.latticeLemma_real_of_pos_of_perron`: the same in the form of `Singularity.latticeLemma_real_of_pos`.

## References

* Volume 5, Section 2.3 of the handbook.
-/

namespace Singularity.Perron

open Finset Matrix

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- **The matrix of a step** (Volume 5, Proposition 2.3.10 of the handbook). For the step `s = (i, j)`, it is the transvection `1 + e_{ij}`. -/
def stepMatrix (s : ι × ι) : Matrix ι ι ℤ := transvection s.1 s.2 1

/-- **The matrix of a run** (Volume 5, Proposition 2.3.10 of the handbook). The matrix of `s :: l` is the matrix of `l` times the matrix of `s`, because the step `s` acts first. -/
def runMatrix : List (ι × ι) → Matrix ι ι ℤ
  | [] => 1
  | s :: l => runMatrix l * stepMatrix s

omit [Fintype ι] in
/-- **The entries of the matrix of a step.** -/
theorem stepMatrix_apply (s : ι × ι) (i j : ι) :
    stepMatrix s i j = (if i = j then 1 else 0) + if i = s.1 ∧ j = s.2 then 1 else 0 := by
  rw [stepMatrix, transvection, Matrix.add_apply, one_apply, Matrix.single, of_apply]
  congr 1
  exact if_congr ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩ rfl rfl

/-- **The matrix of a step acts as the step** (Volume 5, Proposition 2.3.10 of the handbook). -/
theorem stepMatrix_mulVec (s : ι × ι) (D : ι → ℤ) : stepMatrix s *ᵥ D = stepExp s D := by
  rw [stepMatrix, transvection, add_mulVec, one_mulVec, single_mulVec]
  funext l
  rw [stepExp_apply, Pi.add_apply, Function.update_apply]
  split_ifs with h
  · subst h
    simp
  · simp

/-- **The matrix of a run acts as the run** (Volume 5, Proposition 2.3.10 of the handbook). -/
theorem runMatrix_mulVec (l : List (ι × ι)) (D : ι → ℤ) : runMatrix l *ᵥ D = runExp l D := by
  induction l generalizing D with
  | nil => exact one_mulVec D
  | cons s l ih => rw [runMatrix, runExp, ← mulVec_mulVec, stepMatrix_mulVec, ih]

/-- **The matrix of a concatenated run** (Volume 5, Proposition 2.3.10 of the handbook). -/
theorem runMatrix_append (l₁ l₂ : List (ι × ι)) :
    runMatrix (l₁ ++ l₂) = runMatrix l₂ * runMatrix l₁ := by
  induction l₁ with
  | nil => rw [List.nil_append, runMatrix, Matrix.mul_one]
  | cons s l ih => rw [List.cons_append, runMatrix, runMatrix, ih, Matrix.mul_assoc]

omit [Fintype ι] in
/-- **The matrix of a step has entries `≥ 0`** (Volume 5, Proposition 2.3.10 of the handbook). -/
theorem stepMatrix_nonneg (s : ι × ι) (i j : ι) : 0 ≤ stepMatrix s i j := by
  rw [stepMatrix_apply]
  split_ifs <;> norm_num

/-- **The matrix of a run has entries `≥ 0`** (Volume 5, Proposition 2.3.10 of the handbook). It is a product of matrices with entries `≥ 0`. -/
theorem runMatrix_nonneg (l : List (ι × ι)) (i j : ι) : 0 ≤ runMatrix l i j := by
  induction l generalizing i j with
  | nil =>
    rw [runMatrix, one_apply]
    split_ifs <;> norm_num
  | cons s l ih =>
    rw [runMatrix, mul_apply]
    exact sum_nonneg fun m _ => mul_nonneg (ih i m) (stepMatrix_nonneg s m j)

/-- **The matrix of a step has determinant `1`** (Volume 5, Proposition 2.3.10 of the handbook). -/
theorem det_stepMatrix {s : ι × ι} (hs : s.1 ≠ s.2) : (stepMatrix s).det = 1 :=
  det_transvection_of_ne _ _ hs 1

/-- **The matrix of a valid run has determinant `1`** (Volume 5, Proposition 2.3.10 of the handbook). Each step of a valid run has distinct indices. -/
theorem det_runMatrix {w : ι → ℝ} {l : List (ι × ι)} (hl : IsValidRun w l) :
    (runMatrix l).det = 1 := by
  induction l generalizing w with
  | nil => exact det_one
  | cons s l ih => rw [runMatrix, det_mul, ih hl.2, det_stepMatrix (fst_ne_snd_of_lt hl.1), one_mul]

/-- **The weights before and after a run** (Volume 5, Proposition 2.3.10 of the handbook). Let `A` be the matrix of a valid run for `w`, and let `w'` be the weight after the run. Then `w = Aᵀ w'`. Apply the invariance of the value to the exponent `e_j`. -/
theorem sum_runMatrix_mul_runWeight {w : ι → ℝ} {l : List (ι × ι)} (hl : IsValidRun w l)
    (j : ι) : ∑ i, (runMatrix l i j : ℝ) * runWeight w l i = w j := by
  have h := sum_runExp_mul_runWeight hl (Pi.single j 1)
  rw [← runMatrix_mulVec, mulVec_single_one] at h
  rw [show (∑ i, (runMatrix l i j : ℝ) * runWeight w l i) =
    ∑ i, ((runMatrix l).col j i : ℝ) * runWeight w l i from rfl, h]
  simp [Pi.single_apply]

/-- **The lattice lemma from the Perron algorithm** (Volume 5, Proposition 2.3.10 of the handbook). Let `γ_i > 0` be real numbers, linearly independent over `ℤ`, and let `E` be a finite set of integer vectors `a` with `a · γ ≥ 0`. Then there is a valid run `l` for `γ` with matrix `A`, and an inverse `B` of `Aᵀ` over `ℤ`, such that the row `i` of `B` has the value `γ' i` of the weight after the run, and each `a ∈ E` has coefficients `a ᵥ* Aᵀ ≥ 0`. -/
theorem exists_isValidRun_matrix (γ : ι → ℝ) (hγ : ∀ i, 0 < γ i)
    (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * γ i = 0 → a = 0) (E : Finset (ι → ℤ))
    (hE : ∀ a ∈ E, 0 ≤ ∑ i, (a i : ℝ) * γ i) :
    ∃ (l : List (ι × ι)) (B : Matrix ι ι ℤ), IsValidRun γ l ∧ B * (runMatrix l)ᵀ = 1 ∧
      (runMatrix l)ᵀ * B = 1 ∧ (∀ i, ∑ j, (B i j : ℝ) * γ j = runWeight γ l i) ∧
      ∀ a ∈ E, ∀ i, 0 ≤ (a ᵥ* (runMatrix l)ᵀ) i := by
  obtain ⟨l, hl, hlE⟩ := exists_isValidRun_forall_runExp_nonneg_of_nonneg γ hγ hind E hE
  set A := runMatrix l with hA
  have hdet : IsUnit (Aᵀ).det := by
    rw [det_transpose, hA, det_runMatrix hl]
    exact isUnit_one
  have hBA : (Aᵀ)⁻¹ * Aᵀ = 1 := nonsing_inv_mul _ hdet
  refine ⟨l, (Aᵀ)⁻¹, hl, hBA, mul_nonsing_inv _ hdet, fun i => ?_, fun a ha i => ?_⟩
  · set B := (Aᵀ)⁻¹
    have h1 : ∀ m, ∑ j, (B i j : ℝ) * A m j = if i = m then 1 else 0 := by
      intro m
      have h2 := congrFun (congrFun hBA i) m
      rw [mul_apply, one_apply] at h2
      have h3 := congrArg (fun z : ℤ => (z : ℝ)) h2
      simp only [Int.cast_sum, Int.cast_mul, transpose_apply] at h3
      rw [h3]
      split_ifs <;> simp
    calc ∑ j, (B i j : ℝ) * γ j = ∑ j, (B i j : ℝ) * ∑ m, (A m j : ℝ) * runWeight γ l m := by
          refine sum_congr rfl fun j _ => ?_
          rw [hA, sum_runMatrix_mul_runWeight hl]
      _ = ∑ m, (∑ j, (B i j : ℝ) * A m j) * runWeight γ l m := by
          simp only [mul_sum, sum_mul]
          rw [sum_comm]
          refine sum_congr rfl fun m _ => sum_congr rfl fun j _ => ?_
          ring
      _ = runWeight γ l i := by simp [h1]
  · rw [vecMul_transpose, runMatrix_mulVec]
    exact hlE a ha i

/-- **The lattice lemma for positive real weights, from the Perron algorithm** (Volume 5, Proposition 2.3.10 of the handbook). This is the statement of `Singularity.latticeLemma_real_of_pos`, with one more property: the matrix `C` has entries `≥ 0`. Take `C = Aᵀ`, where `A` is the matrix of the run of `Singularity.Perron.exists_isValidRun_matrix`. -/
theorem latticeLemma_real_of_pos_of_perron (γ : ι → ℝ) (hγ : ∀ i, 0 < γ i)
    (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * γ i = 0 → a = 0) (E : Finset (ι → ℤ))
    (hE : ∀ a ∈ E, 0 ≤ ∑ i, (a i : ℝ) * γ i) :
    ∃ B C : Matrix ι ι ℤ, B * C = 1 ∧ C * B = 1 ∧ (∀ l, 0 < ∑ i, (B l i : ℝ) * γ i) ∧
      (∀ a ∈ E, ∀ l, 0 ≤ (a ᵥ* C) l) ∧ ∀ i j, 0 ≤ C i j := by
  obtain ⟨l, B, hl, hBC, hCB, hrow, hEC⟩ := exists_isValidRun_matrix γ hγ hind E hE
  refine ⟨B, (runMatrix l)ᵀ, hBC, hCB, fun i => ?_, hEC, fun i j => runMatrix_nonneg l j i⟩
  rw [hrow i]
  exact runWeight_pos hγ hl i

end Singularity.Perron
