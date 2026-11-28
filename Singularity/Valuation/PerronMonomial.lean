/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Singularity.Valuation.PerronAlgorithm

/-!
# Monomialization of a polynomial by the Perron algorithm

Let `ι` be a finite index set, `k` a commutative semiring and `P = MvPolynomial ι k`. A step `s = (i, j)` is the blowup of `V(x_i, x_j)` in the chart `x_j = x_i x_j'`. On polynomials it is the substitution `x_j ↦ x_i x_j`, and the other variables do not change. The monomial `x^d` goes to `x^{s(d)}`, where `s(d)` is `d` with the entry `i` replaced by `d i + d j`. This is the formula of `Singularity.Perron.stepExp` on exponents in `ℕ`. A run acts on polynomials by the composition of its steps, in order.

Let `w` be a positive weight whose entries are linearly independent over `ℤ`, and let `f ≠ 0` be a polynomial. Let `B` be the exponent in the support of `f` with the least value. After a valid run for `w`, the monomial `x^B` divides all the other monomials of `f` (see `Singularity.Perron.exists_isValidRun_forall_runExp_le`). A valid run is injective on exponents, so the transform of `f` is `x^d * g`, where `d` is the transform of `B` and the constant coefficient of `g` is the coefficient of `x^B` in `f`. One run also does this for a finite set of nonzero polynomials.

## Main definitions

* `Singularity.Perron.stepExpNat`: the exponent in `ℕ` after a step.
* `Singularity.Perron.runExpNat`: the exponent in `ℕ` after a run.
* `Singularity.Perron.stepHom`: the substitution `x_j ↦ x_i x_j` of a step.
* `Singularity.Perron.runHom`: the substitution of a run.

## Main results

* `Singularity.Perron.coe_stepExpNat`, `Singularity.Perron.coe_runExpNat`: the link to `stepExp` and `runExp`.
* `Singularity.Perron.stepHom_monomial`, `Singularity.Perron.runHom_monomial`: the action on monomials.
* `Singularity.Perron.runExpNat_injective`, `Singularity.Perron.runHom_injective`: a run with distinct indices in each step is injective.
* `Singularity.Perron.exists_isValidRun_runHom_eq_monomial_mul_coeff`: after a valid run, a nonzero polynomial is a monomial times a polynomial with a nonzero constant coefficient, in the strong form.
* `Singularity.Perron.exists_isValidRun_runHom_eq_monomial_mul`: the same in the short form.
* `Singularity.Perron.exists_isValidRun_forall_runHom_eq_monomial_mul`: one valid run for a finite set of nonzero polynomials.

## References

* Volume 5, Section 2.3 of the handbook.
-/

namespace Singularity.Perron

open Finset MvPolynomial

variable {ι : Type*} [DecidableEq ι] {k : Type*} [CommSemiring k]

/-! ### Exponents in `ℕ` -/

/-- **The exponent in `ℕ` after a step** (Volume 5, Section 2.3 of the handbook). For the step `s = (i, j)`, the entry `i` of `d` becomes `d i + d j`. -/
noncomputable def stepExpNat (s : ι × ι) (d : ι →₀ ℕ) : ι →₀ ℕ := d + Finsupp.single s.1 (d s.2)

/-- **The exponent in `ℕ` after a run** (Volume 5, Section 2.3 of the handbook). The steps of the list act on the exponent in order. -/
noncomputable def runExpNat : List (ι × ι) → (ι →₀ ℕ) → ι →₀ ℕ
  | [], d => d
  | s :: l, d => runExpNat l (stepExpNat s d)

/-- **The entries of the new exponent in `ℕ`.** -/
theorem stepExpNat_apply (s : ι × ι) (d : ι →₀ ℕ) (l : ι) :
    stepExpNat s d l = if l = s.1 then d s.1 + d s.2 else d l := by
  by_cases h : l = s.1
  · subst h
    simp [stepExpNat]
  · simp [stepExpNat, h]

/-- **The link to `stepExp`** (Volume 5, Section 2.3 of the handbook). The cast of the new exponent to `ℤ` is the new exponent of the cast. -/
theorem coe_stepExpNat (s : ι × ι) (d : ι →₀ ℕ) :
    (fun i => (stepExpNat s d i : ℤ)) = stepExp s (fun i => (d i : ℤ)) := by
  funext l
  rw [stepExpNat_apply, stepExp_apply]
  split_ifs <;> simp

/-- **The link to `runExp`** (Volume 5, Section 2.3 of the handbook). The cast of the exponent after a run to `ℤ` is the exponent of the cast after the run. -/
theorem coe_runExpNat (l : List (ι × ι)) (d : ι →₀ ℕ) :
    (fun i => (runExpNat l d i : ℤ)) = runExp l (fun i => (d i : ℤ)) := by
  induction l generalizing d with
  | nil => rfl
  | cons s l ih => rw [runExpNat, runExp, ih, coe_stepExpNat]

/-- **A step is additive in the exponent in `ℕ`.** -/
theorem stepExpNat_add (s : ι × ι) (d e : ι →₀ ℕ) :
    stepExpNat s (d + e) = stepExpNat s d + stepExpNat s e := by
  ext l
  simp only [stepExpNat_apply, Finsupp.add_apply]
  split_ifs <;> omega

omit [DecidableEq ι] in
/-- **A step maps the exponent `0` in `ℕ` to `0`.** -/
theorem stepExpNat_zero (s : ι × ι) : stepExpNat s (0 : ι →₀ ℕ) = 0 := by
  simp [stepExpNat]

/-- **A step on a single exponent.** The step `s` maps `n e_i` to `n e_i + n e_{s.1}` if `i = s.2`, and it fixes `n e_i` if not. -/
theorem stepExpNat_single (s : ι × ι) (i : ι) (n : ℕ) :
    stepExpNat s (Finsupp.single i n) =
      Finsupp.single i n + Finsupp.single s.1 (if i = s.2 then n else 0) := by
  simp [stepExpNat, Finsupp.single_apply]

omit [DecidableEq ι] in
/-- **A run maps the exponent `0` in `ℕ` to `0`.** -/
theorem runExpNat_zero (l : List (ι × ι)) : runExpNat l (0 : ι →₀ ℕ) = 0 := by
  induction l with
  | nil => rfl
  | cons s l ih => rw [runExpNat, stepExpNat_zero, ih]

/-- **A step with distinct indices is injective** (Volume 5, Section 2.3 of the handbook). The entry `s.2` does not change, so the entry `s.1` is known from the new entry `s.1`. -/
theorem stepExpNat_injective {s : ι × ι} (hs : s.1 ≠ s.2) : Function.Injective (stepExpNat s) := by
  intro a b h
  ext l
  have h1 := DFunLike.congr_fun h s.1
  have h2 := DFunLike.congr_fun h s.2
  have h3 := DFunLike.congr_fun h l
  simp [stepExpNat_apply, hs.symm] at h1 h2
  rw [stepExpNat_apply, stepExpNat_apply] at h3
  split_ifs at h3 with hl
  · subst hl
    omega
  · exact h3

/-- **A run with distinct indices in each step is injective** (Volume 5, Section 2.3 of the handbook). -/
theorem runExpNat_injective {l : List (ι × ι)} (hl : ∀ s ∈ l, s.1 ≠ s.2) :
    Function.Injective (runExpNat l) := by
  induction l with
  | nil => exact Function.injective_id
  | cons s l ih =>
    exact (ih fun t ht => hl t (List.mem_cons_of_mem s ht)).comp
      (stepExpNat_injective (hl s List.mem_cons_self))

/-! ### The substitutions -/

variable (k) in
/-- **The substitution of a step** (Volume 5, Section 2.3 of the handbook). For the step `s = (i, j)`, the variable `x_j` goes to `x_i x_j`, and the other variables do not change. This is the blowup of `V(x_i, x_j)` in the chart `x_j = x_i x_j'`. -/
noncomputable def stepHom (s : ι × ι) : MvPolynomial ι k →ₐ[k] MvPolynomial ι k :=
  aeval fun l => if l = s.2 then X s.1 * X s.2 else X l

variable (k) in
/-- **The substitution of a run** (Volume 5, Section 2.3 of the handbook). First the step `s`, then the rest of the run, in the same order as `runExp`. -/
noncomputable def runHom : List (ι × ι) → (MvPolynomial ι k →ₐ[k] MvPolynomial ι k)
  | [] => AlgHom.id k _
  | s :: l => (runHom l).comp (stepHom k s)

/-- **A step on a monomial with coefficient `1`.** The proof is an induction on the exponent. -/
private theorem stepHom_monomial_one (s : ι × ι) (d : ι →₀ ℕ) :
    stepHom k s (monomial d 1) = monomial (stepExpNat s d) 1 := by
  have hmul : ∀ a b : ι →₀ ℕ, monomial (a + b) (1 : k) = monomial a 1 * monomial b 1 := by
    intro a b
    rw [monomial_mul_monomial, one_mul]
  induction d using Finsupp.induction_linear with
  | zero => rw [stepExpNat_zero, monomial_zero', C_1, map_one]
  | add a b ha hb => rw [hmul, map_mul, ha, hb, stepExpNat_add, hmul]
  | single i n =>
    rw [← X_pow_eq_monomial, map_pow, stepHom, aeval_X, stepExpNat_single]
    split_ifs with h
    · subst h
      rw [mul_pow, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul, add_comm]
    · rw [Finsupp.single_zero, add_zero, X_pow_eq_monomial]

/-- **A step on a monomial** (Volume 5, Section 2.3 of the handbook). The step maps `c x^d` to `c x^{s(d)}`. This holds also if `s.1 = s.2`: then `x_i` goes to `x_i ^ 2` and the entry `i` of `d` becomes `d i + d i`. -/
theorem stepHom_monomial (s : ι × ι) (d : ι →₀ ℕ) (c : k) :
    stepHom k s (monomial d c) = monomial (stepExpNat s d) c := by
  have h : ∀ e : ι →₀ ℕ, monomial e c = algebraMap k (MvPolynomial ι k) c * monomial e 1 := by
    intro e
    rw [algebraMap_eq, C_mul_monomial, mul_one]
  rw [h, map_mul, AlgHom.commutes, stepHom_monomial_one, ← h]

/-- **A run on a monomial** (Volume 5, Section 2.3 of the handbook). The run maps `c x^d` to `c x^{l(d)}`. -/
theorem runHom_monomial (l : List (ι × ι)) (d : ι →₀ ℕ) (c : k) :
    runHom k l (monomial d c) = monomial (runExpNat l d) c := by
  induction l generalizing d with
  | nil => rfl
  | cons s l ih => rw [runHom, AlgHom.comp_apply, stepHom_monomial, ih, runExpNat]

/-- **The substitution of a concatenated run** (Volume 5, Section 2.3 of the handbook). -/
theorem runHom_append (l₁ l₂ : List (ι × ι)) :
    runHom k (l₁ ++ l₂) = (runHom k l₂).comp (runHom k l₁) := by
  induction l₁ with
  | nil => exact (AlgHom.comp_id _).symm
  | cons s l ih => rw [List.cons_append, runHom, runHom, ih, AlgHom.comp_assoc]

/-- **The coefficients after an injective run** (Volume 5, Section 2.3 of the handbook). If `runExpNat l` is injective, then the coefficient of `x^{l(d)}` in the transform of `f` is the coefficient of `x^d` in `f`. -/
theorem coeff_runHom {l : List (ι × ι)} (hl : Function.Injective (runExpNat l))
    (f : MvPolynomial ι k) (d : ι →₀ ℕ) : (runHom k l f).coeff (runExpNat l d) = f.coeff d := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum, coeff_sum]
  simp only [runHom_monomial, coeff_monomial, hl.eq_iff]
  rw [sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (notMem_support_iff.mp h).symm

/-- **A run with distinct indices in each step is injective on polynomials** (Volume 5, Section 2.3 of the handbook). Distinct monomials stay distinct. -/
theorem runHom_injective {l : List (ι × ι)} (hl : ∀ s ∈ l, s.1 ≠ s.2) :
    Function.Injective (runHom k l) := by
  intro f g h
  ext d
  rw [← coeff_runHom (runExpNat_injective hl) f d, ← coeff_runHom (runExpNat_injective hl) g d, h]

/-- **A run on a monomial times a polynomial.** -/
theorem runHom_monomial_mul (l : List (ι × ι)) (d : ι →₀ ℕ) (g : MvPolynomial ι k) :
    runHom k l (monomial d 1 * g) = monomial (runExpNat l d) 1 * runHom k l g := by
  rw [map_mul, runHom_monomial]

/-- **A run with distinct indices keeps the constant coefficient** (Volume 5, Section 2.3 of the handbook). -/
theorem constantCoeff_runHom {l : List (ι × ι)} (hl : ∀ s ∈ l, s.1 ≠ s.2) (g : MvPolynomial ι k) :
    constantCoeff (runHom k l g) = constantCoeff g := by
  have h := coeff_runHom (runExpNat_injective hl) g 0
  rw [runExpNat_zero] at h
  rw [constantCoeff_eq, constantCoeff_eq, h]

/-! ### Monomialization -/

/-- **Monomialization of a polynomial, strong form** (Volume 5, Section 2.3 of the handbook). Let `w` be a positive weight whose entries are linearly independent over `ℤ`, and let `f ≠ 0`. Let `B` be the exponent in the support of `f` with the least value. Then there is a valid run `l` for `w` such that the transform of `f` is `x^{l(B)} * g`, and the constant coefficient of `g` is the coefficient of `x^B` in `f`. -/
theorem exists_isValidRun_runHom_eq_monomial_mul_coeff [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * w i = 0 → a = 0)
    {f : MvPolynomial ι k} (hf : f ≠ 0) :
    ∃ B ∈ f.support, (∀ C ∈ f.support, ∑ i, (B i : ℝ) * w i ≤ ∑ i, (C i : ℝ) * w i) ∧
      ∃ (l : List (ι × ι)) (g : MvPolynomial ι k), IsValidRun w l ∧
        runHom k l f = monomial (runExpNat l B) 1 * g ∧ constantCoeff g = f.coeff B := by
  obtain ⟨B, hB, hmin⟩ :=
    f.support.exists_min_image (fun d => ∑ i, (d i : ℝ) * w i) (support_nonempty.mpr hf)
  obtain ⟨l, hl, hle⟩ := exists_isValidRun_forall_runExp_le w hw hind
    (f.support.image fun d i => (d i : ℤ)) (fun i => (B i : ℤ)) (by
      intro C' hC'
      obtain ⟨C, hC, rfl⟩ := mem_image.mp hC'
      simpa only [Int.cast_natCast] using hmin C hC)
  have hinj := runExpNat_injective (fst_ne_snd_of_isValidRun hl)
  have hle' : ∀ C ∈ f.support, runExpNat l B ≤ runExpNat l C := by
    intro C hC
    refine Finsupp.le_def.mpr fun i => ?_
    have h : runExp l (fun i => (B i : ℤ)) i ≤ runExp l (fun i => (C i : ℤ)) i :=
      hle _ (mem_image_of_mem _ hC) i
    rw [← coe_runExpNat, ← coe_runExpNat] at h
    dsimp only at h
    exact_mod_cast h
  refine ⟨B, hB, hmin, l,
    ∑ C ∈ f.support, monomial (runExpNat l C - runExpNat l B) (f.coeff C), hl, ?_, ?_⟩
  · conv_lhs => rw [f.as_sum]
    rw [map_sum, mul_sum]
    refine sum_congr rfl fun C hC => ?_
    rw [runHom_monomial, monomial_mul_monomial, one_mul, add_tsub_cancel_of_le (hle' C hC)]
  · rw [constantCoeff_eq, coeff_sum, sum_eq_single B]
    · rw [coeff_monomial, tsub_self]
      simp
    · intro C hC hCB
      rw [coeff_monomial]
      split_ifs with h
      · exact absurd (hinj (le_antisymm (tsub_eq_zero_iff_le.mp h) (hle' C hC))) hCB
      · rfl
    · intro h
      exact absurd hB h

/-- **Monomialization of a polynomial** (Volume 5, Section 2.3 of the handbook). Let `w` be a positive weight whose entries are linearly independent over `ℤ`, and let `f ≠ 0`. Then there is a valid run `l` for `w` such that the transform of `f` is `x^d * g` with `g(0) ≠ 0`. -/
theorem exists_isValidRun_runHom_eq_monomial_mul [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * w i = 0 → a = 0) {f : MvPolynomial ι k} (hf : f ≠ 0) :
    ∃ (l : List (ι × ι)) (d : ι →₀ ℕ) (g : MvPolynomial ι k), IsValidRun w l ∧
      runHom k l f = monomial d 1 * g ∧ constantCoeff g ≠ 0 := by
  obtain ⟨B, hB, -, l, g, hl, h, hg⟩ :=
    exists_isValidRun_runHom_eq_monomial_mul_coeff w hw hind hf
  exact ⟨l, runExpNat l B, g, hl, h, hg ▸ mem_support_iff.mp hB⟩

/-- **One run for a finite set of polynomials** (Volume 5, Section 2.3 of the handbook). Let `F` be a finite set of nonzero polynomials. Then one valid run makes each element of `F` a monomial times a polynomial with a nonzero constant coefficient. The proof is an induction on `F`. A run keeps this form, because it keeps the constant coefficient. -/
theorem exists_isValidRun_forall_runHom_eq_monomial_mul [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * w i = 0 → a = 0)
    (F : Finset (MvPolynomial ι k)) (hF : ∀ f ∈ F, f ≠ 0) :
    ∃ l : List (ι × ι), IsValidRun w l ∧ ∀ f ∈ F, ∃ (d : ι →₀ ℕ) (g : MvPolynomial ι k),
      runHom k l f = monomial d 1 * g ∧ constantCoeff g ≠ 0 := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨[], trivial, by simp⟩
  | insert f F _ ih =>
    obtain ⟨l₁, hl₁, h₁⟩ := ih fun f' hf' => hF f' (mem_insert_of_mem hf')
    have hf : runHom k l₁ f ≠ 0 := fun h0 => hF f (mem_insert_self f F)
      (runHom_injective (fst_ne_snd_of_isValidRun hl₁) (h0.trans (map_zero _).symm))
    obtain ⟨l₂, d, g, hl₂, h₂, hg⟩ := exists_isValidRun_runHom_eq_monomial_mul
      (runWeight w l₁) (runWeight_pos hw hl₁) (runWeight_independent hind hl₁) hf
    refine ⟨l₁ ++ l₂, (isValidRun_append w l₁ l₂).mpr ⟨hl₁, hl₂⟩, fun f' hf' => ?_⟩
    rw [runHom_append, AlgHom.comp_apply]
    rcases mem_insert.mp hf' with rfl | hf'
    · exact ⟨d, g, h₂, hg⟩
    · obtain ⟨d', g', h', hg'⟩ := h₁ f' hf'
      refine ⟨runExpNat l₂ d', runHom k l₂ g', by rw [h', runHom_monomial_mul], ?_⟩
      rw [constantCoeff_runHom (fst_ne_snd_of_isValidRun hl₂)]
      exact hg'

end Singularity.Perron
