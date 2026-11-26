/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianKangaroo

/-!
# Origin runs that use all the charts

An origin run is a sequence of points where each step goes to the origin of a chart of the
blowup of the origin, in the coordinates of the start. This file proves Lemma Y and Theorem A of
research note 31 (origin runs that use three or more charts), as the referee report 32 states
them in its Section 6. The handbook numbers of these results are not fixed yet.

## The step on the exponents

The origin of the `x_j`-chart sends `x_j` to `x_j` and `x_i` to `x_j x_i` for `i ≠ j`. So it
sends the monomial `x^e` to `x_j^p x^e'`, where `e'_j = |e| - p` and `e'_i = e_i` for `i ≠ j`.
Here `|e|` is the sum of the entries of `e`, and `|e| ≥ p` because the order of `g` is at least
`p` (`expStep`, `pointChart_eq_X_pow_mul_originTransform`). The map `e ↦ e'` is injective on the
vectors with `|e| ≥ p` (`expStep_injOn`), and it keeps the componentwise order (`expStep_mono`).
So no two monomials cancel, and the coefficients do not change (`coeff_originTransform_expStep`,
`support_originTransform`). The map sends a vector that is not in `p ℕ^n` to a vector that is
not in `p ℕ^n`, so no cleaning is necessary (`isClean_originTransform`). The new divisor is
`Δ ∪ {j}` (`blowupDivisor_zero`).

The difference `δ = e - e'` of two exponents changes by `δ_j ← Σ_i δ_i` (`toZ_expStep_sub`).
This is the step `diffStep j` on the integer vectors.

## Lemma Y

Let `δ ∈ ℤ^k`. Let `P` be the sum of the positive entries, let `Q` be minus the sum of the
negative entries, and let `Φ(δ) = min(P, Q)` (`phi`). The vector `δ` is strictly mixed if it has
an entry `< 0` and an entry `> 0` (`IsMixed`). Then:

1. A step does not make `Φ` larger (`phi_diffStep_le`).
2. If `Σ δ ≥ 0`, a step at a negative entry makes `Φ` smaller (`phi_diffStep_lt_of_nonneg`). If
   `Σ δ ≤ 0`, a step at a positive entry makes `Φ` smaller (`phi_diffStep_lt_of_nonpos`). If
   `Σ δ = 0`, a step at a zero entry changes nothing (`diffStep_eq_self`).
3. If `δ ≥ 0` or `δ ≤ 0`, the same is true after each step (`nonneg_diffStep`,
   `nonpos_diffStep`). So a vector that is strictly mixed after some steps was strictly mixed
   before them (`isMixed_of_isMixed_diffSteps`).
4. A window of steps with all `k` letters makes `Φ` smaller for a strictly mixed `δ`
   (`phi_diffSteps_lt`). If `δ` is strictly mixed at the end of `w` such windows, then
   `w + 1 ≤ Φ(δ_0)` (`length_add_one_le_phi`).

## Theorem A

Let `V` be the set of the minimal exponents of `g` (`minimalSupport`), and let `W` be the
largest value of `Φ(e - e') - 1` for `e, e' ∈ V`, or `0` (`windowBound`). If the steps contain
`W + 1` windows with all `n` letters, then `g` has a least exponent at the end
(`exists_least_polySteps`). If `Δ` contains all the coordinates, then `G` is a unit and `ρ = 0`
there (`originRun_unit_of_windows`). Once `g` has a least exponent, it keeps one
(`hasLeastExponent_polySteps`). An origin run that uses each letter an infinite number of times
gets to `ρ = 0` (`originRun_exists_logJacobianOrder_eq_zero`), so it does not keep `ρ ≥ 1`
(`originRun_not_forall_one_le`).

The file works with polynomials. The note works with power series and uses Dickson's lemma to
make `V` finite. For a polynomial the support is finite, so this is not necessary.

## Main definitions

* `OriginRuns.phi`, `OriginRuns.IsMixed`, `OriginRuns.diffStep`, `OriginRuns.diffSteps`: the
  quantity `Φ` and the step on the integer vectors.
* `OriginRuns.expStep`, `OriginRuns.originTransform`: the step on the exponents and on the
  polynomials.
* `OriginRuns.polySteps`, `OriginRuns.IsAdmissible`: a finite origin run, and the condition that
  each monomial has the degree at least `p` before each step.
* `OriginRuns.runPoly`, `OriginRuns.runDivisor`: the points of an infinite origin run.
* `OriginRuns.minimalSupport`, `OriginRuns.windowBound`: the set `V` and the bound `W`.

## Main results

* `OriginRuns.length_add_one_le_phi`: Lemma Y, part 4.
* `OriginRuns.originStep`, `OriginRuns.rhoStep_originStep`: an origin step is a blowup step
  with no cleaning.
* `OriginRuns.originRun_unit_of_windows`: Theorem A, part 2.
* `OriginRuns.originRun_not_forall_one_le`: Theorem A, part 3.

## References

* Research note 31, Section 2.1 (Lemma Y) and Section 3.1 (Theorem 1).
* Research note 32 (referee report on note 31), Section 6 (Lemma Y and Theorem A).
-/

open MvPolynomial Finsupp

namespace Singularity

namespace OriginRuns

/-! ### Lemma Y -/

section LemmaY

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sum `P` of the positive entries of `δ`. -/
def posSum (δ : ι → ℤ) : ℤ := ∑ i, max (δ i) 0

/-- The number `Q`: minus the sum of the negative entries of `δ`. -/
def negSum (δ : ι → ℤ) : ℤ := ∑ i, max (-δ i) 0

/-- The quantity `Φ(δ) = min(P, Q)` of Lemma Y of research note 31. -/
def phi (δ : ι → ℤ) : ℤ := min (posSum δ) (negSum δ)

/-- The vector `δ` is strictly mixed: it has an entry `< 0` and an entry `> 0`. -/
def IsMixed (δ : ι → ℤ) : Prop := (∃ i, δ i < 0) ∧ ∃ i, 0 < δ i

/-- The step with the letter `j` on a difference of exponents: `δ_j ← Σ_i δ_i`. -/
def diffStep (j : ι) (δ : ι → ℤ) : ι → ℤ := Function.update δ j (∑ i, δ i)

/-- The steps with the letters of the list `l`, from the left to the right. -/
def diffSteps (l : List ι) (δ : ι → ℤ) : ι → ℤ := l.foldl (fun δ j => diffStep j δ) δ

@[simp]
theorem diffSteps_nil (δ : ι → ℤ) : diffSteps [] δ = δ := rfl

@[simp]
theorem diffSteps_cons (j : ι) (l : List ι) (δ : ι → ℤ) :
    diffSteps (j :: l) δ = diffSteps l (diffStep j δ) := rfl

theorem diffSteps_append (l₁ l₂ : List ι) (δ : ι → ℤ) :
    diffSteps (l₁ ++ l₂) δ = diffSteps l₂ (diffSteps l₁ δ) := by
  simp only [diffSteps, List.foldl_append]

/-- The sum of `F` over the entries of `δ` after a change of the entry `j`. -/
theorem sum_comp_update (F : ℤ → ℤ) (δ : ι → ℤ) (j : ι) (v : ℤ) :
    ∑ i, F (Function.update δ j v i) = ∑ i, F (δ i) - F (δ j) + F v := by
  have h1 := Finset.add_sum_erase Finset.univ (fun i => F (δ i)) (Finset.mem_univ j)
  have h2 := Finset.add_sum_erase Finset.univ (fun i => F (Function.update δ j v i))
    (Finset.mem_univ j)
  have h3 : ∑ x ∈ Finset.univ.erase j, F (Function.update δ j v x) =
      ∑ x ∈ Finset.univ.erase j, F (δ x) :=
    Finset.sum_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  simp only [Function.update_self] at h2
  rw [← h2, h3, ← h1]
  ring

theorem max_sub_max_neg (a : ℤ) : max a 0 - max (-a) 0 = a := by
  simp only [max_def]
  split_ifs <;> omega

omit [DecidableEq ι] in
/-- `P - Q = Σ_i δ_i`. -/
theorem posSum_sub_negSum (δ : ι → ℤ) : posSum δ - negSum δ = ∑ i, δ i := by
  rw [posSum, negSum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => max_sub_max_neg (δ i)

theorem posSum_diffStep (j : ι) (δ : ι → ℤ) :
    posSum (diffStep j δ) = posSum δ - max (δ j) 0 + max (∑ i, δ i) 0 :=
  sum_comp_update (fun a => max a 0) δ j _

theorem negSum_diffStep (j : ι) (δ : ι → ℤ) :
    negSum (diffStep j δ) = negSum δ - max (-δ j) 0 + max (-∑ i, δ i) 0 :=
  sum_comp_update (fun a => max (-a) 0) δ j _

omit [DecidableEq ι] in
/-- If `Σ δ ≥ 0`, then `Φ(δ) = Q`. -/
theorem phi_eq_negSum (δ : ι → ℤ) (h : 0 ≤ ∑ i, δ i) : phi δ = negSum δ := by
  have := posSum_sub_negSum δ
  rw [phi]
  exact min_eq_right (by linarith)

/-- If `Σ δ ≥ 0`, then a step does not make `Q` larger. -/
theorem negSum_diffStep_le (j : ι) (δ : ι → ℤ) (h : 0 ≤ ∑ i, δ i) :
    negSum (diffStep j δ) ≤ negSum δ := by
  rw [negSum_diffStep]
  have h1 : max (-∑ i, δ i) 0 = 0 := max_eq_right (by linarith)
  have h2 : 0 ≤ max (-δ j) 0 := le_max_right _ _
  linarith

omit [DecidableEq ι] in
theorem phi_le_posSum (δ : ι → ℤ) : phi δ ≤ posSum δ := min_le_left _ _

omit [DecidableEq ι] in
theorem phi_le_negSum (δ : ι → ℤ) : phi δ ≤ negSum δ := min_le_right _ _

omit [DecidableEq ι] in
theorem phi_neg (δ : ι → ℤ) : phi (-δ) = phi δ := by
  have h1 : posSum (-δ) = negSum δ := rfl
  have h2 : negSum (-δ) = posSum δ := by
    simp only [negSum, posSum, Pi.neg_apply, neg_neg]
  rw [phi, phi, h1, h2, min_comm]

omit [DecidableEq ι] in
theorem sum_neg_apply (δ : ι → ℤ) : ∑ i, (-δ) i = -∑ i, δ i := by
  simp only [Pi.neg_apply, Finset.sum_neg_distrib]

theorem diffStep_neg (j : ι) (δ : ι → ℤ) : diffStep j (-δ) = -diffStep j δ := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp only [diffStep, Function.update_self, Pi.neg_apply, Finset.sum_neg_distrib]
  · simp only [diffStep, Function.update_of_ne hi, Pi.neg_apply]

theorem diffSteps_neg (l : List ι) (δ : ι → ℤ) : diffSteps l (-δ) = -diffSteps l δ := by
  induction l generalizing δ with
  | nil => rfl
  | cons j l ih => rw [diffSteps_cons, diffSteps_cons, diffStep_neg, ih]

/-- **Lemma Y, part 1** (research note 31). A step does not make `Φ` larger. -/
theorem phi_diffStep_le (j : ι) (δ : ι → ℤ) : phi (diffStep j δ) ≤ phi δ := by
  rcases le_total 0 (∑ i, δ i) with h | h
  · rw [phi_eq_negSum δ h]
    exact (phi_le_negSum _).trans (negSum_diffStep_le j δ h)
  · have h' : 0 ≤ ∑ i, (-δ) i := by
      rw [sum_neg_apply]
      linarith
    have := (phi_le_negSum _).trans (negSum_diffStep_le j (-δ) h')
    rw [← phi_eq_negSum (-δ) h', diffStep_neg, phi_neg, phi_neg] at this
    exact this

/-- Lemma Y, part 1, for a list of steps. -/
theorem phi_diffSteps_le (l : List ι) (δ : ι → ℤ) : phi (diffSteps l δ) ≤ phi δ := by
  induction l generalizing δ with
  | nil => exact le_rfl
  | cons j l ih => exact (ih _).trans (phi_diffStep_le j δ)

/-- **Lemma Y, part 2** (research note 31). If `Σ δ ≥ 0`, then a step at a negative entry makes
`Φ` smaller. -/
theorem phi_diffStep_lt_of_nonneg {j : ι} {δ : ι → ℤ} (h : 0 ≤ ∑ i, δ i) (hj : δ j < 0) :
    phi (diffStep j δ) < phi δ := by
  rw [phi_eq_negSum δ h]
  refine (phi_le_negSum _).trans_lt ?_
  rw [negSum_diffStep]
  have h1 : max (-∑ i, δ i) 0 = 0 := max_eq_right (by linarith)
  have h2 : max (-δ j) 0 = -δ j := max_eq_left (by linarith)
  linarith

/-- **Lemma Y, part 2** (research note 31). If `Σ δ ≤ 0`, then a step at a positive entry makes
`Φ` smaller. -/
theorem phi_diffStep_lt_of_nonpos {j : ι} {δ : ι → ℤ} (h : ∑ i, δ i ≤ 0) (hj : 0 < δ j) :
    phi (diffStep j δ) < phi δ := by
  have h' : 0 ≤ ∑ i, (-δ) i := by
    rw [sum_neg_apply]
    linarith
  have := phi_diffStep_lt_of_nonneg (j := j) h' (by simp only [Pi.neg_apply]; linarith)
  rwa [diffStep_neg, phi_neg, phi_neg] at this

/-- **Lemma Y, part 2** (research note 31). If `Σ δ = 0`, then a step at a zero entry changes
nothing. -/
theorem diffStep_eq_self {j : ι} {δ : ι → ℤ} (h : ∑ i, δ i = 0) (hj : δ j = 0) :
    diffStep j δ = δ := by
  rw [diffStep, h, ← hj, Function.update_eq_self]

/-- If `Σ δ ≥ 0` and a step makes the sum negative, then the step makes `Φ` smaller. -/
theorem phi_diffStep_lt_of_sum_neg {j : ι} {δ : ι → ℤ} (h : 0 ≤ ∑ i, δ i)
    (h' : ∑ i, diffStep j δ i < 0) : phi (diffStep j δ) < phi δ := by
  have e := posSum_sub_negSum (diffStep j δ)
  have hq := negSum_diffStep_le j δ h
  rw [phi_eq_negSum δ h]
  refine (phi_le_posSum _).trans_lt ?_
  linarith

/-- The main step of the proof of Lemma Y, part 4. If `Σ δ ≥ 0` and the list `l` contains a
letter `j` with `δ_j < 0`, then the steps of `l` make `Φ` smaller. -/
theorem phi_diffSteps_lt_of_nonneg {l : List ι} {δ : ι → ℤ} (h : 0 ≤ ∑ i, δ i)
    {j : ι} (hjl : j ∈ l) (hj : δ j < 0) : phi (diffSteps l δ) < phi δ := by
  induction l generalizing δ with
  | nil => simp at hjl
  | cons a l ih =>
    rw [diffSteps_cons]
    by_cases ha : δ a < 0
    · exact (phi_diffSteps_le l _).trans_lt (phi_diffStep_lt_of_nonneg h ha)
    · have hja : j ≠ a := fun hja => ha (hja ▸ hj)
      have hjl' : j ∈ l := by
        rcases List.mem_cons.mp hjl with h1 | h1
        · exact absurd h1 hja
        · exact h1
      have hj' : diffStep a δ j < 0 := by
        rw [diffStep, Function.update_of_ne hja]
        exact hj
      by_cases hS : 0 ≤ ∑ i, diffStep a δ i
      · exact (ih hS hjl' hj').trans_le (phi_diffStep_le a δ)
      · exact (phi_diffSteps_le l _).trans_lt
          (phi_diffStep_lt_of_sum_neg h (lt_of_not_ge hS))

/-- **Lemma Y, part 4, one window** (research note 31). If `δ` is strictly mixed and the list
`l` contains all the letters, then the steps of `l` make `Φ` smaller. -/
theorem phi_diffSteps_lt {l : List ι} {δ : ι → ℤ} (hδ : IsMixed δ) (hl : ∀ i, i ∈ l) :
    phi (diffSteps l δ) < phi δ := by
  obtain ⟨⟨j, hj⟩, ⟨j', hj'⟩⟩ := hδ
  rcases le_total 0 (∑ i, δ i) with h | h
  · exact phi_diffSteps_lt_of_nonneg h (hl j) hj
  · have h' : 0 ≤ ∑ i, (-δ) i := by
      rw [sum_neg_apply]
      linarith
    have := phi_diffSteps_lt_of_nonneg h' (hl j') (by simp only [Pi.neg_apply]; linarith)
    rwa [diffSteps_neg, phi_neg, phi_neg] at this

/-- **Lemma Y, part 3** (research note 31). If `δ ≥ 0`, then `δ ≥ 0` after a step. -/
theorem nonneg_diffStep {δ : ι → ℤ} (h : ∀ i, 0 ≤ δ i) (j : ι) : ∀ i, 0 ≤ diffStep j δ i := by
  intro i
  by_cases hi : i = j
  · subst hi
    rw [diffStep, Function.update_self]
    exact Finset.sum_nonneg fun i _ => h i
  · rw [diffStep, Function.update_of_ne hi]
    exact h i

/-- **Lemma Y, part 3** (research note 31). If `δ ≤ 0`, then `δ ≤ 0` after a step. -/
theorem nonpos_diffStep {δ : ι → ℤ} (h : ∀ i, δ i ≤ 0) (j : ι) : ∀ i, diffStep j δ i ≤ 0 := by
  intro i
  by_cases hi : i = j
  · subst hi
    rw [diffStep, Function.update_self]
    exact Finset.sum_nonpos fun i _ => h i
  · rw [diffStep, Function.update_of_ne hi]
    exact h i

theorem nonneg_diffSteps {δ : ι → ℤ} (h : ∀ i, 0 ≤ δ i) (l : List ι) :
    ∀ i, 0 ≤ diffSteps l δ i := by
  induction l generalizing δ with
  | nil => exact h
  | cons j l ih => exact ih (nonneg_diffStep h j)

theorem nonpos_diffSteps {δ : ι → ℤ} (h : ∀ i, δ i ≤ 0) (l : List ι) :
    ∀ i, diffSteps l δ i ≤ 0 := by
  induction l generalizing δ with
  | nil => exact h
  | cons j l ih => exact ih (nonpos_diffStep h j)

omit [DecidableEq ι] in
theorem not_isMixed_iff {δ : ι → ℤ} : ¬ IsMixed δ ↔ (∀ i, 0 ≤ δ i) ∨ ∀ i, δ i ≤ 0 := by
  unfold IsMixed
  constructor
  · intro h
    by_cases h1 : ∃ i, δ i < 0
    · right
      intro i
      by_contra hi
      exact h ⟨h1, i, lt_of_not_ge hi⟩
    · left
      intro i
      by_contra hi
      exact h1 ⟨i, lt_of_not_ge hi⟩
  · rintro (h | h) ⟨⟨i, hi⟩, ⟨i', hi'⟩⟩
    · exact absurd (h i) (not_le.mpr hi)
    · exact absurd (h i') (not_le.mpr hi')

/-- **Lemma Y, part 3** (research note 31). If `δ` is strictly mixed after the steps of `l`,
then `δ` is strictly mixed. -/
theorem isMixed_of_isMixed_diffSteps {l : List ι} {δ : ι → ℤ} (h : IsMixed (diffSteps l δ)) :
    IsMixed δ := by
  by_contra hδ
  rcases not_isMixed_iff.mp hδ with h1 | h1
  · exact not_isMixed_iff.mpr (Or.inl (nonneg_diffSteps h1 l)) h
  · exact not_isMixed_iff.mpr (Or.inr (nonpos_diffSteps h1 l)) h

omit [DecidableEq ι] in
/-- A strictly mixed vector has `Φ ≥ 1`. -/
theorem one_le_phi {δ : ι → ℤ} (h : IsMixed δ) : 1 ≤ phi δ := by
  obtain ⟨⟨i, hi⟩, ⟨i', hi'⟩⟩ := h
  have hP : δ i' ≤ posSum δ := by
    have := Finset.single_le_sum (f := fun i => max (δ i) 0) (fun i _ => le_max_right _ _)
      (Finset.mem_univ i')
    exact (le_max_left _ _).trans this
  have hQ : -δ i ≤ negSum δ := by
    have := Finset.single_le_sum (f := fun i => max (-δ i) 0) (fun i _ => le_max_right _ _)
      (Finset.mem_univ i)
    exact (le_max_left _ _).trans this
  exact le_min (by linarith) (by linarith)

/-- **Lemma Y, part 4** (research note 31, Lemma Y; research note 32, Section 6, Lemma Y). Let
`ws` be a list of windows of consecutive steps, each with all the letters. If `δ` is strictly
mixed at the end of the last window, then the number `w` of the windows satisfies
`w + 1 ≤ Φ(δ_0)`. -/
theorem length_add_one_le_phi {ws : List (List ι)} (hws : ∀ w ∈ ws, ∀ i, i ∈ w) {δ : ι → ℤ}
    (h : IsMixed (diffSteps ws.flatten δ)) : (ws.length : ℤ) + 1 ≤ phi δ := by
  induction ws generalizing δ with
  | nil => simpa using one_le_phi h
  | cons w ws ih =>
    rw [List.flatten_cons, diffSteps_append] at h
    have h1 := ih (fun w' hw' => hws w' (List.mem_cons_of_mem _ hw')) h
    have h2 := phi_diffSteps_lt
      (isMixed_of_isMixed_diffSteps (l := w) (isMixed_of_isMixed_diffSteps (l := ws.flatten) h))
      (hws w List.mem_cons_self)
    rw [List.length_cons]
    push_cast
    linarith

/-- Lemma Y, part 4, in the form of research note 31: after `Φ(δ_0)` complete windows, `δ` is
not strictly mixed. -/
theorem not_isMixed_of_phi_le {ws : List (List ι)} (hws : ∀ w ∈ ws, ∀ i, i ∈ w) {δ : ι → ℤ}
    (hlen : phi δ ≤ ws.length) : ¬ IsMixed (diffSteps ws.flatten δ) := fun h => by
  have := length_add_one_le_phi hws h
  linarith

end LemmaY

/-! ### The step on the exponents -/

section Exponents

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The exponent vector `e` as an integer vector. -/
def toZ (e : σ →₀ ℕ) : σ → ℤ := fun i => (e i : ℤ)

/-- The step with the letter `j` on an exponent vector: `e_j ← |e| - p`. -/
noncomputable def expStep (p : ℕ) (j : σ) (e : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.update e j (e.degree - p)

omit [Fintype σ] in
theorem expStep_apply_self (p : ℕ) (j : σ) (e : σ →₀ ℕ) : expStep p j e j = e.degree - p := by
  simp [expStep]

omit [Fintype σ] in
theorem expStep_apply_of_ne (p : ℕ) {i j : σ} (h : i ≠ j) (e : σ →₀ ℕ) :
    expStep p j e i = e i := by
  simp [expStep, Finsupp.update_apply, h]

omit [DecidableEq σ] in
theorem degree_eq_sum' (e : σ →₀ ℕ) : e.degree = ∑ i, e i := by
  rw [Finsupp.degree]
  exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by simpa using hi

omit [DecidableEq σ] in
theorem apply_le_degree (e : σ →₀ ℕ) (j : σ) : e j ≤ e.degree := by
  rw [degree_eq_sum']
  exact Finset.single_le_sum (f := fun i => e i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

omit [DecidableEq σ] in
theorem degree_le_degree {e e' : σ →₀ ℕ} (h : e ≤ e') : e.degree ≤ e'.degree := by
  rw [degree_eq_sum', degree_eq_sum']
  exact Finset.sum_le_sum fun i _ => h i

omit [DecidableEq σ] in
theorem toZ_sum (e : σ →₀ ℕ) : ∑ i, toZ e i = (e.degree : ℤ) := by
  rw [degree_eq_sum', Nat.cast_sum]
  rfl

/-- **The difference of two exponents** (research note 31, Section 2). If `|e| ≥ p` and
`|e'| ≥ p`, the step `e_j ← |e| - p` changes the difference `δ = e - e'` by `δ_j ← Σ_i δ_i`. -/
theorem toZ_expStep_sub {p : ℕ} (j : σ) {e e' : σ →₀ ℕ} (he : p ≤ e.degree)
    (he' : p ≤ e'.degree) :
    toZ (expStep p j e) - toZ (expStep p j e') = diffStep j (toZ e - toZ e') := by
  funext i
  by_cases hi : i = j
  · subst hi
    have h1 := toZ_sum e
    have h2 := toZ_sum e'
    simp only [Pi.sub_apply, diffStep, Function.update_self, Finset.sum_sub_distrib, h1, h2]
    simp only [toZ, expStep_apply_self]
    push_cast [he, he']
    ring
  · simp only [Pi.sub_apply, diffStep, Function.update_of_ne hi, toZ, expStep_apply_of_ne p hi]

omit [Fintype σ] [DecidableEq σ] in
theorem toZ_injective : Function.Injective (toZ : (σ →₀ ℕ) → σ → ℤ) := by
  intro e e' h
  ext i
  have := congrFun h i
  simp only [toZ] at this
  exact_mod_cast this

theorem eq_zero_of_diffStep_eq_zero {j : σ} {δ : σ → ℤ} (h : diffStep j δ = 0) : δ = 0 := by
  have hne : ∀ i, i ≠ j → δ i = 0 := fun i hi => by
    have := congrFun h i
    rwa [diffStep, Function.update_of_ne hi] at this
  have hsum : ∑ i, δ i = 0 := by
    have := congrFun h j
    rwa [diffStep, Function.update_self] at this
  rw [Finset.sum_eq_single j (fun i _ hi => hne i hi) (fun h => absurd (Finset.mem_univ j) h)]
    at hsum
  funext i
  by_cases hi : i = j
  · rw [hi, hsum]
    rfl
  · exact hne i hi

/-- The step on the exponents is injective on the vectors with `|e| ≥ p`. -/
theorem expStep_injOn (p : ℕ) (j : σ) :
    Set.InjOn (expStep p j) {e : σ →₀ ℕ | p ≤ e.degree} := by
  intro e he e' he' h
  have h1 := toZ_expStep_sub j (p := p) he he'
  rw [h, sub_self] at h1
  have h2 := eq_zero_of_diffStep_eq_zero h1.symm
  exact toZ_injective (sub_eq_zero.mp h2)

/-- The step on the exponents keeps the componentwise order. -/
theorem expStep_mono (p : ℕ) (j : σ) {e e' : σ →₀ ℕ} (h : e ≤ e') :
    expStep p j e ≤ expStep p j e' := by
  intro i
  by_cases hi : i = j
  · subst hi
    rw [expStep_apply_self, expStep_apply_self]
    exact Nat.sub_le_sub_right (degree_le_degree h) p
  · rw [expStep_apply_of_ne p hi, expStep_apply_of_ne p hi]
    exact h i

/-- A vector `e` with `|e| ≥ p` that is not in `p ℕ^n` goes to a vector that is not in
`p ℕ^n`. -/
theorem not_dvd_expStep {p : ℕ} (j : σ) {e : σ →₀ ℕ} (hp : p ≤ e.degree)
    (h : ¬ ∀ i, p ∣ e i) : ¬ ∀ i, p ∣ expStep p j e i := by
  intro h'
  apply h
  have hne : ∀ i, i ≠ j → p ∣ e i := fun i hi => by
    have := h' i
    rwa [expStep_apply_of_ne p hi] at this
  have hdeg : p ∣ e.degree := by
    have := h' j
    rw [expStep_apply_self] at this
    have h2 : e.degree = (e.degree - p) + p := (Nat.sub_add_cancel hp).symm
    rw [h2]
    exact Nat.dvd_add this dvd_rfl
  have hsum : e.degree = e j + ∑ i ∈ Finset.univ.erase j, e i := by
    rw [degree_eq_sum']
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  have hrest : p ∣ ∑ i ∈ Finset.univ.erase j, e i :=
    Finset.dvd_sum fun i hi => hne i (Finset.ne_of_mem_erase hi)
  intro i
  by_cases hi : i = j
  · subst hi
    rw [hsum] at hdeg
    exact (Nat.dvd_add_left hrest).mp hdeg
  · exact hne i hi

/-- The steps with the letters of the list `l` on an exponent vector. -/
noncomputable def expSteps (p : ℕ) (l : List σ) (e : σ →₀ ℕ) : σ →₀ ℕ :=
  l.foldl (fun e j => expStep p j e) e

/-- Each step of the list `l` starts from a vector `e` with `|e| ≥ p`. -/
def ExpAdmissible (p : ℕ) : List σ → (σ →₀ ℕ) → Prop
  | [], _ => True
  | j :: l, e => p ≤ e.degree ∧ ExpAdmissible p l (expStep p j e)

theorem expSteps_mono (p : ℕ) (l : List σ) {e e' : σ →₀ ℕ} (h : e ≤ e') :
    expSteps p l e ≤ expSteps p l e' := by
  induction l generalizing e e' with
  | nil => exact h
  | cons j l ih => exact ih (expStep_mono p j h)

/-- The difference of two exponents along a list of steps follows `diffSteps`. -/
theorem toZ_expSteps_sub {p : ℕ} {l : List σ} {e e' : σ →₀ ℕ} (he : ExpAdmissible p l e)
    (he' : ExpAdmissible p l e') :
    toZ (expSteps p l e) - toZ (expSteps p l e') = diffSteps l (toZ e - toZ e') := by
  induction l generalizing e e' with
  | nil => rfl
  | cons j l ih =>
    rw [diffSteps_cons, ← toZ_expStep_sub j he.1 he'.1]
    exact ih he.2 he'.2

omit [DecidableEq σ] in
/-- Two exponents whose difference is not strictly mixed are comparable. -/
theorem le_or_le_of_not_isMixed {e e' : σ →₀ ℕ} (h : ¬ IsMixed (toZ e - toZ e')) :
    e' ≤ e ∨ e ≤ e' := by
  rcases not_isMixed_iff.mp h with h1 | h1
  · left
    intro i
    have := h1 i
    simp only [Pi.sub_apply, toZ] at this
    omega
  · right
    intro i
    have := h1 i
    simp only [Pi.sub_apply, toZ] at this
    omega

end Exponents

/-! ### The step on the polynomials -/

section Polynomials

variable {σ k : Type*} [Fintype σ] [DecidableEq σ] [Field k]

/-- The origin of the `x_j`-chart on the monomial `x^e`: the exponent of `x_j` becomes `|e|`. -/
theorem pointChart_monomial_one (j : σ) (e : σ →₀ ℕ) :
    pointChart j (0 : σ → k) (monomial e (1 : k)) =
      monomial (e + single j (e.degree - e j)) 1 := by
  induction e using Finsupp.induction with
  | zero => simp
  | single_add i n e _ _ ih =>
    have hm : (monomial (single i n + e) (1 : k)) = X i ^ n * monomial e 1 := by
      rw [X_pow_eq_monomial, monomial_mul_monomial, one_mul]
    have hej := apply_le_degree e j
    rw [hm, map_mul, map_pow, ih]
    by_cases hij : i = j
    · subst hij
      rw [pointChart_X_self, X_pow_eq_monomial, monomial_mul_monomial, one_mul]
      refine congrArg (fun s => monomial s (1 : k)) ?_
      ext l
      simp only [Finsupp.coe_add, Pi.add_apply, map_add, Finsupp.degree_single,
        Finsupp.single_apply]
      split_ifs <;> omega
    · rw [pointChart_X_of_ne _ hij, Pi.zero_apply, map_zero, add_zero, mul_pow, X_pow_eq_monomial,
        X_pow_eq_monomial, monomial_mul_monomial, monomial_mul_monomial]
      simp only [one_mul]
      refine congrArg (fun s => monomial s (1 : k)) ?_
      ext l
      simp only [Finsupp.coe_add, Pi.add_apply, map_add, Finsupp.degree_single,
        Finsupp.single_apply]
      split_ifs <;> omega

/-- If `|e| ≥ p`, the origin of the `x_j`-chart sends `c x^e` to `x_j^p c x^e'`, with
`e' = expStep p j e`. -/
theorem pointChart_monomial (p : ℕ) (j : σ) {e : σ →₀ ℕ} (he : p ≤ e.degree) (c : k) :
    pointChart j (0 : σ → k) (monomial e c) = X j ^ p * monomial (expStep p j e) c := by
  have h1 : monomial e c = C c * monomial e (1 : k) := by
    rw [C_mul_monomial, mul_one]
  have hej := apply_le_degree e j
  rw [h1, map_mul, pointChart_monomial_one, X_pow_eq_monomial, monomial_mul_monomial, one_mul]
  have hC : pointChart j (0 : σ → k) (C c) = C c := by
    simp [pointChart]
  rw [hC, C_mul_monomial, mul_one]
  refine congrArg (fun s => monomial s c) ?_
  ext l
  by_cases hl : l = j
  · subst hl
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, expStep_apply_self]
    omega
  · simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, Ne.symm hl, ↓reduceIte,
      expStep_apply_of_ne p hl, zero_add, add_zero]

/-- The new polynomial at the origin of the `x_j`-chart: the image of `g` with the exponents
`expStep p j e`. -/
noncomputable def originTransform (p : ℕ) (j : σ) (g : MvPolynomial σ k) : MvPolynomial σ k :=
  ∑ e ∈ g.support, monomial (expStep p j e) (g.coeff e)

/-- Each monomial of `g` has the degree at least `p`. -/
def DegreeGe (p : ℕ) (g : MvPolynomial σ k) : Prop := ∀ e ∈ g.support, p ≤ e.degree

omit [Fintype σ] [DecidableEq σ] in
theorem degreeGe_of_le_ord {p : ℕ} {g : MvPolynomial σ k} (h : (p : ℕ∞) ≤ ord g) :
    DegreeGe p g := by
  intro e he
  by_contra hlt
  exact (MvPolynomial.mem_support_iff.mp he) (le_ord_iff.mp h e (by exact_mod_cast lt_of_not_ge hlt))

omit [Fintype σ] [DecidableEq σ] in
theorem le_ord_of_degreeGe {p : ℕ} {g : MvPolynomial σ k} (h : DegreeGe p g) :
    (p : ℕ∞) ≤ ord g := by
  refine le_ord_iff.mpr fun d hd => ?_
  by_contra hc
  have := h d (MvPolynomial.mem_support_iff.mpr hc)
  have hd' : d.degree < p := by exact_mod_cast hd
  omega

/-- **The step of an origin run** (research note 31, Section 2). If each monomial of `g` has
the degree at least `p`, the origin of the `x_j`-chart sends `g` to `x_j^p g'` with
`g' = originTransform p j g`. -/
theorem pointChart_eq_X_pow_mul_originTransform {p : ℕ} (j : σ) {g : MvPolynomial σ k}
    (h : DegreeGe p g) : pointChart j (0 : σ → k) g = X j ^ p * originTransform p j g := by
  conv_lhs => rw [g.as_sum]
  rw [map_sum, originTransform, Finset.mul_sum]
  exact Finset.sum_congr rfl fun e he => pointChart_monomial p j (h e he) _

omit [Fintype σ] in
theorem coeff_originTransform (p : ℕ) (j : σ) (g : MvPolynomial σ k) (d : σ →₀ ℕ) :
    (originTransform p j g).coeff d =
      ∑ e ∈ g.support, if expStep p j e = d then g.coeff e else 0 := by
  rw [originTransform, coeff_sum]
  exact Finset.sum_congr rfl fun e _ => coeff_monomial _ _ _

/-- No two monomials cancel: the coefficient of `x^e'` in `g'` is the coefficient of `x^e` in
`g`. -/
theorem coeff_originTransform_expStep {p : ℕ} (j : σ) {g : MvPolynomial σ k}
    (h : DegreeGe p g) {e : σ →₀ ℕ} (he : p ≤ e.degree) :
    (originTransform p j g).coeff (expStep p j e) = g.coeff e := by
  rw [coeff_originTransform, Finset.sum_eq_single e]
  · simp
  · intro e' he' hne
    exact ite_eq_right_iff.mpr fun heq => absurd (expStep_injOn p j (h e' he') he heq) hne
  · intro hne
    simpa using MvPolynomial.notMem_support_iff.mp hne

/-- The support of `g'` is the image of the support of `g` under the step on the exponents. -/
theorem support_originTransform {p : ℕ} (j : σ) {g : MvPolynomial σ k} (h : DegreeGe p g) :
    (originTransform p j g).support = g.support.image (expStep p j) := by
  ext d
  rw [Finset.mem_image]
  constructor
  · intro hd
    by_contra hne
    push Not at hne
    apply MvPolynomial.mem_support_iff.mp hd
    rw [coeff_originTransform]
    exact Finset.sum_eq_zero fun e he => ite_eq_right_iff.mpr fun heq => absurd heq (hne e he)
  · rintro ⟨e, he, rfl⟩
    rw [MvPolynomial.mem_support_iff, coeff_originTransform_expStep j h (h e he)]
    exact MvPolynomial.mem_support_iff.mp he

/-- **No cleaning is necessary** (research note 32, Section 6). If `g` is clean, then `g'` is
clean. -/
theorem isClean_originTransform {p : ℕ} (j : σ) {g : MvPolynomial σ k} (h : DegreeGe p g)
    (hc : IsClean p g) : IsClean p (originTransform p j g) := by
  intro d hd
  rw [support_originTransform j h, Finset.mem_image] at hd
  obtain ⟨e, he, rfl⟩ := hd
  exact not_dvd_expStep j (h e he) (hc e he)

theorem originTransform_ne_zero {p : ℕ} (j : σ) {g : MvPolynomial σ k} (h : DegreeGe p g)
    (hg : g ≠ 0) : originTransform p j g ≠ 0 := by
  intro h0
  have hs := support_originTransform j h
  rw [h0, MvPolynomial.support_zero] at hs
  exact hg (MvPolynomial.support_eq_empty.mp (Finset.image_eq_empty.mp hs.symm))

/-! ### Finite origin runs -/

/-- The polynomial after the origin steps with the letters of the list `l`. -/
noncomputable def polySteps (p : ℕ) (l : List σ) (g : MvPolynomial σ k) : MvPolynomial σ k :=
  l.foldl (fun g j => originTransform p j g) g

omit [Fintype σ] [DecidableEq σ] in
@[simp]
theorem polySteps_nil (p : ℕ) (g : MvPolynomial σ k) : polySteps p [] g = g := rfl

omit [Fintype σ] [DecidableEq σ] in
@[simp]
theorem polySteps_cons (p : ℕ) (j : σ) (l : List σ) (g : MvPolynomial σ k) :
    polySteps p (j :: l) g = polySteps p l (originTransform p j g) := rfl

omit [Fintype σ] [DecidableEq σ] in
theorem polySteps_append (p : ℕ) (l₁ l₂ : List σ) (g : MvPolynomial σ k) :
    polySteps p (l₁ ++ l₂) g = polySteps p l₂ (polySteps p l₁ g) := by
  simp only [polySteps, List.foldl_append]

/-- Each step of the list `l` is defined: before each step, each monomial has the degree at
least `p`, that is, the order is at least `p` (`degreeGe_of_le_ord`, `le_ord_of_degreeGe`). -/
def IsAdmissible (p : ℕ) : List σ → MvPolynomial σ k → Prop
  | [], _ => True
  | j :: l, g => DegreeGe p g ∧ IsAdmissible p l (originTransform p j g)

omit [Fintype σ] [DecidableEq σ] in
theorem isAdmissible_append {p : ℕ} {l₁ l₂ : List σ} {g : MvPolynomial σ k} :
    IsAdmissible p (l₁ ++ l₂) g ↔
      IsAdmissible p l₁ g ∧ IsAdmissible p l₂ (polySteps p l₁ g) := by
  induction l₁ generalizing g with
  | nil => simp [IsAdmissible]
  | cons j l ih =>
    simp only [List.cons_append, IsAdmissible, polySteps_cons, ih, and_assoc]

/-- The support after the steps of `l` is the image of the support of `g`. -/
theorem support_polySteps {p : ℕ} {l : List σ} {g : MvPolynomial σ k}
    (h : IsAdmissible p l g) :
    (polySteps p l g).support = g.support.image (expSteps p l) ∧
      ∀ e ∈ g.support, ExpAdmissible p l e := by
  induction l generalizing g with
  | nil => exact ⟨by rw [show expSteps p [] = id from rfl, Finset.image_id]; rfl,
      fun _ _ => trivial⟩
  | cons j l ih =>
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := ih h2
    refine ⟨?_, fun e he => ⟨h1 e he, ih2 _ ?_⟩⟩
    · rw [polySteps_cons, ih1, support_originTransform j h1, Finset.image_image]
      rfl
    · rw [support_originTransform j h1]
      exact Finset.mem_image_of_mem _ he

theorem isClean_polySteps {p : ℕ} {l : List σ} {g : MvPolynomial σ k}
    (h : IsAdmissible p l g) (hc : IsClean p g) : IsClean p (polySteps p l g) := by
  induction l generalizing g with
  | nil => exact hc
  | cons j l ih => exact ih h.2 (isClean_originTransform j h.1 hc)

theorem polySteps_ne_zero {p : ℕ} {l : List σ} {g : MvPolynomial σ k}
    (h : IsAdmissible p l g) (hg : g ≠ 0) : polySteps p l g ≠ 0 := by
  induction l generalizing g with
  | nil => exact hg
  | cons j l ih => exact ih h.2 (originTransform_ne_zero j h.1 hg)

/-! ### Theorem A -/

/-- The polynomial `g` has a least exponent for the componentwise order. If `Δ` contains all
the coordinates, then `G` is a unit (`constantCoeff_residualFactor_ne_zero`). -/
def HasLeastExponent (g : MvPolynomial σ k) : Prop :=
  ∃ b ∈ g.support, ∀ d ∈ g.support, b ≤ d

/-- The set `V` of the minimal exponents of `g` for the componentwise order. -/
noncomputable def minimalSupport (g : MvPolynomial σ k) : Finset (σ →₀ ℕ) :=
  open Classical in g.support.filter fun e => ∀ e' ∈ g.support, e' ≤ e → e' = e

/-- The bound `W` of Theorem A: the largest value of `Φ(e - e') - 1` for two minimal exponents
`e, e'` of `g`, or `0`. A pair that is not strictly mixed gives `0`. -/
noncomputable def windowBound (g : MvPolynomial σ k) : ℕ :=
  (minimalSupport g ×ˢ minimalSupport g).sup fun x => (phi (toZ x.1 - toZ x.2)).toNat - 1

theorem le_windowBound {g : MvPolynomial σ k} {v v' : σ →₀ ℕ} (hv : v ∈ minimalSupport g)
    (hv' : v' ∈ minimalSupport g) : (phi (toZ v - toZ v')).toNat - 1 ≤ windowBound g := by
  have hmem : ((v, v') : (σ →₀ ℕ) × (σ →₀ ℕ)) ∈ minimalSupport g ×ˢ minimalSupport g :=
    Finset.mem_product.mpr ⟨hv, hv'⟩
  have := Finset.le_sup
    (f := fun x : (σ →₀ ℕ) × (σ →₀ ℕ) => (phi (toZ x.1 - toZ x.2)).toNat - 1) hmem
  simp only at this
  exact this

/-- In a finite set, each element is above a minimal element. -/
theorem exists_minimal_le {s : Finset (σ →₀ ℕ)} {e : σ →₀ ℕ} (he : e ∈ s) :
    ∃ v ∈ s, v ≤ e ∧ ∀ v' ∈ s, v' ≤ v → v' = v := by
  induction hn : e.degree using Nat.strong_induction_on generalizing e with
  | _ n ih =>
    by_cases hmin : ∀ v' ∈ s, v' ≤ e → v' = e
    · exact ⟨e, he, le_rfl, hmin⟩
    · push Not at hmin
      obtain ⟨v', hv', hle, hne⟩ := hmin
      have hlt : v'.degree < e.degree := by
        rw [degree_eq_sum', degree_eq_sum']
        have hex : ∃ i, v' i < e i := by
          by_contra hall
          push Not at hall
          exact hne (le_antisymm hle hall)
        obtain ⟨i, hi⟩ := hex
        exact Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hi⟩
      obtain ⟨v, hv, hvle, hvmin⟩ := ih _ (hn ▸ hlt) hv' rfl
      exact ⟨v, hv, hvle.trans hle, hvmin⟩

omit [Fintype σ] in
theorem mem_minimalSupport {g : MvPolynomial σ k} {e : σ →₀ ℕ} :
    e ∈ minimalSupport g ↔ e ∈ g.support ∧ ∀ e' ∈ g.support, e' ≤ e → e' = e := by
  classical
  rw [minimalSupport]
  convert Finset.mem_filter

/-- Each exponent of `g` is above a minimal exponent. -/
theorem exists_mem_minimalSupport_le {g : MvPolynomial σ k} {e : σ →₀ ℕ}
    (he : e ∈ g.support) : ∃ v ∈ minimalSupport g, v ≤ e := by
  obtain ⟨v, hv, hle, hmin⟩ := exists_minimal_le he
  exact ⟨v, mem_minimalSupport.mpr ⟨hv, hmin⟩, hle⟩

/-- A finite nonempty set of exponents where each two elements are comparable has a least
element. -/
theorem exists_least_of_pairwise {s : Finset (σ →₀ ℕ)} (hs : s.Nonempty)
    (h : ∀ a ∈ s, ∀ b ∈ s, a ≤ b ∨ b ≤ a) : ∃ b ∈ s, ∀ a ∈ s, b ≤ a := by
  obtain ⟨e, he⟩ := hs
  obtain ⟨v, hv, -, hmin⟩ := exists_minimal_le he
  refine ⟨v, hv, fun a ha => ?_⟩
  rcases h v hv a ha with h1 | h1
  · exact h1
  · exact (hmin a ha h1).ge

/-- **Theorem A, part 1, on the exponents** (research note 31, Theorem 1, part 1). Once `g` has
a least exponent, it keeps one along the origin steps. -/
theorem hasLeastExponent_polySteps {p : ℕ} {l : List σ} {g : MvPolynomial σ k}
    (h : IsAdmissible p l g) (hb : HasLeastExponent g) :
    HasLeastExponent (polySteps p l g) := by
  obtain ⟨b, hb, hle⟩ := hb
  refine ⟨expSteps p l b, ?_, fun d hd => ?_⟩
  · rw [(support_polySteps h).1]
    exact Finset.mem_image_of_mem _ hb
  · rw [(support_polySteps h).1, Finset.mem_image] at hd
    obtain ⟨e, he, rfl⟩ := hd
    exact expSteps_mono p l (hle e he)

/-- **Theorem A, part 2, on the exponents** (research note 31, Theorem 1, part 2). Let `ws` be
a list of windows of origin steps, each with all the letters, with more than `W(g)` windows.
Then `g` has a least exponent at the end of the last window. -/
theorem exists_least_polySteps {p : ℕ} {g : MvPolynomial σ k} (hg : g ≠ 0)
    {ws : List (List σ)} (hws : ∀ w ∈ ws, ∀ i, i ∈ w) (hlen : windowBound g < ws.length)
    (h : IsAdmissible p ws.flatten g) : HasLeastExponent (polySteps p ws.flatten g) := by
  obtain ⟨hsupp, hadm⟩ := support_polySteps h
  have hcomp : ∀ v ∈ minimalSupport g, ∀ v' ∈ minimalSupport g,
      expSteps p ws.flatten v' ≤ expSteps p ws.flatten v ∨
        expSteps p ws.flatten v ≤ expSteps p ws.flatten v' := by
    intro v hv v' hv'
    refine le_or_le_of_not_isMixed fun hmix => ?_
    have hv0 := (mem_minimalSupport.mp hv).1
    have hv0' := (mem_minimalSupport.mp hv').1
    rw [toZ_expSteps_sub (hadm v hv0) (hadm v' hv0')] at hmix
    have h1 := length_add_one_le_phi hws hmix
    have h2 := le_windowBound hv hv'
    have h3 := one_le_phi (isMixed_of_isMixed_diffSteps hmix)
    have h4 : ((phi (toZ v - toZ v')).toNat : ℤ) = phi (toZ v - toZ v') :=
      Int.toNat_of_nonneg (by linarith)
    generalize (phi (toZ v - toZ v')).toNat = q' at h2 h4
    generalize phi (toZ v - toZ v') = q at h1 h3 h4
    generalize windowBound g = W at h2 hlen
    generalize ws.length = L at h1 hlen
    omega
  obtain ⟨e0, he0⟩ := MvPolynomial.support_nonempty.mpr hg
  obtain ⟨v0, hv0, -⟩ := exists_mem_minimalSupport_le he0
  obtain ⟨b, hb, hbmin⟩ := exists_least_of_pairwise
    (s := (minimalSupport g).image (expSteps p ws.flatten)) ⟨_, Finset.mem_image_of_mem _ hv0⟩
    (by
      intro a ha c hc
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hc
      exact (hcomp v hv v' hv').symm)
  obtain ⟨vb, hvb, rfl⟩ := Finset.mem_image.mp hb
  refine ⟨expSteps p ws.flatten vb, ?_, fun d hd => ?_⟩
  · rw [hsupp]
    exact Finset.mem_image_of_mem _ (mem_minimalSupport.mp hvb).1
  · rw [hsupp, Finset.mem_image] at hd
    obtain ⟨e, he, rfl⟩ := hd
    obtain ⟨v, hv, hle⟩ := exists_mem_minimalSupport_le he
    exact (hbmin _ (Finset.mem_image_of_mem _ hv)).trans (expSteps_mono p ws.flatten hle)

/-- If `Δ` contains all the coordinates and `b` is a least exponent of `g`, then `r = b`. -/
theorem divisorExponent_univ_eq {g : MvPolynomial σ k} {b : σ →₀ ℕ} (hb : b ∈ g.support)
    (hle : ∀ d ∈ g.support, b ≤ d) : divisorExponent Finset.univ g = b := by
  ext i
  simp only [divisorExponent_apply, Finset.mem_univ, ↓reduceIte]
  have hmem : b i ∈ (fun d : σ →₀ ℕ => d i) '' (g.support : Set (σ →₀ ℕ)) :=
    ⟨b, Finset.mem_coe.mpr hb, rfl⟩
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ ?_)
  rintro _ ⟨d, hd, rfl⟩
  exact hle d (Finset.mem_coe.mp hd) i

/-- If `Δ` contains all the coordinates and `g` has a least exponent, then `G` is a unit: its
constant term is not `0`. -/
theorem constantCoeff_residualFactor_ne_zero {g : MvPolynomial σ k} (h : HasLeastExponent g) :
    constantCoeff (residualFactor Finset.univ g) ≠ 0 := by
  obtain ⟨b, hb, hle⟩ := h
  rw [residualFactor, divisorExponent_univ_eq hb hle, constantCoeff_eq, coeff_divMonomial,
    add_zero]
  exact MvPolynomial.mem_support_iff.mp hb

/-- If `Δ` contains all the coordinates and `g` has a least exponent, then `G` has the order
`0`. -/
theorem ord_residualFactor_eq_zero {g : MvPolynomial σ k} (h : HasLeastExponent g) :
    ord (residualFactor Finset.univ g) = 0 := by
  have h0 := constantCoeff_residualFactor_ne_zero h
  rw [constantCoeff_eq] at h0
  have := ord_le h0
  rw [map_zero, Nat.cast_zero] at this
  exact nonpos_iff_eq_zero.mp this

/-- **`G` is a unit, so `ρ = 0`** (research note 31, Theorem 1, part 1). Let `Δ` contain all
the coordinates, and let `g` be clean with a least exponent `r`. Then some `r_i` is not `0`
mod `p`, and the generator `r_i G + x_i ∂_i G` of `J` has the order `0`. -/
theorem logJacobianOrder_eq_zero {p : ℕ} [CharP k p] {g : MvPolynomial σ k} (hc : IsClean p g)
    (h : HasLeastExponent g) : logJacobianOrder Finset.univ g = 0 := by
  obtain ⟨b, hb, hle⟩ := h
  have hG := constantCoeff_residualFactor_ne_zero ⟨b, hb, hle⟩
  have hr := divisorExponent_univ_eq hb hle
  obtain ⟨i, hi⟩ : ∃ i, ¬ p ∣ b i := by
    by_contra hall
    push Not at hall
    exact hc b hb hall
  have hik : ((b i : ℕ) : k) ≠ 0 := fun h0 => hi ((CharP.cast_eq_zero_iff k p (b i)).mp h0)
  have hmem := smul_add_X_mul_pderiv_mem_residualLogJacobian (Finset.mem_univ i)
    (divisorExponent Finset.univ g) (residualFactor Finset.univ g)
  rw [hr] at hmem
  have hcoeff : (((b i : ℕ) : k) • residualFactor Finset.univ g +
      X i * pderiv i (residualFactor Finset.univ g)).coeff 0 ≠ 0 := by
    have hadd : ∀ a c : MvPolynomial σ k, (a + c).coeff 0 = a.coeff 0 + c.coeff 0 :=
      fun a c => by simp
    rw [hadd, coeff_smul, coeff_X_mul']
    simp only [Finsupp.support_zero, Finset.notMem_empty, ↓reduceIte, add_zero, smul_eq_mul,
      ← constantCoeff_eq]
    exact mul_ne_zero hik hG
  have h1 := (idealOrd_le_ord hmem).trans (ord_le hcoeff)
  rw [map_zero, Nat.cast_zero] at h1
  rw [logJacobianOrder, hr]
  exact nonpos_iff_eq_zero.mp h1

/-- **Theorem A, part 2** (research note 31, Theorem 1, part 2; research note 32, Section 6,
Theorem A). Let `g` be clean and not `0`, and let `Δ` contain all the coordinates. Let `ws` be a
list of more than `W(g)` windows of origin steps, each with all the `n` letters, where each step
is defined. Then at the end of the last window, `G` is a unit and `ρ = 0`. -/
theorem originRun_unit_of_windows {p : ℕ} [CharP k p] {g : MvPolynomial σ k} (hg : g ≠ 0)
    (hc : IsClean p g) {ws : List (List σ)} (hws : ∀ w ∈ ws, ∀ i, i ∈ w)
    (hlen : windowBound g < ws.length) (h : IsAdmissible p ws.flatten g) :
    ord (residualFactor Finset.univ (polySteps p ws.flatten g)) = 0 ∧
      logJacobianOrder Finset.univ (polySteps p ws.flatten g) = 0 := by
  have hl := exists_least_polySteps hg hws hlen h
  exact ⟨ord_residualFactor_eq_zero hl, logJacobianOrder_eq_zero (isClean_polySteps h hc) hl⟩

/-- **Theorem A, part 1** (research note 31, Theorem 1, part 1; research note 32, Section 6,
Theorem A). Let `Δ` contain all the coordinates. Once `G` is a unit at a clean point, `G` stays
a unit and `ρ = 0` at each later point of the origin run. -/
theorem originRun_unit_stays {p : ℕ} [CharP k p] {g : MvPolynomial σ k} (hc : IsClean p g)
    (hb : HasLeastExponent g) {l : List σ} (h : IsAdmissible p l g) :
    ord (residualFactor Finset.univ (polySteps p l g)) = 0 ∧
      logJacobianOrder Finset.univ (polySteps p l g) = 0 := by
  have hl := hasLeastExponent_polySteps h hb
  exact ⟨ord_residualFactor_eq_zero hl, logJacobianOrder_eq_zero (isClean_polySteps h hc) hl⟩

/-! ### Infinite origin runs -/

/-- The polynomial at the point `P_m` of the origin run from `g` with the letters `w`. -/
noncomputable def runPoly (p : ℕ) (w : ℕ → σ) (g : MvPolynomial σ k) : ℕ → MvPolynomial σ k
  | 0 => g
  | m + 1 => originTransform p (w m) (runPoly p w g m)

/-- The divisor at the point `P_m` of the origin run from `Δ` with the letters `w`. -/
def runDivisor (w : ℕ → σ) (Δ : Finset σ) : ℕ → Finset σ
  | 0 => Δ
  | m + 1 => insert (w m) (runDivisor w Δ m)

/-- The letters `w a, w (a + 1), ..., w (a + n - 1)`. -/
def runList (w : ℕ → σ) (a n : ℕ) : List σ := (List.range n).map fun i => w (a + i)

omit [Fintype σ] [DecidableEq σ] in
theorem runList_succ (w : ℕ → σ) (a n : ℕ) :
    runList w a (n + 1) = runList w a n ++ [w (a + n)] := by
  simp [runList, List.range_succ]

omit [Fintype σ] [DecidableEq σ] in
theorem runList_add (w : ℕ → σ) (a n n' : ℕ) :
    runList w a (n + n') = runList w a n ++ runList w (a + n) n' := by
  induction n' with
  | zero => simp [runList]
  | succ n' ih =>
    rw [← add_assoc, runList_succ, ih, runList_succ, List.append_assoc, add_assoc]

omit [Fintype σ] [DecidableEq σ] in
theorem runPoly_add (p : ℕ) (w : ℕ → σ) (g : MvPolynomial σ k) (a n : ℕ) :
    runPoly p w g (a + n) = polySteps p (runList w a n) (runPoly p w g a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runList_succ, polySteps_append, ← ih, ← add_assoc]
    rfl

omit [Fintype σ] [DecidableEq σ] in
theorem isAdmissible_runList {p : ℕ} {w : ℕ → σ} {g : MvPolynomial σ k}
    (hadm : ∀ m, DegreeGe p (runPoly p w g m)) (a n : ℕ) :
    IsAdmissible p (runList w a n) (runPoly p w g a) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rw [runList_succ, isAdmissible_append]
    refine ⟨ih, ?_, trivial⟩
    rw [← runPoly_add]
    exact hadm _

theorem isClean_runPoly {p : ℕ} {w : ℕ → σ} {g : MvPolynomial σ k}
    (hadm : ∀ m, DegreeGe p (runPoly p w g m)) (hc : IsClean p g) (m : ℕ) :
    IsClean p (runPoly p w g m) := by
  induction m with
  | zero => exact hc
  | succ m ih => exact isClean_originTransform _ (hadm m) ih

theorem runPoly_ne_zero {p : ℕ} {w : ℕ → σ} {g : MvPolynomial σ k}
    (hadm : ∀ m, DegreeGe p (runPoly p w g m)) (hg : g ≠ 0) (m : ℕ) :
    runPoly p w g m ≠ 0 := by
  induction m with
  | zero => exact hg
  | succ m ih => exact originTransform_ne_zero _ (hadm m) ih

omit [Fintype σ] in
theorem runDivisor_mono (w : ℕ → σ) (Δ : Finset σ) {m m' : ℕ} (h : m ≤ m') :
    runDivisor w Δ m ⊆ runDivisor w Δ m' := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans (Finset.subset_insert _ _)

omit [Fintype σ] in
theorem mem_runDivisor (w : ℕ → σ) (Δ : Finset σ) {m n : ℕ} (h : m < n) :
    w m ∈ runDivisor w Δ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h1 | h1
    · exact Finset.mem_insert_of_mem (ih h1)
    · subst h1
      exact Finset.mem_insert_self _ _

omit [DecidableEq σ] in
/-- If each letter occurs an infinite number of times, then the run from `a` on contains a
window with all the letters. -/
theorem exists_window {w : ℕ → σ} (hinf : ∀ i N, ∃ m, N ≤ m ∧ w m = i) (a : ℕ) :
    ∃ n, ∀ i, i ∈ runList w a n := by
  choose f hf using fun i => hinf i a
  refine ⟨Finset.univ.sup (fun i => f i - a) + 1, fun i => ?_⟩
  rw [runList, List.mem_map]
  refine ⟨f i - a, List.mem_range.mpr ?_, ?_⟩
  · have := Finset.le_sup (f := fun i => f i - a) (Finset.mem_univ i)
    omega
  · rw [Nat.add_sub_cancel' (hf i).1, (hf i).2]

omit [DecidableEq σ] in
/-- If each letter occurs an infinite number of times, then the run from `a` on contains `c`
consecutive windows, each with all the letters. -/
theorem exists_windows {w : ℕ → σ} (hinf : ∀ i N, ∃ m, N ≤ m ∧ w m = i) (c a : ℕ) :
    ∃ (ws : List (List σ)) (n : ℕ), ws.length = c ∧ (∀ v ∈ ws, ∀ i, i ∈ v) ∧
      ws.flatten = runList w a n := by
  induction c generalizing a with
  | zero => exact ⟨[], 0, rfl, by simp, rfl⟩
  | succ c ih =>
    obtain ⟨n₀, hn₀⟩ := exists_window hinf a
    obtain ⟨ws, n, hlen, hws, hflat⟩ := ih (a + n₀)
    refine ⟨runList w a n₀ :: ws, n₀ + n, by simp [hlen], ?_, ?_⟩
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hn₀
      · exact hws v hv
    · rw [List.flatten_cons, hflat, runList_add]

/-- **Theorem A, part 3** (research note 31, Theorem 1, part 3; research note 32, Section 6,
Theorem A). Let `g` be clean and not `0`, and let `w` be the letters of an origin run from
`(Δ, g)` where each step is defined. If each of the `n` letters occurs an infinite number of
times, then at some point of the run `Δ` contains all the coordinates, `G` is a unit and
`ρ = 0`. -/
theorem originRun_exists_logJacobianOrder_eq_zero {p : ℕ} [CharP k p] {w : ℕ → σ}
    {g : MvPolynomial σ k} (Δ : Finset σ) (hg : g ≠ 0) (hc : IsClean p g)
    (hadm : ∀ m, DegreeGe p (runPoly p w g m)) (hinf : ∀ i N, ∃ m, N ≤ m ∧ w m = i) :
    ∃ m, runDivisor w Δ m = Finset.univ ∧
      ord (residualFactor Finset.univ (runPoly p w g m)) = 0 ∧
      logJacobianOrder (runDivisor w Δ m) (runPoly p w g m) = 0 := by
  obtain ⟨M, hM⟩ := exists_window hinf 0
  have hΔ : ∀ m, M ≤ m → runDivisor w Δ m = Finset.univ := by
    intro m hm
    refine Finset.eq_univ_of_forall fun i => runDivisor_mono w Δ hm ?_
    obtain ⟨j, hj, hji⟩ := List.mem_map.mp (hM i)
    rw [← hji, zero_add]
    exact mem_runDivisor w Δ (List.mem_range.mp hj)
  obtain ⟨ws, n, hlen, hws, hflat⟩ :=
    exists_windows hinf (windowBound (runPoly p w g M) + 1) M
  have hadm' : IsAdmissible p ws.flatten (runPoly p w g M) := by
    rw [hflat]
    exact isAdmissible_runList hadm M n
  have h := originRun_unit_of_windows (runPoly_ne_zero hadm hg M) (isClean_runPoly hadm hc M)
    hws (by omega) hadm'
  rw [hflat, ← runPoly_add] at h
  refine ⟨M + n, hΔ _ (Nat.le_add_right M n), h.1, ?_⟩
  rw [hΔ _ (Nat.le_add_right M n)]
  exact h.2

/-- **Theorem A, part 3** (research note 31, Theorem 1, part 3). An origin run with `ρ ≥ 1` at
each point, where each step is defined, does not use each of the `n` letters an infinite number
of times. -/
theorem originRun_not_forall_one_le {p : ℕ} [CharP k p] {w : ℕ → σ} {g : MvPolynomial σ k}
    (Δ : Finset σ) (hg : g ≠ 0) (hc : IsClean p g) (hadm : ∀ m, DegreeGe p (runPoly p w g m))
    (hρ : ∀ m, 1 ≤ logJacobianOrder (runDivisor w Δ m) (runPoly p w g m)) :
    ¬ ∀ i N, ∃ m, N ≤ m ∧ w m = i := by
  intro hinf
  obtain ⟨m, -, -, h0⟩ := originRun_exists_logJacobianOrder_eq_zero Δ hg hc hadm hinf
  have := hρ m
  rw [h0] at this
  exact absurd this (by norm_num)

variable [DecidableEq k]

omit [Fintype σ] in
/-- At the origin of the chart, the new divisor is `Δ ∪ {j}`. -/
theorem blowupDivisor_zero (Δ : Finset σ) (j : σ) :
    blowupDivisor Δ j (0 : σ → k) = insert j Δ := by
  ext i
  by_cases hi : i = j
  · simp [blowupDivisor, hi]
  · simp [blowupDivisor, hi]

/-- **The step of an origin run is a blowup step** (research note 31, Section 2; research
note 32, Section 6). Let `g` be clean with each monomial of the degree at least `p`. The origin
of the `x_j`-chart sends `g` to `x_j^p g'`, and the new point is `(Δ ∪ {j}, g')` with no
cleaning. -/
theorem originStep (p : ℕ) (Δ : Finset σ) (j : σ) {g : MvPolynomial σ k} (h : DegreeGe p g)
    (hc : IsClean p g) :
    pointChart j (0 : σ → k) g = X j ^ p * originTransform p j g ∧
      ((insert j Δ, originTransform p j g) : Finset σ × MvPolynomial σ k) =
        (blowupDivisor Δ j (0 : σ → k), cleanPart p (originTransform p j g)) := by
  refine ⟨pointChart_eq_X_pow_mul_originTransform j h, ?_⟩
  rw [blowupDivisor_zero, cleanPart_eq_self (isClean_originTransform j h hc)]

/-- An origin step where `ρ = m` at both points is a `RhoStep`. -/
theorem rhoStep_originStep {p m : ℕ} [CharP k p] {Δ : Finset σ} {j : σ}
    {g : MvPolynomial σ k} (hg : g ≠ 0) (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g)
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (insert j Δ) (originTransform p j g) = m) :
    RhoStep p m (Δ, g) (insert j Δ, originTransform p j g) := by
  obtain ⟨h1, h2⟩ := originStep p Δ j (degreeGe_of_le_ord hord) hc
  exact ⟨j, 0, originTransform p j g, hg, hc, hord, h1, h2, hρ, hρ'⟩

/-- **Each step of an origin run is a blowup step at the origin of a chart**, with no
cleaning. -/
theorem runPoint_step {p : ℕ} {w : ℕ → σ} {g : MvPolynomial σ k} (Δ : Finset σ)
    (hadm : ∀ m, DegreeGe p (runPoly p w g m)) (hc : IsClean p g) (m : ℕ) :
    pointChart (w m) (0 : σ → k) (runPoly p w g m) = X (w m) ^ p * runPoly p w g (m + 1) ∧
      ((runDivisor w Δ (m + 1), runPoly p w g (m + 1)) : Finset σ × MvPolynomial σ k) =
        (blowupDivisor (runDivisor w Δ m) (w m) (0 : σ → k),
          cleanPart p (runPoly p w g (m + 1))) :=
  originStep p _ (w m) (hadm m) (isClean_runPoly hadm hc m)

end Polynomials

end OriginRuns

end Singularity
