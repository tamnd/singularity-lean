/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.NNReal.Basic
import Singularity.Valuation.LocalUniformizationMonomial
import Singularity.Valuation.PerronAlgorithm

/-!
# Monomial charts by blowups

Let `K` be a field, and let `x : ι → K` be nonzero elements. A step `s = (i, j)` of the Perron algorithm (see `Singularity.Valuation.PerronStep`) gives new coordinates: `x_j` becomes `x_j / x_i`, and the other coordinates do not change. This is the chart `x_j = x_i x_j'` of the blowup of `V(x_i, x_j)`. The Laurent monomial `x^D` is the Laurent monomial of the new coordinates with the exponent after the step. So the old coordinates are monomials in the new coordinates with exponents in `ℕ`, and the ring of the new chart contains the ring of the old chart.

Let `V` be a valuation ring of `K`, and let `γ` be a real weight such that `v(x^a) ≤ 1` if and only if `a · γ ≥ 0`. For a strictly monotone homomorphism `φ` from the value group to `ℝ≥0`, the weight `γ_i = -log φ(v(x_i))` has this property. Then the weight after a valid run has the same property for the new coordinates. If `V` is a monomial valuation in `x`, then it is a monomial valuation in the new coordinates.

The main result is the algebraic part of Corollary 2.3.11 of Volume 5 of the handbook. Let `V` be a monomial valuation in `x` with positive weights, and let `s` be a finite subset of `V`. Then there is a valid run such that the new coordinates have value `< 1`, and each `z ∈ s` is a quotient `f / g`, where `f` and `g` are polynomials in the new coordinates and `v(g) = 1`. So `z` lies in the local ring of the chart at the centre of `V`.

## Main definitions

* `Singularity.Perron.stepCoord`: the coordinates after a step.
* `Singularity.Perron.runCoord`: the coordinates after a run.

## Main results

* `Singularity.Perron.laurentMonomial_runCoord_runExp`: a run does not change the Laurent monomials.
* `Singularity.Perron.coord_eq_laurentMonomial_runCoord`: each old coordinate is a monomial in the new coordinates, with exponents in `ℕ`.
* `Singularity.Perron.adjoin_range_le_adjoin_range_runCoord`: the ring of the new chart contains the ring of the old chart.
* `Singularity.Perron.valuation_laurentMonomial_runCoord_le_one_iff`: the weight after a run gives the values of the new coordinates.
* `Singularity.IsMonomialValuation.runCoord`: a monomial valuation stays monomial in the new coordinates.
* `Singularity.Perron.exists_isValidRun_forall_mem_adjoin_runCoord`: a finite subset of `V` lies in the local ring of one chart.
* `Singularity.Perron.exists_isValidRun_forall_mem_adjoin_runCoord_of_rankOne`: the same for the weights `-log φ(v(x_i))`.

## What is not proved

The statement that each step is the blowup of a regular centre of codimension 2 of a scheme is not in Lean. This file only gives the coordinates of the chart, as elements of `K`.

## References

* Volume 5, Section 2.3 of the handbook.
-/

open Finset
open scoped NNReal

namespace Singularity.Perron

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {K : Type*} [Field K]

/-- **The coordinates after a step** (Volume 5, Corollary 2.3.11 of the handbook). For the step `s = (i, j)`, the coordinate `x_j` becomes `x_j / x_i`. This is the chart `x_j = x_i x_j'` of the blowup of `V(x_i, x_j)`. -/
def stepCoord (x : ι → K) (s : ι × ι) : ι → K := Function.update x s.2 (x s.2 / x s.1)

/-- **The coordinates after a run** (Volume 5, Corollary 2.3.11 of the handbook). The steps of the list act on the coordinates in order. -/
def runCoord (x : ι → K) : List (ι × ι) → ι → K
  | [] => x
  | s :: l => runCoord (stepCoord x s) l

omit [Fintype ι] in
/-- **The entries of the new coordinates.** -/
theorem stepCoord_apply (x : ι → K) (s : ι × ι) (l : ι) :
    stepCoord x s l = if l = s.2 then x s.2 / x s.1 else x l := by
  simp [stepCoord, Function.update_apply]

omit [Fintype ι] in
/-- **A step keeps the coordinates nonzero.** -/
theorem stepCoord_ne_zero {x : ι → K} (hx : ∀ i, x i ≠ 0) (s : ι × ι) (i : ι) :
    stepCoord x s i ≠ 0 := by
  rw [stepCoord_apply]
  split_ifs
  · exact div_ne_zero (hx _) (hx _)
  · exact hx i

omit [Fintype ι] in
/-- **A run keeps the coordinates nonzero.** -/
theorem runCoord_ne_zero {x : ι → K} (hx : ∀ i, x i ≠ 0) (l : List (ι × ι)) (i : ι) :
    runCoord x l i ≠ 0 := by
  induction l generalizing x with
  | nil => exact hx i
  | cons s l ih => exact ih (stepCoord_ne_zero hx s)

omit [Fintype ι] in
/-- **A run is surjective on exponents** (Volume 5, Corollary 2.3.11 of the handbook). Each step with distinct indices has an inverse, by `Singularity.Perron.stepExp_update_sub`. -/
theorem runExp_surjective {l : List (ι × ι)} (hl : ∀ s ∈ l, s.1 ≠ s.2) :
    Function.Surjective (runExp l) := by
  induction l with
  | nil => exact fun a => ⟨a, rfl⟩
  | cons s l ih =>
    intro a
    obtain ⟨b, rfl⟩ := ih (fun t ht => hl t (List.mem_cons_of_mem s ht)) a
    refine ⟨Function.update b s.1 (b s.1 - b s.2), ?_⟩
    rw [runExp, stepExp_update_sub (hl s (List.mem_cons.mpr (Or.inl rfl)))]

/-- **A step does not change the Laurent monomials** (Volume 5, Corollary 2.3.11 of the handbook). For the step `s = (i, j)`, we have `x_i^(D_i + D_j) (x_j / x_i)^D_j = x_i^D_i x_j^D_j`. -/
theorem laurentMonomial_stepCoord_stepExp {x : ι → K} (hx : ∀ i, x i ≠ 0) {s : ι × ι}
    (hs : s.1 ≠ s.2) (D : ι → ℤ) :
    laurentMonomial (stepCoord x s) (stepExp s D) = laurentMonomial x D := by
  have h : ∀ l, stepCoord x s l ^ stepExp s D l = x l ^ D l *
      ((if l = s.1 then x s.1 ^ D s.2 else 1) * (if l = s.2 then (x s.1 ^ D s.2)⁻¹ else 1)) := by
    intro l
    rw [stepCoord_apply, stepExp_apply]
    by_cases h1 : l = s.1
    · subst h1
      simp [hs, zpow_add₀ (hx _)]
    · by_cases h2 : l = s.2
      · subst h2
        simp only [h1, div_eq_mul_inv, ite_true, ite_false, one_mul]
        rw [mul_zpow, inv_zpow]
      · simp [h1, h2]
  rw [laurentMonomial, laurentMonomial, prod_congr rfl fun l _ => h l, prod_mul_distrib,
    prod_mul_distrib, prod_ite_eq', prod_ite_eq']
  simp only [mem_univ, ite_true]
  rw [mul_inv_cancel₀ (zpow_ne_zero _ (hx _)), mul_one]

/-- **A run does not change the Laurent monomials** (Volume 5, Corollary 2.3.11 of the handbook). If each step has distinct indices, then the Laurent monomial `x^D` is the Laurent monomial of the new coordinates with the exponent after the run. -/
theorem laurentMonomial_runCoord_runExp {x : ι → K} (hx : ∀ i, x i ≠ 0) {l : List (ι × ι)}
    (hl : ∀ s ∈ l, s.1 ≠ s.2) (D : ι → ℤ) :
    laurentMonomial (runCoord x l) (runExp l D) = laurentMonomial x D := by
  induction l generalizing x D with
  | nil => rfl
  | cons s l ih =>
    rw [runCoord, runExp,
      ih (stepCoord_ne_zero hx s) (fun t ht => hl t (List.mem_cons_of_mem s ht)),
      laurentMonomial_stepCoord_stepExp hx (hl s (List.mem_cons.mpr (Or.inl rfl)))]

/-- **A valid run does not change the Laurent monomials** (Volume 5, Corollary 2.3.11 of the handbook). This is `Singularity.Perron.laurentMonomial_runCoord_runExp` for a valid run. -/
theorem laurentMonomial_runCoord_runExp_of_isValidRun {x : ι → K} (hx : ∀ i, x i ≠ 0)
    {w : ι → ℝ} {l : List (ι × ι)} (hl : IsValidRun w l) (D : ι → ℤ) :
    laurentMonomial (runCoord x l) (runExp l D) = laurentMonomial x D :=
  laurentMonomial_runCoord_runExp hx (fst_ne_snd_of_isValidRun hl) D

/-- **The old coordinates are monomials in the new coordinates** (Volume 5, Corollary 2.3.11 of the handbook). The coordinate `x_j` is the Laurent monomial of the new coordinates with the exponent `runExp l e_j`, and this exponent has entries `≥ 0`. -/
theorem coord_eq_laurentMonomial_runCoord {x : ι → K} (hx : ∀ i, x i ≠ 0) {l : List (ι × ι)}
    (hl : ∀ s ∈ l, s.1 ≠ s.2) (j : ι) :
    x j = laurentMonomial (runCoord x l) (runExp l (Pi.single j 1)) ∧
      ∀ i, 0 ≤ runExp l (Pi.single j 1) i := by
  refine ⟨?_, runExp_nonneg l fun i => ?_⟩
  · rw [laurentMonomial_runCoord_runExp hx hl, laurentMonomial_single]
  · rw [Pi.single_apply]
    split_ifs <;> norm_num

variable {k : Type*} [Field k] [Algebra k K]

omit [DecidableEq ι] in
variable (k) in
/-- **Monomials lie in the polynomial ring.** A Laurent monomial with exponents `≥ 0` lies in the `k`-algebra generated by the elements. -/
theorem laurentMonomial_mem_adjoin {y : ι → K} {D : ι → ℤ} (hD : ∀ i, 0 ≤ D i) :
    laurentMonomial y D ∈ Algebra.adjoin k (Set.range y) := by
  rw [laurentMonomial]
  refine prod_mem fun i _ => ?_
  rw [← Int.toNat_of_nonneg (hD i), zpow_natCast]
  exact pow_mem (Algebra.subset_adjoin (Set.mem_range_self i)) _

variable (k) in
/-- **The new chart contains the old chart** (Volume 5, Corollary 2.3.11 of the handbook). The `k`-algebra generated by the old coordinates is contained in the `k`-algebra generated by the new coordinates. -/
theorem adjoin_range_le_adjoin_range_runCoord {x : ι → K} (hx : ∀ i, x i ≠ 0)
    {l : List (ι × ι)} (hl : ∀ s ∈ l, s.1 ≠ s.2) :
    Algebra.adjoin k (Set.range x) ≤ Algebra.adjoin k (Set.range (runCoord x l)) := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨j, rfl⟩
  obtain ⟨h1, h2⟩ := coord_eq_laurentMonomial_runCoord hx hl j
  rw [h1]
  exact laurentMonomial_mem_adjoin k h2

variable {V : ValuationSubring K}

/-- **The values after a run, strict form** (Volume 5, Corollary 2.3.11 of the handbook). Assume that `v(x^a) < 1` if and only if `a · γ > 0`. For a strictly monotone homomorphism `φ` from the value group to `ℝ≥0`, the weight `γ_i = -log φ(v(x_i))` has this property. Then the new coordinates and the weight after a valid run have the same property. -/
theorem valuation_laurentMonomial_runCoord_lt_one_iff {x : ι → K} (hx : ∀ i, x i ≠ 0)
    {γ : ι → ℝ}
    (hγ : ∀ a : ι → ℤ, V.valuation (laurentMonomial x a) < 1 ↔ 0 < ∑ i, (a i : ℝ) * γ i)
    {l : List (ι × ι)} (hl : IsValidRun γ l) (b : ι → ℤ) :
    V.valuation (laurentMonomial (runCoord x l) b) < 1 ↔
      0 < ∑ i, (b i : ℝ) * runWeight γ l i := by
  obtain ⟨a, rfl⟩ := runExp_surjective (fst_ne_snd_of_isValidRun hl) b
  rw [laurentMonomial_runCoord_runExp_of_isValidRun hx hl, sum_runExp_mul_runWeight hl]
  exact hγ a

/-- **The values after a run** (Volume 5, Corollary 2.3.11 of the handbook). Assume that `v(x^a) ≤ 1` if and only if `a · γ ≥ 0`. For a strictly monotone homomorphism `φ` from the value group to `ℝ≥0`, the weight `γ_i = -log φ(v(x_i))` has this property. Then the new coordinates and the weight after a valid run have the same property. -/
theorem valuation_laurentMonomial_runCoord_le_one_iff {x : ι → K} (hx : ∀ i, x i ≠ 0)
    {γ : ι → ℝ}
    (hγ : ∀ a : ι → ℤ, V.valuation (laurentMonomial x a) ≤ 1 ↔ 0 ≤ ∑ i, (a i : ℝ) * γ i)
    {l : List (ι × ι)} (hl : IsValidRun γ l) (b : ι → ℤ) :
    V.valuation (laurentMonomial (runCoord x l) b) ≤ 1 ↔
      0 ≤ ∑ i, (b i : ℝ) * runWeight γ l i := by
  obtain ⟨a, rfl⟩ := runExp_surjective (fst_ne_snd_of_isValidRun hl) b
  rw [laurentMonomial_runCoord_runExp_of_isValidRun hx hl, sum_runExp_mul_runWeight hl]
  exact hγ a

/-- **The new coordinates have value `< 1`** (Volume 5, Corollary 2.3.11 of the handbook). If the weight is positive and gives the values in the strict form, then each coordinate after a valid run has value `< 1`, because the weight after the run is positive. -/
theorem valuation_runCoord_lt_one {x : ι → K} (hx : ∀ i, x i ≠ 0) {γ : ι → ℝ}
    (hγ : ∀ a : ι → ℤ, V.valuation (laurentMonomial x a) < 1 ↔ 0 < ∑ i, (a i : ℝ) * γ i)
    (hpos : ∀ i, 0 < γ i) {l : List (ι × ι)} (hl : IsValidRun γ l) (i : ι) :
    V.valuation (runCoord x l i) < 1 := by
  rw [← laurentMonomial_single (runCoord x l) i,
    valuation_laurentMonomial_runCoord_lt_one_iff hx hγ hl]
  simpa [Pi.single_apply] using runWeight_pos hpos hl i

omit [DecidableEq ι] in
/-- **The weight of a monomial valuation is independent.** Assume that `v(x^a) ≤ 1` if and only if `a · γ ≥ 0`. If `a · γ = 0`, then `v(x^a) ≤ 1` and `v(x^{-a}) ≤ 1`, so `v(x^a) = 1`, and `a = 0`. -/
theorem independent_of_valuation_le_one_iff {x : ι → K} (hV : IsMonomialValuation k V x)
    {γ : ι → ℝ}
    (hγ : ∀ a : ι → ℤ, V.valuation (laurentMonomial x a) ≤ 1 ↔ 0 ≤ ∑ i, (a i : ℝ) * γ i) :
    ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * γ i = 0 → a = 0 := by
  intro a ha
  apply hV.independent a
  have h1 := (hγ a).mpr ha.ge
  have h2 := (hγ (-a)).mpr (by
    simp only [Pi.neg_apply, Int.cast_neg, neg_mul, sum_neg_distrib, ha, neg_zero, le_refl])
  have h3 : V.valuation (laurentMonomial x a) * V.valuation (laurentMonomial x (-a)) = 1 := by
    rw [← map_mul, ← laurentMonomial_add hV.ne_zero, add_neg_cancel, laurentMonomial_zero,
      map_one]
  refine le_antisymm h1 ?_
  calc 1 = V.valuation (laurentMonomial x a) * V.valuation (laurentMonomial x (-a)) := h3.symm
    _ ≤ V.valuation (laurentMonomial x a) := mul_le_of_le_one_right' h2

omit [DecidableEq ι] in
/-- **The strict form of the values.** Assume that `V` is a monomial valuation in `x`, and that `v(x^a) ≤ 1` if and only if `a · γ ≥ 0`. Then `v(x^a) < 1` if and only if `a · γ > 0`. -/
theorem valuation_lt_one_iff_of_le_one_iff {x : ι → K} (hV : IsMonomialValuation k V x)
    {γ : ι → ℝ}
    (hγ : ∀ a : ι → ℤ, V.valuation (laurentMonomial x a) ≤ 1 ↔ 0 ≤ ∑ i, (a i : ℝ) * γ i)
    (a : ι → ℤ) : V.valuation (laurentMonomial x a) < 1 ↔ 0 < ∑ i, (a i : ℝ) * γ i := by
  have hind := independent_of_valuation_le_one_iff hV hγ
  constructor
  · intro h
    refine lt_of_le_of_ne ((hγ a).mp h.le) fun h0 => ?_
    rw [hind a h0.symm, laurentMonomial_zero, map_one] at h
    exact lt_irrefl _ h
  · intro h
    refine lt_of_le_of_ne ((hγ a).mpr h.le) fun h1 => ?_
    rw [hV.independent a h1] at h
    simp at h

end Singularity.Perron

namespace Singularity

open Perron

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {K : Type*} [Field K] {k : Type*} [Field k]
  [Algebra k K] {V : ValuationSubring K}

/-- **A monomial valuation stays monomial after a run** (Volume 5, Corollary 2.3.11 of the handbook). If `V` is a monomial valuation in `x`, and each step of `l` has distinct indices, then `V` is a monomial valuation in the coordinates after the run. The old coordinates are monomials in the new ones, so the new coordinates generate `K`. A run is surjective on exponents, so the values of the new coordinates are independent. -/
theorem IsMonomialValuation.runCoord {x : ι → K} (hV : IsMonomialValuation k V x)
    {l : List (ι × ι)} (hl : ∀ s ∈ l, s.1 ≠ s.2) :
    IsMonomialValuation k V (Perron.runCoord x l) where
  ne_zero := runCoord_ne_zero hV.ne_zero l
  adjoin_eq_top := by
    rw [eq_top_iff, ← hV.adjoin_eq_top, IntermediateField.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    rw [(coord_eq_laurentMonomial_runCoord hV.ne_zero hl j).1, laurentMonomial]
    exact prod_mem fun i _ =>
      zpow_mem (IntermediateField.subset_adjoin k _ (Set.mem_range_self i)) _
  independent := by
    intro b hb
    obtain ⟨a, rfl⟩ := runExp_surjective hl b
    rw [laurentMonomial_runCoord_runExp hV.ne_zero hl] at hb
    rw [hV.independent a hb, runExp_zero]

end Singularity

namespace Singularity.Perron

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {K : Type*} [Field K] {k : Type*} [Field k]
  [Algebra k K] {V : ValuationSubring K} [Algebra k V] [IsScalarTower k V K]

/-- **Monomial charts by blowups** (Volume 5, Corollary 2.3.11 of the handbook). Let `V` be a monomial valuation in `x`, and let `γ` be a positive weight such that `v(x^a) ≤ 1` if and only if `a · γ ≥ 0`. Let `s` be a finite subset of `V`. Then there is a valid run `l` for `γ` such that the new coordinates have value `< 1`, and each `z ∈ s` has `z g = f` with `f` and `g` in the `k`-algebra generated by the new coordinates and `v(g) = 1`. So `g` is a unit of the local ring of the chart at the centre of `V`, and `z` lies in this local ring.

The proof takes the finite sets of exponents of `Singularity.MonomialValuation.exists_exponents` for the elements of `s`. One valid run makes all these exponents nonnegative. Then the monomials of these exponents are monomials in the new coordinates with exponents in `ℕ`. -/
theorem exists_isValidRun_forall_mem_adjoin_runCoord {x : ι → K}
    (hV : IsMonomialValuation k V x) (γ : ι → ℝ) (hpos : ∀ i, 0 < γ i)
    (hγ : ∀ a : ι → ℤ, V.valuation (laurentMonomial x a) ≤ 1 ↔ 0 ≤ ∑ i, (a i : ℝ) * γ i)
    (s : Finset K) (hs : ∀ z ∈ s, z ∈ V) :
    ∃ l : List (ι × ι), IsValidRun γ l ∧ (∀ i, V.valuation (runCoord x l i) < 1) ∧
      ∀ z ∈ s, ∃ f g : K, f ∈ Algebra.adjoin k (Set.range (runCoord x l)) ∧
        g ∈ Algebra.adjoin k (Set.range (runCoord x l)) ∧ V.valuation g = 1 ∧ z * g = f := by
  classical
  have hind := independent_of_valuation_le_one_iff hV hγ
  choose E hE hES using fun z : s => MonomialValuation.exists_exponents hV (hs z z.2)
  obtain ⟨l, hl, hlE⟩ := exists_isValidRun_forall_runExp_nonneg_of_nonneg γ hpos hind
    (univ.biUnion E) (fun a ha => by
      obtain ⟨z, -, hz⟩ := mem_biUnion.mp ha
      exact (hγ a).mp (hE z a hz))
  refine ⟨l, hl, valuation_runCoord_lt_one hV.ne_zero (valuation_lt_one_iff_of_le_one_iff hV hγ)
    hpos hl, fun z hz => hES ⟨z, hz⟩ _ fun a ha => ?_⟩
  rw [← laurentMonomial_runCoord_runExp_of_isValidRun hV.ne_zero hl]
  exact laurentMonomial_mem_adjoin k (hlE a (mem_biUnion.mpr ⟨⟨z, hz⟩, mem_univ _, ha⟩))

/-- **Monomial charts by blowups, in rank 1** (Volume 5, Corollary 2.3.11 of the handbook). Let `V` be a monomial valuation in `x` with `v(x_i) < 1` for each `i`, and let `φ` be a strictly monotone homomorphism from the value group to `ℝ≥0`. Let `s` be a finite subset of `V`. Then the conclusion of `Singularity.Perron.exists_isValidRun_forall_mem_adjoin_runCoord` holds for the weight `γ_i = -log φ(v(x_i))`. -/
theorem exists_isValidRun_forall_mem_adjoin_runCoord_of_rankOne {x : ι → K}
    (hV : IsMonomialValuation k V x) (hx : ∀ i, V.valuation (x i) < 1)
    (φ : V.ValueGroup →*₀ ℝ≥0) (hφ : StrictMono φ) (s : Finset K) (hs : ∀ z ∈ s, z ∈ V) :
    ∃ l : List (ι × ι), IsValidRun (fun i => -Real.log (φ (V.valuation (x i)))) l ∧
      (∀ i, V.valuation (runCoord x l i) < 1) ∧
      ∀ z ∈ s, ∃ f g : K, f ∈ Algebra.adjoin k (Set.range (runCoord x l)) ∧
        g ∈ Algebra.adjoin k (Set.range (runCoord x l)) ∧ V.valuation g = 1 ∧ z * g = f := by
  set v := V.valuation
  have hpos : ∀ a, (0 : ℝ) < φ (v (laurentMonomial x a)) := by
    intro a
    have h0 : 0 < v (laurentMonomial x a) :=
      zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr (laurentMonomial_ne_zero hV.ne_zero a))
    have h1 := hφ h0
    rw [map_zero] at h1
    exact_mod_cast h1
  set γ : ι → ℝ := fun i => -Real.log (φ (v (x i))) with hγ
  have hx1 : ∀ i, x i = laurentMonomial x (Pi.single i 1) := fun i =>
    (laurentMonomial_single x i).symm
  have hlog : ∀ a, Real.log (φ (v (laurentMonomial x a))) = -∑ i, (a i : ℝ) * γ i := by
    intro a
    have hxi : ∀ i, (0 : ℝ) < φ (v (x i)) := fun i => by rw [hx1 i]; exact hpos _
    rw [laurentMonomial, map_prod, map_prod, NNReal.coe_prod, Real.log_prod]
    · rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zpow₀, map_zpow₀, NNReal.coe_zpow, Real.log_zpow, hγ]
      ring
    · intro i _
      rw [map_zpow₀, map_zpow₀, NNReal.coe_zpow]
      exact (zpow_pos (hxi i) _).ne'
  have hle : ∀ a, v (laurentMonomial x a) ≤ 1 ↔ 0 ≤ ∑ i, (a i : ℝ) * γ i := by
    intro a
    rw [← hφ.le_iff_le, map_one, ← NNReal.coe_le_one, ← Real.log_nonpos_iff (hpos a).le, hlog]
    constructor <;> intro h <;> linarith
  have hγpos : ∀ i, 0 < γ i := by
    intro i
    have h := (valuation_lt_one_iff_of_le_one_iff hV hle (Pi.single i 1)).mp
      (by rw [laurentMonomial_single]; exact hx i)
    simpa [Pi.single_apply] using h
  exact exists_isValidRun_forall_mem_adjoin_runCoord hV γ hγpos hle s hs

end Singularity.Perron
