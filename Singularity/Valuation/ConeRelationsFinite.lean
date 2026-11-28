/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib

/-!
# The combinatorial step of the cone argument

Let `s : ℚ^m → ℝ` be `ℚ`-linear, let `n* ∈ ℚ^m` and `Λ = s(n*)`. Let `X ⊂ ℤ^m` be a set with `s(n) < Λ` for each `n ∈ X`, such that `X ∩ {s ≤ c}` is finite for each real `c < Λ`. Let `P ⊂ X` be finite. Assume that each `n ∈ X \ P` has a relation `n - n* = r Σ_i (n'_i - n*)` with `r > 0` rational and elements `n'_i ∈ X` with `s(n'_i) < s(n)`. Then `X` is finite.

This lemma is the combinatorial step of the cone argument for the equation `z^p = f(x)` over the henselization of a rational function field with an Abhyankar valuation of rank one. There `X` is the set of the exponents of the terms of an element `x` below the distance `Λ`, and each relation comes from the comparison of one coefficient.

## Main results

* `Singularity.cone_relations_induction`: the induction principle on `X`. A property that passes from all elements of `X` with a smaller value of `s` to an element of `X` holds on all of `X`.
* `Singularity.exists_coeff_of_cone_relations`: each `n ∈ X` has the form `n - n* = Σ_{β ∈ P} c_β (β - n*)` with rational `c_β ≥ 0`.
* `Singularity.exists_le_of_cone_relations`: for each `n ∈ X` there is `β ∈ P` with `s(β) ≤ s(n)`.
* `Singularity.sub_le_sup'_of_cone_relations`: the bound `Λ - s(n) ≤ max_{β ∈ P} (Λ - s(β))`.
* `Singularity.eq_empty_of_cone_relations`: if `P` is empty, then `X` is empty.
* `Singularity.finite_of_cone_relations`: the set `X` is finite.

## The proof

1. For `n ∈ X` the set `B(n) = {n' ∈ X : s(n') ≤ s(n)}` is finite. If `s(n') < s(n)`, then `B(n')` is a proper subset of `B(n)`. So strong induction on the cardinality of `B(n)` is possible.
2. By this induction each `n ∈ X` has coefficients `c_β ≥ 0` with `n - n* = Σ_{β ∈ P} c_β (β - n*)`. For `n ∈ P` the coefficients are the indicator of `n`. For `n ∉ P` they are `r` times the sum of the coefficients of the `n'_i`.
3. By the same induction there is `β ∈ P` with `s(β) ≤ s(n)`. If `n ∉ P` and the relation has no terms, then `n = n*`, and this contradicts `s(n) < Λ`.
4. Apply `s` to the relation of step 2. This gives `Λ - s(n) = Σ_β c_β (Λ - s(β))`. Each term is `≥ 0` and the sum is at most `M = Σ_β (Λ - s(β))`. Thus `c_β ≤ M / (Λ - s(β))`, and this bound does not depend on `n`.
5. Thus each coordinate `n_i - n*_i` is bounded independently of `n`. A set of integer vectors with bounded coordinates is finite.

## What is not proved

The module proves only the combinatorial lemma. The valuation-theoretic statements that give the relations are not in Lean. Local uniformization in dimension 4 or more is open.

## References

* Volume 5, Chapter 4 of the handbook, the section on the cone argument.
-/

namespace Singularity

/-- The induction principle for a set `X` on which a real function `f` is below `Λ` and has finite sublevel sets below `Λ`. If a property holds for `x ∈ X` whenever it holds for all `y ∈ X` with `f y < f x`, then it holds on all of `X`. The proof is a strong induction on the cardinality of `{y ∈ X | f y ≤ f x}`. -/
theorem cone_relations_induction {α : Type*} (f : α → ℝ) (Λ : ℝ) (X : Set α)
    (hlt : ∀ x ∈ X, f x < Λ) (hfin : ∀ c : ℝ, c < Λ → {x ∈ X | f x ≤ c}.Finite)
    {p : α → Prop} (h : ∀ x ∈ X, (∀ y ∈ X, f y < f x → p y) → p x) : ∀ x ∈ X, p x := by
  suffices H : ∀ N : ℕ, ∀ x ∈ X, {y ∈ X | f y ≤ f x}.ncard = N → p x from
    fun x hx => H _ x hx rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro x hx hN
    refine h x hx fun y hy hyx => ih _ ?_ y hy rfl
    rw [← hN]
    refine Set.ncard_lt_ncard ?_ (hfin _ (hlt x hx))
    refine ⟨fun z hz => ⟨hz.1, hz.2.trans hyx.le⟩, fun hsub => ?_⟩
    exact absurd (hsub ⟨hx, le_rfl⟩).2 (not_le.mpr hyx)

variable {ι : Type*} [Fintype ι]

/-- Step 2 of the cone argument. Under the hypotheses of `finite_of_cone_relations`, with `P` a `Finset`, each `n ∈ X` has rational coefficients `c β ≥ 0` with `n - n* = Σ_{β ∈ P} c β • (β - n*)`. -/
theorem exists_coeff_of_cone_relations (s : (ι → ℚ) →ₗ[ℚ] ℝ) (nstar : ι → ℚ)
    (X : Set (ι → ℤ)) (P : Finset (ι → ℤ))
    (hlt : ∀ n ∈ X, s (fun i => (n i : ℚ)) < s nstar)
    (hfin : ∀ c : ℝ, c < s nstar → {n ∈ X | s (fun i => (n i : ℚ)) ≤ c}.Finite)
    (hrel : ∀ n ∈ X, n ∉ P → ∃ (k : ℕ) (n' : Fin k → ι → ℤ) (r : ℚ), 0 < r ∧
        (∀ j, n' j ∈ X ∧ s (fun i => (n' j i : ℚ)) < s (fun i => (n i : ℚ))) ∧
        (fun i => (n i : ℚ)) - nstar = r • ∑ j, ((fun i => (n' j i : ℚ)) - nstar)) :
    ∀ n ∈ X, ∃ c : (ι → ℤ) → ℚ, (∀ β, 0 ≤ c β) ∧
      (fun i => (n i : ℚ)) - nstar = ∑ β ∈ P, c β • ((fun i => (β i : ℚ)) - nstar) := by
  refine cone_relations_induction (fun n => s (fun i => (n i : ℚ))) _ X hlt hfin ?_
  intro n hn ih
  by_cases hnP : n ∈ P
  · refine ⟨fun β => if β = n then 1 else 0, fun β => by dsimp only; split_ifs <;> norm_num, ?_⟩
    simp [ite_smul, Finset.sum_ite_eq', hnP]
  · obtain ⟨k, n', r, hr, hn', heq⟩ := hrel n hn hnP
    choose c hc0 hc using fun j => ih (n' j) (hn' j).1 (hn' j).2
    refine ⟨fun β => r * ∑ j, c j β, fun β => ?_, ?_⟩
    · exact mul_nonneg hr.le (Finset.sum_nonneg fun j _ => hc0 j β)
    · rw [heq]
      simp_rw [hc, mul_smul, ← Finset.smul_sum, Finset.sum_smul]
      rw [Finset.sum_comm]

/-- Step 3 of the cone argument. Under the hypotheses of `finite_of_cone_relations`, with `P` a `Finset`, each `n ∈ X` has some `β ∈ P` with `s(β) ≤ s(n)`. -/
theorem exists_le_of_cone_relations (s : (ι → ℚ) →ₗ[ℚ] ℝ) (nstar : ι → ℚ)
    (X : Set (ι → ℤ)) (P : Finset (ι → ℤ))
    (hlt : ∀ n ∈ X, s (fun i => (n i : ℚ)) < s nstar)
    (hfin : ∀ c : ℝ, c < s nstar → {n ∈ X | s (fun i => (n i : ℚ)) ≤ c}.Finite)
    (hrel : ∀ n ∈ X, n ∉ P → ∃ (k : ℕ) (n' : Fin k → ι → ℤ) (r : ℚ), 0 < r ∧
        (∀ j, n' j ∈ X ∧ s (fun i => (n' j i : ℚ)) < s (fun i => (n i : ℚ))) ∧
        (fun i => (n i : ℚ)) - nstar = r • ∑ j, ((fun i => (n' j i : ℚ)) - nstar)) :
    ∀ n ∈ X, ∃ β ∈ P, s (fun i => (β i : ℚ)) ≤ s (fun i => (n i : ℚ)) := by
  refine cone_relations_induction (fun n => s (fun i => (n i : ℚ))) _ X hlt hfin ?_
  intro n hn ih
  by_cases hnP : n ∈ P
  · exact ⟨n, hnP, le_rfl⟩
  · obtain ⟨k, n', r, hr, hn', heq⟩ := hrel n hn hnP
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, smul_zero, sub_eq_zero] at heq
      exact absurd (hlt n hn) (by rw [heq]; exact lt_irrefl _)
    · obtain ⟨β, hβ, hle⟩ := ih (n' ⟨0, hk⟩) (hn' _).1 (hn' _).2
      exact ⟨β, hβ, hle.trans (hn' _).2.le⟩

/-- Step 3 of the cone argument, the bound. Under the hypotheses of `finite_of_cone_relations`, with `P` a nonempty `Finset`, each `n ∈ X` satisfies `Λ - s(n) ≤ max_{β ∈ P} (Λ - s(β))`. -/
theorem sub_le_sup'_of_cone_relations (s : (ι → ℚ) →ₗ[ℚ] ℝ) (nstar : ι → ℚ)
    (X : Set (ι → ℤ)) (P : Finset (ι → ℤ)) (hne : P.Nonempty)
    (hlt : ∀ n ∈ X, s (fun i => (n i : ℚ)) < s nstar)
    (hfin : ∀ c : ℝ, c < s nstar → {n ∈ X | s (fun i => (n i : ℚ)) ≤ c}.Finite)
    (hrel : ∀ n ∈ X, n ∉ P → ∃ (k : ℕ) (n' : Fin k → ι → ℤ) (r : ℚ), 0 < r ∧
        (∀ j, n' j ∈ X ∧ s (fun i => (n' j i : ℚ)) < s (fun i => (n i : ℚ))) ∧
        (fun i => (n i : ℚ)) - nstar = r • ∑ j, ((fun i => (n' j i : ℚ)) - nstar)) :
    ∀ n ∈ X, s nstar - s (fun i => (n i : ℚ)) ≤
      P.sup' hne (fun β => s nstar - s (fun i => (β i : ℚ))) := by
  intro n hn
  obtain ⟨β, hβ, hle⟩ := exists_le_of_cone_relations s nstar X P hlt hfin hrel n hn
  exact Finset.le_sup'_of_le _ hβ (by linarith)

/-- Step 3 of the cone argument, the empty case. Under the hypotheses of `finite_of_cone_relations`, if `P` is empty, then `X` is empty. -/
theorem eq_empty_of_cone_relations (s : (ι → ℚ) →ₗ[ℚ] ℝ) (nstar : ι → ℚ)
    (X : Set (ι → ℤ))
    (hlt : ∀ n ∈ X, s (fun i => (n i : ℚ)) < s nstar)
    (hfin : ∀ c : ℝ, c < s nstar → {n ∈ X | s (fun i => (n i : ℚ)) ≤ c}.Finite)
    (hrel : ∀ n ∈ X, ∃ (k : ℕ) (n' : Fin k → ι → ℤ) (r : ℚ), 0 < r ∧
        (∀ j, n' j ∈ X ∧ s (fun i => (n' j i : ℚ)) < s (fun i => (n i : ℚ))) ∧
        (fun i => (n i : ℚ)) - nstar = r • ∑ j, ((fun i => (n' j i : ℚ)) - nstar)) :
    X = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun n hn => ?_
  obtain ⟨β, hβ, -⟩ := exists_le_of_cone_relations s nstar X ∅ hlt hfin
    (fun n hn _ => hrel n hn) n hn
  simp at hβ

/-- Step 4 of the cone argument. Let `n ∈ X` have the form `n - n* = Σ_{β ∈ P} c β • (β - n*)` with `c β ≥ 0`, and let `β ∈ P`. Then `c β (Λ - s(β)) ≤ Σ_{γ ∈ P} (Λ - s(γ))`. -/
theorem coeff_mul_le_of_cone_relations (s : (ι → ℚ) →ₗ[ℚ] ℝ) (nstar : ι → ℚ)
    (X : Set (ι → ℤ)) (P : Finset (ι → ℤ)) (hPX : ∀ β ∈ P, β ∈ X)
    (hlt : ∀ n ∈ X, s (fun i => (n i : ℚ)) < s nstar)
    (hfin : ∀ c : ℝ, c < s nstar → {n ∈ X | s (fun i => (n i : ℚ)) ≤ c}.Finite)
    (hrel : ∀ n ∈ X, n ∉ P → ∃ (k : ℕ) (n' : Fin k → ι → ℤ) (r : ℚ), 0 < r ∧
        (∀ j, n' j ∈ X ∧ s (fun i => (n' j i : ℚ)) < s (fun i => (n i : ℚ))) ∧
        (fun i => (n i : ℚ)) - nstar = r • ∑ j, ((fun i => (n' j i : ℚ)) - nstar))
    {n : ι → ℤ} (hn : n ∈ X) {c : (ι → ℤ) → ℚ} (hc0 : ∀ β, 0 ≤ c β)
    (hc : (fun i => (n i : ℚ)) - nstar = ∑ β ∈ P, c β • ((fun i => (β i : ℚ)) - nstar))
    {β : ι → ℤ} (hβ : β ∈ P) :
    (c β : ℝ) * (s nstar - s (fun i => (β i : ℚ))) ≤
      ∑ γ ∈ P, (s nstar - s (fun i => (γ i : ℚ))) := by
  have hd : ∀ γ ∈ P, 0 ≤ s nstar - s (fun i => (γ i : ℚ)) :=
    fun γ hγ => sub_nonneg.mpr (hlt γ (hPX γ hγ)).le
  have hs := congrArg s hc
  simp only [map_sub, map_sum, map_smul, Rat.smul_def] at hs
  have hsum : s nstar - s (fun i => (n i : ℚ)) =
      ∑ γ ∈ P, (c γ : ℝ) * (s nstar - s (fun i => (γ i : ℚ))) := by
    rw [show s nstar - s (fun i => (n i : ℚ)) = -(s (fun i => (n i : ℚ)) - s nstar) by ring, hs,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun γ _ => by ring
  obtain ⟨β₀, hβ₀, hle⟩ := exists_le_of_cone_relations s nstar X P hlt hfin hrel n hn
  calc (c β : ℝ) * (s nstar - s (fun i => (β i : ℚ)))
      ≤ ∑ γ ∈ P, (c γ : ℝ) * (s nstar - s (fun i => (γ i : ℚ))) :=
        Finset.single_le_sum (f := fun γ => (c γ : ℝ) * (s nstar - s (fun i => (γ i : ℚ))))
          (fun γ hγ => mul_nonneg (by exact_mod_cast hc0 γ) (hd γ hγ)) hβ
    _ = s nstar - s (fun i => (n i : ℚ)) := hsum.symm
    _ ≤ s nstar - s (fun i => (β₀ i : ℚ)) := by linarith
    _ ≤ ∑ γ ∈ P, (s nstar - s (fun i => (γ i : ℚ))) :=
        Finset.single_le_sum (f := fun γ => s nstar - s (fun i => (γ i : ℚ))) hd hβ₀

/-- **The cone lemma of the cone argument** (Volume 5, Chapter 4 of the handbook). Let `s : ℚ^ι → ℝ` be `ℚ`-linear, `n* ∈ ℚ^ι` and `Λ = s(n*)`. Let `X ⊂ ℤ^ι` with `s(n) < Λ` on `X` and with `X ∩ {s ≤ c}` finite for each `c < Λ`. Let `P ⊆ X` be finite. If each `n ∈ X \ P` satisfies `n - n* = r Σ_j (n'_j - n*)` with `r > 0` and `n'_j ∈ X`, `s(n'_j) < s(n)`, then `X` is finite. -/
theorem finite_of_cone_relations (s : (ι → ℚ) →ₗ[ℚ] ℝ) (nstar : ι → ℚ)
    (X P : Set (ι → ℤ)) (hP : P.Finite) (hPX : P ⊆ X)
    (hlt : ∀ n ∈ X, s (fun i => (n i : ℚ)) < s nstar)
    (hfin : ∀ c : ℝ, c < s nstar → {n ∈ X | s (fun i => (n i : ℚ)) ≤ c}.Finite)
    (hrel : ∀ n ∈ X, n ∉ P → ∃ (k : ℕ) (n' : Fin k → ι → ℤ) (r : ℚ), 0 < r ∧
        (∀ j, n' j ∈ X ∧ s (fun i => (n' j i : ℚ)) < s (fun i => (n i : ℚ))) ∧
        (fun i => (n i : ℚ)) - nstar = r • ∑ j, ((fun i => (n' j i : ℚ)) - nstar)) :
    X.Finite := by
  classical
  set F := hP.toFinset
  have hFX : ∀ β ∈ F, β ∈ X := fun β hβ => hPX (hP.mem_toFinset.mp hβ)
  have hrel' : ∀ n ∈ X, n ∉ F → _ := fun n hn hnF => hrel n hn (by simpa [F] using hnF)
  let d : (ι → ℤ) → ℝ := fun β => s nstar - s (fun i => (β i : ℚ))
  let K : (ι → ℤ) → ℚ := fun β => ⌈(∑ γ ∈ F, d γ) / d β⌉
  let R : ι → ℚ := fun i => ∑ β ∈ F, K β * |(β i : ℚ) - nstar i|
  refine (Set.Finite.pi (t := fun i => Set.Icc ⌈nstar i - R i⌉ ⌊nstar i + R i⌋)
    (fun i => Set.finite_Icc _ _)).subset fun n hn => ?_
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  obtain ⟨c, hc0, hc⟩ := exists_coeff_of_cone_relations s nstar X F hlt hfin hrel' n hn
  have hcK : ∀ β ∈ F, c β ≤ K β := by
    intro β hβ
    have hdpos : 0 < d β := sub_pos.mpr (hlt β (hFX β hβ))
    have h := coeff_mul_le_of_cone_relations s nstar X F hFX hlt hfin hrel' hn hc0 hc hβ
    have h' : (c β : ℝ) ≤ K β :=
      ((le_div_iff₀ hdpos).mpr h).trans (by simp only [K, Rat.cast_intCast]; exact Int.le_ceil _)
    exact_mod_cast h'
  intro i
  have hi : (n i : ℚ) - nstar i = ∑ β ∈ F, c β * ((β i : ℚ) - nstar i) := by
    simpa [Finset.sum_apply] using congrFun hc i
  have habs : |(n i : ℚ) - nstar i| ≤ R i := by
    rw [hi]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun β hβ => ?_)
    rw [abs_mul, abs_of_nonneg (hc0 β)]
    exact mul_le_mul_of_nonneg_right (hcK β hβ) (abs_nonneg _)
  rw [abs_le] at habs
  exact ⟨Int.ceil_le.mpr (by linarith), Int.le_floor.mpr (by linarith)⟩

end Singularity
