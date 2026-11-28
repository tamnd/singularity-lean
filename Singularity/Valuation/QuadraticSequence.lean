/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# The descent argument of the theorem of Abhyankar

This file proves the formal parts of Volume 5, Theorem 1.2.6, Corollary 1.2.7 and
Corollary 1.2.8 of the handbook.

Let `V` be a valuation subring of a field `K`, and let `R_0 ⊆ R_1 ⊆ ...` be subrings of `V`.
Each `R_n` is dominated by `V`: a nonzero element `r` of `R_n` with `r⁻¹ ∉ R_n` has
`v(r) < 1`. Let `μ n F G` be a number in `ℕ`. In the handbook it is the intersection number
`i_{R_n}(F, G)`. The descent hypothesis says: if `F, G ∈ R_n` are nonzero and neither is a unit
of `R_n`, then `F/G = F'/G'` with `F', G' ∈ R_{n+1}`, `G' ≠ 0` and `μ (n+1) F' G' < μ n F G`.
In the handbook this is the step of the proof of Theorem 1.2.6 that uses the inequality of
Noether (Proposition 1.2.5), Lemma 1.1.5, Lemma 1.1.6 and Lemma 1.2.2.

## Main results

* `Singularity.exists_mem_of_descent`: Theorem 1.2.6, the induction of the proof. If
  `z = F/G ∈ V` with `F, G ∈ R_n` and the descent hypothesis holds, then `z ∈ R_N` for some `N`.
  The last step of the proof is here: if `F` is a unit of `R_N` and `G` is not, then
  `v(z) > 1`.
* `Singularity.mem_iff_exists_mem_of_descent`: Theorem 1.2.6 from the descent hypothesis. If
  each element of `K` is a quotient of elements of `R_0`, then `V = ⋃ R_n`.
* `Singularity.exists_forall_mem_of_monotone`: a finite subset of the union of an increasing
  sequence of subrings lies in one of them.
* `Singularity.exists_forall_mem_of_descent`: the step of the proof of Corollary 1.2.7 that
  uses Theorem 1.2.6. Each finite subset of `V` lies in some `R_N`.
* `Singularity.exists_adjoin_le_valuationSubring`: the first step of the proof of
  Corollary 1.2.8. For `x, y ∈ K` there are `u ∈ {x, x⁻¹}` and `w ∈ {y, y⁻¹}` with
  `k[u, w] ⊆ V` and `k(u, w) = k(x, y)`.

## What is not proved

The descent hypothesis is not proved. Its proof needs the branch formula (Lemma 1.2.3),
Lemma 1.2.4 and the inequality of Noether (Proposition 1.2.5), which are not in this file. The
file does not construct the quadratic sequence along `v`. In Corollary 1.2.7 the construction of
the affine models `A_n` and the final appeal to Lemma 1.1.1 are not proved. In Corollary 1.2.8
the algebraic independence of `u` and `w` and the regularity of `k[u, w]` are not proved.
-/

namespace Singularity

variable {K : Type*} [Field K]

/-- **Volume 5, Theorem 1.2.6 of the handbook, the induction.** Let `R_n` be subrings of a
valuation subring `V`, each dominated by `V`, with the descent hypothesis for `μ`. If
`z = F/G ∈ V` with `F, G ∈ R_n` and `G ≠ 0`, then `z ∈ R_N` for some `N`. -/
theorem exists_mem_of_descent (V : ValuationSubring K) (R : ℕ → Subring K)
    (hRV : ∀ n, ∀ r ∈ R n, r ∈ V)
    (hdom : ∀ n, ∀ r ∈ R n, r⁻¹ ∉ R n → V.valuation r < 1)
    (μ : ℕ → K → K → ℕ)
    (hdesc : ∀ n F G, F ∈ R n → G ∈ R n → F ≠ 0 → G ≠ 0 → F⁻¹ ∉ R n → G⁻¹ ∉ R n →
      ∃ F' ∈ R (n + 1), ∃ G' ∈ R (n + 1), G' ≠ 0 ∧ F / G = F' / G' ∧
        μ (n + 1) F' G' < μ n F G)
    {z : K} (hz : z ∈ V) {n : ℕ} {F G : K} (hF : F ∈ R n) (hG : G ∈ R n) (hG0 : G ≠ 0)
    (hzFG : z = F / G) : ∃ N, z ∈ R N := by
  suffices H : ∀ m n F G, μ n F G = m → F ∈ R n → G ∈ R n → G ≠ 0 → z = F / G →
      ∃ N, z ∈ R N from H _ n F G rfl hF hG hG0 hzFG
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro n F G hm hF hG hG0 hzFG
  by_cases hF0 : F = 0
  · exact ⟨n, by rw [hzFG, hF0, zero_div]; exact (R n).zero_mem⟩
  by_cases hGi : G⁻¹ ∈ R n
  · exact ⟨n, by rw [hzFG, div_eq_mul_inv]; exact (R n).mul_mem hF hGi⟩
  by_cases hFi : F⁻¹ ∈ R n
  · exfalso
    have hvG : V.valuation G < 1 := hdom n G hG hGi
    have hvz : V.valuation z ≤ 1 := (V.valuation_le_one_iff z).mpr hz
    have hvFi : V.valuation F⁻¹ ≤ 1 := (V.valuation_le_one_iff _).mpr (hRV n _ hFi)
    have hFz : F = z * G := by rw [hzFG, div_mul_cancel₀ _ hG0]
    have hvF : V.valuation F < 1 := by
      calc V.valuation F = V.valuation z * V.valuation G := by rw [hFz, map_mul]
        _ ≤ 1 * V.valuation G := mul_le_mul' hvz le_rfl
        _ = V.valuation G := one_mul _
        _ < 1 := hvG
    have h1 : V.valuation F * V.valuation F⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hF0, map_one]
    have h2 : V.valuation F * V.valuation F⁻¹ ≤ V.valuation F * 1 := mul_le_mul' le_rfl hvFi
    rw [h1, mul_one] at h2
    exact absurd (h2.trans_lt hvF) (lt_irrefl 1)
  obtain ⟨F', hF', G', hG', hG'0, hq, hlt⟩ := hdesc n F G hF hG hF0 hG0 hFi hGi
  exact ih _ (hm ▸ hlt) (n + 1) F' G' rfl hF' hG' hG'0 (hzFG.trans hq)

/-- **Volume 5, Theorem 1.2.6 of the handbook, from the descent hypothesis.** If each element
of `K` is a quotient of elements of `R_0`, then `V` is the union of the rings `R_n`. -/
theorem mem_iff_exists_mem_of_descent (V : ValuationSubring K) (R : ℕ → Subring K)
    (hRV : ∀ n, ∀ r ∈ R n, r ∈ V)
    (hdom : ∀ n, ∀ r ∈ R n, r⁻¹ ∉ R n → V.valuation r < 1)
    (hfrac : ∀ z : K, ∃ F ∈ R 0, ∃ G ∈ R 0, G ≠ 0 ∧ z = F / G)
    (μ : ℕ → K → K → ℕ)
    (hdesc : ∀ n F G, F ∈ R n → G ∈ R n → F ≠ 0 → G ≠ 0 → F⁻¹ ∉ R n → G⁻¹ ∉ R n →
      ∃ F' ∈ R (n + 1), ∃ G' ∈ R (n + 1), G' ≠ 0 ∧ F / G = F' / G' ∧
        μ (n + 1) F' G' < μ n F G)
    (z : K) : z ∈ V ↔ ∃ n, z ∈ R n := by
  refine ⟨fun hz => ?_, fun ⟨n, hn⟩ => hRV n z hn⟩
  obtain ⟨F, hF, G, hG, hG0, hzFG⟩ := hfrac z
  exact exists_mem_of_descent V R hRV hdom μ hdesc hz hF hG hG0 hzFG

/-- A finite subset of the union of an increasing sequence of subrings lies in one of them. -/
theorem exists_forall_mem_of_monotone {R : ℕ → Subring K} (hmono : Monotone R) (S : Finset K)
    (hS : ∀ s ∈ S, ∃ n, s ∈ R n) : ∃ N, ∀ s ∈ S, s ∈ R N := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a S _ ih =>
    obtain ⟨N, hN⟩ := ih fun s hs => hS s (Finset.mem_insert_of_mem hs)
    obtain ⟨n, hn⟩ := hS a (Finset.mem_insert_self a S)
    refine ⟨max N n, fun s hs => ?_⟩
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact hmono (le_max_right N n) hn
    · exact hmono (le_max_left N n) (hN s hs)

/-- **Volume 5, Corollary 1.2.7 of the handbook, the step that uses Theorem 1.2.6.** Under the
hypotheses of `mem_iff_exists_mem_of_descent`, if the sequence `R_n` increases, then each finite
subset of `V` lies in some `R_N`. -/
theorem exists_forall_mem_of_descent (V : ValuationSubring K) (R : ℕ → Subring K)
    (hmono : Monotone R) (hRV : ∀ n, ∀ r ∈ R n, r ∈ V)
    (hdom : ∀ n, ∀ r ∈ R n, r⁻¹ ∉ R n → V.valuation r < 1)
    (hfrac : ∀ z : K, ∃ F ∈ R 0, ∃ G ∈ R 0, G ≠ 0 ∧ z = F / G)
    (μ : ℕ → K → K → ℕ)
    (hdesc : ∀ n F G, F ∈ R n → G ∈ R n → F ≠ 0 → G ≠ 0 → F⁻¹ ∉ R n → G⁻¹ ∉ R n →
      ∃ F' ∈ R (n + 1), ∃ G' ∈ R (n + 1), G' ≠ 0 ∧ F / G = F' / G' ∧
        μ (n + 1) F' G' < μ n F G)
    (S : Finset K) (hS : ∀ s ∈ S, s ∈ V) : ∃ N, ∀ s ∈ S, s ∈ R N :=
  exists_forall_mem_of_monotone hmono S fun s hs =>
    (mem_iff_exists_mem_of_descent V R hRV hdom hfrac μ hdesc s).mp (hS s hs)

/-- If `a = b` or `a = b⁻¹`, then `b = a` or `b = a⁻¹`. -/
theorem eq_or_eq_inv_symm {a b : K} (h : a = b ∨ a = b⁻¹) : b = a ∨ b = a⁻¹ := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, inv_inv])

/-- If `a = b` or `a = b⁻¹`, and `b` lies in an intermediate field `E`, then `a ∈ E`. -/
theorem mem_intermediateField_of_eq_or_eq_inv {k : Type*} [Field k] [Algebra k K]
    (E : IntermediateField k K) {a b : K} (h : a = b ∨ a = b⁻¹) (hb : b ∈ E) : a ∈ E := by
  rcases h with rfl | rfl
  · exact hb
  · exact inv_mem hb

/-- If `u ∈ {x, x⁻¹}` and `w ∈ {y, y⁻¹}`, then `k(u, w) = k(x, y)`. -/
theorem adjoin_pair_eq_of_eq_or_eq_inv {k : Type*} [Field k] [Algebra k K] {x y u w : K}
    (hu : u = x ∨ u = x⁻¹) (hw : w = y ∨ w = y⁻¹) :
    IntermediateField.adjoin k {u, w} = IntermediateField.adjoin k {x, y} := by
  have key : ∀ {a b c d : K}, (a = c ∨ a = c⁻¹) → (b = d ∨ b = d⁻¹) →
      IntermediateField.adjoin k {a, b} ≤ IntermediateField.adjoin k {c, d} := by
    intro a b c d ha hb
    rw [IntermediateField.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨mem_intermediateField_of_eq_or_eq_inv _ ha
        (IntermediateField.subset_adjoin k _ (by simp)),
      mem_intermediateField_of_eq_or_eq_inv _ hb
        (IntermediateField.subset_adjoin k _ (by simp))⟩
  exact le_antisymm (key hu hw) (key (eq_or_eq_inv_symm hu) (eq_or_eq_inv_symm hw))

/-- **Volume 5, Corollary 1.2.8 of the handbook, the first step.** Let `V` be a valuation
subring of `K` that contains `k`, and let `x, y ∈ K`. There are `u ∈ {x, x⁻¹}` and
`w ∈ {y, y⁻¹}` with `u, w ∈ V`, `k[u, w] ⊆ V` and `k(u, w) = k(x, y)`. -/
theorem exists_adjoin_le_valuationSubring {k : Type*} [Field k] [Algebra k K]
    (V : ValuationSubring K) (hk : ∀ c : k, algebraMap k K c ∈ V) (x y : K) :
    ∃ u w : K, (u = x ∨ u = x⁻¹) ∧ (w = y ∨ w = y⁻¹) ∧ u ∈ V ∧ w ∈ V ∧
      (∀ a ∈ Algebra.adjoin k ({u, w} : Set K), a ∈ V) ∧
      IntermediateField.adjoin k {u, w} = IntermediateField.adjoin k {x, y} := by
  have choose : ∀ t : K, ∃ s : K, (s = t ∨ s = t⁻¹) ∧ s ∈ V := fun t =>
    (V.mem_or_inv_mem t).elim (fun h => ⟨t, Or.inl rfl, h⟩) (fun h => ⟨t⁻¹, Or.inr rfl, h⟩)
  obtain ⟨u, hu, huV⟩ := choose x
  obtain ⟨w, hw, hwV⟩ := choose y
  let VA : Subalgebra k K := { V.toSubring.toSubsemiring with algebraMap_mem' := hk }
  have hle : Algebra.adjoin k ({u, w} : Set K) ≤ VA := by
    rw [Algebra.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨huV, hwV⟩
  exact ⟨u, w, hu, hw, huV, hwV, fun a ha => hle ha, adjoin_pair_eq_of_eq_or_eq_inv hu hw⟩

end Singularity
