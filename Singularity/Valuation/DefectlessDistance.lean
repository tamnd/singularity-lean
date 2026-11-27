/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Best approximations in an extension without defect

This file proves Volume 3, Lemma 2.1.2 and Proposition 3.2.3 of the handbook, in an elementary form. Let `L/K` be a finite extension of fields, and let `V` be a valuation ring of `L` with valuation `w`. Let `x_1, ..., x_e ∈ L^×` be elements whose values lie in distinct cosets of the value group of `K`, and let `y_1, ..., y_f ∈ V` be elements whose residues are linearly independent over the residue field of `K`.

* `Singularity.exists_valuation_sum_mul_eq`: the value of `∑ c_j y_j` is the largest value of the `c_j`.
* `Singularity.exists_valuation_sum_eq_max`: Lemma 2.1.2 of the handbook. The value of `∑ c_ij x_i y_j` is the largest value of the terms `c_ij x_i`.
* `Singularity.exists_forall_valuation_sub_le`: Proposition 3.2.3 of the handbook. If `ef = [L : K]` and `x_1 y_1 = 1`, then each `z ∈ L \ K` has a best approximation in `K`.

The valuations are multiplicative, so a large additive value is a small multiplicative value. The largest element of `w(z - K)` in the handbook is an element `a ∈ K` such that `w(z - a) ≤ w(z - a')` for each `a' ∈ K` in multiplicative notation.

The hypotheses are elementary forms of the hypotheses of the handbook. "The values `w(x_i)` lie in distinct cosets" is the statement `w(a x_i) ≠ w(a' x_{i'})` for `i ≠ i'` and nonzero `a, a' ∈ K`. "The residues of the `y_j` are linearly independent over `Kv`" is the statement: if `d_j ∈ K` have `w(d_j) ≤ 1` and `w(∑ d_j y_j) < 1`, then each `w(d_j) < 1`. The condition `ef = n` is the condition that the number of the `x_i` times the number of the `y_j` is `[L : K]`. The files do not translate the numbers `e` and `f` into such families.

The proofs follow the handbook.
-/

open Finset

namespace Singularity

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (V : ValuationSubring L)

/-- Let `y_1, ..., y_f ∈ V` have residues that are linearly independent over the residue field of `K`. Then for each `c_1, ..., c_f ∈ K` there is `j` with `w(∑ c_j y_j) = w(c_j)`, and `w(c_j)` is the largest value of the `c_{j'}` (the first step of the proof of Volume 3, Lemma 2.1.2 of the handbook). -/
theorem exists_valuation_sum_mul_eq {κ : Type*} [Fintype κ] [Nonempty κ] {y : κ → L}
    (hy0 : ∀ j, V.valuation (y j) ≤ 1)
    (hy : ∀ d : κ → K, (∀ j, V.valuation (algebraMap K L (d j)) ≤ 1) →
      V.valuation (∑ j, algebraMap K L (d j) * y j) < 1 →
      ∀ j, V.valuation (algebraMap K L (d j)) < 1)
    (c : κ → K) :
    ∃ j, V.valuation (∑ j, algebraMap K L (c j) * y j) = V.valuation (algebraMap K L (c j)) ∧
      ∀ j', V.valuation (algebraMap K L (c j')) ≤ V.valuation (algebraMap K L (c j)) := by
  obtain ⟨j, -, hj⟩ := exists_max_image univ
    (fun j => V.valuation (algebraMap K L (c j))) univ_nonempty
  refine ⟨j, ?_, fun j' => hj j' (mem_univ _)⟩
  by_cases hc : c j = 0
  · have h0 : ∀ j', algebraMap K L (c j') = 0 := fun j' => by
      have := hj j' (mem_univ _)
      rwa [hc, map_zero, map_zero, le_zero_iff, Valuation.zero_iff] at this
    simp [h0]
  · set d : κ → K := fun j' => c j' / c j with hd
    have hcd : ∀ j', algebraMap K L (c j') = algebraMap K L (c j) * algebraMap K L (d j') :=
      fun j' => by rw [← map_mul, hd, mul_div_cancel₀ _ hc]
    have hpos : 0 < V.valuation (algebraMap K L (c j)) := by
      rw [zero_lt_iff, Valuation.ne_zero_iff, ne_eq, map_eq_zero]
      exact hc
    have hd1 : ∀ j', V.valuation (algebraMap K L (d j')) ≤ 1 := fun j' => by
      have := hj j' (mem_univ _)
      rw [hcd j', map_mul] at this
      exact (mul_le_iff_le_one_right hpos).mp this
    have hdj : d j = 1 := div_self hc
    have hsum : V.valuation (∑ j', algebraMap K L (d j') * y j') = 1 := by
      refine le_antisymm (Valuation.map_sum_le _ fun j' _ => ?_) ?_
      · rw [map_mul]
        exact mul_le_one' (hd1 j') (hy0 j')
      · by_contra h
        have := hy d hd1 (lt_of_not_ge h) j
        rw [hdj, map_one, map_one] at this
        exact lt_irrefl _ this
    have : ∑ j', algebraMap K L (c j') * y j' =
        algebraMap K L (c j) * ∑ j', algebraMap K L (d j') * y j' := by
      rw [mul_sum]
      refine sum_congr rfl fun j' _ => ?_
      rw [hcd j', mul_assoc]
    rw [this, map_mul, hsum, mul_one]

/-- **The independence lemma** (Volume 3, Lemma 2.1.2 of the handbook). Let `x_1, ..., x_e ∈ L^×` have values in distinct cosets of the value group of `K`, and let `y_1, ..., y_f ∈ V` have residues that are linearly independent over the residue field of `K`. Then for each family `c_ij ∈ K` there is a pair `p` such that `w(∑ c_ij x_i y_j) = w(c_p x_p)`, and `w(c_p x_p)` is the largest value of the terms `c_ij x_i`. -/
theorem exists_valuation_sum_eq_max {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    [Nonempty κ] {x : ι → L} {y : κ → L}
    (hx : ∀ i i', i ≠ i' → ∀ a a' : K, a ≠ 0 → a' ≠ 0 →
      V.valuation (algebraMap K L a * x i) ≠ V.valuation (algebraMap K L a' * x i'))
    (hy0 : ∀ j, V.valuation (y j) ≤ 1)
    (hy : ∀ d : κ → K, (∀ j, V.valuation (algebraMap K L (d j)) ≤ 1) →
      V.valuation (∑ j, algebraMap K L (d j) * y j) < 1 →
      ∀ j, V.valuation (algebraMap K L (d j)) < 1)
    (c : ι × κ → K) :
    ∃ p : ι × κ, V.valuation (∑ q, algebraMap K L (c q) * (x q.1 * y q.2)) =
        V.valuation (algebraMap K L (c p) * x p.1) ∧
      ∀ q, V.valuation (algebraMap K L (c q) * x q.1) ≤
        V.valuation (algebraMap K L (c p) * x p.1) := by
  classical
  have hsum : ∑ q, algebraMap K L (c q) * (x q.1 * y q.2) =
      ∑ i, x i * ∑ j, algebraMap K L (c (i, j)) * y j := by
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    ring
  choose J hJ hJmax using fun i => exists_valuation_sum_mul_eq V hy0 hy (fun j => c (i, j))
  obtain ⟨i, -, hi⟩ := exists_max_image univ
    (fun i => V.valuation (algebraMap K L (c (i, J i)) * x i)) univ_nonempty
  have hterm : ∀ i', V.valuation (x i' * ∑ j, algebraMap K L (c (i', j)) * y j) =
      V.valuation (algebraMap K L (c (i', J i')) * x i') := fun i' => by
    rw [map_mul, hJ i', map_mul, mul_comm]
  refine ⟨(i, J i), ?_, ?_⟩
  · rw [hsum]
    by_cases ht : V.valuation (algebraMap K L (c (i, J i)) * x i) = 0
    · rw [ht]
      exact le_antisymm (Valuation.map_sum_le _ fun i' _ =>
        (hterm i').le.trans ((hi i' (mem_univ _)).trans ht.le)) zero_le
    · rw [Valuation.map_sum_eq_of_lt _ (mem_univ i), hterm]
      intro i' hi'
      rw [mem_sdiff, mem_singleton] at hi'
      rw [hterm, hterm]
      refine lt_of_le_of_ne (hi i' (mem_univ _)) fun heq => ?_
      by_cases h1 : c (i', J i') = 0
      · rw [h1, map_zero, zero_mul, map_zero] at heq
        exact ht heq.symm
      by_cases h2 : c (i, J i) = 0
      · rw [h2, map_zero, zero_mul, map_zero] at ht
        exact ht rfl
      exact hx i' i hi'.2 _ _ h1 h2 heq
  · rintro ⟨i', j'⟩
    calc V.valuation (algebraMap K L (c (i', j')) * x i')
        ≤ V.valuation (algebraMap K L (c (i', J i')) * x i') := by
          rw [map_mul, map_mul]
          gcongr
          exact hJmax i' j'
      _ ≤ _ := hi i' (mem_univ _)

/-- **Best approximations without defect** (Volume 3, Proposition 3.2.3 of the handbook). Let `x_1, ..., x_e ∈ L^×` have values in distinct cosets of the value group of `K`, let `y_1, ..., y_f ∈ V` have residues that are linearly independent over the residue field of `K`, let `ef = [L : K]` and let `x_{i₀} y_{j₀} = 1`. Then for each `z ∈ L \ K` there is `a ∈ K` such that `w(z - a) ≤ w(z - a')` for each `a' ∈ K`. In additive notation, `w(z - a)` is the largest element of `w(z - K)`. -/
theorem exists_forall_valuation_sub_le {ι κ : Type*} [Fintype ι] [Fintype κ] {x : ι → L}
    {y : κ → L} (hx0 : ∀ i, x i ≠ 0)
    (hx : ∀ i i', i ≠ i' → ∀ a a' : K, a ≠ 0 → a' ≠ 0 →
      V.valuation (algebraMap K L a * x i) ≠ V.valuation (algebraMap K L a' * x i'))
    (hy0 : ∀ j, V.valuation (y j) ≤ 1)
    (hy : ∀ d : κ → K, (∀ j, V.valuation (algebraMap K L (d j)) ≤ 1) →
      V.valuation (∑ j, algebraMap K L (d j) * y j) < 1 →
      ∀ j, V.valuation (algebraMap K L (d j)) < 1)
    (hcard : Fintype.card ι * Fintype.card κ = Module.finrank K L) (i₀ : ι) (j₀ : κ)
    (h1 : x i₀ * y j₀ = 1) (z : L) (hz : z ∉ Set.range (algebraMap K L)) :
    ∃ a : K, z - algebraMap K L a ≠ 0 ∧
      ∀ a' : K, V.valuation (z - algebraMap K L a) ≤ V.valuation (z - algebraMap K L a') := by
  classical
  have : Nonempty ι := ⟨i₀⟩
  have : Nonempty κ := ⟨j₀⟩
  set b : ι × κ → L := fun q => x q.1 * y q.2 with hb
  have hli : LinearIndependent K b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg q
    obtain ⟨p, hp, hpmax⟩ := exists_valuation_sum_eq_max V hx hy0 hy g
    have h0 : ∑ q, algebraMap K L (g q) * (x q.1 * y q.2) = 0 := by
      simpa [hb, Algebra.smul_def] using hg
    rw [h0, map_zero] at hp
    have := hpmax q
    rw [← hp, le_zero_iff, Valuation.zero_iff, mul_eq_zero] at this
    rcases this with h | h
    · exact (map_eq_zero (algebraMap K L)).mp h
    · exact absurd h (hx0 _)
  have hspan := hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_prod, hcard])
  have hzmem : z ∈ Submodule.span K (Set.range b) := hspan ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hzmem
  set q₀ : ι × κ := (i₀, j₀) with hq₀
  have hrep : ∀ a : K, z - algebraMap K L a =
      ∑ q, algebraMap K L (Function.update c q₀ (c q₀ - a) q) * (x q.1 * y q.2) := by
    intro a
    rw [← hc]
    simp only [Algebra.smul_def, hb]
    rw [← sum_erase_add _ _ (mem_univ q₀), ← sum_erase_add _ _ (mem_univ q₀),
      Function.update_self, map_sub, sum_congr rfl fun q hq =>
        (by rw [Function.update_of_ne (ne_of_mem_erase hq)] :
          algebraMap K L (Function.update c q₀ (c q₀ - a) q) * (x q.1 * y q.2) =
            algebraMap K L (c q) * (x q.1 * y q.2))]
    have : x q₀.1 * y q₀.2 = 1 := h1
    rw [this]
    ring
  refine ⟨c q₀, fun h => hz ⟨c q₀, (sub_eq_zero.mp h).symm⟩, fun a' => ?_⟩
  obtain ⟨p, hp, -⟩ := exists_valuation_sum_eq_max V hx hy0 hy
    (Function.update c q₀ (c q₀ - c q₀))
  obtain ⟨p', hp', hmax'⟩ := exists_valuation_sum_eq_max V hx hy0 hy
    (Function.update c q₀ (c q₀ - a'))
  rw [hrep (c q₀), hp, hrep a', hp']
  by_cases hpq : p = q₀
  · rw [hpq, Function.update_self, sub_self, map_zero, zero_mul, map_zero]
    exact zero_le
  · have := hmax' p
    rw [Function.update_of_ne hpq (c q₀ - a') c] at this
    rw [Function.update_of_ne hpq (c q₀ - c q₀) c]
    exact this

end Singularity
