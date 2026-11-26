/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Comparable extensions of a valuation are equal

Let `L/K` be an algebraic extension, and let `w, w'` be two extensions to `L` of a valuation `v` of `K`. If `O_w ⊆ O_w'`, then `w = w'` (Volume 3, Lemma 3.1.1 of the handbook). This file proves this result for valuation rings: let `B ⊆ B'` be valuation rings of `L` with `B ∩ K = B' ∩ K`. Then `B = B'`.

The handbook assumes that `L/K` is finite, and it uses that `Γ_w / Γ_v` is finite. The proof here uses only that `Γ_w / Γ_v` is a torsion group, so it works for each algebraic extension. Let `z ∈ L` be nonzero. Then `w(z^n) = w(c)` for some `n > 0` and some `c ∈ K` (`Singularity.exists_pow_valuation_eq_algebraMap`). This follows from a relation `∑ a_i z^i = 0`: two of the nonzero terms have the same largest value.

Now let `z ∈ B'` with `z ∉ B`. Then `z⁻¹ ∈ B`. The element `u = c z^{-n}` has the value `1` for `w`, so `u ∈ B ⊆ B'`. Thus `c = z^n u ∈ B' ∩ K = B ∩ K`, and `z^n ∈ B` because `w(z^n) = w(c)`. So `z = z^n (z⁻¹)^{n-1} ∈ B`, which is a contradiction.

## Main results

* `Singularity.exists_pow_valuation_eq_algebraMap`: a power of an algebraic element has the value of an element of `K`.
* `Singularity.ValuationSubring.eq_of_le_of_comap_eq`: comparable extensions are equal.
-/

namespace Singularity

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- Let `l < m`, let `a ≠ 0`, and let `w(a z^m) = w(b z^l)`. Then `w(z^{m-l}) = w(b / a)`. -/
theorem valuation_pow_sub_eq {w : Valuation L Γ₀} {z : L} (hz : z ≠ 0) {l m : ℕ} (hlm : l < m)
    {a b : K} (ha : a ≠ 0) (h : w (algebraMap K L a * z ^ m) = w (algebraMap K L b * z ^ l)) :
    w (z ^ (m - l)) = w (algebraMap K L (b / a)) := by
  have hwa : w (algebraMap K L a) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact (map_ne_zero _).mpr ha
  have hwz : w (z ^ l) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact pow_ne_zero _ hz
  rw [← Nat.add_sub_of_le hlm.le, pow_add] at h
  simp only [Valuation.map_mul] at h
  rw [map_div₀, map_div₀, eq_div_iff hwa]
  apply mul_right_cancel₀ hwz
  rw [← h]
  ac_rfl

/-- Let `w` be a valuation of `L` and let `z ∈ L` be nonzero and algebraic over `K`. Then there are `n > 0` and `c ∈ K` with `w(z^n) = w(c)`. So the value of `z` is a torsion element modulo the values of `K`. -/
theorem exists_pow_valuation_eq_algebraMap {w : Valuation L Γ₀} {z : L} (hz : z ≠ 0)
    (halg : IsAlgebraic K z) : ∃ n : ℕ, 0 < n ∧ ∃ c : K, w (z ^ n) = w (algebraMap K L c) := by
  classical
  obtain ⟨p, hp0, hpz⟩ := halg
  simp only [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def] at hpz
  obtain ⟨j, hj, hmax⟩ := p.support.exists_max_image
    (fun e => w (algebraMap K L (p.coeff e) * z ^ e)) (Polynomial.support_nonempty.mpr hp0)
  have htne : ∀ e ∈ p.support, w (algebraMap K L (p.coeff e) * z ^ e) ≠ 0 := by
    intro e he
    rw [Valuation.ne_zero_iff]
    exact mul_ne_zero ((map_ne_zero _).mpr (Polynomial.mem_support_iff.mp he)) (pow_ne_zero _ hz)
  by_cases htie : ∀ i ∈ p.support \ {j},
      w (algebraMap K L (p.coeff i) * z ^ i) < w (algebraMap K L (p.coeff j) * z ^ j)
  · have key : w (∑ e ∈ p.support, algebraMap K L (p.coeff e) * z ^ e) =
        w (algebraMap K L (p.coeff j) * z ^ j) := Valuation.map_sum_eq_of_lt w hj htie
    rw [hpz, Valuation.map_zero] at key
    exact absurd key.symm (htne j hj)
  · push_neg at htie
    obtain ⟨i, hi, hle⟩ := htie
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    have heq : w (algebraMap K L (p.coeff i) * z ^ i) = w (algebraMap K L (p.coeff j) * z ^ j) :=
      le_antisymm (hmax i hi.1) hle
    rcases lt_or_gt_of_ne hi.2 with hij | hij
    · exact ⟨j - i, Nat.sub_pos_of_lt hij, _,
        valuation_pow_sub_eq hz hij (Polynomial.mem_support_iff.mp hj) heq.symm⟩
    · exact ⟨i - j, Nat.sub_pos_of_lt hij, _,
        valuation_pow_sub_eq hz hij (Polynomial.mem_support_iff.mp hi.1) heq⟩

/-- Let `L/K` be an algebraic extension, and let `B ⊆ B'` be valuation rings of `L` with `B ∩ K = B' ∩ K`. Then `B = B'` (Volume 3, Lemma 3.1.1 of the handbook). The handbook states the result for two extensions `w, w'` of a valuation `v` of `K` with `O_w ⊆ O_w'`, and it assumes that `L/K` is finite. -/
theorem ValuationSubring.eq_of_le_of_comap_eq [Algebra.IsAlgebraic K L]
    {B B' : ValuationSubring L} (hle : B ≤ B')
    (hcomap : B.comap (algebraMap K L) = B'.comap (algebraMap K L)) : B = B' := by
  refine le_antisymm hle fun z hz' => ?_
  by_contra hz
  have hzinv : z⁻¹ ∈ B := (B.mem_or_inv_mem z).resolve_left hz
  have hz0 : z ≠ 0 := fun h => hz (h ▸ B.zero_mem)
  obtain ⟨n, hn, c, hc⟩ :=
    exists_pow_valuation_eq_algebraMap (w := B.valuation) hz0 (Algebra.IsAlgebraic.isAlgebraic z)
  have hzn0 : z ^ n ≠ 0 := pow_ne_zero _ hz0
  have hvzn : B.valuation (z ^ n) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact hzn0
  have hu : algebraMap K L c * (z ^ n)⁻¹ ∈ B :=
    (B.valuation_le_one_iff (algebraMap K L c * (z ^ n)⁻¹)).mp (le_of_eq (by
      rw [Valuation.map_mul, map_inv₀, ← hc, mul_inv_cancel₀ hvzn]))
  have hcB' : algebraMap K L c ∈ B' := by
    have hcz : algebraMap K L c = z ^ n * (algebraMap K L c * (z ^ n)⁻¹) := by
      rw [mul_left_comm, mul_inv_cancel₀ hzn0, mul_one]
    rw [hcz]
    exact B'.mul_mem (B'.pow_mem hz' n) (hle hu)
  have hcB : algebraMap K L c ∈ B := by
    have hc' : c ∈ B'.comap (algebraMap K L) := hcB'
    rw [← hcomap] at hc'
    exact hc'
  have hznB : z ^ n ∈ B := by
    rw [← B.valuation_le_one_iff, hc, B.valuation_le_one_iff]
    exact hcB
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hzm : z = z ^ (m + 1) * z⁻¹ ^ m := by
    rw [pow_succ, mul_comm (z ^ m) z, mul_assoc, ← mul_pow, mul_inv_cancel₀ hz0, one_pow,
      mul_one]
  apply hz
  rw [hzm]
  exact B.mul_mem hznB (B.pow_mem hzinv m)

end Singularity
