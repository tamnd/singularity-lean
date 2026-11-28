/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra

/-!
# Approximation by `p`-th powers in a valued field of characteristic `p`

Let `K` be a field of characteristic `p` and let `v` be a valuation of `K` with a perfect residue field. For `f ∈ K` the handbook studies the set `A(f) = {v(f - h^p) : h ∈ K}`. This file proves the improvement lemma and the elementary parts of the dichotomy for `A(f)`.

The valuations are multiplicative (`Valuation K Γ₀`), as in the other modules of the repository. So a large additive value is a small multiplicative value. The condition "`v(f - h^p) ∈ pΓ`" is the statement `v (f - h ^ p) = v (a ^ p)` for some `a ≠ 0`. "A better approximation" is an `h'` with `v (f - h' ^ p) < v (f - h ^ p)`. "The largest element of `A(f)`" is a value `v (f - h ^ p)` with `v (f - h ^ p) ≤ v (f - h' ^ p)` for each `h'`.

The hypothesis that the residue field of `v` is perfect has an elementary form (`hres`): for each `u ∈ K` with `v u ≤ 1` there is `r ∈ K` with `v r ≤ 1` and `v (u - r ^ p) < 1`. That is, each element of the valuation ring is a `p`-th power modulo the maximal ideal.

## Main results

* `Singularity.exists_valuation_sub_pow_lt`: the improvement lemma. If `v(f - h^p) = v(a^p)` with `a ≠ 0`, then there is `h'` with `v(f - h'^p) < v(f - h^p)`.
* `Singularity.valuation_sub_pow_ne_of_isLeast`: if `v(f - h^p)` is the largest element of `A(f)` in additive notation and `f ≠ h^p`, then `v(f - h^p)` is not in `pΓ`.
* `Singularity.valuation_sub_algebraMap_pow`: if `θ^p = f` in an extension `L` and `w` extends `v`, then `w(θ - h)^p = v(f - h^p)`.
* `Singularity.valuation_sub_algebraMap_ne_of_isLeast`: in the case of a largest element, `w(θ - h)` is not a value of `v`. So the value group of `w` is larger than the value group of `v`.
* `Singularity.exists_valuation_sub_pow_lt_of_not_exists`: if `A(f)` has no largest element, then each `h` has a better approximation `h'`.
* `Singularity.exists_valuation_sub_algebraMap_lt_of_not_exists`: if `A(f)` has no largest element, then for each `h ∈ K` there is `h' ∈ K` with `w(θ - h') < w(θ - h)`. So `θ` has no best approximation in `K`.
* `Singularity.ne_pow_of_not_exists`: if `A(f)` has no largest element, then `f` is not a `p`-th power in `K`.

## The proof

For the improvement lemma, put `u = (f - h^p)/a^p`. Then `v(u) = 1`, and by `hres` there is `r` with `v(u - r^p) < 1`. Take `h' = h + r a`. By `add_pow_char` we have `h'^p = h^p + r^p a^p`, so `f - h'^p = a^p (u - r^p)`, and `v(f - h'^p) = v(a^p) v(u - r^p) < v(a^p)`. The other statements follow from the improvement lemma and from `(θ - h)^p = f - h^p` (`sub_pow_char`).

## What is not proved

* The file does not prove that in the case without a largest element the extension `K(θ)/K` is immediate. It proves only that `θ` has no best approximation in `K`.
* The file does not prove that `A(f)` always has one of the two forms of the handbook in terms of cuts of the value group, and it does not classify Artin-Schreier defect extensions.
* The file does not prove local uniformization. Local uniformization and resolution of singularities in positive characteristic and dimension 4 or more are open, and this file does not prove them.

## References

* Volume 5, Chapter 4 of the handbook.
* F.-V. Kuhlmann, A classification of Artin-Schreier defect extensions and characterizations of defectless fields, Illinois J. Math. 54 (2010).
-/

namespace Singularity

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
  {p : ℕ} [Fact p.Prime] [CharP K p]

/-- **The improvement lemma** for approximation by `p`-th powers (Volume 5, Chapter 4 of the handbook). Suppose that the residue field of `v` is perfect, in the elementary form `hres`. If `v(f - h^p) = v(a^p)` with `a ≠ 0`, that is, the additive value of `f - h^p` is in `pΓ`, then there is `h'` with `v(f - h'^p) < v(f - h^p)`, that is, a larger additive value. -/
theorem exists_valuation_sub_pow_lt
    (hres : ∀ u : K, v u ≤ 1 → ∃ r : K, v r ≤ 1 ∧ v (u - r ^ p) < 1)
    {f h a : K} (ha : a ≠ 0) (hfa : v (f - h ^ p) = v (a ^ p)) :
    ∃ h' : K, v (f - h' ^ p) < v (f - h ^ p) := by
  have hap : a ^ p ≠ 0 := pow_ne_zero _ ha
  have hpos : 0 < v (a ^ p) := by
    rw [zero_lt_iff, Valuation.ne_zero_iff]
    exact hap
  have hu : v ((f - h ^ p) / a ^ p) = 1 := by
    rw [map_div₀, hfa, div_self hpos.ne']
  obtain ⟨r, -, hr⟩ := hres _ hu.le
  refine ⟨h + r * a, ?_⟩
  have key : f - (h + r * a) ^ p = a ^ p * ((f - h ^ p) / a ^ p - r ^ p) := by
    rw [add_pow_char, mul_sub, mul_div_cancel₀ _ hap, mul_pow]
    ring
  rw [key, map_mul, hfa]
  exact mul_lt_of_lt_one_right hpos hr

/-- Volume 5, Chapter 4 of the handbook. If `v(f - h^p)` is the largest element of `A(f) = {v(f - h'^p)}` in additive notation (the smallest in multiplicative notation) and `f ≠ h^p`, then `v(f - h^p)` is not the value of a `p`-th power, that is, it is not in `pΓ`. -/
theorem valuation_sub_pow_ne_of_isLeast
    (hres : ∀ u : K, v u ≤ 1 → ∃ r : K, v r ≤ 1 ∧ v (u - r ^ p) < 1)
    {f h : K} (hmax : ∀ h' : K, v (f - h ^ p) ≤ v (f - h' ^ p)) (hne : f ≠ h ^ p) (a : K) :
    v (f - h ^ p) ≠ v (a ^ p) := by
  intro hfa
  by_cases ha : a = 0
  · rw [ha, zero_pow (Fact.out : p.Prime).ne_zero, map_zero, Valuation.zero_iff,
      sub_eq_zero] at hfa
    exact hne hfa
  · obtain ⟨h', hh'⟩ := exists_valuation_sub_pow_lt v hres ha hfa
    exact (hmax h').not_gt hh'

omit [Fact p.Prime] [CharP K p] in
/-- If `A(f)` has no largest element, then each `h ∈ K` has a better approximation: there is `h'` with `v(f - h'^p) < v(f - h^p)` (Volume 5, Chapter 4 of the handbook). -/
theorem exists_valuation_sub_pow_lt_of_not_exists {f : K}
    (hno : ¬ ∃ h : K, ∀ h' : K, v (f - h ^ p) ≤ v (f - h' ^ p)) (h : K) :
    ∃ h' : K, v (f - h' ^ p) < v (f - h ^ p) := by
  simp only [not_exists, not_forall, not_le] at hno
  exact hno h

omit [Fact p.Prime] [CharP K p] in
/-- If `A(f)` has no largest element, then `f` is not a `p`-th power in `K`. If `f = h^p`, then `v(f - h^p) = 0` is the largest element of `A(f)` in additive notation. -/
theorem ne_pow_of_not_exists {f : K}
    (hno : ¬ ∃ h : K, ∀ h' : K, v (f - h ^ p) ≤ v (f - h' ^ p)) (h : K) : f ≠ h ^ p := by
  rintro rfl
  exact hno ⟨h, fun h' => by rw [sub_self, map_zero]; exact zero_le⟩

variable {L : Type*} [Field L] [Algebra K L] (w : Valuation L Γ₀)

/-- Let `θ ∈ L` with `θ^p = f`, and let `w` be a valuation of `L` that extends `v`. Then `w(θ - h)^p = v(f - h^p)` for each `h ∈ K`, that is, `p · w(θ - h) = v(f - h^p)` in additive notation (Volume 5, Chapter 4 of the handbook). -/
theorem valuation_sub_algebraMap_pow (hw : ∀ x : K, w (algebraMap K L x) = v x)
    {f : K} {θ : L} (hθ : θ ^ p = algebraMap K L f) (h : K) :
    w (θ - algebraMap K L h) ^ p = v (f - h ^ p) := by
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  rw [← map_pow, sub_pow_char, hθ, ← map_pow, ← map_sub, hw]

/-- Volume 5, Chapter 4 of the handbook. Suppose that `v(f - h^p)` is the largest element of `A(f)` in additive notation and `f ≠ h^p`. Let `θ ∈ L` with `θ^p = f`, and let `w` extend `v`. Then `w(θ - h)` is not a value of `v`. So the value group of `w` is strictly larger than the value group of `v`. -/
theorem valuation_sub_algebraMap_ne_of_isLeast
    (hres : ∀ u : K, v u ≤ 1 → ∃ r : K, v r ≤ 1 ∧ v (u - r ^ p) < 1)
    (hw : ∀ x : K, w (algebraMap K L x) = v x) {f h : K} {θ : L}
    (hθ : θ ^ p = algebraMap K L f)
    (hmax : ∀ h' : K, v (f - h ^ p) ≤ v (f - h' ^ p)) (hne : f ≠ h ^ p) (x : K) :
    w (θ - algebraMap K L h) ≠ v x := by
  intro hx
  apply valuation_sub_pow_ne_of_isLeast v hres hmax hne x
  rw [← valuation_sub_algebraMap_pow v w hw hθ, hx, map_pow]

/-- Volume 5, Chapter 4 of the handbook. If `A(f)` has no largest element, `θ ∈ L` has `θ^p = f`, and `w` extends `v`, then for each `h ∈ K` there is `h' ∈ K` with `w(θ - h') < w(θ - h)`, that is, a larger additive value. So `θ` has no best approximation in `K`. -/
theorem exists_valuation_sub_algebraMap_lt_of_not_exists
    (hw : ∀ x : K, w (algebraMap K L x) = v x) {f : K} {θ : L}
    (hθ : θ ^ p = algebraMap K L f)
    (hno : ¬ ∃ h : K, ∀ h' : K, v (f - h ^ p) ≤ v (f - h' ^ p)) (h : K) :
    ∃ h' : K, w (θ - algebraMap K L h') < w (θ - algebraMap K L h) := by
  obtain ⟨h', hh'⟩ := exists_valuation_sub_pow_lt_of_not_exists v hno h
  refine ⟨h', lt_of_not_ge fun hle => hh'.not_ge ?_⟩
  rw [← valuation_sub_algebraMap_pow v w hw hθ, ← valuation_sub_algebraMap_pow v w hw hθ]
  exact pow_le_pow_left' hle p

end Singularity
