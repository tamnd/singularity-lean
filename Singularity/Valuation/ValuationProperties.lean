/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Valuation.Basic

/-!
# Basic properties of a valuation

This file collects the basic properties of a valuation `v` on a field `K` (Volume 3, Lemma 1.1.3 of the handbook). Each property is already in Mathlib. The file puts them in one statement.

Mathlib writes a valuation multiplicatively: `v : K → Γ₀` with `v (x + y) ≤ max (v x) (v y)`. The handbook writes it additively, with `v(x + y) ≥ min(v(x), v(y))`. So `v(1) = 0` of the handbook is `v 1 = 1` here, `-v(x)` is `(v x)⁻¹`, and `min` is `max`.

The Mathlib names of the properties are these.

* `Valuation.map_one`: `v 1 = 1`.
* `Valuation.map_neg`: `v (-x) = v x`. It gives `v (-1) = 1`.
* `map_inv₀`: `v x⁻¹ = (v x)⁻¹`.
* `Valuation.map_add_of_distinct_val`: if `v x ≠ v y`, then `v (x + y) = max (v x) (v y)`.
* `Valuation.map_sum_eq_of_lt`: if one term has a value larger than the values of the other terms, then the sum has this value.

The additive versions are `AddValuation.map_one`, `AddValuation.map_neg`, `AddValuation.map_inv` and `AddValuation.map_add_of_distinct_val`.

## Main results

* `Singularity.valuation_basic_properties`: the properties in one statement.
-/

namespace Singularity

/-- The basic properties of a valuation `v` on a field `K` (Volume 3, Lemma 1.1.3 of the handbook). The valuation is multiplicative, so `v(1) = v(-1) = 0` of the handbook is `v 1 = v (-1) = 1`, `v(x⁻¹) = -v(x)` is `v x⁻¹ = (v x)⁻¹`, and the rule for the minimum is a rule for the maximum. The last claim is the rule for a sum with a unique term of largest value. -/
theorem valuation_basic_properties {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) {ι : Type*} [DecidableEq ι] :
    v 1 = 1 ∧ v (-1) = 1 ∧ (∀ x, v (-x) = v x) ∧ (∀ x, v x⁻¹ = (v x)⁻¹) ∧
      (∀ x y, v x ≠ v y → v (x + y) = max (v x) (v y)) ∧
      ∀ (s : Finset ι) (f : ι → K) (i : ι), i ∈ s → (∀ j ∈ s, j ≠ i → v (f j) < v (f i)) →
        v (∑ j ∈ s, f j) = v (f i) := by
  refine ⟨v.map_one, by rw [Valuation.map_neg, Valuation.map_one], v.map_neg,
    fun x => map_inv₀ v x, fun x y h => v.map_add_of_distinct_val h, ?_⟩
  intro s f i hi h
  refine v.map_sum_eq_of_lt hi fun j hj => ?_
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
  exact h j hj.1 hj.2

end Singularity
