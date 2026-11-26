/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Independent classes in the graded pieces of a valuation

Let `(R, 𝔪, κ)` be a local ring with a map to a field `K`, and let `v` be a valuation of `K` with valuation ring `V` that contains the image of `R`. For a value `γ`, put `P_γ = {x ∈ R : v(x) ≥ γ}` and `P_γ^+ = {x ∈ R : v(x) > γ}`. Volume 3, Lemma 2.3.1 of the handbook says: let `z_1, ..., z_n ∈ R` with `v(z_k) = γ`, such that the residues of the quotients `z_k / z_1` are linearly independent over `κ`. Then the classes of the `z_k` in the `κ`-vector space `P_γ / P_γ^+` are linearly independent.

This file proves the lemma in an elementary form, without the quotient `P_γ / P_γ^+`. Let `c_1, ..., c_n ∈ R` with `v(∑ c_k z_k) > γ`, that is `∑ c_k z_k ∈ P_γ^+`. Then each `c_k` is in `𝔪`, so its class in `κ` is `0`. This is the linear independence of the classes.

The proof follows the handbook. Divide `∑ c_k z_k` by `z_j`. The result `∑ c_k (z_k / z_j)` has value `< 1`, so its residue `∑ c̄_k (z_k / z_j)‾` is `0`. By the independence of the residues, each `c̄_k` is `0`.

The hypotheses are weaker than in the handbook. The ring `R` need not be a Noetherian domain, and the map `R → K` need not be injective. The field `κ` maps to `Kv` by any map that is compatible with the residue maps. It is not necessary that `v(z_k) = γ` for each `k`: it is sufficient that `z_k / z_j ∈ V`.

## Main results

* `Singularity.mem_maximalIdeal_of_valuation_sum_lt`: the lemma.
-/

open IsLocalRing

namespace Singularity

/-- **Independent classes in `P_γ / P_γ^+`** (Volume 3, Lemma 2.3.1 of the handbook). Let `R` be a local ring with residue field `κ` and a map to a field `K`, and let `V` be a valuation ring of `K` that contains the image of `R`. Let `κ` map to `Kv`, compatibly with the residue maps. Let `z_1, ..., z_n ∈ R`, let `z_j ≠ 0` in `K`, and let `u_k ∈ V` with `u_k z_j = z_k`. Assume that the residues of the `u_k` are linearly independent over `κ`. Let `c_1, ..., c_n ∈ R` with `v(∑ c_k z_k) > v(z_j)`. Then each `c_k` is in the maximal ideal of `R`. -/
theorem mem_maximalIdeal_of_valuation_sum_lt {K : Type*} [Field K] {R : Type*} [CommRing R]
    [IsLocalRing R] [Algebra R K] (V : ValuationSubring K) (hRV : ∀ r, algebraMap R K r ∈ V)
    [Algebra (ResidueField R) (ResidueField V)]
    (hres : ∀ r, algebraMap (ResidueField R) (ResidueField V) (residue R r) =
      residue V ⟨algebraMap R K r, hRV r⟩)
    {n : Type*} [Fintype n] {z : n → R} {j : n} (hz0 : algebraMap R K (z j) ≠ 0)
    {u : n → V} (hu : ∀ i, (u i : K) * algebraMap R K (z j) = algebraMap R K (z i))
    (hind : LinearIndependent (ResidueField R) fun i => residue V (u i)) (c : n → R)
    (hc : V.valuation (algebraMap R K (∑ i, c i * z i)) < V.valuation (algebraMap R K (z j))) :
    ∀ i, c i ∈ maximalIdeal R := by
  classical
  have hpos : 0 < V.valuation (algebraMap R K (z j)) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr hz0
  obtain ⟨w, hwdef⟩ : ∃ w : V, w = ∑ i, (⟨algebraMap R K (c i), hRV (c i)⟩ : V) * u i :=
    ⟨_, rfl⟩
  have hw : (w : K) * algebraMap R K (z j) = algebraMap R K (∑ i, c i * z i) := by
    rw [hwdef]
    push_cast
    try simp only [map_sum, map_mul]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, hu i]
  have hw1 : V.valuation (w : K) < 1 := by
    rw [← hw, map_mul] at hc
    exact (mul_lt_iff_lt_one_left hpos).mp hc
  have hw0 : residue V w = 0 :=
    (residue_eq_zero_iff w).mpr ((V.valuation_lt_one_iff w).mpr hw1)
  have hrel : ∑ i, residue R (c i) • residue V (u i) = 0 := by
    rw [← hw0, hwdef, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, hres, map_mul]
  intro i
  exact (residue_eq_zero_iff _).mp (Fintype.linearIndependent_iff.mp hind _ hrel i)

end Singularity
