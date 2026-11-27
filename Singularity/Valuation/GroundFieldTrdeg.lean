/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.AbhyankarSubfield

/-!
# The transcendence degree over the new ground field

Let `V` be a valuation ring of a field `K` over `k`, and let `y_1, ..., y_m ∈ V` have residues that are algebraically independent over `k`. Volume 5, Lemma 1.4.2 of the handbook replaces the ground field `k` by `k' = k(y_1, ..., y_m)`. The first claims of the lemma are in `Singularity/Valuation/MonomialGroundField.lean`: the `y_i` are algebraically independent (`Singularity.algebraicIndependent_of_residue`), `k' ⊆ V` (`Singularity.mem_of_mem_adjoin_residue`), and local uniformization over `k'` gives local uniformization over `k` (`Singularity.HasLocalUniformization.of_intermediateField`).

This file proves the formula for the transcendence degree in the last claim. If the residues form a transcendence basis of `κ_v` over `k`, then `trdeg_{k'} K + trdeg_k κ_v = trdeg_k K` (`trdeg_adjoin_add_trdeg_residueField`). This is the formula `trdeg_{k'} K = trdeg_k K - trdeg_k κ_v` of the handbook, written with a sum of cardinals, so that it holds also when the degrees are infinite. The claim that `V` is zero-dimensional over `k'` is not proved.

## Main results

* `Singularity.isTranscendenceBasis_adjoinRangeElem`: algebraically independent elements `y_i` are a transcendence basis of `k(y)` over `k`.
* `Singularity.cardinalMk_add_trdeg_adjoin`: `m + trdeg_{k(y)} K = trdeg_k K` for `m` algebraically independent elements `y_i`.
* `Singularity.trdeg_adjoin_add_trdeg_residueField`: the formula of Lemma 1.4.2.
-/

open IsLocalRing Cardinal

namespace Singularity

universe u

variable {k : Type*} {K : Type u} [Field k] [Field K] [Algebra k K]

/-- Let `y_i` be algebraically independent over `k`. Then the `y_i` are a transcendence basis of `k(y)` over `k`. -/
theorem isTranscendenceBasis_adjoinRangeElem {ι : Type*} {y : ι → K}
    (hy : AlgebraicIndependent k y) : IsTranscendenceBasis k (adjoinRangeElem k y) := by
  have hyF : AlgebraicIndependent k (adjoinRangeElem k y) :=
    AlgebraicIndependent.of_comp
      (IsScalarTower.toAlgHom k (IntermediateField.adjoin k (Set.range y)) K) hy
  refine hyF.isTranscendenceBasis_iff_isAlgebraic.mpr ?_
  refine IntermediateField.isAlgebraic_adjoin_iff_top.mp ⟨fun a => ?_⟩
  have ha : a ∈ IntermediateField.adjoin k (Set.range (adjoinRangeElem k y)) := by
    rw [adjoin_range_adjoinRangeElem]
    exact IntermediateField.mem_top
  exact isAlgebraic_algebraMap
    (⟨a, ha⟩ : IntermediateField.adjoin k (Set.range (adjoinRangeElem k y)))

/-- Let `y_i`, for `i ∈ ι`, be algebraically independent over `k`. Then `|ι| + trdeg_{k(y)} K = trdeg_k K`. -/
theorem cardinalMk_add_trdeg_adjoin {ι : Type u} {y : ι → K} (hy : AlgebraicIndependent k y) :
    #ι + Algebra.trdeg (IntermediateField.adjoin k (Set.range y)) K = Algebra.trdeg k K := by
  haveI : FaithfulSMul k (IntermediateField.adjoin k (Set.range y)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap _ _).injective
  haveI : FaithfulSMul (IntermediateField.adjoin k (Set.range y)) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap _ _).injective
  rw [(isTranscendenceBasis_adjoinRangeElem hy).cardinalMk_eq_trdeg]
  exact trdeg_add_eq k (IntermediateField.adjoin k (Set.range y)) K

variable {V : ValuationSubring K} [Algebra k V] [IsScalarTower k V K]

/-- **Volume 5, Lemma 1.4.2 of the handbook**, the formula for the transcendence degree. Let `y_i ∈ V` have residues that form a transcendence basis of `κ_v` over `k`, and let `k' = k(y)`. Then `trdeg_{k'} K + trdeg_k κ_v = trdeg_k K`. -/
theorem trdeg_adjoin_add_trdeg_residueField {ι : Type u} {y : ι → V}
    (hy : IsTranscendenceBasis k fun i => residue V (y i)) :
    Algebra.trdeg (IntermediateField.adjoin k (Set.range fun i => (y i : K))) K +
        Algebra.trdeg k (ResidueField V) = Algebra.trdeg k K := by
  rw [← hy.cardinalMk_eq_trdeg, add_comm]
  exact cardinalMk_add_trdeg_adjoin (algebraicIndependent_of_residue hy.1)

end Singularity
