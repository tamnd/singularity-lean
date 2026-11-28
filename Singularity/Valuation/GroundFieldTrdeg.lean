/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.AbhyankarSubfield

/-!
# The transcendence degree over the new ground field

Let `V` be a valuation ring of a field `K` over `k`, and let `y_1, ..., y_m ∈ V` have residues that are algebraically independent over `k`. Volume 5, Lemma 1.4.2 of the handbook replaces the ground field `k` by `k' = k(y_1, ..., y_m)`. The first claims of the lemma are in `Singularity/Valuation/MonomialGroundField.lean`: the `y_i` are algebraically independent (`Singularity.algebraicIndependent_of_residue`), `k' ⊆ V` (`Singularity.mem_of_mem_adjoin_residue`), and local uniformization over `k'` gives local uniformization over `k` (`Singularity.HasLocalUniformization.of_intermediateField`).

This file proves the formula for the transcendence degree in the last claim. If the residues form a transcendence basis of `κ_v` over `k`, then `trdeg_{k'} K + trdeg_k κ_v = trdeg_k K` (`trdeg_adjoin_add_trdeg_residueField`). This is the formula `trdeg_{k'} K = trdeg_k K - trdeg_k κ_v` of the handbook, written with a sum of cardinals, so that it holds also when the degrees are infinite. The file also proves that `V` is zero-dimensional over `k'`. The map `k' → κ_v` that sends an element of `k'` to its residue is a homomorphism of `k`-algebras (`residueAdjoinHom`), and `κ_v` is algebraic over its image (`isAlgebraic_range_residueAdjoinHom`).

## Main results

* `Singularity.isTranscendenceBasis_adjoinRangeElem`: algebraically independent elements `y_i` are a transcendence basis of `k(y)` over `k`.
* `Singularity.cardinalMk_add_trdeg_adjoin`: `m + trdeg_{k(y)} K = trdeg_k K` for `m` algebraically independent elements `y_i`.
* `Singularity.trdeg_adjoin_add_trdeg_residueField`: the formula of Lemma 1.4.2.
* `Singularity.residueAdjoinHom`: the residue map `k' → κ_v`.
* `Singularity.isAlgebraic_range_residueAdjoinHom`: `κ_v` is algebraic over the image of `k'`.
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
  have : FaithfulSMul k (IntermediateField.adjoin k (Set.range y)) :=
    (faithfulSMul_iff_algebraMap_injective k (IntermediateField.adjoin k (Set.range y))).mpr
      (RingHom.injective (algebraMap k (IntermediateField.adjoin k (Set.range y))))
  have : FaithfulSMul (IntermediateField.adjoin k (Set.range y)) K :=
    (faithfulSMul_iff_algebraMap_injective (IntermediateField.adjoin k (Set.range y)) K).mpr
      (RingHom.injective (algebraMap (IntermediateField.adjoin k (Set.range y)) K))
  rw [(isTranscendenceBasis_adjoinRangeElem hy).cardinalMk_eq_trdeg]
  exact trdeg_add_eq k (IntermediateField.adjoin k (Set.range y))

variable {V : ValuationSubring K} [Algebra k V] [IsScalarTower k V K]

/-- **Volume 5, Lemma 1.4.2 of the handbook**, the formula for the transcendence degree. Let `y_i ∈ V` have residues that form a transcendence basis of `κ_v` over `k`, and let `k' = k(y)`. Then `trdeg_{k'} K + trdeg_k κ_v = trdeg_k K`. -/
theorem trdeg_adjoin_add_trdeg_residueField {ι : Type u} {y : ι → V}
    (hy : IsTranscendenceBasis k fun i => residue V (y i)) :
    Algebra.trdeg (IntermediateField.adjoin k (Set.range fun i => (y i : K))) K +
        Algebra.trdeg k (ResidueField V) = Algebra.trdeg k K := by
  rw [← hy.cardinalMk_eq_trdeg, add_comm]
  exact cardinalMk_add_trdeg_adjoin (algebraicIndependent_of_residue hy.1)

section ResidueAlgebraic

variable {V : ValuationSubring K} [Algebra k V] [IsScalarTower k V K] {κ : Type*} {y : κ → V}

/-- Let `y_1, ..., y_m ∈ V` have residues that are algebraically independent over `k`. Then
`k' = k(y_1, ..., y_m)` lies in `V` (`Singularity.mem_of_mem_adjoin_residue`), and this is the
residue map `k' → κ_v`. -/
noncomputable def residueAdjoinHom (hy : AlgebraicIndependent k fun i => residue V (y i)) :
    IntermediateField.adjoin k (Set.range fun i => (y i : K)) →ₐ[k] ResidueField V :=
  { (residue V).comp
      (RingHom.codRestrict
        (IntermediateField.adjoin k (Set.range fun i => (y i : K))).val.toRingHom V
        fun c => mem_of_mem_adjoin_residue hy c.2) with
    commutes' := fun a => by
      change residue V ⟨algebraMap k K a, _⟩ = algebraMap k (ResidueField V) a
      rw [IsScalarTower.algebraMap_apply k V (ResidueField V)]
      congr 1
      exact Subtype.ext (IsScalarTower.algebraMap_apply k V K a) }

/-- **Volume 5, Lemma 1.4.2 of the handbook**, the residue field is algebraic over the new
ground field. Let `y_i ∈ V` have residues that form a transcendence basis of `κ_v` over `k`, and
let `k' = k(y)`. Then `κ_v` is algebraic over the image of `k'` in `κ_v`. -/
theorem isAlgebraic_range_residueAdjoinHom
    (hy : IsTranscendenceBasis k fun i => residue V (y i)) :
    Algebra.IsAlgebraic (residueAdjoinHom hy.1).range (ResidueField V) := by
  have hle : Algebra.adjoin k (Set.range fun i => residue V (y i)) ≤
      (residueAdjoinHom hy.1).range := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨(y i : K), IntermediateField.subset_adjoin k _ ⟨i, rfl⟩⟩, rfl⟩
  have halg := hy.isAlgebraic
  exact ⟨fun x => (halg.isAlgebraic x).tower_top_of_subalgebra_le hle⟩

end ResidueAlgebraic

end Singularity
