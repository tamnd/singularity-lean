/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.EtaleGeneratorExistence

/-!
# Local uniformization over a monomial subfield, the case of one extension

Let `k ⊆ K₀ ⊆ K` be fields with `[K : K₀]` finite, let `v` be a valuation of `K`, and let `v₀` be its restriction to `K₀`. This file proves that `v` has local uniformization over `k` in the following case.

1. The valuation `v₀` is monomial. Either `v₀` is trivial on a subfield `k(y_1, ..., y_t)` of `K₀` and is a monomial valuation of `K₀ = k(y)(x_1, ..., x_r)` over `k(y)`, or `v₀` is a monomial valuation of `K₀ = k(x_1, ..., x_r)` over `k`.
2. The residue extension of `v` over `v₀` is separable of degree `[K : K₀]`.

This is the proof of the theorem of Knaf-Kuhlmann (Volume 5, Theorem 2.2.1 of the handbook) in the case without ramification, without defect and without splitting of `v₀` in `K`. By the fundamental inequality, condition 2 says that `e = 1`, `d = 1`, and that `v` is the only extension of `v₀` to `K`. The proof composes three results of the library.

* The monomial case over `k(y)` (Volume 5, Corollary 2.1.6) gives local uniformization of `v₀` over `k` (`Singularity.hasLocalUniformization_of_isMonomialValuation_adjoin`).
* Condition 2 gives an étale generator of `K/K₀` at `v` (Volume 5, Lemma 1.3.3, second part, in the case of one extension, `Singularity.exists_isEtaleGenerator_of_finrank_residueField_eq`).
* Local uniformization lifts along an étale generator (Volume 5, Theorem 1.3.4, `Singularity.hasLocalUniformization_of_etaleGenerator`).

The glue is the equality of the valuation ring of `v₀` with the inverse image in `K₀` of the valuation ring of `v` (`Singularity.comap_valuationSubring_eq_of_hasExtension`).

The general theorem of Knaf-Kuhlmann needs more. In general `[Kv : K₀v₀]` is less than `[K : K₀]`, because `v₀` can have several extensions to `K`. Then the proof in the handbook uses the henselization for Lemma 1.3.3, and the generalized stability theorem of Kuhlmann to show that the defect is 1. These are not in the library. This file does not prove `Singularity.localUniformization_abhyankar`.

## Main results

* `Singularity.hasLocalUniformization_of_finrank_residueField_eq`: if the residue extension is separable of degree `[K : K₀]` and `v₀` has local uniformization over `k`, then `v` has local uniformization over `k`.
* `Singularity.hasLocalUniformization_of_monomial_of_finrank_residueField_eq`: the case where `v₀` is trivial on `k(y)` and a monomial valuation of `K₀` over `k(y)`.
* `Singularity.hasLocalUniformization_of_isMonomialValuation_of_finrank_residueField_eq`: the case where `v₀` is a monomial valuation of `K₀` over `k`.
* `Singularity.finrank_residueField_eq_of_eq_top`: for `K₀ = K` the residue extension has degree `1 = [K : K₀]`, and it is separable. So the hypotheses on the residue extension hold in this case, for each valuation.
-/

open IsLocalRing

namespace Singularity

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section Glue

variable {K₀ : IntermediateField k K} {Γ₀ Γ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [LinearOrderedCommGroupWithZero Γ] (v₀ : Valuation K₀ Γ₀) (v : Valuation K Γ) [v₀.HasExtension v]

/-- If the valuation `v` of `K` extends the valuation `v₀` of the subfield `K₀`, then the valuation ring of `v₀` is the inverse image in `K₀` of the valuation ring of `v`. -/
theorem comap_valuationSubring_eq_of_hasExtension :
    v.valuationSubring.comap (algebraMap K₀ K) = v₀.valuationSubring := by
  ext c
  rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
    Valuation.mem_valuationSubring_iff, Valuation.HasExtension.val_map_le_one_iff v₀ v]

/-- **Lifting in the case of one extension** (Volume 5, Lemma 1.3.3 and Theorem 1.3.4 of the handbook). Let `K₀` be a subfield of `K` that contains `k`, with `[K : K₀]` finite. Let the valuation `v` of `K` extend the valuation `v₀` of `K₀`, and assume that the residue extension of `v` over `v₀` is separable of degree `[K : K₀]`. If `v₀` has local uniformization as a valuation of `K₀/k`, then `v` has local uniformization as a valuation of `K/k`.

The hypothesis on the residue extension gives an étale generator of `K/K₀` at `v` (`Singularity.exists_isEtaleGenerator_of_finrank_residueField_eq`), and local uniformization lifts along it (`Singularity.hasLocalUniformization_of_etaleGenerator`). -/
theorem hasLocalUniformization_of_finrank_residueField_eq [FiniteDimensional K₀ K]
    [Algebra.IsSeparable (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring)]
    (hf : Module.finrank (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring) =
      Module.finrank K₀ K)
    (h : HasLocalUniformization k v₀.valuationSubring) :
    HasLocalUniformization k v.valuationSubring := by
  obtain ⟨-, z, hz⟩ := exists_isEtaleGenerator_of_finrank_residueField_eq v₀ v hf
  refine hasLocalUniformization_of_etaleGenerator hz ?_
  rw [comap_valuationSubring_eq_of_hasExtension v₀ v]
  exact h

/-- **Local uniformization over a monomial subfield, without ramification, defect and splitting** (Volume 5, Theorem 2.2.1 of the handbook, in the case of one extension with `e = d = 1`). Let `K₀` be a subfield of `K` that contains `k`, with `[K : K₀]` finite. Let the valuation `v` of `K` extend the valuation `v₀` of `K₀`. Assume the following.

1. There are `y_1, ..., y_t ∈ K₀` such that `v₀` is trivial on `k(y)`, and `v₀` is a monomial valuation of `K₀ = k(y)(x_1, ..., x_r)` over `k(y)`.
2. The residue extension of `v` over `v₀` is separable of degree `[K : K₀]`.

Then `v` has local uniformization as a valuation of `K/k`.

This is the proof of the theorem of Knaf-Kuhlmann in the handbook, in the case where the reduction of `v₀` to `K` has no ramification, no defect and no splitting: by the fundamental inequality, condition 2 says that `e = d = 1` and that `v` is the only extension of `v₀` to `K`. The general theorem allows several extensions of `v₀`, and it needs the henselization and the generalized stability theorem of Kuhlmann. These are not proved here, and this theorem is not `Singularity.localUniformization_abhyankar`. -/
theorem hasLocalUniformization_of_monomial_of_finrank_residueField_eq [FiniteDimensional K₀ K]
    [Algebra.IsSeparable (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring)]
    (hf : Module.finrank (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring) =
      Module.finrank K₀ K)
    {κ ι : Type*} [Fintype κ] [Fintype ι] {y : κ → K₀} {x : ι → K₀}
    (hyV : ∀ c ∈ IntermediateField.adjoin k (Set.range y), c ∈ v₀.valuationSubring)
    (hV : IsMonomialValuation (IntermediateField.adjoin k (Set.range y)) v₀.valuationSubring x) :
    HasLocalUniformization k v.valuationSubring :=
  hasLocalUniformization_of_finrank_residueField_eq v₀ v hf
    (hasLocalUniformization_of_isMonomialValuation_adjoin hyV hV)

/-- **Local uniformization over a monomial subfield, the case over `k`** (Volume 5, Theorem 2.2.1 of the handbook, in the case of one extension with `e = d = 1` and `t = 0`). Let `K₀` be a subfield of `K` that contains `k`, with `[K : K₀]` finite. Let the valuation `v` of `K` extend the valuation `v₀` of `K₀`. Assume that `v₀` is a monomial valuation of `K₀ = k(x_1, ..., x_r)` over `k`, and that the residue extension of `v` over `v₀` is separable of degree `[K : K₀]`. Then `v` has local uniformization as a valuation of `K/k`.

As in `Singularity.hasLocalUniformization_of_monomial_of_finrank_residueField_eq`, this is the case without ramification, defect and splitting of the theorem of Knaf-Kuhlmann. The monomial case is `Singularity.hasLocalUniformization_of_isMonomialValuation`. -/
theorem hasLocalUniformization_of_isMonomialValuation_of_finrank_residueField_eq
    [FiniteDimensional K₀ K]
    [Algebra.IsSeparable (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring)]
    (hf : Module.finrank (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring) =
      Module.finrank K₀ K)
    [Algebra k v₀.valuationSubring] [IsScalarTower k v₀.valuationSubring K₀]
    {ι : Type*} [Fintype ι] {x : ι → K₀} (hV : IsMonomialValuation k v₀.valuationSubring x) :
    HasLocalUniformization k v.valuationSubring :=
  hasLocalUniformization_of_finrank_residueField_eq v₀ v hf
    (hasLocalUniformization_of_isMonomialValuation hV)

end Glue

section Top

variable {Γ₀ Γ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ]
  (v₀ : Valuation (⊤ : IntermediateField k K) Γ₀) (v : Valuation K Γ) [v₀.HasExtension v]

/-- For `K₀ = K`, the map of residue fields is bijective. -/
theorem bijective_algebraMap_residueField_of_eq_top :
    Function.Bijective
      (algebraMap (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring)) := by
  refine ⟨(algebraMap (ResidueField v₀.valuationSubring)
    (ResidueField v.valuationSubring)).injective, fun w => ?_⟩
  obtain ⟨z, rfl⟩ := residue_surjective w
  have hz : (⟨(z : K), trivial⟩ : (⊤ : IntermediateField k K)) ∈ v₀.valuationSubring := by
    rw [← comap_valuationSubring_eq_of_hasExtension v₀ v]
    exact z.2
  exact ⟨residue v₀.valuationSubring ⟨_, hz⟩, rfl⟩

/-- **The hypotheses on the residue field for `K₀ = K`.** Let `v₀` be the restriction of the valuation `v` of `K` to the subfield `K₀ = K`. Then the residue extension of `v` over `v₀` is separable, and its degree is `1 = [K : K₀]`. So the hypotheses on the residue extension in `Singularity.hasLocalUniformization_of_monomial_of_finrank_residueField_eq` hold, for each valuation `v`. With these hypotheses, that theorem gives local uniformization for each valuation of `K/k` that is a monomial valuation of `K` over a subfield `k(y)` on which it is trivial. -/
theorem finrank_residueField_eq_of_eq_top :
    Algebra.IsSeparable (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring) ∧
      Module.finrank (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring) =
        Module.finrank (⊤ : IntermediateField k K) K := by
  have hb := bijective_algebraMap_residueField_of_eq_top v₀ v
  refine ⟨?_, ?_⟩
  · exact Algebra.IsSeparable.of_algHom _ _
      (AlgEquiv.ofBijective (Algebra.ofId _ _) hb).symm.toAlgHom
  · rw [Module.finrank_of_bijective_algebraMap hb, IntermediateField.finrank_top]

/- The hypotheses fit together for `K₀ = K`: a valuation of `K/k` whose restriction to `K₀ = K` is trivial on `k(y)` and monomial over `k(y)` has local uniformization over `k`. -/
example {κ ι : Type*} [Fintype κ] [Fintype ι] {y : κ → (⊤ : IntermediateField k K)}
    {x : ι → (⊤ : IntermediateField k K)}
    (hyV : ∀ c ∈ IntermediateField.adjoin k (Set.range y), c ∈ v₀.valuationSubring)
    (hV : IsMonomialValuation (IntermediateField.adjoin k (Set.range y)) v₀.valuationSubring x) :
    HasLocalUniformization k v.valuationSubring := by
  obtain ⟨hs, hf⟩ := finrank_residueField_eq_of_eq_top v₀ v
  have := hs
  have : FiniteDimensional (⊤ : IntermediateField k K) K :=
    Module.finite_of_finrank_pos (by rw [IntermediateField.finrank_top]; exact one_pos)
  exact hasLocalUniformization_of_monomial_of_finrank_residueField_eq v₀ v hf hyV hV

end Top

end Singularity
