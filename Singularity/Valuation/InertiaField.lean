/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.DegreePTowers
import Singularity.Valuation.MonomialFiniteExtension
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# Local uniformization from the decomposition field to the inertia field

Step 4 of the reduction of Cossart-Piltant (Volume 6, Proposition 2.2.1 of the handbook, [CP19, Proposition 4.10]) uses the ramification theory of valuations [ZS2, Chapter VI]. Let `L/K` be a finite Galois extension with group `G`, and let `W` be a valuation subring of `L`. The decomposition group `D` is the stabilizer of `W` in `G`, and the inertia group `I ⊆ D` is the subgroup that acts trivially on the residue field of `W`. Their fixed fields are the decomposition field `K^Z` and the inertia field `K^T`, with `K ⊆ K^Z ⊆ K^T ⊆ L`. This file proves the unramified part of Step 4 between `K^Z` and `K^T`: local uniformization goes up from `W ∩ K^Z` to `W ∩ K^T`.

The file has these parts.

(a) `Singularity.inertiaGroup K W` and `Singularity.inertiaField K W`. An automorphism `σ` of `L/K` is in the inertia group if `σ` maps `W` onto `W` and `w(σ x - x) < 1` for each `x ∈ W`.

(b) `Singularity.finiteDimensional_residueField_and_finrank_le`. Let `E'/E` be a finite extension, and let the valuation `v` of `E'` extend the valuation `v₀` of `E`. Then the residue extension is finite of degree at most `[E' : E]`.

(c) `Singularity.isSeparable_and_finrank_residueField_inertiaField`. Assume that each `K`-automorphism of `L` maps `W` into `W`, that is, `K` contains the decomposition field. Then the residue extension of `W ∩ K^T` over `W ∩ K` is separable of degree `[K^T : K]`. The proof uses the invariant theory of Mathlib (`Algebra.IsInvariant`). The group `G` acts on the valuation ring `B` of `W`, and `B^G` is the valuation ring of `W ∩ K`. So the residue extension of `W` over `W ∩ K` is normal, and `G` maps onto its automorphism group (`Ideal.Quotient.stabilizerHom_surjective`). The kernel is in `I`. The same argument for `I` shows that the residue field of `W` has no automorphism over the residue field of `W ∩ K^T`. A count of separable degrees with (b) gives the result.

(d) `Singularity.hasLocalUniformization_of_finrank_residueField_eq_of_algebra`: the lifting theorem `Singularity.hasLocalUniformization_of_finrank_residueField_eq` for an extension `E'/E` that is given as an algebra.

(e) `Singularity.hasLocalUniformization_inertiaField`. Let `L/K` be a finite Galois extension of extensions of `k`, and assume that `K` contains the decomposition field of `W`. If `W ∩ K` has local uniformization over `k`, then `W ∩ K^T` has local uniformization over `k`. By (c) there is an étale generator of `K^T/K` at `W ∩ K^T`, and local uniformization lifts along it.

(f) `Singularity.hasLocalUniformization_inertiaField_decompositionField`: the same result for a general finite Galois extension `L/K`, from the decomposition field `K^Z` of `W` to the inertia field of `W` over `K^Z`.

## What is not proved

The results of this file are unconditional, but they are only one part of Step 4. These parts are not proved.

* The passage from `K` to the decomposition field `K^Z`. The valuation `W ∩ K` can have several extensions to `L`, and the proof of [CP19] goes through the henselization. The library does not have it.
* The tame part from the inertia field to the ramification field. This extension is totally ramified and abelian of degree prime to `p`. [CP19] refers to the proof of [CP08, Theorem 8.1] and to [CP19, Proposition 4.13]. These results are not in Lean.
* The passage down from `K^r` to `K`, Steps 1 and 2 of the reduction, and the Galois steps of degree `p` (`Singularity.LocalUniformizationGaloisStep`, an explicit hypothesis in `Singularity.hasLocalUniformization_of_isGalois`).

## References

* [CP08] V. Cossart and O. Piltant, *Resolution of singularities of threefolds in positive characteristic I*, J. Algebra 320 (2008).
* [CP19] V. Cossart and O. Piltant, *Resolution of singularities of arithmetical threefolds*, J. Algebra 529 (2019).
* [ZS2] O. Zariski and P. Samuel, *Commutative Algebra*, Volume II.
-/

open IntermediateField IsLocalRing Module

namespace Singularity

section FieldTheory

variable (F E : Type*) [Field F] [Field E] [Algebra F E]

/-- For a normal extension `E/F`, the separable degree is the number of `F`-automorphisms of `E`. -/
theorem finSepDegree_eq_card_algEquiv [Normal F E] :
    Field.finSepDegree F E = Nat.card (E ≃ₐ[F] E) := by
  rw [Field.finSepDegree_eq_of_adjoin_splits F E E (S := Set.univ) (adjoin_univ F E)
    fun s _ => ⟨‹Normal F E›.isIntegral s, ‹Normal F E›.splits s⟩]
  exact Nat.card_congr (Algebra.IsAlgebraic.algEquivEquivAlgHom F E).toEquiv.symm

variable {F E} {M : Type*} [Field M] [Algebra F M] [Algebra M E] [IsScalarTower F M E]

/-- Let `F ⊆ M ⊆ E` be fields with `E/F` finite. Assume that `E/F` and `E/M` are normal, that the only `M`-automorphism of `E` is the identity, that `E/F` has at least `d` automorphisms, and that `[M : F] ≤ d`. Then `M/F` is separable of degree `d`. The separable degree of `E/F` is the number of its automorphisms, and the separable degree of `E/M` is `1`. So the separable degree of `M/F` is at least `d`. It is at most `[M : F] ≤ d`. -/
theorem isSeparable_and_finrank_eq_of_normal [FiniteDimensional F E] [Normal F E] [Normal M E]
    (hM : ∀ σ : E ≃ₐ[M] E, σ = 1) {d : ℕ} (hd : d ≤ Nat.card (E ≃ₐ[F] E))
    (hle : finrank F M ≤ d) : Algebra.IsSeparable F M ∧ finrank F M = d := by
  have : FiniteDimensional F M := FiniteDimensional.left F M E
  have : FiniteDimensional M E := FiniteDimensional.right F M E
  have h1 : Field.finSepDegree M E = 1 := by
    rw [finSepDegree_eq_card_algEquiv M E, Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => (hM a).trans (hM b).symm⟩, inferInstance⟩
  have h2 := Field.finSepDegree_mul_finSepDegree_of_isAlgebraic F M E
  rw [h1, mul_one, finSepDegree_eq_card_algEquiv F E] at h2
  have h3 := Field.finSepDegree_le_finrank F M
  have h4 : Nat.card (E ≃ₐ[F] E) ≤ finrank F M := by rw [← h2]; exact h3
  have heq : finrank F M = d := le_antisymm hle (hd.trans h4)
  refine ⟨(Field.finSepDegree_eq_finrank_iff F M).1 (le_antisymm h3 ?_), heq⟩
  rw [h2, heq]
  exact hd

end FieldTheory

section ResidueDegree

variable {E E' : Type*} [Field E] [Field E'] [Algebra E E'] {Γ₀ Γ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ]
  (v₀ : Valuation E Γ₀) (v : Valuation E' Γ) [v₀.HasExtension v]

/-- Lifts of residues that are linearly independent over the residue field of `v₀` are linearly independent over `E`. Divide a relation by a coefficient of largest value and reduce it. -/
theorem linearIndependent_of_residue {ι : Type*} (b : ι → v.valuationSubring)
    (hb : LinearIndependent (ResidueField v₀.valuationSubring)
      fun i => residue v.valuationSubring (b i)) :
    LinearIndependent E fun i => (b i : E') := by
  classical
  rw [linearIndependent_iff']
  intro t g hg i hi
  by_contra hgi
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image t (fun i => v₀ (g i)) ⟨i, hi⟩
  have hgj : g j ≠ 0 := by
    intro h0
    have := hjmax i hi
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact hgi this
  have hmem : ∀ l ∈ t, v₀ (g l / g j) ≤ 1 := by
    intro l hl
    rw [map_div₀, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hgj))]
    exact hjmax l hl
  set h : ι → v₀.valuationSubring := fun l =>
    if hl : l ∈ t then ⟨g l / g j, hmem l hl⟩ else 0 with hh
  have hsum : ∑ l ∈ t, h l • b l = 0 := by
    apply Subtype.ext
    change _ = (0 : E')
    have : ∑ l ∈ t, (g l / g j) • (b l : E') = 0 := by
      simp_rw [div_eq_mul_inv, mul_comm (g _), mul_smul]
      rw [← Finset.smul_sum, hg, smul_zero]
    rw [← this]
    push_cast
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Valuation.HasExtension.val_smul]
    simp [hh, hl]
  have hres := congrArg (residue v.valuationSubring) hsum
  rw [map_sum, map_zero] at hres
  have hres' : ∑ l ∈ t,
      residue v₀.valuationSubring (h l) • residue v.valuationSubring (b l) = 0 := by
    rw [← hres]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, ResidueField.algebraMap_residue]
  have h0 := linearIndependent_iff'.1 hb t _ hres' j hj
  have h1 : h j = 1 := by
    apply Subtype.ext
    simp [hh, hj, div_self hgj]
  rw [h1, map_one] at h0
  exact one_ne_zero h0

/-- The residue degree is at most the degree: if `E'/E` is finite, then the residue extension of `v` over `v₀` is finite, of degree at most `[E' : E]`. -/
theorem finiteDimensional_residueField_and_finrank_le [FiniteDimensional E E'] :
    FiniteDimensional (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring) ∧
      finrank (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring) ≤
        finrank E E' := by
  have hrank :
      Module.rank (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring) ≤
        finrank E E' := by
    refine rank_le fun s hs => ?_
    choose b hb using fun i : s => residue_surjective (R := v.valuationSubring) (i : _)
    have hli : LinearIndependent (ResidueField v₀.valuationSubring)
        fun i : s => residue v.valuationSubring (b i) := by
      simpa only [hb] using hs
    have := (linearIndependent_of_residue v₀ v b hli).fintype_card_le_finrank
    simpa using this
  have hfin : FiniteDimensional (ResidueField v₀.valuationSubring)
      (ResidueField v.valuationSubring) :=
    Module.rank_lt_aleph0_iff.1 (hrank.trans_lt Cardinal.natCast_lt_aleph0)
  exact ⟨hfin, Module.finrank_le_of_rank_le hrank⟩

/-- The maximal ideal of the valuation ring of `w` consists of the elements of value less than `1`. -/
theorem mem_maximalIdeal_valuationSubring_iff {L Γ : Type*} [Field L]
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ) (b : w.valuationSubring) :
    b ∈ maximalIdeal w.valuationSubring ↔ w b < 1 := by
  rw [ValuationSubring.valuation_lt_one_iff]
  exact (Valuation.isEquiv_valuation_valuationSubring w).lt_one_iff_lt_one.symm

end ResidueDegree

section Extension

variable {K M L : Type*} [Field K] [Field M] [Field L] [Algebra K M] [Algebra M L] [Algebra K L]
  [IsScalarTower K M L] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)

/-- For fields `K ⊆ M ⊆ L` and a valuation `w` of `L`, the restriction of `w` to `M` extends the restriction of `w` to `K`. -/
instance hasExtension_comap_comap :
    (w.comap (algebraMap K L)).HasExtension (w.comap (algebraMap M L)) :=
  ⟨fun r s => by simp only [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply]⟩

/-- A valuation `w` of `L` extends its restriction to a subfield `K`. -/
instance hasExtension_comap : (w.comap (algebraMap K L)).HasExtension w :=
  ⟨Valuation.IsEquiv.refl⟩

omit [Algebra K L] in
/-- The valuation ring of the restriction of `W.valuation` to `K` is the inverse image of `W`. -/
theorem valuationSubring_comap_valuation (W : ValuationSubring L) (f : K →+* L) :
    (W.valuation.comap f).valuationSubring = W.comap f := by
  ext x
  rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply,
    ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_comap]

end Extension

section Lift

variable {k E E' : Type*} [Field k] [Field E] [Field E'] [Algebra k E] [Algebra k E'] [Algebra E E']
  [IsScalarTower k E E'] {Γ₀ Γ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [LinearOrderedCommGroupWithZero Γ] (v₀ : Valuation E Γ₀) (v : Valuation E' Γ)
  [v₀.HasExtension v]

/-- **Lifting in the case of one extension, for an algebra `E'/E`.** This is `Singularity.hasLocalUniformization_of_finrank_residueField_eq` for a finite extension `E'/E` that is given as an algebra, not as an intermediate field. Let the valuation `v` of `E'` extend the valuation `v₀` of `E`, and assume that the residue extension of `v` over `v₀` is separable of degree `[E' : E]`. If `v₀` has local uniformization over `k`, then `v` has local uniformization over `k`.

The image `K₀` of `E` in `E'` is an intermediate field of `E'/k`, and `E ≃ K₀` over `k`. This isomorphism carries `v₀` to the restriction of `v` to `K₀`, and it does not change the residue fields and the degrees. -/
theorem hasLocalUniformization_of_finrank_residueField_eq_of_algebra [FiniteDimensional E E']
    [Algebra.IsSeparable (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring)]
    (hf : finrank (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring) =
      finrank E E')
    (h : HasLocalUniformization k v₀.valuationSubring) :
    HasLocalUniformization k v.valuationSubring := by
  let K₀ : IntermediateField k E' := (IsScalarTower.toAlgHom k E E').fieldRange
  let e : E ≃ₐ[k] K₀ := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k E E')
  let v₁ : Valuation K₀ Γ := v.comap (algebraMap K₀ E')
  have : v₁.HasExtension v := ⟨Valuation.IsEquiv.refl⟩
  have he : ∀ a : E, ((e a : K₀) : E') = algebraMap E E' a := fun _ => rfl
  have hmem : ∀ a : E, e a ∈ v₁.valuationSubring ↔ a ∈ v₀.valuationSubring := by
    intro a
    rw [Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff,
      ← Valuation.HasExtension.val_map_le_one_iff v₀ v, ← he]
    rfl
  let φ : v₀.valuationSubring ≃+* v₁.valuationSubring :=
    { toFun := fun a => ⟨e a, (hmem a).2 a.2⟩
      invFun := fun b => ⟨e.symm b, (hmem _).1 (by rw [AlgEquiv.apply_symm_apply]; exact b.2)⟩
      left_inv := fun a => Subtype.ext (e.symm_apply_apply (a : E))
      right_inv := fun b => Subtype.ext (e.apply_symm_apply (b : K₀))
      map_mul' := fun a b => Subtype.ext (map_mul e (a : E) b)
      map_add' := fun a b => Subtype.ext (map_add e (a : E) b) }
  let i := ResidueField.mapEquiv φ
  have hc : (algebraMap (ResidueField v₁.valuationSubring) (ResidueField v.valuationSubring)).comp
      i.toRingHom = (RingEquiv.refl (ResidueField v.valuationSubring)).toRingHom.comp
        (algebraMap (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring)) := by
    ext x
    obtain ⟨a, rfl⟩ := residue_surjective x
    rfl
  have : Algebra.IsSeparable (ResidueField v₁.valuationSubring)
      (ResidueField v.valuationSubring) :=
    Algebra.IsSeparable.of_equiv_equiv i (RingEquiv.refl _) hc
  have hEK : (algebraMap K₀ E').comp e.toRingEquiv.toRingHom =
      (RingEquiv.refl E').toRingHom.comp (algebraMap E E') := rfl
  have : FiniteDimensional K₀ E' :=
    Module.Finite.of_equiv_equiv e.toRingEquiv (RingEquiv.refl E') hEK
  have hf' : finrank (ResidueField v₁.valuationSubring) (ResidueField v.valuationSubring) =
      finrank K₀ E' := by
    rw [← Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl _) hc, hf]
    exact Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl E') hEK
  refine hasLocalUniformization_of_finrank_residueField_eq v₁ v hf' ?_
  refine HasLocalUniformization.of_algEquiv e ?_
  have hcomap : v₁.valuationSubring.comap (e : E →+* K₀) = v₀.valuationSubring := by
    ext a
    exact hmem a
  rwa [hcomap]

end Lift

section Inertia

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

/-- Let `σ` be an automorphism of `L` that maps `W` onto `W`. Then `σ` preserves the elements of value less than `1`. -/
theorem valuation_apply_lt_one_iff {W : ValuationSubring L} {σ : L ≃ₐ[K] L}
    (hσ : ∀ x, σ x ∈ W ↔ x ∈ W) (x : L) :
    W.valuation (σ x) < 1 ↔ W.valuation x < 1 := by
  have key : ∀ y : L, W.valuation y < 1 ↔ y = 0 ∨ y⁻¹ ∉ W := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · rw [← W.valuation_le_one_iff, map_inv₀,
        inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hy)), not_le]
      simp [hy]
  rw [key, key, ← map_inv₀, hσ, map_eq_zero_iff _ σ.injective]

/-- The **inertia group** of a valuation subring `W` of `L` in the group of `K`-automorphisms of `L`. An automorphism `σ` lies in it if `σ` maps `W` onto `W` and acts trivially on the residue field of `W`, that is, `w(σ x - x) < 1` for each `x ∈ W`, where `w` is the valuation of `W`. -/
def inertiaGroup (W : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) where
  carrier := {σ | (∀ x, σ x ∈ W ↔ x ∈ W) ∧ ∀ x ∈ W, W.valuation (σ x - x) < 1}
  mul_mem' {σ τ} hσ hτ := by
    refine ⟨fun x => (hσ.1 _).trans (hτ.1 x), fun x hx => ?_⟩
    have : (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x) := by
      rw [AlgEquiv.mul_apply]
      ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans_lt (max_lt (hσ.2 _ ((hτ.1 x).2 hx)) (hτ.2 x hx))
  one_mem' := ⟨fun x => Iff.rfl, fun x _ => by simp⟩
  inv_mem' {σ} hσ := by
    have hss : ∀ x, σ (σ⁻¹ x) = x := fun x => by
      rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    have h1 : ∀ x, σ⁻¹ x ∈ W ↔ x ∈ W := fun x => by
      rw [← hσ.1 (σ⁻¹ x), hss]
    refine ⟨h1, fun x hx => ?_⟩
    have := hσ.2 (σ⁻¹ x) ((h1 x).2 hx)
    rwa [hss, ← Valuation.map_neg, neg_sub] at this

theorem mem_inertiaGroup_iff {W : ValuationSubring L} {σ : L ≃ₐ[K] L} :
    σ ∈ inertiaGroup K W ↔
      (∀ x, σ x ∈ W ↔ x ∈ W) ∧ ∀ x ∈ W, W.valuation (σ x - x) < 1 :=
  Iff.rfl

/-- The **inertia field** of a valuation subring `W` of `L` over `K`: the fixed field of the inertia group `Singularity.inertiaGroup K W`. -/
def inertiaField (W : ValuationSubring L) : IntermediateField K L :=
  fixedField (inertiaGroup K W)

theorem mem_inertiaField_iff {W : ValuationSubring L} (x : L) :
    x ∈ inertiaField K W ↔ ∀ σ ∈ inertiaGroup K W, σ x = x :=
  mem_fixedField_iff _ _

end Inertia

section Residue

open scoped Pointwise

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (W : ValuationSubring L)

/-- **The residue extension of the inertia field.** Let `L/K` be a finite Galois extension and let `W` be a valuation subring of `L`. Assume that each `K`-automorphism of `L` maps `W` into `W`, so that `K` contains the decomposition field of `W`. Let `T` be the inertia field of `W` over `K`. Then the residue extension of `W ∩ T` over `W ∩ K` is separable of degree `[T : K]`.

The group `G = Gal(L/K)` acts on the valuation ring `B` of `W`, and `B^G` is the valuation ring of `W ∩ K`. By the theory of invariants, the residue extension `κ_W/κ_K` is normal, and `G` maps onto its automorphism group. The kernel of this map is in the inertia group `I`. So `κ_W/κ_K` has at least `|G|/|I| = [T : K]` automorphisms. For the same reason `κ_W` has no automorphism over `κ_T`. A count of separable degrees gives the result, because `[κ_T : κ_K] ≤ [T : K]`. -/
theorem isSeparable_and_finrank_residueField_inertiaField
    (hW : ∀ σ : L ≃ₐ[K] L, ∀ x ∈ W, σ x ∈ W) :
    Algebra.IsSeparable (ResidueField (W.valuation.comap (algebraMap K L)).valuationSubring)
        (ResidueField (W.valuation.comap (algebraMap (inertiaField K W) L)).valuationSubring) ∧
      finrank (ResidueField (W.valuation.comap (algebraMap K L)).valuationSubring)
        (ResidueField (W.valuation.comap (algebraMap (inertiaField K W) L)).valuationSubring) =
        finrank K (inertiaField K W) := by
  classical
  set T := inertiaField K W with hT
  set I := inertiaGroup K W with hI
  set w := W.valuation with hw
  set vK := w.comap (algebraMap K L) with hvK
  set vT := w.comap (algebraMap T L) with hvT
  set B := w.valuationSubring with hB
  set A₀ := vK.valuationSubring with hA₀
  set A₁ := vT.valuationSubring with hA₁
  have hW' : ∀ (σ : L ≃ₐ[K] L) (x : L), σ x ∈ W ↔ x ∈ W := fun σ x => by
    refine ⟨fun h => ?_, hW σ x⟩
    have := hW σ⁻¹ _ h
    rwa [AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply] at this
  have hmemB : ∀ x : L, x ∈ B ↔ x ∈ W := fun x =>
    (Valuation.mem_valuationSubring_iff _ _).trans (W.valuation_le_one_iff x)
  have hBσ : ∀ (σ : L ≃ₐ[K] L) (b : B), σ b ∈ B := fun σ b =>
    (hmemB _).2 ((hW' σ b).2 ((hmemB b).1 b.2))
  let _ : MulSemiringAction (L ≃ₐ[K] L) B :=
    { smul := fun σ b => ⟨σ b, hBσ σ b⟩
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun σ => Subtype.ext (map_zero σ)
      smul_add := fun σ a b => Subtype.ext (map_add σ (a : L) b)
      smul_one := fun σ => Subtype.ext (map_one σ)
      smul_mul := fun σ a b => Subtype.ext (map_mul σ (a : L) b) }
  have hQ : ∀ b : B, b ∈ maximalIdeal B ↔ w b < 1 := mem_maximalIdeal_valuationSubring_iff w
  have hIiff : ∀ σ : L ≃ₐ[K] L, σ ∈ I ↔ ∀ b : B, σ • b - b ∈ maximalIdeal B := by
    intro σ
    rw [hI, mem_inertiaGroup_iff]
    refine ⟨fun h b => (hQ _).2 (h.2 b ((hmemB b).1 b.2)),
      fun h => ⟨hW' σ, fun x hx => ?_⟩⟩
    exact (hQ _).1 (h ⟨x, (hmemB x).2 hx⟩)
  have : SMulCommClass (L ≃ₐ[K] L) A₀ B := ⟨fun σ a b => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    congr 1
    exact Subtype.ext (σ.commutes (a : K))⟩
  have : SMulCommClass I A₁ B := ⟨fun σ a b => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    congr 1
    exact Subtype.ext ((mem_inertiaField_iff K _).1 (a : T).2 σ σ.2)⟩
  have : Algebra.IsInvariant A₀ B (L ≃ₐ[K] L) := ⟨fun b hb => by
    have hfix : ∀ σ : L ≃ₐ[K] L, σ (b : L) = b := fun σ => congrArg Subtype.val (hb σ)
    obtain ⟨c, hc⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (b : L)).2 hfix
    refine ⟨⟨c, ?_⟩, Subtype.ext hc⟩
    change w (algebraMap K L c) ≤ 1
    rw [hc]
    exact b.2⟩
  have : Algebra.IsInvariant A₁ B I := ⟨fun b hb => by
    have hbT : (b : L) ∈ T :=
      (mem_inertiaField_iff K _).2 fun σ hσ => congrArg Subtype.val (hb ⟨σ, hσ⟩)
    exact ⟨⟨⟨b, hbT⟩, b.2⟩, Subtype.ext rfl⟩⟩
  have hstab :
      ∀ σ : L ≃ₐ[K] L, σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) (maximalIdeal B) := by
    intro σ
    rw [MulAction.mem_stabilizer_iff, Ideal.pointwise_smul_eq_comap]
    ext b
    rw [Ideal.mem_comap, hQ, hQ]
    exact valuation_apply_lt_one_iff K (hW' σ⁻¹) b
  -- The residue extension of `W` over `W ∩ T` has no nontrivial automorphism.
  have hM : ∀ φ : ResidueField B ≃ₐ[ResidueField A₁] ResidueField B, φ = 1 := by
    intro φ
    obtain ⟨τ, rfl⟩ := Ideal.Quotient.stabilizerHom_surjective I (maximalIdeal A₁)
      (maximalIdeal B) φ
    ext y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact Ideal.Quotient.eq.2 ((hIiff τ.1.1).1 τ.1.2 b)
  -- The residue extension of `W` over `W ∩ K` has at least `[T : K]` automorphisms.
  have hcardG : Nat.card (L ≃ₐ[K] L) = finrank K T * Nat.card I := by
    rw [IsGalois.card_aut_eq_finrank, ← Module.finrank_mul_finrank K T L, hT, inertiaField,
      finrank_fixedField_eq_card]
  have hd : finrank K T ≤ Nat.card (ResidueField B ≃ₐ[ResidueField A₀] ResidueField B) := by
    set f := Ideal.Quotient.stabilizerHom (maximalIdeal B) (maximalIdeal A₀) (L ≃ₐ[K] L)
    have hsurj : Function.Surjective f :=
      Ideal.Quotient.stabilizerHom_surjective (L ≃ₐ[K] L) (maximalIdeal A₀) (maximalIdeal B)
    have hker : ∀ σ ∈ f.ker, ((σ : _) : L ≃ₐ[K] L) ∈ I := by
      intro σ hσ
      rw [hIiff]
      intro b
      have h0 := DFunLike.congr_fun (f.mem_ker.1 hσ) (Ideal.Quotient.mk _ b)
      have h1 : Ideal.Quotient.mk (maximalIdeal B) ((σ : L ≃ₐ[K] L) • b) =
          Ideal.Quotient.mk (maximalIdeal B) b := h0
      exact Ideal.Quotient.eq.1 h1
    have h1 : Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) (maximalIdeal B)) =
        Nat.card (L ≃ₐ[K] L) :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hstab)
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    have h3 : Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) (maximalIdeal B) ⧸ f.ker) =
        Nat.card (ResidueField B ≃ₐ[ResidueField A₀] ResidueField B) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv
    have h4 : Nat.card f.ker ≤ Nat.card I :=
      Nat.card_le_card_of_injective (fun σ => (⟨σ.1.1, hker σ.1 σ.2⟩ : I))
        fun a b h => by
          simp only [Subtype.mk.injEq] at h
          exact Subtype.ext (Subtype.ext h)
    have hI0 : 0 < Nat.card I := Nat.card_pos
    rw [h1, hcardG, h3] at h2
    exact le_of_mul_le_mul_right (h2 ▸ Nat.mul_le_mul_left _ h4) hI0
  have : FiniteDimensional (ResidueField A₀) (ResidueField B) :=
    (finiteDimensional_residueField_and_finrank_le vK w).1
  have hle : finrank (ResidueField A₀) (ResidueField A₁) ≤ finrank K T :=
    (finiteDimensional_residueField_and_finrank_le vK vT).2
  have : Normal (ResidueField A₀) (ResidueField B) :=
    Ideal.Quotient.normal (L ≃ₐ[K] L) (maximalIdeal A₀) (maximalIdeal B)
  have : Normal (ResidueField A₁) (ResidueField B) :=
    Ideal.Quotient.normal I (maximalIdeal A₁) (maximalIdeal B)
  have : IsScalarTower (ResidueField A₀) (ResidueField A₁) (ResidueField B) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      obtain ⟨a, rfl⟩ := residue_surjective x
      rfl
  exact isSeparable_and_finrank_eq_of_normal hM hd hle

end Residue

section Uniformization

open scoped Pointwise

attribute [local instance] isScalarTower_intermediateField

variable {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [FiniteDimensional K L] [IsGalois K L]

/-- **Local uniformization goes up to the inertia field** (part of Step 4 of the reduction of Cossart-Piltant, Volume 6, Proposition 2.2.1 of the handbook). Let `L/K` be a finite Galois extension of extensions of `k`, and let `W` be a valuation subring of `L`. Assume that each `K`-automorphism of `L` maps `W` into `W`, so that `K` contains the decomposition field of `W`. Let `T` be the inertia field of `W` over `K`. If `W ∩ K` has local uniformization over `k`, then `W ∩ T` has local uniformization over `k`.

By `Singularity.isSeparable_and_finrank_residueField_inertiaField`, the residue extension of `W ∩ T` over `W ∩ K` is separable of degree `[T : K]`. So there is an étale generator of `T/K` at `W ∩ T`, and local uniformization lifts along it. -/
theorem hasLocalUniformization_inertiaField (W : ValuationSubring L)
    (hW : ∀ σ : L ≃ₐ[K] L, ∀ x ∈ W, σ x ∈ W)
    (h : HasLocalUniformization k (W.comap (algebraMap K L))) :
    HasLocalUniformization k (W.comap (algebraMap (inertiaField K W) L)) := by
  obtain ⟨hsep, hf⟩ := isSeparable_and_finrank_residueField_inertiaField W hW
  have := hasLocalUniformization_of_finrank_residueField_eq_of_algebra (k := k)
    (W.valuation.comap (algebraMap K L)) (W.valuation.comap (algebraMap (inertiaField K W) L)) hf
    (by rwa [valuationSubring_comap_valuation])
  rwa [valuationSubring_comap_valuation] at this

/-- **Local uniformization goes up from the decomposition field to the inertia field** (part of Step 4 of the reduction of Cossart-Piltant, Volume 6, Proposition 2.2.1 of the handbook). Let `L/K` be a finite Galois extension of extensions of `k`, and let `W` be a valuation subring of `L`. Let `Z` be the decomposition field of `W`, the fixed field of the stabilizer of `W` in `Gal(L/K)`, and let `T` be the inertia field of `W` over `Z`. If `W ∩ Z` has local uniformization over `k`, then `W ∩ T` has local uniformization over `k`.

Each `Z`-automorphism of `L` fixes `Z`, so it is in the decomposition group, and it maps `W` onto `W`. So `Singularity.hasLocalUniformization_inertiaField` applies to `L/Z`. The passage from `K` to `Z` is not proved here. -/
theorem hasLocalUniformization_inertiaField_decompositionField (W : ValuationSubring L)
    (h : HasLocalUniformization k
      (W.comap (algebraMap (fixedField (W.decompositionSubgroup K)) L))) :
    HasLocalUniformization k
      (W.comap (algebraMap (inertiaField (fixedField (W.decompositionSubgroup K)) W) L)) := by
  refine hasLocalUniformization_inertiaField W (fun σ x hx => ?_) h
  have hσ : σ.restrictScalars K ∈ W.decompositionSubgroup K := by
    have h1 : σ.restrictScalars K ∈ fixingSubgroup (fixedField (W.decompositionSubgroup K)) :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => σ.commutes ⟨y, hy⟩
    rwa [fixingSubgroup_fixedField] at h1
  have := ValuationSubring.smul_mem_pointwise_smul (σ.restrictScalars K) x W hx
  rwa [MulAction.mem_stabilizer_iff.1 hσ] at this

end Uniformization

end Singularity
