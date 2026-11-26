/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.NormalizationCharP
import Mathlib.GroupTheory.Sylow

/-!
# The field theory of Galois alterations

This file proves two statements of field theory from Volume 8, Chapter 3 of the handbook.

(a) Separable distillation (Volume 8, Proposition 3.1.1 of the handbook). Let `L/K` be a finite extension, let `L'` be a normal closure of `L/K`, let `G` be the group of the `K`-automorphisms of `L'`, and let `M` be the fixed field of `G`. Then `L'/L` is finite, `M/K` is purely inseparable, `L'/M` is Galois, and each `K`-automorphism of `L'` is an `M`-automorphism, so `Gal(L'/M) = G`. The main step is Volume 1, Lemma 2.4.5 of the handbook, which is `Singularity.Algebra.isPurelyInseparable_fixedField_top`. Here `L'` is the normal closure of `L` in the algebraic closure of `L` of Mathlib.

(b) The degree prime to `ℓ` (Volume 8, Lemma 3.2.2 of the handbook). Let `L'/M` be a finite Galois extension with group `G`, let `ℓ` be a prime, and let `P` be an `ℓ`-Sylow subgroup of `G`. Let `K ⊆ M` be a subfield with `[M : K] = p^e`, where `p ≠ ℓ` is a prime. Then `ℓ` does not divide `[L'^P : K]`. The proof is the proof of the handbook: `[L'^P : M]` is the index of `P` in `G`, and the index of a Sylow subgroup is prime to `ℓ`. The handbook asks that `M/K` is purely inseparable. The statement here uses only the degree.

## Main results

* `Singularity.isPurelyInseparable_isGalois_fixedField_top`: part (a) for each finite normal extension `L'` of `K`.
* `Singularity.bijective_restrictScalars_fixedField_top`: the map `Gal(L'/M) → G` is bijective.
* `Singularity.separable_distillation`: part (a) with the normal closure of `L/K`.
* `Singularity.not_dvd_finrank_fixedField_sylow`: part (b).
-/

open Module IntermediateField

namespace Singularity

/-- Let `L'` be a finite normal extension of `K`, and let `M` be the fixed field of the group of the `K`-automorphisms of `L'`. Then `M/K` is purely inseparable and `L'/M` is Galois. This is the main part of Volume 8, Proposition 3.1.1 of the handbook. -/
theorem isPurelyInseparable_isGalois_fixedField_top (K L' : Type*) [Field K] [Field L']
    [Algebra K L'] [FiniteDimensional K L'] [Normal K L'] :
    IsPurelyInseparable K (fixedField (⊤ : Subgroup Gal(L'/K))) ∧
      IsGalois (fixedField (⊤ : Subgroup Gal(L'/K))) L' :=
  ⟨Singularity.Algebra.isPurelyInseparable_fixedField_top K L',
    IsGalois.of_fixed_field L' (⊤ : Subgroup Gal(L'/K))⟩

/-- Let `M` be the fixed field of the group `G` of the `K`-automorphisms of `L'`. Then the map from `Gal(L'/M)` to `G` that forgets the `M`-linearity is bijective. So `Gal(L'/M) = G`, as in Volume 8, Proposition 3.1.1 of the handbook. -/
theorem bijective_restrictScalars_fixedField_top (K L' : Type*) [Field K] [Field L']
    [Algebra K L'] :
    Function.Bijective
      (fun σ : Gal(L'/(fixedField (⊤ : Subgroup Gal(L'/K)))) => σ.restrictScalars K) := by
  refine ⟨fun σ τ h => AlgEquiv.restrictScalars_injective K h, fun τ => ?_⟩
  have hτ : τ ∈ (fixedField (⊤ : Subgroup Gal(L'/K))).fixingSubgroup := by
    rw [mem_fixingSubgroup_iff]
    intro x hx
    exact (mem_fixedField_iff _ _).mp hx τ (Subgroup.mem_top τ)
  refine ⟨(fixedField (⊤ : Subgroup Gal(L'/K))).fixingSubgroupEquiv ⟨τ, hτ⟩, ?_⟩
  ext x
  rfl

/-- Volume 8, Proposition 3.1.1 of the handbook (separable distillation). Let `L/K` be a finite extension, and let `L'` be the normal closure of `L/K` in an algebraic closure of `L`. Let `M` be the fixed field of the group of the `K`-automorphisms of `L'`. Then `L'` is a finite extension of `L`, `M/K` is purely inseparable, and `L'/M` is Galois. -/
theorem separable_distillation (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    FiniteDimensional L (normalClosure K L (AlgebraicClosure L)) ∧
      IsPurelyInseparable K
        (fixedField (⊤ : Subgroup Gal((normalClosure K L (AlgebraicClosure L))/K))) ∧
      IsGalois (fixedField (⊤ : Subgroup Gal((normalClosure K L (AlgebraicClosure L))/K)))
        (normalClosure K L (AlgebraicClosure L)) :=
  ⟨FiniteDimensional.right K L (normalClosure K L (AlgebraicClosure L)),
    isPurelyInseparable_isGalois_fixedField_top K _⟩

/-- Volume 8, Lemma 3.2.2 of the handbook. Let `L'/M` be a finite Galois extension, let `ℓ` be a prime, and let `P` be an `ℓ`-Sylow subgroup of `Gal(L'/M)`. Let `K ⊆ M` be a subfield with `[M : K] = p ^ e`, where `p ≠ ℓ` is a prime. Then `ℓ` does not divide `[L'^P : K]`. The handbook asks that `M/K` is purely inseparable. This statement uses only the degree. -/
theorem not_dvd_finrank_fixedField_sylow {K M L' : Type*} [Field K] [Field M] [Field L']
    [Algebra K M] [Algebra M L'] [Algebra K L'] [IsScalarTower K M L']
    [FiniteDimensional M L'] [IsGalois M L'] {ℓ p e : ℕ} [Fact ℓ.Prime] (hp : p.Prime)
    (hpℓ : p ≠ ℓ) (hM : finrank K M = p ^ e) (P : Sylow ℓ Gal(L'/M)) :
    ¬ ℓ ∣ finrank K (fixedField (P : Subgroup Gal(L'/M))) := by
  have hℓ : ℓ.Prime := Fact.out
  have h1 : finrank M (fixedField (P : Subgroup Gal(L'/M))) =
      (P : Subgroup Gal(L'/M)).index := by
    have h2 := Module.finrank_mul_finrank M (fixedField (P : Subgroup Gal(L'/M))) L'
    rw [finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank,
      ← Subgroup.index_mul_card (P : Subgroup Gal(L'/M))] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  rw [← Module.finrank_mul_finrank K M (fixedField (P : Subgroup Gal(L'/M))), h1, hM]
  intro h
  rcases hℓ.dvd_mul.mp h with h | h
  · exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow h)).symm
  · exact Sylow.not_dvd_index P h

end Singularity
