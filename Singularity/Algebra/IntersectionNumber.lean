/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# The intersection number of two elements

Let `R` be a ring and let `f, g ∈ R`. The intersection number of `f` and `g` is the length `i_R(f, g)` of the `R`-module `R/(f, g)` (Volume 5, Definition 1.2.1 of the handbook). This file proves parts of Volume 5, Lemma 1.2.2 of the handbook.

1. If `R` is local, then `i_R(f, g) = 0` if and only if `f` or `g` is a unit (`length_quotient_span_pair_eq_zero_iff`).
2. If `f` has no common prime factor with `g_1`, then `i_R(f, g_1 g_2) = i_R(f, g_1) + i_R(f, g_2)` (`length_quotient_span_pair_mul_of_prime`).

The length is a value in `ℕ∞`, so part 2 holds also when a length is infinite. The handbook takes a regular local ring of dimension 2. The proof of part 2 uses only that `R` is a unique factorization domain, and the more general form `length_quotient_span_pair_mul` uses only that `f ∣ g_1 c` implies `f ∣ c`. The claim of part 1 that `i_R(f, g)` is finite is not proved, and the hypothesis of part 2 that `f` has no common prime factor with `g_2` is not used.

The proof of part 2 is the proof of the handbook. Multiplication by `g_1` maps `R/(f, g_2)` into `R/(f, g_1 g_2)`, and the quotient by its image is `R/(f, g_1)`. The map is injective: if `g_1 b = c f + d g_1 g_2`, then `f ∣ g_1 (b - d g_2)`, so `f ∣ b - d g_2` and `b ∈ (f, g_2)`. The length is additive in this exact sequence.

## Main results

* `Singularity.mulQuotientSpanPair`: the map `R/(f, g_2) → R/(f, g_1 g_2)`, multiplication by `g_1`.
* `Singularity.quotientSpanPairMap`: the map `R/(f, g_1 g_2) → R/(f, g_1)`.
* `Singularity.length_quotient_span_pair_mul`: `i_R(f, g_1 g_2) = i_R(f, g_1) + i_R(f, g_2)` if `f ∣ g_1 c` implies `f ∣ c`.
* `Singularity.length_quotient_span_pair_mul_of_prime`: the same in a unique factorization domain, if `f ≠ 0` has no common prime factor with `g_1`.
* `Singularity.length_quotient_span_pair_eq_zero_iff`: in a local ring, `i_R(f, g) = 0` if and only if `f` or `g` is a unit.
-/

namespace Singularity

open Ideal

variable {R : Type*} [CommRing R]

/-- The map `R/(f, g₂) → R/(f, g₁ g₂)`, multiplication by `g₁`. -/
noncomputable def mulQuotientSpanPair (f g₁ g₂ : R) :
    (R ⧸ span ({f, g₂} : Set R)) →ₗ[R] R ⧸ span ({f, g₁ * g₂} : Set R) :=
  Submodule.mapQ _ _ (LinearMap.mulLeft R g₁) fun a ha => by
    obtain ⟨c, d, rfl⟩ := mem_span_pair.mp ha
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
    exact mem_span_pair.mpr ⟨g₁ * c, d, by ring⟩

/-- The map `R/(f, g₁ g₂) → R/(f, g₁)` of the inclusion `(f, g₁ g₂) ⊆ (f, g₁)`. -/
noncomputable def quotientSpanPairMap (f g₁ g₂ : R) :
    (R ⧸ span ({f, g₁ * g₂} : Set R)) →ₗ[R] R ⧸ span ({f, g₁} : Set R) :=
  Submodule.mapQ _ _ LinearMap.id fun a ha => by
    obtain ⟨c, d, rfl⟩ := mem_span_pair.mp ha
    rw [Submodule.mem_comap, LinearMap.id_apply]
    exact mem_span_pair.mpr ⟨c, d * g₂, by ring⟩

theorem mulQuotientSpanPair_mk (f g₁ g₂ b : R) :
    mulQuotientSpanPair f g₁ g₂ (Submodule.Quotient.mk b) = Submodule.Quotient.mk (g₁ * b) := by
  rw [mulQuotientSpanPair, Submodule.mapQ_apply, LinearMap.mulLeft_apply]

theorem quotientSpanPairMap_mk (f g₁ g₂ b : R) :
    quotientSpanPairMap f g₁ g₂ (Submodule.Quotient.mk b) = Submodule.Quotient.mk b := by
  rw [quotientSpanPairMap, Submodule.mapQ_apply, LinearMap.id_apply]

/-- If `f ∣ g₁ c` implies `f ∣ c`, then multiplication by `g₁` is injective on `R/(f, g₂)`. -/
theorem mulQuotientSpanPair_injective {f g₁ g₂ : R} (h : ∀ c : R, f ∣ g₁ * c → f ∣ c) :
    Function.Injective (mulQuotientSpanPair f g₁ g₂) := by
  refine (injective_iff_map_eq_zero _).mpr fun y hy => ?_
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [mulQuotientSpanPair_mk, Submodule.Quotient.mk_eq_zero] at hy
  obtain ⟨c, d, hcd⟩ := mem_span_pair.mp hy
  have hdvd : f ∣ g₁ * (b - d * g₂) := ⟨c, by linear_combination -hcd⟩
  obtain ⟨e, he⟩ := h _ hdvd
  rw [Submodule.Quotient.mk_eq_zero]
  exact mem_span_pair.mpr ⟨e, d, by linear_combination -he⟩

theorem quotientSpanPairMap_surjective (f g₁ g₂ : R) :
    Function.Surjective (quotientSpanPairMap f g₁ g₂) := by
  intro y
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Submodule.Quotient.mk b, quotientSpanPairMap_mk f g₁ g₂ b⟩

/-- The sequence `R/(f, g₂) → R/(f, g₁ g₂) → R/(f, g₁)` is exact. -/
theorem exact_mulQuotientSpanPair (f g₁ g₂ : R) :
    Function.Exact (mulQuotientSpanPair f g₁ g₂) (quotientSpanPairMap f g₁ g₂) := by
  intro y
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [quotientSpanPairMap_mk, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hb
    obtain ⟨c, d, rfl⟩ := mem_span_pair.mp hb
    refine ⟨Submodule.Quotient.mk d, ?_⟩
    rw [mulQuotientSpanPair_mk, Submodule.Quotient.eq]
    exact mem_span_pair.mpr ⟨-c, 0, by ring⟩
  · rintro ⟨z, hz⟩
    obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [mulQuotientSpanPair_mk, Submodule.Quotient.eq] at hz
    obtain ⟨c, e, hce⟩ := mem_span_pair.mp hz
    exact mem_span_pair.mpr ⟨-c, d - e * g₂, by linear_combination -hce⟩

/-- **Volume 5, Lemma 1.2.2 (2) of the handbook**, in a general form. If `f ∣ g₁ c` implies `f ∣ c` for each `c`, then `i_R(f, g₁ g₂) = i_R(f, g₁) + i_R(f, g₂)`, where `i_R(f, g)` is the length of `R/(f, g)`. -/
theorem length_quotient_span_pair_mul {f g₁ g₂ : R} (h : ∀ c : R, f ∣ g₁ * c → f ∣ c) :
    Module.length R (R ⧸ span ({f, g₁ * g₂} : Set R)) =
      Module.length R (R ⧸ span ({f, g₁} : Set R)) +
        Module.length R (R ⧸ span ({f, g₂} : Set R)) := by
  rw [Module.length_eq_add_of_exact (mulQuotientSpanPair f g₁ g₂) (quotientSpanPairMap f g₁ g₂)
    (mulQuotientSpanPair_injective h) (quotientSpanPairMap_surjective f g₁ g₂)
    (exact_mulQuotientSpanPair f g₁ g₂), add_comm]

/-- **Volume 5, Lemma 1.2.2 (2) of the handbook**, in a unique factorization domain. Let `f ≠ 0` have no common prime factor with `g₁`. Then `i_R(f, g₁ g₂) = i_R(f, g₁) + i_R(f, g₂)`, where `i_R(f, g)` is the length of `R/(f, g)`. -/
theorem length_quotient_span_pair_mul_of_prime [IsDomain R] [UniqueFactorizationMonoid R]
    {f g₁ g₂ : R} (hf : f ≠ 0) (h : ∀ p : R, Prime p → p ∣ f → p ∣ g₁ → False) :
    Module.length R (R ⧸ span ({f, g₁ * g₂} : Set R)) =
      Module.length R (R ⧸ span ({f, g₁} : Set R)) +
        Module.length R (R ⧸ span ({f, g₂} : Set R)) := by
  have hrel : IsRelPrime f g₁ :=
    WfDvdMonoid.isRelPrime_of_no_irreducible_factors (fun h0 => hf h0.1) fun z hz hzf hzg =>
      h z (UniqueFactorizationMonoid.irreducible_iff_prime.mp hz) hzf hzg
  exact length_quotient_span_pair_mul fun c hc => hrel.dvd_of_dvd_mul_left hc

open IsLocalRing in
/-- **Volume 5, Lemma 1.2.2 (1) of the handbook**, the second claim. In a local ring, `i_R(f, g) = 0` if and only if `f` or `g` is a unit, where `i_R(f, g)` is the length of `R/(f, g)`. -/
theorem length_quotient_span_pair_eq_zero_iff [IsLocalRing R] {f g : R} :
    Module.length R (R ⧸ span ({f, g} : Set R)) = 0 ↔ IsUnit f ∨ IsUnit g := by
  rw [Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff]
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    have hle : span ({f, g} : Set R) ≤ maximalIdeal R := by
      refine span_le.mpr ?_
      rintro z (rfl | rfl)
      · exact (mem_maximalIdeal _).mpr hne.1
      · exact (mem_maximalIdeal _).mpr hne.2
    rw [h] at hle
    exact (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp hle)
  · rintro (hu | hu)
    · exact eq_top_of_isUnit_mem _ (subset_span (Set.mem_insert _ _)) hu
    · exact eq_top_of_isUnit_mem _ (subset_span (Set.mem_insert_of_mem _ rfl)) hu

end Singularity
