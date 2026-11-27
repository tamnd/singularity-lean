/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.Regular

/-!
# A regular point lies on one irreducible component

This file proves the affine form of Volume 1, Corollary 1.3.4 of the handbook. Let `A` be a ring and let `𝔮` be a prime ideal of `A` such that `A_𝔮` is a regular local ring. Then exactly one minimal prime ideal of `A` is contained in `𝔮`. In the language of schemes, the point `𝔮` of `Spec A` lies on exactly one irreducible component.

* `Singularity.Algebra.existsUnique_minimalPrimes_le_of_isRegularLocalRing`: the affine form of Corollary 1.3.4 of the handbook.

The ring `A_𝔮` is a domain (Theorem 1.3.3 of the handbook, `isDomain_of_isRegularLocalRing`). Let `𝔭 ⊆ 𝔮` be a minimal prime of `A`. The preimage `J` of the zero ideal of `A_𝔮` is a prime ideal of `A`, and `J ⊆ 𝔭` because `𝔭` is the preimage of `𝔭 A_𝔮`. By the minimality of `𝔭`, `𝔭 = J`. So each minimal prime in `𝔮` is equal to `J`.
-/

open IsLocalRing Ideal

universe u

namespace Singularity.Algebra

/-- Let `𝔮` be a prime ideal of `A` such that `A_𝔮` is a domain. Then each minimal prime of `A` that is contained in `𝔮` is the preimage of the zero ideal of `A_𝔮`. -/
theorem eq_comap_bot_of_mem_minimalPrimes {A : Type u} [CommRing A] (q : Ideal A) [q.IsPrime]
    [IsDomain (Localization.AtPrime q)] {p : Ideal A} (hp : p ∈ minimalPrimes A) (hpq : p ≤ q) :
    p = (⊥ : Ideal (Localization.AtPrime q)).comap
      (algebraMap A (Localization.AtPrime q)) := by
  have hpp : p.IsPrime := hp.1.1
  have hdisj : Disjoint (q.primeCompl : Set A) p :=
    Set.disjoint_left.mpr fun _ hx hxp => hx (hpq hxp)
  have hcomap : (p.map (algebraMap A (Localization.AtPrime q))).comap
      (algebraMap A (Localization.AtPrime q)) = p :=
    IsLocalization.under_map_of_isPrime_disjoint q.primeCompl (Localization.AtPrime q) hpp hdisj
  have hJle : (⊥ : Ideal (Localization.AtPrime q)).comap
      (algebraMap A (Localization.AtPrime q)) ≤ p := by
    rw [← hcomap]
    exact Ideal.comap_mono bot_le
  have hJ : ((⊥ : Ideal (Localization.AtPrime q)).comap
      (algebraMap A (Localization.AtPrime q))).IsPrime :=
    inferInstance
  exact le_antisymm (hp.2 ⟨hJ, bot_le⟩ hJle) hJle

/-- Let `𝔮` be a prime ideal of `A` such that `A_𝔮` is a regular local ring. Then exactly one minimal prime ideal of `A` is contained in `𝔮` (the affine form of Volume 1, Corollary 1.3.4 of the handbook). -/
theorem existsUnique_minimalPrimes_le_of_isRegularLocalRing {A : Type u} [CommRing A]
    (q : Ideal A) [q.IsPrime] [IsRegularLocalRing (Localization.AtPrime q)] :
    ∃! p, p ∈ minimalPrimes A ∧ p ≤ q := by
  have := isDomain_of_isRegularLocalRing (Localization.AtPrime q)
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal A) ≤ q)
  refine ⟨p, ⟨hp, hpq⟩, fun p' ⟨hp', hp'q⟩ => ?_⟩
  rw [eq_comap_bot_of_mem_minimalPrimes q hp' hp'q, eq_comap_bot_of_mem_minimalPrimes q hp hpq]

end Singularity.Algebra
