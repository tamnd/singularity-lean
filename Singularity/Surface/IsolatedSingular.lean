/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.RegularLocus
import Singularity.Scheme.NormalDimOne
import Mathlib.Order.SuccPred.ENat
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# The singular points of a normal surface

Volume 4, Lemma 1.2.3 and Theorem 1.2.4 of the handbook show that the singular points of a normal Noetherian scheme of dimension at most 2 form a finite set of closed points, if the regular locus is open. This file proves both results for an affine scheme `Spec R`.

* `Singularity.finite_isMaximal_of_height_eq_two`: let `R` be a Noetherian ring and let `Z` be a closed subset of `Spec R` such that each `z ∈ Z` has height 2. Then `Z` is finite and each point of `Z` is a closed point. The bound `dim R ≤ 2` of the handbook is not necessary for this.
* `Singularity.height_eq_two_of_notMem_regularLocus`: let `R` be Noetherian with `dim R ≤ 2`. If `R_p` is an integrally closed domain and not regular, then `p` has height 2.
* `Singularity.finite_isMaximal_compl_regularLocus`: let `R` be Noetherian with `dim R ≤ 2`, let each `R_p` be an integrally closed domain, and let `Reg(R)` be open. Then `Sing(R)` is a finite set of closed points, and each of them has height 2.

The file proves the results for affine schemes only. It does not prove the last claim of Theorem 1.2.4, that the result holds for each normal excellent surface, since this needs the openness of the regular locus of an excellent ring.
-/

universe u

open PrimeSpectrum

namespace Singularity

variable {R : Type u} [CommRing R]

/-- Let `R` be a Noetherian ring and let `Z ⊆ Spec R` be a closed subset such that each point of `Z` has height 2. Then `Z` is a finite set of closed points (Volume 4, Lemma 1.2.3 of the handbook, for an affine scheme). -/
theorem finite_isMaximal_of_height_eq_two [IsNoetherianRing R] {Z : Set (PrimeSpectrum R)}
    (hZ : IsClosed Z) (h2 : ∀ z ∈ Z, z.asIdeal.height = 2) :
    Z.Finite ∧ ∀ z ∈ Z, z.asIdeal.IsMaximal := by
  obtain ⟨J, rfl⟩ := (isClosed_iff_zeroLocus_ideal Z).mp hZ
  have key : ∀ y ∈ zeroLocus (J : Set R), ∀ z ∈ zeroLocus (J : Set R),
      y.asIdeal ≤ z.asIdeal → y.asIdeal = z.asIdeal := by
    intro y hy z hz hyz
    by_contra hne
    have h := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hyz hne)
    rw [h2 y hy, h2 z hz, ENat.add_one_le_iff (ENat.ofNat_ne_top 2)] at h
    exact lt_irrefl _ h
  refine ⟨?_, fun z hz => ?_⟩
  · have hfin : (PrimeSpectrum.asIdeal ⁻¹' J.minimalPrimes).Finite :=
      Set.Finite.preimage (fun a _ b _ h => PrimeSpectrum.ext h)
        (Ideal.finite_minimalPrimes_of_isNoetherianRing R J)
    refine hfin.subset fun z hz => ?_
    show (z.asIdeal.IsPrime ∧ J ≤ z.asIdeal) ∧
      ∀ ⦃q : Ideal R⦄, q.IsPrime ∧ J ≤ q → q ≤ z.asIdeal → z.asIdeal ≤ q
    refine ⟨⟨z.isPrime, SetLike.coe_subset_coe.mp ((mem_zeroLocus z J).mp hz)⟩,
      fun q hq hqz => ?_⟩
    have hq' : (⟨q, hq.1⟩ : PrimeSpectrum R) ∈ zeroLocus (J : Set R) :=
      (mem_zeroLocus _ _).mpr (SetLike.coe_subset_coe.mpr hq.2)
    exact (key _ hq' z hz hqz).symm.le
  · obtain ⟨m, hm, hzm⟩ := Ideal.exists_le_maximal z.asIdeal z.isPrime.ne_top
    have hm' : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈ zeroLocus (J : Set R) :=
      (mem_zeroLocus _ _).mpr
        (((mem_zeroLocus z J).mp hz).trans (SetLike.coe_subset_coe.mpr hzm))
    rw [key z hz _ hm' hzm]
    exact hm

/-- Let `R` be a Noetherian ring with `dim R ≤ 2`, and let `p` be a prime such that `R_p` is an integrally closed domain. If `R_p` is not regular, then `p` has height 2 (Volume 4, proof of Theorem 1.2.4 of the handbook). -/
theorem height_eq_two_of_notMem_regularLocus [IsNoetherianRing R] (hdim : ringKrullDim R ≤ 2)
    {p : PrimeSpectrum R} [IsDomain (Localization.AtPrime p.asIdeal)]
    [IsIntegrallyClosed (Localization.AtPrime p.asIdeal)]
    (hp : p ∉ Algebra.regularLocus R) : p.asIdeal.height = 2 := by
  have h1 : (p.asIdeal.height : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) :=
    (Ideal.height_le_ringKrullDim_of_isPrime (I := p.asIdeal)).trans hdim
  have h2 : p.asIdeal.height ≤ 2 := WithBot.coe_le_coe.mp h1
  have htop : p.asIdeal.height ≠ ⊤ := ne_top_of_le_ne_top (ENat.ofNat_ne_top 2) h2
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← hn] at h2 ⊢
  have hn2 : n ≤ 2 := by exact_mod_cast h2
  by_contra hne
  have hn1 : n ≤ 1 := by
    have : n ≠ 2 := fun h => hne (by exact_mod_cast h)
    omega
  have : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl _ inferInstance
  apply hp
  show IsRegularLocalRing (Localization.AtPrime p.asIdeal)
  apply isRegularLocalRing_of_isIntegrallyClosed
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Localization.AtPrime p.asIdeal),
    ← hn]
  exact (WithBot.coe_le_coe.mpr (by exact_mod_cast hn1) :
    ((n : ℕ∞) : WithBot ℕ∞) ≤ ((1 : ℕ∞) : WithBot ℕ∞))

/-- Let `R` be a Noetherian ring with `dim R ≤ 2` such that each `R_p` is an integrally closed domain, and let `Reg(R)` be open. Then `Sing(R) = Spec R \ Reg(R)` is a finite set of closed points, and each of them has height 2 (Volume 4, Theorem 1.2.4 of the handbook, for an affine scheme). -/
theorem finite_isMaximal_compl_regularLocus [IsNoetherianRing R] (hdim : ringKrullDim R ≤ 2)
    (hnorm : ∀ p : PrimeSpectrum R, IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal))
    (hreg : IsOpen (Algebra.regularLocus R)) :
    (Algebra.regularLocus R)ᶜ.Finite ∧ (∀ p ∈ (Algebra.regularLocus R)ᶜ, p.asIdeal.IsMaximal) ∧
      ∀ p ∈ (Algebra.regularLocus R)ᶜ, p.asIdeal.height = 2 := by
  have h2 : ∀ p ∈ (Algebra.regularLocus R)ᶜ, p.asIdeal.height = 2 := fun p hp => by
    have := (hnorm p).1
    have := (hnorm p).2
    exact height_eq_two_of_notMem_regularLocus hdim hp
  obtain ⟨hfin, hmax⟩ := finite_isMaximal_of_height_eq_two hreg.isClosed_compl h2
  exact ⟨hfin, hmax, h2⟩

end Singularity
