/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.RegularLocus
import Mathlib.RingTheory.Derivation.Basic

/-!
# The Jacobian criterion for a hypersurface

Let `A` be a Noetherian ring, let `q` be a prime ideal such that `A_q` is regular, and let
`F ∈ q`. If a derivation `D` of `A` has `D F ∉ q`, then `A_q / (F)` is a regular local ring. This
is the case of one equation of the Jacobian criterion ([Mat89, Theorem 30.3]). The proof does not
use differentials: if `F ∈ q² A_q`, then `s F ∈ q²` for some `s ∉ q`, and `D (s F) ∈ q` gives
`D F ∈ q`.

## Main results

* `derivation_mem_of_mem_sq`: a derivation maps `I²` into `I`.
* `notMem_maximalIdeal_sq_of_derivation`: the image of `F` in `A_q` is not in the square of the
  maximal ideal.
* `isRegularLocalRing_localization_quotient_of_derivation`: the ring `(A / (F))_(q / (F))` is a
  regular local ring.
* `regularLocus_quotient_of_derivation`: if `A` is a regular ring, then each prime of `A / (F)`
  that does not contain the image of `D F` is in the regular locus.

## References

* [Mat89] H. Matsumura, *Commutative Ring Theory*, Cambridge University Press, 1989.
-/

universe u v

open IsLocalRing Ideal

namespace Singularity.Algebra

variable {k : Type v} [CommRing k] {A : Type u} [CommRing A] [Algebra k A]

/-- A derivation maps the square of an ideal `I` into `I`. -/
theorem derivation_mem_of_mem_sq (D : Derivation k A A) (I : Ideal A) {x : A} (hx : x ∈ I ^ 2) :
    D x ∈ I := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun x y hx hy => ?_)
  · rw [D.leibniz, smul_eq_mul, smul_eq_mul]
    exact I.add_mem (I.mul_mem_right _ ha) (I.mul_mem_right _ hb)
  · rw [map_add]
    exact I.add_mem hx hy

/-- Let `q` be a prime and let `F ∈ q`. If a derivation `D` has `D F ∉ q`, then the image of `F`
in `A_q` is in the maximal ideal and not in its square. -/
theorem notMem_maximalIdeal_sq_of_derivation (D : Derivation k A A) (q : Ideal A) [q.IsPrime]
    {F : A} (hF : F ∈ q) (hD : D F ∉ q) :
    algebraMap A (Localization.AtPrime q) F ∈ maximalIdeal (Localization.AtPrime q) ∧
      algebraMap A (Localization.AtPrime q) F ∉ maximalIdeal (Localization.AtPrime q) ^ 2 := by
  refine ⟨(IsLocalization.AtPrime.to_map_mem_maximal_iff _ q F).mpr hF, fun h => ?_⟩
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q, ← Ideal.map_pow] at h
  obtain ⟨s, hs, hsF⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl _ (q ^ 2) F).mp h
  have h1 := derivation_mem_of_mem_sq D q hsF
  rw [D.leibniz, smul_eq_mul, smul_eq_mul] at h1
  have h2 : s * D F ∈ q := by
    have := q.sub_mem h1 (q.mul_mem_right (D s) hF)
    rwa [add_sub_cancel_right] at this
  exact (Ideal.IsPrime.mem_or_mem ‹_› h2).elim hs hD

/-- The Jacobian criterion for a hypersurface. Let `A_q` be regular, let `F ∈ q`, and let `D` be
a derivation with `D F ∉ q`. Then `A_q / (F)` is a regular local ring. -/
theorem isRegularLocalRing_quotient_of_derivation [IsNoetherianRing A] (D : Derivation k A A)
    (q : Ideal A) [q.IsPrime] [IsRegularLocalRing (Localization.AtPrime q)] {F : A}
    (hF : F ∈ q) (hD : D F ∉ q) :
    IsRegularLocalRing (Localization.AtPrime q ⧸
      (span {F}).map (algebraMap A (Localization.AtPrime q))) := by
  obtain ⟨hm, hm2⟩ := notMem_maximalIdeal_sq_of_derivation D q hF hD
  rw [Ideal.map_span, Set.image_singleton]
  exact (quotient_span_singleton hm hm2).1

/-- The Jacobian criterion for a hypersurface, for the localization of `A / (F)`. -/
theorem isRegularLocalRing_localization_quotient_of_derivation [IsNoetherianRing A]
    (D : Derivation k A A) (q : Ideal A) [q.IsPrime] [IsRegularLocalRing (Localization.AtPrime q)]
    {F : A} (hF : F ∈ q) (hD : D F ∉ q) [(q.map (Ideal.Quotient.mk (span {F}))).IsPrime] :
    IsRegularLocalRing (Localization.AtPrime (q.map (Ideal.Quotient.mk (span {F})))) := by
  have := isRegularLocalRing_quotient_of_derivation D q hF hD
  exact IsRegularLocalRing.of_ringEquiv
    (localizationQuotientEquiv (span {F}) q ((span_singleton_le_iff_mem _).mpr hF)).symm

/-- Let `A` be a regular ring, let `F ∈ A`, and let `D` be a derivation of `A`. Then each prime
of `A / (F)` that does not contain the image of `D F` is in the regular locus of `A / (F)`. -/
theorem regularLocus_quotient_of_derivation [IsRegularRing A] (D : Derivation k A A) (F : A) :
    (PrimeSpectrum.basicOpen (Ideal.Quotient.mk (span {F}) (D F)) :
      Set (PrimeSpectrum (A ⧸ span {F}))) ⊆ regularLocus (A ⧸ span {F}) := by
  intro P hP
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hP
  set q := P.asIdeal.comap (Ideal.Quotient.mk (span {F}))
  have hq : q.map (Ideal.Quotient.mk (span {F})) = P.asIdeal :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  have hFq : F ∈ q := by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (mem_span_singleton_self F)]
    exact P.asIdeal.zero_mem
  have hDq : D F ∉ q := hP
  have hprime : (q.map (Ideal.Quotient.mk (span {F}))).IsPrime := by
    rw [hq]
    exact P.2
  have := isRegularLocalRing_localization_quotient_of_derivation D q hFq hDq
  rw [mem_regularLocus]
  revert this hprime
  rw [hq]
  intro _ h
  exact h

end Singularity.Algebra
