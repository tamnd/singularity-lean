/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.Frobenius
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The Frobenius is flat at each prime

This file proves Volume 1, Lemma 6.4.2 of the handbook. Let `R` be a ring of characteristic `p`. Then the Frobenius of `R` is flat if and only if the Frobenius of `R_𝔭` is flat for each prime `𝔭` of `R`.

* `Singularity.Algebra.charP_localization_atPrime`: the ring `R_𝔭` has characteristic `p`.
* `Singularity.Algebra.localRingHom_frobenius`: the map that the Frobenius of `R` induces on `R_𝔭` is the Frobenius of `R_𝔭`.
* `Singularity.Algebra.flat_frobenius_iff_forall_localization`: Lemma 6.4.2 of the handbook.

The proof is the proof of the handbook in the language of ring homomorphisms. The Frobenius of `R_𝔭` is the localization of the Frobenius of `R` at `𝔭`, because `𝔭` is its own inverse image. Flatness of a ring homomorphism is local on the target (`RingHom.Flat.ofLocalizationPrime`), and it is preserved by localization (`RingHom.Flat.localRingHom`).
-/

namespace Singularity.Algebra

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]

/-- Let `R` be a ring of characteristic `p` and let `P` be a prime of `R`. Then `R_P` has characteristic `p`. This is an instance. -/
instance charP_localization_atPrime (P : Ideal R) [P.IsPrime] :
    CharP (Localization.AtPrime P) p :=
  (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
    rw [← map_natCast (algebraMap R (Localization.AtPrime P)), CharP.cast_eq_zero, map_zero])

variable (R p)

/-- Let `P` be a prime of `R`. The map `R_P → R_P` that the Frobenius of `R` induces is the Frobenius of `R_P`. -/
theorem localRingHom_frobenius (P : Ideal R) [P.IsPrime] (h : P = P.comap (frobenius R p)) :
    Localization.localRingHom P P (frobenius R p) h = frobenius (Localization.AtPrime P) p := by
  refine IsLocalization.ringHom_ext P.primeCompl ?_
  ext x
  simp only [RingHom.comp_apply, Localization.localRingHom_to_map, frobenius_def, map_pow]

/-- Volume 1, Lemma 6.4.2 of the handbook. Let `R` be a ring of characteristic `p`. Then the Frobenius of `R` is flat if and only if the Frobenius of `R_P` is flat for each prime `P` of `R`. -/
theorem flat_frobenius_iff_forall_localization :
    (frobenius R p).Flat ↔ ∀ (P : Ideal R) [P.IsPrime],
      (frobenius (Localization.AtPrime P) p).Flat := by
  have key : ∀ (P : Ideal R) [P.IsPrime] (Q : Ideal R) [Q.IsPrime]
      (hQ : Q = P.comap (frobenius R p)),
      (frobenius (Localization.AtPrime P) p).Flat →
      (Localization.localRingHom Q P (frobenius R p) hQ).Flat := by
    intro P _ Q _ hQ hP
    obtain rfl : Q = P := hQ.trans (comap_frobenius_eq R p P)
    rw [localRingHom_frobenius R p Q hQ]
    exact hP
  constructor
  · intro hF P _
    rw [← localRingHom_frobenius R p P (comap_frobenius_eq R p P).symm]
    exact hF.localRingHom P P (comap_frobenius_eq R p P).symm
  · intro h
    exact RingHom.Flat.ofLocalizationPrime (frobenius R p) fun J _ =>
      key J (J.comap (frobenius R p)) rfl (h J)

end Singularity.Algebra
