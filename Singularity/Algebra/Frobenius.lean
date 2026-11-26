/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.CharP.Reduced
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# The first properties of the Frobenius

Let `R` be a ring of characteristic `p` and let `F : R → R`, `F(a) = a^p`, be the Frobenius (`frobenius R p` in Mathlib). This file proves two results of Volume 1, Section 6.1 of the handbook.

* `Singularity.Algebra.comap_frobenius_eq` and `Singularity.Algebra.primeSpectrum_comap_frobenius`: for each prime ideal `𝔭`, `F⁻¹(𝔭) = 𝔭`, so the map of `Spec R` that `F` gives is the identity (Volume 1, Lemma 6.1.2 of the handbook).
* `Singularity.Algebra.injective_frobenius_iff_isReduced`: `F` is injective if and only if `R` is reduced (Volume 1, Proposition 6.1.3 of the handbook).

Lemma 6.1.2 holds for each exponential characteristic `p`. Proposition 6.1.3 needs that `p` is prime: in characteristic `0` the Frobenius is the identity.
-/

namespace Singularity.Algebra

variable (R : Type*) [CommRing R]

/-- Let `R` be a ring of exponential characteristic `p` and let `𝔭` be a prime ideal. Then `F⁻¹(𝔭) = 𝔭` (Volume 1, Lemma 6.1.2 of the handbook). -/
theorem comap_frobenius_eq (p : ℕ) [ExpChar R p] (P : Ideal R) [P.IsPrime] :
    P.comap (frobenius R p) = P := by
  ext a
  rw [Ideal.mem_comap, frobenius_def]
  exact ⟨fun h => (inferInstance : P.IsPrime).mem_of_pow_mem p h,
    fun h => P.pow_mem_of_mem h p (expChar_pos R p)⟩

/-- The map of `Spec R` that the Frobenius gives is the identity (Volume 1, Lemma 6.1.2 of the handbook). -/
theorem primeSpectrum_comap_frobenius (p : ℕ) [ExpChar R p] :
    PrimeSpectrum.comap (frobenius R p) = fun P => P := by
  funext P
  apply PrimeSpectrum.ext
  rw [PrimeSpectrum.comap_asIdeal]
  exact comap_frobenius_eq R p P.asIdeal

/-- Let `R` be a ring of prime characteristic `p`. Then the Frobenius of `R` is injective if and only if `R` is reduced (Volume 1, Proposition 6.1.3 of the handbook). -/
theorem injective_frobenius_iff_isReduced (p : ℕ) [Fact p.Prime] [CharP R p] :
    Function.Injective (frobenius R p) ↔ IsReduced R := by
  refine ⟨fun h => ⟨fun x ⟨n, hn⟩ => ?_⟩, fun _ => frobenius_inj R p⟩
  have hle : n ≤ p ^ n := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have h0 : (frobenius R p)^[n] x = (frobenius R p)^[n] 0 := by
    rw [iterate_frobenius, iterate_frobenius, zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero),
      ← Nat.sub_add_cancel hle, pow_add, hn, mul_zero]
  exact (h.iterate n) h0

end Singularity.Algebra
