/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianBlowupLocal

/-!
# `Θ(u^p g) = Θ(g)` for a unit `u` at the origin

Let `k` be a field of characteristic `p`. Part 2 of Lemma 3.6 of research note 03 says that
`Θ(u^p g) = Θ(g)` for each unit `u` of the local ring. In `k[x]` the library has only
`Θ(u^p g) = (u^p) Θ(g)` (`logJacobian_pow_mul`), and the equality for a unit constant
(`logJacobian_C_mul`).

This file proves the equality in the local ring `O` of `k[x]` at the origin
(`OriginLocalRing σ k`), for each polynomial `u` with a nonzero constant term. Such a `u` is not a
unit of `k[x]` in general, but it is a unit of `O` (`isUnit_algebraMap_of_constantCoeff_ne_zero`).
So the image of `(u^p)` in `O` is the unit ideal, and `Θ(u^p g) O = Θ(g) O`
(`map_logJacobian_pow_mul_of_constantCoeff_ne_zero`).

The units of the power series ring that are not images of polynomials are not covered.

## Main results

* `map_logJacobian_pow_mul_of_constantCoeff_ne_zero`: `Θ(u^p g) O = Θ(g) O` if `u(0) ≠ 0`.

## References

* Research note 03, Section 3.3: Lemma 3.6, part 2.
* Volume 7, Section 3.1 of the handbook.
-/

open MvPolynomial

namespace Singularity

section UnitLocal

variable {σ k : Type*} [Field k] (p : ℕ) [CharP k p]

/-- **`Θ(u^p g) = Θ(g)` at the origin** (research note 03, Lemma 3.6, part 2). Let `u` be a
polynomial with a nonzero constant term. Then `Θ(u^p g)` and `Θ(g)` have the same image in the
local ring of `k[x]` at the origin. -/
theorem map_logJacobian_pow_mul_of_constantCoeff_ne_zero (Δ : Finset σ)
    {u : MvPolynomial σ k} (hu : constantCoeff u ≠ 0) (g : MvPolynomial σ k) :
    Ideal.map (algebraMap (MvPolynomial σ k) (OriginLocalRing σ k)) (logJacobian Δ (u ^ p * g)) =
      Ideal.map (algebraMap (MvPolynomial σ k) (OriginLocalRing σ k)) (logJacobian Δ g) := by
  have hup : constantCoeff (u ^ p) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero p hu
  have h : Ideal.map (algebraMap (MvPolynomial σ k) (OriginLocalRing σ k))
      (Ideal.span {u ^ p}) = ⊤ := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top]
    exact isUnit_algebraMap_of_constantCoeff_ne_zero hup
  rw [logJacobian_pow_mul p Δ u g, Ideal.map_mul, h, Ideal.top_mul]

end UnitLocal

end Singularity
