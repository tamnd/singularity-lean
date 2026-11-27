/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianNonincrease
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The transformation law as an equality in the local ring of the new point

Let `k` be a field of characteristic `p`, and let `π = pointChart j t` be the chart of `x_j` of
the blowup of the origin, followed by the translation `t`. The new point `x'` is the origin of the
chart. Let `π(g) = x_j^p g'`. The library proves Theorem 3.11 of research note 03 in `k[x]` as two
inclusions (`map_pointChart_logJacobianTangent_le_span_mul`,
`span_mul_logJacobian_le_map_pointChart`):

* `π(Θ₀(g)) ⊆ (x_j^p) Θ'(g')`;
* `(x_j^p u) Θ'(g') ⊆ π(Θ₀(g))`, with `u = blowupUnit Δ j t`.

The polynomial `u` is not a unit in `k[x]`, but its constant term is not `0`
(`constantCoeff_blowupUnit_ne_zero`). So `u` is a unit in the local ring `O_{x'}` of `k[x]` at the
maximal ideal `(x_i : i ∈ σ)` of the origin. This file proves the equality of Theorem 3.11 in
`O_{x'}`:

  `(x_j^p) Θ'(g') O_{x'} = π(Θ₀(g)) O_{x'}`.

Here `Θ'` is the log-Jacobian ideal for the new divisor `Δ' = blowupDivisor Δ j t`. Since `x_j` is
not a zero divisor, this is the equality `Θ_{E'}(g') = x_j^(-p) π^*Θ_C(g) O_{x'}` of the note.

## Main definitions

* `originIdeal σ k`: the maximal ideal of the origin, the kernel of the constant term.
* `OriginLocalRing σ k`: the localization of `k[x]` at `originIdeal σ k`.

## Main results

* `isUnit_algebraMap_blowupUnit`: `u` is a unit in `O_{x'}`.
* `map_logJacobian_eq_map_pointChart`: Theorem 3.11 of research note 03 as an equality of ideals
  of `O_{x'}`.

## References

* Research note 03, Section 3.5: Definition 3.10 and Theorem 3.11.
* Volume 7, Section 3.2 of the handbook: Theorem 3.2.3.
-/

open MvPolynomial

namespace Singularity

section Local

variable (σ k : Type*) [Field k]

/-- **The maximal ideal of the origin** of `k[x_i : i ∈ σ]`: the kernel of the constant term. -/
noncomputable def originIdeal : Ideal (MvPolynomial σ k) :=
  RingHom.ker (constantCoeff : MvPolynomial σ k →+* k)

instance originIdeal_isPrime : (originIdeal σ k).IsPrime :=
  RingHom.ker_isPrime _

/-- **The local ring of the origin**: the localization of `k[x_i : i ∈ σ]` at the maximal ideal of
the origin. -/
abbrev OriginLocalRing : Type _ :=
  Localization.AtPrime (originIdeal σ k)

variable {σ k}

/-- A polynomial is in the maximal ideal of the origin if and only if its constant term is `0`. -/
theorem mem_originIdeal {f : MvPolynomial σ k} : f ∈ originIdeal σ k ↔ constantCoeff f = 0 :=
  RingHom.mem_ker

/-- A polynomial with a nonzero constant term is a unit in the local ring of the origin. -/
theorem isUnit_algebraMap_of_constantCoeff_ne_zero {f : MvPolynomial σ k}
    (hf : constantCoeff f ≠ 0) : IsUnit (algebraMap (MvPolynomial σ k) (OriginLocalRing σ k) f) :=
  IsLocalization.map_units (OriginLocalRing σ k)
    (⟨f, fun h => hf (mem_originIdeal.mp h)⟩ : (originIdeal σ k).primeCompl)

variable [DecidableEq σ] [DecidableEq k]

/-- **The unit of the transformation law is a unit at the new point.** The polynomial
`u = blowupUnit Δ j t` is a unit in the local ring of the origin of the chart. -/
theorem isUnit_algebraMap_blowupUnit (Δ : Finset σ) (j : σ) (t : σ → k) :
    IsUnit (algebraMap (MvPolynomial σ k) (OriginLocalRing σ k) (blowupUnit Δ j t)) :=
  isUnit_algebraMap_of_constantCoeff_ne_zero (constantCoeff_blowupUnit_ne_zero Δ j t)

variable [Fintype σ] (p : ℕ) [CharP k p] {Δ : Finset σ} {j : σ} {t : σ → k}
  {g g' : MvPolynomial σ k}

/-- **The transformation law as an equality** (research note 03, Theorem 3.11; Volume 7,
Section 3.2 of the handbook, Theorem 3.2.3). Let `π = pointChart j t` and `π(g) = x_j^p g'`. In
the local ring `O_{x'}` of the new point, the origin of the chart,
`(x_j^p) Θ'(g') O_{x'} = π(Θ₀(g)) O_{x'}`, with `Θ'` the log-Jacobian ideal for the new divisor
`blowupDivisor Δ j t`. -/
theorem map_logJacobian_eq_map_pointChart (hg : pointChart j t g = X j ^ p * g') :
    Ideal.map (algebraMap (MvPolynomial σ k) (OriginLocalRing σ k))
        (Ideal.span {X j ^ p} * logJacobian (blowupDivisor Δ j t) g') =
      Ideal.map (algebraMap (MvPolynomial σ k) (OriginLocalRing σ k))
        (Ideal.map (pointChart j t) (logJacobianTangent Δ g)) := by
  set L := algebraMap (MvPolynomial σ k) (OriginLocalRing σ k)
  refine le_antisymm ?_ (Ideal.map_mono (map_pointChart_logJacobianTangent_le_span_mul p hg))
  have hu : Ideal.map L (Ideal.span {blowupUnit Δ j t}) = ⊤ := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top]
    exact isUnit_algebraMap_blowupUnit Δ j t
  calc Ideal.map L (Ideal.span {X j ^ p} * logJacobian (blowupDivisor Δ j t) g')
      = Ideal.map L (Ideal.span {X j ^ p} * Ideal.span {blowupUnit Δ j t} *
          logJacobian (blowupDivisor Δ j t) g') := by
        rw [Ideal.map_mul, Ideal.map_mul, Ideal.map_mul, hu, Ideal.mul_top]
    _ = Ideal.map L (Ideal.span {X j ^ p * blowupUnit Δ j t} *
          logJacobian (blowupDivisor Δ j t) g') := by
        rw [Ideal.span_singleton_mul_span_singleton]
    _ ≤ Ideal.map L (Ideal.map (pointChart j t) (logJacobianTangent Δ g)) :=
        Ideal.map_mono (span_mul_logJacobian_le_map_pointChart p hg)

end Local

end Singularity
