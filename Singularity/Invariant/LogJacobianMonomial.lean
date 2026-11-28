/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianEndCase
import Singularity.Valuation.WeakLogMonomialization
import Singularity.Algebra.MvPolynomialOrigin

/-!
# The end case `ρ = 0` gives a monomial modulo `p`-th powers

Let `k` be a field of characteristic `p`, let `E = V(∏_{i ∈ Δ} x_i)`, and write `g = x^r G` with `r = divisorExponent Δ g` and `G = residualFactor Δ g`. Let `L` be the local ring of `k[x_i : i ∈ σ]` at the origin. This file shows that the two end cases of the log-Jacobian order give an element `g` that is monomial modulo `p`-th powers in `L` (`IsMonomialModPow`). Both cases give the ramified type of `IsMonomialModPow`: `g = u ∏ y^{a_y}` for a regular system of parameters `y`, with a unit `u` and an exponent `a_y` that `p` does not divide.

1. Type 0 of Volume 7: `G(0) ≠ 0`, and `p ∤ r_i` for some `i ∈ Δ`. The parameters are the variables `x_i`. The exponents are `r`. The unit is `G`.
2. Type 1 of Volume 7: `G(0) = 0`, and `∂_j G(0) ≠ 0` for some `j ∉ Δ`. The parameters are the variables `x_i` with `i ≠ j`, and `G`. The exponents are `r_i` and `1`. The unit is `1`.

## Main definitions

* `Singularity.varExponent`: the exponent function on `L` that gives the exponent `r_i` to the image of `x_i`.

## Main results

* `Singularity.algebraMap_monomial_one`: the image of `x^r` in `L` is the product of the images `x_i ^ r_i`.
* `Singularity.varExponent_X`: the exponent of the image of `x_i` is `r_i`.
* `Singularity.isMonomialModPow_of_type_zero`: type 0 of Volume 7 gives the ramified type.
* `Singularity.isMonomialModPow_of_type_one`: type 1 of Volume 7 gives the ramified type.
* `Singularity.isMonomialModPow_of_logJacobianOrder_eq_zero`: for a clean `g` with `ρ = 0`, the image of `g` in `L` is monomial modulo `p`-th powers.

## The proof

The images of the variables are a regular system of parameters of `L` (`isRegularSystemOfParameters_X`). In type 0 the element `G` is not in the ideal of the origin, so its image is a unit of `L`. In type 1 the image of `G` replaces the parameter `x_j` (`isRegularSystemOfParameters_insert`). Since `j ∉ Δ`, the exponent `r_j` is `0`. So `x^r` is a monomial in the variables `x_i` with `i ≠ j`. The exponent of the parameter `G` is `1`, and `p ∤ 1`. The end case theorem `logJacobianOrder_eq_zero_iff` says that `ρ = 0` gives type 0 or type 1.

## What is not proved

The result is for the local ring of `k[x_i : i ∈ σ]` at the origin only. This file does not state the result for a general regular local ring with a regular system of parameters. It does not use a blow-up, and it does not treat the case `ρ > 0`. It does not prove `WeakLogMonomialization`.

## References

* Volume 7, Section 3.5 of the handbook: Proposition 3.5.1 and Theorem 3.5.3.
* Volume 5, Chapter 4 of the handbook.
-/

open MvPolynomial IsLocalRing Singularity.Algebra

namespace Singularity

variable {σ k : Type*} [Fintype σ] [Field k]

/-- The image of the monomial `x^r` in `L` is the product of the images `x_i ^ r_i`. -/
theorem algebraMap_monomial_one (r : σ →₀ ℕ) :
    algebraMap (MvPolynomial σ k) (OriginLocalRing σ k) (monomial r 1) =
      ∏ i, algebraMap (MvPolynomial σ k) (OriginLocalRing σ k) (X i) ^ r i := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod]
  simp only [map_pow]

/-- The exponent function on `L` that gives the exponent `r_i` to the image of `x_i`, and `0` to the other elements. -/
noncomputable def varExponent (r : σ →₀ ℕ) (y : OriginLocalRing σ k) : ℕ := by
  classical
  exact ∑ i, if algebraMap (MvPolynomial σ k) (OriginLocalRing σ k) (X i) = y then r i else 0

/-- The exponent of the image of `x_i` is `r_i`. -/
theorem varExponent_X (r : σ →₀ ℕ) (i : σ) :
    varExponent r (algebraMap (MvPolynomial σ k) (OriginLocalRing σ k) (X i)) = r i := by
  classical
  unfold varExponent
  convert Finset.sum_ite_eq' Finset.univ i (fun l => r l) using 2 with l
  · simp only [(algebraMap_X_injective σ k).eq_iff]
  · simp

variable (p : ℕ) [Fact p.Prime] {Δ : Finset σ} {g : MvPolynomial σ k}

/-- **Type 0 of Volume 7 gives the ramified type.** The hypothesis is type 0: the constant term of the residual factor `G` is not zero (`G(0) ≠ 0`), and `p` does not divide the exponent `r_i` of some `i ∈ Δ`. Then the image of `g = x^r G` in `L` is monomial modulo `p`-th powers. The parameters are the variables, the exponents are `r` and the unit is `G`. This is the ramified type of `IsMonomialModPow`. -/
theorem isMonomialModPow_of_type_zero (h0 : constantCoeff (residualFactor Δ g) ≠ 0)
    (hr : ∃ i ∈ Δ, ¬ p ∣ divisorExponent Δ g i) :
    IsMonomialModPow p (algebraMap (MvPolynomial σ k) (OriginLocalRing σ k) g) := by
  classical
  set φ := algebraMap (MvPolynomial σ k) (OriginLocalRing σ k)
  set r := divisorExponent Δ g
  set G := residualFactor Δ g
  have hGu : IsUnit (φ G) :=
    IsLocalization.map_units (OriginLocalRing σ k)
      (⟨G, fun hG => h0 (mem_originIdeal.mp hG)⟩ : (originIdeal σ k).primeCompl)
  obtain ⟨i, -, hi⟩ := hr
  refine ⟨0, 1, φ G, Finset.univ.image fun i => φ (X i), varExponent r,
    isRegularSystemOfParameters_X σ k, hGu, one_ne_zero, ?_, Or.inl ⟨φ (X i), ?_, ?_⟩⟩
  · rw [zero_pow (Fact.out : p.Prime).ne_zero, one_pow, one_mul, zero_add,
      Finset.prod_image fun a _ b _ h => algebraMap_X_injective σ k h]
    simp only [varExponent_X]
    rw [← algebraMap_monomial_one, ← map_mul, mul_comm, monomial_mul_residualFactor]
  · exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  · rwa [varExponent_X]

/-- **Type 1 of Volume 7 gives the ramified type.** The hypothesis is type 1: the constant term of the residual factor `G` is zero (`G(0) = 0`), and the partial derivative of `G` along a variable `x_j` with `j ∉ Δ` is not zero at the origin (`∂_j G(0) ≠ 0`). Then the image of `g = x^r G` in `L` is monomial modulo `p`-th powers. The parameters are the variables `x_i` with `i ≠ j`, and `G`. The exponent of `G` is `1`, and the unit is `1`. This is the ramified type of `IsMonomialModPow`. -/
theorem isMonomialModPow_of_type_one (h0 : constantCoeff (residualFactor Δ g) = 0)
    (hj : ∃ j ∉ Δ, constantCoeff (pderiv j (residualFactor Δ g)) ≠ 0) :
    IsMonomialModPow p (algebraMap (MvPolynomial σ k) (OriginLocalRing σ k) g) := by
  classical
  set φ := algebraMap (MvPolynomial σ k) (OriginLocalRing σ k)
  set r := divisorExponent Δ g
  set G := residualFactor Δ g
  obtain ⟨j, hjΔ, hj⟩ := hj
  set T := (Finset.univ.erase j).image fun i => φ (X i)
  have hGT : φ G ∉ T := algebraMap_notMem_image hj
  let a : OriginLocalRing σ k → ℕ := fun y => if y = φ G then 1 else varExponent r y
  refine ⟨0, 1, 1, insert (φ G) T, a, isRegularSystemOfParameters_insert h0 hj, isUnit_one,
    one_ne_zero, ?_, Or.inl ⟨φ G, Finset.mem_insert_self _ _, ?_⟩⟩
  · rw [zero_pow (Fact.out : p.Prime).ne_zero, one_pow, one_mul, zero_add, one_mul,
      Finset.prod_insert hGT, Finset.prod_image fun a _ b _ h => algebraMap_X_injective σ k h]
    have hT : ∀ i ∈ Finset.univ.erase j, a (φ (X i)) = r i := by
      intro i hi
      have hne : φ (X i) ≠ φ G := fun h => hGT (h ▸ Finset.mem_image_of_mem _ hi)
      simp only [a, hne, ite_false]
      exact varExponent_X r i
    rw [Finset.prod_congr rfl fun i hi => by rw [hT i hi]]
    rw [Finset.prod_erase Finset.univ (f := fun i => φ (X i) ^ r i)
      (by rw [show r j = 0 from divisorExponent_eq_zero hjΔ, pow_zero])]
    simp only [a, ite_true, pow_one]
    rw [← algebraMap_monomial_one, ← map_mul, mul_comm, monomial_mul_residualFactor]
  · simp only [a, ite_true]
    exact (Fact.out : p.Prime).not_dvd_one

/-- **The end case gives a monomial modulo `p`-th powers** (Volume 7, Section 3.5 of the handbook, Proposition 3.5.1 and Theorem 3.5.3). For a clean `g` with `ρ = 0`, the image of `g` in the local ring `L` at the origin is monomial modulo `p`-th powers. Type 0 and type 1 of Volume 7 both give the ramified type of `IsMonomialModPow`. -/
theorem isMonomialModPow_of_logJacobianOrder_eq_zero [CharP k p] (hc : IsClean p g)
    (hρ : logJacobianOrder Δ g = 0) :
    IsMonomialModPow p (algebraMap (MvPolynomial σ k) (OriginLocalRing σ k) g) := by
  rcases (logJacobianOrder_eq_zero_iff p hc).mp hρ with ⟨h0, hr⟩ | ⟨h0, hj⟩
  · exact isMonomialModPow_of_type_zero p h0 hr
  · exact isMonomialModPow_of_type_one p h0 hj

end Singularity
