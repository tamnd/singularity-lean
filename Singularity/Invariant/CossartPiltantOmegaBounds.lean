/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.CossartPiltantOmega

/-!
# The bounds on the invariant `ω` of Cossart and Piltant

Let `k` be a field, let `g` be a polynomial in `k[x_i : i ∈ σ]`, and let `Δ` give the divisor
`E = V(∏_{i ∈ Δ} x_i)`. Write `g = x^r G` with `G = residualFactor Δ g`, and let `ε = ord G` be the
residual order. The invariant `ω = cpOmega Δ g` is the one of Volume 6, Definition 3.2.5 of the
handbook. This file proves Lemma 3.2.14 of Volume 6, Section 3.2 of the handbook for it.

1. `ε - 1 ≤ ω ≤ ε` (`ord_residualFactor_sub_one_le_cpOmega`, `cpOmega_le_ord_residualFactor`).
   The subtraction is the truncated one of `ℕ∞`, so the real content of `ω ≥ 0` is that the case
   `ω = ε - 1` of Definition 3.2.5 occurs only for `ε ≥ 1`
   (`one_le_ord_residualFactor_of_exists`). In this case `ω + 1 = ε`
   (`cpOmega_add_one_of_exists`).
2. For `g ≠ 0`, `ω = 0` if and only if `ε = 0`, or `ε = 1` and the linear form `in(G)` is not in
   the span of the `X_i` with `i ∈ Δ` (`cpOmega_eq_zero_iff`). The last condition is stated as:
   the coefficient of `x_j` in `G` is not `0` for some `j ∉ Δ`. For `ε = 1` the coefficients of
   the `x_j` in `G` are the coefficients of the linear form `in(G)`.
3. If `Δ` contains all the coordinates, then `ω = ε` (`cpOmega_eq_of_forall_mem`).

The handbook states the lemma for a clean `f^cl` in the power series ring `k[[u]]` over a perfect
field, with well adapted coordinates. Here `g` is a polynomial, and the statements hold for each
field `k` and each polynomial `g`. For a clean `g`, `ε` is the invariant `ε(x)` of the handbook by
Proposition 3.2.4(4).

## Main results

* `cpOmega_le_ord_residualFactor`, `ord_residualFactor_sub_one_le_cpOmega`,
  `ord_residualFactor_le_cpOmega_add_one`: part 1, `ε - 1 ≤ ω ≤ ε`.
* `one_le_ord_residualFactor_of_exists`, `cpOmega_add_one_of_exists`: part 1, `ω ≥ 0`.
* `cpOmega_eq_zero_iff`: part 2.
* `cpOmega_eq_of_forall_mem`: part 3.

## References

* Volume 6, Section 3.2 of the handbook: Definition 3.2.5 and Lemma 3.2.14.
-/

open MvPolynomial Finsupp

namespace Singularity

section Semiring

variable {σ k : Type*} [CommSemiring k] {Δ : Finset σ} {g : MvPolynomial σ k}

/-- **Lemma 3.2.14, part 1, `ω ≤ ε`** (Volume 6, Section 3.2 of the handbook). -/
theorem cpOmega_le_ord_residualFactor (Δ : Finset σ) (g : MvPolynomial σ k) :
    cpOmega Δ g ≤ ord (residualFactor Δ g) := by
  unfold cpOmega
  split_ifs
  · exact tsub_le_self
  · exact le_rfl

/-- **Lemma 3.2.14, part 1, `ε ≤ ω + 1`** (Volume 6, Section 3.2 of the handbook). -/
theorem ord_residualFactor_le_cpOmega_add_one (Δ : Finset σ) (g : MvPolynomial σ k) :
    ord (residualFactor Δ g) ≤ cpOmega Δ g + 1 := by
  unfold cpOmega
  split_ifs
  · exact le_tsub_add
  · exact le_self_add

/-- **Lemma 3.2.14, part 1, `ε - 1 ≤ ω`** (Volume 6, Section 3.2 of the handbook). -/
theorem ord_residualFactor_sub_one_le_cpOmega (Δ : Finset σ) (g : MvPolynomial σ k) :
    ord (residualFactor Δ g) - 1 ≤ cpOmega Δ g :=
  tsub_le_iff_right.mpr (ord_residualFactor_le_cpOmega_add_one Δ g)

/-- **Lemma 3.2.14, part 3** (Volume 6, Section 3.2 of the handbook). If `Δ` contains all the
coordinates, then there is no free coordinate, and `ω = ε`. -/
theorem cpOmega_eq_of_forall_mem (h : ∀ j, j ∈ Δ) : cpOmega Δ g = ord (residualFactor Δ g) :=
  cpOmega_of_forall fun j hj => absurd (h j) hj

/-- The homogeneous component of degree `0` is a constant, so its derivatives are `0`. -/
theorem pderiv_homogeneousComponent_zero (j : σ) (G : MvPolynomial σ k) :
    pderiv j (homogeneousComponent 0 G) = 0 := by
  rw [homogeneousComponent_zero, pderiv_C]

/-- The derivative along `x_j` of the linear part of `G` is the coefficient of `x_j` in `G`. So it
is not `0` if and only if this coefficient is not `0`. -/
theorem pderiv_homogeneousComponent_one_ne_zero_iff (j : σ) (G : MvPolynomial σ k) :
    pderiv j (homogeneousComponent 1 G) ≠ 0 ↔ G.coeff (Finsupp.single j 1) ≠ 0 := by
  classical
  constructor
  · intro h
    obtain ⟨b, hb⟩ := ne_zero_iff.mp h
    rw [coeff_pderiv] at hb
    have hc := left_ne_zero_of_mul hb
    rw [coeff_homogeneousComponent] at hc
    split_ifs at hc with hdeg
    · have hb0 : b = 0 := by
        rw [map_add, degree_single] at hdeg
        exact (degree_eq_zero_iff b).mp (by omega)
      rw [hb0, zero_add] at hc
      exact hc
    · exact absurd rfl hc
  · intro h
    refine ne_zero_iff.mpr ⟨0, ?_⟩
    rw [coeff_pderiv, zero_add, coeff_homogeneousComponent, degree_single, if_pos rfl]
    simpa using h

end Semiring

section Field

variable {σ k : Type*} [Field k] {Δ : Finset σ} {g : MvPolynomial σ k}

/-- **Lemma 3.2.14, part 1, `ω ≥ 0`** (Volume 6, Section 3.2 of the handbook). If `∂_j F ≠ 0` for
some free coordinate `x_j`, with `F` the initial form of `g`, then `ε ≥ 1`. The reason: `F` is
`x^r in(G)` and `∂_j F = x^r ∂_j in(G)`, so `in(G)` is not a constant. -/
theorem one_le_ord_residualFactor_of_exists
    (h : ∃ j ∉ Δ, pderiv j (homogeneousComponent (ord g).toNat g) ≠ 0) :
    1 ≤ ord (residualFactor Δ g) := by
  cases hd : ord (residualFactor Δ g) using ENat.recTopCoe with
  | top => exact le_top
  | coe d =>
    obtain ⟨j, -, hne⟩ := (exists_pderiv_initialForm_ne_zero_iff hd).mp h
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · exact absurd (pderiv_homogeneousComponent_zero j _) hne
    · exact_mod_cast (show 1 ≤ d by omega)

/-- **Lemma 3.2.14, part 1** (Volume 6, Section 3.2 of the handbook). In the first case of
Definition 3.2.5, `ω + 1 = ε`. So the subtraction `ε - 1` there is not truncated. -/
theorem cpOmega_add_one_of_exists
    (h : ∃ j ∉ Δ, pderiv j (homogeneousComponent (ord g).toNat g) ≠ 0) :
    cpOmega Δ g + 1 = ord (residualFactor Δ g) := by
  rw [cpOmega_of_exists h]
  exact tsub_add_cancel_of_le (one_le_ord_residualFactor_of_exists h)

/-- **Lemma 3.2.14, part 2** (Volume 6, Section 3.2 of the handbook). Let `g ≠ 0`. Then `ω = 0`
if and only if `ε = 0`, or `ε = 1` and the linear form `in(G)` is not in the span of the `X_i`
with `i ∈ Δ`, that is, `G` has a nonzero coefficient of `x_j` for some `j ∉ Δ`. -/
theorem cpOmega_eq_zero_iff (hg : g ≠ 0) :
    cpOmega Δ g = 0 ↔ ord (residualFactor Δ g) = 0 ∨
      (ord (residualFactor Δ g) = 1 ∧
        ∃ j ∉ Δ, (residualFactor Δ g).coeff (Finsupp.single j 1) ≠ 0) := by
  have hG : residualFactor Δ g ≠ 0 := by
    intro h0
    apply hg
    rw [← monomial_mul_residualFactor Δ g, h0, mul_zero]
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ord (residualFactor Δ g) = d :=
    ⟨(ord (residualFactor Δ g)).toNat, (ENat.natCast_toNat (ord_ne_top hG)).symm⟩
  have hiff := exists_pderiv_initialForm_ne_zero_iff hd
  rw [hd]
  by_cases hex : ∃ j ∉ Δ, pderiv j (homogeneousComponent (ord g).toNat g) ≠ 0
  · have h1 := cpOmega_add_one_of_exists hex
    rw [hd] at h1
    obtain ⟨j, hj, hne⟩ := hiff.mp hex
    have hd1 : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with rfl | hpos
      · exact absurd (pderiv_homogeneousComponent_zero j _) hne
      · omega
    constructor
    · intro h0
      rw [h0, zero_add] at h1
      have hd' : d = 1 := by exact_mod_cast h1.symm
      subst hd'
      exact Or.inr ⟨Nat.cast_one, j, hj, (pderiv_homogeneousComponent_one_ne_zero_iff j _).mp hne⟩
    · rintro (h0 | ⟨h0, -⟩)
      · have : d = 0 := by exact_mod_cast h0
        omega
      · have hd' : d = 1 := by exact_mod_cast h0
        subst hd'
        rw [cpOmega_of_exists hex, hd, Nat.cast_one, tsub_self]
  · rw [cpOmega_of_forall fun j hj => not_not.mp fun hne => hex ⟨j, hj, hne⟩, hd]
    constructor
    · exact Or.inl
    · rintro (h0 | ⟨h0, j, hj, hc⟩)
      · exact h0
      · exfalso
        have hd' : d = 1 := by exact_mod_cast h0
        subst hd'
        exact hex (hiff.mpr ⟨j, hj, (pderiv_homogeneousComponent_one_ne_zero_iff j _).mpr hc⟩)

end Field

end Singularity
