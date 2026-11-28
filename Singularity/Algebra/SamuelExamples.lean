/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.MultiplicityRegular
import Singularity.Algebra.RegularOrderMul
import Singularity.Algebra.HypersurfaceHeight
import Singularity.Algebra.Regular
import Singularity.Algebra.Jacobian
import Singularity.Algebra.LocalPolynomialCompletion
import Singularity.Algebra.PBasisExistence
import Singularity.Algebra.PIndependence
import Singularity.Example.ImperfectField
import Singularity.Invariant.Order
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Examples and results of Volume 1: completion, Hilbert-Samuel functions, `p`-bases

This file proves parts of Volume 1, Proposition 4.2.8, Example 3.1.6, Example 3.3.16,
Proposition 6.2.5 and Example 1.8.19 of the handbook.

## Proposition 4.2.8

Let `I` be a finitely generated ideal of `R` and let `R̂` be the `I`-adic completion.

* `Singularity.Algebra.ker_evalₐ_eq_map_pow`: the kernel of `R̂ → R/I^n` is `I^n R̂`.
* `Singularity.Algebra.adicCompletionQuotientPowAlgEquiv`: `R̂/I^n R̂ ≃ R/I^n`.
* `Singularity.Algebra.map_pow_adicCompletion`: `(I R̂)^n = I^n R̂`.
* `Singularity.Algebra.isAdicComplete_map_adicCompletion`: `R̂` is `I R̂`-adically complete.
* `Singularity.Algebra.map_le_jacobson_adicCompletion`: `I R̂` is in the Jacobson radical.

The handbook states this for a Noetherian ring. Here only `I.FG` is used.

## Example 3.1.6

Let `k` be a field and let `S = k[x_1, ..., x_d]` localized at `(x_1, ..., x_d)`. This is
`Singularity.Algebra.AffineOriginRing k d`.

* `Singularity.Algebra.isRegularLocalRing_affineOriginRing` and
  `Singularity.Algebra.ringKrullDim_affineOriginRing`: `S` is regular local of dimension `d`.
* `Singularity.Algebra.hilbertSamuel_affineOriginRing_succ`: `χ_S(j + 1) = C(j + d, d)`.
* `Singularity.Algebra.hilbertSamuel_affineOriginRing_eq_sum`: for `d = e + 1`,
  `χ_S(j) = ∑_{i < j} C(i + e, e) = C(j + e, e + 1)`.
* `Singularity.Algebra.factorial_mul_hilbertSamuel_affineOriginRing`: for `d = e + 1`,
  `d! χ_S(j) = (j + e)(j + e - 1) ... j`. So `χ_S` is a polynomial with leading term `j^d / d!`.
* `Singularity.Algebra.samuelMultiplicity_affineOriginRing`: `e(S) = 1`.

## Example 3.3.16

For `F ∈ k[x_0, ..., x_n]` of order `d ≥ 1` at the origin, the ring `S/(F)` with
`S = AffineOriginRing k (n + 1)` is `Singularity.Algebra.HypersurfaceGerm F`. Its maximal ideal
is `Singularity.Algebra.hypersurfaceGermIdeal F`, the image of the maximal ideal of `S`.

* `Singularity.Algebra.algebraMap_mem_maximalIdeal_pow_iff`: the image of `F` in `S` is in
  `𝔪^e` if and only if `e ≤ ord F`.
* `Singularity.Algebra.hilbertSamuel_germ_of_le`, `Singularity.Algebra.hilbertSamuel_germ_add`
  and `Singularity.Algebra.samuelMultiplicity_germ`: the Hilbert-Samuel function and the
  multiplicity `e(S/(F)) = ord F`.
* `Singularity.Algebra.hilbertSamuel_planeCurve`: for a plane curve of order `d`,
  `χ(N) = d N - C(d, 2)` for `N ≥ d - 1`.
* `Singularity.Algebra.hilbertSamuel_cusp`, `Singularity.Algebra.hilbertSamuel_node`:
  `χ(N) = 2N - 1` for `N ≥ 1`, and the multiplicity is `2`.
* `Singularity.Algebra.hilbertSamuel_x3_add_y5`, `Singularity.Algebra.hilbertSamuel_x2y_add_y4`:
  `χ(N) = 3N - 3` for `N ≥ 2`, and the multiplicity is `3`.
* `Singularity.Algebra.samuelMultiplicity_xa_add_yb`: the curve `x^a + y^b` with `1 ≤ a ≤ b`
  has multiplicity `a`.
* `Singularity.Algebra.hilbertSamuel_surface_two`: a surface of order `2` has `χ(N) = N^2` for
  each `N` and multiplicity `2`. This applies to `xy - z^2`, to `A_m` (`xy - z^(m+1)`, `m ≥ 1`)
  and to the Whitney umbrella `x^2 - y^2 z` (`Singularity.Algebra.ord_xy_sub_z2`,
  `Singularity.Algebra.ord_am`, `Singularity.Algebra.ord_umbrella`).
* `Singularity.Algebra.hilbertSamuel_surface_three`: a surface of order `3` has
  `χ(N) = 3 C(N, 2) + 1` for `N ≥ 1`. For the cubic cone `x^3 + y^3 + z^3` this gives the values
  `1, 4, 10, 19, 31, 46` (`Singularity.Algebra.hilbertSamuel_cubicCone_values`), and
  `Δ²χ = 3` (`Singularity.Algebra.hilbertSamuel_surface_three_fwdDiff`).

## Proposition 6.2.5

Only the case `n = 1`, `K = k(t)` is proved. Let `k` be a perfect field of characteristic `p`.

* `Singularity.Algebra.isPBasis_ratFunc_X`: `{t}` is a `p`-basis of `k(t)` over `k`.
* `Singularity.Algebra.finrank_pSubring_ratFunc`: `[k(t) : k(t)^p] = p`.

## Example 1.8.19

Let `K` be a field and `δ` an additive derivation of `K`. Then
`Singularity.Algebra.coeffDerivation δ` is the derivation of `K[x, y]` that applies `δ` to each
coefficient. Let `f = y^2 - x^p + t`.

* `Singularity.Algebra.isRegularRing_quotient_of_derivation_eq_one`: if a derivation sends `F`
  to `1`, then `A/(F)` is regular, for `A` regular.
* `Singularity.Algebra.isRegularRing_example_1_8_19`: if `δ t = 1` for a derivation `δ` of
  `K` over some ring, then `K[x, y]/(f)` is a regular ring.
* `Singularity.Algebra.isRegularRing_example_1_8_19_ratFunc`: the case `K = k(t)`, `k` perfect
  of characteristic `p`, with `δ = ∂/∂t` from the `p`-basis `{t}`.
* `Singularity.Algebra.derivation_example_1_8_19` and
  `Singularity.Algebra.derivation_example_1_8_19_mem`: in characteristic `p`, each `K`-linear
  derivation `D` has `D f = 2 y D(y)`, which lies in `n = (x^p - t, y)`. Also
  `Singularity.Algebra.pderiv_zero_example_1_8_19`: `∂f/∂x = 0`.
* `Singularity.Algebra.example_1_8_19_baseChange` and
  `Singularity.Algebra.example_1_8_19_baseChange_mem`: if `a^p = t`, then
  `f = y^2 - (x - a)^p`, and this lies in `(x - a, y)^2`.
* `Singularity.Algebra.derivation_pow_char_eq_zero`: each derivation kills `t = a^p`.

## What is not proved

* Proposition 6.2.5 in general: `[K : K^p] = p^n` for a finitely generated `K` of transcendence
  degree `n`, and the claim that a separating transcendence basis is a `p`-basis. Only
  `K = k(t)` is done.
* In Example 1.8.19: that `n` is a maximal ideal, and that the base change `A ⊗_k k'` is not
  regular at `(x - a, y)`. Only the facts that lead to these claims are proved.
* In Example 3.3.16: the blowup chart paragraph on `A_m`.
* Proposition 4.2.8 is stated for a finitely generated ideal `I`, not for a Noetherian ring.
  This covers the Noetherian case, where each ideal is finitely generated.
-/

namespace Singularity

namespace Algebra

open IsLocalRing Ideal MvPolynomial

/-! ### Proposition 4.2.8 -/

section Completion

open AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- Volume 1, Proposition 4.2.8 (1) of the handbook: the kernel of `R̂ → R/I^n` is `I^n R̂`. -/
theorem ker_evalₐ_eq_map_pow (fg : I.FG) (n : ℕ) :
    RingHom.ker (evalₐ I n) = (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  ext x
  have h1 : (I ^ n • ⊤ : Ideal R) ≤ I ^ n := by simp
  have h2 : I ^ n ≤ (I ^ n • ⊤ : Ideal R) := by simp
  trans x ∈ LinearMap.ker (AdicCompletion.eval I R n)
  · rw [RingHom.mem_ker, LinearMap.mem_ker]
    constructor
    · intro hx
      rw [← factor_evalₐ_eq_eval I x h2, hx, _root_.map_zero]
    · intro hx
      rw [← factor_eval_eq_evalₐ I x h1, hx, _root_.map_zero]
  · rw [← pow_smul_top_eq_ker_eval fg, Ideal.smul_top_eq_map]
    rfl

/-- Volume 1, Proposition 4.2.8 (1) of the handbook: `R̂/I^n R̂ ≃ R/I^n`. -/
noncomputable def adicCompletionQuotientPowAlgEquiv (fg : I.FG) (n : ℕ) :
    (AdicCompletion I R ⧸ (I ^ n).map (algebraMap R (AdicCompletion I R))) ≃ₐ[R]
      R ⧸ I ^ n :=
  (Ideal.quotientEquivAlgOfEq R (ker_evalₐ_eq_map_pow I fg n).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (surjective_evalₐ I n))

/-- Volume 1, Proposition 4.2.8 (2) of the handbook: `(I R̂)^n = I^n R̂`. -/
theorem map_pow_adicCompletion (n : ℕ) :
    (I.map (algebraMap R (AdicCompletion I R))) ^ n =
      (I ^ n).map (algebraMap R (AdicCompletion I R)) :=
  (Ideal.map_pow _ I n).symm

/-- Volume 1, Proposition 4.2.8 (2) of the handbook: `R̂` is `I R̂`-adically complete. -/
theorem isAdicComplete_map_adicCompletion (fg : I.FG) :
    IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) :=
  AdicCompletion.isAdicComplete_self I fg

/-- Volume 1, Proposition 4.2.8 (3) of the handbook: `I R̂` is in the Jacobson radical. -/
theorem map_le_jacobson_adicCompletion (fg : I.FG) :
    I.map (algebraMap R (AdicCompletion I R)) ≤ (⊥ : Ideal (AdicCompletion I R)).jacobson := by
  have := isAdicComplete_map_adicCompletion I fg
  exact IsAdicComplete.le_jacobson_bot (I.map (algebraMap R (AdicCompletion I R)))

end Completion

/-! ### Example 3.1.6 -/

section AffineOrigin

variable (k : Type*) [Field k] (m : ℕ)

/-- The local ring `k[x_1, ..., x_m]` localized at `(x_1, ..., x_m)`. -/
abbrev AffineOriginRing : Type _ := Localization.AtPrime (idealOfVars (Fin m) k)

theorem isRegularLocalRing_affineOriginRing : IsRegularLocalRing (AffineOriginRing k m) :=
  inferInstance

theorem ringKrullDim_affineOriginRing : ringKrullDim (AffineOriginRing k m) = m := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (idealOfVars (Fin m) k)
      (AffineOriginRing k m),
    height_isMaximal_mvPolynomial m]
  all_goals norm_cast

/-- Volume 1, Example 3.1.6 of the handbook: `χ(j + 1) = C(j + m, m)`. -/
theorem hilbertSamuel_affineOriginRing_succ (j : ℕ) :
    hilbertSamuel (maximalIdeal (AffineOriginRing k m)) (AffineOriginRing k m) (j + 1) =
      (j + m).choose m :=
  hilbertSamuel_succ_eq_choose (ringKrullDim_affineOriginRing k m) j

/-- The sum `∑_{i < j} C(i + e, e) = C(j + e, e + 1)`. -/
theorem sum_range_choose_add (e j : ℕ) :
    ∑ i ∈ Finset.range j, (i + e).choose e = (j + e).choose (e + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ih, show j + 1 + e = j + e + 1 by omega,
      Nat.choose_succ_succ' (j + e) e]
    omega

/-- Volume 1, Example 3.1.6 of the handbook, for `m = e + 1`:
`χ(j) = ∑_{i < j} C(i + e, e) = C(j + e, e + 1)`. -/
theorem hilbertSamuel_affineOriginRing_eq_sum (e j : ℕ) :
    hilbertSamuel (maximalIdeal (AffineOriginRing k (e + 1))) (AffineOriginRing k (e + 1)) j =
      (∑ i ∈ Finset.range j, (i + e).choose e : ℕ) ∧
    hilbertSamuel (maximalIdeal (AffineOriginRing k (e + 1))) (AffineOriginRing k (e + 1)) j =
      (j + e).choose (e + 1) := by
  have h := hilbertSamuel_eq_choose (ringKrullDim_affineOriginRing k (e + 1)) j
  exact ⟨by rw [h, sum_range_choose_add], h⟩

/-- Volume 1, Example 3.1.6 of the handbook: `(e + 1)! χ(j) = (j + e) (j + e - 1) ... j`. So
`χ` is a polynomial of degree `e + 1` with leading coefficient `1 / (e + 1)!`. -/
theorem factorial_mul_hilbertSamuel_affineOriginRing (e j : ℕ) :
    ((e + 1).factorial : ℕ∞) *
        hilbertSamuel (maximalIdeal (AffineOriginRing k (e + 1))) (AffineOriginRing k (e + 1)) j =
      ((j + e).descFactorial (e + 1) : ℕ) := by
  rw [hilbertSamuel_eq_choose (ringKrullDim_affineOriginRing k (e + 1)) j,
    Nat.descFactorial_eq_factorial_mul_choose]
  exact (Nat.cast_mul _ _).symm

/-- Volume 1, Example 3.1.6 of the handbook: the length of `𝔪^j / 𝔪^(j+1)` is
`C(j + e, e)`. -/
theorem length_grPiece_affineOriginRing (e j : ℕ) :
    Module.length (AffineOriginRing k (e + 1))
        (grPiece (maximalIdeal (AffineOriginRing k (e + 1))) (AffineOriginRing k (e + 1)) j) =
      (j + e).choose e :=
  length_grPiece_eq_choose (ringKrullDim_affineOriginRing k (e + 1)) j

/-- Volume 1, Example 3.1.6 of the handbook: the multiplicity of `S` is `1`. -/
theorem samuelMultiplicity_affineOriginRing :
    samuelMultiplicity (maximalIdeal (AffineOriginRing k m)) (AffineOriginRing k m) m = 1 :=
  samuelMultiplicity_regular _ (ringKrullDim_affineOriginRing k m)

end AffineOrigin

/-! ### Example 3.3.16 -/

section Germ

variable {k : Type*} [Field k] {m : ℕ}

/-- The image of `F` in the local ring at the origin is in `𝔪^e` if and only if `e ≤ ord F`. -/
theorem algebraMap_mem_maximalIdeal_pow_iff (F : MvPolynomial (Fin m) k) (e : ℕ) :
    algebraMap (MvPolynomial (Fin m) k) (AffineOriginRing k m) F ∈
        maximalIdeal (AffineOriginRing k m) ^ e ↔ (e : ℕ∞) ≤ ord F := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := idealOfVars (Fin m) k), ← Ideal.map_pow,
    le_ord_iff_mem_pow]
  refine ⟨fun h => ?_, fun h => Ideal.mem_map_of_mem _ h⟩
  obtain ⟨⟨⟨g, hg⟩, ⟨s, hs⟩⟩, h⟩ := (IsLocalization.mem_map_algebraMap_iff
    (idealOfVars (Fin m) k).primeCompl (AffineOriginRing k m)).mp h
  simp only at h
  rw [← map_mul] at h
  have h' := IsLocalization.injective (AffineOriginRing k m)
    (primeCompl_le_nonZeroDivisors (idealOfVars (Fin m) k)) h
  have hs0 : ord s = 0 := by
    have hn : ¬ 1 ≤ ord s := by
      rw [one_le_ord_iff, ← Singularity.mem_idealOfVars_iff]
      exact hs
    by_contra h0
    exact hn (Order.one_le_iff_ne_zero.mpr h0)
  rw [← h', ← le_ord_iff_mem_pow, ord_mul, hs0, add_zero] at hg
  exact le_ord_iff_mem_pow.mp hg

/-- The hypersurface germ `S/(F)`, for `S` the local ring of `k^m` at the origin. -/
abbrev HypersurfaceGerm (F : MvPolynomial (Fin m) k) : Type _ :=
  AffineOriginRing k m ⧸ span {algebraMap (MvPolynomial (Fin m) k) (AffineOriginRing k m) F}

/-- The image of the maximal ideal of `S` in `S/(F)`. -/
noncomputable def hypersurfaceGermIdeal (F : MvPolynomial (Fin m) k) :
    @Ideal (HypersurfaceGerm F) CommRing.toCommSemiring.toSemiring :=
  (maximalIdeal (AffineOriginRing k m)).map (Ideal.Quotient.mk _)

theorem algebraMap_mem_pow_of_ord_eq {F : MvPolynomial (Fin m) k} {d : ℕ} (hF : ord F = d) :
    algebraMap (MvPolynomial (Fin m) k) (AffineOriginRing k m) F ∈
      maximalIdeal (AffineOriginRing k m) ^ d :=
  (algebraMap_mem_maximalIdeal_pow_iff F d).mpr hF.ge

theorem algebraMap_notMem_pow_succ_of_ord_eq {F : MvPolynomial (Fin m) k} {d : ℕ}
    (hF : ord F = d) :
    algebraMap (MvPolynomial (Fin m) k) (AffineOriginRing k m) F ∉
      maximalIdeal (AffineOriginRing k m) ^ (d + 1) := by
  rw [algebraMap_mem_maximalIdeal_pow_iff, hF]
  exact_mod_cast (by omega : ¬ d + 1 ≤ d)

theorem isLocalRing_hypersurfaceGerm {F : MvPolynomial (Fin m) k} {d : ℕ} (hd : 1 ≤ d)
    (hF : ord F = d) : IsLocalRing (HypersurfaceGerm F) := by
  refine isLocalRing_quotient_of_le_maximalIdeal ((span_singleton_le_iff_mem _).mpr ?_)
  exact Ideal.pow_le_self (by omega) (algebraMap_mem_pow_of_ord_eq hF)

theorem hypersurfaceGermIdeal_eq {F : MvPolynomial (Fin m) k} [IsLocalRing (HypersurfaceGerm F)] :
    hypersurfaceGermIdeal F = maximalIdeal (HypersurfaceGerm F) :=
  (maximalIdeal_quotient_eq_map _).symm

variable {n : ℕ}

/-- Volume 1, Example 3.3.16 of the handbook: `χ(N) = C(N + n, n + 1)` for `N ≤ ord F`. -/
theorem hilbertSamuel_germ_of_le {F : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hd : 1 ≤ d)
    (hF : ord F = d) {N : ℕ} (hN : N ≤ d) :
    hilbertSamuel (hypersurfaceGermIdeal F) (HypersurfaceGerm F) N = (N + n).choose (n + 1) := by
  have := isLocalRing_hypersurfaceGerm hd hF
  rw [hypersurfaceGermIdeal_eq]
  exact hilbertSamuel_hypersurface_of_le (ringKrullDim_affineOriginRing k (n + 1))
    (algebraMap_mem_pow_of_ord_eq hF) hN

/-- Volume 1, Example 3.3.16 of the handbook:
`χ(N + d) = C(N + d + n, n + 1) - C(N + n, n + 1)` for `d = ord F`. -/
theorem hilbertSamuel_germ_add {F : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hd : 1 ≤ d)
    (hF : ord F = d) (N : ℕ) :
    hilbertSamuel (hypersurfaceGermIdeal F) (HypersurfaceGerm F) (N + d) =
      (((N + d + n).choose (n + 1) - (N + n).choose (n + 1) : ℕ) : ℕ∞) := by
  have := isLocalRing_hypersurfaceGerm hd hF
  rw [hypersurfaceGermIdeal_eq]
  exact hilbertSamuel_hypersurface_add_of_notMem (ringKrullDim_affineOriginRing k (n + 1))
    (algebraMap_mem_pow_of_ord_eq hF) (algebraMap_notMem_pow_succ_of_ord_eq hF) N

/-- Volume 1, Example 3.3.16 of the handbook: the multiplicity of `S/(F)` is `ord F`. -/
theorem samuelMultiplicity_germ {F : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hd : 1 ≤ d)
    (hF : ord F = d) :
    samuelMultiplicity (hypersurfaceGermIdeal F) (HypersurfaceGerm F) n = d := by
  have := isLocalRing_hypersurfaceGerm hd hF
  rw [hypersurfaceGermIdeal_eq]
  exact samuelMultiplicity_hypersurface_of_notMem (ringKrullDim_affineOriginRing k (n + 1))
    (algebraMap_mem_pow_of_ord_eq hF) (algebraMap_notMem_pow_succ_of_ord_eq hF)

end Germ

section Arith

/-- The identity `2 C(n, 2) + n = n^2`. -/
theorem two_mul_choose_two_add (n : ℕ) : 2 * n.choose 2 + n = n * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ' n 1
    rw [Nat.choose_one_right] at h
    rw [h]
    have : ((2 * (n + n.choose 2) + (n + 1) : ℕ) : ℚ) = (((n + 1) * (n + 1) : ℕ) : ℚ) := by
      have ih' : ((2 * n.choose 2 + n : ℕ) : ℚ) = ((n * n : ℕ) : ℚ) := by rw [ih]
      push_cast at ih' ⊢
      linear_combination ih'
    exact_mod_cast this

/-- The identity `C(a + b, 2) = C(a, 2) + a b + C(b, 2)`. -/
theorem choose_two_add (a b : ℕ) : (a + b).choose 2 = a.choose 2 + a * b + b.choose 2 := by
  induction b with
  | zero => simp
  | succ b ih =>
    have h1 : (a + b + 1).choose 2 = (a + b).choose 1 + (a + b).choose 2 :=
      Nat.choose_succ_succ' (a + b) 1
    have h2 : (b + 1).choose 2 = b.choose 1 + b.choose 2 := Nat.choose_succ_succ' b 1
    rw [Nat.choose_one_right] at h1 h2
    rw [← add_assoc, h1, ih, h2]
    ring

/-- The arithmetic of the plane curve formula. -/
theorem planeCurve_arith (d M : ℕ) :
    (M + d + 1).choose 2 - (M + 1).choose 2 = d * (M + d) - d.choose 2 := by
  rw [show M + d + 1 = M + 1 + d by omega, choose_two_add, add_assoc, Nat.add_sub_cancel_left]
  refine Nat.eq_sub_of_add_eq ?_
  have h := two_mul_choose_two_add d
  have : (((M + 1) * d + d.choose 2 + d.choose 2 : ℕ) : ℚ) = ((d * (M + d) : ℕ) : ℚ) := by
    have h' : ((2 * d.choose 2 + d : ℕ) : ℚ) = ((d * d : ℕ) : ℚ) := by rw [h]
    push_cast at h' ⊢
    linear_combination h'
  exact_mod_cast this

/-- The arithmetic of a surface of order `2`. -/
theorem surface_two_arith (M : ℕ) : (M + 2 + 2).choose 3 - (M + 2).choose 3 = (M + 2) ^ 2 := by
  have h1 : (M + 2 + 2).choose 3 = (M + 3).choose 2 + (M + 3).choose 3 :=
    Nat.choose_succ_succ' (M + 3) 2
  have h2 : (M + 3).choose 3 = (M + 2).choose 2 + (M + 2).choose 3 :=
    Nat.choose_succ_succ' (M + 2) 2
  rw [h1, h2, ← add_assoc, Nat.add_sub_cancel]
  have h3 := two_mul_choose_two_add (M + 3)
  have h4 := two_mul_choose_two_add (M + 2)
  have : (((M + 3).choose 2 + (M + 2).choose 2 : ℕ) : ℚ) = (((M + 2) ^ 2 : ℕ) : ℚ) := by
    have h3' : ((2 * (M + 3).choose 2 + (M + 3) : ℕ) : ℚ) =
        (((M + 3) * (M + 3) : ℕ) : ℚ) := by
      rw [h3]
    have h4' : ((2 * (M + 2).choose 2 + (M + 2) : ℕ) : ℚ) =
        (((M + 2) * (M + 2) : ℕ) : ℚ) := by
      rw [h4]
    push_cast at h3' h4' ⊢
    linear_combination h3' / 2 + h4' / 2
  exact_mod_cast this

/-- The arithmetic of a surface of order `3`. -/
theorem surface_three_arith (M : ℕ) :
    (M + 3 + 2).choose 3 - (M + 2).choose 3 = 3 * (M + 3).choose 2 + 1 := by
  have h1 : (M + 3 + 2).choose 3 = (M + 4).choose 2 + (M + 4).choose 3 :=
    Nat.choose_succ_succ' (M + 4) 2
  have h2 : (M + 4).choose 3 = (M + 3).choose 2 + (M + 3).choose 3 :=
    Nat.choose_succ_succ' (M + 3) 2
  have h3 : (M + 3).choose 3 = (M + 2).choose 2 + (M + 2).choose 3 :=
    Nat.choose_succ_succ' (M + 2) 2
  have h4 : (M + 4).choose 2 = (M + 3).choose 1 + (M + 3).choose 2 :=
    Nat.choose_succ_succ' (M + 3) 1
  have h5 : (M + 3).choose 2 = (M + 2).choose 1 + (M + 2).choose 2 :=
    Nat.choose_succ_succ' (M + 2) 1
  rw [Nat.choose_one_right] at h4 h5
  omega

end Arith

section PlaneCurve

variable {k : Type*} [Field k]

/-- Volume 1, Example 3.3.16 of the handbook: a plane curve of order `d` has
`χ(N) = d N - C(d, 2)` for `N ≥ d - 1`. -/
theorem hilbertSamuel_planeCurve {F : MvPolynomial (Fin 2) k} {d : ℕ} (hd : 1 ≤ d)
    (hF : ord F = d) {N : ℕ} (hN : d ≤ N + 1) :
    hilbertSamuel (hypersurfaceGermIdeal F) (HypersurfaceGerm F) N =
      ((d * N - d.choose 2 : ℕ) : ℕ∞) := by
  rcases Nat.lt_or_ge N d with h | h
  · have hNd : N + 1 = d := by omega
    rw [hilbertSamuel_germ_of_le (n := 1) hd hF h.le]
    subst hNd
    refine congrArg (Nat.cast : ℕ → ℕ∞) (Nat.sub_eq_of_eq_add ?_).symm
    have h2 := two_mul_choose_two_add (N + 1)
    have : (((N + 1) * N : ℕ) : ℚ) = (((N + 1).choose 2 + (N + 1).choose 2 : ℕ) : ℚ) := by
      have h' : ((2 * (N + 1).choose 2 + (N + 1) : ℕ) : ℚ) =
          (((N + 1) * (N + 1) : ℕ) : ℚ) := by
        rw [h2]
      push_cast at h' ⊢
      linear_combination -h'
    exact_mod_cast this
  · obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le' h
    rw [hilbertSamuel_germ_add (n := 1) hd hF M]
    exact congrArg (Nat.cast : ℕ → ℕ∞) (planeCurve_arith d M)

/-- Volume 1, Example 3.3.16 of the handbook: a plane curve of order `d` has multiplicity `d`. -/
theorem samuelMultiplicity_planeCurve {F : MvPolynomial (Fin 2) k} {d : ℕ} (hd : 1 ≤ d)
    (hF : ord F = d) : samuelMultiplicity (hypersurfaceGermIdeal F) (HypersurfaceGerm F) 1 = d :=
  samuelMultiplicity_germ (n := 1) hd hF

/-- A homogeneous nonzero polynomial of degree `d` has order `d`. -/
theorem ord_eq_of_isHomogeneous {σ R : Type*} [CommSemiring R] {F : MvPolynomial σ R} {d : ℕ}
    (h : F.IsHomogeneous d) (hF : F ≠ 0) : ord F = d := by
  obtain ⟨s, hs, he⟩ := exists_coeff_ne_zero_and_ord_eq hF
  rw [he]
  congr 1
  rw [Finsupp.degree_eq_weight_one]
  exact h hs

theorem ord_cusp : ord (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k) = 2 := by
  rw [sub_eq_add_neg, ord_add_of_lt] <;> norm_num [ord_X_pow]

theorem ord_node : ord (X 1 ^ 2 - X 0 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k) = 2 := by
  have hh : (X 1 ^ 2 - X 0 ^ 2 : MvPolynomial (Fin 2) k).IsHomogeneous 2 :=
    (isHomogeneous_X_pow (R := k) _ _).sub (isHomogeneous_X_pow (R := k) _ _)
  have hne : (X 1 ^ 2 - X 0 ^ 2 : MvPolynomial (Fin 2) k) ≠ 0 := by
    intro h
    have := congrArg (eval ![1, 0]) h
    simp at this
  have h2 := ord_eq_of_isHomogeneous hh hne
  rw [sub_eq_add_neg, ord_add_of_lt] <;> norm_num [h2, ord_X_pow]

theorem ord_x3_add_y5 : ord (X 0 ^ 3 + X 1 ^ 5 : MvPolynomial (Fin 2) k) = 3 := by
  rw [ord_add_of_lt] <;> norm_num [ord_X_pow]

theorem ord_x2y_add_y4 : ord (X 0 ^ 2 * X 1 + X 1 ^ 4 : MvPolynomial (Fin 2) k) = 3 := by
  rw [ord_add_of_lt] <;> norm_num [ord_X_pow, ord_mul, ord_X]

theorem ord_xa_add_yb {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ord (X 0 ^ a + X 1 ^ b : MvPolynomial (Fin 2) k) = a := by
  rcases hab.lt_or_eq with h | rfl
  · rw [ord_add_of_lt, ord_X_pow]
    rw [ord_X_pow, ord_X_pow]
    exact_mod_cast h
  · refine ord_eq_of_isHomogeneous
      ((isHomogeneous_X_pow (R := k) _ _).add (isHomogeneous_X_pow (R := k) _ _)) ?_
    intro h
    have := congrArg (eval ![1, 0]) h
    simp [zero_pow (by omega : a ≠ 0)] at this

/-- Volume 1, Example 3.3.16 of the handbook: the cusp `y^2 - x^3` has `χ(N) = 2N - 1` for
`N ≥ 1`, and multiplicity `2`. -/
theorem hilbertSamuel_cusp {N : ℕ} (hN : 1 ≤ N) :
    hilbertSamuel (hypersurfaceGermIdeal (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k))
        (HypersurfaceGerm (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k)) N =
        ((2 * N - 1 : ℕ) : ℕ∞) ∧
    samuelMultiplicity (hypersurfaceGermIdeal (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k))
        (HypersurfaceGerm (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k)) 1 = 2 :=
  ⟨(hilbertSamuel_planeCurve (d := 2) (by norm_num) (by simp [ord_cusp]) (by omega)).trans
      (by norm_num [Nat.choose_two_right]),
    samuelMultiplicity_planeCurve (d := 2) (by norm_num) (by simp [ord_cusp])⟩

/-- Volume 1, Example 3.3.16 of the handbook: the node `y^2 - x^2 - x^3` has `χ(N) = 2N - 1`
for `N ≥ 1`, and multiplicity `2`. -/
theorem hilbertSamuel_node {N : ℕ} (hN : 1 ≤ N) :
    hilbertSamuel (hypersurfaceGermIdeal (X 1 ^ 2 - X 0 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k))
        (HypersurfaceGerm (X 1 ^ 2 - X 0 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k)) N =
        ((2 * N - 1 : ℕ) : ℕ∞) ∧
    samuelMultiplicity
        (hypersurfaceGermIdeal (X 1 ^ 2 - X 0 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k))
        (HypersurfaceGerm (X 1 ^ 2 - X 0 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k)) 1 = 2 :=
  ⟨(hilbertSamuel_planeCurve (d := 2) (by norm_num) (by simp [ord_node]) (by omega)).trans
      (by norm_num [Nat.choose_two_right]),
    samuelMultiplicity_planeCurve (d := 2) (by norm_num) (by simp [ord_node])⟩

/-- Volume 1, Example 3.3.16 of the handbook: `x^3 + y^5` has `χ(N) = 3N - 3` for `N ≥ 2`, and
multiplicity `3`. -/
theorem hilbertSamuel_x3_add_y5 {N : ℕ} (hN : 2 ≤ N) :
    hilbertSamuel (hypersurfaceGermIdeal (X 0 ^ 3 + X 1 ^ 5 : MvPolynomial (Fin 2) k))
        (HypersurfaceGerm (X 0 ^ 3 + X 1 ^ 5 : MvPolynomial (Fin 2) k)) N =
        ((3 * N - 3 : ℕ) : ℕ∞) ∧
    samuelMultiplicity (hypersurfaceGermIdeal (X 0 ^ 3 + X 1 ^ 5 : MvPolynomial (Fin 2) k))
        (HypersurfaceGerm (X 0 ^ 3 + X 1 ^ 5 : MvPolynomial (Fin 2) k)) 1 = 3 :=
  ⟨(hilbertSamuel_planeCurve (d := 3) (by norm_num) (by simp [ord_x3_add_y5]) (by omega)).trans
      (by norm_num [Nat.choose_two_right]),
    samuelMultiplicity_planeCurve (d := 3) (by norm_num) (by simp [ord_x3_add_y5])⟩

/-- Volume 1, Example 3.3.16 of the handbook: `x^2 y + y^4` has `χ(N) = 3N - 3` for `N ≥ 2`, and
multiplicity `3`. -/
theorem hilbertSamuel_x2y_add_y4 {N : ℕ} (hN : 2 ≤ N) :
    hilbertSamuel (hypersurfaceGermIdeal (X 0 ^ 2 * X 1 + X 1 ^ 4 : MvPolynomial (Fin 2) k))
        (HypersurfaceGerm (X 0 ^ 2 * X 1 + X 1 ^ 4 : MvPolynomial (Fin 2) k)) N =
        ((3 * N - 3 : ℕ) : ℕ∞) ∧
    samuelMultiplicity (hypersurfaceGermIdeal (X 0 ^ 2 * X 1 + X 1 ^ 4 : MvPolynomial (Fin 2) k))
        (HypersurfaceGerm (X 0 ^ 2 * X 1 + X 1 ^ 4 : MvPolynomial (Fin 2) k)) 1 = 3 :=
  ⟨(hilbertSamuel_planeCurve (d := 3) (by norm_num) (by simp [ord_x2y_add_y4]) (by omega)).trans
      (by norm_num [Nat.choose_two_right]),
    samuelMultiplicity_planeCurve (d := 3) (by norm_num) (by simp [ord_x2y_add_y4])⟩

/-- Volume 1, Example 3.3.16 of the handbook: `x^a + y^b` with `1 ≤ a ≤ b` has multiplicity
`a`. -/
theorem samuelMultiplicity_xa_add_yb {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    samuelMultiplicity (hypersurfaceGermIdeal (X 0 ^ a + X 1 ^ b : MvPolynomial (Fin 2) k))
        (HypersurfaceGerm (X 0 ^ a + X 1 ^ b : MvPolynomial (Fin 2) k)) 1 = a :=
  samuelMultiplicity_planeCurve ha (ord_xa_add_yb ha hab)

end PlaneCurve

section Surface

variable {k : Type*} [Field k]

/-- Volume 1, Example 3.3.16 of the handbook: a surface of order `2` has `χ(N) = N^2` for each
`N`, and multiplicity `2`. -/
theorem hilbertSamuel_surface_two {F : MvPolynomial (Fin 3) k} (hF : ord F = 2) (N : ℕ) :
    hilbertSamuel (hypersurfaceGermIdeal F) (HypersurfaceGerm F) N = ((N ^ 2 : ℕ) : ℕ∞) ∧
    samuelMultiplicity (hypersurfaceGermIdeal F) (HypersurfaceGerm F) 2 = 2 := by
  have hF' : ord F = ((2 : ℕ) : ℕ∞) := by simp [hF]
  refine ⟨?_, samuelMultiplicity_germ (n := 2) (by norm_num) hF'⟩
  rcases Nat.lt_or_ge N 3 with h | h
  · rw [hilbertSamuel_germ_of_le (n := 2) (by norm_num) hF' (by omega : N ≤ 2)]
    interval_cases N <;> exact congrArg (Nat.cast : ℕ → ℕ∞) (by decide)
  · obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 2 ≤ N)
    rw [hilbertSamuel_germ_add (n := 2) (by norm_num) hF' M]
    exact congrArg (Nat.cast : ℕ → ℕ∞) (surface_two_arith M)

theorem ord_xy_sub_z2 : ord (X 0 * X 1 - X 2 ^ 2 : MvPolynomial (Fin 3) k) = 2 := by
  have hh : (X 0 * X 1 - X 2 ^ 2 : MvPolynomial (Fin 3) k).IsHomogeneous 2 :=
    ((isHomogeneous_X (R := k) _).mul (isHomogeneous_X (R := k) _)).sub
      (isHomogeneous_X_pow (R := k) _ _)
  have hne : (X 0 * X 1 - X 2 ^ 2 : MvPolynomial (Fin 3) k) ≠ 0 := by
    intro h
    have := congrArg (eval ![1, 1, 0]) h
    simp at this
  simp [ord_eq_of_isHomogeneous hh hne]

theorem ord_am {m : ℕ} (hm : 1 ≤ m) :
    ord (X 0 * X 1 - X 2 ^ (m + 1) : MvPolynomial (Fin 3) k) = 2 := by
  have h : ord (X 0 * X 1 : MvPolynomial (Fin 3) k) = 2 := by
    rw [ord_mul, ord_X, ord_X]
    rfl
  rcases hm.lt_or_eq with hm' | rfl
  · rw [sub_eq_add_neg, ord_add_of_lt, h]
    rw [h, ord_neg, ord_X_pow]
    have h3 : (2 : ℕ) < m + 1 := by omega
    exact_mod_cast h3
  · have hh : (X 0 * X 1 - X 2 ^ (1 + 1) : MvPolynomial (Fin 3) k).IsHomogeneous 2 :=
      ((isHomogeneous_X (R := k) 0).mul (isHomogeneous_X (R := k) 1)).sub
        (isHomogeneous_X_pow (R := k) _ _)
    refine ord_eq_of_isHomogeneous hh ?_
    intro h0
    have := congrArg (eval ![1, 1, 0]) h0
    simp at this

theorem ord_umbrella : ord (X 0 ^ 2 - X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) = 2 := by
  rw [sub_eq_add_neg, ord_add_of_lt] <;> norm_num [ord_X_pow, ord_mul, ord_X]

/-- Volume 1, Example 3.3.16 of the handbook: a surface of order `3` has
`χ(N) = 3 C(N, 2) + 1` for `N ≥ 1`, and multiplicity `3`. -/
theorem hilbertSamuel_surface_three {F : MvPolynomial (Fin 3) k} (hF : ord F = 3) {N : ℕ}
    (hN : 1 ≤ N) :
    hilbertSamuel (hypersurfaceGermIdeal F) (HypersurfaceGerm F) N =
        ((3 * N.choose 2 + 1 : ℕ) : ℕ∞) ∧
    samuelMultiplicity (hypersurfaceGermIdeal F) (HypersurfaceGerm F) 2 = 3 := by
  have hF' : ord F = ((3 : ℕ) : ℕ∞) := by simp [hF]
  refine ⟨?_, samuelMultiplicity_germ (n := 2) (by norm_num) hF'⟩
  rcases Nat.lt_or_ge N 4 with h | h
  · rw [hilbertSamuel_germ_of_le (n := 2) (by norm_num) hF' (by omega : N ≤ 3)]
    interval_cases N <;> exact congrArg (Nat.cast : ℕ → ℕ∞) (by decide)
  · obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 3 ≤ N)
    rw [hilbertSamuel_germ_add (n := 2) (by norm_num) hF' M]
    exact congrArg (Nat.cast : ℕ → ℕ∞) (surface_three_arith M)

/-- Volume 1, Example 3.3.16 of the handbook: for a surface of order `3`, the second difference
`χ(N + 2) - 2 χ(N + 1) + χ(N)` is `3` for `N ≥ 1`. -/
theorem hilbertSamuel_surface_three_fwdDiff {F : MvPolynomial (Fin 3) k} (hF : ord F = 3)
    {N : ℕ} (hN : 1 ≤ N) :
    hilbertSamuel (hypersurfaceGermIdeal F) (HypersurfaceGerm F) (N + 2) +
        hilbertSamuel (hypersurfaceGermIdeal F) (HypersurfaceGerm F) N =
      2 * hilbertSamuel (hypersurfaceGermIdeal F) (HypersurfaceGerm F) (N + 1) + 3 := by
  rw [(hilbertSamuel_surface_three hF (by omega : 1 ≤ N + 2)).1,
    (hilbertSamuel_surface_three hF hN).1,
    (hilbertSamuel_surface_three hF (by omega : 1 ≤ N + 1)).1]
  have h1 : (N + 2).choose 2 = (N + 1).choose 1 + (N + 1).choose 2 :=
    Nat.choose_succ_succ' (N + 1) 1
  have h2 : (N + 1).choose 2 = N.choose 1 + N.choose 2 := Nat.choose_succ_succ' N 1
  rw [Nat.choose_one_right] at h1 h2
  norm_cast
  omega

theorem ord_cubicCone : ord (X 0 ^ 3 + X 1 ^ 3 + X 2 ^ 3 : MvPolynomial (Fin 3) k) = 3 := by
  have hh : (X 0 ^ 3 + X 1 ^ 3 + X 2 ^ 3 : MvPolynomial (Fin 3) k).IsHomogeneous 3 :=
    ((isHomogeneous_X_pow (R := k) _ _).add (isHomogeneous_X_pow (R := k) _ _)).add
      (isHomogeneous_X_pow (R := k) _ _)
  have hne : (X 0 ^ 3 + X 1 ^ 3 + X 2 ^ 3 : MvPolynomial (Fin 3) k) ≠ 0 := by
    intro h
    have := congrArg (eval ![1, 0, 0]) h
    simp at this
  simp [ord_eq_of_isHomogeneous hh hne]

/-- Volume 1, Example 3.3.16 of the handbook: the cubic cone `x^3 + y^3 + z^3` has Hilbert-Samuel
values `1, 4, 10, 19, 31, 46` at `N = 1, ..., 6`. -/
theorem hilbertSamuel_cubicCone_values :
    let F : MvPolynomial (Fin 3) k := X 0 ^ 3 + X 1 ^ 3 + X 2 ^ 3
    hilbertSamuel (hypersurfaceGermIdeal F) (HypersurfaceGerm F) 1 = 1 ∧
    hilbertSamuel (hypersurfaceGermIdeal F) (HypersurfaceGerm F) 2 = 4 ∧
    hilbertSamuel (hypersurfaceGermIdeal F) (HypersurfaceGerm F) 3 = 10 ∧
    hilbertSamuel (hypersurfaceGermIdeal F) (HypersurfaceGerm F) 4 = 19 ∧
    hilbertSamuel (hypersurfaceGermIdeal F) (HypersurfaceGerm F) 5 = 31 ∧
    hilbertSamuel (hypersurfaceGermIdeal F) (HypersurfaceGerm F) 6 = 46 := by
  intro F
  have h := fun N (hN : 1 ≤ N) => (hilbertSamuel_surface_three (k := k) ord_cubicCone hN).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [h _ (by norm_num)] <;>
    norm_num [Nat.choose_two_right]

end Surface

/-! ### Proposition 6.2.5 for `k(t)` -/

section PBasisRatFunc

variable (F : Type*) [Field F] (p : ℕ) [hp : Fact p.Prime] [CharP F p] [PerfectRing F p]

/-- For `F` perfect, the subring `F K^p` of `K = F(t)` consists of `p`-th powers. -/
theorem exists_pow_eq_of_mem_pSubring {x : RatFunc F} (hx : x ∈ pSubring (K := RatFunc F) F p) :
    ∃ y : RatFunc F, y ^ p = x := by
  have hle : pSubring (K := RatFunc F) F p ≤ (frobenius (RatFunc F) p).range := by
    refine Subring.closure_le.mpr ?_
    rintro _ (⟨c, rfl⟩ | ⟨a, rfl⟩)
    · obtain ⟨c', hc'⟩ := surjective_frobenius F p c
      refine RingHom.mem_range.mpr ⟨algebraMap F (RatFunc F) c', ?_⟩
      rw [frobenius_def, ← map_pow, ← hc', frobenius_def]
    · exact RingHom.mem_range.mpr ⟨a, rfl⟩
  obtain ⟨y, hy⟩ := RingHom.mem_range.mp (hle hx)
  exact ⟨y, hy⟩

omit [CharP F p] [PerfectRing F p] in
/-- Each element of `F(t)` lies in the field that `F K^p` and `t` generate. -/
theorem adjoin_pSubring_X_eq_top :
    IntermediateField.adjoin (pSubring (K := RatFunc F) F p) {(RatFunc.X : RatFunc F)} = ⊤ := by
  set E := IntermediateField.adjoin (pSubring (K := RatFunc F) F p) {(RatFunc.X : RatFunc F)}
  have hC : ∀ c : F, algebraMap F (RatFunc F) c ∈ E := fun c =>
    E.algebraMap_mem ⟨algebraMap F (RatFunc F) c, Subring.subset_closure (Or.inl ⟨c, rfl⟩)⟩
  have hXE : (RatFunc.X : RatFunc F) ∈ E :=
    IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
  have hpol : ∀ q : Polynomial F, algebraMap (Polynomial F) (RatFunc F) q ∈ E := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      rw [RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C]
      exact hC a
    | add q r hq hr =>
      rw [map_add]
      exact E.add_mem hq hr
    | monomial n a h =>
      rw [pow_succ, ← mul_assoc, map_mul, RatFunc.algebraMap_X]
      exact E.mul_mem h hXE
  refine eq_top_iff.mpr fun f _ => ?_
  rw [← RatFunc.num_div_denom f]
  exact E.div_mem (hpol _) (hpol _)

/-- Volume 1, Proposition 6.2.5 of the handbook for `K = F(t)` and `F` perfect: `{t}` is a
`p`-basis of `F(t)` over `F`. -/
theorem isPBasis_ratFunc_X : IsPBasis F p ({RatFunc.X} : Finset (RatFunc F)) := by
  classical
  refine ⟨?_, fun x _ => ?_⟩
  · change IsPIndependent F p _
    rw [isPIndependent_iff]
    intro b hb
    rw [Finset.mem_singleton] at hb
    subst hb
    rw [Finset.erase_singleton, Finset.coe_empty, IntermediateField.adjoin_empty,
      IntermediateField.mem_bot]
    rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := exists_pow_eq_of_mem_pSubring F p y.2
    exact Singularity.Example.X_ne_pow hp.out.two_le z (hz.trans hy)
  · rw [span_pMonomial_eq, ← adjoin_toSubalgebra_pSubring, Finset.coe_singleton,
      adjoin_pSubring_X_eq_top F p]
    simp

/-- Volume 1, Proposition 6.2.5 of the handbook for `K = F(t)` and `F` perfect:
`[F(t) : F(t)^p] = p`. -/
theorem finrank_pSubring_ratFunc :
    Module.finrank (pSubring (K := RatFunc F) F p) (RatFunc F) = p := by
  rw [finrank_pSubring_eq (isPBasis_ratFunc_X F p), Finset.card_singleton, pow_one]

/-- The derivation `∂/∂t` of `F(t)`, for `F` perfect, from the `p`-basis `{t}`. -/
noncomputable def ratFuncDerivX : Derivation F (RatFunc F) (RatFunc F) :=
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  pBasisDerivation (isPBasis_ratFunc_X F p) fun _ => 1

theorem ratFuncDerivX_X : ratFuncDerivX F p RatFunc.X = 1 := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  exact pBasisDerivation_apply (isPBasis_ratFunc_X F p) (fun _ => 1)
    ⟨RatFunc.X, Finset.mem_singleton_self _⟩

end PBasisRatFunc

/-! ### Example 1.8.19 -/

section CoeffDerivation

variable {σ K : Type*} [CommRing K] (δ : Derivation ℤ K K)

/-- Apply `δ` to each coefficient of a polynomial. -/
noncomputable def coeffDerivationAux : MvPolynomial σ K →+ MvPolynomial σ K :=
  AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom δ.toLinearMap.toAddMonoidHom).comp
      AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)

theorem coeff_coeffDerivationAux (f : MvPolynomial σ K) (n : σ →₀ ℕ) :
    (coeffDerivationAux δ f).coeff n = δ (f.coeff n) :=
  rfl

theorem coeffDerivationAux_monomial (s : σ →₀ ℕ) (c : K) :
    coeffDerivationAux δ (monomial s c) = monomial s (δ c) := by
  classical
  refine MvPolynomial.ext _ _ fun n => ?_
  rw [coeff_coeffDerivationAux, coeff_monomial, coeff_monomial]
  split_ifs <;> simp

theorem coeffDerivationAux_mul (a b : MvPolynomial σ K) :
    coeffDerivationAux δ (a * b) =
      a • coeffDerivationAux δ b + b • coeffDerivationAux δ a := by
  induction a using MvPolynomial.induction_on' with
  | monomial s c =>
    induction b using MvPolynomial.induction_on' with
    | monomial t e =>
      rw [monomial_mul_monomial, coeffDerivationAux_monomial, coeffDerivationAux_monomial,
        coeffDerivationAux_monomial, smul_eq_mul, smul_eq_mul, monomial_mul_monomial,
        monomial_mul_monomial, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, add_comm t s]
    | add b₁ b₂ h₁ h₂ =>
      rw [mul_add, map_add, h₁, h₂, map_add, smul_add, add_smul]
      abel
  | add a₁ a₂ h₁ h₂ =>
    rw [add_mul, map_add, h₁, h₂, map_add, smul_add, add_smul]
    abel

/-- The derivation of `K[x_i]` that applies `δ` to each coefficient. -/
noncomputable def coeffDerivation :
    Derivation ℤ (MvPolynomial σ K) (MvPolynomial σ K) :=
  Derivation.mk' (coeffDerivationAux δ).toIntLinearMap (coeffDerivationAux_mul δ)

theorem coeffDerivation_monomial (s : σ →₀ ℕ) (c : K) :
    coeffDerivation δ (monomial s c) = monomial s (δ c) :=
  coeffDerivationAux_monomial δ s c

theorem coeffDerivation_C (c : K) : coeffDerivation δ (C c : MvPolynomial σ K) = C (δ c) := by
  rw [← monomial_zero', coeffDerivation_monomial, monomial_zero']

theorem coeffDerivation_X (i : σ) : coeffDerivation δ (X i : MvPolynomial σ K) = 0 := by
  rw [X, coeffDerivation_monomial, δ.map_one_eq_zero, _root_.map_zero]

end CoeffDerivation

section Example1819

/-- If `A` is regular and a derivation `D` of `A` has `D F = 1`, then `A/(F)` is regular. -/
theorem isRegularRing_quotient_of_derivation_eq_one {k A : Type*} [CommRing k] [CommRing A]
    [Algebra k A] [IsRegularRing A] (D : Derivation k A A) {F : A} (hF : D F = 1) :
    IsRegularRing (A ⧸ span {F}) := by
  rw [isRegularRing_iff]
  intro q hq
  have h := regularLocus_quotient_of_derivation D F
  rw [hF, map_one, PrimeSpectrum.basicOpen_one] at h
  exact h (show (⟨q, hq⟩ : PrimeSpectrum (A ⧸ span {F})) ∈
    ((⊤ : TopologicalSpace.Opens (PrimeSpectrum (A ⧸ span {F}))) : Set _) by simp)

variable {K : Type*} [Field K]

/-- Volume 1, Example 1.8.19 of the handbook: if `δ t = 1` for a derivation `δ` of `K` over
some ring `R`, then `K[x, y]/(y^2 - x^p + t)` is a regular ring. -/
theorem isRegularRing_example_1_8_19 {R : Type*} [CommRing R] [Algebra R K]
    (δ : Derivation R K K) {t : K} (ht : δ t = 1) (p : ℕ) :
    IsRegularRing (MvPolynomial (Fin 2) K ⧸ span {X 1 ^ 2 - X 0 ^ p + C t}) := by
  have ht' : δ.restrictScalars ℤ t = 1 := ht
  refine isRegularRing_quotient_of_derivation_eq_one (coeffDerivation (δ.restrictScalars ℤ)) ?_
  rw [map_add, map_sub, Derivation.leibniz_pow, Derivation.leibniz_pow, coeffDerivation_X,
    coeffDerivation_X, coeffDerivation_C, ht']
  simp only [smul_zero, sub_self, zero_add, map_one]

/-- Volume 1, Example 1.8.19 of the handbook, for `K = F(t)` with `F` perfect of characteristic
`p`: the ring `K[x, y]/(y^2 - x^p + t)` is regular. -/
theorem isRegularRing_example_1_8_19_ratFunc (F : Type*) [Field F] (p : ℕ) [Fact p.Prime]
    [CharP F p] [PerfectRing F p] :
    IsRegularRing
      (MvPolynomial (Fin 2) (RatFunc F) ⧸
        span {(X 1 ^ 2 - X 0 ^ p + C (RatFunc.X : RatFunc F) :
          MvPolynomial (Fin 2) (RatFunc F))}) :=
  isRegularRing_example_1_8_19 (ratFuncDerivX F p) (ratFuncDerivX_X F p) p

variable (p : ℕ) [CharP K p]

/-- Volume 1, Example 1.8.19 of the handbook: in characteristic `p`, each `K`-linear derivation
`D` of `K[x, y]` sends `f = y^2 - x^p + t` to `2 y D(y)`. -/
theorem derivation_example_1_8_19
    (D : Derivation K (MvPolynomial (Fin 2) K) (MvPolynomial (Fin 2) K)) (t : K) :
    D (X 1 ^ 2 - X 0 ^ p + C t) = 2 * X 1 * D (X 1) := by
  have hC : D (C t) = 0 := by
    rw [← MvPolynomial.algebraMap_eq]
    exact D.map_algebraMap t
  have h0 : D (X 0 ^ p) = 0 := by
    rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  rw [map_add, map_sub, hC, h0, sub_zero, add_zero, Derivation.leibniz_pow, smul_eq_mul,
    nsmul_eq_mul, show 2 - 1 = 1 from rfl, pow_one]
  push_cast
  ring

/-- Volume 1, Example 1.8.19 of the handbook: in characteristic `p`, each `K`-linear derivation
`D` of `K[x, y]` sends `f` into `n = (x^p - t, y)`. -/
theorem derivation_example_1_8_19_mem (D : Derivation K (MvPolynomial (Fin 2) K)
    (MvPolynomial (Fin 2) K)) (t : K) :
    D (X 1 ^ 2 - X 0 ^ p + C t) ∈ span {X 0 ^ p - C t, (X 1 : MvPolynomial (Fin 2) K)} := by
  rw [derivation_example_1_8_19 p D t]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

/-- Volume 1, Example 1.8.19 of the handbook: `∂f/∂x = 0` in characteristic `p`. -/
theorem pderiv_zero_example_1_8_19 (t : K) :
    pderiv 0 (X 1 ^ 2 - X 0 ^ p + C t : MvPolynomial (Fin 2) K) = 0 := by
  rw [derivation_example_1_8_19 p (pderiv 0) t, pderiv_X_of_ne (by decide), mul_zero]

/-- Volume 1, Example 1.8.19 of the handbook: each additive derivation kills `a^p`. -/
theorem derivation_pow_char_eq_zero (δ : Derivation ℤ K K) (a : K) : δ (a ^ p) = 0 := by
  rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]

variable [Fact p.Prime]

/-- Volume 1, Example 1.8.19 of the handbook: if `a^p = t`, then `f = y^2 - (x - a)^p`. -/
theorem example_1_8_19_baseChange {a t : K} (ha : a ^ p = t) :
    (X 1 ^ 2 - X 0 ^ p + C t : MvPolynomial (Fin 2) K) = X 1 ^ 2 - (X 0 - C a) ^ p := by
  rw [sub_pow_char, ← map_pow, ha]
  ring

/-- Volume 1, Example 1.8.19 of the handbook: if `a^p = t`, then `f ∈ (x - a, y)^2`. -/
theorem example_1_8_19_baseChange_mem {a t : K} (ha : a ^ p = t) :
    (X 1 ^ 2 - X 0 ^ p + C t : MvPolynomial (Fin 2) K) ∈
      span {X 0 - C a, (X 1 : MvPolynomial (Fin 2) K)} ^ 2 := by
  rw [example_1_8_19_baseChange p ha]
  refine Ideal.sub_mem _ (Ideal.pow_mem_pow (Ideal.subset_span (by simp)) 2) ?_
  exact Ideal.pow_le_pow_right (Fact.out : p.Prime).two_le
    (Ideal.pow_mem_pow (Ideal.subset_span (by simp)) p)

end Example1819

end Algebra

end Singularity
