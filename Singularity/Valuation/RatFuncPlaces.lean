/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Algebra.Order.Archimedean.Defs
import Singularity.Valuation.Center
import Singularity.Valuation.DefectlessDistance
import Singularity.Valuation.LexConvexSubgroup

/-!
# Places of the rational function field, and small results on Abhyankar and defect

This file proves parts of Volume 3 of the handbook.

* `Singularity.valuationSubring_ratFunc_trichotomy`: Example 1.5.6. Each valuation ring `V`
  of `k(x)` with `k ⊆ V` is `k(x)`, or the ring of a `P`-adic valuation for a nonzero prime `P`
  of `k[x]`, or the ring of the valuation at infinity.
* `Singularity.toLocalSubring_eq_ofPrime_centerIdeal`: the ring of the `P`-adic valuation is
  the local ring `k[x]_P` (Examples 1.4.5 and 1.5.6).
* `Singularity.centerIdeal_idealX_and_ofPrime_eq`: Example 1.4.5, the algebraic part. On the
  chart `k[t]`, the center of `ord_t` is `(t)`, and the local ring at `(t)` is the valuation ring.
* `Singularity.IsConvexSubgroup.eq_top_of_one_lt_mem` and
  `Singularity.isLeast_delta_one_lexValueX`: Example 2.4.5, the two computations of the
  smallest convex subgroup that contains `μ`.
* `Singularity.trdeg_sub_eq_dim_sub` and `Singularity.add_trdeg_eq_dim_iff`: Corollary 2.3.4,
  from the dimension formula `dim R + trdeg(κ/k) = trdeg(K/k)` as a hypothesis.
* `Singularity.div_eq_pow_of_eq_pow_mul` and `Singularity.mul_eq_of_eq_pow_mul`:
  Corollary 3.2.2, from the conclusion `n = p^ν e f` of the theorem of Ostrowski as a hypothesis.
* `Singularity.exists_forall_valuation_sub_le_of_eq_pow_mul`: Corollary 4.2.3, from the
  conclusion of the theorem of Ostrowski and Proposition 3.2.3
  (`Singularity.exists_forall_valuation_sub_le`).

The proof of Example 1.5.6 follows the handbook in the case `x ∈ V`. The prime `P` is
`m_V ∩ k[x]`. Since the numerator and the denominator of an element are coprime, an element is
in `V` if and only if its denominator is not in `P`. In the case `x ∉ V` the proof is direct.
Each nonzero polynomial `f` has `v(f) = v(x)^(deg f)`, for `V` and for the valuation at infinity.
So both rings contain `f/g` if and only if `deg f ≤ deg g`.

The following is not proved here.

* Theorem 2.3.3 (the local Abhyankar inequality). It needs Hilbert-Samuel functions.
* Theorem 3.1.4 (the theorem of Ostrowski). Corollaries 3.2.2 and 4.2.3 take its conclusion as
  a hypothesis.
* The scheme-theoretic part of Example 1.4.5: the line with the origin doubled, its two distinct
  origins, and the fact that it is not separated.
* In Example 1.5.6, the bijection and the homeomorphism with the points of `P^1`.
* In Example 2.4.5, the claims on lengths, on the ideal `q`, and on the residue fields.
* In Corollary 2.3.4, the dimension formula for varieties. It is a hypothesis.
* In Corollary 4.2.3, the choice of the families `x_i` and `y_j` from `e` and `f`, as in
  Proposition 3.2.3.
-/

open Polynomial

namespace Singularity

section RatFuncPlaces

variable {k : Type*} [Field k]

/-- The image of a polynomial in `k(x)` is the polynomial evaluated at `x`. -/
theorem ratFunc_algebraMap_eq_aeval_X (f : k[X]) :
    algebraMap k[X] (RatFunc k) f = aeval (RatFunc.X : RatFunc k) f := by
  rw [← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply, aeval_X_left_apply]

/-- Let `v` be a valuation of `k(x)` with `v(f) ≤ 1` for each polynomial `f`. Then
`v(x) ≤ 1` if and only if the denominator of `x` has value `1`. The proof uses that the
numerator and the denominator are coprime. -/
theorem valuation_le_one_iff_not_denom_lt_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (RatFunc k) Γ) (hv : ∀ f : k[X], v (algebraMap k[X] (RatFunc k) f) ≤ 1)
    (x : RatFunc k) :
    v x ≤ 1 ↔ ¬ v (algebraMap k[X] (RatFunc k) x.denom) < 1 := by
  have hd : algebraMap k[X] (RatFunc k) x.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr x.denom_ne_zero
  have hd0 : v (algebraMap k[X] (RatFunc k) x.denom) ≠ 0 := (Valuation.ne_zero_iff v).mpr hd
  have hx : v x = v (algebraMap k[X] (RatFunc k) x.num) /
      v (algebraMap k[X] (RatFunc k) x.denom) := by
    rw [← map_div₀, RatFunc.num_div_denom]
  constructor
  · intro h hlt
    obtain ⟨a, b, hab⟩ := x.isCoprime_num_denom
    have hn : ¬ v (algebraMap k[X] (RatFunc k) x.num) < 1 := by
      intro hn
      have h1 : v (algebraMap k[X] (RatFunc k) (a * x.num + b * x.denom)) < 1 := by
        rw [map_add]
        refine (v.map_add _ _).trans_lt (max_lt ?_ ?_)
        · rw [map_mul, v.map_mul]
          exact (mul_le_of_le_one_left' (hv a)).trans_lt hn
        · rw [map_mul, v.map_mul]
          exact (mul_le_of_le_one_left' (hv b)).trans_lt hlt
      rw [hab, map_one, v.map_one] at h1
      exact lt_irrefl _ h1
    have hn1 : v (algebraMap k[X] (RatFunc k) x.num) = 1 := le_antisymm (hv _) (not_lt.mp hn)
    rw [hx, hn1] at h
    have : (1 : Γ) ≤ v (algebraMap k[X] (RatFunc k) x.denom) :=
      calc (1 : Γ) = 1 / v (algebraMap k[X] (RatFunc k) x.denom) *
            v (algebraMap k[X] (RatFunc k) x.denom) := (div_mul_cancel₀ 1 hd0).symm
        _ ≤ 1 * v (algebraMap k[X] (RatFunc k) x.denom) := by gcongr
        _ = _ := one_mul _
    exact not_le.mpr hlt this
  · intro h
    have hd1 : v (algebraMap k[X] (RatFunc k) x.denom) = 1 := le_antisymm (hv _) (not_lt.mp h)
    rw [hx, hd1, div_one]
    exact hv _

/-- Two valuations of `k(x)` that are at most `1` on the polynomials, and that have the same
polynomials of value `< 1`, have the same valuation ring. -/
theorem valuationSubring_eq_of_polynomial {Γ₁ Γ₂ : Type*} [LinearOrderedCommGroupWithZero Γ₁]
    [LinearOrderedCommGroupWithZero Γ₂] (v₁ : Valuation (RatFunc k) Γ₁)
    (v₂ : Valuation (RatFunc k) Γ₂)
    (h₁ : ∀ f : k[X], v₁ (algebraMap k[X] (RatFunc k) f) ≤ 1)
    (h₂ : ∀ f : k[X], v₂ (algebraMap k[X] (RatFunc k) f) ≤ 1)
    (h : ∀ f : k[X], v₁ (algebraMap k[X] (RatFunc k) f) < 1 ↔
      v₂ (algebraMap k[X] (RatFunc k) f) < 1) :
    v₁.valuationSubring = v₂.valuationSubring := by
  ext x
  rw [Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff,
    valuation_le_one_iff_not_denom_lt_one v₁ h₁, valuation_le_one_iff_not_denom_lt_one v₂ h₂, h]

/-- A valuation that is `1` on the nonzero constants and `< 1` on `1/x` is at most `1` on
`q(1/x)` for each polynomial `q`. -/
theorem valuation_aeval_inv_X_le_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (RatFunc k) Γ) (hc : ∀ c : k, c ≠ 0 → v (algebraMap k (RatFunc k) c) = 1)
    (hX : v (RatFunc.X⁻¹) < 1) (q : k[X]) :
    v (aeval (RatFunc.X⁻¹ : RatFunc k) q) ≤ 1 := by
  refine Polynomial.induction_on q (fun a => ?_) (fun p r hp hr => ?_) (fun n a h => ?_)
  · rw [aeval_C]
    by_cases ha : a = 0
    · rw [ha, map_zero, v.map_zero]
      exact zero_le_one
    · exact (hc a ha).le
  · rw [map_add]
    exact (v.map_add _ _).trans (max_le hp hr)
  · rw [pow_succ, ← mul_assoc, map_mul, v.map_mul, aeval_X]
    exact (mul_le_of_le_one_right' hX.le).trans h

/-- A valuation that is `1` on the nonzero constants and `< 1` on `1/x` has the value `1` on
`q(1/x)` if the constant term of `q` is not `0`. -/
theorem valuation_aeval_inv_X_eq_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (RatFunc k) Γ) (hc : ∀ c : k, c ≠ 0 → v (algebraMap k (RatFunc k) c) = 1)
    (hX : v (RatFunc.X⁻¹) < 1) (q : k[X]) (hq : q.coeff 0 ≠ 0) :
    v (aeval (RatFunc.X⁻¹ : RatFunc k) q) = 1 := by
  have hq' : aeval (RatFunc.X⁻¹ : RatFunc k) q = algebraMap k (RatFunc k) (q.coeff 0) +
      RatFunc.X⁻¹ * aeval (RatFunc.X⁻¹ : RatFunc k) q.divX := by
    conv_lhs => rw [← X_mul_divX_add q]
    rw [map_add, map_mul, aeval_X, aeval_C, add_comm]
  have hlt : v (RatFunc.X⁻¹ * aeval (RatFunc.X⁻¹ : RatFunc k) q.divX) <
      v (algebraMap k (RatFunc k) (q.coeff 0)) := by
    rw [v.map_mul, hc _ hq]
    exact (mul_le_of_le_one_right' (valuation_aeval_inv_X_le_one v hc hX _)).trans_lt hX
  rw [hq', v.map_add_eq_of_lt_left hlt, hc _ hq]

/-- A valuation that is `1` on the nonzero constants and `< 1` on `1/x` has the value
`v(x)^(deg f)` on each nonzero polynomial `f`. -/
theorem valuation_algebraMap_eq_pow_natDegree {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (RatFunc k) Γ) (hc : ∀ c : k, c ≠ 0 → v (algebraMap k (RatFunc k) c) = 1)
    (hX : v (RatFunc.X⁻¹) < 1) {f : k[X]} (hf : f ≠ 0) :
    v (algebraMap k[X] (RatFunc k) f) = v RatFunc.X ^ f.natDegree := by
  let _ : Invertible (RatFunc.X : RatFunc k) := invertibleOfNonzero RatFunc.X_ne_zero
  have h := eval₂_reverse_mul_pow (algebraMap k (RatFunc k)) (RatFunc.X : RatFunc k) f
  rw [invOf_eq_inv, ← aeval_def, ← aeval_def] at h
  rw [ratFunc_algebraMap_eq_aeval_X, ← h, v.map_mul, v.map_pow,
    valuation_aeval_inv_X_eq_one v hc hX _ (by
      rw [coeff_zero_reverse]
      exact leadingCoeff_ne_zero.mpr hf), one_mul]

/-- Let `1 < a`. Then `a^m / a^n ≤ 1` if and only if `m ≤ n`. -/
theorem pow_div_pow_le_one_iff {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a : Γ}
    (ha : 1 < a) (m n : ℕ) : a ^ m / a ^ n ≤ 1 ↔ m ≤ n := by
  have ha0 : a ≠ 0 := (zero_lt_one.trans ha).ne'
  rw [div_le_one₀ (pow_pos (zero_lt_one.trans ha) n)]
  exact pow_le_pow_iff_right₀ ha

/-- A valuation that is `1` on the nonzero constants and `< 1` on `1/x` is at most `1` on
`x ∈ k(x)` if and only if `x = 0` or the degree of the numerator is at most the degree of the
denominator. -/
theorem valuation_le_one_iff_natDegree_le {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (RatFunc k) Γ) (hc : ∀ c : k, c ≠ 0 → v (algebraMap k (RatFunc k) c) = 1)
    (hX : v (RatFunc.X⁻¹) < 1) (x : RatFunc k) :
    v x ≤ 1 ↔ x = 0 ∨ x.num.natDegree ≤ x.denom.natDegree := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : x.num ≠ 0 := fun h => hx (RatFunc.num_eq_zero_iff.mp h)
  have h1 : 1 < v RatFunc.X := by
    rw [map_inv₀] at hX
    have h0 : v RatFunc.X ≠ 0 := (Valuation.ne_zero_iff v).mpr RatFunc.X_ne_zero
    exact (inv_lt_one₀ (zero_lt_iff.mpr h0)).mp hX
  rw [← RatFunc.num_div_denom x, map_div₀, valuation_algebraMap_eq_pow_natDegree v hc hX hn,
    valuation_algebraMap_eq_pow_natDegree v hc hX x.denom_ne_zero,
    pow_div_pow_le_one_iff h1, RatFunc.num_div_denom x]
  simp [hx]

/-- The valuation subrings of `k(x)` that contain `k` (Volume 3, Example 1.5.6 of the
handbook). Each valuation ring `V` of `k(x)` with `k ⊆ V` is one of the following.
1. The whole field `k(x)`.
2. The valuation ring of the `P`-adic valuation, for a nonzero prime `P` of `k[x]`. This is
   the ring `k[x]_(P)`.
3. The valuation ring of the valuation at infinity. This is the ring `k[1/x]_(1/x)`. -/
theorem valuationSubring_ratFunc_trichotomy [DecidableEq (RatFunc k)]
    (V : ValuationSubring (RatFunc k)) (hk : ∀ c : k, algebraMap k (RatFunc k) c ∈ V) :
    V = ⊤ ∨ (∃ P : IsDedekindDomain.HeightOneSpectrum k[X],
      V = (P.valuation (RatFunc k)).valuationSubring) ∨
      V = (RatFunc.inftyValuation k).valuationSubring := by
  have hc : ∀ c : k, c ≠ 0 → V.valuation (algebraMap k (RatFunc k) c) = 1 := by
    intro c hc0
    refine le_antisymm ((V.valuation_le_one_iff _).mpr (hk c)) ?_
    have h1 := (V.valuation_le_one_iff _).mpr (hk c⁻¹)
    have h2 : V.valuation (algebraMap k (RatFunc k) c) *
        V.valuation (algebraMap k (RatFunc k) c⁻¹) = 1 := by
      rw [← V.valuation.map_mul, ← map_mul, mul_inv_cancel₀ hc0, map_one, V.valuation.map_one]
    by_contra hlt
    rw [not_le] at hlt
    have : V.valuation (algebraMap k (RatFunc k) c) *
        V.valuation (algebraMap k (RatFunc k) c⁻¹) < 1 :=
      (mul_le_of_le_one_right' h1).trans_lt hlt
    exact this.ne h2
  by_cases hX : (RatFunc.X : RatFunc k) ∈ V
  · -- The polynomials lie in `V`.
    have hpoly : ∀ f : k[X], V.valuation (algebraMap k[X] (RatFunc k) f) ≤ 1 := by
      intro f
      rw [V.valuation_le_one_iff, ratFunc_algebraMap_eq_aeval_X]
      refine Polynomial.induction_on f (fun a => ?_) (fun p r hp hr => ?_) (fun n a h => ?_)
      · rw [aeval_C]
        exact hk a
      · rw [map_add]
        exact add_mem hp hr
      · rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
        exact mul_mem h hX
    let A : Subring (RatFunc k) := (algebraMap k[X] (RatFunc k)).range
    have hA : A ≤ V.toSubring := by
      rintro _ ⟨f, rfl⟩
      exact (V.valuation_le_one_iff _).mp (hpoly f)
    let p : Ideal k[X] := (centerIdeal V A hA).comap (algebraMap k[X] (RatFunc k)).rangeRestrict
    have hp : ∀ f : k[X], f ∈ p ↔ V.valuation (algebraMap k[X] (RatFunc k) f) < 1 :=
      fun f => Iff.rfl
    by_cases hbot : p = ⊥
    · left
      refine top_unique fun x _ => ?_
      rw [← V.valuation_le_one_iff, valuation_le_one_iff_not_denom_lt_one _ hpoly, ← hp, hbot,
        Ideal.mem_bot]
      exact x.denom_ne_zero
    · right; left
      let P : IsDedekindDomain.HeightOneSpectrum k[X] := ⟨p, inferInstance, hbot⟩
      refine ⟨P, ?_⟩
      conv_lhs => rw [← V.valuationSubring_valuation]
      refine valuationSubring_eq_of_polynomial _ _ hpoly (P.valuation_le_one) fun f => ?_
      rw [← hp, IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  · right; right
    have hXinv : V.valuation (RatFunc.X⁻¹) < 1 := by
      rw [map_inv₀]
      have h1 : 1 < V.valuation RatFunc.X := not_le.mp fun h => hX ((V.valuation_le_one_iff _).mp h)
      exact (inv_lt_one₀ (zero_lt_one.trans h1)).mpr h1
    have hcinf : ∀ c : k, c ≠ 0 →
        RatFunc.inftyValuation k (algebraMap k (RatFunc k) c) = 1 :=
      fun c hc0 => Valuation.IsTrivialOn.eq_one (v := RatFunc.inftyValuation k) c hc0
    have hXinf : RatFunc.inftyValuation k (RatFunc.X⁻¹) < 1 := by
      rw [map_inv₀, RatFunc.inftyValuation.X, WithZero.inv_exp, WithZero.exp_lt_one_iff]
      norm_num
    ext x
    rw [← V.valuation_le_one_iff, Valuation.mem_valuationSubring_iff,
      valuation_le_one_iff_natDegree_le _ hc hXinv,
      valuation_le_one_iff_natDegree_le _ hcinf hXinf]

end RatFuncPlaces

section LocalRings

open IsDedekindDomain

variable {k : Type*} [Field k]

/-- The ring `k[x]`, as a subring of `k(x)`. In Volume 3, Example 1.4.5 of the handbook, it is
the ring of each of the two charts of the line with the origin doubled. -/
noncomputable abbrev polynomialChart (k : Type*) [Field k] : Subring (RatFunc k) :=
  (algebraMap k[X] (RatFunc k)).range

/-- The ring `k[x]` lies in the valuation ring of each `P`-adic valuation. -/
theorem polynomialChart_le (P : HeightOneSpectrum k[X]) :
    polynomialChart k ≤ (P.valuation (RatFunc k)).valuationSubring.toSubring := by
  rintro _ ⟨f, rfl⟩
  exact P.valuation_le_one f

/-- The center of the `P`-adic valuation on `k[x]` is `P`. -/
theorem mem_centerIdeal_polynomialChart_iff (P : HeightOneSpectrum k[X]) (f : k[X]) :
    (⟨algebraMap k[X] (RatFunc k) f, f, rfl⟩ : polynomialChart k) ∈
      centerIdeal (P.valuation (RatFunc k)).valuationSubring (polynomialChart k)
        (polynomialChart_le P) ↔ f ∈ P.asIdeal := by
  rw [mem_centerIdeal, ← ((P.valuation (RatFunc k)).isEquiv_valuation_valuationSubring
    ).lt_one_iff_lt_one]
  exact P.valuation_lt_one_iff_mem f

/-- The valuation ring of the `P`-adic valuation of `k(x)` is the local ring `k[x]_P`, as
subrings of `k(x)` (Volume 3, Examples 1.4.5 and 1.5.6 of the handbook). -/
theorem toLocalSubring_eq_ofPrime_centerIdeal (P : HeightOneSpectrum k[X]) :
    (P.valuation (RatFunc k)).valuationSubring.toLocalSubring =
      LocalSubring.ofPrime (polynomialChart k)
        (centerIdeal _ (polynomialChart k) (polynomialChart_le P)) := by
  set V := (P.valuation (RatFunc k)).valuationSubring
  have hA := polynomialChart_le P
  refine LocalSubring.toSubring_injective (le_antisymm ?_ (ofPrime_centerIdeal_le V _ hA).1)
  intro x hx
  have hx' : P.valuation (RatFunc k) x ≤ 1 := hx
  rw [valuation_le_one_iff_not_denom_lt_one _ P.valuation_le_one] at hx'
  have hden : (⟨algebraMap k[X] (RatFunc k) x.denom, x.denom, rfl⟩ : polynomialChart k) ∉
      centerIdeal V (polynomialChart k) hA := by
    rw [mem_centerIdeal_polynomialChart_iff, ← P.valuation_lt_one_iff_mem (K := RatFunc k)]
    exact hx'
  have hd : algebraMap k[X] (RatFunc k) x.denom ≠ 0 := fun h =>
    x.denom_ne_zero (RatFunc.algebraMap_injective k (h.trans (map_zero _).symm))
  refine ⟨IsLocalization.mk' (Localization.AtPrime (centerIdeal V (polynomialChart k) hA))
    (⟨algebraMap k[X] (RatFunc k) x.num, x.num, rfl⟩ : polynomialChart k)
    (⟨_, hden⟩ : (centerIdeal V (polynomialChart k) hA).primeCompl), ?_⟩
  rw [IsLocalization.lift_mk'_spec]
  show algebraMap k[X] (RatFunc k) x.num = algebraMap k[X] (RatFunc k) x.denom * x
  rw [mul_comm]
  exact (div_eq_iff hd).mp (RatFunc.num_div_denom x)

/-- **Two centers on the line with the origin doubled** (Volume 3, Example 1.4.5 of the
handbook, the algebraic part). Let `V = k[t]_(t)` be the valuation ring of `ord_t` on `k(t)`.
Each of the two charts of the line with the origin doubled has the ring `k[t]`. On each chart
the center of `V` is the origin `(t)`: a polynomial `f` is in the center if and only if
`t ∣ f`. The local ring of each origin is `k[t]_(t)`, and it is equal to `V`. So `V` dominates
the local rings of both origins. -/
theorem centerIdeal_idealX_and_ofPrime_eq :
    (∀ f : k[X], (⟨algebraMap k[X] (RatFunc k) f, f, rfl⟩ : polynomialChart k) ∈
      centerIdeal ((Polynomial.idealX k).valuation (RatFunc k)).valuationSubring
        (polynomialChart k) (polynomialChart_le _) ↔ X ∣ f) ∧
    LocalSubring.ofPrime (polynomialChart k) (centerIdeal _ (polynomialChart k)
      (polynomialChart_le (Polynomial.idealX k))) =
      ((Polynomial.idealX k).valuation (RatFunc k)).valuationSubring.toLocalSubring := by
  refine ⟨fun f => ?_, (toLocalSubring_eq_ofPrime_centerIdeal _).symm⟩
  rw [mem_centerIdeal_polynomialChart_iff, Polynomial.idealX_span, Ideal.mem_span_singleton]

end LocalRings

section ConvexExamples

/-- In an archimedean ordered group, a convex subgroup that contains an element `μ > 1` is the
whole group. This is the archimedean case of Volume 3, Example 2.4.5 of the handbook: there
the smallest convex subgroup that contains `μ` is `Γ_v`. -/
theorem IsConvexSubgroup.eq_top_of_one_lt_mem {G : Type*} [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] [MulArchimedean G] {H : Subgroup G} (hH : IsConvexSubgroup H) {μ : G}
    (hμ : 1 < μ) (hμH : μ ∈ H) : H = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨n, hn⟩ := MulArchimedean.arch (mabs g) hμ
  rw [← mabs_mem_iff]
  exact hH (one_le_mabs g) hn (pow_mem hμH n)

/-- The value `(0, 1)` in the lexicographic group `ℤ^2`. In Volume 3, Example 2.4.5 of the
handbook, it is the value `v(x)` of the valuation of rank 2. -/
def lexValueX : LexZn 2 := Multiplicative.ofAdd (toLex ![0, 1])

/-- **The smallest convex subgroup in the rank 2 case** (Volume 3, Example 2.4.5 of the
handbook). The subgroup `0 × ℤ` of the lexicographic group `ℤ^2` is convex, it contains
`(0, 1)`, and it lies in each convex subgroup that contains `(0, 1)`. -/
theorem isLeast_delta_one_lexValueX :
    IsConvexSubgroup (LexZn.delta 2 1) ∧ lexValueX ∈ LexZn.delta 2 1 ∧
      ∀ H : Subgroup (LexZn 2), IsConvexSubgroup H → lexValueX ∈ H → LexZn.delta 2 1 ≤ H := by
  refine ⟨LexZn.isConvexSubgroup_delta 1, ?_, ?_⟩
  · rw [LexZn.mem_delta]
    intro i hi
    have : i = 0 := Fin.ext (by omega)
    subst this
    rfl
  · intro H hH hμ
    obtain ⟨m, hm, rfl⟩ := (LexZn.isConvexSubgroup_iff H).mp hH
    have hm1 : m ≤ 1 := by
      by_contra h
      have h1 := (LexZn.mem_delta.mp hμ) 1 (by simp; omega)
      exact absurd h1 (by decide)
    intro g hg
    rw [LexZn.mem_delta] at hg ⊢
    exact fun i hi => hg i (by omega)

end ConvexExamples

section Abhyankar

universe u

/-- **Local and global Abhyankar defects** (Volume 3, Corollary 2.3.4 of the handbook, the
algebraic part). Let `k ⊆ κ ⊆ L` be fields, where `κ` is the residue field of the center and
`L = Kv` is the residue field of `v`. Assume the dimension formula
`dim R + trdeg(κ/k) = trdeg(K/k)` and that the transcendence degrees of `κ/k` and `L/κ` are
finite. Then `trdeg(K/k) - r - trdeg(L/k) = dim R - r - trdeg(L/κ)` for each `r`. -/
theorem trdeg_sub_eq_dim_sub {k κ K L : Type u} [Field k] [Field κ] [Field K] [Field L]
    [Algebra k κ] [Algebra κ L] [Algebra k L] [IsScalarTower k κ L] [Algebra k K] (d r : ℕ)
    (hκ : Algebra.trdeg k κ < Cardinal.aleph0) (hL : Algebra.trdeg κ L < Cardinal.aleph0)
    (hdim : d + (Algebra.trdeg k κ).toNat = (Algebra.trdeg k K).toNat) :
    ((Algebra.trdeg k K).toNat : ℤ) - r - (Algebra.trdeg k L).toNat =
      (d : ℤ) - r - (Algebra.trdeg κ L).toNat := by
  have h := trdeg_add_eq k κ (A := L)
  have h' : (Algebra.trdeg k L).toNat = (Algebra.trdeg k κ).toNat + (Algebra.trdeg κ L).toNat :=
    by rw [← h, Cardinal.toNat_add hκ hL]
  rw [h', ← hdim]
  push_cast
  ring

/-- Under the hypotheses of `trdeg_sub_eq_dim_sub`, equality holds in the local form of the
Abhyankar inequality if and only if it holds in the field form (Volume 3, Corollary 2.3.4 of
the handbook, the last claim). -/
theorem add_trdeg_eq_dim_iff {k κ K L : Type u} [Field k] [Field κ] [Field K] [Field L]
    [Algebra k κ] [Algebra κ L] [Algebra k L] [IsScalarTower k κ L] [Algebra k K] (d r : ℕ)
    (hκ : Algebra.trdeg k κ < Cardinal.aleph0) (hL : Algebra.trdeg κ L < Cardinal.aleph0)
    (hdim : d + (Algebra.trdeg k κ).toNat = (Algebra.trdeg k K).toNat) :
    r + (Algebra.trdeg κ L).toNat = d ↔
      r + (Algebra.trdeg k L).toNat = (Algebra.trdeg k K).toNat := by
  have := trdeg_sub_eq_dim_sub (K := K) d r hκ hL hdim
  omega

end Abhyankar

section Defect

/-- The defect is a power of `p` (Volume 3, Corollary 3.2.2 of the handbook, from the theorem of
Ostrowski). If `n = p^ν e f` with `ef > 0`, then `d = n / (ef) = p^ν`. -/
theorem div_eq_pow_of_eq_pow_mul {n e f p ν : ℕ} (hef : 0 < e * f)
    (h : n = p ^ ν * (e * f)) : n / (e * f) = p ^ ν := by
  rw [h, Nat.mul_div_cancel _ hef]

/-- **No defect for degrees prime to `p`** (Volume 3, Corollary 3.2.2 of the handbook, from the
theorem of Ostrowski). If `n = p^ν e f` and either `p = 1` or `p` is a prime with `p ∤ n`, then
`ef = n`. -/
theorem mul_eq_of_eq_pow_mul {n e f p ν : ℕ} (hp : p = 1 ∨ (p.Prime ∧ ¬ p ∣ n))
    (h : n = p ^ ν * (e * f)) : e * f = n := by
  rcases hp with rfl | ⟨hp, hn⟩
  · simp [h]
  · cases ν with
    | zero => simp [h]
    | succ ν =>
      exact absurd (h ▸ dvd_mul_of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero ν)) _) hn

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (V : ValuationSubring L)

/-- **Best approximations in residue characteristic `0`** (Volume 3, Corollary 4.2.3 of the
handbook, from the theorem of Ostrowski). Let `x_1, ..., x_e` and `y_1, ..., y_f` be as in
`Singularity.exists_forall_valuation_sub_le`. Assume the conclusion `n = p^ν e f` of the theorem
of Ostrowski, with `p = 1`, or with `p` a prime that does not divide `n = [L : K]`. Then each
`z ∈ L \ K` has a best approximation in `K`. -/
theorem exists_forall_valuation_sub_le_of_eq_pow_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    {x : ι → L} {y : κ → L} (hx0 : ∀ i, x i ≠ 0)
    (hx : ∀ i i', i ≠ i' → ∀ a a' : K, a ≠ 0 → a' ≠ 0 →
      V.valuation (algebraMap K L a * x i) ≠ V.valuation (algebraMap K L a' * x i'))
    (hy0 : ∀ j, V.valuation (y j) ≤ 1)
    (hy : ∀ d : κ → K, (∀ j, V.valuation (algebraMap K L (d j)) ≤ 1) →
      V.valuation (∑ j, algebraMap K L (d j) * y j) < 1 →
      ∀ j, V.valuation (algebraMap K L (d j)) < 1)
    {p ν : ℕ} (hp : p = 1 ∨ (p.Prime ∧ ¬ p ∣ Module.finrank K L))
    (hO : Module.finrank K L = p ^ ν * (Fintype.card ι * Fintype.card κ)) (i₀ : ι) (j₀ : κ)
    (h1 : x i₀ * y j₀ = 1) (z : L) (hz : z ∉ Set.range (algebraMap K L)) :
    ∃ a : K, z - algebraMap K L a ≠ 0 ∧
      ∀ a' : K, V.valuation (z - algebraMap K L a) ≤ V.valuation (z - algebraMap K L a') :=
  exists_forall_valuation_sub_le V hx0 hx hy0 hy (mul_eq_of_eq_pow_mul hp hO) i₀ j₀ h1 z hz

end Defect

end Singularity
