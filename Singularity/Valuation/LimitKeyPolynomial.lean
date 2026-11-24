/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.LimitAugmentation

/-!
# The limit key polynomial is a key polynomial for the limit augmentation

This file continues `Singularity/Valuation/LimitAugmentation.lean`. Let `μᵢ = [μ; φᵢ, γᵢ]` be a continuous family of one degree `d` (`ContinuousFamily μ ι`), let `φ` be a limit key polynomial (`ContinuousFamily.IsLimitKeyPolynomial`), and let `w = [μ_∞; φ, γ]` be the limit augmentation with `γ ≤ μᵢ φ` for each `i`. The file proves two results.

1. The polynomial `φ` is a key polynomial for `w` in the sense of `KeyPolynomial` (Definition 3.3.3 of Volume 3 of the handbook). That is, `φ` is monic, `w`-irreducible and `w`-minimal. This needs no hypothesis beyond the hypotheses that make `w` a valuation.
2. Let `μᵢ ≤ ν` for each `i` in additive notation, and let `ν` agree with `μ` in degree less than `d`. Then `w = [μ_∞; φ, ν(φ)]` agrees with `ν` on the polynomials of degree at most `deg φ` if and only if `φ` has the largest `ν`-value (in additive notation) among the monic polynomials of degree `deg φ`. Thus the claim "`w` and `ν` agree in degree `≤ deg φ`" is false for an arbitrary limit key polynomial. It is true for a limit key polynomial of largest `ν`-value. Each monic polynomial `ψ` of degree `deg φ` with `ν(ψ) ≥ ν(φ)` in additive notation is again a limit key polynomial. So if the largest value is attained, it is attained by a limit key polynomial.

The conventions are those of `Singularity/Valuation/KeyPolynomials.lean`. The valuations are multiplicative. Thus `μ ≤ ν` in the additive notation of the handbook is `∀ f, ν f ≤ μ f` here, and "the largest additive value" is "the smallest value" here.

## The proof

* The criterion for divisibility. Let `r` be the remainder of `f` modulo `φ`. Then `μ_∞ r ≤ w f`, since `r` is the coefficient of index `0` of the `φ`-expansion. The polynomial `φ` `w`-divides `f` if and only if `μ_∞ r < w f`. For one direction, `(f - φ * h) %ₘ φ = r`, so `μ_∞ r ≤ w (f - φ * h) < w f`. For the other direction, take `h = f /ₘ φ`. Then `f - φ * h = r` and `w r = μ_∞ r`.
* The product of remainders. Let `a` and `b` have degree less than the degree of `φ`. They are stable, and so is `a * b`. The quotient of `a * b` by `φ` has degree less than the degree of `φ`, so it is stable. Then `μ_∞ (a * b %ₘ φ) = μ_∞ (a * b) = μ_∞ a * μ_∞ b` by `IsLimitKeyPolynomial.stableValue_modByMonic`.
* The key polynomial. A polynomial `f` of degree less than the degree of `φ` is its own remainder, and `w f = μ_∞ f`. So `φ` does not `w`-divide `f`. This gives the minimality, and `φ` does not `w`-divide `1`. If `φ` does not `w`-divide `f` and `g`, then `μ_∞ (f %ₘ φ) = w f` and `μ_∞ (g %ₘ φ) = w g`. The remainder of `f * g` is the remainder of `(f %ₘ φ) * (g %ₘ φ)`, so it has the value `w f * w g = w (f * g)`. Thus `φ` does not `w`-divide `f * g`. This is the proof of `KeyPolynomial.keyPolynomial_of_forall_eq`, with `μ_∞` in place of `μ`.
* Other limit key polynomials. Let `ψ` be monic of degree `deg φ` with `ν ψ ≤ ν φ`, and let `s = ψ - φ`. Then `ν s ≤ ν φ`. If `ψ` were stable, then for `j` large `μⱼ φ ≤ max (μⱼ ψ) (μⱼ s) = max (ν ψ) (ν s) ≤ ν φ ≤ μⱼ φ`. So `φ` would be stable, a contradiction.
* Agreement in degree `≤ deg φ`. Let `f` have degree at most `deg φ`. Then `f = r + φ * c` with a constant `c`. If `c ≠ 0`, then `f = c * ψ` for the monic polynomial `ψ = φ + c⁻¹ r` of degree `deg φ`. The hypothesis `ν φ ≤ ν ψ` gives `ν (φ * c) ≤ ν f`, and then `ν r ≤ ν f`. So `w f ≤ max (w r) (w φ * w c) = max (ν r) (ν (φ * c)) ≤ ν f`. The other inequality `ν f ≤ w f` is `IsLimitKeyPolynomial.map_le_limitAugmentedValuationFun`. For the converse, the coefficient of index `1` of the `φ`-expansion of `ψ` is `1`. So `ν φ ≤ w ψ = ν ψ`.

## Main results

* `Singularity.ContinuousFamily.IsLimitKeyPolynomial.muDvd_iff_of_forall_eq`: the criterion for `w`-divisibility by `φ`.
* `Singularity.ContinuousFamily.IsLimitKeyPolynomial.keyPolynomial_of_forall_eq` and `Singularity.ContinuousFamily.IsLimitKeyPolynomial.keyPolynomial_limitAugmentedValuation`: `φ` is a key polynomial for `[μ_∞; φ, γ]`.
* `Singularity.ContinuousFamily.IsLimitKeyPolynomial.of_map_le`: a monic polynomial of degree `deg φ` with a value at least `ν(φ)` in additive notation is a limit key polynomial.
* `Singularity.ContinuousFamily.IsLimitKeyPolynomial.forall_limitAugmentedValuationFun_eq_iff`: `[μ_∞; φ, ν(φ)]` agrees with `ν` in degree at most `deg φ` if and only if `φ` has the largest `ν`-value among the monic polynomials of degree `deg φ`.
* `Singularity.ContinuousFamily.IsLimitKeyPolynomial.limitStep`: the limit step of MacLane-Vaquié for such a `φ`. There is a valuation `w` with the values of `[μ_∞; φ, ν(φ)]`. The polynomial `φ` is a key polynomial for `w`, `μᵢ ≤ w ≤ ν` for each `i`, and `w` agrees with `ν` in degree at most `deg φ`.

## What the file does not prove

The file does not prove that the largest `ν`-value among the monic polynomials of degree `deg φ` is attained. This can fail, and then the chain needs more steps of the same degree. The file does not build the full chain of MacLane-Vaquié with ordinary and limit steps, and it does not prove that this chain reaches `ν`. It does not bound the number of limit steps. It does not treat the graded algebra of the limit augmentation.

## References

* [Vaq07] M. Vaquié, Extension d'une valuation.
* [HMOS22] F. J. Herrera Govantes, W. Mahboub, M. A. Olalla Acosta and M. Spivakovsky, Key polynomials for simple extensions of valued fields.
-/

open Polynomial

namespace Singularity

namespace ContinuousFamily

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
variable {μ : Valuation K[X] Γ₀} {ι : Type*} [LinearOrder ι] {F : ContinuousFamily μ ι}
variable {φ : K[X]} {γ : Γ₀}

/-- The limit value of the remainder of `f` modulo `φ` is at most the limit augmented value of `f`. In additive notation, `μ_∞(a₀) ≥ [μ_∞; φ, γ](f)` for the coefficient `a₀` of the `φ`-expansion of `f`. -/
theorem stableValue_modByMonic_le_limitAugmentedValuationFun (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) (f : K[X]) :
    F.stableValue (f %ₘ φ) ≤ F.limitAugmentedValuationFun φ γ f := by
  simpa [expansionCoeff_zero_eq_modByMonic] using
    F.le_limitAugmentedValuationFun (γ := γ) hφ hd f 0

namespace IsLimitKeyPolynomial

variable [Nonempty ι] [NoMaxOrder ι] (hφ : F.IsLimitKeyPolynomial φ)
include hφ

/-- The product of two remainders in the limit. Let `a` and `b` have degree less than the degree of `φ`. Then `μ_∞ (a * b %ₘ φ) = μ_∞ a * μ_∞ b`. -/
theorem stableValue_mul_modByMonic {a b : K[X]} (ha : a.degree < φ.degree)
    (hb : b.degree < φ.degree) :
    F.stableValue (a * b %ₘ φ) = F.stableValue a * F.stableValue b := by
  have hs := (hφ.isStable_of_degree_lt ha).stableValue_mul (hφ.isStable_of_degree_lt hb)
  rw [hφ.stableValue_modByMonic hs.1 (hφ.isStable_of_degree_lt
    (degree_mul_divByMonic_lt hφ.monic hφ.natDegree_pos ha hb)), hs.2]

omit [NoMaxOrder ι] in
/-- The criterion for divisibility by `φ` for the limit augmentation. Let `w` be a valuation with the values of `[μ_∞; φ, γ]`. Then `φ` `w`-divides `f` if and only if `μ_∞ (f %ₘ φ) < w f`. In additive notation, the minimum of the terms of the `φ`-expansion of `f` is not attained at `j = 0`. -/
theorem muDvd_iff_of_forall_eq {w : Valuation K[X] Γ₀}
    (hw : ∀ f, w f = F.limitAugmentedValuationFun φ γ f) {f : K[X]} :
    MuDvd w φ f ↔ F.stableValue (f %ₘ φ) < w f := by
  have hm := hφ.monic
  have hd := hφ.natDegree_pos
  constructor
  · rintro ⟨h, hh⟩
    have h0 : (f - φ * h) %ₘ φ = f %ₘ φ := by
      rw [sub_modByMonic, (modByMonic_eq_zero_iff_dvd hm).2 (dvd_mul_right _ _), sub_zero]
    have hle := F.stableValue_modByMonic_le_limitAugmentedValuationFun (γ := γ) hm hd (f - φ * h)
    rw [h0, ← hw] at hle
    exact lt_of_le_of_lt hle hh
  · intro hf
    refine ⟨f /ₘ φ, ?_⟩
    unfold MuEquiv
    rwa [sub_eq_of_eq_add (modByMonic_add_div f φ).symm, hw,
      F.limitAugmentedValuationFun_of_degree_lt hm hd (degree_modByMonic_lt f hm)]

/-- A limit key polynomial `φ` is a key polynomial for each valuation `w` with the values of the limit augmentation `[μ_∞; φ, γ]`. The theorem gives the three conditions of `KeyPolynomial`: `φ` is monic, `w`-irreducible and `w`-minimal. Such a `w` exists if `γ ≤ μᵢ φ` for each `i` (`ContinuousFamily.limitAugmentedValuation`). -/
theorem keyPolynomial_of_forall_eq {w : Valuation K[X] Γ₀}
    (hw : ∀ f, w f = F.limitAugmentedValuationFun φ γ f) : KeyPolynomial w φ := by
  have hm := hφ.monic
  have hd := hφ.natDegree_pos
  have hdvd := fun f => hφ.muDvd_iff_of_forall_eq hw (f := f)
  -- a polynomial of degree less than the degree of `φ` is not `w`-divided by `φ`
  have hlow : ∀ f : K[X], f.degree < φ.degree → ¬ MuDvd w φ f := fun f hf h => by
    rw [hdvd, (modByMonic_eq_self_iff hm).2 hf, hw,
      F.limitAugmentedValuationFun_of_degree_lt hm hd hf] at h
    exact lt_irrefl _ h
  -- the limit value of the remainder of `f` is at most `w f`
  have hle : ∀ f : K[X], F.stableValue (f %ₘ φ) ≤ w f := fun f =>
    (hw f).symm ▸ F.stableValue_modByMonic_le_limitAugmentedValuationFun hm hd f
  refine ⟨hm, ⟨hlow 1 ?_, fun f g hfg => ?_⟩, fun f _ h => ?_⟩
  · rw [degree_one]
    exact natDegree_pos_iff_degree_pos.1 hd
  · rw [hdvd] at hfg
    rw [hdvd, hdvd]
    by_contra hne
    rw [not_or, not_lt, not_lt] at hne
    have hf := le_antisymm (hle f) hne.1
    have hg := le_antisymm (hle g) hne.2
    rw [mul_modByMonic, hφ.stableValue_mul_modByMonic (degree_modByMonic_lt f hm)
      (degree_modByMonic_lt g hm), hf, hg, ← Valuation.map_mul] at hfg
    exact lt_irrefl _ hfg
  · by_contra hlt
    rw [not_le] at hlt
    exact hlow f (degree_lt_degree hlt) h

/-- A limit key polynomial `φ` is a key polynomial for the limit augmentation `[μ_∞; φ, γ]`, for each `γ` with `γ ≤ μᵢ φ` for each `i`. In additive notation, `γ ≥ μᵢ(φ)` for each `i`. This is the condition that makes `[μ_∞; φ, γ]` a valuation. -/
theorem keyPolynomial_limitAugmentedValuation
    (hγ : ∀ i, γ ≤ augmentedValuationFun μ (F.key i) (F.value i) φ) :
    KeyPolynomial (F.limitAugmentedValuation φ γ hφ hγ) φ :=
  hφ.keyPolynomial_of_forall_eq fun _ => rfl

variable {ν : Valuation K[X] Γ₀}
  (hν : ∀ i f, ν f ≤ augmentedValuationFun μ (F.key i) (F.value i) f)
  (hlow : ∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = μ a)

include hν hlow in
/-- Let `μᵢ ≤ ν` for each `i` in additive notation, and let `ν` agree with `μ` in degree less than `d`. Let `ψ` be a monic polynomial of the degree of the limit key polynomial `φ`, with `ν ψ ≤ ν φ`. In additive notation, `ν(ψ) ≥ ν(φ)`. Then `ψ` is a limit key polynomial. -/
theorem of_map_le {ψ : K[X]} (hψ : ψ.Monic) (hdeg : ψ.natDegree = φ.natDegree)
    (hle : ν ψ ≤ ν φ) : F.IsLimitKeyPolynomial ψ := by
  classical
  refine ⟨hψ, fun hs => hφ.not_isStable ?_, fun f hf => by
    rw [hdeg]
    exact hφ.natDegree_le f hf⟩
  set s := ψ - φ with hsdef
  have hsd : s.degree < φ.degree := degree_sub_lt_of_monic hφ.monic hψ hdeg
  have hss := hφ.isStable_of_degree_lt hsd
  have hνs : ν s ≤ ν φ := (Valuation.map_sub _ _ _).trans (max_le hle le_rfl)
  obtain ⟨i, hi⟩ := F.exists_forall_val_eq {ψ, s} (by simp [hs, hss])
  refine (stableValue_eq_of_forall (i := i) (c := ν φ) fun j hj =>
    le_antisymm ?_ (hν j φ)).1
  have e1 : F.val j ψ = ν ψ :=
    (hi j hj ψ (by simp)).trans (F.stableValue_eq_of_isStable hν hlow hs)
  have e2 : F.val j s = ν s :=
    (hi j hj s (by simp)).trans (F.stableValue_eq_of_isStable hν hlow hss)
  calc F.val j φ = F.val j (ψ - s) := by rw [hsdef, sub_sub_cancel]
    _ ≤ max (F.val j ψ) (F.val j s) := Valuation.map_sub _ _ _
    _ ≤ ν φ := by
      rw [e1, e2]
      exact max_le hle hνs

include hν hlow in
/-- Agreement in degree at most `deg φ`. Let `μᵢ ≤ ν` for each `i` in additive notation, let `ν` agree with `μ` in degree less than `d`, and let `ν φ ≤ ν ψ` for each monic `ψ` of the degree of `φ`. In additive notation, `φ` has the largest `ν`-value among the monic polynomials of its degree. Then the limit augmentation `[μ_∞; φ, ν(φ)]` agrees with `ν` on each polynomial of degree at most `deg φ`. -/
theorem limitAugmentedValuationFun_eq_of_natDegree_le
    (hopt : ∀ ψ : K[X], ψ.Monic → ψ.natDegree = φ.natDegree → ν φ ≤ ν ψ) {f : K[X]}
    (hf : f.natDegree ≤ φ.natDegree) : F.limitAugmentedValuationFun φ (ν φ) f = ν f := by
  have hm := hφ.monic
  have hd := hφ.natDegree_pos
  obtain ⟨w, hw⟩ : ∃ w : Valuation K[X] Γ₀, ∀ g, w g = F.limitAugmentedValuationFun φ (ν φ) g :=
    ⟨F.limitAugmentedValuation φ (ν φ) hφ (fun i => hν i φ), fun _ => rfl⟩
  have hwlow : ∀ a : K[X], a.degree < φ.degree → w a = ν a := fun a ha => by
    rw [hw, F.limitAugmentedValuationFun_of_degree_lt hm hd ha,
      F.stableValue_eq_of_isStable hν hlow (hφ.isStable_of_degree_lt ha)]
  -- the quotient of `f` by `φ` is a constant `c`
  have hdeg : (f /ₘ φ).degree ≤ 0 := by
    by_cases h0 : f /ₘ φ = 0
    · rw [h0, degree_zero]
      exact bot_le
    · rw [degree_eq_natDegree h0, natDegree_divByMonic f hm, Nat.sub_eq_zero_of_le hf]
      simp
  obtain ⟨c, hc⟩ : ∃ c, f /ₘ φ = C c := ⟨_, eq_C_of_degree_le_zero hdeg⟩
  have hsum : f %ₘ φ + φ * C c = f := hc ▸ modByMonic_add_div f φ
  have hr : (f %ₘ φ).degree < φ.degree := degree_modByMonic_lt f hm
  have hC : (C c).degree < φ.degree := degree_C_le.trans_lt (natDegree_pos_iff_degree_pos.1 hd)
  -- the main inequality: `ν (φ * c) ≤ ν f`
  have hkey : ν (φ * C c) ≤ ν f := by
    by_cases hc0 : c = 0
    · rw [hc0, C_0, mul_zero, Valuation.map_zero]
      exact zero_le
    have hr' : (C c⁻¹ * (f %ₘ φ)).degree < φ.degree := by
      rw [degree_C_mul (inv_ne_zero hc0)]
      exact hr
    have hψ : (φ + C c⁻¹ * (f %ₘ φ)).Monic := hm.add_of_left hr'
    have hψd : (φ + C c⁻¹ * (f %ₘ φ)).natDegree = φ.natDegree :=
      natDegree_add_eq_left_of_degree_lt hr'
    have hcc : C c * C c⁻¹ = 1 := by rw [← C_mul, mul_inv_cancel₀ hc0, C_1]
    have e : f = C c * (φ + C c⁻¹ * (f %ₘ φ)) := by
      conv_lhs => rw [← hsum]
      rw [mul_add, ← mul_assoc, hcc, one_mul, mul_comm φ]
      exact add_comm _ _
    calc ν (φ * C c) = ν (C c) * ν φ := by rw [Valuation.map_mul, mul_comm]
      _ ≤ ν (C c) * ν (φ + C c⁻¹ * (f %ₘ φ)) := mul_le_mul' le_rfl (hopt _ hψ hψd)
      _ = ν f := by rw [← Valuation.map_mul, ← e]
  have hrle : ν (f %ₘ φ) ≤ ν f := by
    rw [eq_sub_of_add_eq hsum]
    exact (Valuation.map_sub _ _ _).trans (max_le le_rfl hkey)
  refine le_antisymm ?_ (hφ.map_le_limitAugmentedValuationFun hν hlow le_rfl f)
  rw [← hw]
  calc w f = w (f %ₘ φ + φ * C c) := by rw [hsum]
    _ ≤ max (w (f %ₘ φ)) (w (φ * C c)) := Valuation.map_add _ _ _
    _ = max (ν (f %ₘ φ)) (ν (φ * C c)) := by
      rw [Valuation.map_mul w, Valuation.map_mul ν, hwlow _ hr, hwlow _ hC, hw,
        F.limitAugmentedValuationFun_self hm hd]
    _ ≤ ν f := max_le hrle hkey

omit [NoMaxOrder ι] in
/-- The converse of `limitAugmentedValuationFun_eq_of_natDegree_le`. If `[μ_∞; φ, ν(φ)]` agrees with `ν` on each polynomial of degree at most `deg φ`, then `ν φ ≤ ν ψ` for each monic `ψ` of the degree of `φ`. The coefficient of index `1` of the `φ`-expansion of `ψ` is `1`, so `ν φ ≤ [μ_∞; φ, ν(φ)] ψ = ν ψ`. -/
theorem map_le_of_forall_eq
    (h : ∀ f : K[X], f.natDegree ≤ φ.natDegree → F.limitAugmentedValuationFun φ (ν φ) f = ν f)
    {ψ : K[X]} (hψ : ψ.Monic) (hdeg : ψ.natDegree = φ.natDegree) : ν φ ≤ ν ψ := by
  have hm := hφ.monic
  have hd := hφ.natDegree_pos
  have hr := degree_sub_lt_of_monic hm hψ hdeg
  have h1 : (1 : K[X]).degree < φ.degree := by
    rw [degree_one]
    exact natDegree_pos_iff_degree_pos.1 hd
  have e : expansionCoeff φ ψ 1 = 1 := by
    have h2 := expansionCoeff_pow_mul_of_degree_lt hm h1 1 1
    have h3 := expansionCoeff_pow_mul_of_degree_lt hm hr 0 1
    rw [pow_one, mul_one, ite_eq_left rfl] at h2
    rw [pow_zero, one_mul, ite_eq_right one_ne_zero] at h3
    rw [show ψ = φ + (ψ - φ) by ring, expansionCoeff_add, h2, h3, add_zero]
  calc ν φ = F.stableValue (expansionCoeff φ ψ 1) * ν φ ^ 1 := by
        rw [e, F.stableValue_one.2, one_mul, pow_one]
    _ ≤ F.limitAugmentedValuationFun φ (ν φ) ψ := F.le_limitAugmentedValuationFun hm hd ψ 1
    _ = ν ψ := h ψ hdeg.le

include hν hlow in
/-- Let `μᵢ ≤ ν` for each `i` in additive notation, and let `ν` agree with `μ` in degree less than `d`. Then the limit augmentation `[μ_∞; φ, ν(φ)]` agrees with `ν` on the polynomials of degree at most `deg φ` if and only if `φ` has the largest `ν`-value (in additive notation) among the monic polynomials of degree `deg φ`. -/
theorem forall_limitAugmentedValuationFun_eq_iff :
    (∀ f : K[X], f.natDegree ≤ φ.natDegree → F.limitAugmentedValuationFun φ (ν φ) f = ν f) ↔
      ∀ ψ : K[X], ψ.Monic → ψ.natDegree = φ.natDegree → ν φ ≤ ν ψ :=
  ⟨fun h _ hψ hdeg => hφ.map_le_of_forall_eq h hψ hdeg,
    fun hopt _ hf => hφ.limitAugmentedValuationFun_eq_of_natDegree_le hν hlow hopt hf⟩

include hν hlow in
/-- The limit step of MacLane-Vaquié. Let `μᵢ ≤ ν` for each `i` in additive notation, let `ν` agree with `μ` in degree less than `d`, and let the limit key polynomial `φ` have the largest `ν`-value among the monic polynomials of its degree. Then there is a valuation `w` with the values of `[μ_∞; φ, ν(φ)]`. The polynomial `φ` is a key polynomial for `w`, `μᵢ ≤ w ≤ ν` for each `i` in additive notation, and `w` agrees with `ν` on the polynomials of degree at most `deg φ`. -/
theorem limitStep
    (hopt : ∀ ψ : K[X], ψ.Monic → ψ.natDegree = φ.natDegree → ν φ ≤ ν ψ) :
    ∃ w : Valuation K[X] Γ₀, (∀ f, w f = F.limitAugmentedValuationFun φ (ν φ) f) ∧
      KeyPolynomial w φ ∧ (∀ i f, w f ≤ augmentedValuationFun μ (F.key i) (F.value i) f) ∧
      (∀ f, ν f ≤ w f) ∧ ∀ f : K[X], f.natDegree ≤ φ.natDegree → w f = ν f :=
  ⟨F.limitAugmentedValuation φ (ν φ) hφ (fun i => hν i φ), fun _ => rfl,
    hφ.keyPolynomial_limitAugmentedValuation _,
    fun i f => hφ.limitAugmentedValuationFun_le (fun j => hν j φ) i f,
    fun f => hφ.map_le_limitAugmentedValuationFun hν hlow le_rfl f,
    fun _ hf => hφ.limitAugmentedValuationFun_eq_of_natDegree_le hν hlow hopt hf⟩

end IsLimitKeyPolynomial

end ContinuousFamily

end Singularity
