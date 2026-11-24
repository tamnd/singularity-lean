/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.Augmentation

/-!
# The step of MacLane

Let `μ` and `ν` be valuations on `K[X]` with `μ ≤ ν` in the additive notation of the handbook, and let `φ` be a monic polynomial of least degree with `μ(φ) < ν(φ)`. This file proves that `φ` is a key polynomial for `μ`, and that the augmented valuation `μ' = [μ; φ, ν(φ)]` satisfies `μ ≤ μ' ≤ ν`. Also `μ'` agrees with `ν` on the polynomials of degree less than the degree of `φ`, and `μ'(φ) = ν(φ)`. This is the step of the theorem of MacLane-Vaquié that builds the chain of part 4 of Theorem 3.3.5 of Volume 3 of the handbook (Lemma 3.3.9). The file also proves the first step of the chain: if `ν` extends `v`, then the monomial valuation `[v; X, ν(X)]` is at most `ν`.

The conventions are those of `Singularity/Valuation/KeyPolynomials.lean`. The valuations are multiplicative. Thus `μ ≤ ν` in the handbook is `∀ f, ν f ≤ μ f` here, and `μ(φ) < ν(φ)` is `ν φ < μ φ`.

## The hypotheses

The theorems for a given `φ` use three hypotheses: `∀ f, ν f ≤ μ f`, `ν φ < μ φ`, and `ν f = μ f` for each `f` of degree less than the degree of `φ`. They do not ask that `μ` or `ν` has support `0`, and they do not ask that `μ` is an augmentation or a monomial valuation. If `μ` and `ν` agree on the constants, then the third hypothesis holds exactly when `φ` has the least degree among the monic polynomials with `ν φ < μ φ` (`exists_monic_map_lt`).

## The proof

* If `φ` `μ`-divides `f`, then `ν f < μ f`. Write `f = (f - φ * h) + φ * h` with `ν (f - φ * h) ≤ μ (f - φ * h) < μ f` and `ν (φ * h) < μ (φ * h) = μ f`.
* If `ν f < μ f`, then `φ` `μ`-divides `f`. Write `f = a + φ * q` with `a = f %ₘ φ`. Then `ν a = μ a`. If `μ f ≤ μ a`, then `ν f < ν a`, so `ν (φ * q) = ν a`, and `μ (φ * q) > ν (φ * q) = μ a`. Then `μ f = μ (φ * q) > μ a`, a contradiction. Thus `μ (f - φ * q) = μ a < μ f`.
* Thus `φ` `μ`-divides `f` if and only if `ν f < μ f`. The irreducibility and the minimality of `φ` follow from this criterion, because `ν (f * g) < μ (f * g)` gives `ν f < μ f` or `ν g < μ g`.
* For the `φ`-expansion `f = ∑ aⱼ φ ^ j`, we have `ν f ≤ max (ν aⱼ * ν φ ^ j) = max (μ aⱼ * ν φ ^ j) = [μ; φ, ν φ] f`.

## Main results

* `Singularity.muDvd_iff_map_lt`: `φ` `μ`-divides `f` if and only if `ν f < μ f`.
* `Singularity.keyPolynomial_of_map_lt`: `φ` is a key polynomial for `μ`.
* `Singularity.map_le_augmentedValuationFun_of_map_eq`: `[μ; φ, ν φ] ≤ ν` in additive notation, for the function of Definition 3.3.4.
* `Singularity.map_le_augmentedValuation_of_map_lt` and `Singularity.augmentedValuation_eq_of_map_lt`: `[μ; φ, ν φ] ≤ ν`, and the augmentation agrees with `ν` in degree less than the degree of `φ`.
* `Singularity.exists_monic_map_lt`: if `μ ≠ ν` and the two valuations agree on the constants, then a monic `φ` of least degree with `ν φ < μ φ` exists.
* `Singularity.exists_keyPolynomial_augmentedValuation`: the step of MacLane. If `μ ≠ ν`, then there are a key polynomial `φ` for `μ` with `ν φ < μ φ` and the augmentation `μ' = [μ; φ, ν φ]` with `μ ≤ μ' ≤ ν` in additive notation.
* `Singularity.map_le_monomialValuationFun` and `Singularity.map_le_monomialValuation`: the first step, `[v; X, ν(X)] ≤ ν` in additive notation.

The file does not prove part 4 of Theorem 3.3.5. It proves one step of the chain. The file does not prove that the chain reaches `ν`, or that `ν` is a limit of the chain, and it does not construct the limit augmentations.

## References

* [Mac36] S. MacLane, A construction for absolute values in polynomial rings.
* [Vaq07] M. Vaquié, Extension d'une valuation.
-/

open Polynomial

namespace Singularity

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

section Step

variable {μ ν : Valuation K[X] Γ₀} {φ : K[X]}

/-- Let `ν f ≤ μ f` for each `f` and let `ν φ < μ φ`. If `φ` `μ`-divides `f`, then `ν f < μ f`. In additive notation, `μ(f) < ν(f)`. -/
theorem map_lt_of_muDvd (hle : ∀ f, ν f ≤ μ f) (hlt : ν φ < μ φ) {f : K[X]}
    (h : MuDvd μ φ f) : ν f < μ f := by
  obtain ⟨g, hg⟩ := h
  have heq : μ f = μ (φ * g) := hg.map_eq
  have hg0 : μ g ≠ 0 := by
    intro h0
    apply hg.ne_zero
    rw [heq, Valuation.map_mul, h0, mul_zero]
  have h1 : ν (φ * g) < μ f := by
    rw [heq, Valuation.map_mul, Valuation.map_mul]
    calc ν φ * ν g ≤ ν φ * μ g := mul_le_mul' le_rfl (hle g)
      _ < μ φ * μ g := mul_lt_mul_of_pos_right hlt (zero_lt_iff.2 hg0)
  have h2 : ν (f - φ * g) < μ f := lt_of_le_of_lt (hle _) hg
  calc ν f = ν ((f - φ * g) + φ * g) := by rw [sub_add_cancel]
    _ ≤ max (ν (f - φ * g)) (ν (φ * g)) := Valuation.map_add _ _ _
    _ < μ f := max_lt h2 h1

/-- Let `ν f ≤ μ f` for each `f`, let `φ` be monic with `ν φ < μ φ`, and let `ν` and `μ` agree in degree less than the degree of `φ`. If `ν f < μ f`, then `φ` `μ`-divides `f`. -/
theorem muDvd_of_map_lt (hle : ∀ f, ν f ≤ μ f) (hφ : φ.Monic) (hlt : ν φ < μ φ)
    (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f) {f : K[X]} (h : ν f < μ f) :
    MuDvd μ φ f := by
  refine ⟨f /ₘ φ, ?_⟩
  unfold MuEquiv
  have hf : f %ₘ φ + φ * (f /ₘ φ) = f := modByMonic_add_div f φ
  have hsub : f - φ * (f /ₘ φ) = f %ₘ φ := by
    rw [sub_eq_iff_eq_add, hf]
  rw [hsub]
  by_contra hcon
  rw [not_lt] at hcon
  have ha : ν (f %ₘ φ) = μ (f %ₘ φ) := hlow _ (degree_modByMonic_lt f hφ)
  have hνf : ν f < ν (f %ₘ φ) := by
    rw [ha]
    exact lt_of_lt_of_le h hcon
  have hνq : ν (φ * (f /ₘ φ)) = ν (f %ₘ φ) := by
    by_contra hne
    have e := Valuation.map_add_of_distinct_val ν (Ne.symm hne)
    rw [hf] at e
    exact absurd (e ▸ le_max_left _ _ : ν (f %ₘ φ) ≤ ν f) (not_le.2 hνf)
  have hνa0 : ν (f %ₘ φ) ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le hνf)
  have hq0 : μ (f /ₘ φ) ≠ 0 := by
    intro h0
    have h0' : ν (f /ₘ φ) = 0 := le_zero_iff.1 (h0 ▸ hle _)
    apply hνa0
    rw [← hνq, Valuation.map_mul, h0', mul_zero]
  have hlt' : μ (f %ₘ φ) < μ (φ * (f /ₘ φ)) := by
    rw [← ha, ← hνq, Valuation.map_mul, Valuation.map_mul]
    calc ν φ * ν (f /ₘ φ) ≤ ν φ * μ (f /ₘ φ) := mul_le_mul' le_rfl (hle _)
      _ < μ φ * μ (f /ₘ φ) := mul_lt_mul_of_pos_right hlt (zero_lt_iff.2 hq0)
  have e : μ f = μ (φ * (f /ₘ φ)) := by
    conv_lhs => rw [← hf]
    exact Valuation.map_add_eq_of_lt_right μ hlt'
  rw [e] at hcon
  exact absurd hcon (not_le.2 hlt')

/-- Let `ν f ≤ μ f` for each `f`, let `φ` be monic with `ν φ < μ φ`, and let `ν` and `μ` agree in degree less than the degree of `φ`. Then `φ` `μ`-divides `f` if and only if `ν f < μ f`. In additive notation, the condition is `μ(f) < ν(f)`. -/
theorem muDvd_iff_map_lt (hle : ∀ f, ν f ≤ μ f) (hφ : φ.Monic) (hlt : ν φ < μ φ)
    (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f) {f : K[X]} :
    MuDvd μ φ f ↔ ν f < μ f :=
  ⟨map_lt_of_muDvd hle hlt, muDvd_of_map_lt hle hφ hlt hlow⟩

/-- The step of MacLane, part (a). Let `ν f ≤ μ f` for each `f`, let `φ` be monic with `ν φ < μ φ`, and let `ν` and `μ` agree in degree less than the degree of `φ`. Then `φ` is a key polynomial for `μ`. In additive notation, the hypotheses say that `μ ≤ ν` and that `φ` is a monic polynomial of least degree with `μ(φ) < ν(φ)`. -/
theorem keyPolynomial_of_map_lt (hle : ∀ f, ν f ≤ μ f) (hφ : φ.Monic) (hlt : ν φ < μ φ)
    (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f) : KeyPolynomial μ φ := by
  have hiff := fun f => muDvd_iff_map_lt (f := f) hle hφ hlt hlow
  refine ⟨hφ, ⟨?_, fun f g hfg => ?_⟩, fun f _ hfd => ?_⟩
  · rw [hiff, Valuation.map_one, Valuation.map_one]
    exact lt_irrefl 1
  · rw [hiff] at hfg
    rw [hiff, hiff]
    by_contra hne
    rw [not_or, not_lt, not_lt] at hne
    have e1 := le_antisymm (hle f) hne.1
    have e2 := le_antisymm (hle g) hne.2
    rw [Valuation.map_mul, Valuation.map_mul, e1, e2] at hfg
    exact lt_irrefl _ hfg
  · by_contra hd
    rw [not_le] at hd
    rw [hiff] at hfd
    exact ne_of_lt hfd (hlow f (degree_lt_degree hd))

/-- The step of MacLane, part (b), for the function of Definition 3.3.4. Let `φ` be monic of positive degree, and let `ν` and `μ` agree in degree less than the degree of `φ`. Then the augmented value `[μ; φ, ν φ] f` is at least `ν f`. In additive notation, `[μ; φ, ν(φ)] ≤ ν`. -/
theorem map_le_augmentedValuationFun_of_map_eq (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f) (f : K[X]) :
    ν f ≤ augmentedValuationFun μ φ (ν φ) f := by
  conv_lhs => rw [eq_sum_expansionCoeff hφ hd f]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [Valuation.map_mul, Valuation.map_pow, hlow _ (degree_expansionCoeff_lt hφ f j)]
  exact le_augmentedValuationFun hφ hd f j

/-- The step of MacLane, part (b). Let `ν f ≤ μ f` for each `f`, let `φ` be monic with `ν φ < μ φ`, and let `ν` and `μ` agree in degree less than the degree of `φ`. Then the augmented valuation `μ' = [μ; φ, ν φ]` satisfies `ν f ≤ μ' f`. In additive notation, `μ' ≤ ν`. The inequality `μ ≤ μ'` is `augmentedValuation_le`. -/
theorem map_le_augmentedValuation_of_map_lt (hle : ∀ f, ν f ≤ μ f) (hφ : φ.Monic)
    (hlt : ν φ < μ φ) (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f) (f : K[X]) :
    ν f ≤ augmentedValuation μ φ (ν φ) (keyPolynomial_of_map_lt hle hφ hlt hlow) hlt.le f :=
  map_le_augmentedValuationFun_of_map_eq hφ
    (keyPolynomial_of_map_lt hle hφ hlt hlow).natDegree_pos hlow f

/-- The step of MacLane, part (b). Under the hypotheses of `map_le_augmentedValuation_of_map_lt`, the augmented valuation `[μ; φ, ν φ]` agrees with `ν` on the polynomials of degree less than the degree of `φ`. -/
theorem augmentedValuation_eq_of_map_lt (hle : ∀ f, ν f ≤ μ f) (hφ : φ.Monic)
    (hlt : ν φ < μ φ) (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f) {f : K[X]}
    (hf : f.degree < φ.degree) :
    augmentedValuation μ φ (ν φ) (keyPolynomial_of_map_lt hle hφ hlt hlow) hlt.le f = ν f := by
  rw [augmentedValuation_of_degree_lt _ _ hf, hlow f hf]

/-- Let `μ` and `ν` agree on the constants, let `ν f ≤ μ f` for each `f`, and let `μ ≠ ν`. Then there is a monic polynomial `φ` with `ν φ < μ φ` such that `ν f = μ f` for each `f` of degree less than the degree of `φ`. The proof takes `φ` of least degree. -/
theorem exists_monic_map_lt (hC : ∀ c, ν (C c) = μ (C c)) (hle : ∀ f, ν f ≤ μ f)
    (hne : μ ≠ ν) : ∃ φ : K[X], φ.Monic ∧ ν φ < μ φ ∧
      ∀ f : K[X], f.degree < φ.degree → ν f = μ f := by
  classical
  -- the value of a nonzero constant is not zero
  have hC0 : ∀ c : K, c ≠ 0 → μ (C c) ≠ 0 := fun c hc h0 => by
    have h1 : μ (C c * C c⁻¹) = 1 := by rw [← C_mul, mul_inv_cancel₀ hc, C_1, Valuation.map_one]
    rw [Valuation.map_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  -- the monic polynomial `f * C (leadingCoeff f)⁻¹`
  have hnorm : ∀ f : K[X], f ≠ 0 →
      (ν (f * C f.leadingCoeff⁻¹) < μ (f * C f.leadingCoeff⁻¹) ↔ ν f < μ f) := fun f hf0 => by
    have hc : μ (C f.leadingCoeff⁻¹) ≠ 0 :=
      hC0 _ (inv_ne_zero (leadingCoeff_ne_zero.2 hf0))
    rw [Valuation.map_mul, Valuation.map_mul, hC]
    exact mul_lt_mul_iff_of_pos_right (zero_lt_iff.2 hc)
  have hex : ∃ n, ∃ φ : K[X], φ.Monic ∧ φ.natDegree = n ∧ ν φ < μ φ := by
    obtain ⟨f, hf⟩ : ∃ f, ν f ≠ μ f := by
      by_contra h
      rw [not_exists] at h
      exact hne (Valuation.ext fun f => (not_not.1 (h f)).symm)
    have hlt : ν f < μ f := lt_of_le_of_ne (hle f) hf
    have hf0 : f ≠ 0 := by
      rintro rfl
      rw [Valuation.map_zero, Valuation.map_zero] at hlt
      exact lt_irrefl _ hlt
    exact ⟨_, _, monic_mul_leadingCoeff_inv hf0, rfl, (hnorm f hf0).2 hlt⟩
  obtain ⟨φ, hφ, hdeg, hlt⟩ := Nat.find_spec hex
  refine ⟨φ, hφ, hlt, fun f hf => ?_⟩
  by_cases hf0 : f = 0
  · rw [hf0, Valuation.map_zero, Valuation.map_zero]
  refine le_antisymm (hle f) (not_lt.1 fun h => ?_)
  have hlt' : f.natDegree < Nat.find hex := by
    rw [← hdeg]
    exact natDegree_lt_natDegree hf0 hf
  refine Nat.find_min hex hlt' ⟨_, monic_mul_leadingCoeff_inv hf0, ?_, (hnorm f hf0).2 h⟩
  rw [natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.2 hf0))]

/-- The step of MacLane (Lemma 3.3.9 of Volume 3 of the handbook). Let `μ` and `ν` be valuations on `K[X]` that agree on the constants, with `ν f ≤ μ f` for each `f` and `μ ≠ ν`. Then there are a key polynomial `φ` for `μ` with `ν φ < μ φ`, of least degree, and the augmented valuation `μ' = [μ; φ, ν φ]` satisfies `ν f ≤ μ' f ≤ μ f` for each `f`, `μ' φ = ν φ`, and `μ' f = ν f` in degree less than the degree of `φ`. In additive notation, `μ < μ' ≤ ν`. -/
theorem exists_keyPolynomial_augmentedValuation (hC : ∀ c, ν (C c) = μ (C c))
    (hle : ∀ f, ν f ≤ μ f) (hne : μ ≠ ν) :
    ∃ (φ : K[X]) (hφ : KeyPolynomial μ φ) (hlt : ν φ < μ φ),
      (∀ f : K[X], ν f ≤ augmentedValuation μ φ (ν φ) hφ hlt.le f) ∧
      (∀ f : K[X], augmentedValuation μ φ (ν φ) hφ hlt.le f ≤ μ f) ∧
      augmentedValuation μ φ (ν φ) hφ hlt.le φ = ν φ ∧
      (∀ f : K[X], f.degree < φ.degree → augmentedValuation μ φ (ν φ) hφ hlt.le f = ν f) ∧
      (∀ f : K[X], f.degree < φ.degree → ν f = μ f) := by
  obtain ⟨φ, hφ, hlt, hlow⟩ := exists_monic_map_lt hC hle hne
  exact ⟨φ, keyPolynomial_of_map_lt hle hφ hlt hlow, hlt,
    map_le_augmentedValuation_of_map_lt hle hφ hlt hlow, augmentedValuation_le _ _,
    augmentedValuation_self _ _, fun _ hf => augmentedValuation_eq_of_map_lt hle hφ hlt hlow hf,
    hlow⟩

end Step

section FirstStep

variable {v : Valuation K Γ₀} {ν : Valuation K[X] Γ₀}

/-- The first step of the chain of MacLane. Let `ν` be a valuation on `K[X]` that extends `v`. Then the monomial value `[v; X, ν X] f` is at least `ν f`. In additive notation, `[v; X, ν(X)] ≤ ν`. -/
theorem map_le_monomialValuationFun (hν : ∀ a, ν (C a) = v a) (f : K[X]) :
    ν f ≤ monomialValuationFun v (ν X) f := by
  conv_lhs => rw [as_sum_support_C_mul_X_pow f]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [Valuation.map_mul, Valuation.map_pow, hν]
  exact le_monomialValuationFun f i

/-- The first step of the chain of MacLane: if `ν` extends `v`, then `[v; X, ν(X)] ≤ ν` in additive notation. The monomial valuation agrees with `ν` on the constants and at `X`. -/
theorem map_le_monomialValuation (hν : ∀ a, ν (C a) = v a) (f : K[X]) :
    ν f ≤ monomialValuation v (ν X) f :=
  map_le_monomialValuationFun hν f

end FirstStep

end Singularity
