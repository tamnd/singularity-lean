/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.MacLaneStep

/-!
# The chain of MacLane

Let `v` be a valuation on a field `K`, and let `ν` be a valuation on `K[X]` that extends `v`. This file iterates the step of MacLane (`Singularity/Valuation/MacLaneStep.lean`). It builds the chain `μ₀ ≤ μ₁ ≤ μ₂ ≤ ⋯ ≤ ν` of part 4 of Theorem 3.3.5 of Volume 3 of the handbook, with `μ₀ = [v; X, ν(X)]` and `μᵢ₊₁ = [μᵢ; φᵢ, ν(φᵢ)]`. It proves the properties of the chain, and the theorem of MacLane: if the value group of `ν` is discrete of rank 1, then `ν` is the limit of the chain.

The conventions are those of `Singularity/Valuation/KeyPolynomials.lean`. The valuations are multiplicative. Thus `μ ≤ ν` in the handbook is `∀ f, ν f ≤ μ f` here, a large additive value is a small value here, and `∞` is `0`.

## The chain

The step from `μ` is defined when `μ` agrees with `ν` on the constants and `μ ≤ ν` in additive notation (`MacLaneBelow ν μ`). If `μ ≠ ν`, then `φ = macLaneKey ν μ` is a monic polynomial of least degree with `μ(φ) < ν(φ)`, chosen with the axiom of choice, and `macLaneStep ν μ` is the augmentation `[μ; φ, ν(φ)]`. If `μ = ν`, then the step does not change `μ`. The chain is `macLaneChain v ν`, and its key polynomials are `macLaneChainKey v ν`. If `μᵢ = ν`, then the chain is constant from `i` on, and we say that the chain is finite and ends with `ν`.

## Hypotheses

The properties of the chain need only that `ν` extends `v`. The limit theorem needs that the value group of `ν` is discrete of rank 1. We state this as: for `c ≠ 0` and each `d`, the set of values of `ν` between `c` and `d` is finite (`hdisc`). This holds if `ν` takes values in `ℤₘ₀`. It does not hold for a discrete valuation of rank 2. The limit theorem does not need that `v` is discrete, or that `ν` has support `0`.

## The proof

* Let `μ' = [μ; φ, ν(φ)]` be the step from `μ ≠ ν`. Then `μ(f) < μ'(f)` if and only if `μ(f) < ν(f)`, in additive notation. Both conditions say that `φ` `μ`-divides `f` (`Singularity.muDvd_iff_map_lt`, once for `ν` and once for `μ'`). Thus the values `μᵢ(f)` increase strictly until they reach `ν(f)`, and then they stay at `ν(f)`.
* Each value `μᵢ(f)` is a value of `ν`. For `i ≥ 1` it is `μᵢ₋₁(aⱼ) + jν(φᵢ₋₁) = ν(aⱼφᵢ₋₁ʲ)` for a coefficient `aⱼ` of the `φᵢ₋₁`-expansion of `f`, because `μᵢ₋₁` and `ν` agree in degree less than the degree of `φᵢ₋₁`.
* If `ν(f) < ∞` and the values `μᵢ(f)` do not reach `ν(f)`, then they form an infinite strictly increasing sequence of values of `ν` between `μ₀(f)` and `ν(f)`. The discreteness forbids this.
* `μᵢ₊₁` agrees with `ν` in degree less than the degree of `φᵢ`, so `φᵢ₊₁` has degree at least the degree of `φᵢ`. If the degrees are equal, write `φᵢ₊₁ = φᵢ + a` with `deg a < deg φᵢ`. If `ν(a) < ν(φᵢ)` in additive notation, then `μᵢ₊₁(φᵢ₊₁) = ν(a) = ν(φᵢ₊₁)`, which is false. Thus `ν(φᵢ₊₁) > μᵢ₊₁(φᵢ₊₁) ≥ ν(φᵢ)`.

## Main results

* `Singularity.augmentedValuationFun_lt_iff_map_lt` and `Singularity.macLaneStep_lt_iff`: `μ(f) < μ'(f)` if and only if `μ(f) < ν(f)`, in additive notation.
* `Singularity.natDegree_le_of_map_lt_augmentedValuationFun` and `Singularity.map_lt_map_of_natDegree_eq`: the next key polynomial `ψ` has degree at least the degree of `φ`, and if the degrees are equal, then `ν(φ) < ν(ψ)` in additive notation. These two theorems do not mention the chain.
* `Singularity.eventually_le_of_succ_lt` and `Singularity.eventually_eq_of_succ_lt`: the limit principle for a sequence of valuations `μₙ ≤ μₙ₊₁ ≤ ν` with values in the value group of `ν` and with `μₙ(f) < μₙ₊₁(f)` whenever `μₙ(f) < ν(f)`.
* `Singularity.macLaneChain_succ_le`, `Singularity.le_macLaneChain`, `Singularity.macLaneChain_succ_lt_self`: `μᵢ ≤ μᵢ₊₁ ≤ ν`, and `μᵢ < μᵢ₊₁` at `φᵢ` if `μᵢ ≠ ν`.
* `Singularity.keyPolynomial_macLaneChainKey` and `Singularity.macLaneChain_succ_eq`: `φᵢ` is a key polynomial for `μᵢ`, and `μᵢ₊₁ = [μᵢ; φᵢ, ν(φᵢ)]`.
* `Singularity.natDegree_macLaneChainKey_le_succ`: the degrees of the `φᵢ` do not decrease.
* `Singularity.map_macLaneChainKey_succ_lt`: if `φᵢ` and `φᵢ₊₁` have the same degree, then `ν(φᵢ) < ν(φᵢ₊₁)` in additive notation.
* `Singularity.macLaneChain_succ_eq_of_map_eq_zero`: if `ν(φᵢ) = ∞`, then `μᵢ₊₁ = ν`.
* `Singularity.natDegree_macLaneChainKey_le_of_map_eq_zero`: if `ν(F) = ∞` for some `F ≠ 0`, then the degrees of the `φᵢ` are at most the degree of `F`.
* `Singularity.macLaneChain_eventually_eq` and `Singularity.macLaneChain_eventually_le`: the theorem of MacLane. If the value group of `ν` is discrete of rank 1, then for each `f` with `ν(f) < ∞` we have `μᵢ(f) = ν(f)` for all large `i`. For `f` with `ν(f) = ∞`, the values `μᵢ(f)` become larger than each given value.
* `Singularity.exists_macLaneChain_eq` and `Singularity.exists_macLaneChain_eq_of_map_eq_zero`: if the value group of `ν` is discrete of rank 1, the degrees of the `φᵢ` are bounded, and the finite values `ν(φᵢ)` are bounded, then the chain is finite and ends with `ν`. If `ν(F) = ∞` for some `F ≠ 0`, then the degrees are bounded.

## What the file does not prove

The chain need not be finite. Let `v` be the `p`-adic valuation on `ℚ`, let `s ∈ ℤₚ`, and let `ν(f) = v(f(s))`. If `s` is transcendental over `ℚ`, then `ν` has support `0`. If `s` is algebraic and not in `ℚ`, then `ν` has support `(F)` with `F` the minimal polynomial of `s`. In both cases the value group of `ν` is `ℤ`, and the chain can have infinitely many key polynomials `X - aᵢ` with `aᵢ ∈ ℚ` that converge to `s`. Then `ν` is only the limit of the chain. Thus the finiteness theorems need the bound on the values `ν(φᵢ)`. Also the key polynomial `φᵢ` is a choice. Another choice of `φᵢ` of the same degree gives another chain.

The file does not construct the limit augmentations of Vaquié, which are needed when the value group of `ν` is not discrete. It does not prove that `φᵢ₊₁` is unique up to `μᵢ`-equivalence, and it does not prove the claim on the graded algebra in part 3 of Theorem 3.3.5.

## References

* [Mac36] S. MacLane, A construction for absolute values in polynomial rings.
* [Vaq07] M. Vaquié, Extension d'une valuation.
-/

open Polynomial

namespace Singularity

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

section Augmentation

variable {μ ν : Valuation K[X] Γ₀} {φ ψ : K[X]}

/-- Let `ν f ≤ μ f` for each `f`, let `φ` be monic with `ν φ < μ φ`, and let `ν` and `μ` agree in degree less than the degree of `φ`. Then the augmentation `μ' = [μ; φ, ν φ]` changes the value of `f` if and only if `ν f < μ f`. In additive notation, `μ(f) < μ'(f)` if and only if `μ(f) < ν(f)`. Both conditions say that `φ` `μ`-divides `f`. -/
theorem augmentedValuationFun_lt_iff_map_lt (hle : ∀ f, ν f ≤ μ f) (hφ : φ.Monic)
    (hlt : ν φ < μ φ) (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f) (f : K[X]) :
    augmentedValuationFun μ φ (ν φ) f < μ f ↔ ν f < μ f := by
  have hkey := keyPolynomial_of_map_lt hle hφ hlt hlow
  rw [← augmentedValuation_apply hkey hlt.le]
  refine ⟨fun h => lt_of_le_of_lt (map_le_augmentedValuation_of_map_lt hle hφ hlt hlow f) h,
    fun h => ?_⟩
  refine map_lt_of_muDvd (augmentedValuation_le hkey hlt.le) ?_
    (muDvd_of_map_lt hle hφ hlt hlow h)
  rw [augmentedValuation_self]
  exact hlt

/-- Let `φ` be monic of positive degree, and let `ν` and `μ` agree in degree less than the degree of `φ`. If `ν ψ < [μ; φ, ν φ] ψ`, then the degree of `ψ` is at least the degree of `φ`. Thus the next key polynomial of the chain of MacLane has degree at least the degree of `φ`. -/
theorem natDegree_le_of_map_lt_augmentedValuationFun (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f)
    (hlt : ν ψ < augmentedValuationFun μ φ (ν φ) ψ) : φ.natDegree ≤ ψ.natDegree := by
  by_contra h
  rw [not_le] at h
  have hdeg := degree_lt_degree h
  rw [augmentedValuationFun_of_degree_lt hφ hd hdeg, ← hlow _ hdeg] at hlt
  exact lt_irrefl _ hlt

/-- Let `φ` be monic of positive degree, and let `ν` and `μ` agree in degree less than the degree of `φ`. Let `ψ` be monic of the same degree as `φ`, with `ν ψ < [μ; φ, ν φ] ψ`. Then `ν ψ < ν φ`. In additive notation, if the next key polynomial `ψ` of the chain of MacLane has the same degree as `φ`, then `ν(φ) < ν(ψ)`. -/
theorem map_lt_map_of_natDegree_eq (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f) (hψ : ψ.Monic)
    (hdeg : ψ.natDegree = φ.natDegree) (hlt : ν ψ < augmentedValuationFun μ φ (ν φ) ψ) :
    ν ψ < ν φ := by
  have hdeg' : ψ.degree = φ.degree := by
    rw [degree_eq_natDegree hψ.ne_zero, degree_eq_natDegree hφ.ne_zero, hdeg]
  have ha : (ψ - φ).degree < φ.degree := by
    rw [← hdeg']
    exact degree_sub_lt_left hdeg' hψ.ne_zero (by rw [hψ.leadingCoeff, hφ.leadingCoeff])
  have hsum : ψ = φ + (ψ - φ) := by ring
  have hle : augmentedValuationFun μ φ (ν φ) ψ ≤ max (ν φ) (ν (ψ - φ)) := by
    conv_lhs => rw [hsum]
    refine (augmentedValuationFun_add_le_max hφ hd _ _).trans (le_of_eq ?_)
    rw [augmentedValuationFun_self hφ hd, augmentedValuationFun_of_degree_lt hφ hd ha,
      hlow _ ha]
  rcases lt_or_ge (ν φ) (ν (ψ - φ)) with h | h
  · exfalso
    have e : ν ψ = ν (ψ - φ) := by
      rw [hsum, Valuation.map_add_eq_of_lt_right _ h, ← hsum]
    rw [max_eq_right h.le, ← e] at hle
    exact absurd hlt (not_lt.2 hle)
  · rw [max_eq_left h] at hle
    exact lt_of_lt_of_le hlt hle

end Augmentation

section Sequence

variable {ν : Valuation K[X] Γ₀}

/-- A strictly decreasing sequence of values of `ν` that is bounded below by `c ≠ 0` does not exist, if the value group of `ν` is discrete of rank 1. -/
theorem false_of_strictAnti
    (hdisc : ∀ c d : Γ₀, c ≠ 0 → (Set.Icc c d ∩ Set.range ν).Finite) {s : ℕ → Γ₀}
    (hs : StrictAnti s) {c : Γ₀} (hc : c ≠ 0) (hcs : ∀ n, c ≤ s n)
    (hr : ∀ n, s n ∈ Set.range ν) : False := by
  have hfin := (hdisc c (s 0) hc).subset (Set.range_subset_iff.2 fun n =>
    ⟨⟨hcs n, hs.antitone (Nat.zero_le n)⟩, hr n⟩)
  exact Set.infinite_range_of_injective hs.injective hfin

/-- The limit principle of MacLane. Let the value group of `ν` be discrete of rank 1: for `c ≠ 0` and each `d`, only finitely many values of `ν` lie between `c` and `d`. Let `μₙ` be valuations whose values are values of `ν`, with `μₙ ≤ μₙ₊₁` in additive notation, and with `μₙ(f) < μₙ₊₁(f)` whenever `μₙ(f) < ν(f)`. Let `c ≠ 0` with `ν f ≤ c`. Then `μₙ f ≤ c` for all large `n`. -/
theorem eventually_le_of_succ_lt
    (hdisc : ∀ c d : Γ₀, c ≠ 0 → (Set.Icc c d ∩ Set.range ν).Finite)
    {μ : ℕ → Valuation K[X] Γ₀} (hsucc : ∀ n f, μ (n + 1) f ≤ μ n f)
    (hlt : ∀ n f, ν f < μ n f → μ (n + 1) f < μ n f) (hr : ∀ n f, μ n f ∈ Set.range ν)
    (f : K[X]) {c : Γ₀} (hc : c ≠ 0) (hfc : ν f ≤ c) :
    ∃ N, ∀ n, N ≤ n → μ n f ≤ c := by
  have hanti : Antitone fun n => μ n f := antitone_nat_of_succ_le fun n => hsucc n f
  by_contra hcon
  push Not at hcon
  have hall : ∀ n, c < μ n f := fun n => by
    obtain ⟨m, hm, hlt'⟩ := hcon n
    exact lt_of_lt_of_le hlt' (hanti hm)
  exact false_of_strictAnti hdisc (s := fun n => μ n f)
    (strictAnti_nat_of_succ_lt fun n => hlt n f (lt_of_le_of_lt hfc (hall n))) hc
    (fun n => (hall n).le) (fun n => hr n f)

/-- The limit principle of MacLane. Let the value group of `ν` be discrete of rank 1. Let `μₙ` be valuations whose values are values of `ν`, with `μₙ ≤ μₙ₊₁ ≤ ν` in additive notation, and with `μₙ(f) < μₙ₊₁(f)` whenever `μₙ(f) < ν(f)`. Then for each `f` with `ν f ≠ 0`, we have `μₙ f = ν f` for all large `n`. -/
theorem eventually_eq_of_succ_lt
    (hdisc : ∀ c d : Γ₀, c ≠ 0 → (Set.Icc c d ∩ Set.range ν).Finite)
    {μ : ℕ → Valuation K[X] Γ₀} (hle : ∀ n f, ν f ≤ μ n f) (hsucc : ∀ n f, μ (n + 1) f ≤ μ n f)
    (hlt : ∀ n f, ν f < μ n f → μ (n + 1) f < μ n f) (hr : ∀ n f, μ n f ∈ Set.range ν)
    (f : K[X]) (hf : ν f ≠ 0) :
    ∃ N, ∀ n, N ≤ n → μ n f = ν f := by
  obtain ⟨N, hN⟩ := eventually_le_of_succ_lt hdisc hsucc hlt hr f hf le_rfl
  exact ⟨N, fun n hn => le_antisymm (hN n hn) (hle n f)⟩

end Sequence

section Step

/-- The valuation `μ` agrees with `ν` on the constants, and `μ ≤ ν` in the additive notation of the handbook. In multiplicative notation, `ν f ≤ μ f` for each `f`. -/
def MacLaneBelow (ν μ : Valuation K[X] Γ₀) : Prop :=
  (∀ c, ν (C c) = μ (C c)) ∧ ∀ f, ν f ≤ μ f

open Classical in
/-- The key polynomial of the step of MacLane from `μ` towards `ν`. If `MacLaneBelow ν μ` and `μ ≠ ν`, then it is a monic polynomial `φ` of least degree with `ν φ < μ φ`, chosen with the axiom of choice. Otherwise it is `X`, and it plays no role. -/
noncomputable def macLaneKey (ν μ : Valuation K[X] Γ₀) : K[X] :=
  if h : MacLaneBelow ν μ ∧ μ ≠ ν then Classical.choose (exists_monic_map_lt h.1.1 h.1.2 h.2)
  else X

variable {ν μ : Valuation K[X] Γ₀}

/-- The key polynomial of the step is monic, `ν φ < μ φ`, and `ν` and `μ` agree in degree less than the degree of `φ`. -/
theorem macLaneKey_spec (h : MacLaneBelow ν μ) (hne : μ ≠ ν) :
    (macLaneKey ν μ).Monic ∧ ν (macLaneKey ν μ) < μ (macLaneKey ν μ) ∧
      ∀ f : K[X], f.degree < (macLaneKey ν μ).degree → ν f = μ f := by
  have e : macLaneKey ν μ = Classical.choose (exists_monic_map_lt h.1 h.2 hne) :=
    dite_eq_left ⟨h, hne⟩
  rw [e]
  exact Classical.choose_spec (exists_monic_map_lt h.1 h.2 hne)

/-- The key polynomial of the step from `μ` is a key polynomial for `μ`. -/
theorem keyPolynomial_macLaneKey (h : MacLaneBelow ν μ) (hne : μ ≠ ν) :
    KeyPolynomial μ (macLaneKey ν μ) :=
  keyPolynomial_of_map_lt h.2 (macLaneKey_spec h hne).1 (macLaneKey_spec h hne).2.1
    (macLaneKey_spec h hne).2.2

variable (ν μ) in
open Classical in
/-- The step of MacLane from `μ` towards `ν`. If `MacLaneBelow ν μ` and `μ ≠ ν`, then it is the augmentation `[μ; φ, ν φ]` with `φ = macLaneKey ν μ`. Otherwise it is `μ`. -/
noncomputable def macLaneStep : Valuation K[X] Γ₀ :=
  if h : MacLaneBelow ν μ ∧ μ ≠ ν then
    augmentedValuation μ (macLaneKey ν μ) (ν (macLaneKey ν μ))
      (keyPolynomial_macLaneKey h.1 h.2) (macLaneKey_spec h.1 h.2).2.1.le
  else μ

/-- If `μ ≠ ν`, then the step is the augmentation `[μ; φ, ν φ]`. -/
theorem macLaneStep_eq (h : MacLaneBelow ν μ) (hne : μ ≠ ν) :
    macLaneStep ν μ = augmentedValuation μ (macLaneKey ν μ) (ν (macLaneKey ν μ))
      (keyPolynomial_macLaneKey h hne) (macLaneKey_spec h hne).2.1.le :=
  dite_eq_left ⟨h, hne⟩

/-- If `μ ≠ ν`, then the value of the step is the augmented value. -/
theorem macLaneStep_apply (h : MacLaneBelow ν μ) (hne : μ ≠ ν) (f : K[X]) :
    macLaneStep ν μ f = augmentedValuationFun μ (macLaneKey ν μ) (ν (macLaneKey ν μ)) f := by
  rw [macLaneStep_eq h hne, augmentedValuation_apply]

/-- The step from `ν` is `ν`. -/
theorem macLaneStep_self : macLaneStep ν ν = ν :=
  dite_eq_right fun h => h.2 rfl

/-- The step does not decrease the values in additive notation: `μ ≤ μ'`. -/
theorem macLaneStep_le (f : K[X]) : macLaneStep ν μ f ≤ μ f := by
  by_cases h : MacLaneBelow ν μ ∧ μ ≠ ν
  · rw [macLaneStep_eq h.1 h.2]
    exact augmentedValuation_le _ _ f
  · rw [macLaneStep, dite_eq_right h]

/-- The step keeps the condition `MacLaneBelow ν`: the step agrees with `ν` on the constants, and `μ' ≤ ν` in additive notation. -/
theorem macLaneBelow_macLaneStep (h : MacLaneBelow ν μ) : MacLaneBelow ν (macLaneStep ν μ) := by
  by_cases hne : μ = ν
  · rw [hne, macLaneStep_self]
    rw [hne] at h
    exact h
  refine ⟨fun c => ?_, fun f => ?_⟩
  · rw [macLaneStep_eq h hne, augmentedValuation_C, h.1]
  · rw [macLaneStep_eq h hne]
    exact map_le_augmentedValuation_of_map_lt h.2 (macLaneKey_spec h hne).1
      (macLaneKey_spec h hne).2.1 (macLaneKey_spec h hne).2.2 f

/-- If `μ ≠ ν`, then the step sends the key polynomial `φ` to `ν φ`. -/
theorem macLaneStep_key (h : MacLaneBelow ν μ) (hne : μ ≠ ν) :
    macLaneStep ν μ (macLaneKey ν μ) = ν (macLaneKey ν μ) := by
  rw [macLaneStep_eq h hne, augmentedValuation_self]

/-- If `μ ≠ ν`, then the step agrees with `ν` in degree less than the degree of the key polynomial. -/
theorem macLaneStep_of_degree_lt (h : MacLaneBelow ν μ) (hne : μ ≠ ν) {f : K[X]}
    (hf : f.degree < (macLaneKey ν μ).degree) : macLaneStep ν μ f = ν f := by
  have hs := macLaneKey_spec h hne
  rw [macLaneStep_eq h hne]
  exact augmentedValuation_eq_of_map_lt h.2 hs.1 hs.2.1 hs.2.2 hf

/-- The step changes the value of `f` if and only if `μ f ≠ ν f`. In additive notation, `μ(f) < μ'(f)` if and only if `μ(f) < ν(f)`. Both conditions say that the key polynomial `μ`-divides `f`. -/
theorem macLaneStep_lt_iff (h : MacLaneBelow ν μ) (f : K[X]) :
    macLaneStep ν μ f < μ f ↔ ν f < μ f := by
  by_cases hne : μ = ν
  · subst hne
    rw [macLaneStep_self]
  have hs := macLaneKey_spec h hne
  rw [macLaneStep_apply h hne]
  exact augmentedValuationFun_lt_iff_map_lt h.2 hs.1 hs.2.1 hs.2.2 f

/-- Each value of the step is a value of `ν`. -/
theorem exists_eq_macLaneStep (h : MacLaneBelow ν μ) (f : K[X]) :
    ∃ g, macLaneStep ν μ f = ν g := by
  by_cases hne : μ = ν
  · subst hne
    exact ⟨f, by rw [macLaneStep_self]⟩
  have hs := macLaneKey_spec h hne
  obtain ⟨j, hj⟩ := exists_eq_augmentedValuationFun (μ := μ) (φ := macLaneKey ν μ)
    (γ := ν (macLaneKey ν μ)) f
  refine ⟨expansionCoeff (macLaneKey ν μ) f j * macLaneKey ν μ ^ j, ?_⟩
  rw [macLaneStep_apply h hne, ← hj, Valuation.map_mul, Valuation.map_pow,
    hs.2.2 _ (degree_expansionCoeff_lt hs.1 f j)]

end Step

section Chain

variable (v : Valuation K Γ₀) (ν : Valuation K[X] Γ₀)

/-- The chain of MacLane for `ν` (part 4 of Theorem 3.3.5 of Volume 3 of the handbook). It starts with the monomial valuation `μ₀ = [v; X, ν X]`, and `μᵢ₊₁` is the step of MacLane from `μᵢ` towards `ν`. -/
noncomputable def macLaneChain : ℕ → Valuation K[X] Γ₀
  | 0 => monomialValuation v (ν X)
  | n + 1 => macLaneStep ν (macLaneChain n)

/-- The key polynomial `φᵢ` of the chain of MacLane. If `μᵢ ≠ ν`, then `μᵢ₊₁ = [μᵢ; φᵢ, ν φᵢ]`. -/
noncomputable def macLaneChainKey (n : ℕ) : K[X] :=
  macLaneKey ν (macLaneChain v ν n)

variable {v ν}

@[simp]
theorem macLaneChain_zero : macLaneChain v ν 0 = monomialValuation v (ν X) :=
  rfl

theorem macLaneChain_succ (n : ℕ) :
    macLaneChain v ν (n + 1) = macLaneStep ν (macLaneChain v ν n) :=
  rfl

variable (hν : ∀ a, ν (C a) = v a)
include hν

/-- Each valuation of the chain agrees with `ν` on the constants, and it is at most `ν` in additive notation. -/
theorem macLaneBelow_macLaneChain (n : ℕ) : MacLaneBelow ν (macLaneChain v ν n) := by
  induction n with
  | zero =>
    refine ⟨fun c => ?_, map_le_monomialValuation hν⟩
    rw [macLaneChain_zero, monomialValuation_C, hν]
  | succ n ih => exact macLaneBelow_macLaneStep ih

/-- The chain is at most `ν` in additive notation: `μᵢ ≤ ν`. -/
theorem le_macLaneChain (n : ℕ) (f : K[X]) : ν f ≤ macLaneChain v ν n f :=
  (macLaneBelow_macLaneChain hν n).2 f

omit hν in
/-- The chain increases in additive notation: `μᵢ ≤ μᵢ₊₁`. -/
theorem macLaneChain_succ_le (n : ℕ) (f : K[X]) :
    macLaneChain v ν (n + 1) f ≤ macLaneChain v ν n f :=
  macLaneStep_le f

omit hν in
/-- The chain increases in additive notation: `μₙ ≤ μₘ` for `n ≤ m`. -/
theorem macLaneChain_antitone (f : K[X]) : Antitone fun n => macLaneChain v ν n f :=
  antitone_nat_of_succ_le fun n => macLaneChain_succ_le n f

omit hν in
/-- If the chain reaches `ν`, then it stays at `ν`. -/
theorem macLaneChain_eq_of_le {n m : ℕ} (hnm : n ≤ m) (h : macLaneChain v ν n = ν) :
    macLaneChain v ν m = ν := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => rw [macLaneChain_succ, ih, macLaneStep_self]

/-- If `μᵢ ≠ ν`, then `φᵢ` is a key polynomial for `μᵢ`. -/
theorem keyPolynomial_macLaneChainKey {n : ℕ} (hne : macLaneChain v ν n ≠ ν) :
    KeyPolynomial (macLaneChain v ν n) (macLaneChainKey v ν n) :=
  keyPolynomial_macLaneKey (macLaneBelow_macLaneChain hν n) hne

/-- If `μᵢ ≠ ν`, then `μᵢ(φᵢ) < ν(φᵢ)` in additive notation. -/
theorem map_macLaneChainKey_lt {n : ℕ} (hne : macLaneChain v ν n ≠ ν) :
    ν (macLaneChainKey v ν n) < macLaneChain v ν n (macLaneChainKey v ν n) :=
  (macLaneKey_spec (macLaneBelow_macLaneChain hν n) hne).2.1

/-- If `μᵢ ≠ ν`, then `μᵢ` agrees with `ν` in degree less than the degree of `φᵢ`. -/
theorem macLaneChain_of_degree_lt {n : ℕ} (hne : macLaneChain v ν n ≠ ν) {f : K[X]}
    (hf : f.degree < (macLaneChainKey v ν n).degree) : macLaneChain v ν n f = ν f :=
  ((macLaneKey_spec (macLaneBelow_macLaneChain hν n) hne).2.2 f hf).symm

/-- If `μᵢ ≠ ν`, then `μᵢ₊₁` is the augmentation `[μᵢ; φᵢ, ν φᵢ]`. -/
theorem macLaneChain_succ_eq {n : ℕ} (hne : macLaneChain v ν n ≠ ν) :
    macLaneChain v ν (n + 1) = augmentedValuation (macLaneChain v ν n) (macLaneChainKey v ν n)
      (ν (macLaneChainKey v ν n)) (keyPolynomial_macLaneChainKey hν hne)
      (map_macLaneChainKey_lt hν hne).le :=
  macLaneStep_eq (macLaneBelow_macLaneChain hν n) hne

/-- If `μᵢ ≠ ν`, then `μᵢ₊₁(φᵢ) = ν(φᵢ)`. -/
theorem macLaneChain_succ_key {n : ℕ} (hne : macLaneChain v ν n ≠ ν) :
    macLaneChain v ν (n + 1) (macLaneChainKey v ν n) = ν (macLaneChainKey v ν n) :=
  macLaneStep_key (macLaneBelow_macLaneChain hν n) hne

/-- If `μᵢ ≠ ν`, then `μᵢ < μᵢ₊₁` in additive notation: the two valuations differ at `φᵢ`. -/
theorem macLaneChain_succ_lt_self {n : ℕ} (hne : macLaneChain v ν n ≠ ν) :
    macLaneChain v ν (n + 1) (macLaneChainKey v ν n) <
      macLaneChain v ν n (macLaneChainKey v ν n) := by
  rw [macLaneChain_succ_key hν hne]
  exact map_macLaneChainKey_lt hν hne

/-- If `μᵢ ≠ ν`, then `μᵢ₊₁` agrees with `ν` in degree less than the degree of `φᵢ`. -/
theorem macLaneChain_succ_of_degree_lt {n : ℕ} (hne : macLaneChain v ν n ≠ ν) {f : K[X]}
    (hf : f.degree < (macLaneChainKey v ν n).degree) : macLaneChain v ν (n + 1) f = ν f :=
  macLaneStep_of_degree_lt (macLaneBelow_macLaneChain hν n) hne hf

/-- The values of the chain at `f` increase strictly until they reach `ν f`. In additive notation, `μᵢ(f) < μᵢ₊₁(f)` if and only if `μᵢ(f) < ν(f)`. -/
theorem macLaneChain_succ_lt_iff (n : ℕ) (f : K[X]) :
    macLaneChain v ν (n + 1) f < macLaneChain v ν n f ↔ ν f < macLaneChain v ν n f :=
  macLaneStep_lt_iff (macLaneBelow_macLaneChain hν n) f

/-- Each value of the chain is a value of `ν`. -/
theorem exists_eq_macLaneChain (n : ℕ) (f : K[X]) : ∃ g, macLaneChain v ν n f = ν g := by
  cases n with
  | zero =>
    rw [macLaneChain_zero, monomialValuation_apply]
    by_cases h0 : monomialValuationFun v (ν X) f = 0
    · exact ⟨0, by rw [h0, Valuation.map_zero]⟩
    obtain ⟨i, hi⟩ := exists_eq_monomialValuationFun h0
    exact ⟨C (f.coeff i) * X ^ i, by rw [Valuation.map_mul, Valuation.map_pow, hν, hi]⟩
  | succ n => exact exists_eq_macLaneStep (macLaneBelow_macLaneChain hν n) f

/-- The degrees of the key polynomials do not decrease. If `μᵢ₊₁ ≠ ν`, then the degree of `φᵢ` is at most the degree of `φᵢ₊₁`. -/
theorem natDegree_macLaneChainKey_le_succ {n : ℕ} (hne : macLaneChain v ν (n + 1) ≠ ν) :
    (macLaneChainKey v ν n).natDegree ≤ (macLaneChainKey v ν (n + 1)).natDegree := by
  have hne' : macLaneChain v ν n ≠ ν := fun h => hne (macLaneChain_eq_of_le n.le_succ h)
  by_contra hlt
  rw [not_le] at hlt
  have e := macLaneChain_succ_of_degree_lt hν hne' (degree_lt_degree hlt)
  exact ne_of_lt (map_macLaneChainKey_lt hν hne) e.symm

/-- Let `φᵢ` and `φᵢ₊₁` have the same degree, and let `μᵢ₊₁ ≠ ν`. Then `ν(φᵢ) < ν(φᵢ₊₁)` in additive notation. -/
theorem map_macLaneChainKey_succ_lt {n : ℕ} (hne : macLaneChain v ν (n + 1) ≠ ν)
    (hdeg : (macLaneChainKey v ν (n + 1)).natDegree = (macLaneChainKey v ν n).natDegree) :
    ν (macLaneChainKey v ν (n + 1)) < ν (macLaneChainKey v ν n) := by
  have hne' : macLaneChain v ν n ≠ ν := fun h => hne (macLaneChain_eq_of_le n.le_succ h)
  have hφ := keyPolynomial_macLaneChainKey hν hne'
  have hlt := map_macLaneChainKey_lt hν hne
  rw [macLaneChain_succ, macLaneStep_apply (macLaneBelow_macLaneChain hν n) hne'] at hlt
  exact map_lt_map_of_natDegree_eq hφ.monic hφ.natDegree_pos
    (macLaneKey_spec (macLaneBelow_macLaneChain hν n) hne').2.2
    (keyPolynomial_macLaneChainKey hν hne).monic hdeg hlt

/-- If `μᵢ ≠ ν` and `ν(φᵢ) = ∞`, then `μᵢ₊₁ = [μᵢ; φᵢ, ∞]` is `ν`. Thus the chain is finite and ends with `ν`. -/
theorem macLaneChain_succ_eq_of_map_eq_zero {n : ℕ} (hne : macLaneChain v ν n ≠ ν)
    (h0 : ν (macLaneChainKey v ν n) = 0) : macLaneChain v ν (n + 1) = ν := by
  have hφ := keyPolynomial_macLaneChainKey hν hne
  refine Valuation.ext fun f => ?_
  have hsupp : macLaneChainKey v ν n * (f /ₘ macLaneChainKey v ν n) ∈ Valuation.supp ν := by
    rw [Valuation.mem_supp_iff, Valuation.map_mul, h0, zero_mul]
  rw [macLaneChain_succ, macLaneStep_apply (macLaneBelow_macLaneChain hν n) hne]
  change augmentedValuationFun (macLaneChain v ν n) (macLaneChainKey v ν n)
    (ν (macLaneChainKey v ν n)) f = ν f
  rw [h0, augmentedValuationFun_zero_right hφ.monic hφ.natDegree_pos,
    macLaneChain_of_degree_lt hν hne (degree_modByMonic_lt f hφ.monic),
    ← Valuation.map_add_supp ν _ hsupp, modByMonic_add_div f (macLaneChainKey v ν n)]

/-- Let `ν(F) = ∞` for some `F ≠ 0`. If `μᵢ ≠ ν`, then the degree of `φᵢ` is at most the degree of `F`. -/
theorem natDegree_macLaneChainKey_le_of_map_eq_zero {F : K[X]} (hF : F ≠ 0) (hF0 : ν F = 0)
    {n : ℕ} (hne : macLaneChain v ν n ≠ ν) :
    (macLaneChainKey v ν n).natDegree ≤ F.natDegree := by
  by_contra hlt
  rw [not_le] at hlt
  apply hne
  set G := F * C F.leadingCoeff⁻¹ with hGdef
  have hG : G.Monic := monic_mul_leadingCoeff_inv hF
  have hGdeg : G.degree < (macLaneChainKey v ν n).degree := by
    refine degree_lt_degree ?_
    rw [hGdef, natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.2 hF))]
    exact hlt
  have hG0 : ν G = 0 := by rw [hGdef, Valuation.map_mul, hF0, zero_mul]
  have hμG : macLaneChain v ν n G = 0 := by rw [macLaneChain_of_degree_lt hν hne hGdeg, hG0]
  refine Valuation.ext fun f => ?_
  have hs1 : G * (f /ₘ G) ∈ Valuation.supp (macLaneChain v ν n) := by
    rw [Valuation.mem_supp_iff, Valuation.map_mul, hμG, zero_mul]
  have hs2 : G * (f /ₘ G) ∈ Valuation.supp ν := by
    rw [Valuation.mem_supp_iff, Valuation.map_mul, hG0, zero_mul]
  have hr : (f %ₘ G).degree < (macLaneChainKey v ν n).degree :=
    (degree_modByMonic_lt f hG).trans hGdeg
  rw [← modByMonic_add_div f G, Valuation.map_add_supp _ _ hs1, Valuation.map_add_supp _ _ hs2,
    macLaneChain_of_degree_lt hν hne hr]

end Chain

section Limit

variable {v : Valuation K Γ₀} {ν : Valuation K[X] Γ₀}

variable (hν : ∀ a, ν (C a) = v a)
  (hdisc : ∀ c d : Γ₀, c ≠ 0 → (Set.Icc c d ∩ Set.range ν).Finite)
include hν hdisc

/-- Let the value group of `ν` be discrete of rank 1. Let `c ≠ 0` with `ν f ≤ c`. Then `μᵢ f ≤ c` for all large `i`. In additive notation, `μᵢ(f) ≥ c` for all large `i` if `c` is finite and `ν(f) ≥ c`. -/
theorem macLaneChain_eventually_le (f : K[X]) {c : Γ₀} (hc : c ≠ 0) (hfc : ν f ≤ c) :
    ∃ N, ∀ n, N ≤ n → macLaneChain v ν n f ≤ c :=
  eventually_le_of_succ_lt hdisc (macLaneChain_succ_le · ·)
    (fun n f => (macLaneChain_succ_lt_iff hν n f).2)
    (fun n f => (exists_eq_macLaneChain hν n f).imp fun _ hg => hg.symm) f hc hfc

/-- The theorem of MacLane (part 4 of Theorem 3.3.5 of Volume 3 of the handbook, for a discrete valuation of rank 1). Let `ν` be a valuation on `K[X]` that extends `v`, and let the value group of `ν` be discrete of rank 1: for `c ≠ 0` and each `d`, only finitely many values of `ν` lie between `c` and `d`. Then `ν` is the limit of the chain of MacLane: for each `f` with `ν f ≠ 0`, the value `μᵢ f` is `ν f` for all large `i`. For `f` with `ν f = 0`, the values `μᵢ f` tend to `0` by `macLaneChain_eventually_le`. -/
theorem macLaneChain_eventually_eq (f : K[X]) (hf : ν f ≠ 0) :
    ∃ N, ∀ n, N ≤ n → macLaneChain v ν n f = ν f :=
  eventually_eq_of_succ_lt hdisc (le_macLaneChain hν) (macLaneChain_succ_le · ·)
    (fun n f => (macLaneChain_succ_lt_iff hν n f).2)
    (fun n f => (exists_eq_macLaneChain hν n f).imp fun _ hg => hg.symm) f hf

/-- Let the value group of `ν` be discrete of rank 1. Let the degrees of the key polynomials `φᵢ` be at most `d`, and let `c ≠ 0` with `c ≤ ν φᵢ` for each `i` with `ν φᵢ ≠ 0`. In additive notation, the finite values `ν(φᵢ)` are at most `c`. Then the chain is finite and ends with `ν`: there is an `i` with `μᵢ = ν`. -/
theorem exists_macLaneChain_eq (d : ℕ) {c : Γ₀} (hc : c ≠ 0)
    (hdeg : ∀ n, macLaneChain v ν n ≠ ν → (macLaneChainKey v ν n).natDegree ≤ d)
    (hval : ∀ n, macLaneChain v ν n ≠ ν → ν (macLaneChainKey v ν n) ≠ 0 →
      c ≤ ν (macLaneChainKey v ν n)) :
    ∃ n, macLaneChain v ν n = ν := by
  by_contra hcon
  push Not at hcon
  set D := fun n => (macLaneChainKey v ν n).natDegree with hD
  have hmono : Monotone D :=
    monotone_nat_of_le_succ fun n => natDegree_macLaneChainKey_le_succ hν (hcon (n + 1))
  have hbdd : BddAbove (Set.range D) := ⟨d, Set.forall_mem_range.2 fun n => hdeg n (hcon n)⟩
  obtain ⟨N, hN⟩ := Nat.sSup_mem (Set.range_nonempty D) hbdd
  have hconst : ∀ n, N ≤ n → D n = D N := fun n hn =>
    le_antisymm (hN ▸ le_csSup hbdd ⟨n, rfl⟩) (hmono hn)
  have h0 : ∀ n, ν (macLaneChainKey v ν n) ≠ 0 := fun n h =>
    hcon (n + 1) (macLaneChain_succ_eq_of_map_eq_zero hν (hcon n) h)
  refine false_of_strictAnti hdisc (s := fun k => ν (macLaneChainKey v ν (N + k)))
    (strictAnti_nat_of_succ_lt fun k => ?_) hc (fun k => hval _ (hcon _) (h0 _))
    (fun k => ⟨_, rfl⟩)
  refine map_macLaneChainKey_succ_lt hν (hcon (N + k + 1)) ?_
  change D (N + k + 1) = D (N + k)
  rw [hconst (N + k + 1) (by omega), hconst (N + k) (by omega)]

/-- Let the value group of `ν` be discrete of rank 1, and let `ν F = 0` for some `F ≠ 0`. This is the case of an algebraic element. Let `c ≠ 0` with `c ≤ ν φᵢ` for each `i` with `ν φᵢ ≠ 0`. Then the chain is finite and ends with `ν`. The degrees of the `φᵢ` are at most the degree of `F`. -/
theorem exists_macLaneChain_eq_of_map_eq_zero {F : K[X]} (hF : F ≠ 0) (hF0 : ν F = 0)
    {c : Γ₀} (hc : c ≠ 0)
    (hval : ∀ n, macLaneChain v ν n ≠ ν → ν (macLaneChainKey v ν n) ≠ 0 →
      c ≤ ν (macLaneChainKey v ν n)) :
    ∃ n, macLaneChain v ν n = ν :=
  exists_macLaneChain_eq hν hdisc F.natDegree hc
    (fun _ hne => natDegree_macLaneChainKey_le_of_map_eq_zero hν hF hF0 hne) hval

end Limit

end Singularity
