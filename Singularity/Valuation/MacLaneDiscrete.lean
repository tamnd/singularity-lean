/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Data.Int.Interval
import Singularity.Valuation.LimitKeyPolynomial

/-!
# Part 4 of MacLane-Vaquié for a discrete valuation of rank 1

Let `v` be a valuation on a field `K`, and let `ν` be a valuation on `K[X]` that extends `v`. Assume that the values of `ν` are discrete of rank 1: for `c ≠ 0` and each `d`, only finitely many values of `ν` lie between `c` and `d` (`hdisc`). This holds if `ν` takes values in `ℤᵐ⁰`, that is, if the additive values are in `ℤ ∪ {∞}` (`Singularity.finite_Icc_inter_range_int`). This file proves the form of part 4 of Theorem 3.3.5 of Volume 3 of the handbook that MacLane proved for this case [Mac36]. The chain of ordinary augmentations is finite and ends with `ν`, or `ν` is its limit, and the limit augmentations of Vaquié [Vaq07] give nothing new.

`Singularity/Valuation/MacLaneChain.lean` proves that `ν` is the limit of the chain of MacLane (`Singularity.macLaneChain_eventually_eq`). This file adds three results.

1. The values of `ν` on the key polynomials of the chain. Let the chain be infinite, and let the degrees of the key polynomials `φᵢ` be bounded. This is the case if `ν` has a nonzero support. Then `ν(φᵢ)` tends to `∞` in additive notation. This is the precise point where the discreteness enters: from some index on, the `φᵢ` have one degree, and then the values `ν(φᵢ)` increase strictly in additive notation. A strictly increasing sequence of values of `ν` is not bounded.
2. Continuous families. Let `μᵢ = [μ; φᵢ, γᵢ]` be a continuous family of augmentations of one degree (`Singularity.ContinuousFamily`), with `μᵢ ≤ ν` for each `i` in additive notation, with `ν = μ` in degree less than the degree of the family, and with values `γᵢ` that are values of `ν`. In the construction of Vaquié, `γᵢ = ν(φᵢ)`. Then each `f` with `ν(f) ≠ ∞` is stable, and `μᵢ(f) = ν(f)` for `i` large. So `ν` is the limit of the family on these polynomials. The values `γᵢ` tend to `∞`. If `ν` has support `0`, then each polynomial is stable, and the family has no limit key polynomial.
3. The limit step. Let `φ` be a limit key polynomial for such a family. Then `ν(φ) = ∞`. The only value `γ` that is admissible for the limit augmentation `[μ_∞; φ, γ]` is `γ = ∞`, and this limit augmentation is `ν`. Thus a limit step can only be the last step, and it ends with `ν`.

The conventions are those of `Singularity/Valuation/KeyPolynomials.lean`. The valuations are multiplicative. Thus `μ ≤ ν` in the handbook is `∀ f, ν f ≤ μ f` here, a large additive value is a small value here, and `∞` is `0`.

## The proof

* The discreteness is used through one lemma (`Singularity.false_of_strictAnti_of_noMaxOrder`). A family of values of `ν` that is strictly decreasing (in multiplicative notation), indexed by a nonempty totally ordered set without a largest element, and bounded below by some `c ≠ 0`, does not exist. Such an index set contains a strictly increasing sequence, and the values along this sequence are infinitely many values of `ν` between `c` and the first value. For the chain, this is `Singularity.false_of_strictAnti`.
* For the chain, the degrees of the `φᵢ` do not decrease (`Singularity.natDegree_macLaneChainKey_le_succ`). If they are bounded, they are constant from some `N` on. Then `ν(φᵢ₊₁) < ν(φᵢ)` for `i ≥ N` (`Singularity.map_macLaneChainKey_succ_lt`). If `c ≤ ν(φᵢ)` for infinitely many `i`, then `c ≤ ν(φᵢ)` for each `i ≥ N`, which the lemma forbids.
* For a continuous family, each value `μᵢ(f)` is a value `μ(aⱼ) γᵢ ^ j` of one term of the `φᵢ`-expansion. Since `μ = ν` in degree less than the degree of `φᵢ` and `γᵢ = ν(g)` for some `g`, this is `ν(aⱼ gʲ)`. An unstable `f` has values `μᵢ(f)` that decrease strictly (`Singularity.ContinuousFamily.val_lt_val_of_not_isStable`). They are bounded below by `ν(f)`. So the lemma gives `ν(f) = 0`. The values `γᵢ` decrease strictly by the definition of a continuous family.
* Let `φ` be a limit key polynomial. It is unstable, so `ν(φ) = 0`. If `γ ≤ μᵢ(φ)` for each `i` and `γ ≠ 0`, then the strictly decreasing values `μᵢ(φ)` are bounded below by `γ`, a contradiction. So `γ = 0`. The limit augmentation `[μ_∞; φ, 0]` sends `f` to `μ_∞(r)` for the remainder `r` of `f` modulo `φ`. The remainder has degree less than the degree of `φ`, so it is stable and `μ_∞(r) = ν(r)` (`Singularity.ContinuousFamily.stableValue_eq_of_isStable`). Finally `ν(r) = ν(f)`, because `f - r` is a multiple of `φ` and `ν(φ) = 0`.

## Main results

* `Singularity.false_of_strictAnti_of_noMaxOrder`: the use of the discreteness.
* `Singularity.finite_Icc_inter_range_int`: the hypothesis `hdisc` holds for a valuation with values in `ℤᵐ⁰`.
* `Singularity.macLaneChain_eventually_eq_int`: the theorem of MacLane for a valuation `ν` with values in `ℤᵐ⁰`.
* `Singularity.macLaneChainKey_eventually_lt` and `Singularity.macLaneChainKey_eventually_lt_of_map_eq_zero`: for an infinite chain with bounded degrees, in particular if `ν` has a nonzero support, `ν(φᵢ) → ∞` in additive notation.
* `Singularity.ContinuousFamily.isStable_of_map_ne_zero` and `Singularity.ContinuousFamily.eventually_val_eq_of_map_ne_zero`: for a continuous family below `ν`, each `f` with `ν(f) ≠ ∞` is stable, and `μᵢ(f) = ν(f)` for `i` large.
* `Singularity.ContinuousFamily.eventually_value_lt`: the values `γᵢ` tend to `∞` in additive notation.
* `Singularity.ContinuousFamily.isStable_of_supp_eq_bot`, `Singularity.ContinuousFamily.stableValue_eq_of_supp_eq_bot` and `Singularity.ContinuousFamily.not_isLimitKeyPolynomial`: if `ν` has support `0`, then each polynomial is stable, `μ_∞ = ν`, and there is no limit key polynomial.
* `Singularity.ContinuousFamily.IsLimitKeyPolynomial.map_eq_zero`, `Singularity.ContinuousFamily.IsLimitKeyPolynomial.eq_zero_of_le`, `Singularity.ContinuousFamily.IsLimitKeyPolynomial.limitAugmentedValuationFun_eq_of_le` and `Singularity.ContinuousFamily.IsLimitKeyPolynomial.limitAugmentedValuation_eq`: a limit key polynomial has `ν(φ) = ∞`, the only admissible value is `γ = ∞`, and each limit augmentation of the family is `ν`.

## What the file does not prove

The file does not build a chain of MacLane-Vaquié with limit steps. It shows that in the discrete case of rank 1 such a chain is not needed. The chain of ordinary augmentations can be infinite, also if `ν` has a nonzero support (Example 3.3.14 of Volume 3 of the handbook). Then `ν` is only the limit of the chain, and for `f` in the support the values `μᵢ(f)` tend to `∞` but are finite. The degrees of the `φᵢ` need not be bounded if `ν` has support `0`. The file does not treat value groups that are not discrete of rank 1.

## References

* [Mac36] S. MacLane, A construction for absolute values in polynomial rings.
* [Vaq07] M. Vaquié, Extension d'une valuation.
-/

open Polynomial

namespace Singularity

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

section Discrete

/-- The use of the discreteness. Let the values of `ν` be discrete of rank 1. A strictly decreasing family of values of `ν`, indexed by a nonempty totally ordered set without a largest element and bounded below by some `c ≠ 0`, does not exist. In additive notation, a strictly increasing family of values of `ν` is not bounded. -/
theorem false_of_strictAnti_of_noMaxOrder {ν : Valuation K[X] Γ₀}
    (hdisc : ∀ c d : Γ₀, c ≠ 0 → (Set.Icc c d ∩ Set.range ν).Finite)
    {ι : Type*} [LinearOrder ι] [Nonempty ι] [NoMaxOrder ι] {s : ι → Γ₀} (hs : StrictAnti s)
    {c : Γ₀} (hc : c ≠ 0) (hcs : ∀ i, c ≤ s i) (hr : ∀ i, s i ∈ Set.range ν) : False := by
  choose g hg using fun i : ι => exists_gt i
  have ht : StrictMono fun n : ℕ => g^[n] (Classical.arbitrary ι) :=
    strictMono_nat_of_lt_succ fun n => by
      rw [Function.iterate_succ_apply']
      exact hg _
  exact false_of_strictAnti hdisc (hs.comp_strictMono ht) hc (fun n => hcs _) fun n => hr _

/-- The hypothesis of discreteness holds for a valuation with values in `ℤᵐ⁰`. In additive notation, the values are in `ℤ ∪ {∞}`. Between `c ≠ 0` and `d` there are only finitely many elements of `ℤᵐ⁰`. -/
theorem finite_Icc_inter_range_int (ν : Valuation K[X] (WithZero (Multiplicative ℤ)))
    (c d : WithZero (Multiplicative ℤ)) (hc : c ≠ 0) : (Set.Icc c d ∩ Set.range ν).Finite := by
  refine ((Set.finite_Icc (WithZero.log c) (WithZero.log d)).image WithZero.exp).subset ?_
  rintro x ⟨⟨hcx, hxd⟩, -⟩
  have hx : x ≠ 0 := ne_of_gt (lt_of_lt_of_le (zero_lt_iff.2 hc) hcx)
  have hd : d ≠ 0 := ne_of_gt (lt_of_lt_of_le (zero_lt_iff.2 hx) hxd)
  refine ⟨WithZero.log x, ⟨?_, ?_⟩, WithZero.exp_log hx⟩
  · rwa [← WithZero.exp_le_exp, WithZero.exp_log hc, WithZero.exp_log hx]
  · rwa [← WithZero.exp_le_exp, WithZero.exp_log hx, WithZero.exp_log hd]

end Discrete

section Chain

variable {v : Valuation K Γ₀} {ν : Valuation K[X] Γ₀}

/-- The theorem of MacLane for a valuation `ν` with values in `ℤᵐ⁰`, that is, with additive values in `ℤ ∪ {∞}`. For each `f` with `ν f ≠ 0`, the value `μᵢ f` of the chain of MacLane is `ν f` for all large `i`. -/
theorem macLaneChain_eventually_eq_int {v : Valuation K (WithZero (Multiplicative ℤ))}
    {ν : Valuation K[X] (WithZero (Multiplicative ℤ))} (hν : ∀ a, ν (C a) = v a) (f : K[X])
    (hf : ν f ≠ 0) : ∃ N, ∀ n, N ≤ n → macLaneChain v ν n f = ν f :=
  macLaneChain_eventually_eq hν (finite_Icc_inter_range_int ν) f hf

variable (hν : ∀ a, ν (C a) = v a)
  (hdisc : ∀ c d : Γ₀, c ≠ 0 → (Set.Icc c d ∩ Set.range ν).Finite)
include hν hdisc

/-- Let the values of `ν` be discrete of rank 1, let the chain of MacLane be infinite, and let the degrees of its key polynomials `φᵢ` be at most `d`. Then `ν φᵢ` tends to `0`: for each `c ≠ 0`, `ν φᵢ < c` for all large `i`. In additive notation, `ν(φᵢ) → ∞`. -/
theorem macLaneChainKey_eventually_lt (hcon : ∀ n, macLaneChain v ν n ≠ ν) (d : ℕ)
    (hdeg : ∀ n, (macLaneChainKey v ν n).natDegree ≤ d) {c : Γ₀} (hc : c ≠ 0) :
    ∃ N, ∀ n, N ≤ n → ν (macLaneChainKey v ν n) < c := by
  set D := fun n => (macLaneChainKey v ν n).natDegree with hD
  have hmono : Monotone D :=
    monotone_nat_of_le_succ fun n => natDegree_macLaneChainKey_le_succ hν (hcon (n + 1))
  have hbdd : BddAbove (Set.range D) := ⟨d, Set.forall_mem_range.2 hdeg⟩
  obtain ⟨N, hN⟩ := Nat.sSup_mem (Set.range_nonempty D) hbdd
  have hconst : ∀ n, N ≤ n → D n = D N := fun n hn =>
    le_antisymm (hN ▸ le_csSup hbdd ⟨n, rfl⟩) (hmono hn)
  have hanti : StrictAnti fun k => ν (macLaneChainKey v ν (N + k)) :=
    strictAnti_nat_of_succ_lt fun k => map_macLaneChainKey_succ_lt hν (hcon (N + k + 1)) (by
      change D (N + k + 1) = D (N + k)
      rw [hconst (N + k + 1) (by omega), hconst (N + k) (by omega)])
  by_contra hne
  push Not at hne
  refine false_of_strictAnti hdisc hanti hc (fun k => ?_) (fun k => ⟨_, rfl⟩)
  obtain ⟨n, hn, hcn⟩ := hne (N + k)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := hanti.antitone (show k ≤ k + m by omega)
  simp only [← add_assoc] at h
  exact hcn.trans h

/-- Let the values of `ν` be discrete of rank 1, and let `ν F = 0` for some `F ≠ 0`. If the chain of MacLane is infinite, then `ν φᵢ` tends to `0`. In additive notation, `ν(φᵢ) → ∞`. -/
theorem macLaneChainKey_eventually_lt_of_map_eq_zero {F : K[X]} (hF : F ≠ 0) (hF0 : ν F = 0)
    (hcon : ∀ n, macLaneChain v ν n ≠ ν) {c : Γ₀} (hc : c ≠ 0) :
    ∃ N, ∀ n, N ≤ n → ν (macLaneChainKey v ν n) < c :=
  macLaneChainKey_eventually_lt hν hdisc hcon F.natDegree
    (fun n => natDegree_macLaneChainKey_le_of_map_eq_zero hν hF hF0 (hcon n)) hc

end Chain

namespace ContinuousFamily

variable {μ : Valuation K[X] Γ₀} {ι : Type*} [LinearOrder ι] {F : ContinuousFamily μ ι}
  {ν : Valuation K[X] Γ₀}

section Range

variable (hlow : ∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = μ a)
  (hval : ∀ i, F.value i ∈ Set.range ν)
include hlow hval

/-- Let `ν` agree with `μ` in degree less than the degree of the family, and let the values `γᵢ` be values of `ν`. Then each value `μᵢ f` is a value of `ν`. -/
theorem val_mem_range (i : ι) (f : K[X]) :
    augmentedValuationFun μ (F.key i) (F.value i) f ∈ Set.range ν := by
  obtain ⟨j, hj⟩ := exists_eq_augmentedValuationFun (μ := μ) (φ := F.key i) (γ := F.value i) f
  obtain ⟨g, hg⟩ := hval i
  refine ⟨expansionCoeff (F.key i) f j * g ^ j, ?_⟩
  rw [← hj, Valuation.map_mul, Valuation.map_pow, hg,
    hlow i _ (degree_expansionCoeff_lt (F.keyPolynomial i).monic f j)]

variable [Nonempty ι] [NoMaxOrder ι]
  (hdisc : ∀ c d : Γ₀, c ≠ 0 → (Set.Icc c d ∩ Set.range ν).Finite)
include hdisc

omit hlow in
/-- Let the values of `ν` be discrete of rank 1, and let the values `γᵢ` of a continuous family be values of `ν`. Then `γᵢ` tends to `0`: for each `c ≠ 0`, `γᵢ < c` for all large `i`. In additive notation, `γᵢ → ∞`. -/
theorem eventually_value_lt {c : Γ₀} (hc : c ≠ 0) : ∃ i, ∀ j, i ≤ j → F.value j < c := by
  by_contra hne
  push Not at hne
  refine false_of_strictAnti_of_noMaxOrder hdisc F.value_strictAnti hc (fun i => ?_) hval
  obtain ⟨j, hij, hcj⟩ := hne i
  exact hcj.trans (F.value_strictAnti.antitone hij)

/-- Let the values of `ν` be discrete of rank 1, let `ν` agree with `μ` in degree less than the degree of the family, and let the values `γᵢ` be values of `ν`. Let `φ` be unstable, with `γ ≤ μᵢ φ` for each `i`. Then `γ = 0`. In additive notation, `γ = ∞`. -/
theorem eq_zero_of_not_isStable {φ : K[X]} (hφ : ¬ F.IsStable φ) {γ : Γ₀}
    (hγ : ∀ i, γ ≤ augmentedValuationFun μ (F.key i) (F.value i) φ) : γ = 0 := by
  by_contra h0
  exact false_of_strictAnti_of_noMaxOrder hdisc (s := fun i => F.val i φ)
    (fun i j hij => F.val_lt_val_of_not_isStable hφ hij) h0 hγ
    (fun i => val_mem_range hlow hval i φ)

variable (hν : ∀ i f, ν f ≤ augmentedValuationFun μ (F.key i) (F.value i) f)
include hν

/-- Let the values of `ν` be discrete of rank 1. Let `μᵢ ≤ ν` for each `i` in additive notation, let `ν` agree with `μ` in degree less than the degree of the family, and let the values `γᵢ` be values of `ν`. Then each `f` with `ν f ≠ 0` is stable. -/
theorem isStable_of_map_ne_zero {f : K[X]} (hf : ν f ≠ 0) : F.IsStable f := by
  by_contra hs
  exact hf (eq_zero_of_not_isStable hlow hval hdisc hs fun i => hν i f)

/-- Under the hypotheses of `isStable_of_map_ne_zero`, `ν` is the limit of the family on each `f` with `ν f ≠ 0`: `μᵢ f = ν f` for all large `i`. -/
theorem eventually_val_eq_of_map_ne_zero {f : K[X]} (hf : ν f ≠ 0) :
    ∃ i, ∀ j, i ≤ j → augmentedValuationFun μ (F.key j) (F.value j) f = ν f := by
  have hs := isStable_of_map_ne_zero hlow hval hdisc hν hf
  obtain ⟨i, hi⟩ := hs.exists_forall_eq
  exact ⟨i, fun j hj => (hi j hj).trans (F.stableValue_eq_of_isStable hν hlow hs)⟩

section Support

variable (hsupp : ∀ f, ν f = 0 → f = 0)
include hsupp

/-- Under the hypotheses of `isStable_of_map_ne_zero`, let `ν` have support `0`. Then each polynomial is stable. -/
theorem isStable_of_supp_eq_bot (f : K[X]) : F.IsStable f := by
  by_cases hf : f = 0
  · rw [hf]
    exact isStable_zero
  · exact isStable_of_map_ne_zero hlow hval hdisc hν fun h => hf (hsupp f h)

/-- Under the hypotheses of `isStable_of_map_ne_zero`, let `ν` have support `0`. Then the limit `μ_∞` of the family is `ν`. -/
theorem stableValue_eq_of_supp_eq_bot (f : K[X]) : F.stableValue f = ν f :=
  F.stableValue_eq_of_isStable hν hlow (isStable_of_supp_eq_bot hlow hval hdisc hν hsupp f)

/-- Under the hypotheses of `isStable_of_map_ne_zero`, let `ν` have support `0`. Then the family has no limit key polynomial. -/
theorem not_isLimitKeyPolynomial (φ : K[X]) : ¬ F.IsLimitKeyPolynomial φ := fun hφ =>
  hφ.not_isStable (isStable_of_supp_eq_bot hlow hval hdisc hν hsupp φ)

end Support

namespace IsLimitKeyPolynomial

variable {φ : K[X]} (hφ : F.IsLimitKeyPolynomial φ)
include hφ

/-- Under the hypotheses of `isStable_of_map_ne_zero`, a limit key polynomial `φ` has `ν φ = 0`. In additive notation, `ν(φ) = ∞`. -/
theorem map_eq_zero : ν φ = 0 := by
  by_contra h
  exact hφ.not_isStable (isStable_of_map_ne_zero hlow hval hdisc hν h)

omit hν in
/-- Under the hypotheses of `eq_zero_of_not_isStable`, the only value `γ` with `γ ≤ μᵢ φ` for each `i` is `γ = 0`. In additive notation, the limit augmentation `[μ_∞; φ, γ]` is defined only for `γ = ∞`. -/
theorem eq_zero_of_le {γ : Γ₀} (hγ : ∀ i, γ ≤ augmentedValuationFun μ (F.key i) (F.value i) φ) :
    γ = 0 :=
  eq_zero_of_not_isStable hlow hval hdisc hφ.not_isStable hγ

/-- Under the hypotheses of `isStable_of_map_ne_zero`, the limit augmentation `[μ_∞; φ, ν(φ)]` takes the values of `ν`. -/
theorem limitAugmentedValuationFun_eq (f : K[X]) : F.limitAugmentedValuationFun φ (ν φ) f = ν f := by
  have h0 : ν φ = 0 := hφ.map_eq_zero hlow hval hdisc hν
  have hm := hφ.monic
  have hd := hφ.natDegree_pos
  have hr : (f %ₘ φ).degree < φ.degree := degree_modByMonic_lt f hm
  have hs : φ * (f /ₘ φ) ∈ Valuation.supp ν := by
    rw [Valuation.mem_supp_iff, Valuation.map_mul, h0, zero_mul]
  have e : F.limitAugmentedValuationFun φ 0 f = F.stableValue (f %ₘ φ) := by
    refine le_antisymm ((F.limitAugmentedValuationFun_le_iff hm hd).2 fun j => ?_) ?_
    · cases j with
      | zero => rw [expansionCoeff_zero_eq_modByMonic, pow_zero, mul_one]
      | succ j =>
        rw [zero_pow (Nat.succ_ne_zero j), mul_zero]
        exact zero_le
    · simpa [expansionCoeff_zero_eq_modByMonic] using
        F.le_limitAugmentedValuationFun (γ := 0) hm hd f 0
  rw [h0, e, F.stableValue_eq_of_isStable hν hlow (hφ.isStable_of_degree_lt hr),
    ← Valuation.map_add_supp ν _ hs, modByMonic_add_div f φ]

/-- Under the hypotheses of `isStable_of_map_ne_zero`, let `γ ≤ μᵢ φ` for each `i`. Then the limit augmentation `[μ_∞; φ, γ]` takes the values of `ν`. -/
theorem limitAugmentedValuationFun_eq_of_le {γ : Γ₀}
    (hγ : ∀ i, γ ≤ augmentedValuationFun μ (F.key i) (F.value i) φ) (f : K[X]) :
    F.limitAugmentedValuationFun φ γ f = ν f := by
  rw [hφ.eq_zero_of_le hlow hval hdisc hγ, ← hφ.map_eq_zero hlow hval hdisc hν]
  exact hφ.limitAugmentedValuationFun_eq hlow hval hdisc hν f

/-- The limit step in the discrete case of rank 1. Under the hypotheses of `isStable_of_map_ne_zero`, each limit augmentation `[μ_∞; φ, γ]` of the family is `ν`. The value `γ` is `0` by `eq_zero_of_le`, and `ν φ = 0` by `map_eq_zero`. Thus a limit step is the last step of the chain, and it ends with `ν`. -/
theorem limitAugmentedValuation_eq {γ : Γ₀}
    (hγ : ∀ i, γ ≤ augmentedValuationFun μ (F.key i) (F.value i) φ) :
    F.limitAugmentedValuation φ γ hφ hγ = ν :=
  Valuation.ext fun f => hφ.limitAugmentedValuationFun_eq_of_le hlow hval hdisc hν hγ f

end IsLimitKeyPolynomial

end Range

end ContinuousFamily

end Singularity
