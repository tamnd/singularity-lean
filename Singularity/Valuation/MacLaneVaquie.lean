/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.LimitKeyPolynomial

/-!
# The chain of MacLane-Vaquié with limit steps

This file builds the chain of MacLane-Vaquié [Vaq07] with ordinary and limit augmentations, for a valuation `ν` on `K[X]` with any value group. It continues `Singularity/Valuation/MacLaneChain.lean` (ordinary steps only), `Singularity/Valuation/LimitKeyPolynomial.lean` (one limit step) and `Singularity/Valuation/MacLaneDiscrete.lean` (the case of a discrete value group of rank 1).

The conventions are those of `Singularity/Valuation/KeyPolynomials.lean`. The valuations are multiplicative. Thus `μ ≤ ν` in the additive notation of the handbook is `∀ f, ν f ≤ μ f` here, and the value `∞` is `0`.

A step of MacLane-Vaquié towards `ν` (`MacLaneVaquieStep ν μ μ'`) is one of two kinds. An ordinary step is `μ' = [μ; φ, ν(φ)]`, where `φ` is a monic polynomial of least degree with `μ(φ) < ν(φ)` in additive notation. A limit step is `μ' = [μ_∞; φ, ν(φ)]`, where `(μᵢ)` is a continuous family of augmentations of `μ` below `ν`, and `φ` is a limit key polynomial of degree larger than the degree of the family.

## The proof

Let `ν` agree with `w` on the constants, and let `w ≤ ν` and `w ≠ ν` in additive notation. Let `φ₀` be a monic polynomial of least degree `d` with `w(φ₀) < ν(φ₀)`. Then `w` and `ν` agree in degree less than `d`. One round of the construction makes `w` agree with `ν` in degree at most `d` with one step (`exists_macLaneVaquieStep_or_forall_isStable`). The round does not choose a sequence of key polynomials of degree `d`. It uses all of them at once, as in the complete families of [Vaq07].

* Let `ψ` be monic of degree `d` with `ν(ψ) ≥ ν(φ₀)` in additive notation. Then `ψ - φ₀` has degree less than `d`, so `w(ψ) = w(φ₀) < ν(φ₀) ≤ ν(ψ)`. Thus `ψ` is a key polynomial for `w` (`keyPolynomial_of_map_lt`).
* If some monic `ψ₀` of degree `d` has the largest `ν`-value among the monic polynomials of degree `d`, then the ordinary step `[w; ψ₀, ν(ψ₀)]` agrees with `ν` in degree at most `d`. Write `f = r + ψ₀ c` with `deg r < d` and a constant `c` (`map_eq_of_natDegree_le_of_forall_le`).
* Otherwise the values `ν(ψ) ≥ ν(φ₀)` of the monic `ψ` of degree `d` have no largest element. They index a continuous family `[w; ψ, ν(ψ)]` (`completeFamily`). The index set is this set of values with the reverse order. It is not empty, and it has no largest element. The family is below `ν`, and `ν` agrees with `w` in degree less than `d`. Each monic `ψ` of degree `d` is stable: if `ν(ψ') ≥ ν(ψ)` in additive notation, then `[w; ψ', ν(ψ')] ψ = ν(ψ)`.
* If all polynomials are stable, then `ν` is the limit of the family (`ContinuousFamily.stableValue_eq_of_isStable`). Otherwise a limit key polynomial `φ` exists. Its degree is larger than `d`, since the monic polynomials of degree `d` are stable. The limit step `[μ_∞; φ, ν(φ)]` agrees with `ν` in degree less than `deg φ`, so in degree at most `d`.

Rounds repeat. Either a round ends with a family of which `ν` is the limit, or the rounds give a sequence `wₙ` such that `wₙ` agrees with `ν` in degree at most `n` (`exists_macLaneVaquie_seq_or_forall_isStable`). In the second case `ν` is the limit of the chain: for each `f`, `wₙ f = ν f` for `n ≥ deg f`.

Let `ν(F) = ∞` for some `F ≠ 0`. If a valuation `w` agrees with `ν` in degree at most `deg F`, then `w = ν`, since each `f` is congruent modulo `F` to a polynomial of degree less than `deg F` (`eq_of_map_eq_zero_of_degree_lt`). The same argument shows that `ν` is not the limit of a continuous family over `w ≠ ν`: the stable polynomial `F` would have an expansion coefficient `a ≠ 0` of degree less than `d` with `ν(a) = ∞` (`ContinuousFamily.not_isStable_of_map_eq_zero`). So `ν` is reached by finitely many steps (`reflTransGen_macLaneVaquieStep_of_map_eq_zero`).

Let `φ` be a monic `ν`-minimal polynomial of positive degree. By the expansion criterion, `ν(f)` is the minimum of `ν(aⱼ) + jν(φ)` for the `φ`-expansion of `f`. So a valuation `w ≤ ν` that agrees with `ν` in degree less than `deg φ` and at `φ` is `ν` (`eq_of_isMuMinimal`). Thus `w_{deg φ} = ν` in the first case. The second case does not hold. If `deg φ` is less than the degree `d` of the family, then `μ = ν`. Otherwise let `φ` be stable, so `μⱼ(φ) = ν(φ)` for `j` large, and let `r` be the remainder of `φ` modulo `φⱼ`. Then `μⱼ(φ - r) > μⱼ(φ)`, but `ν(φ - r) = min(ν(r), ν(φ)) ≤ ν(φ)` since `φ` is `ν`-minimal and `deg r < deg φ` (`ContinuousFamily.not_forall_isStable_of_isMuMinimal`). So `ν` is reached by finitely many steps (`reflTransGen_macLaneVaquieStep_of_isMuMinimal`). Conversely, the key polynomial of the last step of a chain is a key polynomial for its end (`MacLaneVaquieStep.exists_keyPolynomial`). Thus finitely many steps lead from `w₀ ≠ ν` to `ν` if and only if `ν` has a key polynomial.

## Main results

* `Singularity.MacLaneVaquieStep`: a step of MacLane-Vaquié towards `ν`, ordinary or limit.
* `Singularity.exists_macLaneVaquieStep_or_forall_isStable`: one round in degree `d`. One step makes `w` agree with `ν` in degree at most `d`, or `ν` is the limit of a continuous family over `w`. At a limit step the degree of the key polynomial increases strictly.
* `Singularity.exists_macLaneVaquie_seq_or_forall_isStable`: the chain. Either `ν` is the limit of a chain `wₙ` of steps with `wₙ = ν` in degree at most `n`, or `ν` is the limit of a continuous family over a valuation of the chain.
* `Singularity.reflTransGen_macLaneVaquieStep_of_map_eq_zero`: part 4 of the theorem of MacLane-Vaquié for a valuation `ν` with nonzero support. The chain reaches `ν` after finitely many steps. The corollary `reflTransGen_monomialValuation_of_map_eq_zero` starts at `[v; X, ν(X)]`.
* `Singularity.reflTransGen_macLaneVaquieStep_iff_exists_keyPolynomial`: the criterion for a finite chain. For `w₀ ≠ ν`, finitely many steps lead from `w₀` to `ν` if and only if `ν` has a key polynomial. The value group and the support of `ν` are arbitrary. A monic `ν`-minimal polynomial of positive degree is sufficient (`reflTransGen_macLaneVaquieStep_of_isMuMinimal`).
* `Singularity.reflTransGen_macLaneVaquieStep_or_forall_not_keyPolynomial`: part 4 with three cases. A finite chain reaches `ν`, or `ν` has no key polynomial and `ν` is the limit of an infinite chain `wₙ ≠ ν`, or `ν` has no key polynomial and `ν` is the limit of a continuous family over a valuation of the chain.

## What the file does not prove

The index sets of the continuous families are totally ordered sets of values. They are not well ordered as in [Vaq07], and the file does not extract a cofinal well ordered subfamily. The file does not prove that the chain is unique, and it does not prove that the degrees and the values `ν(φ)` of the key polynomials depend only on `ν`. It does not prove the conditions of [Vaq07] on two consecutive steps of an admissible family. For a valuation without a key polynomial, it does not decide whether `ν` is the limit of an infinite chain or the limit of a continuous family. It does not relate the existence of a key polynomial to the value group and the residue field of `ν`.

## References

* [Vaq07] M. Vaquié, Extension d'une valuation.
-/

open Polynomial

namespace Singularity

universe uV

variable {K : Type*} [Field K] {Γ₀ : Type uV} [LinearOrderedCommGroupWithZero Γ₀]

section Agreement

variable {ν w : Valuation K[X] Γ₀}

/-- Let `w` agree with `ν` in degree less than `D`, and let `ν(a) = ∞` for some `a ≠ 0` of degree less than `D`. Then `w = ν`. Each `f` is congruent modulo `a` to a polynomial of degree less than the degree of `a`, and the multiples of `a` have the value `∞` for both valuations. -/
theorem eq_of_map_eq_zero_of_degree_lt {D : WithBot ℕ} (h : ∀ f : K[X], f.degree < D → w f = ν f)
    {a : K[X]} (ha : a ≠ 0) (haD : a.degree < D) (ha0 : ν a = 0) : w = ν := by
  set G := a * C a.leadingCoeff⁻¹ with hGdef
  have hc : a.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.2 ha)
  have hG : G.Monic := monic_mul_leadingCoeff_inv ha
  have hGD : G.degree < D := by
    rw [hGdef, degree_mul_C hc]
    exact haD
  have hG0 : ν G = 0 := by rw [hGdef, Valuation.map_mul, ha0, zero_mul]
  have hwG : w G = 0 := by rw [h G hGD, hG0]
  refine Valuation.ext fun f => ?_
  have hs1 : G * (f /ₘ G) ∈ Valuation.supp w := by
    rw [Valuation.mem_supp_iff, Valuation.map_mul, hwG, zero_mul]
  have hs2 : G * (f /ₘ G) ∈ Valuation.supp ν := by
    rw [Valuation.mem_supp_iff, Valuation.map_mul, hG0, zero_mul]
  have hr : (f %ₘ G).degree < D := (degree_modByMonic_lt f hG).trans hGD
  rw [← modByMonic_add_div f G, Valuation.map_add_supp _ _ hs1, Valuation.map_add_supp _ _ hs2,
    h _ hr]

/-- Agreement in degree at most `deg φ`. Let `w ≤ ν` in additive notation, let `w` agree with `ν` in degree less than the degree of a monic `φ` and at `φ`, and let `φ` have the largest `ν`-value among the monic polynomials of its degree. Then `w` agrees with `ν` in degree at most `deg φ`. -/
theorem map_eq_of_natDegree_le_of_forall_le (hle : ∀ f, ν f ≤ w f) {φ : K[X]} (hm : φ.Monic)
    (hd : 0 < φ.natDegree) (hlow : ∀ a : K[X], a.degree < φ.degree → w a = ν a)
    (hφ : w φ = ν φ) (hopt : ∀ ψ : K[X], ψ.Monic → ψ.natDegree = φ.natDegree → ν φ ≤ ν ψ)
    {f : K[X]} (hf : f.natDegree ≤ φ.natDegree) : w f = ν f := by
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
  refine le_antisymm ?_ (hle f)
  calc w f = w (f %ₘ φ + φ * C c) := by rw [hsum]
    _ ≤ max (w (f %ₘ φ)) (w (φ * C c)) := Valuation.map_add _ _ _
    _ = max (ν (f %ₘ φ)) (ν (φ * C c)) := by
      rw [Valuation.map_mul w, Valuation.map_mul ν, hlow _ hr, hlow _ hC, hφ]
    _ ≤ ν f := max_le hrle hkey

end Agreement

section Step

/-- A step of MacLane-Vaquié from `μ` to `μ'` towards `ν` [Vaq07]. An ordinary step (`augment`) is `μ' = [μ; φ, ν(φ)]`, where `μ ≤ ν` in additive notation and `φ` is a monic polynomial of least degree with `μ(φ) < ν(φ)`. A limit step (`limit`) is `μ' = [μ_∞; φ, ν(φ)]`, where `(μᵢ)` is a continuous family of augmentations of `μ` with `μᵢ ≤ ν`, `ν` agrees with `μ` in degree less than the degree of the family, and `φ` is a limit key polynomial of degree larger than the degree of the family. The valuation `μ'` is given by its values. -/
inductive MacLaneVaquieStep (ν μ μ' : Valuation K[X] Γ₀) : Prop
  | augment (φ : K[X]) (hle : ∀ f, ν f ≤ μ f) (hφ : φ.Monic) (hlt : ν φ < μ φ)
      (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f)
      (h : ∀ f, μ' f = augmentedValuationFun μ φ (ν φ) f)
  | limit (ι : Type uV) [LinearOrder ι] [Nonempty ι] [NoMaxOrder ι] (F : ContinuousFamily μ ι)
      (hν : ∀ i f, ν f ≤ augmentedValuationFun μ (F.key i) (F.value i) f)
      (hlow : ∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = μ a) (φ : K[X])
      (hφ : F.IsLimitKeyPolynomial φ) (hdeg : ∀ i, (F.key i).natDegree < φ.natDegree)
      (h : ∀ f, μ' f = F.limitAugmentedValuationFun φ (ν φ) f)

variable {ν μ μ' : Valuation K[X] Γ₀}

/-- A step of MacLane-Vaquié keeps the conditions of the chain: `μ'` agrees with `ν` on the constants, and `μ' ≤ ν` in additive notation. -/
theorem MacLaneVaquieStep.macLaneBelow (h : MacLaneVaquieStep ν μ μ')
    (hC : ∀ c, ν (C c) = μ (C c)) : (∀ c, ν (C c) = μ' (C c)) ∧ ∀ f, ν f ≤ μ' f := by
  rcases h with ⟨φ, hle, hφ, hlt, hlow, h⟩ | ⟨ι, F, hν, hlow, φ, hφ, hdeg, h⟩
  · have hd := (keyPolynomial_of_map_lt hle hφ hlt hlow).natDegree_pos
    refine ⟨fun c => ?_, fun f => ?_⟩
    · rw [h, augmentedValuationFun_C hφ hd, hC]
    · rw [h]
      exact map_le_augmentedValuationFun_of_map_eq hφ hd hlow f
  · refine ⟨fun c => ?_, fun f => ?_⟩
    · rw [h, F.limitAugmentedValuationFun_of_degree_lt hφ.monic hφ.natDegree_pos
        (degree_C_le.trans_lt (natDegree_pos_iff_degree_pos.1 hφ.natDegree_pos)),
        (F.stableValue_C c).2, hC]
    · rw [h]
      exact hφ.map_le_limitAugmentedValuationFun hν hlow le_rfl f

/-- A finite chain of steps of MacLane-Vaquié keeps the conditions of the chain. -/
theorem macLaneBelow_of_reflTransGen (h : Relation.ReflTransGen (MacLaneVaquieStep ν) μ μ')
    (hC : ∀ c, ν (C c) = μ (C c)) (hle : ∀ f, ν f ≤ μ f) :
    (∀ c, ν (C c) = μ' (C c)) ∧ ∀ f, ν f ≤ μ' f := by
  induction h with
  | refl => exact ⟨hC, hle⟩
  | tail _ hs ih => exact hs.macLaneBelow ih.1

end Step

section Complete

variable {ν w : Valuation K[X] Γ₀} {φ : K[X]}

variable (ν φ) in
/-- The values `ν(ψ)` of the monic polynomials `ψ` of the degree of `φ` with `ν(ψ) ≥ ν(φ)` in additive notation. With the reverse order, this set indexes the complete family `completeFamily`. -/
def completeValues : Set Γ₀ :=
  {γ | γ ≤ ν φ ∧ ∃ ψ : K[X], ψ.Monic ∧ ψ.natDegree = φ.natDegree ∧ ν ψ = γ}

variable (hle : ∀ f, ν f ≤ w f) (hm : φ.Monic) (hlt : ν φ < w φ)
  (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = w f)

include hle hm hlt hlow in
/-- Let `ψ` be monic of the degree of `φ` with `ν(ψ) ≥ ν(φ)` in additive notation. Then `w(ψ) = w(φ) < ν(ψ)`, and `ψ` is a key polynomial for `w`. -/
theorem keyPolynomial_of_map_le_of_natDegree_eq {ψ : K[X]} (hψ : ψ.Monic)
    (hψd : ψ.natDegree = φ.natDegree) (hνψ : ν ψ ≤ ν φ) :
    w ψ = w φ ∧ ν ψ < w ψ ∧ (∀ f : K[X], f.degree < ψ.degree → ν f = w f) ∧
      KeyPolynomial w ψ := by
  have ha : (ψ - φ).degree < φ.degree := degree_sub_lt_of_monic hm hψ hψd
  have hwa : w (ψ - φ) < w φ := by
    rw [← hlow _ ha]
    exact ((Valuation.map_sub _ _ _).trans (max_le hνψ le_rfl)).trans_lt hlt
  have hwψ : w ψ = w φ := by
    rw [show ψ = φ + (ψ - φ) by ring, Valuation.map_add_eq_of_lt_left _ hwa]
  have hdeg : ψ.degree = φ.degree := by
    rw [degree_eq_natDegree hψ.ne_zero, degree_eq_natDegree hm.ne_zero, hψd]
  have hltψ : ν ψ < w ψ := (hνψ.trans_lt hlt).trans_eq hwψ.symm
  have hlowψ : ∀ f : K[X], f.degree < ψ.degree → ν f = w f := fun f hf =>
    hlow f (hf.trans_eq hdeg)
  exact ⟨hwψ, hltψ, hlowψ, keyPolynomial_of_map_lt hle hψ hltψ hlowψ⟩

theorem completeValues_spec (i : (completeValues ν φ)ᵒᵈ) :
    ∃ ψ : K[X], ψ.Monic ∧ ψ.natDegree = φ.natDegree ∧ ν ψ = (OrderDual.ofDual i).1 :=
  (OrderDual.ofDual i).2.2

/-- The key polynomial of index `i` of the complete family. It is a monic polynomial of the degree of `φ` with the value `i`. -/
noncomputable def completeKey (i : (completeValues ν φ)ᵒᵈ) : K[X] :=
  Classical.choose (completeValues_spec i)

theorem completeKey_spec (i : (completeValues ν φ)ᵒᵈ) :
    (completeKey i).Monic ∧ (completeKey i).natDegree = φ.natDegree ∧
      ν (completeKey i) = (OrderDual.ofDual i).1 :=
  Classical.choose_spec (completeValues_spec i)

/-- The complete family in the degree of `φ` [Vaq07]. Let `w ≤ ν` in additive notation, and let `φ` be a monic polynomial of least degree with `w(φ) < ν(φ)`. The family consists of the augmentations `[w; ψ, ν(ψ)]` for all monic `ψ` of the degree of `φ` with `ν(ψ) ≥ ν(φ)` in additive notation, one `ψ` for each value. -/
noncomputable def completeFamily : ContinuousFamily w (completeValues ν φ)ᵒᵈ where
  key := completeKey
  value i := (OrderDual.ofDual i).1
  keyPolynomial i := by
    obtain ⟨h1, h2, h3⟩ := completeKey_spec i
    exact (keyPolynomial_of_map_le_of_natDegree_eq hle hm hlt hlow h1 h2
      (h3.trans_le (OrderDual.ofDual i).2.1)).2.2.2
  natDegree_eq i j := (completeKey_spec i).2.1.trans (completeKey_spec j).2.1.symm
  value_lt i := by
    obtain ⟨h1, h2, h3⟩ := completeKey_spec i
    rw [← h3]
    exact (keyPolynomial_of_map_le_of_natDegree_eq hle hm hlt hlow h1 h2
      (h3.trans_le (OrderDual.ofDual i).2.1)).2.1
  value_strictAnti _ _ h := h
  map_sub_le i j hij := by
    obtain ⟨h1, h2, h3⟩ := completeKey_spec i
    obtain ⟨h1', h2', h3'⟩ := completeKey_spec j
    have ha : (completeKey j - completeKey i).degree < φ.degree := by
      have := degree_sub_lt_of_monic h1 h1' (h2'.trans h2.symm)
      rwa [degree_eq_natDegree h1.ne_zero, h2, ← degree_eq_natDegree hm.ne_zero] at this
    have hji : (OrderDual.ofDual j).1 < (OrderDual.ofDual i).1 := hij
    rw [← hlow _ ha]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
    · rw [h3']
      exact hji.le
    · rw [h3]

variable {hle hm hlt hlow}

theorem completeFamily_key (i : (completeValues ν φ)ᵒᵈ) :
    (completeFamily hle hm hlt hlow).key i = completeKey i :=
  rfl

theorem completeFamily_value (i : (completeValues ν φ)ᵒᵈ) :
    (completeFamily hle hm hlt hlow).value i = (OrderDual.ofDual i).1 :=
  rfl

/-- The index set of the complete family is not empty: it contains the value `ν(φ)`. -/
theorem completeValues_nonempty (hφ : φ.Monic) : Nonempty (completeValues ν φ)ᵒᵈ :=
  ⟨OrderDual.toDual ⟨ν φ, le_rfl, φ, hφ, rfl, rfl⟩⟩

include hle hm hlt hlow in
/-- The complete family is below `ν`, and `ν` agrees with `w` in degree less than the degree of the family. -/
theorem completeFamily_le :
    (∀ i f, ν f ≤ augmentedValuationFun w ((completeFamily hle hm hlt hlow).key i)
      ((completeFamily hle hm hlt hlow).value i) f) ∧
    ∀ i (a : K[X]), a.degree < ((completeFamily hle hm hlt hlow).key i).degree → ν a = w a := by
  have hdeg : ∀ i, ((completeFamily hle hm hlt hlow).key i).degree = φ.degree := fun i => by
    obtain ⟨h1, h2, -⟩ := completeKey_spec i
    rw [completeFamily_key, degree_eq_natDegree h1.ne_zero, h2, degree_eq_natDegree hm.ne_zero]
  have hlowF : ∀ i (a : K[X]), a.degree < ((completeFamily hle hm hlt hlow).key i).degree →
      ν a = w a := fun i a ha => hlow a (ha.trans_eq (hdeg i))
  refine ⟨fun i f => ?_, hlowF⟩
  have hk := (completeFamily hle hm hlt hlow).keyPolynomial i
  rw [completeFamily_value, ← (completeKey_spec i).2.2]
  exact map_le_augmentedValuationFun_of_map_eq hk.monic hk.natDegree_pos (hlowF i) f

/-- If no monic polynomial of the degree of `φ` has the largest `ν`-value among these polynomials, then the index set of the complete family has no largest element. -/
theorem completeValues_noMaxOrder
    (hnomax : ∀ ψ₀ : K[X], ψ₀.Monic → ψ₀.natDegree = φ.natDegree →
      ∃ ψ : K[X], ψ.Monic ∧ ψ.natDegree = φ.natDegree ∧ ν ψ < ν ψ₀) :
    NoMaxOrder (completeValues ν φ)ᵒᵈ := by
  refine ⟨fun i => ?_⟩
  obtain ⟨h1, h2, h3⟩ := completeKey_spec i
  obtain ⟨ψ, hψ, hψd, hlt'⟩ := hnomax _ h1 h2
  rw [h3] at hlt'
  exact ⟨OrderDual.toDual ⟨ν ψ, hlt'.le.trans (OrderDual.ofDual i).2.1, ψ, hψ, hψd, rfl⟩, hlt'⟩

include hle hm hlt hlow in
/-- Each monic polynomial `ψ` of the degree of `φ` is stable for the complete family, with the limit value `ν(ψ)`. -/
theorem completeFamily_isStable {ψ : K[X]} (hψ : ψ.Monic) (hψd : ψ.natDegree = φ.natDegree) :
    (completeFamily hle hm hlt hlow).IsStable ψ := by
  set F := completeFamily hle hm hlt hlow
  have hex : ∃ ψ' : K[X], ψ'.Monic ∧ ψ'.natDegree = φ.natDegree ∧ ν ψ' = min (ν ψ) (ν φ) := by
    rcases le_total (ν ψ) (ν φ) with h | h
    · exact ⟨ψ, hψ, hψd, (min_eq_left h).symm⟩
    · exact ⟨φ, hm, rfl, (min_eq_right h).symm⟩
  let i₀ : (completeValues ν φ)ᵒᵈ := OrderDual.toDual ⟨min (ν ψ) (ν φ), min_le_right _ _, hex⟩
  refine (ContinuousFamily.stableValue_eq_of_forall (F := F) (i := i₀) (c := ν ψ)
    fun j hj => le_antisymm ?_ ((completeFamily_le (hle := hle)).1 j ψ)).1
  have hvj : F.value j ≤ ν ψ := (F.value_strictAnti.antitone hj).trans (min_le_left _ _)
  obtain ⟨h1, h2, h3⟩ := completeKey_spec j
  have ha : (ψ - F.key j).degree < (F.key j).degree := degree_sub_lt_of_monic h1 hψ (hψd.trans h2.symm)
  have hνk : ν (F.key j) = F.value j := h3
  calc F.val j ψ = F.val j (F.key j + (ψ - F.key j)) := by rw [add_sub_cancel]
    _ ≤ max (F.val j (F.key j)) (F.val j (ψ - F.key j)) := Valuation.map_add _ _ _
    _ = max (F.value j) (ν (ψ - F.key j)) := by
      rw [F.val_key_of_le le_rfl, F.val_of_degree_lt ha j,
        (completeFamily_le (hle := hle)).2 j _ ha]
    _ ≤ ν ψ := max_le hvj ((Valuation.map_sub _ _ _).trans (max_le le_rfl (hνk.trans_le hvj)))

end Complete

section Round

variable {ν w : Valuation K[X] Γ₀}

/-- One round of the chain of MacLane-Vaquié in degree `d`. Let `ν` agree with `w` on the constants, and let `w ≤ ν` and `w ≠ ν` in additive notation. Let `d` be the least degree of a monic `φ` with `w(φ) < ν(φ)`. Then `w` agrees with `ν` in degree less than `d`, and one of two cases holds. In the first case, one step of MacLane-Vaquié (ordinary or limit) gives a valuation that agrees with `ν` in degree at most `d`. In the second case, `ν` is the limit of a continuous family of augmentations of `w`: each polynomial is stable, and its limit value is its value for `ν`. -/
theorem exists_macLaneVaquieStep_or_forall_isStable (hC : ∀ c, ν (C c) = w (C c))
    (hle : ∀ f, ν f ≤ w f) (hne : w ≠ ν) :
    ∃ d : ℕ, (∀ f : K[X], f.natDegree < d → w f = ν f) ∧
      (∃ φ : K[X], φ.Monic ∧ φ.natDegree = d ∧ ν φ < w φ) ∧
      ((∃ w' : Valuation K[X] Γ₀, MacLaneVaquieStep ν w w' ∧
          ∀ f : K[X], f.natDegree ≤ d → w' f = ν f) ∨
        ∃ (ι : Type uV) (_ : LinearOrder ι) (_ : Nonempty ι) (_ : NoMaxOrder ι)
          (F : ContinuousFamily w ι),
          (∀ i f, ν f ≤ augmentedValuationFun w (F.key i) (F.value i) f) ∧
          (∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = w a) ∧
          ∀ f, F.IsStable f ∧ F.stableValue f = ν f) := by
  classical
  obtain ⟨φ₀, hm₀, hlt₀, hlow₀⟩ := exists_monic_map_lt hC hle hne
  have hdeg₀ : φ₀.degree = φ₀.natDegree := degree_eq_natDegree hm₀.ne_zero
  refine ⟨φ₀.natDegree, fun f hf => (hlow₀ f ?_).symm, ⟨φ₀, hm₀, rfl, hlt₀⟩, ?_⟩
  · rw [hdeg₀]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast hf)
  by_cases hmax : ∃ ψ₀ : K[X], ψ₀.Monic ∧ ψ₀.natDegree = φ₀.natDegree ∧
      ∀ ψ : K[X], ψ.Monic → ψ.natDegree = φ₀.natDegree → ν ψ₀ ≤ ν ψ
  · -- an ordinary step
    obtain ⟨ψ₀, hψ₀, hψ₀d, hopt⟩ := hmax
    obtain ⟨-, hlt, hlowψ, hk⟩ :=
      keyPolynomial_of_map_le_of_natDegree_eq hle hm₀ hlt₀ hlow₀ hψ₀ hψ₀d (hopt φ₀ hm₀ rfl)
    have hdψ := hk.natDegree_pos
    refine Or.inl ⟨augmentedValuation w ψ₀ (ν ψ₀) hk hlt.le,
      MacLaneVaquieStep.augment ψ₀ hle hψ₀ hlt hlowψ fun f => augmentedValuation_apply _ _ _,
      fun f hf => ?_⟩
    refine map_eq_of_natDegree_le_of_forall_le (fun g => ?_) hψ₀ hdψ (fun a ha => ?_)
      (augmentedValuation_self _ _) (fun ψ hψ hψd => hopt ψ hψ (hψd.trans hψ₀d))
      (hf.trans_eq hψ₀d.symm)
    · rw [augmentedValuation_apply]
      exact map_le_augmentedValuationFun_of_map_eq hψ₀ hdψ hlowψ g
    · rw [augmentedValuation_of_degree_lt _ _ ha, hlowψ a ha]
  -- the complete family
  have hnomax : ∀ ψ₀ : K[X], ψ₀.Monic → ψ₀.natDegree = φ₀.natDegree →
      ∃ ψ : K[X], ψ.Monic ∧ ψ.natDegree = φ₀.natDegree ∧ ν ψ < ν ψ₀ := by
    intro ψ₀ h1 h2
    by_contra hc
    push Not at hc
    exact hmax ⟨ψ₀, h1, h2, hc⟩
  have := completeValues_nonempty (ν := ν) hm₀
  have := completeValues_noMaxOrder (ν := ν) hnomax
  set F := completeFamily hle hm₀ hlt₀ hlow₀
  obtain ⟨hν, hlow⟩ := completeFamily_le (hle := hle) (hm := hm₀) (hlt := hlt₀) (hlow := hlow₀)
  by_cases hst : ∀ f, F.IsStable f
  · exact Or.inr ⟨(completeValues ν φ₀)ᵒᵈ, inferInstance, inferInstance, inferInstance, F, hν, hlow,
      fun f => ⟨hst f, F.stableValue_eq_of_isStable hν hlow (hst f)⟩⟩
  -- a limit step
  push Not at hst
  obtain ⟨φ, hφ⟩ := ContinuousFamily.exists_isLimitKeyPolynomial hst
  have hkd : ∀ i, (F.key i).natDegree = φ₀.natDegree := fun i => (completeKey_spec i).2.1
  have hdlt : φ₀.natDegree < φ.natDegree := by
    obtain ⟨i⟩ := ‹Nonempty (completeValues ν φ₀)ᵒᵈ›
    refine lt_of_le_of_ne ((hkd i).symm.trans_le (hφ.natDegree_key_le i)) fun h => ?_
    exact hφ.not_isStable (completeFamily_isStable hφ.monic h.symm)
  have hdeg : ∀ i, (F.key i).natDegree < φ.natDegree := fun i => (hkd i).trans_lt hdlt
  refine Or.inl ⟨F.limitAugmentedValuation φ (ν φ) hφ (fun i => hν i φ),
    MacLaneVaquieStep.limit _ F hν hlow φ hφ hdeg fun f => rfl, fun f hf => ?_⟩
  have hfd : f.degree < φ.degree := by
    rw [degree_eq_natDegree hφ.monic.ne_zero]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast hf.trans_lt hdlt)
  rw [ContinuousFamily.limitAugmentedValuation_apply,
    F.limitAugmentedValuationFun_of_degree_lt hφ.monic hφ.natDegree_pos hfd,
    F.stableValue_eq_of_isStable hν hlow (hφ.isStable_of_degree_lt hfd)]

/-- The chain of MacLane-Vaquié. Let `ν` agree with `w₀` on the constants, and let `w₀ ≤ ν` in additive notation. Then one of two cases holds. In the first case, there is a sequence `wₙ` with `w₀` at the start and finitely many steps of MacLane-Vaquié from `wₙ` to `wₙ₊₁`, such that `wₙ` agrees with `ν` in degree at most `n`. Thus `ν` is the limit of the chain. In the second case, the chain reaches a valuation `μ ≠ ν` after finitely many steps, and `ν` is the limit of a continuous family of augmentations of `μ`. -/
theorem exists_macLaneVaquie_seq_or_forall_isStable {ν w₀ : Valuation K[X] Γ₀}
    (hC : ∀ c, ν (C c) = w₀ (C c)) (hle : ∀ f, ν f ≤ w₀ f) :
    (∃ w : ℕ → Valuation K[X] Γ₀, w 0 = w₀ ∧
        (∀ n, Relation.ReflTransGen (MacLaneVaquieStep ν) (w n) (w (n + 1))) ∧
        ∀ n (f : K[X]), f.natDegree ≤ n → w n f = ν f) ∨
      ∃ μ : Valuation K[X] Γ₀, Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ μ ∧ μ ≠ ν ∧
        ∃ (ι : Type uV) (_ : LinearOrder ι) (_ : Nonempty ι) (_ : NoMaxOrder ι)
          (F : ContinuousFamily μ ι),
          (∀ i f, ν f ≤ augmentedValuationFun μ (F.key i) (F.value i) f) ∧
          (∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = μ a) ∧
          ∀ f, F.IsStable f ∧ F.stableValue f = ν f := by
  classical
  by_cases hB : ∃ μ : Valuation K[X] Γ₀, Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ μ ∧
      μ ≠ ν ∧ ∃ (ι : Type uV) (_ : LinearOrder ι) (_ : Nonempty ι) (_ : NoMaxOrder ι)
        (F : ContinuousFamily μ ι),
        (∀ i f, ν f ≤ augmentedValuationFun μ (F.key i) (F.value i) f) ∧
        (∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = μ a) ∧
        ∀ f, F.IsStable f ∧ F.stableValue f = ν f
  · exact Or.inr hB
  refine Or.inl ?_
  have hnext : ∀ (n : ℕ) (w : Valuation K[X] Γ₀), ∃ w' : Valuation K[X] Γ₀,
      (Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ w ∧ (∀ c, ν (C c) = w (C c)) ∧
        (∀ f, ν f ≤ w f) ∧ ∀ f : K[X], f.natDegree ≤ n → w f = ν f) →
      Relation.ReflTransGen (MacLaneVaquieStep ν) w w' ∧
        Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ w' ∧ (∀ c, ν (C c) = w' (C c)) ∧
        (∀ f, ν f ≤ w' f) ∧ ∀ f : K[X], f.natDegree ≤ n + 1 → w' f = ν f := by
    intro n w
    by_cases hP : Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ w ∧ (∀ c, ν (C c) = w (C c)) ∧
        (∀ f, ν f ≤ w f) ∧ ∀ f : K[X], f.natDegree ≤ n → w f = ν f
    swap
    · exact ⟨w, fun h => absurd h hP⟩
    obtain ⟨hr, hCw, hlew, hagree⟩ := hP
    by_cases hne : w = ν
    · exact ⟨w, fun _ => ⟨.refl, hr, hCw, hlew, fun f _ => by rw [hne]⟩⟩
    obtain ⟨d, -, ⟨φ, -, hφd, hφlt⟩, hA | hB'⟩ :=
      exists_macLaneVaquieStep_or_forall_isStable hCw hlew hne
    · obtain ⟨w', hs, hw'⟩ := hA
      have hnd : n < d := by
        by_contra h
        push Not at h
        exact hφlt.ne (hagree φ (hφd.trans_le h)).symm
      have hb := hs.macLaneBelow hCw
      exact ⟨w', fun _ => ⟨.single hs, hr.tail hs, hb.1, hb.2, fun f hf => hw' f (by omega)⟩⟩
    · exact absurd ⟨w, hr, hne, hB'⟩ hB
  choose g hg using hnext
  let w : ℕ → Valuation K[X] Γ₀ := fun n => Nat.rec (motive := fun _ => Valuation K[X] Γ₀) w₀
    (fun k x => g k x) n
  have hw : ∀ n, Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ (w n) ∧
      (∀ c, ν (C c) = w n (C c)) ∧ (∀ f, ν f ≤ w n f) ∧
      ∀ f : K[X], f.natDegree ≤ n → w n f = ν f := by
    intro n
    induction n with
    | zero =>
      refine ⟨.refl, hC, hle, fun f hf => ?_⟩
      change w₀ f = ν f
      rw [eq_C_of_natDegree_le_zero hf]
      exact (hC _).symm
    | succ n ih => exact (hg n (w n) ih).2
  exact ⟨w, rfl, fun n => (hg n (w n) (hw n)).1, fun n => (hw n).2.2.2⟩

end Round

namespace ContinuousFamily

variable {μ ν : Valuation K[X] Γ₀} {ι : Type*} [LinearOrder ι] [Nonempty ι] [NoMaxOrder ι]
  {F : ContinuousFamily μ ι}

omit [Nonempty ι] in
/-- Let `ν(P) = ∞` for some `P ≠ 0`. Let `(μᵢ)` be a continuous family of augmentations of `μ ≠ ν` below `ν`, and let `ν` agree with `μ` in degree less than the degree of the family. Then `P` is not stable. Thus `ν` is not the limit of the family. -/
theorem not_isStable_of_map_eq_zero
    (hν : ∀ i f, ν f ≤ augmentedValuationFun μ (F.key i) (F.value i) f)
    (hlow : ∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = μ a) (hne : μ ≠ ν)
    {P : K[X]} (hP : P ≠ 0) (hP0 : ν P = 0) : ¬ F.IsStable P := by
  intro hs
  obtain ⟨i, hi⟩ := hs.exists_forall_eq
  have hvi : F.val i P = 0 := (hi i le_rfl).trans ((F.stableValue_eq_of_isStable hν hlow hs).trans hP0)
  have hval : F.value i ≠ 0 := by
    intro h
    obtain ⟨j, hij⟩ := exists_gt i
    have hlt := F.value_strictAnti hij
    rw [h] at hlt
    exact absurd hlt (not_lt.2 zero_le)
  have hk := F.keyPolynomial i
  obtain ⟨k, hk0⟩ : ∃ k, expansionCoeff (F.key i) P k ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hP
    rw [eq_sum_expansionCoeff hk.monic hk.natDegree_pos P]
    simp [hall]
  have hle0 : μ (expansionCoeff (F.key i) P k) * F.value i ^ k = 0 := by
    refine le_antisymm ?_ zero_le
    rw [← hvi, val_apply]
    exact le_augmentedValuationFun hk.monic hk.natDegree_pos P k
  have hμ0 : μ (expansionCoeff (F.key i) P k) = 0 :=
    (mul_eq_zero.1 hle0).resolve_right (pow_ne_zero k hval)
  have hdeg := degree_expansionCoeff_lt hk.monic P k
  refine hne (eq_of_map_eq_zero_of_degree_lt (fun f hf => (hlow i f hf).symm) hk0 hdeg ?_)
  rw [hlow i _ hdeg, hμ0]

end ContinuousFamily

section Support

variable {ν w₀ : Valuation K[X] Γ₀}

/-- Part 4 of the theorem of MacLane-Vaquié for a valuation with nonzero support. Let `ν` agree with `w₀` on the constants, let `w₀ ≤ ν` in additive notation, and let `ν(F) = ∞` for some `F ≠ 0`. Then finitely many steps of MacLane-Vaquié lead from `w₀` to `ν`. The value group of `ν` is arbitrary. -/
theorem reflTransGen_macLaneVaquieStep_of_map_eq_zero (hC : ∀ c, ν (C c) = w₀ (C c))
    (hle : ∀ f, ν f ≤ w₀ f) {F : K[X]} (hF : F ≠ 0) (hF0 : ν F = 0) :
    Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ ν := by
  rcases exists_macLaneVaquie_seq_or_forall_isStable hC hle with
    ⟨w, hw0, hstep, hagree⟩ | ⟨μ, -, hne, ι, _, _, _, G, hν, hlow, hst⟩
  · have hrt : ∀ n, Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ (w n) := by
      intro n
      induction n with
      | zero => rw [hw0]
      | succ n ih => exact ih.trans (hstep n)
    have hD : ∀ f : K[X], f.degree < ((F.natDegree + 1 : ℕ) : WithBot ℕ) →
        w F.natDegree f = ν f := by
      intro f hf
      refine hagree _ f ?_
      by_cases h0 : f = 0
      · rw [h0, natDegree_zero]
        exact Nat.zero_le _
      · exact Nat.lt_succ_iff.1 ((natDegree_lt_iff_degree_lt h0).2 hf)
    have hFD : F.degree < ((F.natDegree + 1 : ℕ) : WithBot ℕ) :=
      degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_self _)
    have hr := hrt F.natDegree
    rwa [eq_of_map_eq_zero_of_degree_lt hD hF hFD hF0] at hr
  · exact absurd (hst F).1 (ContinuousFamily.not_isStable_of_map_eq_zero hν hlow hne hF hF0)

/-- Part 4 of the theorem of MacLane-Vaquié for a valuation with nonzero support, from the first valuation `[v; X, ν(X)]` of the chain. -/
theorem reflTransGen_monomialValuation_of_map_eq_zero {v : Valuation K Γ₀}
    (hν : ∀ a, ν (C a) = v a) {F : K[X]} (hF : F ≠ 0) (hF0 : ν F = 0) :
    Relation.ReflTransGen (MacLaneVaquieStep ν) (monomialValuation v (ν X)) ν :=
  reflTransGen_macLaneVaquieStep_of_map_eq_zero (fun c => by rw [monomialValuation_C, hν])
    (map_le_monomialValuation hν) hF hF0

end Support

section KeyPolynomial

variable {ν w : Valuation K[X] Γ₀}

/-- Let `φ` be monic of positive degree and `ν`-minimal. Let `w ≤ ν` in additive notation, and let `w` agree with `ν` in degree less than the degree of `φ` and at `φ`. Then `w = ν`. By the expansion criterion, `ν(f)` is the minimum of `ν(aⱼ) + jν(φ)` in additive notation for the `φ`-expansion `f = ∑ aⱼ φ ^ j`, and `w(f)` is at least this minimum. -/
theorem eq_of_isMuMinimal (hle : ∀ f, ν f ≤ w f) {φ : K[X]} (hm : φ.Monic)
    (hd : 0 < φ.natDegree) (hmin : IsMuMinimal ν φ)
    (hlow : ∀ a : K[X], a.degree < φ.degree → w a = ν a) (hφ : w φ = ν φ) : w = ν := by
  refine Valuation.ext fun f => le_antisymm ?_ (hle f)
  calc w f ≤ augmentedValuationFun w φ (w φ) f := map_le_augmentedValuationFun hm hd f
    _ = augmentedValuationFun ν φ (ν φ) f := by
      unfold augmentedValuationFun
      rw [hφ]
      refine Finset.sup_congr rfl fun j _ => ?_
      rw [hlow _ (degree_expansionCoeff_lt hm f j)]
    _ = ν f := (hmin.map_eq_augmentedValuationFun hm hd f).symm

/-- The last step of a chain of MacLane-Vaquié gives a key polynomial. If one step of MacLane-Vaquié leads from `μ` to `μ'`, then the key polynomial `φ` of the step is a key polynomial for `μ'`. This holds for an ordinary step and for a limit step, and also if `μ'(φ) = ∞`. -/
theorem MacLaneVaquieStep.exists_keyPolynomial {μ μ' : Valuation K[X] Γ₀}
    (h : MacLaneVaquieStep ν μ μ') : ∃ φ, KeyPolynomial μ' φ := by
  rcases h with ⟨φ, hle, hφ, hlt, hlow, h⟩ | ⟨ι, F, hν, hlow, φ, hφ, hdeg, h⟩
  · exact ⟨φ, (keyPolynomial_of_map_lt hle hφ hlt hlow).keyPolynomial_of_forall_eq h⟩
  · exact ⟨φ, hφ.keyPolynomial_of_forall_eq h⟩

/-- Let finitely many steps of MacLane-Vaquié lead from `w₀` to `μ ≠ w₀`. Then `μ` has a key polynomial: the key polynomial of the last step. -/
theorem exists_keyPolynomial_of_reflTransGen {w₀ μ : Valuation K[X] Γ₀}
    (h : Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ μ) (hne : w₀ ≠ μ) :
    ∃ φ, KeyPolynomial μ φ := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨c, -, hs⟩
  · exact absurd rfl hne
  · exact hs.exists_keyPolynomial

end KeyPolynomial

namespace ContinuousFamily

variable {μ ν : Valuation K[X] Γ₀} {ι : Type*} [LinearOrder ι] [Nonempty ι] [NoMaxOrder ι]
  {F : ContinuousFamily μ ι}

/-- Let `φ` be a monic `ν`-minimal polynomial of positive degree. Let `(μᵢ)` be a continuous family of augmentations of `μ ≠ ν` below `ν`, and let `ν` agree with `μ` in degree less than the degree `d` of the family. Then some polynomial is not stable. Thus `ν` is not the limit of the family.

If `deg φ < d`, then `μ` agrees with `ν` in degree less than `deg φ` and at `φ`, so `μ = ν` by `eq_of_isMuMinimal`. Let `deg φ ≥ d`, and assume that `φ` is stable. Then `μⱼ(φ) = ν(φ)` for `j` large. Let `r` be the remainder of `φ` modulo `φⱼ`. Then `μⱼ(φ - r) > μⱼ(φ)` in additive notation (`val_sub_modByMonic_lt`). Since `deg r < deg φ`, the polynomial `φ` is not `ν`-equivalent to `r`, so `ν(φ - r) = min(ν(r), ν(φ)) ≤ ν(φ)`. With `ν(φ - r) ≥ μⱼ(φ - r)` this is a contradiction. -/
theorem not_forall_isStable_of_isMuMinimal
    (hν : ∀ i f, ν f ≤ augmentedValuationFun μ (F.key i) (F.value i) f)
    (hlow : ∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = μ a) (hne : μ ≠ ν)
    {φ : K[X]} (hm : φ.Monic) (hd : 0 < φ.natDegree) (hmin : IsMuMinimal ν φ) :
    ¬ ∀ f, F.IsStable f := by
  intro hst
  obtain ⟨i⟩ := ‹Nonempty ι›
  by_cases hdeg : φ.degree < (F.key i).degree
  · refine hne (eq_of_isMuMinimal (fun f => ?_) hm hd hmin
      (fun a ha => (hlow i a (ha.trans hdeg)).symm) (hlow i φ hdeg).symm)
    exact (hν i f).trans (augmentedValuation_le (F.keyPolynomial i) (F.value_lt i).le f)
  push Not at hdeg
  by_cases h0 : ν φ = 0
  · exact not_isStable_of_map_eq_zero hν hlow hne hm.ne_zero h0 (hst φ)
  obtain ⟨i₀, hi₀⟩ := (hst φ).exists_forall_eq
  obtain ⟨j, hj⟩ := exists_gt i₀
  have hs := F.stableValue_eq_of_isStable hν hlow (hst φ)
  have hvi : F.val i₀ φ = ν φ := (hi₀ i₀ le_rfl).trans hs
  have hvj : F.val j φ = ν φ := (hi₀ j hj.le).trans hs
  have hlt := F.val_sub_modByMonic_lt hj (hvi.trans hvj.symm) (by rw [hvj]; exact h0)
  have hr : (-(φ %ₘ F.key j)).degree < φ.degree := by
    rw [degree_neg]
    exact (degree_modByMonic_lt φ (F.keyPolynomial j).monic).trans_le
      ((F.degree_key_eq j i).trans_le hdeg)
  have hmax := hmin.map_add_mul_eq_max hr 1
  rw [mul_one, neg_add_eq_sub] at hmax
  have h1 : ν φ ≤ ν (φ - φ %ₘ F.key j) := by
    rw [hmax]
    exact le_max_right _ _
  exact lt_irrefl _ ((h1.trans (hν j _)).trans_lt (hlt.trans_eq hvj))

end ContinuousFamily

section Finite

variable {ν w₀ : Valuation K[X] Γ₀}

/-- Let `ν` agree with `w₀` on the constants, let `w₀ ≤ ν` in additive notation, and let `φ` be a monic `ν`-minimal polynomial of positive degree. Then finitely many steps of MacLane-Vaquié lead from `w₀` to `ν`. The value group and the support of `ν` are arbitrary.

In the first case of `exists_macLaneVaquie_seq_or_forall_isStable`, the valuation `w_{deg φ}` agrees with `ν` in degree at most `deg φ`, so it is `ν` by `eq_of_isMuMinimal`. The second case does not hold by `ContinuousFamily.not_forall_isStable_of_isMuMinimal`. -/
theorem reflTransGen_macLaneVaquieStep_of_isMuMinimal (hC : ∀ c, ν (C c) = w₀ (C c))
    (hle : ∀ f, ν f ≤ w₀ f) {φ : K[X]} (hm : φ.Monic) (hd : 0 < φ.natDegree)
    (hmin : IsMuMinimal ν φ) : Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ ν := by
  rcases exists_macLaneVaquie_seq_or_forall_isStable hC hle with
    ⟨w, hw0, hstep, hagree⟩ | ⟨μ, -, hne, ι, _, _, _, G, hν, hlow, hst⟩
  · have hrt : ∀ n, Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ (w n) := by
      intro n
      induction n with
      | zero => rw [hw0]
      | succ n ih => exact ih.trans (hstep n)
    have hr := hrt φ.natDegree
    have heq := eq_of_isMuMinimal (macLaneBelow_of_reflTransGen hr hC hle).2 hm hd hmin
      (fun a ha => hagree _ a (natDegree_le_natDegree ha.le)) (hagree _ φ le_rfl)
    rwa [heq] at hr
  · exact absurd (fun f => (hst f).1)
      (ContinuousFamily.not_forall_isStable_of_isMuMinimal hν hlow hne hm hd hmin)

/-- The criterion for a finite chain of MacLane-Vaquié. Let `ν` agree with `w₀` on the constants, let `w₀ ≤ ν` in additive notation, and let `w₀ ≠ ν`. Then finitely many steps of MacLane-Vaquié lead from `w₀` to `ν` if and only if `ν` has a key polynomial. The value group and the support of `ν` are arbitrary. -/
theorem reflTransGen_macLaneVaquieStep_iff_exists_keyPolynomial (hC : ∀ c, ν (C c) = w₀ (C c))
    (hle : ∀ f, ν f ≤ w₀ f) (hne : w₀ ≠ ν) :
    Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ ν ↔ ∃ φ, KeyPolynomial ν φ :=
  ⟨fun h => exists_keyPolynomial_of_reflTransGen h hne, fun ⟨_, hφ⟩ =>
    reflTransGen_macLaneVaquieStep_of_isMuMinimal hC hle hφ.monic hφ.natDegree_pos
      hφ.isMuMinimal⟩

/-- Part 4 of the theorem of MacLane-Vaquié with the three cases. Let `ν` agree with `w₀` on the constants, and let `w₀ ≤ ν` in additive notation. Then one of three cases holds. In the first case, finitely many steps of MacLane-Vaquié lead from `w₀` to `ν`. Otherwise `ν` has no key polynomial, and one of two cases holds. In the second case, there is a sequence `wₙ` with `w₀` at the start and finitely many steps from `wₙ` to `wₙ₊₁`, such that `wₙ` agrees with `ν` in degree at most `n` and `wₙ ≠ ν` for each `n`. Thus `ν` is the limit of an infinite chain. In the third case, finitely many steps lead from `w₀` to a valuation `μ ≠ ν`, and `ν` is the limit of a continuous family of augmentations of `μ`: each polynomial is stable, and its limit value is its value for `ν`. The value group and the support of `ν` are arbitrary. If `ν` has nonzero support, the first case holds (`reflTransGen_macLaneVaquieStep_of_map_eq_zero`). -/
theorem reflTransGen_macLaneVaquieStep_or_forall_not_keyPolynomial
    (hC : ∀ c, ν (C c) = w₀ (C c)) (hle : ∀ f, ν f ≤ w₀ f) :
    Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ ν ∨
      ((∀ φ, ¬ KeyPolynomial ν φ) ∧
        ((∃ w : ℕ → Valuation K[X] Γ₀, w 0 = w₀ ∧
            (∀ n, Relation.ReflTransGen (MacLaneVaquieStep ν) (w n) (w (n + 1))) ∧
            (∀ n (f : K[X]), f.natDegree ≤ n → w n f = ν f) ∧ ∀ n, w n ≠ ν) ∨
          ∃ μ : Valuation K[X] Γ₀, Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ μ ∧ μ ≠ ν ∧
            ∃ (ι : Type uV) (_ : LinearOrder ι) (_ : Nonempty ι) (_ : NoMaxOrder ι)
              (F : ContinuousFamily μ ι),
              (∀ i f, ν f ≤ augmentedValuationFun μ (F.key i) (F.value i) f) ∧
              (∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = μ a) ∧
              ∀ f, F.IsStable f ∧ F.stableValue f = ν f)) := by
  by_cases hR : Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ ν
  · exact Or.inl hR
  refine Or.inr ⟨fun φ hφ => hR (reflTransGen_macLaneVaquieStep_of_isMuMinimal hC hle hφ.monic
    hφ.natDegree_pos hφ.isMuMinimal), ?_⟩
  rcases exists_macLaneVaquie_seq_or_forall_isStable hC hle with
    ⟨w, hw0, hstep, hagree⟩ | hB
  · refine Or.inl ⟨w, hw0, hstep, hagree, fun n hn => hR ?_⟩
    have hrt : ∀ n, Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ (w n) := by
      intro n
      induction n with
      | zero => rw [hw0]
      | succ n ih => exact ih.trans (hstep n)
    have h := hrt n
    rwa [hn] at h
  · exact Or.inr hB

end Finite

end Singularity
