/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.MacLaneUnique

/-!
# The limit augmentation of Vaquié for a continuous family

This file constructs the limit augmentation of Vaquié [Vaq07] for a continuous family of augmented valuations of constant degree. It continues `Singularity/Valuation/MacLaneChain.lean`, where the chain of MacLane is built by ordinary augmentations only.

The conventions are those of `Singularity/Valuation/KeyPolynomials.lean`. The valuations are multiplicative. Thus `μ ≤ ν` in the additive notation of the handbook is `∀ f, ν f ≤ μ f` here, the value `∞` is `0`, and a supremum of additive values is an infimum here.

A continuous family (`ContinuousFamily μ ι`) is a family of augmentations `μᵢ = [μ; φᵢ, γᵢ]` of one valuation `μ` on `K[X]`, indexed by a totally ordered set `ι`. The `φᵢ` are key polynomials for `μ` of one degree `d`, with `γᵢ < μ φᵢ`. In additive notation, `γᵢ > μ(φᵢ)`, the values `γᵢ` increase strictly, and `μ(φⱼ - φᵢ) ≥ γᵢ` for `i < j`. Then `μᵢ = [μ; φⱼ, γᵢ]` for `i ≤ j`, and the family increases: `μᵢ ≤ μⱼ` in additive notation. In [Vaq07] and [HMOS22] the index set is well ordered without a last element. The file only needs a total order. The results on the limit use `[Nonempty ι]` and `[NoMaxOrder ι]`.

A polynomial `f` is stable (`ContinuousFamily.IsStable`) if `μᵢ f` is constant for `i` large. The limit `μ_∞ f` (`ContinuousFamily.stableValue`) is this constant value. For an unstable `f` the file sets `μ_∞ f = 0`, that is `∞` in additive notation. Thus `μ_∞` is a function on all of `K[X]`, and it is the supremum of the `μᵢ` (in additive notation) on the stable polynomials.

The limit key polynomials (`ContinuousFamily.IsLimitKeyPolynomial`) are the monic polynomials of least degree among the unstable polynomials. The limit augmentation (`ContinuousFamily.limitAugmentedValuationFun`) is `[μ_∞; φ, γ] f = max_j μ_∞ aⱼ * γ ^ j` for the `φ`-expansion `f = ∑ aⱼ φ ^ j`. In additive notation this is `min_j (μ_∞(aⱼ) + jγ)`.

## The proof

* Let `i < j` and `μᵢ f = μⱼ f ≠ 0`. Since `μᵢ = [μ; φⱼ, γᵢ]` and `γⱼ < γᵢ` in multiplicative notation, the terms `aₖ φⱼ ^ k` with `k ≥ 1` of the `φⱼ`-expansion of `f` have `μⱼ` value less than `μᵢ f`. So `f` is `μⱼ`-equivalent to its remainder `r` modulo `φⱼ`, and `μₖ f = μ r` for each `k ≥ j` (`ContinuousFamily.val_eq_of_val_eq`). Thus a polynomial is either stable, or its values `μᵢ f` decrease strictly (`ContinuousFamily.not_isStable_iff`).
* Let `μᵢ ≤ ν` for each `i` in additive notation, and let `ν` agree with `μ` in degree less than `d`. For a stable `f` the remainder `r` above has `ν r = μ r = μ_∞ f`, and `ν (f - r) < ν r`. So `ν f = μ_∞ f` (`ContinuousFamily.stableValue_eq_of_isStable`). Since `μᵢ ≤ ν` and the family increases strictly, `μᵢ ≠ ν` for each `i`. So "the family does not reach `ν`" means that some `f` has `μᵢ f ≠ ν f` for each `i`. This holds if and only if some polynomial is unstable (`ContinuousFamily.exists_not_isStable_iff`).
* The products of stable polynomials are stable, and the constants are stable. So a monic polynomial of least degree among the unstable polynomials exists if an unstable polynomial exists. It is a limit key polynomial `φ`. The degree of `φ` is at least `d`, and the polynomials of degree less than the degree of `φ` are stable. The polynomial `φ` divides `f` in the limit (`ContinuousFamily.LimitDvd`, the `μᵢ`-divisibility for `i` large) if and only if `f` is unstable. So `φ` is irreducible and minimal in the limit, as in the definition of [Vaq07].
* For the limit augmentation, let `γ ≤ μᵢ φ` for each `i` in multiplicative notation, that is `γ ≥ μᵢ(φ)` for each `i` in additive notation. On the polynomials of degree less than the degree of `φ`, the function `μ_∞` is multiplicative and ultrametric, since finitely many stable polynomials are stable from one index on. The key lemma for the limit is the following. If `f` and its quotient `q` by `φ` are stable, then `μ_∞ (f %ₘ φ) = μ_∞ f` and `μ_∞ q * γ ≤ μ_∞ f`. The first claim uses that `μᵢ φ` decreases strictly. Then the proof of multiplicativity for an ordinary augmentation applies with `μ_∞` in place of `μ`.
* For `μᵢ ≤ [μ_∞; φ, γ]` it is sufficient to show `[μ_∞; φ, γ] φᵢ ≤ γᵢ`. If the degree of `φᵢ` is less than the degree of `φ`, this is `μ_∞ φᵢ ≤ μᵢ φᵢ = γᵢ`. If the degrees are equal, let `a = φ - φᵢ`. If `γᵢ < μ a`, then `μⱼ φ = μ a` for each `j ≥ i` and `φ` is stable, a contradiction. So `μ a ≤ γᵢ`, and `[μ_∞; φ, γ] φᵢ ≤ max (γ, μ a) ≤ γᵢ`.
* For `[μ_∞; φ, γ] ≤ ν` with `ν φ ≤ γ`, the `φ`-expansion gives `ν f ≤ max_j ν aⱼ * (ν φ) ^ j ≤ max_j μ_∞ aⱼ * γ ^ j`. The choice `γ = ν φ` satisfies both conditions on `γ`.

## Main results

* `Singularity.ContinuousFamily.stableValue_eq_of_isStable`: if `μᵢ ≤ ν` for each `i` and `ν` agrees with `μ` in degree less than `d`, then `μ_∞ f = ν f` for each stable `f`.
* `Singularity.ContinuousFamily.exists_not_isStable_iff`: under the same hypotheses, some polynomial is unstable if and only if some `f` has `μᵢ f ≠ ν f` for each `i`.
* `Singularity.ContinuousFamily.exists_isLimitKeyPolynomial`: if some polynomial is unstable, then a limit key polynomial exists.
* `Singularity.ContinuousFamily.IsLimitKeyPolynomial.limitDvd_iff`: a limit key polynomial divides `f` in the limit if and only if `f` is unstable. The consequences are `IsLimitKeyPolynomial.not_limitDvd_one`, `IsLimitKeyPolynomial.limitDvd_or_limitDvd` and `IsLimitKeyPolynomial.natDegree_le_of_limitDvd`.
* `Singularity.ContinuousFamily.IsLimitKeyPolynomial.limitAugmentedValuationFun_mul` and `Singularity.ContinuousFamily.IsLimitKeyPolynomial.limitAugmentedValuationFun_add_le_max`: the limit augmentation is a valuation (`ContinuousFamily.limitAugmentedValuation`).
* `Singularity.ContinuousFamily.IsLimitKeyPolynomial.limitAugmentedValuationFun_le`: `μᵢ ≤ [μ_∞; φ, γ]` for each `i` in additive notation.
* `Singularity.ContinuousFamily.IsLimitKeyPolynomial.map_le_limitAugmentedValuationFun`: `[μ_∞; φ, γ] ≤ ν` in additive notation if `γ ≤ ν(φ)`. The case `γ = ν(φ)` is `IsLimitKeyPolynomial.limitAugmentedValuationFun_map_le`.

## What the file does not prove

The file does not prove that `φ` is a key polynomial for `[μ_∞; φ, γ]`, and it does not treat the graded algebra of the limit augmentation. It does not prove that each limit key polynomial in the sense of [Vaq07] is a monic polynomial of least degree among the unstable polynomials. It only proves the properties of the converse direction above. It does not build the full chain of MacLane-Vaquié with limit steps, and it does not prove that this chain reaches `ν`. The hypothesis that `ν` agrees with `μ` in degree less than `d` is assumed. It holds in the construction of the family below `ν` in [Vaq07], but the file does not derive it from `μᵢ ≤ ν`.

## References

* [Vaq07] M. Vaquié, Extension d'une valuation.
* [HMOS22] F. J. Herrera Govantes, W. Mahboub, M. A. Olalla Acosta and M. Spivakovsky, Key polynomials for simple extensions of valued fields.
-/

open Polynomial

namespace Singularity

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- If `v x ≠ v (x + y)`, then `v y` is the maximum of `v x` and `v (x + y)`. -/
theorem valuation_eq_max_of_ne {R : Type*} [Ring R] (v : Valuation R Γ₀) {x y : R}
    (h : v x ≠ v (x + y)) : v y = max (v x) (v (x + y)) := by
  rcases lt_trichotomy (v y) (v x) with hlt | heq | hgt
  · exact absurd (v.map_add_eq_of_lt_left hlt).symm h
  · have hle : v (x + y) ≤ v x := (v.map_add x y).trans (max_eq_left heq.le).le
    rw [max_eq_left hle, heq]
  · rw [v.map_add_eq_of_lt_right hgt, max_eq_right hgt.le]

/-- A continuous family of augmented valuations of constant degree (Vaquié, [Vaq07]). The index set `ι` is totally ordered. The family consists of the augmentations `μᵢ = [μ; φᵢ, γᵢ]` of one valuation `μ`, where the `φᵢ` are key polynomials for `μ` of one degree `d`, and `γᵢ < μ φᵢ`. In additive notation the values `γᵢ` increase strictly, and `μ(φⱼ - φᵢ) ≥ γᵢ` for `i < j`. The last condition says that `μᵢ = [μ; φⱼ, γᵢ]` for `i < j` (`ContinuousFamily.val_apply_eq_of_le`). It gives `μᵢ ≤ μⱼ` in additive notation (`ContinuousFamily.val_le_val`). -/
structure ContinuousFamily (μ : Valuation K[X] Γ₀) (ι : Type*) [LinearOrder ι] where
  /-- The key polynomial `φᵢ`. -/
  key : ι → K[X]
  /-- The value `γᵢ`. -/
  value : ι → Γ₀
  keyPolynomial : ∀ i, KeyPolynomial μ (key i)
  natDegree_eq : ∀ i j, (key i).natDegree = (key j).natDegree
  value_lt : ∀ i, value i < μ (key i)
  value_strictAnti : StrictAnti value
  map_sub_le : ∀ i j, i < j → μ (key j - key i) ≤ value i

namespace ContinuousFamily

variable {μ : Valuation K[X] Γ₀} {ι : Type*} [LinearOrder ι] (F : ContinuousFamily μ ι)

/-- The polynomial `f` is stable for the family if the value `μᵢ f` is constant for `i` large. -/
def IsStable (f : K[X]) : Prop :=
  ∃ i, ∀ j, i ≤ j → augmentedValuationFun μ (F.key j) (F.value j) f =
    augmentedValuationFun μ (F.key i) (F.value i) f

open Classical in
/-- The limit `μ_∞ f` of the family. It is the eventual value `μᵢ f` if `f` is stable, and `0` otherwise. In additive notation the value `0` is `∞`, so this is the convention `μ_∞ f = ∞` for an unstable `f`. The stable value is the supremum of the values `μᵢ f` in additive notation (`ContinuousFamily.stableValue_le`). -/
noncomputable def stableValue (f : K[X]) : Γ₀ :=
  if h : F.IsStable f then augmentedValuationFun μ (F.key h.choose) (F.value h.choose) f else 0

/-- A limit key polynomial for the family (Vaquié, [Vaq07]). It is a monic polynomial of least degree among the polynomials that are not stable. -/
structure IsLimitKeyPolynomial (φ : K[X]) : Prop where
  monic : φ.Monic
  not_isStable : ¬ F.IsStable φ
  natDegree_le : ∀ f, ¬ F.IsStable f → φ.natDegree ≤ f.natDegree

/-- The polynomial `φ` divides `f` in the limit (Vaquié, [Vaq07]). There is an index `i` such that `φ` `μⱼ`-divides `f` for each `j ≥ i`: `μⱼ (f - φ * h) < μⱼ f` for some `h`. -/
def LimitDvd (φ f : K[X]) : Prop :=
  ∃ i, ∀ j, i ≤ j → ∃ h : K[X], augmentedValuationFun μ (F.key j) (F.value j) (f - φ * h) <
    augmentedValuationFun μ (F.key j) (F.value j) f

/-- The limit augmentation `[μ_∞; φ, γ]` as a function (Vaquié, [Vaq07]). For the `φ`-expansion `f = ∑ aⱼ φ ^ j`, its value is the maximum of `μ_∞ aⱼ * γ ^ j`. In additive notation, `min_j (μ_∞(aⱼ) + jγ)`. -/
noncomputable def limitAugmentedValuationFun (φ : K[X]) (γ : Γ₀) (f : K[X]) : Γ₀ :=
  (Finset.range (f.natDegree + 1)).sup fun j => F.stableValue (expansionCoeff φ f j) * γ ^ j

section Basic

/-- The valuation `μᵢ = [μ; φᵢ, γᵢ]` of the family. -/
noncomputable def val (i : ι) : Valuation K[X] Γ₀ :=
  augmentedValuation μ (F.key i) (F.value i) (F.keyPolynomial i) (F.value_lt i).le

variable {F}

theorem val_apply (i : ι) (f : K[X]) :
    F.val i f = augmentedValuationFun μ (F.key i) (F.value i) f :=
  rfl

theorem isStable_iff {f : K[X]} : F.IsStable f ↔ ∃ i, ∀ j, i ≤ j → F.val j f = F.val i f :=
  Iff.rfl

theorem limitDvd_iff_muDvd {φ f : K[X]} :
    F.LimitDvd φ f ↔ ∃ i, ∀ j, i ≤ j → MuDvd (F.val j) φ f :=
  Iff.rfl

/-- The key polynomials of the family have one degree. -/
theorem degree_key_eq (i j : ι) : (F.key i).degree = (F.key j).degree := by
  rw [degree_eq_natDegree (F.keyPolynomial i).monic.ne_zero,
    degree_eq_natDegree (F.keyPolynomial j).monic.ne_zero, F.natDegree_eq i j]

/-- For `i < j`, the key polynomials `φᵢ` and `φⱼ` have the same value for `μ`. -/
theorem map_key_eq_of_lt {i j : ι} (h : i < j) : μ (F.key j) = μ (F.key i) := by
  have hequiv : MuEquiv μ (F.key i) (F.key j) := by
    unfold MuEquiv
    rw [Valuation.map_sub_swap]
    exact (F.map_sub_le i j h).trans_lt (F.value_lt i)
  exact hequiv.map_eq.symm

/-- For `i ≤ j`, the valuation `μᵢ` is the augmentation `[μ; φⱼ, γᵢ]`. -/
theorem val_apply_eq_of_le {i j : ι} (h : i ≤ j) (f : K[X]) :
    F.val i f = augmentedValuationFun μ (F.key j) (F.value i) f := by
  rcases h.lt_or_eq with h | rfl
  · rw [val_apply]
    exact (F.keyPolynomial i).augmentedValuationFun_eq_of_map_sub_le (F.keyPolynomial j)
      (F.natDegree_eq j i) (F.value_lt i).le
      ((F.value_lt i).le.trans_eq (F.map_key_eq_of_lt h).symm) (F.map_sub_le i j h) f
  · rfl

/-- The family is increasing: `μᵢ ≤ μⱼ` for `i ≤ j` in additive notation. -/
theorem val_le_val {i j : ι} (h : i ≤ j) (f : K[X]) : F.val j f ≤ F.val i f := by
  rw [val_apply_eq_of_le h, val_apply]
  exact augmentedValuationFun_mono (F.keyPolynomial j).monic (F.keyPolynomial j).natDegree_pos
    (F.value_strictAnti.antitone h) f

/-- For `i ≤ j`, the value `μᵢ φⱼ` is `γᵢ`. -/
theorem val_key_of_le {i j : ι} (h : i ≤ j) : F.val i (F.key j) = F.value i := by
  rw [val_apply_eq_of_le h]
  exact augmentedValuationFun_self (F.keyPolynomial j).monic (F.keyPolynomial j).natDegree_pos

/-- The valuations of the family agree with `μ` in degree less than `d`. -/
theorem val_of_degree_lt {i : ι} {a : K[X]} (ha : a.degree < (F.key i).degree) (j : ι) :
    F.val j a = μ a :=
  augmentedValuation_of_degree_lt _ _ (by rwa [F.degree_key_eq j i])

/-- The key lemma. Let `i < j` and `μᵢ f = μⱼ f ≠ 0`. Then `f` is `μⱼ`-equivalent to its remainder modulo `φⱼ`. -/
theorem val_sub_modByMonic_lt {i j : ι} (hij : i < j) {f : K[X]} (h : F.val i f = F.val j f)
    (hf : F.val j f ≠ 0) : F.val j (f - f %ₘ F.key j) < F.val j f := by
  have hm := (F.keyPolynomial j).monic
  have hd := (F.keyPolynomial j).natDegree_pos
  have hγ : F.value j < F.value i := F.value_strictAnti hij
  have hpos : 0 < F.val j f := zero_lt_iff.2 hf
  rw [show f - f %ₘ F.key j = F.key j * (f /ₘ F.key j) from
    (eq_sub_of_add_eq' (modByMonic_add_div f (F.key j))).symm]
  obtain ⟨k, hk⟩ := exists_eq_augmentedValuationFun (μ := μ) (φ := F.key j) (γ := F.value j)
    (F.key j * (f /ₘ F.key j))
  rw [val_apply, ← hk]
  cases k with
  | zero =>
    rw [expansionCoeff_mul_left_zero hm, Valuation.map_zero, zero_mul]
    exact hpos
  | succ k =>
    rw [expansionCoeff_mul_left_succ hm, ← expansionCoeff_succ]
    by_cases h0 : μ (expansionCoeff (F.key j) f (k + 1)) = 0
    · rw [h0, zero_mul]
      exact hpos
    calc μ (expansionCoeff (F.key j) f (k + 1)) * F.value j ^ (k + 1)
        < μ (expansionCoeff (F.key j) f (k + 1)) * F.value i ^ (k + 1) :=
          mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hγ zero_le k.succ_ne_zero)
            (zero_lt_iff.2 h0)
      _ ≤ augmentedValuationFun μ (F.key j) (F.value i) f := le_augmentedValuationFun hm hd f _
      _ = F.val j f := by rw [← val_apply_eq_of_le hij.le, h]

/-- The dichotomy. If `μᵢ f = μⱼ f` for some `i < j`, then `μₖ f = μᵢ f` for each `k ≥ i`. -/
theorem val_eq_of_val_eq {i j : ι} (hij : i < j) {f : K[X]} (h : F.val i f = F.val j f) {k : ι}
    (hk : i ≤ k) : F.val k f = F.val i f := by
  rcases le_total k j with hkj | hjk
  · exact le_antisymm (F.val_le_val hk f) (h.trans_le (F.val_le_val hkj f))
  by_cases hf : F.val j f = 0
  · rw [h, hf]
    exact le_zero_iff.1 ((F.val_le_val hjk f).trans_eq hf)
  set r := f %ₘ F.key j
  have hr : r.degree < (F.key j).degree := degree_modByMonic_lt f (F.keyPolynomial j).monic
  have hlt := F.val_sub_modByMonic_lt hij h hf
  have hrj : F.val j r = F.val j f := by
    have := (show MuEquiv (F.val j) f r from hlt).map_eq
    exact this.symm
  have hrk : F.val k r = F.val j r := by
    rw [F.val_of_degree_lt hr k, F.val_of_degree_lt hr j]
  have hlt' : F.val k (f - r) < F.val k r := by
    rw [hrk, hrj]
    exact (F.val_le_val hjk _).trans_lt hlt
  calc F.val k f = F.val k (r + (f - r)) := by rw [add_sub_cancel]
    _ = F.val k r := Valuation.map_add_eq_of_lt_left _ hlt'
    _ = F.val i f := by rw [hrk, hrj, h]

end Basic

section Stable

variable {F}

/-- If `f` is not stable, then the values `μᵢ f` decrease strictly. In additive notation, `μᵢ(f) < μⱼ(f)` for `i < j`. -/
theorem val_lt_val_of_not_isStable {f : K[X]} (hf : ¬ F.IsStable f) {i j : ι} (hij : i < j) :
    F.val j f < F.val i f :=
  lt_of_le_of_ne (F.val_le_val hij.le f) fun h => hf ⟨i, fun _ hk => F.val_eq_of_val_eq hij h.symm hk⟩

/-- A polynomial is not stable if and only if its values decrease strictly. -/
theorem not_isStable_iff [NoMaxOrder ι] {f : K[X]} :
    ¬ F.IsStable f ↔ ∀ i j, i < j → F.val j f < F.val i f := by
  refine ⟨fun hf i j hij => F.val_lt_val_of_not_isStable hf hij, fun h ⟨i, hi⟩ => ?_⟩
  obtain ⟨j, hij⟩ := exists_gt i
  exact (h i j hij).ne (hi j hij.le)

/-- A stable polynomial has the value `μ_∞ f` for all large indices. -/
theorem IsStable.exists_forall_eq {f : K[X]} (hf : F.IsStable f) :
    ∃ i, ∀ j, i ≤ j → F.val j f = F.stableValue f := by
  refine ⟨hf.choose, fun j hj => ?_⟩
  rw [stableValue, dite_eq_left hf]
  exact hf.choose_spec j hj

/-- If `μⱼ f = c` for all `j ≥ i`, then `f` is stable with `μ_∞ f = c`. -/
theorem stableValue_eq_of_forall {f : K[X]} {i : ι} {c : Γ₀}
    (h : ∀ j, i ≤ j → F.val j f = c) : F.IsStable f ∧ F.stableValue f = c := by
  have hs : F.IsStable f := ⟨i, fun j hj => (h j hj).trans (h i le_rfl).symm⟩
  obtain ⟨i', hi'⟩ := hs.exists_forall_eq
  exact ⟨hs, (hi' (max i i') (le_max_right _ _)).symm.trans (h _ (le_max_left _ _))⟩

/-- The limit is the supremum of the family in additive notation: `μ_∞ f ≤ μᵢ f` in multiplicative notation. -/
theorem stableValue_le (f : K[X]) (i : ι) : F.stableValue f ≤ F.val i f := by
  by_cases hf : F.IsStable f
  · obtain ⟨i', hi'⟩ := hf.exists_forall_eq
    rw [← hi' (max i i') (le_max_right _ _)]
    exact F.val_le_val (le_max_left _ _) f
  · rw [stableValue, dite_eq_right hf]
    exact zero_le

theorem stableValue_zero : F.stableValue 0 = 0 := by
  rw [stableValue]
  split_ifs
  exacts [augmentedValuationFun_zero, rfl]

/-- A polynomial of degree less than `d` is stable, with the value `μ a`. -/
theorem stableValue_of_degree_lt {i : ι} {a : K[X]} (ha : a.degree < (F.key i).degree) :
    F.IsStable a ∧ F.stableValue a = μ a :=
  stableValue_eq_of_forall (i := i) fun j _ => F.val_of_degree_lt ha j

theorem isStable_zero [Nonempty ι] : F.IsStable 0 :=
  (stableValue_eq_of_forall (F := F) (i := Classical.arbitrary ι) fun _ _ =>
    Valuation.map_zero _).1

theorem stableValue_one [Nonempty ι] : F.IsStable 1 ∧ F.stableValue 1 = 1 :=
  stableValue_eq_of_forall (i := Classical.arbitrary ι) fun _ _ => Valuation.map_one _

theorem stableValue_C [Nonempty ι] (c : K) : F.IsStable (C c) ∧ F.stableValue (C c) = μ (C c) :=
  stableValue_of_degree_lt (i := Classical.arbitrary ι) (degree_C_le.trans_lt
    (natDegree_pos_iff_degree_pos.1 (F.keyPolynomial _).natDegree_pos))

/-- The product of two stable polynomials is stable, and `μ_∞` is multiplicative on them. -/
theorem IsStable.stableValue_mul {f g : K[X]} (hf : F.IsStable f) (hg : F.IsStable g) :
    F.IsStable (f * g) ∧ F.stableValue (f * g) = F.stableValue f * F.stableValue g := by
  obtain ⟨i, hi⟩ := hf.exists_forall_eq
  obtain ⟨i', hi'⟩ := hg.exists_forall_eq
  exact stableValue_eq_of_forall (i := max i i') fun j hj => by
    rw [Valuation.map_mul, hi j (le_of_max_le_left hj), hi' j (le_of_max_le_right hj)]

/-- For finitely many stable polynomials, there is a common index of stability. -/
theorem exists_forall_val_eq [Nonempty ι] (s : Finset K[X]) (hs : ∀ f ∈ s, F.IsStable f) :
    ∃ i, ∀ j, i ≤ j → ∀ f ∈ s, F.val j f = F.stableValue f := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary ι, fun _ _ f hf => by simp at hf⟩
  | insert a s ha ih =>
    obtain ⟨i, hi⟩ := ih fun f hf => hs f (Finset.mem_insert_of_mem hf)
    obtain ⟨i', hi'⟩ := (hs a (Finset.mem_insert_self a s)).exists_forall_eq
    refine ⟨max i i', fun j hj f hf => ?_⟩
    rcases Finset.mem_insert.1 hf with rfl | hf
    · exact hi' j (le_of_max_le_right hj)
    · exact hi j (le_of_max_le_left hj) f hf

/-- The limit valuation and `ν` (part (b)). Let `μᵢ ≤ ν` for each `i` in additive notation, and let `ν` agree with `μ` in degree less than `d`. Then the limit value of a stable polynomial is its value for `ν`. -/
theorem stableValue_eq_of_isStable [NoMaxOrder ι] {ν : Valuation K[X] Γ₀}
    (hν : ∀ i f, ν f ≤ augmentedValuationFun μ (F.key i) (F.value i) f)
    (hlow : ∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = μ a) {f : K[X]}
    (hf : F.IsStable f) : F.stableValue f = ν f := by
  obtain ⟨i, hi⟩ := hf.exists_forall_eq
  obtain ⟨j, hij⟩ := exists_gt i
  have hc : F.val i f = F.val j f := (hi i le_rfl).trans (hi j hij.le).symm
  rw [← hi j hij.le]
  refine le_antisymm ?_ (hν j f)
  by_contra hlt
  rw [not_le] at hlt
  have hf0 : F.val j f ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le hlt)
  set r := f %ₘ F.key j
  have hr : r.degree < (F.key j).degree := degree_modByMonic_lt f (F.keyPolynomial j).monic
  have hlt' := F.val_sub_modByMonic_lt hij hc hf0
  have hrj : F.val j r = F.val j f := (show MuEquiv (F.val j) f r from hlt').map_eq.symm
  have hνr : ν r = F.val j f := by rw [hlow j r hr, ← F.val_of_degree_lt hr j, hrj]
  have hνsub : ν (f - r) < ν r := by
    rw [hνr]
    exact (hν j _).trans_lt hlt'
  have hνf : ν f = ν r :=
    calc ν f = ν (r + (f - r)) := by rw [add_sub_cancel]
      _ = ν r := Valuation.map_add_eq_of_lt_left _ hνsub
  rw [hνf, hνr] at hlt
  exact lt_irrefl _ hlt

/-- Part (b). Under the hypotheses of `stableValue_eq_of_isStable`, some polynomial is not stable if and only if the family does not reach `ν`: some `f` has `μᵢ f ≠ ν f` for each `i`. -/
theorem exists_not_isStable_iff [NoMaxOrder ι] {ν : Valuation K[X] Γ₀}
    (hν : ∀ i f, ν f ≤ augmentedValuationFun μ (F.key i) (F.value i) f)
    (hlow : ∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = μ a) :
    (∃ f, ¬ F.IsStable f) ↔ ∃ f, ∀ i, augmentedValuationFun μ (F.key i) (F.value i) f ≠ ν f := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, fun i h => ?_⟩
    obtain ⟨j, hij⟩ := exists_gt i
    have hlt := F.val_lt_val_of_not_isStable hf hij
    rw [val_apply i, h] at hlt
    exact absurd hlt (not_lt.2 (hν j f))
  · rintro ⟨f, hf⟩
    refine ⟨f, fun hs => ?_⟩
    obtain ⟨i, hi⟩ := hs.exists_forall_eq
    exact hf i ((hi i le_rfl).trans (F.stableValue_eq_of_isStable hν hlow hs))

end Stable

section LimitKey

variable {F}

/-- Part (b). If some polynomial is not stable, then a limit key polynomial exists. -/
theorem exists_isLimitKeyPolynomial [Nonempty ι] (h : ∃ f, ¬ F.IsStable f) :
    ∃ φ, F.IsLimitKeyPolynomial φ := by
  classical
  have hex : ∃ n, ∃ f, ¬ F.IsStable f ∧ f.natDegree = n := by
    obtain ⟨f, hf⟩ := h
    exact ⟨_, f, hf, rfl⟩
  obtain ⟨f, hf, hfn⟩ := Nat.find_spec hex
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf F.isStable_zero
  have hc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hf0
  refine ⟨f * C f.leadingCoeff⁻¹, ⟨monic_mul_leadingCoeff_inv hf0, fun hs => hf ?_, fun g hg => ?_⟩⟩
  · have hprod := (hs.stableValue_mul (F.stableValue_C f.leadingCoeff).1).1
    rwa [mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, mul_one] at hprod
  · rw [natDegree_mul_C (inv_ne_zero hc), hfn]
    exact Nat.find_min' hex ⟨g, hg, rfl⟩

namespace IsLimitKeyPolynomial

variable {φ : K[X]} (hφ : F.IsLimitKeyPolynomial φ)
include hφ

/-- A limit key polynomial has degree at least `d`. -/
theorem natDegree_key_le (i : ι) : (F.key i).natDegree ≤ φ.natDegree := by
  by_contra h
  rw [not_le] at h
  exact hφ.not_isStable (stableValue_of_degree_lt (i := i) (degree_lt_degree h)).1

/-- The values of a limit key polynomial decrease strictly. -/
theorem val_lt {i j : ι} (hij : i < j) : F.val j φ < F.val i φ :=
  val_lt_val_of_not_isStable hφ.not_isStable hij

variable [Nonempty ι]

theorem natDegree_pos : 0 < φ.natDegree :=
  (F.keyPolynomial (Classical.arbitrary ι)).natDegree_pos.trans_le (hφ.natDegree_key_le _)

/-- A polynomial of degree less than the degree of a limit key polynomial is stable. -/
theorem isStable_of_degree_lt {a : K[X]} (ha : a.degree < φ.degree) : F.IsStable a := by
  by_contra h
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact h F.isStable_zero
  exact (natDegree_lt_natDegree ha0 ha).not_ge (hφ.natDegree_le a h)

variable [NoMaxOrder ι]

/-- Part (b). A limit key polynomial `φ` divides `f` in the limit if and only if `f` is not stable. -/
theorem limitDvd_iff {f : K[X]} : F.LimitDvd φ f ↔ ¬ F.IsStable f := by
  rw [limitDvd_iff_muDvd]
  constructor
  · rintro ⟨i, hi⟩ hs
    obtain ⟨i', hi'⟩ := hs.exists_forall_eq
    obtain ⟨l, hkl⟩ := exists_gt (max i i')
    obtain ⟨h, hh⟩ := hi (max i i') (le_max_left _ _)
    have hh' : F.val (max i i') (f - φ * h) < F.val (max i i') f := hh
    have hfk := hi' (max i i') (le_max_right _ _)
    have hfl := hi' l ((le_max_right _ _).trans hkl.le)
    have hc : F.val (max i i') f ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le hh')
    have hprod : F.val (max i i') (φ * h) = F.val (max i i') f := hh.map_eq.symm
    have hk0 : F.val (max i i') h ≠ 0 := by
      intro h0
      apply hc
      rw [← hprod, Valuation.map_mul, h0, mul_zero]
    have h1 : F.val l (φ * h) < F.val (max i i') f := by
      rw [← hprod, Valuation.map_mul, Valuation.map_mul]
      exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos (hφ.val_lt hkl) (F.val_le_val hkl.le h)
        zero_le (zero_lt_iff.2 hk0)
    have h2 : F.val l (f - φ * h) < F.val (max i i') f := (F.val_le_val hkl.le _).trans_lt hh'
    have h3 : F.val l f < F.val (max i i') f :=
      calc F.val l f = F.val l ((f - φ * h) + φ * h) := by rw [sub_add_cancel]
        _ ≤ max (F.val l (f - φ * h)) (F.val l (φ * h)) := Valuation.map_add _ _ _
        _ < F.val (max i i') f := max_lt h2 h1
    rw [hfk, hfl] at h3
    exact lt_irrefl _ h3
  · intro hf
    set q := f /ₘ φ
    set r := f %ₘ φ
    have hsum : r + φ * q = f := modByMonic_add_div f φ
    have hr := hφ.isStable_of_degree_lt (degree_modByMonic_lt f hφ.monic)
    obtain ⟨i₀, hi₀⟩ := hr.exists_forall_eq
    by_cases hex : ∃ i, ∀ j, i ≤ j → F.stableValue r < F.val j (φ * q)
    · obtain ⟨i, hi⟩ := hex
      refine ⟨max i i₀, fun j hj => ⟨q, ?_⟩⟩
      have h1 := hi j (le_of_max_le_left hj)
      have h2 := hi₀ j (le_of_max_le_right hj)
      have hfj : F.val j f = F.val j (φ * q) := by
        rw [← hsum]
        exact Valuation.map_add_eq_of_lt_right _ (h2.trans_lt h1)
      show F.val j (f - φ * q) < F.val j f
      rw [hfj, show f - φ * q = r from (eq_sub_of_add_eq hsum).symm, h2]
      exact h1
    exfalso
    push Not at hex
    obtain ⟨j, hj, hjc⟩ := hex i₀
    apply hf
    by_cases hc : F.stableValue r = 0
    · refine (stableValue_eq_of_forall (i := j) (c := 0) fun l hl => le_zero_iff.1 ?_).1
      rw [← hsum]
      refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
      · rw [hi₀ l (hj.trans hl), hc]
      · exact (F.val_le_val hl _).trans (hjc.trans hc.le)
    obtain ⟨k, hjk⟩ := exists_gt j
    have hk : F.val k (φ * q) < F.stableValue r := by
      by_cases h0 : F.val j (φ * q) = 0
      · exact lt_of_le_of_lt ((F.val_le_val hjk.le _).trans h0.le) (zero_lt_iff.2 hc)
      refine lt_of_lt_of_le ?_ hjc
      have hq0 : F.val j q ≠ 0 := fun h' => h0 (by rw [Valuation.map_mul, h', mul_zero])
      rw [Valuation.map_mul, Valuation.map_mul]
      exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos (hφ.val_lt hjk) (F.val_le_val hjk.le q)
        zero_le (zero_lt_iff.2 hq0)
    refine (stableValue_eq_of_forall (i := k) (c := F.stableValue r) fun l hl => ?_).1
    have hrl := hi₀ l (hj.trans (hjk.le.trans hl))
    rw [← hsum, Valuation.map_add_eq_of_lt_left _ ?_, hrl]
    rw [hrl]
    exact (F.val_le_val hl _).trans_lt hk

/-- A limit key polynomial does not divide `1` in the limit. -/
theorem not_limitDvd_one : ¬ F.LimitDvd φ 1 := fun h =>
  hφ.limitDvd_iff.1 h F.stableValue_one.1

/-- A limit key polynomial is irreducible in the limit. -/
theorem limitDvd_or_limitDvd {f g : K[X]} (h : F.LimitDvd φ (f * g)) :
    F.LimitDvd φ f ∨ F.LimitDvd φ g := by
  rw [hφ.limitDvd_iff, hφ.limitDvd_iff]
  by_contra hc
  rw [not_or, not_not, not_not] at hc
  exact hφ.limitDvd_iff.1 h (hc.1.stableValue_mul hc.2).1

/-- A limit key polynomial is minimal in the limit. -/
theorem natDegree_le_of_limitDvd {f : K[X]} (h : F.LimitDvd φ f) : φ.natDegree ≤ f.natDegree :=
  hφ.natDegree_le f (hφ.limitDvd_iff.1 h)

end IsLimitKeyPolynomial

end LimitKey

/-- A finite sum of polynomials of degree less than the degree of `φ ≠ 0` has degree less than the degree of `φ`. -/
theorem _root_.Singularity.degree_sum_lt_degree {φ : K[X]} (hφ : φ ≠ 0) {α : Type*} {s : Finset α}
    {G : α → K[X]} (hG : ∀ x ∈ s, (G x).degree < φ.degree) :
    (∑ x ∈ s, G x).degree < φ.degree := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, degree_zero, degree_eq_natDegree hφ]
    exact WithBot.bot_lt_coe _
  | insert y s hy ih =>
    rw [Finset.sum_insert hy]
    exact (degree_add_le _ _).trans_lt (max_lt (hG y (Finset.mem_insert_self y s))
      (ih fun x hx => hG x (Finset.mem_insert_of_mem hx)))

/-- For `a` and `b` of degree less than the degree of `φ`, the quotient of `a * b` by `φ` has degree less than the degree of `φ`. -/
theorem _root_.Singularity.degree_mul_divByMonic_lt {φ a b : K[X]} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) (ha : a.degree < φ.degree) (hb : b.degree < φ.degree) :
    (a * b /ₘ φ).degree < φ.degree := by
  have hna : a.natDegree < φ.natDegree := by
    by_cases h0 : a = 0
    · rw [h0, natDegree_zero]
      exact hd
    · exact natDegree_lt_natDegree h0 ha
  have hnb : b.natDegree < φ.natDegree := by
    by_cases h0 : b = 0
    · rw [h0, natDegree_zero]
      exact hd
    · exact natDegree_lt_natDegree h0 hb
  refine degree_lt_degree ?_
  rw [natDegree_divByMonic _ hφ]
  have := natDegree_mul_le (p := a) (q := b)
  omega

section LimitAugmentation

variable {F} [Nonempty ι] {φ : K[X]} {γ : Γ₀}

namespace IsLimitKeyPolynomial

variable (hφ : F.IsLimitKeyPolynomial φ)
include hφ

/-- The limit `μ_∞` is ultrametric on the polynomials of degree less than the degree of `φ`. -/
theorem stableValue_add_le {a b : K[X]} (ha : a.degree < φ.degree) (hb : b.degree < φ.degree) :
    F.stableValue (a + b) ≤ max (F.stableValue a) (F.stableValue b) := by
  classical
  have hab : (a + b).degree < φ.degree := (degree_add_le a b).trans_lt (max_lt ha hb)
  obtain ⟨i, hi⟩ := F.exists_forall_val_eq {a, b, a + b} (by
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    exact ⟨hφ.isStable_of_degree_lt ha, hφ.isStable_of_degree_lt hb,
      hφ.isStable_of_degree_lt hab⟩)
  rw [← hi i le_rfl a (by simp), ← hi i le_rfl b (by simp), ← hi i le_rfl (a + b) (by simp)]
  exact Valuation.map_add _ _ _

/-- The limit `μ_∞` on a sum of terms of smaller value. -/
theorem stableValue_add_eq_of_lt {a b : K[X]} (ha : a.degree < φ.degree)
    (hb : b.degree < φ.degree) (h : F.stableValue b < F.stableValue a) :
    F.stableValue (a + b) = F.stableValue a := by
  classical
  have hab : (a + b).degree < φ.degree := (degree_add_le a b).trans_lt (max_lt ha hb)
  obtain ⟨i, hi⟩ := F.exists_forall_val_eq {a, b, a + b} (by
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    exact ⟨hφ.isStable_of_degree_lt ha, hφ.isStable_of_degree_lt hb,
      hφ.isStable_of_degree_lt hab⟩)
  rw [← hi i le_rfl a (by simp), ← hi i le_rfl b (by simp)] at h
  rw [← hi i le_rfl a (by simp), ← hi i le_rfl (a + b) (by simp)]
  exact Valuation.map_add_eq_of_lt_left _ h

theorem stableValue_sum_mul_le {α : Type*} {s : Finset α} {G : α → K[X]}
    (hG : ∀ x ∈ s, (G x).degree < φ.degree) {c C : Γ₀}
    (h : ∀ x ∈ s, F.stableValue (G x) * c ≤ C) : F.stableValue (∑ x ∈ s, G x) * c ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, F.stableValue_zero, zero_mul]
    exact zero_le
  | insert y s hy ih =>
    rw [Finset.sum_insert hy]
    have hGy := hG y (Finset.mem_insert_self y s)
    have hGs : ∀ x ∈ s, (G x).degree < φ.degree := fun x hx => hG x (Finset.mem_insert_of_mem hx)
    calc F.stableValue (G y + ∑ x ∈ s, G x) * c
        ≤ max (F.stableValue (G y)) (F.stableValue (∑ x ∈ s, G x)) * c := by
          gcongr
          exact hφ.stableValue_add_le hGy (degree_sum_lt_degree hφ.monic.ne_zero hGs)
      _ = max (F.stableValue (G y) * c) (F.stableValue (∑ x ∈ s, G x) * c) := max_mul _ _ _
      _ ≤ C := max_le (h y (Finset.mem_insert_self y s))
          (ih hGs fun x hx => h x (Finset.mem_insert_of_mem hx))

theorem stableValue_sum_mul_lt {α : Type*} {s : Finset α} {G : α → K[X]}
    (hG : ∀ x ∈ s, (G x).degree < φ.degree) {c C : Γ₀} (hC : 0 < C)
    (h : ∀ x ∈ s, F.stableValue (G x) * c < C) : F.stableValue (∑ x ∈ s, G x) * c < C := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, F.stableValue_zero, zero_mul]
    exact hC
  | insert y s hy ih =>
    rw [Finset.sum_insert hy]
    have hGy := hG y (Finset.mem_insert_self y s)
    have hGs : ∀ x ∈ s, (G x).degree < φ.degree := fun x hx => hG x (Finset.mem_insert_of_mem hx)
    calc F.stableValue (G y + ∑ x ∈ s, G x) * c
        ≤ max (F.stableValue (G y)) (F.stableValue (∑ x ∈ s, G x)) * c := by
          gcongr
          exact hφ.stableValue_add_le hGy (degree_sum_lt_degree hφ.monic.ne_zero hGs)
      _ = max (F.stableValue (G y) * c) (F.stableValue (∑ x ∈ s, G x) * c) := max_mul _ _ _
      _ < C := max_lt (h y (Finset.mem_insert_self y s))
          (ih hGs fun x hx => h x (Finset.mem_insert_of_mem hx))

variable [NoMaxOrder ι]

/-- The remainder in the limit. Let `f` and its quotient `q` by `φ` be stable. Then the remainder `r` of `f` modulo `φ` has `μ_∞ r = μ_∞ f`. -/
theorem stableValue_modByMonic {f : K[X]} (hf : F.IsStable f) (hq : F.IsStable (f /ₘ φ)) :
    F.stableValue (f %ₘ φ) = F.stableValue f := by
  classical
  have hr := hφ.isStable_of_degree_lt (degree_modByMonic_lt f hφ.monic)
  obtain ⟨i, hi⟩ := F.exists_forall_val_eq {f, f %ₘ φ, f /ₘ φ} (by
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    exact ⟨hf, hr, hq⟩)
  obtain ⟨j, hij⟩ := exists_gt i
  have hsum : f %ₘ φ + φ * (f /ₘ φ) = f := modByMonic_add_div f φ
  by_contra hne
  have key : ∀ k, i ≤ k → F.val k φ * F.stableValue (f /ₘ φ) =
      max (F.stableValue (f %ₘ φ)) (F.stableValue f) := by
    intro k hk
    have h1 := hi k hk f (by simp)
    have h2 := hi k hk (f %ₘ φ) (by simp)
    have h3 := hi k hk (f /ₘ φ) (by simp)
    rw [← h1, ← h2, ← h3, ← Valuation.map_mul]
    have hv := valuation_eq_max_of_ne (F.val k) (x := f %ₘ φ) (y := φ * (f /ₘ φ)) (by
      rw [hsum, h1, h2]
      exact hne)
    rwa [hsum] at hv
  have e1 := key i le_rfl
  have e2 := key j hij.le
  have hM : max (F.stableValue (f %ₘ φ)) (F.stableValue f) ≠ 0 := by
    intro h0
    apply hne
    rw [le_zero_iff.1 ((le_max_left _ _).trans h0.le), le_zero_iff.1 ((le_max_right _ _).trans h0.le)]
  have hq0 : F.stableValue (f /ₘ φ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at e1
    exact hM e1.symm
  have hlt : F.val j φ * F.stableValue (f /ₘ φ) < F.val i φ * F.stableValue (f /ₘ φ) :=
    mul_lt_mul_of_lt_of_le_of_nonneg_of_pos (hφ.val_lt hij) le_rfl zero_le (zero_lt_iff.2 hq0)
  rw [e1, e2] at hlt
  exact lt_irrefl _ hlt

/-- The quotient in the limit. Let `γ ≤ μᵢ φ` for each `i`, and let `f` and its quotient `q` by `φ` be stable. Then `μ_∞ q * γ ≤ μ_∞ f`. -/
theorem stableValue_divByMonic_mul_le
    (hγ : ∀ i, γ ≤ augmentedValuationFun μ (F.key i) (F.value i) φ) {f : K[X]}
    (hf : F.IsStable f) (hq : F.IsStable (f /ₘ φ)) :
    F.stableValue (f /ₘ φ) * γ ≤ F.stableValue f := by
  classical
  have hr := hφ.isStable_of_degree_lt (degree_modByMonic_lt f hφ.monic)
  obtain ⟨i, hi⟩ := F.exists_forall_val_eq {f, f %ₘ φ, f /ₘ φ} (by
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    exact ⟨hf, hr, hq⟩)
  have hsub : φ * (f /ₘ φ) = f - f %ₘ φ := eq_sub_of_add_eq' (modByMonic_add_div f φ)
  have hγi : γ ≤ F.val i φ := hγ i
  calc F.stableValue (f /ₘ φ) * γ ≤ F.stableValue (f /ₘ φ) * F.val i φ := by gcongr
    _ = F.val i (φ * (f /ₘ φ)) := by
      rw [Valuation.map_mul, hi i le_rfl (f /ₘ φ) (by simp), mul_comm]
    _ = F.val i (f - f %ₘ φ) := by rw [hsub]
    _ ≤ max (F.val i f) (F.val i (f %ₘ φ)) := Valuation.map_sub _ _ _
    _ = F.stableValue f := by
      rw [hi i le_rfl f (by simp), hi i le_rfl _ (by simp), hφ.stableValue_modByMonic hf hq,
        max_self]

/-- The bound for the terms of the `φ`-expansion of `φ ^ n * p`, for `p` stable with a quotient by `φ` of degree less than the degree of `φ`. -/
theorem stableValue_expansionCoeff_pow_mul_le
    (hγ : ∀ i, γ ≤ augmentedValuationFun μ (F.key i) (F.value i) φ) {p : K[X]}
    (hp : F.IsStable p) (hq : (p /ₘ φ).degree < φ.degree) (n k : ℕ) :
    F.stableValue (expansionCoeff φ (φ ^ n * p) k) * γ ^ k ≤ F.stableValue p * γ ^ n := by
  have hm := hφ.monic
  have hqs := hφ.isStable_of_degree_lt hq
  rcases lt_or_ge k n with hk | hk
  · rw [expansionCoeff_pow_mul_of_lt hm p hk, F.stableValue_zero, zero_mul]
    exact zero_le
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [expansionCoeff_pow_mul_add hm, pow_add, ← mul_assoc]
  match m with
  | 0 =>
    refine le_of_eq ?_
    rw [expansionCoeff_zero_eq_modByMonic, hφ.stableValue_modByMonic hp hqs, pow_zero, mul_one]
  | 1 =>
    rw [expansionCoeff_succ, expansionCoeff_zero_eq_modByMonic, (modByMonic_eq_self_iff hm).2 hq,
      pow_one]
    gcongr
    exact hφ.stableValue_divByMonic_mul_le hγ hp hqs
  | m + 2 =>
    rw [expansionCoeff_succ, expansionCoeff_succ, (divByMonic_eq_zero_iff hm).2 hq,
      expansionCoeff_zero, F.stableValue_zero, zero_mul, zero_mul]
    exact zero_le

end IsLimitKeyPolynomial

omit [Nonempty ι] in
theorem le_limitAugmentedValuationFun (hφ : φ.Monic) (hd : 0 < φ.natDegree) (f : K[X]) (j : ℕ) :
    F.stableValue (expansionCoeff φ f j) * γ ^ j ≤ F.limitAugmentedValuationFun φ γ f := by
  by_cases hj : j < f.natDegree + 1
  · exact Finset.le_sup (f := fun j => F.stableValue (expansionCoeff φ f j) * γ ^ j)
      (Finset.mem_range.2 hj)
  · rw [expansionCoeff_eq_zero hφ hd (by omega), F.stableValue_zero, zero_mul]
    exact zero_le

omit [Nonempty ι] in
theorem limitAugmentedValuationFun_le_iff (hφ : φ.Monic) (hd : 0 < φ.natDegree) {f : K[X]}
    {c : Γ₀} : F.limitAugmentedValuationFun φ γ f ≤ c ↔
      ∀ j, F.stableValue (expansionCoeff φ f j) * γ ^ j ≤ c :=
  ⟨fun h j => (F.le_limitAugmentedValuationFun hφ hd f j).trans h,
    fun h => Finset.sup_le fun j _ => h j⟩

omit [Nonempty ι] in
theorem exists_eq_limitAugmentedValuationFun (f : K[X]) :
    ∃ j, F.stableValue (expansionCoeff φ f j) * γ ^ j = F.limitAugmentedValuationFun φ γ f := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup (Finset.range (f.natDegree + 1))
    ⟨0, by simp⟩ fun j => F.stableValue (expansionCoeff φ f j) * γ ^ j
  exact ⟨j, hj.symm⟩

omit [Nonempty ι] in
theorem limitAugmentedValuationFun_zero : F.limitAugmentedValuationFun φ γ 0 = 0 := by
  simp [limitAugmentedValuationFun, expansionCoeff_zero, stableValue_zero]

/-- The limit augmentation agrees with `μ_∞` in degree less than the degree of `φ`. -/
theorem limitAugmentedValuationFun_of_degree_lt (hφ : φ.Monic) (hd : 0 < φ.natDegree) {f : K[X]}
    (hf : f.degree < φ.degree) : F.limitAugmentedValuationFun φ γ f = F.stableValue f := by
  have h0 : expansionCoeff φ f 0 = f := (modByMonic_eq_self_iff hφ).2 hf
  refine le_antisymm ((F.limitAugmentedValuationFun_le_iff hφ hd).2 fun j => ?_) ?_
  · cases j with
    | zero => rw [h0, pow_zero, mul_one]
    | succ j =>
      rw [expansionCoeff_succ, (divByMonic_eq_zero_iff hφ).2 hf, expansionCoeff_zero,
        F.stableValue_zero, zero_mul]
      exact zero_le
  · simpa [h0] using F.le_limitAugmentedValuationFun (γ := γ) hφ hd f 0

theorem limitAugmentedValuationFun_one (hφ : φ.Monic) (hd : 0 < φ.natDegree) :
    F.limitAugmentedValuationFun φ γ 1 = 1 := by
  rw [F.limitAugmentedValuationFun_of_degree_lt hφ hd (by
    rw [degree_one]
    exact natDegree_pos_iff_degree_pos.1 hd), F.stableValue_one.2]

/-- The limit augmentation sends `φ` to `γ`. -/
theorem limitAugmentedValuationFun_self (hφ : φ.Monic) (hd : 0 < φ.natDegree) :
    F.limitAugmentedValuationFun φ γ φ = γ := by
  have h1 : (1 : K[X]).degree < φ.degree := by
    rw [degree_one]
    exact natDegree_pos_iff_degree_pos.1 hd
  have hdiv : φ /ₘ φ = 1 := by
    simpa using mul_divByMonic_cancel_left (1 : K[X]) hφ
  have e1 : expansionCoeff φ φ 1 = 1 := by
    rw [expansionCoeff_succ, hdiv, expansionCoeff_zero_eq_modByMonic,
      (modByMonic_eq_self_iff hφ).2 h1]
  refine le_antisymm ((F.limitAugmentedValuationFun_le_iff hφ hd).2 fun j => ?_) ?_
  · match j with
    | 0 =>
      rw [expansionCoeff_zero_eq_modByMonic, modByMonic_self hφ, F.stableValue_zero, zero_mul]
      exact zero_le
    | 1 => rw [e1, F.stableValue_one.2, one_mul, pow_one]
    | j + 2 =>
      rw [expansionCoeff_succ, expansionCoeff_succ, hdiv, (divByMonic_eq_zero_iff hφ).2 h1,
        expansionCoeff_zero, F.stableValue_zero, zero_mul]
      exact zero_le
  · simpa [e1, F.stableValue_one.2] using F.le_limitAugmentedValuationFun (γ := γ) hφ hd φ 1

namespace IsLimitKeyPolynomial

variable (hφ : F.IsLimitKeyPolynomial φ)
include hφ

/-- The ultrametric inequality for the limit augmentation. -/
theorem limitAugmentedValuationFun_add_le_max (f g : K[X]) :
    F.limitAugmentedValuationFun φ γ (f + g) ≤
      max (F.limitAugmentedValuationFun φ γ f) (F.limitAugmentedValuationFun φ γ g) := by
  have hm := hφ.monic
  have hd := hφ.natDegree_pos
  refine (F.limitAugmentedValuationFun_le_iff hm hd).2 fun j => ?_
  rw [expansionCoeff_add]
  calc F.stableValue (expansionCoeff φ f j + expansionCoeff φ g j) * γ ^ j
      ≤ max (F.stableValue (expansionCoeff φ f j)) (F.stableValue (expansionCoeff φ g j)) *
          γ ^ j := by
        gcongr
        exact hφ.stableValue_add_le (degree_expansionCoeff_lt hm f j)
          (degree_expansionCoeff_lt hm g j)
    _ = max (F.stableValue (expansionCoeff φ f j) * γ ^ j)
          (F.stableValue (expansionCoeff φ g j) * γ ^ j) := max_mul _ _ _
    _ ≤ _ := max_le_max (F.le_limitAugmentedValuationFun hm hd f j)
          (F.le_limitAugmentedValuationFun hm hd g j)

variable [NoMaxOrder ι]

/-- Part (c): the limit augmentation is multiplicative. Let `φ` be a limit key polynomial and let `γ ≤ μᵢ φ` for each `i`. In additive notation, `γ ≥ μᵢ(φ)` for each `i`. Then `[μ_∞; φ, γ] (f * g) = [μ_∞; φ, γ] f * [μ_∞; φ, γ] g`. -/
theorem limitAugmentedValuationFun_mul
    (hγ : ∀ i, γ ≤ augmentedValuationFun μ (F.key i) (F.value i) φ) (f g : K[X]) :
    F.limitAugmentedValuationFun φ γ (f * g) =
      F.limitAugmentedValuationFun φ γ f * F.limitAugmentedValuationFun φ γ g := by
  classical
  have hm := hφ.monic
  have hd := hφ.natDegree_pos
  set N := f.natDegree + 1
  set M := g.natDegree + 1
  set a := expansionCoeff φ f
  set b := expansionCoeff φ g
  have hda : ∀ i, (a i).degree < φ.degree := fun i => degree_expansionCoeff_lt hm f i
  have hdb : ∀ j, (b j).degree < φ.degree := fun j => degree_expansionCoeff_lt hm g j
  have hab : ∀ i j, F.IsStable (a i * b j) := fun i j =>
    ((hφ.isStable_of_degree_lt (hda i)).stableValue_mul (hφ.isStable_of_degree_lt (hdb j))).1
  have habv : ∀ i j, F.stableValue (a i * b j) = F.stableValue (a i) * F.stableValue (b j) :=
    fun i j =>
      ((hφ.isStable_of_degree_lt (hda i)).stableValue_mul (hφ.isStable_of_degree_lt (hdb j))).2
  have hq : ∀ i j, (a i * b j /ₘ φ).degree < φ.degree := fun i j =>
    degree_mul_divByMonic_lt hm hd (hda i) (hdb j)
  -- the product as a double sum
  have hfg : f * g =
      ∑ x ∈ Finset.range N ×ˢ Finset.range M, φ ^ (x.1 + x.2) * (a x.1 * b x.2) := by
    conv_lhs => rw [eq_sum_expansionCoeff hm hd f, eq_sum_expansionCoeff hm hd g]
    rw [Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]
    ring
  have hcoeff : ∀ k, expansionCoeff φ (f * g) k = ∑ x ∈ Finset.range N ×ˢ Finset.range M,
      expansionCoeff φ (φ ^ (x.1 + x.2) * (a x.1 * b x.2)) k := fun k => by
    rw [hfg, expansionCoeff_sum]
  -- the bound for each term
  have hterm : ∀ i j k,
      F.stableValue (expansionCoeff φ (φ ^ (i + j) * (a i * b j)) k) * γ ^ k ≤
        (F.stableValue (a i) * γ ^ i) * (F.stableValue (b j) * γ ^ j) := fun i j k => by
    refine (hφ.stableValue_expansionCoeff_pow_mul_le hγ (hab i j) (hq i j) _ k).trans_eq ?_
    rw [habv, pow_add]
    exact mul_mul_mul_comm _ _ _ _
  refine le_antisymm ((F.limitAugmentedValuationFun_le_iff hm hd).2 fun k => ?_) ?_
  · -- the upper bound
    rw [hcoeff]
    refine hφ.stableValue_sum_mul_le (fun x _ => degree_expansionCoeff_lt hm _ _)
      fun x _ => (hterm _ _ _).trans ?_
    exact mul_le_mul' (F.le_limitAugmentedValuationFun hm hd f _)
      (F.le_limitAugmentedValuationFun hm hd g _)
  -- the lower bound
  set ν := F.limitAugmentedValuationFun φ γ
  by_cases hf : ν f = 0
  · rw [hf, zero_mul]
    exact zero_le
  by_cases hg : ν g = 0
  · rw [hg, mul_zero]
    exact zero_le
  have ef := F.exists_eq_limitAugmentedValuationFun (φ := φ) (γ := γ) f
  have eg := F.exists_eq_limitAugmentedValuationFun (φ := φ) (γ := γ) g
  set i₀ := Nat.find ef
  set j₀ := Nat.find eg
  have hfi₀ : F.stableValue (a i₀) * γ ^ i₀ = ν f := Nat.find_spec ef
  have hgj₀ : F.stableValue (b j₀) * γ ^ j₀ = ν g := Nat.find_spec eg
  have hlt_f : ∀ i < i₀, F.stableValue (a i) * γ ^ i < ν f := fun i hi =>
    lt_of_le_of_ne (F.le_limitAugmentedValuationFun hm hd f i) (Nat.find_min ef hi)
  have hlt_g : ∀ j < j₀, F.stableValue (b j) * γ ^ j < ν g := fun j hj =>
    lt_of_le_of_ne (F.le_limitAugmentedValuationFun hm hd g j) (Nat.find_min eg hj)
  have hi₀ : i₀ < N := by
    by_contra h
    apply hf
    have h0 : a i₀ = 0 := expansionCoeff_eq_zero hm hd (by omega)
    rw [← hfi₀, h0, F.stableValue_zero, zero_mul]
  have hj₀ : j₀ < M := by
    by_contra h
    apply hg
    have h0 : b j₀ = 0 := expansionCoeff_eq_zero hm hd (by omega)
    rw [← hgj₀, h0, F.stableValue_zero, zero_mul]
  set k := i₀ + j₀
  have hmem : (i₀, j₀) ∈ Finset.range N ×ˢ Finset.range M :=
    Finset.mem_product.2 ⟨Finset.mem_range.2 hi₀, Finset.mem_range.2 hj₀⟩
  have hpos : 0 < ν f * ν g := zero_lt_iff.2 (mul_ne_zero hf hg)
  -- the main term
  set t := expansionCoeff φ (φ ^ (i₀ + j₀) * (a i₀ * b j₀)) k with ht
  have hmain : F.stableValue t * γ ^ k = ν f * ν g := by
    have e : t = a i₀ * b j₀ %ₘ φ := by
      rw [ht, show k = 0 + (i₀ + j₀) from (zero_add _).symm, expansionCoeff_pow_mul_add hm,
        expansionCoeff_zero_eq_modByMonic]
    rw [e, hφ.stableValue_modByMonic (hab i₀ j₀) (hφ.isStable_of_degree_lt (hq i₀ j₀)), habv,
      ← hfi₀, ← hgj₀, pow_add]
    exact mul_mul_mul_comm _ _ _ _
  -- the other terms
  have hrest : ∀ x ∈ (Finset.range N ×ˢ Finset.range M).erase (i₀, j₀),
      F.stableValue (expansionCoeff φ (φ ^ (x.1 + x.2) * (a x.1 * b x.2)) k) * γ ^ k <
        ν f * ν g := by
    intro x hx
    have hne := Finset.ne_of_mem_erase hx
    rcases lt_or_ge k (x.1 + x.2) with hk | hk
    · rw [expansionCoeff_pow_mul_of_lt hm _ hk, F.stableValue_zero, zero_mul]
      exact hpos
    refine lt_of_le_of_lt (hterm _ _ _) ?_
    rcases lt_or_ge x.1 i₀ with h1 | h1
    · exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos (hlt_f _ h1)
        (F.le_limitAugmentedValuationFun hm hd g _) zero_le (zero_lt_iff.2 hg)
    · have h2 : x.2 < j₀ := by
        by_contra h2
        rw [not_lt] at h2
        exact hne (Prod.ext (by omega) (by omega))
      exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (F.le_limitAugmentedValuationFun hm hd f _)
        (hlt_g _ h2) zero_le (zero_lt_iff.2 hf)
  have hsum := hφ.stableValue_sum_mul_lt (fun x _ => degree_expansionCoeff_lt hm _ _) hpos hrest
  rw [← hmain] at hsum
  have hval : F.stableValue (expansionCoeff φ (f * g) k) = F.stableValue t := by
    rw [hcoeff, ← Finset.add_sum_erase _ _ hmem]
    exact hφ.stableValue_add_eq_of_lt (degree_expansionCoeff_lt hm _ _)
      (degree_sum_lt_degree hm.ne_zero fun x _ => degree_expansionCoeff_lt hm _ _)
      (lt_of_mul_lt_mul_right' hsum)
  calc ν f * ν g = F.stableValue (expansionCoeff φ (f * g) k) * γ ^ k := by rw [hval, hmain]
    _ ≤ ν (f * g) := F.le_limitAugmentedValuationFun hm hd _ _

end IsLimitKeyPolynomial

variable (F φ γ) [NoMaxOrder ι]

/-- The limit augmentation `[μ_∞; φ, γ]` as a valuation, for a limit key polynomial `φ` and `γ ≤ μᵢ φ` for each `i` (Vaquié, [Vaq07]). -/
noncomputable def limitAugmentedValuation (hφ : F.IsLimitKeyPolynomial φ)
    (hγ : ∀ i, γ ≤ augmentedValuationFun μ (F.key i) (F.value i) φ) : Valuation K[X] Γ₀ where
  toFun := F.limitAugmentedValuationFun φ γ
  map_zero' := F.limitAugmentedValuationFun_zero
  map_one' := F.limitAugmentedValuationFun_one hφ.monic hφ.natDegree_pos
  map_mul' := hφ.limitAugmentedValuationFun_mul hγ
  map_add_le_max' := hφ.limitAugmentedValuationFun_add_le_max

variable {F φ γ}

theorem limitAugmentedValuation_apply (hφ : F.IsLimitKeyPolynomial φ)
    (hγ : ∀ i, γ ≤ augmentedValuationFun μ (F.key i) (F.value i) φ) (f : K[X]) :
    F.limitAugmentedValuation φ γ hφ hγ f = F.limitAugmentedValuationFun φ γ f :=
  rfl

namespace IsLimitKeyPolynomial

variable (hφ : F.IsLimitKeyPolynomial φ)
include hφ

/-- Part (c): `μᵢ ≤ [μ_∞; φ, γ]` in additive notation. In multiplicative notation, `[μ_∞; φ, γ] f ≤ μᵢ f` for each `i` and `f`. -/
theorem limitAugmentedValuationFun_le
    (hγ : ∀ i, γ ≤ augmentedValuationFun μ (F.key i) (F.value i) φ) (i : ι) (f : K[X]) :
    F.limitAugmentedValuationFun φ γ f ≤ augmentedValuationFun μ (F.key i) (F.value i) f := by
  have hm := hφ.monic
  have hd := hφ.natDegree_pos
  have hki := F.keyPolynomial i
  set w := F.limitAugmentedValuation φ γ hφ hγ
  have hdeg : (F.key i).degree ≤ φ.degree := by
    rw [degree_eq_natDegree hki.monic.ne_zero, degree_eq_natDegree hm.ne_zero]
    exact_mod_cast hφ.natDegree_key_le i
  have hlow : ∀ a : K[X], a.degree < (F.key i).degree → w a = μ a := fun a ha => by
    rw [limitAugmentedValuation_apply, F.limitAugmentedValuationFun_of_degree_lt hm hd
      (ha.trans_le hdeg), (stableValue_of_degree_lt ha).2]
  have hkey : w (F.key i) ≤ F.value i := by
    by_cases hlt : (F.key i).natDegree < φ.natDegree
    · rw [limitAugmentedValuation_apply, F.limitAugmentedValuationFun_of_degree_lt hm hd
        (degree_lt_degree hlt), ← F.val_key_of_le le_rfl]
      exact F.stableValue_le _ i
    have hnd : φ.natDegree = (F.key i).natDegree :=
      le_antisymm (not_lt.1 hlt) (hφ.natDegree_key_le i)
    set a := φ - F.key i
    have ha : a.degree < (F.key i).degree := degree_sub_lt_of_monic hki.monic hm hnd
    have hφa : φ = F.key i + a := (add_sub_cancel _ _).symm
    have hμa : μ a ≤ F.value i := by
      by_contra h
      rw [not_le] at h
      refine hφ.not_isStable (stableValue_eq_of_forall (i := i) (c := μ a) fun j hj => ?_).1
      have hkj : F.val j (F.key i) < F.val j a := by
        rw [F.val_of_degree_lt ha j]
        exact ((F.val_le_val hj _).trans_eq (F.val_key_of_le le_rfl)).trans_lt h
      rw [hφa, Valuation.map_add_eq_of_lt_right _ hkj, F.val_of_degree_lt ha j]
    have hγi : γ ≤ F.value i :=
      calc γ ≤ F.val i φ := hγ i
        _ = F.val i (F.key i + a) := by rw [← hφa]
        _ ≤ max (F.val i (F.key i)) (F.val i a) := Valuation.map_add _ _ _
        _ ≤ F.value i := by
          rw [F.val_key_of_le le_rfl, F.val_of_degree_lt ha i]
          exact max_le le_rfl hμa
    calc w (F.key i) = w (φ - a) := by rw [sub_sub_cancel]
      _ ≤ max (w φ) (w a) := Valuation.map_sub _ _ _
      _ ≤ F.value i := by
        rw [limitAugmentedValuation_apply, limitAugmentedValuation_apply,
          F.limitAugmentedValuationFun_self hm hd, F.limitAugmentedValuationFun_of_degree_lt hm hd
            (ha.trans_le hdeg), (stableValue_of_degree_lt ha).2]
        exact max_le hγi hμa
  exact (map_le_augmentedValuationFun_of_map_eq hki.monic hki.natDegree_pos hlow f).trans
    (augmentedValuationFun_mono hki.monic hki.natDegree_pos hkey f)

/-- Part (c): `[μ_∞; φ, γ] ≤ ν` in additive notation. Let `μᵢ ≤ ν` for each `i`, let `ν` agree with `μ` in degree less than `d`, and let `ν φ ≤ γ`. In additive notation, `γ ≤ ν(φ)`. Then `ν f ≤ [μ_∞; φ, γ] f` for each `f`. -/
theorem map_le_limitAugmentedValuationFun {ν : Valuation K[X] Γ₀}
    (hν : ∀ i f, ν f ≤ augmentedValuationFun μ (F.key i) (F.value i) f)
    (hlow : ∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = μ a) (hγ : ν φ ≤ γ)
    (f : K[X]) : ν f ≤ F.limitAugmentedValuationFun φ γ f := by
  have hm := hφ.monic
  have hd := hφ.natDegree_pos
  conv_lhs => rw [eq_sum_expansionCoeff hm hd f]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [Valuation.map_mul, Valuation.map_pow, ← F.stableValue_eq_of_isStable hν hlow
    (hφ.isStable_of_degree_lt (degree_expansionCoeff_lt hm f j))]
  exact (mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le hγ j)).trans
    (F.le_limitAugmentedValuationFun hm hd f j)

/-- Part (c) with the choice `γ = ν φ`. Then `μᵢ ≤ [μ_∞; φ, ν(φ)] ≤ ν` in additive notation. -/
theorem limitAugmentedValuationFun_map_le {ν : Valuation K[X] Γ₀}
    (hν : ∀ i f, ν f ≤ augmentedValuationFun μ (F.key i) (F.value i) f)
    (hlow : ∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = μ a) (i : ι) (f : K[X]) :
    ν f ≤ F.limitAugmentedValuationFun φ (ν φ) f ∧
      F.limitAugmentedValuationFun φ (ν φ) f ≤ augmentedValuationFun μ (F.key i) (F.value i) f :=
  ⟨hφ.map_le_limitAugmentedValuationFun hν hlow le_rfl f,
    hφ.limitAugmentedValuationFun_le (fun j => hν j φ) i f⟩

end IsLimitKeyPolynomial

end LimitAugmentation

end ContinuousFamily

end Singularity
