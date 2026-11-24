/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Inductions

/-!
# Key polynomials

This file defines the key polynomials of MacLane for a valuation on `K[X]` (node SG0000000Z, Section 3.3 of Volume 3 of the handbook). It also proves that the monomial valuation `[v; X, γ]` is a valuation (Lemma 3.3.2), and it defines the augmented valuation `[μ; φ, γ]` (Definition 3.3.4).

## Conventions

A valuation of Mathlib is multiplicative. It takes values in a linearly ordered commutative group with zero `Γ₀`, and a small value means a large additive value. The handbook uses additive notation. Thus the additive condition `μ(f) ≥ γ` is `μ f ≤ γ` here, `∞` is `0`, a sum `μ(f) + μ(g)` is a product `μ f * μ g`, and a minimum is a maximum. The term `v(aᵢ) + iγ` of the handbook is `v aᵢ * γ ^ i` here.

## The graded algebra

The file does not construct the graded algebra `gr_μ` of Definition 3.3.1. It uses an equivalent form of the conditions on initial forms, with polynomials only. The handbook takes `μ` with support `0`, so each nonzero `f` has an initial form `in_μ f`.

* `in_μ f = in_μ g` if and only if `μ (f - g) < μ f`. This is `MuEquiv μ f g`.
* A nonzero homogeneous element of `gr_μ` of degree `δ` is the class of an `f` with `μ f = δ`, so it is the initial form `in_μ f`.
* The ring `gr_μ` is a graded domain. If `in_μ φ` divides `in_μ f`, then the quotient is homogeneous, so it is `in_μ h` for some `h`. Then `in_μ f = in_μ (φ * h)`. Thus `in_μ φ` divides `in_μ f` if and only if `f` is `μ`-equivalent to `φ * h` for some `h`. This is `MuDvd μ φ f`.
* The initial form `in_μ φ` is a unit if and only if it divides `in_μ 1`, that is if `MuDvd μ φ 1`.
* Let `p` be a nonzero homogeneous element of a domain that is graded by a totally ordered group. Then `p` is prime if and only if it is not a unit and, when it divides a product of two homogeneous elements, it divides one of them. The proof compares the components of the lowest degree. So `in_μ φ` is prime if and only if `IsMuIrreducible μ φ` holds.

Thus, for a valuation `μ` with support `0`, a polynomial `φ` satisfies `KeyPolynomial μ φ` if and only if it is a key polynomial in the sense of Definition 3.3.3. The definition of `KeyPolynomial` does not need the condition on the support. For the zero polynomial, `MuDvd μ φ 0` is false. This agrees with the handbook, because the conditions of the handbook apply only to polynomials with an initial form.

## Main definitions

* `Singularity.MuEquiv μ f g`: the polynomials `f` and `g` are `μ`-equivalent.
* `Singularity.MuDvd μ φ f`: the polynomial `φ` `μ`-divides `f`.
* `Singularity.IsMuIrreducible μ φ` and `Singularity.IsMuMinimal μ φ`: the conditions (1) and (2) of Definition 3.3.3.
* `Singularity.KeyPolynomial μ φ`: the polynomial `φ` is a key polynomial for `μ` (Definition 3.3.3).
* `Singularity.monomialValuation v γ`: the monomial valuation `[v; X, γ]` (Lemma 3.3.2).
* `Singularity.expansionCoeff φ f j`: the coefficient `aⱼ` of the `φ`-expansion of `f`.
* `Singularity.augmentedValuationFun μ φ γ`: the augmented valuation `[μ; φ, γ]` as a function (Definition 3.3.4).

## Main results

* `Singularity.KeyPolynomial.natDegree_pos` and `Singularity.KeyPolynomial.not_isUnit`: a key polynomial has positive degree and is not a unit.
* `Singularity.monomialValuationFun_mul`: Lemma 3.3.2, the monomial valuation is multiplicative.
* `Singularity.monomialValuation_eq_zero_iff`: the support of `[v; X, γ]` is `0` if `γ ≠ 0`.
* `Singularity.keyPolynomial_X_monomialValuation`: `X` is a key polynomial for `[v; X, γ]`.
* `Singularity.eq_sum_expansionCoeff`: the `φ`-expansion `f = ∑ aⱼ φ ^ j`.
* `Singularity.augmentedValuationFun_of_degree_lt` and `Singularity.augmentedValuationFun_self`: the augmented valuation agrees with `μ` in degree less than the degree of `φ`, and it sends `φ` to `γ` (parts of Theorem 3.3.5 (2)).
* `Singularity.augmentedValuationFun_X`: the augmentation `[μ; X, γ]` of a valuation that extends `v` is `[v; X, γ]`.

The file does not prove Theorem 3.3.5 (the theorem of MacLane-Vaquié). In particular it does not prove that the augmented valuation is multiplicative.

## References

* [Mac36] S. MacLane, A construction for absolute values in polynomial rings.
* [Vaq07] M. Vaquié, Extension d'une valuation.
* [HMOS22] F. J. Herrera Govantes, W. Mahboub, M. A. Olalla Acosta and M. Spivakovsky, Key polynomials for simple extensions of valued fields.
-/

open Polynomial

namespace Singularity

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

section Equiv

variable (μ : Valuation K[X] Γ₀)

/-- Two polynomials `f` and `g` are `μ`-equivalent if `μ (f - g) < μ f`. In additive notation this is `μ(f - g) > μ(f)`, the condition of Definition 3.3.1 of the handbook. It says that `f` and `g` have the same initial form in the graded algebra of `μ`. -/
def MuEquiv (f g : K[X]) : Prop :=
  μ (f - g) < μ f

/-- The polynomial `φ` `μ`-divides `f` if `f` is `μ`-equivalent to `φ * h` for some `h`. This is the condition that the initial form of `φ` divides the initial form of `f` in the graded algebra of `μ` (Definition 3.3.1). The relation is false for `f` with `μ f = 0`, for example for `f = 0`. -/
def MuDvd (φ f : K[X]) : Prop :=
  ∃ h : K[X], MuEquiv μ f (φ * h)

/-- The polynomial `φ` is `μ`-irreducible if it does not `μ`-divide `1`, and if it `μ`-divides `f` or `g` when it `μ`-divides `f * g`. This is the elementwise form of the condition that the initial form of `φ` is a prime element of the graded algebra (Definition 3.3.3 (1)). -/
def IsMuIrreducible (φ : K[X]) : Prop :=
  ¬ MuDvd μ φ 1 ∧ ∀ f g : K[X], MuDvd μ φ (f * g) → MuDvd μ φ f ∨ MuDvd μ φ g

/-- The polynomial `φ` is `μ`-minimal if each nonzero polynomial that `φ` `μ`-divides has degree at least the degree of `φ` (Definition 3.3.3 (2)). -/
def IsMuMinimal (φ : K[X]) : Prop :=
  ∀ f : K[X], f ≠ 0 → MuDvd μ φ f → φ.natDegree ≤ f.natDegree

/-- A key polynomial for a valuation `μ` on `K[X]` (Definition 3.3.3 of Volume 3 of the handbook, node SG0000000Z). It is a monic polynomial that is `μ`-irreducible and `μ`-minimal. The conditions are stated with `μ`-equivalence. See the docstring of the file for the relation to the graded algebra. -/
structure KeyPolynomial (φ : K[X]) : Prop where
  monic : φ.Monic
  isMuIrreducible : IsMuIrreducible μ φ
  isMuMinimal : IsMuMinimal μ φ

variable {μ}

namespace MuEquiv

variable {f g h : K[X]}

/-- If `f` is `μ`-equivalent to a polynomial, then `μ f ≠ 0`. -/
theorem ne_zero (hfg : MuEquiv μ f g) : μ f ≠ 0 :=
  ne_of_gt (lt_of_le_of_lt zero_le hfg)

/-- Two `μ`-equivalent polynomials have the same value. -/
theorem map_eq (hfg : MuEquiv μ f g) : μ f = μ g := by
  have hg : g = f + -(f - g) := by ring
  rw [hg, Valuation.map_add_eq_of_lt_left _ (by rw [Valuation.map_neg]; exact hfg)]

/-- The `μ`-equivalence is symmetric. -/
theorem symm (hfg : MuEquiv μ f g) : MuEquiv μ g f := by
  unfold MuEquiv
  rw [Valuation.map_sub_swap, ← hfg.map_eq]
  exact hfg

/-- A polynomial with nonzero value is `μ`-equivalent to itself. -/
theorem refl (hf : μ f ≠ 0) : MuEquiv μ f f := by
  unfold MuEquiv
  rw [sub_self, Valuation.map_zero]
  exact lt_of_le_of_ne zero_le (Ne.symm hf)

/-- The `μ`-equivalence is transitive. -/
theorem trans (hfg : MuEquiv μ f g) (hgh : MuEquiv μ g h) : MuEquiv μ f h := by
  unfold MuEquiv
  have : f - h = (f - g) + (g - h) := by ring
  rw [this]
  exact Valuation.map_add_lt _ hfg (hfg.map_eq ▸ hgh)

/-- The `μ`-equivalence is compatible with products. Thus the initial form of `f * g` is the product of the initial forms of `f` and `g`. -/
theorem mul {f' g' : K[X]} (hf : MuEquiv μ f f') (hg : MuEquiv μ g g') :
    MuEquiv μ (f * g) (f' * g') := by
  unfold MuEquiv
  have : f * g - f' * g' = (f - f') * g + f' * (g - g') := by ring
  rw [this, Valuation.map_mul]
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [Valuation.map_mul]
    exact mul_lt_mul_of_pos_right hf (zero_lt_iff.2 hg.ne_zero)
  · rw [Valuation.map_mul, ← hf.map_eq]
    exact mul_lt_mul_of_pos_left hg (zero_lt_iff.2 hf.ne_zero)

end MuEquiv

/-- The polynomial `φ` `μ`-divides `φ * h` if `μ (φ * h) ≠ 0`. -/
theorem muDvd_mul_self {φ h : K[X]} (h0 : μ (φ * h) ≠ 0) : MuDvd μ φ (φ * h) :=
  ⟨h, MuEquiv.refl h0⟩

/-- If `φ` `μ`-divides `f`, then `φ` `μ`-divides each polynomial that is `μ`-equivalent to `f`. -/
theorem MuDvd.of_muEquiv {φ f g : K[X]} (hf : MuDvd μ φ f) (hfg : MuEquiv μ f g) :
    MuDvd μ φ g := by
  obtain ⟨h, hh⟩ := hf
  exact ⟨h, hfg.symm.trans hh⟩

/-- No polynomial `μ`-divides `0`. -/
theorem not_muDvd_zero (φ : K[X]) : ¬ MuDvd μ φ 0 := by
  rintro ⟨h, hh⟩
  exact hh.ne_zero (Valuation.map_zero μ)

/-- The polynomial `1` `μ`-divides `1`. -/
theorem muDvd_one_one : MuDvd μ 1 1 :=
  ⟨1, by rw [mul_one]; exact MuEquiv.refl (by simp)⟩

namespace KeyPolynomial

variable {φ : K[X]}

/-- A key polynomial does not `μ`-divide `1`. Thus its initial form is not a unit. -/
theorem not_muDvd_one (hφ : KeyPolynomial μ φ) : ¬ MuDvd μ φ 1 :=
  hφ.isMuIrreducible.1

/-- A key polynomial is not `1`. -/
theorem ne_one (hφ : KeyPolynomial μ φ) : φ ≠ 1 := by
  rintro rfl
  exact hφ.not_muDvd_one muDvd_one_one

/-- A key polynomial has positive degree. -/
theorem natDegree_pos (hφ : KeyPolynomial μ φ) : 0 < φ.natDegree := by
  rw [Nat.pos_iff_ne_zero]
  intro h
  exact hφ.ne_one ((Polynomial.Monic.natDegree_eq_zero hφ.monic).1 h)

/-- A key polynomial is not a unit of `K[X]`. -/
theorem not_isUnit (hφ : KeyPolynomial μ φ) : ¬ IsUnit φ := by
  intro hu
  have := natDegree_eq_zero_of_isUnit hu
  exact (Nat.pos_iff_ne_zero.1 hφ.natDegree_pos) this

end KeyPolynomial

end Equiv

section Monomial

variable (v : Valuation K Γ₀) (γ : Γ₀)

/-- The monomial valuation `[v; X, γ]` of Lemma 3.3.2 as a function. It sends `f = ∑ aᵢ Xⁱ` to the maximum of `v aᵢ * γ ^ i`. In additive notation this is the minimum of `v(aᵢ) + iγ`. -/
noncomputable def monomialValuationFun (f : K[X]) : Γ₀ :=
  f.support.sup fun i => v (f.coeff i) * γ ^ i

variable {v γ}

/-- Each term `v aᵢ * γ ^ i` is at most the monomial value. -/
theorem le_monomialValuationFun (f : K[X]) (i : ℕ) :
    v (f.coeff i) * γ ^ i ≤ monomialValuationFun v γ f := by
  by_cases hi : i ∈ f.support
  · exact Finset.le_sup (f := fun i => v (f.coeff i) * γ ^ i) hi
  · rw [notMem_support_iff.1 hi, Valuation.map_zero, zero_mul]
    exact zero_le

/-- The monomial value is at most `c` if and only if each term `v aᵢ * γ ^ i` is at most `c`. -/
theorem monomialValuationFun_le_iff {f : K[X]} {c : Γ₀} :
    monomialValuationFun v γ f ≤ c ↔ ∀ i, v (f.coeff i) * γ ^ i ≤ c := by
  refine ⟨fun h i => (le_monomialValuationFun f i).trans h, fun h => ?_⟩
  exact Finset.sup_le fun i _ => h i

/-- A nonzero monomial value is the value of one term. -/
theorem exists_eq_monomialValuationFun {f : K[X]} (hf : monomialValuationFun v γ f ≠ 0) :
    ∃ i, v (f.coeff i) * γ ^ i = monomialValuationFun v γ f := by
  have hs : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hf
    simp [monomialValuationFun, h, bot_eq_zero]
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup f.support hs fun i => v (f.coeff i) * γ ^ i
  exact ⟨i, hi.symm⟩

/-- The monomial valuation extends `v`. -/
theorem monomialValuationFun_C (a : K) : monomialValuationFun v γ (C a) = v a := by
  refine le_antisymm (monomialValuationFun_le_iff.2 fun i => ?_) ?_
  · rw [coeff_C]
    split_ifs with hi
    · rw [hi, pow_zero, mul_one]
    · rw [Valuation.map_zero, zero_mul]
      exact zero_le
  · simpa using le_monomialValuationFun (v := v) (γ := γ) (C a) 0

/-- The monomial value of `0` is `0`. -/
theorem monomialValuationFun_zero : monomialValuationFun v γ 0 = 0 := by
  simpa using monomialValuationFun_C (v := v) (γ := γ) 0

/-- The monomial value of `1` is `1`. -/
theorem monomialValuationFun_one : monomialValuationFun v γ 1 = 1 := by
  simpa using monomialValuationFun_C (v := v) (γ := γ) 1

/-- The monomial value of `X` is `γ`. -/
theorem monomialValuationFun_X : monomialValuationFun v γ X = γ := by
  refine le_antisymm (monomialValuationFun_le_iff.2 fun i => ?_) ?_
  · rw [coeff_X]
    split_ifs with hi
    · rw [← hi, Valuation.map_one, one_mul, pow_one]
    · rw [Valuation.map_zero, zero_mul]
      exact zero_le
  · simpa using le_monomialValuationFun (v := v) (γ := γ) X 1

/-- The ultrametric inequality for the monomial valuation. -/
theorem monomialValuationFun_add_le_max (f g : K[X]) :
    monomialValuationFun v γ (f + g) ≤
      max (monomialValuationFun v γ f) (monomialValuationFun v γ g) := by
  refine monomialValuationFun_le_iff.2 fun i => ?_
  rw [coeff_add]
  calc v (f.coeff i + g.coeff i) * γ ^ i ≤ max (v (f.coeff i)) (v (g.coeff i)) * γ ^ i :=
        mul_le_mul_left (Valuation.map_add _ _ _) _
    _ = max (v (f.coeff i) * γ ^ i) (v (g.coeff i) * γ ^ i) := max_mul _ _ _
    _ ≤ _ := max_le_max (le_monomialValuationFun f i) (le_monomialValuationFun g i)

/-- The monomial value of a product is at most the product of the values. -/
theorem monomialValuationFun_mul_le (f g : K[X]) :
    monomialValuationFun v γ (f * g) ≤
      monomialValuationFun v γ f * monomialValuationFun v γ g := by
  refine monomialValuationFun_le_iff.2 fun n => ?_
  rw [coeff_mul]
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.antidiagonal n)
    (fun x => v (f.coeff x.1 * g.coeff x.2)) ⟨(0, n), by simp⟩
  have hsum := Valuation.map_sum_le v hmax
  calc v (∑ x ∈ Finset.antidiagonal n, f.coeff x.1 * g.coeff x.2) * γ ^ n
      ≤ v (f.coeff k.1 * g.coeff k.2) * γ ^ n := mul_le_mul_left hsum _
    _ = (v (f.coeff k.1) * γ ^ k.1) * (v (g.coeff k.2) * γ ^ k.2) := by
        rw [← Finset.mem_antidiagonal.1 hk, pow_add, Valuation.map_mul]
        exact mul_mul_mul_comm _ _ _ _
    _ ≤ _ := mul_le_mul' (le_monomialValuationFun f _) (le_monomialValuationFun g _)

/-- Lemma 3.3.2 of the handbook: the monomial value of a product is the product of the values. Let `i₀` and `j₀` be the smallest indices where the values of `f` and `g` are attained. Then the coefficient of `X ^ (i₀ + j₀)` in `f * g` has the value of `aᵢ₀ * bⱼ₀`, because each other term of this coefficient has a smaller value. -/
theorem monomialValuationFun_mul (f g : K[X]) :
    monomialValuationFun v γ (f * g) =
      monomialValuationFun v γ f * monomialValuationFun v γ g := by
  refine le_antisymm (monomialValuationFun_mul_le f g) ?_
  by_cases hf : monomialValuationFun v γ f = 0
  · rw [hf, zero_mul]
    exact zero_le
  by_cases hg : monomialValuationFun v γ g = 0
  · rw [hg, mul_zero]
    exact zero_le
  classical
  have ef := exists_eq_monomialValuationFun hf
  have eg := exists_eq_monomialValuationFun hg
  set i₀ := Nat.find ef with hi₀
  set j₀ := Nat.find eg with hj₀
  have hfi₀ : v (f.coeff i₀) * γ ^ i₀ = monomialValuationFun v γ f := Nat.find_spec ef
  have hgj₀ : v (g.coeff j₀) * γ ^ j₀ = monomialValuationFun v γ g := Nat.find_spec eg
  -- terms below the minimal index are strictly smaller
  have hlt_f : ∀ i < i₀, v (f.coeff i) * γ ^ i < monomialValuationFun v γ f := fun i hi =>
    lt_of_le_of_ne (le_monomialValuationFun f i) (Nat.find_min ef hi)
  have hlt_g : ∀ j < j₀, v (g.coeff j) * γ ^ j < monomialValuationFun v γ g := fun j hj =>
    lt_of_le_of_ne (le_monomialValuationFun g j) (Nat.find_min eg hj)
  set n := i₀ + j₀
  have hmem : (i₀, j₀) ∈ Finset.antidiagonal n := Finset.mem_antidiagonal.2 rfl
  have key : ∀ x ∈ (Finset.antidiagonal n).erase (i₀, j₀),
      v (f.coeff x.1 * g.coeff x.2) < v (f.coeff i₀ * g.coeff j₀) := by
    intro x hx
    obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
    have hsum : x.1 + x.2 = i₀ + j₀ := Finset.mem_antidiagonal.1 hx
    have hlt : (v (f.coeff x.1) * γ ^ x.1) * (v (g.coeff x.2) * γ ^ x.2) <
        monomialValuationFun v γ f * monomialValuationFun v γ g := by
      rcases lt_or_ge x.1 i₀ with h1 | h1
      · exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos (hlt_f _ h1) (le_monomialValuationFun g _)
          zero_le (zero_lt_iff.2 hg)
      · have h2 : x.2 < j₀ := by
          by_contra h2
          push Not at h2
          exact hne (Prod.ext (by omega) (by omega))
        exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (le_monomialValuationFun f _) (hlt_g _ h2)
          zero_le (zero_lt_iff.2 hf)
    rw [← hfi₀, ← hgj₀] at hlt
    have e1 : (v (f.coeff x.1) * γ ^ x.1) * (v (g.coeff x.2) * γ ^ x.2) =
        v (f.coeff x.1 * g.coeff x.2) * γ ^ n := by
      rw [Valuation.map_mul, show n = x.1 + x.2 from hsum.symm, pow_add]
      exact mul_mul_mul_comm _ _ _ _
    have e2 : (v (f.coeff i₀) * γ ^ i₀) * (v (g.coeff j₀) * γ ^ j₀) =
        v (f.coeff i₀ * g.coeff j₀) * γ ^ n := by
      rw [Valuation.map_mul, pow_add]
      exact mul_mul_mul_comm _ _ _ _
    rw [e1, e2] at hlt
    exact lt_of_mul_lt_mul_right' hlt
  have hne0 : v (f.coeff i₀ * g.coeff j₀) ≠ 0 := by
    intro h0
    apply hf
    rw [← hfi₀]
    rw [Valuation.map_mul, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · rw [h0, zero_mul]
    · exfalso
      apply hg
      rw [← hgj₀, h0, zero_mul]
  have hcoeff : v ((f * g).coeff n) = v (f.coeff i₀ * g.coeff j₀) := by
    rw [coeff_mul, ← Finset.add_sum_erase _ _ hmem]
    exact Valuation.map_add_eq_of_lt_left _ (Valuation.map_sum_lt _ hne0 key)
  calc monomialValuationFun v γ f * monomialValuationFun v γ g
      = v (f.coeff i₀ * g.coeff j₀) * γ ^ n := by
        rw [← hfi₀, ← hgj₀, Valuation.map_mul, pow_add]
        exact mul_mul_mul_comm _ _ _ _
    _ = v ((f * g).coeff n) * γ ^ n := by rw [hcoeff]
    _ ≤ _ := le_monomialValuationFun _ _

variable (v γ)

/-- The monomial valuation `[v; X, γ]` on `K[X]` (Lemma 3.3.2 of Volume 3 of the handbook). -/
noncomputable def monomialValuation : Valuation K[X] Γ₀ where
  toFun := monomialValuationFun v γ
  map_zero' := monomialValuationFun_zero
  map_one' := monomialValuationFun_one
  map_mul' := monomialValuationFun_mul
  map_add_le_max' := monomialValuationFun_add_le_max

variable {v γ}

/-- The value of the monomial valuation is `monomialValuationFun`. -/
@[simp]
theorem monomialValuation_apply (f : K[X]) :
    monomialValuation v γ f = monomialValuationFun v γ f :=
  rfl

/-- The monomial valuation extends `v`. -/
theorem monomialValuation_C (a : K) : monomialValuation v γ (C a) = v a :=
  monomialValuationFun_C a

/-- The monomial valuation sends `X` to `γ`. -/
theorem monomialValuation_X : monomialValuation v γ X = γ :=
  monomialValuationFun_X

/-- If `γ ≠ 0`, then the support of the monomial valuation is `0`. -/
theorem monomialValuation_eq_zero_iff (hγ : γ ≠ 0) {f : K[X]} :
    monomialValuation v γ f = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ Valuation.map_zero _⟩
  by_contra hf
  obtain ⟨i, hi⟩ : ∃ i, f.coeff i ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hf (Polynomial.ext h')
  have hle := le_monomialValuationFun (v := v) (γ := γ) f i
  rw [monomialValuation_apply] at h
  rw [h, le_zero_iff, mul_eq_zero, Valuation.zero_iff] at hle
  rcases hle with hle | hle
  · exact hi hle
  · exact pow_ne_zero i hγ hle

/-- For the monomial valuation, `X` `μ`-divides `f` if and only if the constant coefficient of `f` has a value smaller than the value of `f`. -/
theorem muDvd_X_iff {μ : Valuation K[X] Γ₀} (hμ : ∀ f, μ f = monomialValuationFun v γ f)
    {f : K[X]} : MuDvd μ X f ↔ v (f.coeff 0) < μ f := by
  constructor
  · rintro ⟨h, hh⟩
    have h0 : (f - X * h).coeff 0 = f.coeff 0 := by simp
    calc v (f.coeff 0) = v ((f - X * h).coeff 0) * γ ^ 0 := by rw [h0, pow_zero, mul_one]
      _ ≤ μ (f - X * h) := (hμ _).symm ▸ le_monomialValuationFun _ _
      _ < μ f := hh
  · intro hf
    refine ⟨divX f, ?_⟩
    unfold MuEquiv
    have : f - X * divX f = C (f.coeff 0) := sub_eq_iff_eq_add'.2 (X_mul_divX_add f).symm
    rwa [this, hμ, monomialValuationFun_C]

/-- The polynomial `X` is a key polynomial for each valuation with the values of the monomial valuation `[v; X, γ]`. -/
theorem keyPolynomial_X_of_forall_eq {μ : Valuation K[X] Γ₀}
    (hμ : ∀ f, μ f = monomialValuationFun v γ f) : KeyPolynomial μ X := by
  refine ⟨monic_X, ⟨?_, fun f g hfg => ?_⟩, fun f hf hfX => ?_⟩
  · rw [muDvd_X_iff hμ]
    simp [hμ, monomialValuationFun_one]
  · rw [muDvd_X_iff hμ, Valuation.map_mul, mul_coeff_zero, Valuation.map_mul] at hfg
    rw [muDvd_X_iff hμ, muDvd_X_iff hμ]
    exact lt_or_lt_of_mul_lt_mul hfg
  · rw [natDegree_X]
    rw [muDvd_X_iff hμ] at hfX
    by_contra h
    push Not at h
    rw [Nat.lt_one_iff] at h
    rw [eq_C_of_natDegree_eq_zero h, hμ, monomialValuationFun_C, coeff_C_zero] at hfX
    exact lt_irrefl _ hfX

/-- The polynomial `X` is a key polynomial for the monomial valuation `[v; X, γ]`. -/
theorem keyPolynomial_X_monomialValuation : KeyPolynomial (monomialValuation v γ) X :=
  keyPolynomial_X_of_forall_eq fun _ => rfl

end Monomial

section Expansion

variable (φ : K[X])

/-- The coefficient `aⱼ` of the `φ`-expansion `f = ∑ aⱼ φ ^ j`. It is the remainder of `f /ₘ φ ^ j` modulo `φ`, computed by `j` divisions by `φ`. If `φ` is monic, then `aⱼ` has degree less than the degree of `φ`. -/
noncomputable def expansionCoeff (f : K[X]) (j : ℕ) : K[X] :=
  ((fun g => g /ₘ φ)^[j] f) %ₘ φ

variable {φ}

/-- The coefficient `a₀` is the remainder of `f` modulo `φ`. -/
theorem expansionCoeff_zero_eq_modByMonic (f : K[X]) : expansionCoeff φ f 0 = f %ₘ φ :=
  rfl

/-- The coefficients of `f` after `a₀` are the coefficients of `f /ₘ φ`. -/
theorem expansionCoeff_succ (f : K[X]) (j : ℕ) :
    expansionCoeff φ f (j + 1) = expansionCoeff φ (f /ₘ φ) j := by
  rw [expansionCoeff, expansionCoeff, Function.iterate_succ_apply]

/-- Repeated division of `0` by `φ` gives `0`. -/
theorem iterate_divByMonic_zero (j : ℕ) : (fun g => g /ₘ φ)^[j] 0 = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, zero_divByMonic, ih]

/-- The coefficients of the expansion of `0` are `0`. -/
theorem expansionCoeff_zero (j : ℕ) : expansionCoeff φ 0 j = 0 := by
  rw [expansionCoeff, iterate_divByMonic_zero, zero_modByMonic]

/-- The coefficients of the expansion are additive. -/
theorem expansionCoeff_add (f g : K[X]) (j : ℕ) :
    expansionCoeff φ (f + g) j = expansionCoeff φ f j + expansionCoeff φ g j := by
  induction j generalizing f g with
  | zero => exact add_modByMonic f g
  | succ j ih =>
    rw [expansionCoeff_succ, expansionCoeff_succ, expansionCoeff_succ, add_divByMonic, ih]

/-- The coefficients of the expansion of `-f` are the negatives of the coefficients of `f`. -/
theorem expansionCoeff_neg (f : K[X]) (j : ℕ) :
    expansionCoeff φ (-f) j = -expansionCoeff φ f j := by
  induction j generalizing f with
  | zero => exact neg_modByMonic f φ
  | succ j ih => rw [expansionCoeff_succ, expansionCoeff_succ, neg_divByMonic, ih]

/-- If `φ` is monic, then each coefficient of the expansion has degree less than the degree of `φ`. -/
theorem degree_expansionCoeff_lt (hφ : φ.Monic) (f : K[X]) (j : ℕ) :
    (expansionCoeff φ f j).degree < φ.degree :=
  degree_modByMonic_lt _ hφ

/-- After `N` steps of division, `f` is the sum of `aⱼ φ ^ j` for `j < N` and of `φ ^ N` times the quotient of the last step. -/
theorem eq_sum_expansionCoeff_add (f : K[X]) (N : ℕ) :
    f = ∑ j ∈ Finset.range N, expansionCoeff φ f j * φ ^ j +
      φ ^ N * (fun g => g /ₘ φ)^[N] f := by
  induction N generalizing f with
  | zero => simp
  | succ N ih =>
    have hs : ∑ j ∈ Finset.range N, expansionCoeff φ f (j + 1) * φ ^ (j + 1) =
        φ * ∑ j ∈ Finset.range N, expansionCoeff φ (f /ₘ φ) j * φ ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [expansionCoeff_succ]; ring
    calc f = f %ₘ φ + φ * (f /ₘ φ) := (modByMonic_add_div f φ).symm
      _ = f %ₘ φ + φ * (∑ j ∈ Finset.range N, expansionCoeff φ (f /ₘ φ) j * φ ^ j +
          φ ^ N * (fun g => g /ₘ φ)^[N] (f /ₘ φ)) := by rw [← ih]
      _ = _ := by
        rw [Finset.sum_range_succ', hs, Function.iterate_succ_apply,
          expansionCoeff_zero_eq_modByMonic, pow_zero, mul_one, pow_succ']
        ring

/-- If `φ` is monic of positive degree, then `N` divisions of `f` by `φ` give `0` when `N` is larger than the degree of `f`. -/
theorem iterate_divByMonic_eq_zero (hφ : φ.Monic) (hd : 0 < φ.natDegree) {f : K[X]} {N : ℕ}
    (hN : f.natDegree < N) : (fun g => g /ₘ φ)^[N] f = 0 := by
  induction N generalizing f with
  | zero => omega
  | succ N ih =>
    rw [Function.iterate_succ_apply]
    by_cases h0 : f /ₘ φ = 0
    · rw [h0, iterate_divByMonic_zero]
    · apply ih
      have hle : φ.degree ≤ f.degree := not_lt.1 (mt (divByMonic_eq_zero_iff hφ).2 h0)
      have := natDegree_le_natDegree hle
      rw [natDegree_divByMonic f hφ]
      omega

/-- If `φ` is monic of positive degree, then `aⱼ = 0` when `j` is larger than the degree of `f`. -/
theorem expansionCoeff_eq_zero (hφ : φ.Monic) (hd : 0 < φ.natDegree) {f : K[X]} {j : ℕ}
    (hj : f.natDegree < j) : expansionCoeff φ f j = 0 := by
  rw [expansionCoeff, iterate_divByMonic_eq_zero hφ hd hj, zero_modByMonic]

/-- The `φ`-expansion: if `φ` is monic of positive degree, then `f = ∑ aⱼ φ ^ j`. -/
theorem eq_sum_expansionCoeff (hφ : φ.Monic) (hd : 0 < φ.natDegree) (f : K[X]) :
    f = ∑ j ∈ Finset.range (f.natDegree + 1), expansionCoeff φ f j * φ ^ j := by
  conv_lhs => rw [eq_sum_expansionCoeff_add (φ := φ) f (f.natDegree + 1)]
  rw [iterate_divByMonic_eq_zero hφ hd (Nat.lt_succ_self _), mul_zero, add_zero]

/-- Division by `X` is `divX`. -/
theorem divByMonic_X_eq_divX (f : K[X]) : f /ₘ X = divX f :=
  (div_modByMonic_unique (divX f) (C (f.coeff 0)) monic_X
    ⟨by rw [add_comm]; exact X_mul_divX_add f,
      degree_C_le.trans_lt (by rw [degree_X]; exact zero_lt_one)⟩).1

/-- The coefficients of `divX` applied `j` times. -/
theorem coeff_iterate_divX (f : K[X]) (j n : ℕ) : (divX^[j] f).coeff n = f.coeff (n + j) := by
  induction j generalizing f with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, ih, coeff_divX, add_assoc]

/-- The `X`-expansion of `f` has the coefficients `C (f.coeff j)`. -/
theorem expansionCoeff_X (f : K[X]) (j : ℕ) : expansionCoeff X f j = C (f.coeff j) := by
  have h : (fun g : K[X] => g /ₘ X) = divX := funext divByMonic_X_eq_divX
  rw [expansionCoeff, h, modByMonic_X, ← coeff_zero_eq_eval_zero, coeff_iterate_divX, zero_add]

end Expansion

section Augmented

variable (μ : Valuation K[X] Γ₀) (φ : K[X]) (γ : Γ₀)

/-- The augmented valuation `[μ; φ, γ]` of Definition 3.3.4 as a function. It sends `f` with `φ`-expansion `∑ aⱼ φ ^ j` to the maximum of `μ aⱼ * γ ^ j`. In additive notation this is the minimum of `μ(aⱼ) + jγ`. The handbook takes `γ > μ(φ)` in additive notation, that is `γ < μ φ` here, and `γ = 0` is the case `γ = ∞`. The definition does not need these conditions. -/
noncomputable def augmentedValuationFun (f : K[X]) : Γ₀ :=
  (Finset.range (f.natDegree + 1)).sup fun j => μ (expansionCoeff φ f j) * γ ^ j

variable {μ φ γ}

/-- Each term `μ aⱼ * γ ^ j` is at most the augmented value. -/
theorem le_augmentedValuationFun (hφ : φ.Monic) (hd : 0 < φ.natDegree) (f : K[X]) (j : ℕ) :
    μ (expansionCoeff φ f j) * γ ^ j ≤ augmentedValuationFun μ φ γ f := by
  by_cases hj : j < f.natDegree + 1
  · exact Finset.le_sup (f := fun j => μ (expansionCoeff φ f j) * γ ^ j) (Finset.mem_range.2 hj)
  · rw [expansionCoeff_eq_zero hφ hd (by omega), Valuation.map_zero, zero_mul]
    exact zero_le

/-- The augmented value is at most `c` if and only if each term `μ aⱼ * γ ^ j` is at most `c`. -/
theorem augmentedValuationFun_le_iff (hφ : φ.Monic) (hd : 0 < φ.natDegree) {f : K[X]}
    {c : Γ₀} : augmentedValuationFun μ φ γ f ≤ c ↔ ∀ j, μ (expansionCoeff φ f j) * γ ^ j ≤ c :=
  ⟨fun h j => (le_augmentedValuationFun hφ hd f j).trans h,
    fun h => Finset.sup_le fun j _ => h j⟩

/-- The augmented value of `0` is `0`. -/
theorem augmentedValuationFun_zero : augmentedValuationFun μ φ γ 0 = 0 := by
  simp [augmentedValuationFun, expansionCoeff_zero]

/-- Theorem 3.3.5 (2) in part: the augmented valuation agrees with `μ` on the polynomials of degree less than the degree of `φ`. -/
theorem augmentedValuationFun_of_degree_lt (hφ : φ.Monic) (hd : 0 < φ.natDegree) {f : K[X]}
    (hf : f.degree < φ.degree) : augmentedValuationFun μ φ γ f = μ f := by
  have h0 : expansionCoeff φ f 0 = f := (modByMonic_eq_self_iff hφ).2 hf
  refine le_antisymm ((augmentedValuationFun_le_iff hφ hd).2 fun j => ?_) ?_
  · cases j with
    | zero => rw [h0, pow_zero, mul_one]
    | succ j =>
      rw [expansionCoeff_succ, (divByMonic_eq_zero_iff hφ).2 hf, expansionCoeff_zero,
        Valuation.map_zero, zero_mul]
      exact zero_le
  · simpa [h0] using le_augmentedValuationFun (μ := μ) (γ := γ) hφ hd f 0

/-- The augmented valuation agrees with `μ` on the constants. Thus it extends `v` if `μ` extends `v`. -/
theorem augmentedValuationFun_C (hφ : φ.Monic) (hd : 0 < φ.natDegree) (a : K) :
    augmentedValuationFun μ φ γ (C a) = μ (C a) :=
  augmentedValuationFun_of_degree_lt hφ hd
    (degree_C_le.trans_lt (natDegree_pos_iff_degree_pos.1 hd))

/-- The augmented value of `1` is `1`. -/
theorem augmentedValuationFun_one (hφ : φ.Monic) (hd : 0 < φ.natDegree) :
    augmentedValuationFun μ φ γ 1 = 1 := by
  simpa using augmentedValuationFun_C (μ := μ) (γ := γ) hφ hd 1

/-- Theorem 3.3.5 (2) in part: the augmented valuation sends `φ` to `γ`. -/
theorem augmentedValuationFun_self (hφ : φ.Monic) (hd : 0 < φ.natDegree) :
    augmentedValuationFun μ φ γ φ = γ := by
  have h1 : (1 : K[X]).degree < φ.degree := by
    rw [degree_one]
    exact natDegree_pos_iff_degree_pos.1 hd
  have hdiv : φ /ₘ φ = 1 := by
    simpa using mul_divByMonic_cancel_left (1 : K[X]) hφ
  have e1 : expansionCoeff φ φ 1 = 1 := by
    rw [expansionCoeff_succ, hdiv, expansionCoeff_zero_eq_modByMonic,
      (modByMonic_eq_self_iff hφ).2 h1]
  refine le_antisymm ((augmentedValuationFun_le_iff hφ hd).2 fun j => ?_) ?_
  · match j with
    | 0 =>
      rw [expansionCoeff_zero_eq_modByMonic, modByMonic_self hφ, Valuation.map_zero, zero_mul]
      exact zero_le
    | 1 => rw [e1, Valuation.map_one, one_mul, pow_one]
    | j + 2 =>
      rw [expansionCoeff_succ, expansionCoeff_succ, hdiv, (divByMonic_eq_zero_iff hφ).2 h1,
        expansionCoeff_zero, Valuation.map_zero, zero_mul]
      exact zero_le
  · simpa [e1] using le_augmentedValuationFun (μ := μ) (γ := γ) hφ hd φ 1

/-- The ultrametric inequality for the augmented valuation. -/
theorem augmentedValuationFun_add_le_max (hφ : φ.Monic) (hd : 0 < φ.natDegree) (f g : K[X]) :
    augmentedValuationFun μ φ γ (f + g) ≤
      max (augmentedValuationFun μ φ γ f) (augmentedValuationFun μ φ γ g) := by
  refine (augmentedValuationFun_le_iff hφ hd).2 fun j => ?_
  rw [expansionCoeff_add]
  calc μ (expansionCoeff φ f j + expansionCoeff φ g j) * γ ^ j
      ≤ max (μ (expansionCoeff φ f j)) (μ (expansionCoeff φ g j)) * γ ^ j :=
        mul_le_mul_left (Valuation.map_add _ _ _) _
    _ = max (μ (expansionCoeff φ f j) * γ ^ j) (μ (expansionCoeff φ g j) * γ ^ j) :=
        max_mul _ _ _
    _ ≤ _ := max_le_max (le_augmentedValuationFun hφ hd f j) (le_augmentedValuationFun hφ hd g j)

/-- The augmented value of `-f` is the augmented value of `f`. -/
theorem augmentedValuationFun_neg (f : K[X]) :
    augmentedValuationFun μ φ γ (-f) = augmentedValuationFun μ φ γ f := by
  simp only [augmentedValuationFun, natDegree_neg, expansionCoeff_neg, Valuation.map_neg]

/-- The value of `f` is at most its value for the augmentation `[μ; φ, μ φ]`. In additive notation, `μ(f)` is at least the minimum of `μ(aⱼ) + jμ(φ)`. -/
theorem map_le_augmentedValuationFun (hφ : φ.Monic) (hd : 0 < φ.natDegree) (f : K[X]) :
    μ f ≤ augmentedValuationFun μ φ (μ φ) f := by
  conv_lhs => rw [eq_sum_expansionCoeff hφ hd f]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [Valuation.map_mul, Valuation.map_pow]
  exact le_augmentedValuationFun hφ hd f j

/-- If `μ` extends `v`, then the augmentation `[μ; X, γ]` is the monomial valuation `[v; X, γ]`. -/
theorem augmentedValuationFun_X {v : Valuation K Γ₀} (hμ : ∀ a, μ (C a) = v a) (f : K[X]) :
    augmentedValuationFun μ X γ f = monomialValuationFun v γ f := by
  have hd : 0 < (X : K[X]).natDegree := by rw [natDegree_X]; exact zero_lt_one
  have key : ∀ j, μ (expansionCoeff X f j) * γ ^ j = v (f.coeff j) * γ ^ j := fun j => by
    rw [expansionCoeff_X, hμ]
  refine le_antisymm ((augmentedValuationFun_le_iff monic_X hd).2 fun j => ?_)
    (monomialValuationFun_le_iff.2 fun j => ?_)
  · rw [key]
    exact le_monomialValuationFun f j
  · rw [← key]
    exact le_augmentedValuationFun monic_X hd f j

end Augmented

end Singularity
