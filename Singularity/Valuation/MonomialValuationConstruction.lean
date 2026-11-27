/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Order.AddGroupWithTop

/-!
# The construction of a monomial valuation

This file proves Volume 3, Lemma 1.6.1 of the handbook. Let `Γ` be an ordered group and let `γ : σ → Γ`. For `a ∈ ℕ^σ` put `a · γ = ∑ a_i γ_i`. For a nonzero polynomial `f = ∑_a c_a x^a` put `v(f) = min {a · γ : c_a ≠ 0}`. Then `v(f/g) = v(f) - v(g)` defines a valuation of `k(x)/k`.

The file writes valuations additively, with values in `WithTop Γ`. The value of `0` is `⊤`. The weight `a · γ` is Mathlib's `Finsupp.weight γ a`.

The proof follows the handbook. The inequality `v(f) + v(g) ≤ v(fg)` holds because each monomial of `fg` is a product of a monomial of `f` and a monomial of `g`. For the other inequality, let `f_0` and `g_0` be the parts of `f` and `g` of least weight. They are weighted homogeneous and not zero, so `f_0 g_0` is weighted homogeneous of weight `v(f) + v(g)` and not zero. A monomial of `f_0 g_0` has the same coefficient in `fg`, because the other products of monomials have a larger weight.

The ring of coefficients is a domain `k`. The valuation extends to the fraction field because its support is zero.

## Main results

* `Singularity.monomialWeight`: the function `v` on polynomials.
* `Singularity.monomialWeight_mul`: `v(fg) = v(f) + v(g)`.
* `Singularity.monomialAddValuation`: `v` as an additive valuation of the polynomial ring.
* `Singularity.monomialAddValuationFrac`: the extension to `FractionRing (MvPolynomial σ k)`.
* `Singularity.monomialAddValuationFrac_mk'`: `v(f/g) = v(f) - v(g)`.
* `Singularity.monomialAddValuationFrac_C`: `v(c) = 0` for each nonzero `c ∈ k`, so `v` is a valuation of `k(x)/k`.
* `Singularity.monomialAddValuationFrac_X`: `v(x_i) = γ_i`.
-/

namespace Singularity

open MvPolynomial Finsupp Pointwise

variable {σ : Type*} {k : Type*} [CommRing k]
variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]

/-- The monomial weight `v(f) = min {a · γ : c_a ≠ 0}`, with `v(0) = ⊤`. -/
noncomputable def monomialWeight (γ : σ → Γ) (f : MvPolynomial σ k) : WithTop Γ :=
  f.support.inf fun a => ((weight γ a : Γ) : WithTop Γ)

theorem monomialWeight_zero (γ : σ → Γ) : monomialWeight γ (0 : MvPolynomial σ k) = ⊤ := by
  simp [monomialWeight]

theorem monomialWeight_le {γ : σ → Γ} {f : MvPolynomial σ k} {a : σ →₀ ℕ}
    (ha : f.coeff a ≠ 0) : monomialWeight γ f ≤ (weight γ a : WithTop Γ) :=
  Finset.inf_le (MvPolynomial.mem_support_iff.mpr ha)

theorem le_monomialWeight_iff {γ : σ → Γ} {f : MvPolynomial σ k} {c : WithTop Γ} :
    c ≤ monomialWeight γ f ↔ ∀ a, f.coeff a ≠ 0 → c ≤ (weight γ a : WithTop Γ) := by
  simp [monomialWeight, Finset.le_inf_iff]

theorem monomialWeight_eq_top_iff {γ : σ → Γ} {f : MvPolynomial σ k} :
    monomialWeight γ f = ⊤ ↔ f = 0 := by
  constructor
  · intro h
    by_contra hf
    obtain ⟨a, ha⟩ := ne_zero_iff.mp hf
    have := monomialWeight_le (γ := γ) ha
    rw [h] at this
    exact WithTop.coe_ne_top (top_le_iff.mp this)
  · rintro rfl; exact monomialWeight_zero γ

/-- A nonzero polynomial has a monomial of least weight. -/
theorem exists_monomialWeight_eq {γ : σ → Γ} {f : MvPolynomial σ k} (hf : f ≠ 0) :
    ∃ a, f.coeff a ≠ 0 ∧ monomialWeight γ f = (weight γ a : WithTop Γ) := by
  have hs : f.support.Nonempty := support_nonempty.mpr hf
  obtain ⟨a, ha, h⟩ := Finset.exists_mem_eq_inf f.support hs
    (fun a => ((weight γ a : Γ) : WithTop Γ))
  exact ⟨a, MvPolynomial.mem_support_iff.mp ha, h⟩

theorem monomialWeight_one [Nontrivial k] (γ : σ → Γ) :
    monomialWeight γ (1 : MvPolynomial σ k) = 0 := by
  classical
  simp [monomialWeight, support_one]

theorem min_monomialWeight_le_add (γ : σ → Γ) (f g : MvPolynomial σ k) :
    min (monomialWeight γ f) (monomialWeight γ g) ≤ monomialWeight γ (f + g) := by
  rw [le_monomialWeight_iff]
  intro a ha
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at ha
  by_cases hf : f.coeff a = 0
  · rw [hf, zero_add] at ha
    exact min_le_of_right_le (monomialWeight_le ha)
  · exact min_le_of_left_le (monomialWeight_le hf)

variable [IsOrderedAddMonoid Γ]

theorem add_monomialWeight_le_mul (γ : σ → Γ) (f g : MvPolynomial σ k) :
    monomialWeight γ f + monomialWeight γ g ≤ monomialWeight γ (f * g) := by
  classical
  rw [le_monomialWeight_iff]
  intro a ha
  have hmem : a ∈ f.support + g.support := support_mul f g (MvPolynomial.mem_support_iff.mpr ha)
  obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.mp hmem
  rw [map_add, WithTop.coe_add]
  exact add_le_add (monomialWeight_le (MvPolynomial.mem_support_iff.mp hb))
    (monomialWeight_le (MvPolynomial.mem_support_iff.mp hc))

/-- The key step. If `f` and `g` are not zero, then `fg` has a monomial of weight
`v(f) + v(g)`. -/
theorem monomialWeight_mul_le [IsDomain k] (γ : σ → Γ) {f g : MvPolynomial σ k}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    monomialWeight γ (f * g) ≤ monomialWeight γ f + monomialWeight γ g := by
  classical
  obtain ⟨a₀, ha₀, hm⟩ := exists_monomialWeight_eq (γ := γ) hf
  obtain ⟨b₀, hb₀, hn⟩ := exists_monomialWeight_eq (γ := γ) hg
  set m := weight γ a₀
  set n := weight γ b₀
  have hfm : ∀ b, f.coeff b ≠ 0 → m ≤ weight γ b := fun b hb => by
    have := monomialWeight_le (γ := γ) hb
    rw [hm] at this
    exact WithTop.coe_le_coe.mp this
  have hgn : ∀ c, g.coeff c ≠ 0 → n ≤ weight γ c := fun c hc => by
    have := monomialWeight_le (γ := γ) hc
    rw [hn] at this
    exact WithTop.coe_le_coe.mp this
  set f₀ := weightedHomogeneousComponent γ m f
  set g₀ := weightedHomogeneousComponent γ n g
  have hf₀ : f₀ ≠ 0 := by
    intro h
    apply ha₀
    have h1 : f₀.coeff a₀ = f.coeff a₀ := by
      simp [f₀, m, coeff_weightedHomogeneousComponent]
    rw [← h1, h]
    simp
  have hg₀ : g₀ ≠ 0 := by
    intro h
    apply hb₀
    have h1 : g₀.coeff b₀ = g.coeff b₀ := by
      simp [g₀, n, coeff_weightedHomogeneousComponent]
    rw [← h1, h]
    simp
  have hhom : IsWeightedHomogeneous γ (f₀ * g₀) (m + n) :=
    (weightedHomogeneousComponent_isWeightedHomogeneous m f).mul
      (weightedHomogeneousComponent_isWeightedHomogeneous n g)
  obtain ⟨e, he⟩ := ne_zero_iff.mp (mul_ne_zero hf₀ hg₀)
  have hwe : weight γ e = m + n := hhom he
  have hcoeff : (f * g).coeff e = (f₀ * g₀).coeff e := by
    rw [coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hsum : weight γ p.1 + weight γ p.2 = m + n := by
      rw [← map_add, Finset.mem_antidiagonal.mp hp, hwe]
    simp only [f₀, g₀, coeff_weightedHomogeneousComponent]
    by_cases h1 : weight γ p.1 = m
    · have h2 : weight γ p.2 = n := by
        rw [h1] at hsum; exact add_left_cancel hsum
      simp only [h1, h2, ↓reduceIte]
    · simp only [h1, ↓reduceIte, zero_mul]
      rcases lt_or_gt_of_ne h1 with hlt | hgt
      · have : f.coeff p.1 = 0 := by
          by_contra h; exact absurd (hfm _ h) (not_le.mpr hlt)
        rw [this, zero_mul]
      · have hlt : weight γ p.2 < n := by
          by_contra h
          have := add_lt_add_of_lt_of_le hgt (not_lt.mp h)
          rw [hsum] at this
          exact lt_irrefl _ this
        have : g.coeff p.2 = 0 := by
          by_contra h; exact absurd (hgn _ h) (not_le.mpr hlt)
        rw [this, mul_zero]
  have hne : (f * g).coeff e ≠ 0 := by rw [hcoeff]; exact he
  calc monomialWeight γ (f * g) ≤ (weight γ e : WithTop Γ) := monomialWeight_le hne
    _ = monomialWeight γ f + monomialWeight γ g := by
      rw [hm, hn, hwe, WithTop.coe_add]

/-- `v(fg) = v(f) + v(g)`. -/
theorem monomialWeight_mul [IsDomain k] (γ : σ → Γ) (f g : MvPolynomial σ k) :
    monomialWeight γ (f * g) = monomialWeight γ f + monomialWeight γ g := by
  by_cases hf : f = 0
  · simp [hf, monomialWeight_zero]
  by_cases hg : g = 0
  · simp [hg, monomialWeight_zero]
  exact le_antisymm (monomialWeight_mul_le γ hf hg) (add_monomialWeight_le_mul γ f g)

/-- The monomial weight as an additive valuation of the polynomial ring. -/
noncomputable def monomialAddValuation [IsDomain k] (γ : σ → Γ) :
    AddValuation (MvPolynomial σ k) (WithTop Γ) :=
  AddValuation.of (monomialWeight γ) (monomialWeight_zero γ) (monomialWeight_one γ)
    (min_monomialWeight_le_add γ) (monomialWeight_mul γ)

theorem monomialAddValuation_apply [IsDomain k] (γ : σ → Γ) (f : MvPolynomial σ k) :
    monomialAddValuation γ f = monomialWeight γ f := rfl

theorem monomialAddValuation_supp [IsDomain k] (γ : σ → Γ) :
    (monomialAddValuation (k := k) γ).supp = ⊥ := by
  ext f
  rw [AddValuation.mem_supp_iff, monomialAddValuation_apply, monomialWeight_eq_top_iff,
    Ideal.mem_bot]

instance [IsDomain k] (γ : σ → Γ) : (monomialAddValuation (k := k) γ).supp.IsPrime := by
  rw [monomialAddValuation_supp]
  exact Ideal.isPrime_bot

theorem nonZeroDivisors_le_primeCompl [IsDomain k] (γ : σ → Γ) :
    nonZeroDivisors (MvPolynomial σ k) ≤ (monomialAddValuation (k := k) γ).supp.primeCompl := by
  intro f hf
  change f ∉ (monomialAddValuation (k := k) γ).supp
  rw [monomialAddValuation_supp, Ideal.mem_bot]
  exact nonZeroDivisors.ne_zero hf

/-- Volume 3, Lemma 1.6.1. The monomial valuation of the fraction field `k(x)`. -/
noncomputable def monomialAddValuationFrac [IsDomain k] (γ : σ → Γ) :
    AddValuation (FractionRing (MvPolynomial σ k)) (WithTop Γ) :=
  AddValuation.ofValuation (Valuation.extendToLocalization
    (AddValuation.toValuation (monomialAddValuation (k := k) γ))
    (nonZeroDivisors_le_primeCompl γ) (FractionRing (MvPolynomial σ k)))

theorem monomialAddValuationFrac_algebraMap [IsDomain k] (γ : σ → Γ) (f : MvPolynomial σ k) :
    monomialAddValuationFrac γ (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k)) f) =
      monomialWeight γ f :=
  congrArg (fun x => OrderDual.ofDual (Multiplicative.toAdd x))
    (Valuation.extendToLocalization_apply_map_apply
      (AddValuation.toValuation (monomialAddValuation (k := k) γ))
      (nonZeroDivisors_le_primeCompl γ) (FractionRing (MvPolynomial σ k)) f)

/-- `v(f/g) = v(f) - v(g)`, the formula of the handbook. -/
theorem monomialAddValuationFrac_mk' [IsDomain k] (γ : σ → Γ) (f : MvPolynomial σ k)
    (g : nonZeroDivisors (MvPolynomial σ k)) :
    monomialAddValuationFrac γ (IsLocalization.mk' (FractionRing (MvPolynomial σ k)) f g) =
      monomialWeight γ f - monomialWeight γ (g : MvPolynomial σ k) := by
  have h := congrArg (fun x => OrderDual.ofDual (Multiplicative.toAdd x))
    (Valuation.extendToLocalization_mk' (AddValuation.toValuation (monomialAddValuation (k := k) γ))
      (nonZeroDivisors_le_primeCompl γ) (FractionRing (MvPolynomial σ k)) f g)
  exact h.trans (sub_eq_add_neg _ _).symm

omit [IsOrderedAddMonoid Γ] in
theorem monomialWeight_C (γ : σ → Γ) {c : k} (hc : c ≠ 0) :
    monomialWeight γ (C c : MvPolynomial σ k) = 0 := by
  classical
  simp [monomialWeight, support_C, hc]

omit [IsOrderedAddMonoid Γ] in
theorem monomialWeight_X [Nontrivial k] (γ : σ → Γ) (i : σ) :
    monomialWeight γ (X i : MvPolynomial σ k) = (γ i : WithTop Γ) := by
  classical
  simp [monomialWeight, support_X, weight_apply]

/-- The valuation is trivial on `k`, so it is a valuation of `k(x)/k`. -/
theorem monomialAddValuationFrac_C [IsDomain k] (γ : σ → Γ) {c : k} (hc : c ≠ 0) :
    monomialAddValuationFrac γ
      (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k)) (C c)) = 0 := by
  rw [monomialAddValuationFrac_algebraMap, monomialWeight_C γ hc]

theorem monomialAddValuationFrac_X [IsDomain k] (γ : σ → Γ) (i : σ) :
    monomialAddValuationFrac γ
      (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k)) (X i)) =
      (γ i : WithTop Γ) := by
  rw [monomialAddValuationFrac_algebraMap, monomialWeight_X]

end Singularity
