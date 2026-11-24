/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.Order
import Mathlib.Analysis.Convex.Combination
import Mathlib.Basic.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The Newton polyhedron and the initial forms of a polynomial

Let `f` be a polynomial in `R[x_i : i ∈ σ]`. Its Newton polyhedron is the subset

  `N(f) = conv(supp f) + ℝ_{≥0}^σ`

of `σ → ℝ`: the convex hull of the exponents of the monomials of `f`, plus the positive orthant.
This is the definition of Hironaka [Hir67] and of Hauser [Hau03, §8] for a power series at the
origin, restricted to polynomials. We take the real convex hull in `σ → ℝ`, and not the set of
lattice points above the support, because the faces of the polyhedron, the supporting
hyperplanes of a weight vector, and the Minkowski sum of two polyhedra are statements about real
convex sets. Only the positive orthant is added, so `N(f)` records the order of `f` at the
origin and not its degree. The polyhedron of `0` is empty.

The initial form of `f` for a weight vector `w : σ → ℕ` is the part of `f` of the smallest
`w`-weight. Its support is the face of `N(f)` on which the linear form `v ↦ ∑ w_i v_i` is
smallest. For `w = 1` it is the usual initial form, the homogeneous part of degree `ord f`.

## Main definitions

* `Singularity.newtonPolyhedron f`: the Newton polyhedron `conv(supp f) + ℝ_{≥0}^σ`.
* `Singularity.weightedOrd w f`: the order of `f` for the weight vector `w`.
* `Singularity.initialForm w f`: the initial form of `f` for `w`.

## Main results

* `convex_newtonPolyhedron`, `newtonPolyhedron_add_orthant`: `N(f)` is convex and is stable
  under the addition of the orthant.
* `newtonPolyhedron_monomial`: the polyhedron of a monomial is a translate of the orthant.
* `newtonPolyhedron_mul_subset`: `N(fg) ⊆ N(f) + N(g)`, the Minkowski sum.
* `newtonPolyhedron_add_subset`: `N(f + g) ⊆ conv(N(f) ∪ N(g))`.
* `isLeast_weight_newtonPolyhedron`: the smallest value of `v ↦ ∑ w_i v_i` on `N(f)` is the
  weighted order of `f`.
* `isLeast_sum_newtonPolyhedron`: the order of `f` is the smallest total degree on `N(f)`.
* `isWeightedHomogeneous_initialForm`, `initialForm_ne_zero`, `mem_support_initialForm`: the
  initial form is weighted homogeneous, nonzero for `f ≠ 0`, and its support is the face of
  smallest weight.
* `initialForm_mul`: over a ring without zero divisors, the initial form of a product is the
  product of the initial forms.
* `initialForm_add_of_lt`: a weighted homogeneous `P ≠ 0` is the initial form of `P + Q` when `Q`
  has a larger weighted order.

## References

* [Hir67] H. Hironaka, *Characteristic polyhedra of singularities*, J. Math. Kyoto Univ. 7
  (1967).
* [Hau03] H. Hauser, *The Hironaka theorem on resolution of singularities*, Bull. AMS 40 (2003).
-/

open MvPolynomial Finsupp Pointwise

namespace Singularity

variable {σ R : Type*} [CommSemiring R]

/-! ### The Newton polyhedron -/

/-- An exponent vector as a point of `σ → ℝ`. This is an additive map. -/
noncomputable def expToReal : (σ →₀ ℕ) →+ (σ → ℝ) where
  toFun d i := d i
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

@[simp]
theorem expToReal_apply (d : σ →₀ ℕ) (i : σ) : expToReal d i = d i := rfl

/-- The positive orthant `ℝ_{≥0}^σ` of `σ → ℝ`. -/
def orthant (σ : Type*) : Set (σ → ℝ) := {v | ∀ i, 0 ≤ v i}

theorem convex_orthant : Convex ℝ (orthant σ) := by
  intro u hu v hv a b ha hb _ i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hu i)) (mul_nonneg hb (hv i))

theorem zero_mem_orthant : (0 : σ → ℝ) ∈ orthant σ := fun _ => le_rfl

theorem orthant_add_orthant : orthant σ + orthant σ = orthant σ := by
  refine subset_antisymm ?_ fun v hv => ⟨v, hv, 0, zero_mem_orthant, add_zero v⟩
  rintro _ ⟨u, hu, v, hv, rfl⟩ i
  exact add_nonneg (hu i) (hv i)

theorem convexHull_orthant : convexHull ℝ (orthant σ) = orthant σ :=
  convex_orthant.convexHull_eq

/-- The Newton polyhedron of a polynomial: the convex hull of the exponents of its monomials,
plus the positive orthant. -/
noncomputable def newtonPolyhedron (f : MvPolynomial σ R) : Set (σ → ℝ) :=
  convexHull ℝ (expToReal '' (f.support : Set (σ →₀ ℕ))) + orthant σ

theorem convex_newtonPolyhedron (f : MvPolynomial σ R) : Convex ℝ (newtonPolyhedron f) :=
  (convex_convexHull ℝ _).add convex_orthant

theorem expToReal_mem_newtonPolyhedron {f : MvPolynomial σ R} {d : σ →₀ ℕ}
    (hd : d ∈ f.support) : expToReal d ∈ newtonPolyhedron f :=
  ⟨expToReal d, subset_convexHull ℝ _ ⟨d, hd, rfl⟩, 0, zero_mem_orthant, add_zero _⟩

theorem newtonPolyhedron_add_orthant (f : MvPolynomial σ R) :
    newtonPolyhedron f + orthant σ = newtonPolyhedron f := by
  rw [newtonPolyhedron, add_assoc, orthant_add_orthant]

/-- `N(f)` is the convex hull of the support plus the orthant, and also the convex hull of the
support moved by the orthant. -/
theorem newtonPolyhedron_eq_convexHull (f : MvPolynomial σ R) :
    newtonPolyhedron f = convexHull ℝ (expToReal '' (f.support : Set (σ →₀ ℕ)) + orthant σ) := by
  rw [convexHull_add, convexHull_orthant, newtonPolyhedron]

@[simp]
theorem newtonPolyhedron_zero : newtonPolyhedron (0 : MvPolynomial σ R) = ∅ := by
  simp [newtonPolyhedron]

/-- The Newton polyhedron of a monomial `c x^d` with `c ≠ 0` is the orthant moved to `d`. -/
theorem newtonPolyhedron_monomial {d : σ →₀ ℕ} {c : R} (hc : c ≠ 0) :
    newtonPolyhedron (monomial d c) = {expToReal d} + orthant σ := by
  classical
  rw [newtonPolyhedron, support_monomial, ite_eq_right hc, Finset.coe_singleton, Set.image_singleton,
    convexHull_singleton]

/-- The Newton polyhedron of a product lies in the Minkowski sum of the Newton polyhedra. Over a
domain the two are equal; the inclusion is the half that holds over each ring. -/
theorem newtonPolyhedron_mul_subset (f g : MvPolynomial σ R) :
    newtonPolyhedron (f * g) ⊆ newtonPolyhedron f + newtonPolyhedron g := by
  classical
  have hs : expToReal '' ((f * g).support : Set (σ →₀ ℕ)) ⊆
      expToReal '' (f.support : Set (σ →₀ ℕ)) + expToReal '' (g.support : Set (σ →₀ ℕ)) := by
    rw [← Set.image_add]
    refine Set.image_mono ?_
    rw [← Finset.coe_add]
    exact_mod_cast support_mul f g
  calc newtonPolyhedron (f * g)
      ⊆ convexHull ℝ (expToReal '' (f.support : Set (σ →₀ ℕ)) +
          expToReal '' (g.support : Set (σ →₀ ℕ))) + orthant σ :=
        Set.add_subset_add_right (convexHull_mono hs)
    _ = newtonPolyhedron f + newtonPolyhedron g := by
        rw [convexHull_add, newtonPolyhedron, newtonPolyhedron, add_add_add_comm,
          orthant_add_orthant]

/-- The Newton polyhedron of a sum lies in the convex hull of the union of the two polyhedra. -/
theorem newtonPolyhedron_add_subset (f g : MvPolynomial σ R) :
    newtonPolyhedron (f + g) ⊆ convexHull ℝ (newtonPolyhedron f ∪ newtonPolyhedron g) := by
  classical
  rw [newtonPolyhedron_eq_convexHull]
  refine convexHull_mono ?_
  have hs : ((f + g).support : Set (σ →₀ ℕ)) ⊆ (f.support : Set (σ →₀ ℕ)) ∪ g.support := by
    exact_mod_cast MvPolynomial.support_add
  rintro _ ⟨_, ⟨d, hd, rfl⟩, v, hv, rfl⟩
  rcases hs hd with h | h
  · exact Or.inl ⟨expToReal d, subset_convexHull ℝ _ ⟨d, h, rfl⟩, v, hv, rfl⟩
  · exact Or.inr ⟨expToReal d, subset_convexHull ℝ _ ⟨d, h, rfl⟩, v, hv, rfl⟩

/-! ### Weighted orders and initial forms -/

/-- The order of `f` for a weight vector `w`: the smallest `w`-weight of a monomial of `f`, or
`⊤` for `f = 0`. -/
noncomputable def weightedOrd (w : σ → ℕ) (f : MvPolynomial σ R) : ℕ∞ :=
  (f : MvPowerSeries σ R).weightedOrder w

/-- For the weight `1` the weighted order is the order. -/
theorem weightedOrd_one (f : MvPolynomial σ R) : weightedOrd (fun _ => 1) f = ord f := rfl

theorem weightedOrd_le {w : σ → ℕ} {f : MvPolynomial σ R} {d : σ →₀ ℕ} (h : f.coeff d ≠ 0) :
    weightedOrd w f ≤ weight w d :=
  MvPowerSeries.weightedOrder_le w (by rwa [coeff_coe])

theorem coeff_eq_zero_of_lt_weightedOrd {w : σ → ℕ} {f : MvPolynomial σ R} {d : σ →₀ ℕ}
    (h : (weight w d : ℕ∞) < weightedOrd w f) : f.coeff d = 0 := by
  by_contra hd
  exact absurd (weightedOrd_le hd) (not_le.mpr h)

@[simp]
theorem weightedOrd_eq_top_iff {w : σ → ℕ} {f : MvPolynomial σ R} :
    weightedOrd w f = ⊤ ↔ f = 0 := by
  rw [weightedOrd, MvPowerSeries.weightedOrder_eq_top_iff, coe_eq_zero_iff]

theorem exists_coeff_ne_zero_and_weightedOrd_eq (w : σ → ℕ) {f : MvPolynomial σ R} (hf : f ≠ 0) :
    ∃ d : σ →₀ ℕ, f.coeff d ≠ 0 ∧ weightedOrd w f = weight w d := by
  have hfin : (weightedOrd w f).toNat = weightedOrd w f :=
    ENat.natCast_toNat (fun h => hf (weightedOrd_eq_top_iff.mp h))
  obtain ⟨d, hd, hdeg⟩ := MvPowerSeries.exists_coeff_ne_zero_and_weightedOrder w hfin
  rw [coeff_coe] at hd
  exact ⟨d, hd, hdeg.symm⟩

/-- The smallest value of the linear form `v ↦ ∑ w_i v_i` on the Newton polyhedron of `f ≠ 0` is
the weighted order of `f`. -/
theorem isLeast_weight_newtonPolyhedron [Fintype σ] (w : σ → ℕ) {f : MvPolynomial σ R}
    (hf : f ≠ 0) :
    IsLeast ((fun v : σ → ℝ => ∑ i, (w i : ℝ) * v i) '' newtonPolyhedron f)
      ((weightedOrd w f).toNat : ℝ) := by
  obtain ⟨d, hd, hdeg⟩ := exists_coeff_ne_zero_and_weightedOrd_eq w hf
  have hwd : (weightedOrd w f).toNat = weight w d := by rw [hdeg, ENat.toNat_natCast]
  have hweight : ∀ e : σ →₀ ℕ, (weight w e : ℝ) = ∑ i, (w i : ℝ) * expToReal e i := by
    intro e
    rw [weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    push_cast
    simp [mul_comm]
  refine ⟨⟨expToReal d, expToReal_mem_newtonPolyhedron (MvPolynomial.mem_support_iff.mpr hd), ?_⟩, ?_⟩
  · simp only [hwd, hweight]
  · rintro _ ⟨_, ⟨c, hc, v, hv, rfl⟩, rfl⟩
    have hH : convexHull ℝ (expToReal '' (f.support : Set (σ →₀ ℕ))) ⊆
        {u : σ → ℝ | ((weightedOrd w f).toNat : ℝ) ≤ ∑ i, (w i : ℝ) * u i} := by
      refine convexHull_min ?_ (convex_halfSpace_ge ?_ _)
      · rintro _ ⟨e, he, rfl⟩
        simp only [Set.mem_ofPred_eq, ← hweight]
        have := weightedOrd_le (w := w) (MvPolynomial.mem_support_iff.mp he)
        rw [hdeg, Nat.cast_le] at this
        rw [hwd]
        exact_mod_cast this
      · exact ⟨fun u v => by simp [mul_add, Finset.sum_add_distrib],
          fun a u => by simp [Finset.mul_sum, mul_left_comm]⟩
    have h1 := hH hc
    have h2 : 0 ≤ ∑ i, (w i : ℝ) * v i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hv i)
    simp only [Set.mem_ofPred_eq] at h1
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    linarith

/-- The order of `f ≠ 0` is the smallest total degree `∑ v_i` of a point `v` of the Newton
polyhedron. -/
theorem isLeast_sum_newtonPolyhedron [Fintype σ] {f : MvPolynomial σ R} (hf : f ≠ 0) :
    IsLeast ((fun v : σ → ℝ => ∑ i, v i) '' newtonPolyhedron f) ((ord f).toNat : ℝ) := by
  simpa [weightedOrd_one] using isLeast_weight_newtonPolyhedron (fun _ => 1) hf

/-- The initial form of `f` for the weight vector `w`: the sum of the terms of `f` of the smallest
`w`-weight. It is `0` for `f = 0`. -/
noncomputable def initialForm (w : σ → ℕ) (f : MvPolynomial σ R) : MvPolynomial σ R :=
  weightedHomogeneousComponent w (weightedOrd w f).toNat f

theorem coeff_initialForm (w : σ → ℕ) (f : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (initialForm w f).coeff d =
      if weight w d = (weightedOrd w f).toNat then f.coeff d else 0 :=
  coeff_weightedHomogeneousComponent _ _ _

theorem isWeightedHomogeneous_initialForm (w : σ → ℕ) (f : MvPolynomial σ R) :
    IsWeightedHomogeneous w (initialForm w f) (weightedOrd w f).toNat :=
  weightedHomogeneousComponent_isWeightedHomogeneous _ _

/-- The support of the initial form is the set of exponents of `f` of the smallest weight: the
face of the Newton polyhedron on which `v ↦ ∑ w_i v_i` is smallest. -/
theorem mem_support_initialForm {w : σ → ℕ} {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hf : f ≠ 0) :
    d ∈ (initialForm w f).support ↔ d ∈ f.support ∧ (weight w d : ℕ∞) = weightedOrd w f := by
  have hfin : ((weightedOrd w f).toNat : ℕ∞) = weightedOrd w f :=
    ENat.natCast_toNat (fun h => hf (weightedOrd_eq_top_iff.mp h))
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, coeff_initialForm]
  conv_rhs => rw [← hfin, Nat.cast_inj]
  split_ifs with h <;> simp [h]

theorem initialForm_ne_zero (w : σ → ℕ) {f : MvPolynomial σ R} (hf : f ≠ 0) :
    initialForm w f ≠ 0 := by
  obtain ⟨d, hd, hdeg⟩ := exists_coeff_ne_zero_and_weightedOrd_eq w hf
  intro h
  have := (mem_support_initialForm (w := w) (d := d) hf).mpr ⟨MvPolynomial.mem_support_iff.mpr hd, hdeg.symm⟩
  rw [h] at this
  simp at this

@[simp]
theorem initialForm_zero (w : σ → ℕ) : initialForm w (0 : MvPolynomial σ R) = 0 := by
  simp [initialForm]

theorem coe_weightedHomogeneousComponent (w : σ → ℕ) (n : ℕ) (f : MvPolynomial σ R) :
    ((weightedHomogeneousComponent w n f : MvPolynomial σ R) : MvPowerSeries σ R) =
      MvPowerSeries.weightedHomogeneousComponent w n (f : MvPowerSeries σ R) := by
  ext d
  rw [coeff_coe, coeff_weightedHomogeneousComponent,
    MvPowerSeries.coeff_weightedHomogeneousComponent, coeff_coe]

/-- Over a ring without zero divisors, the weighted order of a product is the sum of the weighted
orders. -/
theorem weightedOrd_mul [NoZeroDivisors R] (w : σ → ℕ) (f g : MvPolynomial σ R) :
    weightedOrd w (f * g) = weightedOrd w f + weightedOrd w g := by
  rw [weightedOrd, weightedOrd, weightedOrd, MvPolynomial.coe_mul]
  exact MvPowerSeries.weightedOrder_mul w _ _

/-- Over a ring without zero divisors, the initial form of a product is the product of the
initial forms. -/
theorem initialForm_mul [NoZeroDivisors R] (w : σ → ℕ) (f g : MvPolynomial σ R) :
    initialForm w (f * g) = initialForm w f * initialForm w g := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hpf : ((weightedOrd w f).toNat : ℕ∞) = weightedOrd w f :=
    ENat.natCast_toNat (fun h => hf (weightedOrd_eq_top_iff.mp h))
  have hpg : ((weightedOrd w g).toNat : ℕ∞) = weightedOrd w g :=
    ENat.natCast_toNat (fun h => hg (weightedOrd_eq_top_iff.mp h))
  have hsum : (weightedOrd w (f * g)).toNat = (weightedOrd w f).toNat + (weightedOrd w g).toNat := by
    rw [weightedOrd_mul, ← hpf, ← hpg, ← Nat.cast_add, ENat.toNat_natCast, ENat.toNat_natCast,
      ENat.toNat_natCast]
  apply coe_injective
  rw [initialForm, hsum, coe_weightedHomogeneousComponent, MvPolynomial.coe_mul,
    MvPolynomial.coe_mul, initialForm, initialForm, coe_weightedHomogeneousComponent, coe_weightedHomogeneousComponent]
  exact (MvPowerSeries.weightedHomogeneousComponent_mul_of_le_weightedOrder
    (le_of_eq hpf) (le_of_eq hpg))

/-- If `P ≠ 0` is weighted homogeneous of weight `n` and `Q` has weighted order larger than `n`,
then `P` is the initial form of `P + Q`. -/
theorem initialForm_add_of_lt {w : σ → ℕ} {P Q : MvPolynomial σ R} {n : ℕ}
    (hP : IsWeightedHomogeneous w P n) (hP0 : P ≠ 0) (hQ : (n : ℕ∞) < weightedOrd w Q) :
    initialForm w (P + Q) = P := by
  have hPo : weightedOrd w P = n := by
    refine le_antisymm ?_ ?_
    · obtain ⟨d, hd⟩ := support_nonempty.mpr hP0
      have hd' := MvPolynomial.mem_support_iff.mp hd
      exact (weightedOrd_le hd').trans_eq (by rw [hP hd'])
    · refine MvPowerSeries.le_weightedOrder w fun d hd => ?_
      rw [coeff_coe]
      by_contra h
      rw [hP h] at hd
      exact lt_irrefl _ hd
  have hord : weightedOrd w (P + Q) = n := by
    rw [weightedOrd, MvPolynomial.coe_add, MvPowerSeries.weightedOrder_add_of_weightedOrder_ne]
    · change min (weightedOrd w P) (weightedOrd w Q) = n
      rw [hPo, min_eq_left hQ.le]
    · change weightedOrd w P ≠ weightedOrd w Q
      rw [hPo]
      exact hQ.ne
  ext d
  rw [coeff_initialForm, hord, ENat.toNat_natCast, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  split_ifs with h
  · rw [coeff_eq_zero_of_lt_weightedOrd (f := Q) (by rw [h]; exact hQ), add_zero]
  · rw [hP.coeff_eq_zero d h]

end Singularity
