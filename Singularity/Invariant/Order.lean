/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.HilbertSamuel
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# The order of a polynomial at the origin

Let `R` be a commutative ring and let `f` be a polynomial in `R[x_i : i ∈ σ]`. The order of `f`
at the origin is the smallest total degree of a monomial of `f`, or `⊤` if `f = 0`. It is the
first invariant of each proof of resolution (spec 03.2, step 2): the hypersurface `f = 0` has
multiplicity `ord f` at the origin.

Mathlib has the order of a multivariate power series, `MvPowerSeries.order`, with its laws. We
define the order of a polynomial as the order of its image in the power series ring, so that each
law of Mathlib applies, and we add the laws that the theory of resolution uses.

The project already has the order `Singularity.Algebra.order I f` of an element for an ideal `I`
(the largest `n` with `f ∈ I^n`, in `Singularity/Algebra/HilbertSamuel.lean`). We prove that the
two agree when `I` is the ideal of the variables (`ord_eq_order_idealOfVars`). So `ord f ≥ n` if
and only if `f ∈ m^n`, with `m = (x_i : i ∈ σ)`.

## Main definitions

* `Singularity.ord f`: the order of a polynomial at the origin, in `ℕ∞`.
* `Singularity.idealOrd I`: the order of an ideal, the smallest order of its elements. It is the
  largest `n` with `I ⊆ m^n` (`le_idealOrd_iff`).
* `Singularity.linearChange A`: the linear change of coordinates `x_i ↦ ∑ j, A i j x_j`.

## Main results

* `ord_eq_iInf_degree`: the order is the smallest total degree of a monomial of the support.
* `le_ord_iff_mem_pow`: `n ≤ ord f` if and only if `f ∈ m^n`.
* `ord_eq_order_idealOfVars`: the bridge to `Singularity.Algebra.order`.
* `min_ord_le_ord_add`, `ord_add_of_ord_ne`, `le_ord_mul`: the laws over each ring.
* `ord_mul`, `ord_pow`, `ord_prod`: over a ring without zero divisors the order is additive.
* `idealOrd_mul`, `idealOrd_sup`, `idealOrd_span_singleton`, `idealOrd_pow`: the laws of the
  order of an ideal.
* `ord_le_ord_aeval`: a substitution `x_i ↦ φ_i` with `φ_i(0) = 0` does not lower the order.
* `ord_algEquiv`, `ord_linearChange`: a change of coordinates that fixes the origin, for example an
  invertible linear change, does not change the order.

## References

* [Hau03] H. Hauser, *The Hironaka theorem on resolution of singularities*, Bull. AMS 40 (2003),
  §5 (the order of an ideal).
-/

open MvPolynomial Finsupp

namespace Singularity

section Semiring

variable {σ R : Type*} [CommSemiring R]

/-- The order of a polynomial at the origin: the smallest total degree of a monomial with a
nonzero coefficient, or `⊤` for the zero polynomial. It is the order of the polynomial as a power
series (`MvPowerSeries.order`). -/
noncomputable def ord (f : MvPolynomial σ R) : ℕ∞ :=
  (f : MvPowerSeries σ R).order

theorem ord_def (f : MvPolynomial σ R) : ord f = (f : MvPowerSeries σ R).order := rfl

/-- The basic law of the order: `n ≤ ord f` if and only if each monomial of total degree less
than `n` has coefficient `0`. -/
theorem le_ord_iff {f : MvPolynomial σ R} {n : ℕ} :
    (n : ℕ∞) ≤ ord f ↔ ∀ d : σ →₀ ℕ, degree d < n → f.coeff d = 0 := by
  refine ⟨fun h d hd => ?_, fun h => MvPowerSeries.nat_le_order fun d hd => ?_⟩
  · rw [← coeff_coe]
    exact MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)
  · rw [coeff_coe]
    exact h d hd

/-- A monomial with a nonzero coefficient bounds the order from above. -/
theorem ord_le {f : MvPolynomial σ R} {d : σ →₀ ℕ} (h : f.coeff d ≠ 0) :
    ord f ≤ ((degree d : ℕ) : ℕ∞) :=
  MvPowerSeries.order_le (by rwa [coeff_coe])

theorem coeff_eq_zero_of_lt_ord {f : MvPolynomial σ R} {d : σ →₀ ℕ} (h : ((degree d : ℕ) : ℕ∞) < ord f) :
    f.coeff d = 0 := by
  by_contra hd
  exact absurd (ord_le hd) (not_le.mpr h)

@[simp]
theorem ord_eq_top_iff {f : MvPolynomial σ R} : ord f = ⊤ ↔ f = 0 := by
  rw [ord, MvPowerSeries.order_eq_top_iff, coe_eq_zero_iff]

@[simp]
theorem ord_zero : ord (0 : MvPolynomial σ R) = ⊤ := ord_eq_top_iff.mpr rfl

theorem ord_ne_top {f : MvPolynomial σ R} (hf : f ≠ 0) : ord f ≠ ⊤ :=
  fun h => hf (ord_eq_top_iff.mp h)

/-- A nonzero polynomial has a monomial whose total degree is the order. -/
theorem exists_coeff_ne_zero_and_ord_eq {f : MvPolynomial σ R} (hf : f ≠ 0) :
    ∃ d : σ →₀ ℕ, f.coeff d ≠ 0 ∧ ord f = ((degree d : ℕ) : ℕ∞) := by
  have hfin : (ord f).toNat = ord f := ENat.natCast_toNat (ord_ne_top hf)
  obtain ⟨d, hd, hdeg⟩ := MvPowerSeries.exists_coeff_ne_zero_and_order hfin
  rw [coeff_coe] at hd
  exact ⟨d, hd, hdeg.symm⟩

/-- The order is the smallest total degree of a monomial of the support. -/
theorem ord_eq_iInf_degree (f : MvPolynomial σ R) :
    ord f = ⨅ d ∈ f.support, ((degree d : ℕ) : ℕ∞) := by
  refine le_antisymm (le_iInf₂ fun d hd => ord_le (MvPolynomial.mem_support_iff.mp hd)) ?_
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · obtain ⟨d, hd, hdeg⟩ := exists_coeff_ne_zero_and_ord_eq hf
    rw [hdeg]
    exact iInf₂_le d (MvPolynomial.mem_support_iff.mpr hd)

/-- `n ≤ ord f` if and only if `f` lies in the `n`-th power of the ideal of the variables. -/
theorem le_ord_iff_mem_pow {f : MvPolynomial σ R} {n : ℕ} :
    (n : ℕ∞) ≤ ord f ↔ f ∈ idealOfVars σ R ^ n := by
  rw [le_ord_iff, mem_pow_idealOfVars_iff']

/-- A polynomial lies in the ideal of the variables if and only if its constant term is `0`. -/
theorem mem_idealOfVars_iff {f : MvPolynomial σ R} :
    f ∈ idealOfVars σ R ↔ constantCoeff f = 0 := by
  rw [← pow_one (idealOfVars σ R), mem_pow_idealOfVars_iff', constantCoeff_eq]
  refine ⟨fun h => h 0 (by simp), fun h d hd => ?_⟩
  have : d = 0 := by
    have hd0 : degree d = 0 := by omega
    exact (degree_eq_zero_iff d).mp hd0
  rw [this, h]

theorem one_le_ord_iff {f : MvPolynomial σ R} : 1 ≤ ord f ↔ constantCoeff f = 0 := by
  rw [← mem_idealOfVars_iff, ← pow_one (idealOfVars σ R), ← le_ord_iff_mem_pow, Nat.cast_one]

theorem ord_monomial {d : σ →₀ ℕ} {c : R} (hc : c ≠ 0) : ord (monomial d c) = ((degree d : ℕ) : ℕ∞) := by
  rw [ord, coe_monomial, MvPowerSeries.order_monomial_of_ne_zero hc]

theorem ord_C {c : R} (hc : c ≠ 0) : ord (C c : MvPolynomial σ R) = 0 := by
  rw [← monomial_zero', ord_monomial hc, map_zero, Nat.cast_zero]

@[simp]
theorem ord_one [Nontrivial R] : ord (1 : MvPolynomial σ R) = 0 := by
  rw [← C_1, ord_C one_ne_zero]

@[simp]
theorem ord_X [Nontrivial R] (i : σ) : ord (X i : MvPolynomial σ R) = 1 := by
  rw [X, ord_monomial one_ne_zero, degree_single, Nat.cast_one]

@[simp]
theorem ord_X_pow [Nontrivial R] (i : σ) (n : ℕ) : ord (X i ^ n : MvPolynomial σ R) = n := by
  rw [X_pow_eq_monomial, ord_monomial one_ne_zero, degree_single]

/-- The order of a sum is at least the smaller of the two orders. -/
theorem min_ord_le_ord_add (f g : MvPolynomial σ R) : min (ord f) (ord g) ≤ ord (f + g) := by
  rw [ord, ord, ord, MvPolynomial.coe_add]
  exact MvPowerSeries.min_order_le_add

theorem le_ord_add {f g : MvPolynomial σ R} {n : ℕ∞} (hf : n ≤ ord f) (hg : n ≤ ord g) :
    n ≤ ord (f + g) :=
  (le_min hf hg).trans (min_ord_le_ord_add f g)

/-- If two polynomials have different orders, the order of the sum is the smaller one. -/
theorem ord_add_of_ord_ne {f g : MvPolynomial σ R} (h : ord f ≠ ord g) :
    ord (f + g) = min (ord f) (ord g) := by
  rw [ord, ord, ord, MvPolynomial.coe_add]
  exact MvPowerSeries.order_add_of_order_ne h

theorem ord_add_of_lt {f g : MvPolynomial σ R} (h : ord f < ord g) : ord (f + g) = ord f := by
  rw [ord_add_of_ord_ne h.ne, min_eq_left h.le]

/-- The order of a product is at least the sum of the orders. -/
theorem le_ord_mul (f g : MvPolynomial σ R) : ord f + ord g ≤ ord (f * g) := by
  rw [ord, ord, ord, MvPolynomial.coe_mul]
  exact MvPowerSeries.le_order_mul

theorem le_ord_pow (f : MvPolynomial σ R) (n : ℕ) : n • ord f ≤ ord (f ^ n) := by
  rw [ord, ord, MvPolynomial.coe_pow]
  exact MvPowerSeries.le_order_pow n

/-- The order of a polynomial is not changed by the multiplication with a unit of `R`. -/
theorem le_ord_smul (a : R) (f : MvPolynomial σ R) : ord f ≤ ord (a • f) := by
  rw [smul_eq_C_mul]
  exact le_add_self.trans (le_ord_mul _ _)

section NoZeroDivisors

variable [NoZeroDivisors R]

/-- Over a ring without zero divisors the order of a product is the sum of the orders. -/
theorem ord_mul (f g : MvPolynomial σ R) : ord (f * g) = ord f + ord g := by
  rw [ord, ord, ord, MvPolynomial.coe_mul]
  exact MvPowerSeries.order_mul _ _

theorem ord_pow [Nontrivial R] (f : MvPolynomial σ R) (n : ℕ) : ord (f ^ n) = n • ord f := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ord_mul, ih, succ_nsmul]

theorem ord_prod [Nontrivial R] {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) :
    ord (∏ i ∈ s, f i) = ∑ i ∈ s, ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ord_mul, ih]

end NoZeroDivisors

/-! ### The order of an ideal -/

/-- The order of an ideal `I` of the polynomial ring at the origin: the smallest order of an
element of `I`. It is the largest `n` with `I ⊆ m^n` (`le_idealOrd_iff`), as in spec 03.2,
step 2. -/
noncomputable def idealOrd (I : Ideal (MvPolynomial σ R)) : ℕ∞ :=
  sInf (ord '' (I : Set (MvPolynomial σ R)))

theorem idealOrd_le_ord {I : Ideal (MvPolynomial σ R)} {f : MvPolynomial σ R} (hf : f ∈ I) :
    idealOrd I ≤ ord f :=
  sInf_le ⟨f, hf, rfl⟩

theorem le_idealOrd {I : Ideal (MvPolynomial σ R)} {n : ℕ∞} (h : ∀ f ∈ I, n ≤ ord f) :
    n ≤ idealOrd I :=
  le_sInf (by rintro _ ⟨f, hf, rfl⟩; exact h f hf)

/-- The order of an ideal is attained by an element. -/
theorem exists_mem_ord_eq_idealOrd (I : Ideal (MvPolynomial σ R)) :
    ∃ f ∈ I, ord f = idealOrd I := by
  obtain ⟨f, hf, h⟩ := csInf_mem (s := ord '' (I : Set (MvPolynomial σ R))) ⟨_, 0, I.zero_mem, rfl⟩
  exact ⟨f, hf, h⟩

/-- `n ≤ ord I` if and only if `I ⊆ m^n`. -/
theorem le_idealOrd_iff {I : Ideal (MvPolynomial σ R)} {n : ℕ} :
    (n : ℕ∞) ≤ idealOrd I ↔ I ≤ idealOfVars σ R ^ n :=
  ⟨fun h _ hf => le_ord_iff_mem_pow.mp (h.trans (idealOrd_le_ord hf)),
    fun h => le_idealOrd fun _ hf => le_ord_iff_mem_pow.mpr (h hf)⟩

/-- A larger ideal has a smaller order. -/
theorem idealOrd_anti {I J : Ideal (MvPolynomial σ R)} (h : I ≤ J) : idealOrd J ≤ idealOrd I :=
  le_idealOrd fun _ hf => idealOrd_le_ord (h hf)

@[simp]
theorem idealOrd_bot : idealOrd (⊥ : Ideal (MvPolynomial σ R)) = ⊤ :=
  top_le_iff.mp <| le_idealOrd fun f hf => by
    rw [Ideal.mem_bot.mp hf, ord_zero]

/-- The order of a principal ideal is the order of its generator. -/
theorem idealOrd_span_singleton (f : MvPolynomial σ R) :
    idealOrd (Ideal.span {f}) = ord f := by
  refine le_antisymm (idealOrd_le_ord (Ideal.mem_span_singleton_self f)) (le_idealOrd ?_)
  intro g hg
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hg
  exact le_add_self.trans (le_ord_mul a f)

/-- The order of a sum of ideals is the smaller of the two orders. -/
theorem idealOrd_sup (I J : Ideal (MvPolynomial σ R)) :
    idealOrd (I ⊔ J) = min (idealOrd I) (idealOrd J) := by
  refine le_antisymm (le_min (idealOrd_anti le_sup_left) (idealOrd_anti le_sup_right)) ?_
  refine le_idealOrd fun h hh => ?_
  obtain ⟨f, hf, g, hg, rfl⟩ := Submodule.mem_sup.mp hh
  exact (min_le_min (idealOrd_le_ord hf) (idealOrd_le_ord hg)).trans (min_ord_le_ord_add f g)

/-- The order of a product of ideals is at least the sum of the orders. -/
theorem le_idealOrd_mul (I J : Ideal (MvPolynomial σ R)) :
    idealOrd I + idealOrd J ≤ idealOrd (I * J) := by
  refine le_idealOrd fun h hh => ?_
  refine Submodule.mul_induction_on hh (fun f hf g hg => ?_) (fun a b ha hb => le_ord_add ha hb)
  exact (add_le_add (idealOrd_le_ord hf) (idealOrd_le_ord hg)).trans (le_ord_mul f g)

/-- Over a ring without zero divisors the order of a product of ideals is the sum of the
orders. -/
theorem idealOrd_mul [NoZeroDivisors R] (I J : Ideal (MvPolynomial σ R)) :
    idealOrd (I * J) = idealOrd I + idealOrd J := by
  refine le_antisymm ?_ (le_idealOrd_mul I J)
  obtain ⟨f, hf, hfo⟩ := exists_mem_ord_eq_idealOrd I
  obtain ⟨g, hg, hgo⟩ := exists_mem_ord_eq_idealOrd J
  rw [← hfo, ← hgo, ← ord_mul]
  exact idealOrd_le_ord (Ideal.mul_mem_mul hf hg)

theorem idealOrd_pow [NoZeroDivisors R] [Nontrivial R] (I : Ideal (MvPolynomial σ R)) (n : ℕ) :
    idealOrd (I ^ n) = n • idealOrd I := by
  induction n with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, zero_smul]
    exact le_antisymm ((idealOrd_le_ord (Submodule.mem_top (x := 1))).trans_eq ord_one) bot_le
  | succ n ih => rw [pow_succ, idealOrd_mul, ih, succ_nsmul]

/-- The ideal of the variables has order `1`. -/
theorem idealOrd_idealOfVars [Nontrivial R] [Nonempty σ] : idealOrd (idealOfVars σ R) = 1 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨i⟩ := ‹Nonempty σ›
    have hi : (X i : MvPolynomial σ R) ∈ idealOfVars σ R := Ideal.subset_span (Set.mem_range_self i)
    exact (idealOrd_le_ord hi).trans_eq (ord_X i)
  · exact le_idealOrd_iff.mpr (by rw [pow_one])

/-! ### Changes of coordinates -/

/-- A substitution `x_i ↦ φ_i` with `φ_i(0) = 0` for each `i` does not lower the order. -/
theorem ord_le_ord_aeval {τ : Type*} (φ : σ → MvPolynomial τ R)
    (hφ : ∀ i, constantCoeff (φ i) = 0) (f : MvPolynomial σ R) :
    ord f ≤ ord (aeval φ f) := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  let g : MvPolynomial σ R →+* MvPolynomial τ R := (aeval φ).toRingHom
  have hm : idealOfVars σ R ≤ (idealOfVars τ R).comap g := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    show g (X i) ∈ idealOfVars τ R
    rw [mem_idealOfVars_iff]
    simpa [g] using hφ i
  exact le_ord_iff_mem_pow.mpr
    (Ideal.le_comap_pow g n (Ideal.pow_right_mono hm n (le_ord_iff_mem_pow.mp hn)))

/-- An automorphism of the polynomial ring that fixes the origin, and whose inverse fixes the
origin, does not change the order. -/
theorem ord_algEquiv {τ : Type*} (e : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R)
    (he : ∀ i, constantCoeff (e (X i)) = 0) (he' : ∀ i, constantCoeff (e.symm (X i)) = 0)
    (f : MvPolynomial σ R) : ord (e f) = ord f := by
  have h1 : ∀ g, e g = aeval (fun i => e (X i)) g := fun g => by
    have := comp_aeval_apply (f := X) e.toAlgHom g
    rw [aeval_X_left_apply] at this
    exact this
  have h2 : ∀ g, e.symm g = aeval (fun i => e.symm (X i)) g := fun g => by
    have := comp_aeval_apply (f := X) e.symm.toAlgHom g
    rw [aeval_X_left_apply] at this
    exact this
  refine le_antisymm ?_ ?_
  · calc ord (e f) ≤ ord (e.symm (e f)) := by rw [h2]; exact ord_le_ord_aeval _ he' _
      _ = ord f := by rw [e.symm_apply_apply]
  · rw [h1]
    exact ord_le_ord_aeval _ he _

variable [Fintype σ]

/-- The linear change of coordinates `x_i ↦ ∑ j, A i j x_j` given by a square matrix `A`. -/
noncomputable def linearChange (A : Matrix σ σ R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i => ∑ j, C (A i j) * X j

theorem linearChange_X (A : Matrix σ σ R) (i : σ) :
    linearChange A (X i) = ∑ j, C (A i j) * X j :=
  aeval_X _ _

theorem constantCoeff_linearChange_X (A : Matrix σ σ R) (i : σ) :
    constantCoeff (linearChange A (X i)) = 0 := by
  simp [linearChange_X]

/-- A linear change of coordinates does not lower the order. -/
theorem ord_le_ord_linearChange (A : Matrix σ σ R) (f : MvPolynomial σ R) :
    ord f ≤ ord (linearChange A f) :=
  ord_le_ord_aeval _ (fun i => by simp) f

/-- The composite of two linear changes is the linear change of the product, in the reverse
order. -/
theorem linearChange_linearChange (A B : Matrix σ σ R) (f : MvPolynomial σ R) :
    linearChange A (linearChange B f) = linearChange (B * A) f := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun i => ?_
  simp only [AlgHom.comp_apply, linearChange_X, map_sum, map_mul, algHom_C, algebraMap_eq,
    Finset.mul_sum, Matrix.mul_apply, ← mul_assoc, Finset.sum_mul]
  exact Finset.sum_comm

theorem linearChange_one [DecidableEq σ] (f : MvPolynomial σ R) : linearChange 1 f = f := by
  rw [← AlgHom.id_apply (R := R) f]
  congr 1
  refine MvPolynomial.algHom_ext fun i => ?_
  simp [linearChange_X, Matrix.one_apply]

/-- An invertible linear change of coordinates does not change the order. -/
theorem ord_linearChange [DecidableEq σ] (A : Matrix σ σ R) [Invertible A]
    (f : MvPolynomial σ R) : ord (linearChange A f) = ord f := by
  refine le_antisymm ?_ (ord_le_ord_linearChange A f)
  calc ord (linearChange A f) ≤ ord (linearChange (⅟A) (linearChange A f)) :=
        ord_le_ord_linearChange _ _
    _ = ord f := by rw [linearChange_linearChange, mul_invOf_self, linearChange_one]

end Semiring

section Ring

variable {σ R : Type*} [CommRing R]

@[simp]
theorem ord_neg (f : MvPolynomial σ R) : ord (-f) = ord f := by
  have h : ((-f : MvPolynomial σ R) : MvPowerSeries σ R) = -(f : MvPowerSeries σ R) :=
    map_neg coeToMvPowerSeries.ringHom f
  rw [ord, ord, h]
  exact MvPowerSeries.order_neg _

/-- The bridge to `Singularity.Algebra.order`: the order of a polynomial at the origin is its
order for the ideal of the variables, the largest `n` with `f ∈ m^n`. -/
theorem ord_eq_order_idealOfVars (f : MvPolynomial σ R) :
    ord f = Algebra.order (idealOfVars σ R) f := by
  refine le_antisymm (ENat.forall_natCast_le_iff_le.mp fun n hn => ?_)
    (ENat.forall_natCast_le_iff_le.mp fun n hn => ?_)
  · exact Algebra.le_order_iff.mpr (le_ord_iff_mem_pow.mp hn)
  · exact le_ord_iff_mem_pow.mpr (Algebra.le_order_iff.mp hn)

end Ring

end Singularity
