/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobian
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# The order along a coordinate subvariety

Let `S` be a finite set of variables, and let `Z = V(x_i : i ∈ S)` be the coordinate subvariety
of `S`. This file gives the order along `Z` of Volume 7, Definition 3.13.2 of the handbook, and it
proves Lemma 3.13.14 for coordinate subvarieties.

* `ordAlong S f` is the order of `f` along `Z`: the smallest sum `∑ i ∈ S, d i` for a monomial
  `x^d` of `f` (`ordAlong_eq_iInf`), or `⊤` for `f = 0`. It is the largest `n` with `f ∈ I_Z^n`,
  where `I_Z = (x_i : i ∈ S)` is `varsIdeal S` (`le_ordAlong_iff_mem_pow`).
* The order along `Z` is a valuation. The order of a product is the sum of the orders
  (`ordAlong_mul`), and the order of a sum is at least the minimum (`min_le_ordAlong_add`).
* The derivations `∂_j` and `x_j ∂_j` lower the order along `Z` by at most `1`
  (`ordAlong_le_ordAlong_pderiv_add_one`, `ordAlong_le_ordAlong_X_mul_pderiv_add_one`).
* `cleanOrdAlong p S g` is the clean order `ν̄_Z(g)`, the supremum of the order along `Z` of
  `g + h^p`. Here `h` is a polynomial, and not a series as in the handbook.
* `orderGAlong p Δ S g` is the order `ν^G_Z = ν̄_Z(g) - ∑ r_i` of `G` along `Z`, where the sum is
  over `i ∈ Δ ∩ S`, the components of the divisor that contain `Z`.
* **Lemma 3.13.14** (`orderGAlong_le_idealOrdAlong_add_one`): `ν^G_Z ≤ ord_Z(J) + 1`, with `J` the
  residual log-Jacobian ideal. So if `ν^G_Z ≥ n + 1`, then `J ⊆ I_Z^n`
  (`residualLogJacobian_le_pow_varsIdeal`).

## References

* Volume 7, Section 3.13 of the handbook: Definition 3.13.2 and Lemma 3.13.14.
-/

open MvPolynomial Finsupp

namespace Singularity

section Semiring

variable {σ R : Type*} [CommSemiring R] [DecidableEq σ]

/-- The weight of the order along `V(x_i : i ∈ S)`: `1` for `i ∈ S`, and `0` for the other
variables. -/
def alongWeight (S : Finset σ) : σ → ℕ := fun i => if i ∈ S then 1 else 0

theorem weight_alongWeight (S : Finset σ) (d : σ →₀ ℕ) :
    weight (alongWeight S) d = ∑ i ∈ S, d i := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  simp only [alongWeight, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  exact Finset.sum_subset (fun i hi => (Finset.mem_filter.mp hi).2)
    (fun i hiS hi => by simpa [hiS] using hi)

/-- The order of `f` along the coordinate subvariety `Z = V(x_i : i ∈ S)`: the smallest sum
`∑ i ∈ S, d i` for a monomial `x^d` of `f`, or `⊤` for `f = 0` (Volume 7, Definition 3.13.2 of
the handbook). -/
noncomputable def ordAlong (S : Finset σ) (f : MvPolynomial σ R) : ℕ∞ :=
  (f : MvPowerSeries σ R).weightedOrder (alongWeight S)

/-- A monomial of `f` bounds the order along `Z` from above. -/
theorem ordAlong_le {S : Finset σ} {f : MvPolynomial σ R} {d : σ →₀ ℕ} (h : f.coeff d ≠ 0) :
    ordAlong S f ≤ ((∑ i ∈ S, d i : ℕ) : ℕ∞) := by
  rw [← weight_alongWeight]
  exact MvPowerSeries.weightedOrder_le (w := alongWeight S) (by rwa [MvPolynomial.coeff_coe])

/-- If each monomial of `f` has the degree at least `n` in the variables of `S`, then the order
of `f` along `Z` is at least `n`. -/
theorem le_ordAlong {S : Finset σ} {f : MvPolynomial σ R} {n : ℕ∞}
    (h : ∀ d ∈ f.support, n ≤ ((∑ i ∈ S, d i : ℕ) : ℕ∞)) : n ≤ ordAlong S f := by
  refine MvPowerSeries.le_weightedOrder (w := alongWeight S) fun d hd => ?_
  rw [MvPolynomial.coeff_coe]
  by_contra hc
  rw [weight_alongWeight] at hd
  exact absurd (h d (MvPolynomial.mem_support_iff.mpr hc)) (not_le.mpr hd)

theorem le_ordAlong_iff {S : Finset σ} {f : MvPolynomial σ R} {n : ℕ∞} :
    n ≤ ordAlong S f ↔ ∀ d ∈ f.support, n ≤ ((∑ i ∈ S, d i : ℕ) : ℕ∞) :=
  ⟨fun h _ hd => h.trans (ordAlong_le (MvPolynomial.mem_support_iff.mp hd)), le_ordAlong⟩

/-- The order along `Z` is the smallest degree in the variables of `S` of a monomial of `f`. -/
theorem ordAlong_eq_iInf (S : Finset σ) (f : MvPolynomial σ R) :
    ordAlong S f = ⨅ d ∈ f.support, ((∑ i ∈ S, d i : ℕ) : ℕ∞) :=
  le_antisymm (le_iInf₂ fun _ hd => ordAlong_le (MvPolynomial.mem_support_iff.mp hd))
    (le_ordAlong fun d hd => iInf₂_le d hd)

@[simp]
theorem ordAlong_zero (S : Finset σ) : ordAlong S (0 : MvPolynomial σ R) = ⊤ := by
  rw [ordAlong, MvPolynomial.coe_zero, MvPowerSeries.weightedOrder_zero]

theorem ordAlong_monomial (S : Finset σ) {d : σ →₀ ℕ} {c : R} (hc : c ≠ 0) :
    ordAlong S (monomial d c) = ((∑ i ∈ S, d i : ℕ) : ℕ∞) := by
  rw [ordAlong, MvPolynomial.coe_monomial,
    MvPowerSeries.weightedOrder_monomial_of_ne_zero (w := alongWeight S) hc, weight_alongWeight]

theorem ordAlong_X_pow [Nontrivial R] (S : Finset σ) (i : σ) (n : ℕ) :
    ordAlong S (X i ^ n : MvPolynomial σ R) = ((if i ∈ S then n else 0 : ℕ) : ℕ∞) := by
  rw [X_pow_eq_monomial, ordAlong_monomial S one_ne_zero]
  congr 1
  simp [Finsupp.single_apply]

theorem ordAlong_X [Nontrivial R] (S : Finset σ) (i : σ) :
    ordAlong S (X i : MvPolynomial σ R) = ((if i ∈ S then 1 else 0 : ℕ) : ℕ∞) := by
  rw [← ordAlong_X_pow (R := R) S i 1, pow_one]

/-- If `f` and `g` have the order at least `n` along `Z`, then so does `f + g`. -/
theorem le_ordAlong_add {S : Finset σ} {f g : MvPolynomial σ R} {n : ℕ∞}
    (hf : n ≤ ordAlong S f) (hg : n ≤ ordAlong S g) : n ≤ ordAlong S (f + g) := by
  refine le_ordAlong fun d hd => ?_
  rw [MvPolynomial.mem_support_iff, coeff_add_apply] at hd
  by_cases h : f.coeff d = 0
  · rw [h, zero_add] at hd
    exact hg.trans (ordAlong_le hd)
  · exact hf.trans (ordAlong_le h)

/-- The order along `Z` of a sum is at least the minimum of the orders. -/
theorem min_le_ordAlong_add (S : Finset σ) (f g : MvPolynomial σ R) :
    min (ordAlong S f) (ordAlong S g) ≤ ordAlong S (f + g) :=
  le_ordAlong_add (min_le_left _ _) (min_le_right _ _)

/-- The order along `Z` of a product is at least the sum of the orders. -/
theorem le_ordAlong_mul (S : Finset σ) (f g : MvPolynomial σ R) :
    ordAlong S f + ordAlong S g ≤ ordAlong S (f * g) := by
  rw [ordAlong, ordAlong, ordAlong, MvPolynomial.coe_mul]
  apply MvPowerSeries.le_weightedOrder_mul

theorem ordAlong_le_ordAlong_mul_left (S : Finset σ) (a f : MvPolynomial σ R) :
    ordAlong S f ≤ ordAlong S (a * f) :=
  le_add_self.trans (le_ordAlong_mul S a f)

/-- Over a ring without zero divisors, the order along `Z` of a product is the sum of the
orders. -/
theorem ordAlong_mul [NoZeroDivisors R] (S : Finset σ) (f g : MvPolynomial σ R) :
    ordAlong S (f * g) = ordAlong S f + ordAlong S g := by
  rw [ordAlong, ordAlong, ordAlong, MvPolynomial.coe_mul]
  exact MvPowerSeries.weightedOrder_mul _ _ _

/-- The derivative `∂_j` lowers the order along `Z` by at most `1`. -/
theorem ordAlong_le_ordAlong_pderiv_add_one (S : Finset σ) (j : σ) (F : MvPolynomial σ R) :
    ordAlong S F ≤ ordAlong S (pderiv j F) + 1 := by
  refine tsub_le_iff_right.mp (le_ordAlong fun d hd => ?_)
  rw [MvPolynomial.mem_support_iff, coeff_pderiv] at hd
  have h := ordAlong_le (S := S) (left_ne_zero_of_mul hd)
  refine tsub_le_iff_right.mpr (h.trans ?_)
  have hs : ∑ i ∈ S, (d + single j 1 : σ →₀ ℕ) i ≤ (∑ i ∈ S, d i) + 1 := by
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply,
      Finset.sum_ite_eq]
    split_ifs <;> omega
  exact_mod_cast hs

/-- The logarithmic derivative `x_j ∂_j` lowers the order along `Z` by at most `1`. -/
theorem ordAlong_le_ordAlong_X_mul_pderiv_add_one (S : Finset σ) (j : σ)
    (F : MvPolynomial σ R) : ordAlong S F ≤ ordAlong S (X j * pderiv j F) + 1 :=
  (ordAlong_le_ordAlong_pderiv_add_one S j F).trans
    (add_le_add (ordAlong_le_ordAlong_mul_left S _ _) le_rfl)

/-! ### The ideal of `Z` and its powers -/

/-- The ideal `I_Z = (x_i : i ∈ S)` of the coordinate subvariety `Z`. -/
noncomputable def varsIdeal (S : Finset σ) : Ideal (MvPolynomial σ R) :=
  Ideal.span (X '' (S : Set σ))

/-- The ideal of the polynomials with the order at least `n` along `Z`. -/
noncomputable def alongIdeal (S : Finset σ) (n : ℕ∞) : Ideal (MvPolynomial σ R) where
  carrier := {f | n ≤ ordAlong S f}
  add_mem' hf hg := le_ordAlong_add hf hg
  zero_mem' := by
    show n ≤ ordAlong S 0
    rw [ordAlong_zero]
    exact le_top
  smul_mem' a f hf := hf.trans (ordAlong_le_ordAlong_mul_left S a f)

theorem mem_alongIdeal {S : Finset σ} {n : ℕ∞} {f : MvPolynomial σ R} :
    f ∈ alongIdeal S n ↔ n ≤ ordAlong S f := Iff.rfl

theorem pow_varsIdeal_le_alongIdeal [Nontrivial R] (S : Finset σ) (n : ℕ) :
    varsIdeal S ^ n ≤ alongIdeal (R := R) S (n : ℕ∞) := by
  induction n with
  | zero =>
    intro f _
    rw [mem_alongIdeal, Nat.cast_zero]
    exact zero_le
  | succ n ih =>
    rw [pow_succ', Ideal.mul_le]
    intro a ha b hb
    have h1 : varsIdeal S ≤ alongIdeal (R := R) S 1 := by
      rw [varsIdeal, Ideal.span_le]
      rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, mem_alongIdeal, ordAlong_X, ite_eq_left (Finset.mem_coe.mp hi),
        Nat.cast_one]
    rw [mem_alongIdeal]
    calc ((n + 1 : ℕ) : ℕ∞) = 1 + n := by push_cast; ring
      _ ≤ ordAlong S a + ordAlong S b :=
        add_le_add (mem_alongIdeal.mp (h1 ha)) (mem_alongIdeal.mp (ih hb))
      _ ≤ _ := le_ordAlong_mul S a b

theorem monomial_mem_pow_varsIdeal (S : Finset σ) (n : ℕ) :
    ∀ (d : σ →₀ ℕ) (c : R), n ≤ ∑ i ∈ S, d i → monomial d c ∈ varsIdeal S ^ n := by
  induction n with
  | zero =>
    intro d c _
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    intro d c hd
    obtain ⟨i, hiS, hi⟩ : ∃ i ∈ S, d i ≠ 0 := Finset.exists_ne_zero_of_sum_ne_zero (by omega)
    have hle : single i 1 ≤ d := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + single i 1 :=
      ⟨d - single i 1, (tsub_add_cancel_of_le hle).symm⟩
    have hd' : n ≤ ∑ j ∈ S, d' j := by
      simp only [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply,
        Finset.sum_ite_eq, hiS, ↓reduceIte] at hd
      omega
    rw [monomial_add_single, pow_one, pow_succ',
      show monomial d' c * X i = X i * monomial d' c from mul_comm _ _]
    exact Ideal.mul_mem_mul (Ideal.subset_span ⟨i, hiS, rfl⟩) (ih d' c hd')

/-- **The order along `Z` and the powers of `I_Z`.** The order of `f` along `Z` is at least `n`
if and only if `f ∈ I_Z^n`. So the order along `Z` is the largest `n` with `f ∈ I_Z^n`. -/
theorem le_ordAlong_iff_mem_pow [Nontrivial R] {S : Finset σ} {f : MvPolynomial σ R} {n : ℕ} :
    (n : ℕ∞) ≤ ordAlong S f ↔ f ∈ varsIdeal S ^ n := by
  refine ⟨fun h => ?_, fun h => mem_alongIdeal.mp (pow_varsIdeal_le_alongIdeal S n h)⟩
  rw [f.as_sum]
  refine Ideal.sum_mem _ fun d hd => monomial_mem_pow_varsIdeal S n d _ ?_
  have := h.trans (ordAlong_le (MvPolynomial.mem_support_iff.mp hd))
  exact_mod_cast this

/-! ### The order of an ideal along `Z` -/

/-- The order of an ideal along `Z`: the smallest order along `Z` of an element of the ideal. -/
noncomputable def idealOrdAlong (S : Finset σ) (I : Ideal (MvPolynomial σ R)) : ℕ∞ :=
  sInf (ordAlong S '' (I : Set (MvPolynomial σ R)))

theorem idealOrdAlong_le_ordAlong {S : Finset σ} {I : Ideal (MvPolynomial σ R)}
    {f : MvPolynomial σ R} (hf : f ∈ I) : idealOrdAlong S I ≤ ordAlong S f :=
  sInf_le ⟨f, hf, rfl⟩

/-- If each generator of an ideal has the order at least `n` along `Z`, then so does the
ideal. -/
theorem le_idealOrdAlong_span {S : Finset σ} {T : Set (MvPolynomial σ R)} {n : ℕ∞}
    (h : ∀ s ∈ T, n ≤ ordAlong S s) : n ≤ idealOrdAlong S (Ideal.span T) := by
  refine le_sInf ?_
  rintro _ ⟨f, hf, rfl⟩
  replace hf : f ∈ Ideal.span T := hf
  induction hf using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    rw [ordAlong_zero]
    exact le_top
  | add x y _ _ hx hy => exact le_ordAlong_add hx hy
  | smul a x _ hx => exact hx.trans (ordAlong_le_ordAlong_mul_left S a x)

end Semiring

/-! ### The clean order and the order of `G` along `Z` -/

section Field

variable {σ k : Type*} [Field k] [DecidableEq σ] (p : ℕ)

/-- The clean order `ν̄_Z(g)` of `g` along `Z = V(x_i : i ∈ S)`: the supremum of the order along
`Z` of `g + h^p` (Volume 7, Definition 3.13.2 of the handbook). In this file `h` is a polynomial.
-/
noncomputable def cleanOrdAlong (S : Finset σ) (g : MvPolynomial σ k) : ℕ∞ :=
  ⨆ h : MvPolynomial σ k, ordAlong S (g + h ^ p)

/-- The order `ν^G_Z = ν̄_Z(g) - ∑ r_i` of `G` along `Z = V(x_i : i ∈ S)`, where `g = x^r G` and
the sum is over `i ∈ Δ ∩ S` (Volume 7, Definition 3.13.2 of the handbook). -/
noncomputable def orderGAlong (Δ S : Finset σ) (g : MvPolynomial σ k) : ℕ∞ :=
  cleanOrdAlong p S g - ((∑ i ∈ Δ ∩ S, divisorExponent Δ g i : ℕ) : ℕ∞)

theorem ordAlong_add_pow_le_cleanOrdAlong (S : Finset σ) (g h : MvPolynomial σ k) :
    ordAlong S (g + h ^ p) ≤ cleanOrdAlong p S g :=
  le_iSup (fun h => ordAlong S (g + h ^ p)) h

theorem ordAlong_le_cleanOrdAlong {p : ℕ} (hp : p ≠ 0) (S : Finset σ) (g : MvPolynomial σ k) :
    ordAlong S g ≤ cleanOrdAlong p S g := by
  simpa [zero_pow hp] using ordAlong_add_pow_le_cleanOrdAlong p S g 0

variable [CharP k p]

omit [DecidableEq σ] in
theorem pderiv_add_pow (j : σ) (g h : MvPolynomial σ k) :
    pderiv j (g + h ^ p) = pderiv j g := by
  simp only [map_add, pderiv_pow, CharP.cast_eq_zero (MvPolynomial σ k) p, zero_mul, add_zero]

/-- The main step of Lemma 3.13.14. Let `g = x^r G` with `r` supported in `Δ`, and let `e` be a
generator of the residual log-Jacobian ideal. Then the order of `g + h^p` along `Z` is at most
`∑_{i ∈ S} r_i + ord_Z(e) + 1`. -/
theorem ordAlong_monomial_mul_add_pow_le (S : Finset σ) {Δ : Finset σ} {r : σ →₀ ℕ}
    (hr : ∀ i, i ∉ Δ → r i = 0) (G h : MvPolynomial σ k) {e : MvPolynomial σ k}
    (he : e ∈ (fun i => (r i : k) • G + X i * pderiv i G) '' (Δ : Set σ) ∪
      (fun j => pderiv j G) '' (Δ : Set σ)ᶜ) :
    ordAlong S (monomial r 1 * G + h ^ p) ≤ ((∑ i ∈ S, r i : ℕ) : ℕ∞) + ordAlong S e + 1 := by
  have hmon : ∀ e : MvPolynomial σ k,
      ordAlong S (monomial r 1 * e) = ((∑ i ∈ S, r i : ℕ) : ℕ∞) + ordAlong S e := by
    intro e
    rw [ordAlong_mul, ordAlong_monomial S one_ne_zero]
  rcases he with ⟨i, -, rfl⟩ | ⟨j, hj, rfl⟩
  · have h1 : X i * pderiv i (monomial r (1 : k)) = (r i : k) • monomial r 1 := by
      rw [X_mul_pderiv_monomial, Nat.cast_smul_eq_nsmul]
    have he : X i * pderiv i (monomial r 1 * G + h ^ p) =
        monomial r 1 * ((r i : k) • G + X i * pderiv i G) := by
      rw [pderiv_add_pow]
      calc X i * pderiv i (monomial r 1 * G)
          = X i * pderiv i (monomial r 1) * G + monomial r 1 * (X i * pderiv i G) := by
            rw [pderiv_mul]
            ring
        _ = monomial r 1 * ((r i : k) • G + X i * pderiv i G) := by
            rw [h1, smul_mul_assoc, ← mul_smul_comm, ← mul_add]
    rw [← hmon, ← he]
    exact ordAlong_le_ordAlong_X_mul_pderiv_add_one S i _
  · have he : pderiv j (monomial r 1 * G + h ^ p) = monomial r 1 * pderiv j G := by
      rw [pderiv_add_pow, pderiv_mul, pderiv_monomial, hr j hj, Nat.cast_zero, mul_zero,
        monomial_zero, zero_mul, zero_add]
    rw [← hmon, ← he]
    exact ordAlong_le_ordAlong_pderiv_add_one S j _

/-- **Lemma 3.13.14 for a coordinate subvariety** (Volume 7, Section 3.13 of the handbook). Let
`Z = V(x_i : i ∈ S)`. Then `ν^G_Z ≤ ord_Z(J) + 1`, where `J` is the residual log-Jacobian ideal
of `g`. The reason is that a derivation or a logarithmic derivation lowers the order along `Z` by
at most `1`, it kills `h^p`, and `x^r J` is the ideal of these derivatives of `g`. -/
theorem orderGAlong_le_idealOrdAlong_add_one (Δ S : Finset σ) (g : MvPolynomial σ k) :
    orderGAlong p Δ S g ≤
      idealOrdAlong S (residualLogJacobian Δ (divisorExponent Δ g) (residualFactor Δ g)) + 1 := by
  have hrΔ : ∀ i, i ∉ Δ → divisorExponent Δ g i = 0 := fun i hi => divisorExponent_eq_zero hi
  have hs : ∑ i ∈ Δ ∩ S, divisorExponent Δ g i = ∑ i ∈ S, divisorExponent Δ g i :=
    Finset.sum_subset Finset.inter_subset_right fun i hiS hi =>
      hrΔ i fun hiΔ => hi (Finset.mem_inter.mpr ⟨hiΔ, hiS⟩)
  rw [orderGAlong, hs]
  refine tsub_le_iff_right.mp (le_idealOrdAlong_span fun e he => ?_)
  rw [tsub_le_iff_right, tsub_le_iff_right]
  refine iSup_le fun h => ?_
  conv_lhs => rw [← monomial_mul_residualFactor Δ g]
  exact (ordAlong_monomial_mul_add_pow_le p S hrΔ _ h he).trans (le_of_eq (by ring))

/-- **Lemma 3.13.14, the consequence.** If `ν^G_Z ≥ n + 1`, then `J ⊆ I_Z^n`. -/
theorem residualLogJacobian_le_pow_varsIdeal {Δ S : Finset σ} {g : MvPolynomial σ k} {n : ℕ}
    (h : (n : ℕ∞) + 1 ≤ orderGAlong p Δ S g) :
    residualLogJacobian Δ (divisorExponent Δ g) (residualFactor Δ g) ≤ varsIdeal S ^ n := by
  intro f hf
  refine le_ordAlong_iff_mem_pow.mp ?_
  have h2 := (h.trans (orderGAlong_le_idealOrdAlong_add_one p Δ S g)).trans
    (add_le_add (idealOrdAlong_le_ordAlong hf) le_rfl)
  generalize ordAlong S f = x at h2 ⊢
  induction x using ENat.recTopCoe with
  | top => exact le_top
  | coe m =>
    have : n + 1 ≤ m + 1 := by exact_mod_cast h2
    exact_mod_cast (by omega : n ≤ m)

end Field

end Singularity
