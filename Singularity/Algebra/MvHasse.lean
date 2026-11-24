/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.Order
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Nat.Choose.Lucas

/-!
# Hasse-Schmidt derivatives in several variables

Let `R` be a commutative ring and let `f` be a polynomial in `R[x_i : i ∈ σ]`. Substitute
`x_i + y_i` for `x_i`, with new variables `y_i`. The result is a polynomial in the `y_i` with
coefficients in `R[x]`, and the Hasse-Schmidt derivative `D^α f` is the coefficient of `y^α`:

  `f(x + y) = ∑_α (D^α f)(x) y^α`.

On a monomial the binomial theorem gives

  `D^α (x^β) = binom(β, α) x^(β - α)`, with `binom(β, α) = ∏_i binom(β_i, α_i)`.

The coefficient is `0` unless `α ≤ β` in each coordinate. Over the rational numbers,
`D^α = ∂^α / α!`, with `α! = ∏_i α_i!`. Over a ring of characteristic `p` the factorials can be
`0`, and the operators `D^α` are the right replacement for the higher derivatives. For example, let
`p` be a prime and let `R` have characteristic `p`. Each derivation of `R[x, y]` kills `x^p y^p`,
because `∂_x (x^p y^p) = p x^(p-1) y^p = 0`. But `D^(p, 0) (x^p y^p) = binom(p, p) y^p = y^p`.
So the operators `D^α` see the `p`-th powers, and the first derivatives do not.

This file follows the text of Volume 1, Section 6.3 of the handbook: the operators `∂^(β)` that
come after Proposition 6.3.2 are the operators `hasseDeriv β` of this file. It also proves the
criterion for the order of Proposition 1.1.4 of Volume 7 of the handbook.

The definition by the substitution `x ↦ x + y` makes the Leibniz rule free: the substitution is a
homomorphism of rings, and the coefficient of `y^α` in a product is a sum over the antidiagonal of
`α` (`hasseDeriv_mul`). The formula on monomials is proved by induction on the exponent, with the
rule of Pascal in each coordinate (`choose_add_single_one`).

## Main definitions

* `Singularity.Algebra.MvHasse.choose β α`: the binomial coefficient `∏_i binom(β_i, α_i)` of two
  multi-indices.
* `Singularity.Algebra.MvHasse.taylor`: the substitution `x_i ↦ x_i + y_i` from `R[x]` to
  `R[x][y]`.
* `Singularity.Algebra.MvHasse.hasseDeriv α`: the Hasse-Schmidt derivative `D^α`, the coefficient
  of `y^α` in `f(x + y)`. It is `R`-linear.

## Main results

* `hasseDeriv_monomial`: `D^α (r x^β) = binom(β, α) r x^(β - α)`.
* `hasseDeriv_zero`, `hasseDeriv_C`, `hasseDeriv_X`: the first values.
* `uniqueAlgEquiv_hasseDeriv`: in one variable, `D^α` is `Polynomial.hasseDeriv` (Proposition 6.3.2
  of Volume 1 of the handbook).
* `hasseDeriv_single_one`: `D^(e_i)` is the partial derivative `∂_i`.
* `hasseDeriv_mul`: the Leibniz rule `D^α (f g) = ∑_(β + γ = α) D^β f D^γ g`.
* `hasseDeriv_comp`: the composition rule `D^α (D^β f) = binom(α + β, α) D^(α + β) f`.
* `coeff_taylor`, `taylor_eq_sum`: the Taylor formula `f(x + y) = ∑_α (D^α f)(x) y^α`.
* `coeff_aeval_X_add_C`, `aeval_X_add_C_eq_sum`: the Taylor formula at a point `a`,
  `f(a + y) = ∑_α (D^α f)(a) y^α`.
* `constantCoeff_hasseDeriv`: `(D^α f)(0)` is the coefficient of `x^α` in `f`.
* `le_ord_iff_hasseDeriv`: `ord f ≥ d` if and only if `(D^α f)(0) = 0` for each `α` with
  `|α| < d`.
* `le_ord_aeval_X_add_C_iff`: the same criterion at a point `a` (Proposition 1.1.4 of Volume 7 of
  the handbook).
* `exists_expand_eq_iff_hasseDeriv`: the test for `q`-th powers. Let `R` have characteristic `p`
  and let `q = p^e`. Then `f` is a polynomial in `x_i^q` if and only if `D^α f = 0` for each
  `α ≠ 0` with `α_i < q` for each `i`.
* `hasseDeriv_expand_mul`: for `α_i < q`, `D^α (g(x^q) f) = g(x^q) D^α f`. So these operators are
  linear over `R[x_i^q]` (the first claim of Theorem 6.3.6 of Volume 1 of the handbook, and
  Lemma 6.3.5 for these operators).

## References

* [HSDer] H. Hasse and F. K. Schmidt, *Noch eine Begründung der Theorie der höheren
  Differentialquotienten in einem algebraischen Funktionenkörper einer Unbestimmten*, J. Reine
  Angew. Math. 177 (1937).
* Volume 1, Section 6.3 and Volume 7, Section 1.1 of the handbook.
-/

open MvPolynomial Finsupp

namespace Singularity.Algebra.MvHasse

/-! ### Binomial coefficients of multi-indices -/

section Choose

variable {σ : Type*}

/-- The binomial coefficient of two multi-indices, `binom(β, α) = ∏_i binom(β_i, α_i)`. The
product runs over the support of `α`, because `binom(b, 0) = 1`. It is `0` unless `α ≤ β`. -/
def choose (β α : σ →₀ ℕ) : ℕ :=
  ∏ i ∈ α.support, (β i).choose (α i)

/-- The product that defines `choose β α` can run over each finite set that contains the support
of `α`. -/
theorem choose_eq_prod_of_subset (β α : σ →₀ ℕ) {s : Finset σ} (hs : α.support ⊆ s) :
    choose β α = ∏ i ∈ s, (β i).choose (α i) := by
  refine Finset.prod_subset hs fun i _ hi => ?_
  rw [Finsupp.notMem_support_iff.mp hi, Nat.choose_zero_right]

@[simp]
theorem choose_zero_right (β : σ →₀ ℕ) : choose β 0 = 1 := by
  simp [choose]

@[simp]
theorem choose_self (β : σ →₀ ℕ) : choose β β = 1 :=
  Finset.prod_eq_one fun _ _ => Nat.choose_self _

theorem choose_ne_zero_iff {β α : σ →₀ ℕ} : choose β α ≠ 0 ↔ α ≤ β := by
  rw [choose, Finset.prod_ne_zero_iff, Finsupp.le_iff]
  exact forall₂_congr fun _ _ => Nat.choose_ne_zero_iff

theorem choose_eq_zero_iff {β α : σ →₀ ℕ} : choose β α = 0 ↔ ¬ α ≤ β := by
  rw [← choose_ne_zero_iff, not_not]

theorem choose_single (β : σ →₀ ℕ) (i : σ) (n : ℕ) :
    choose β (single i n) = (β i).choose n := by
  classical
  rw [choose_eq_prod_of_subset β _ (Finsupp.support_single_subset), Finset.prod_singleton,
    single_eq_same]

/-- The rule of Pascal for multi-indices: `binom(β + e_i, α) = binom(β, α) + binom(β, α - e_i)`,
where the second term is present only if `α_i ≠ 0`. -/
theorem choose_add_single_one (β α : σ →₀ ℕ) (i : σ) :
    choose (β + single i 1) α = choose β α + if α i = 0 then 0 else choose β (α - single i 1) := by
  classical
  by_cases hi : α i = 0
  · rw [ite_eq_left hi, add_zero]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hji : j ≠ i := fun h => Finsupp.mem_support_iff.mp hj (h ▸ hi)
    rw [Finsupp.add_apply, single_eq_of_ne hji, add_zero]
  · rw [ite_eq_right hi, choose_eq_prod_of_subset β (α - single i 1) Finsupp.support_tsub]
    have hmem : i ∈ α.support := Finsupp.mem_support_iff.mpr hi
    simp only [choose]
    rw [← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hmem,
      ← Finset.mul_prod_erase _ _ hmem]
    have h1 : ∏ j ∈ α.support.erase i, ((β + single i 1 : σ →₀ ℕ) j).choose (α j) =
        ∏ j ∈ α.support.erase i, (β j).choose (α j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Finsupp.add_apply, single_eq_of_ne (Finset.ne_of_mem_erase hj), add_zero]
    have h2 : ∏ j ∈ α.support.erase i, (β j).choose ((α - single i 1 : σ →₀ ℕ) j) =
        ∏ j ∈ α.support.erase i, (β j).choose (α j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Finsupp.tsub_apply, single_eq_of_ne (Finset.ne_of_mem_erase hj), Nat.sub_zero]
    rw [h1, h2, Finsupp.add_apply, Finsupp.tsub_apply, single_eq_same, ← add_mul]
    obtain ⟨k, hk⟩ : ∃ k, α i = k + 1 := Nat.exists_eq_add_one_of_ne_zero hi
    rw [hk, Nat.choose_succ_succ', Nat.add_sub_cancel]
    ring

/-- The identity behind the composition rule:
`binom(β - γ, α) binom(β, γ) = binom(α + γ, α) binom(β, α + γ)`. -/
theorem choose_tsub_mul_choose (β α γ : σ →₀ ℕ) :
    choose (β - γ) α * choose β γ = choose (α + γ) α * choose β (α + γ) := by
  classical
  have hα : α.support ⊆ α.support ∪ γ.support := Finset.subset_union_left
  have hγ : γ.support ⊆ α.support ∪ γ.support := Finset.subset_union_right
  rw [choose_eq_prod_of_subset _ _ hα, choose_eq_prod_of_subset _ _ hγ,
    choose_eq_prod_of_subset _ _ hα, choose_eq_prod_of_subset _ _ Finsupp.support_add,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Finsupp.tsub_apply, Finsupp.add_apply]
  rcases le_or_gt (α i + γ i) (β i) with h | h
  · have key := Nat.choose_mul (n := β i) (k := α i + γ i) (s := γ i) le_add_self
    rw [Nat.add_sub_cancel] at key
    rw [Nat.choose_symm_add]
    linarith [key]
  · rw [Nat.choose_eq_zero_of_lt h, mul_zero]
    rcases le_or_gt (γ i) (β i) with h' | h'
    · rw [Nat.choose_eq_zero_of_lt (show β i - γ i < α i by omega), zero_mul]
    · rw [Nat.choose_eq_zero_of_lt h', mul_zero]

end Choose

/-! ### The definition -/

section Semiring

variable {σ R : Type*} [CommSemiring R]

variable (σ R) in
/-- The Taylor substitution `x_i ↦ x_i + y_i`, from `R[x]` to `R[x][y]`. The outer variables are
the `y_i`, and the coefficients are polynomials in the `x_i`. -/
noncomputable def taylor : MvPolynomial σ R →ₐ[R] MvPolynomial σ (MvPolynomial σ R) :=
  aeval fun i => C (X i) + X i

/-- The Hasse-Schmidt derivative `D^α`: the coefficient of `y^α` in `f(x + y)`. On a monomial,
`D^α (x^β) = binom(β, α) x^(β - α)` (`hasseDeriv_monomial`). This is the operator `∂^(α)` of
Volume 1, Section 6.3 of the handbook. -/
noncomputable def hasseDeriv (α : σ →₀ ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R where
  toFun f := (taylor σ R f).coeff α
  map_add' f g := by rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  map_smul' c f := by rw [map_smul, coeff_smul, RingHom.id_apply]

theorem hasseDeriv_apply (α : σ →₀ ℕ) (f : MvPolynomial σ R) :
    hasseDeriv α f = (taylor σ R f).coeff α := rfl

/-- The Taylor formula in the form of coefficients: the coefficient of `y^α` in `f(x + y)` is
`D^α f`. -/
theorem coeff_taylor (α : σ →₀ ℕ) (f : MvPolynomial σ R) :
    (taylor σ R f).coeff α = hasseDeriv α f := rfl

@[simp]
theorem taylor_X (i : σ) : taylor σ R (X i) = C (X i) + X i :=
  aeval_X _ _

@[simp]
theorem taylor_C (r : R) : taylor σ R (C r) = C (C r) :=
  aeval_C _ _

/-- Two linear maps on `R[x]` agree if they agree on the monomials. -/
theorem linearMap_ext_monomial {M : Type*} [AddCommMonoid M] [Module R M]
    {φ ψ : MvPolynomial σ R →ₗ[R] M} (h : ∀ β r, φ (monomial β r) = ψ (monomial β r)) :
    φ = ψ := by
  refine LinearMap.ext fun f => ?_
  refine MvPolynomial.induction_on' f h fun p q hp hq => ?_
  rw [map_add, map_add, hp, hq]

/-- An induction principle on the multi-indices: add `e_i` at each step. -/
theorem induction_add_single_one {P : (σ →₀ ℕ) → Prop} (h0 : P 0)
    (h : ∀ β i, P β → P (β + single i 1)) (β : σ →₀ ℕ) : P β := by
  induction β using Finsupp.induction with
  | zero => exact h0
  | single_add a b f ha hb ih =>
    clear ha hb
    induction b with
    | zero => rwa [single_zero, zero_add]
    | succ n ihn =>
      have := h _ a ihn
      rwa [add_right_comm, ← single_add] at this

/-- The coefficients of `(x + y)^β`: the coefficient of `y^α` is `binom(β, α) x^(β - α)`. -/
theorem coeff_taylor_monomial_one (β α : σ →₀ ℕ) :
    (taylor σ R (monomial β 1)).coeff α = monomial (β - α) ((choose β α : ℕ) : R) := by
  classical
  induction β using induction_add_single_one generalizing α with
  | h0 =>
    rw [monomial_zero', map_one, map_one, coeff_one]
    by_cases h : α = 0
    · subst h
      rw [ite_eq_left rfl, tsub_zero, choose_zero_right, Nat.cast_one, monomial_zero', C_1]
    · rw [ite_eq_right (Ne.symm h),
        choose_eq_zero_iff.mpr (fun h' => h (nonpos_iff_eq_zero.mp h')), Nat.cast_zero,
        monomial_zero]
  | h β i ih =>
    rw [monomial_add_single, pow_one, map_mul, taylor_X, mul_add, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, mul_comm _ (C (X i)), coeff_C_mul, coeff_mul_X', ih, ih,
      choose_add_single_one, X]
    by_cases hi : α i = 0
    · have he : single i 1 + (β - α) = β + single i 1 - α := by
        ext j
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, single_apply]
        split_ifs with hj
        · subst hj; omega
        · omega
      rw [ite_eq_right (by rwa [Finsupp.mem_support_iff, not_not]), ite_eq_left hi, add_zero,
        add_zero, monomial_mul_monomial, one_mul, he]
    · have he : β - (α - single i 1) = β + single i 1 - α := by
        ext j
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, single_apply]
        split_ifs with hj
        · subst hj; omega
        · omega
      rw [ite_eq_left (Finsupp.mem_support_iff.mpr hi), ite_eq_right hi, Nat.cast_add, map_add,
        he]
      congr 1
      by_cases hc : choose β α = 0
      · rw [hc, Nat.cast_zero, monomial_zero, mul_zero, monomial_zero]
      · have hle := Finsupp.le_def.mp (choose_ne_zero_iff.mp hc)
        have he' : single i 1 + (β - α) = β + single i 1 - α := by
          ext j
          have := hle j
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, single_apply]
          split_ifs <;> omega
        rw [monomial_mul_monomial, one_mul, he']

/-- The Hasse-Schmidt derivative of a monomial: `D^α (r x^β) = binom(β, α) r x^(β - α)`. The
coefficient is `0` unless `α ≤ β`. -/
theorem hasseDeriv_monomial (α β : σ →₀ ℕ) (r : R) :
    hasseDeriv α (monomial β r) = monomial (β - α) ((choose β α : R) * r) := by
  have h : monomial β r = C r * monomial β (1 : R) := by rw [C_mul_monomial, mul_one]
  rw [hasseDeriv_apply, h, map_mul, taylor_C, coeff_C_mul, coeff_taylor_monomial_one,
    C_mul_monomial, mul_comm r]

/-- The operator `D^0` is the identity. -/
@[simp]
theorem hasseDeriv_zero : (hasseDeriv 0 : MvPolynomial σ R →ₗ[R] MvPolynomial σ R) =
    LinearMap.id :=
  linearMap_ext_monomial fun β r => by
    rw [hasseDeriv_monomial, tsub_zero, choose_zero_right, Nat.cast_one, one_mul,
      LinearMap.id_apply]

theorem hasseDeriv_zero_apply (f : MvPolynomial σ R) : hasseDeriv 0 f = f := by
  rw [hasseDeriv_zero, LinearMap.id_apply]

/-- `D^α` kills the constants for `α ≠ 0`. -/
theorem hasseDeriv_C [DecidableEq σ] (α : σ →₀ ℕ) (r : R) :
    hasseDeriv α (C r : MvPolynomial σ R) = if α = 0 then C r else 0 := by
  rw [← monomial_zero', hasseDeriv_monomial]
  split_ifs with h
  · rw [h, tsub_zero, choose_zero_right, Nat.cast_one, one_mul]
  · rw [choose_eq_zero_iff.mpr (fun h' => h (nonpos_iff_eq_zero.mp h')), Nat.cast_zero, zero_mul,
      monomial_zero]

/-- `D^α (x_i)` is `x_i` for `α = 0`, `1` for `α = e_i`, and `0` otherwise. -/
theorem hasseDeriv_X [DecidableEq σ] (α : σ →₀ ℕ) (i : σ) :
    hasseDeriv α (X i : MvPolynomial σ R) =
      if α = 0 then X i else if α = single i 1 then 1 else 0 := by
  rw [X, hasseDeriv_monomial, mul_one]
  split_ifs with h0 h1
  · rw [h0, tsub_zero, choose_zero_right, Nat.cast_one]
  · rw [h1, tsub_self, choose_self, Nat.cast_one, monomial_zero', C_1]
  · have hle : ¬ α ≤ single i 1 := by
      intro hle
      have hle' := Finsupp.le_def.mp hle
      have hi := hle' i
      rw [single_eq_same] at hi
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with hi | hi
      · refine h0 (Finsupp.ext fun j => ?_)
        have := hle' j
        rw [single_apply] at this
        rw [Finsupp.zero_apply]
        split_ifs at this with hj
        · rw [← hj, hi]
        · omega
      · refine h1 (Finsupp.ext fun j => ?_)
        have := hle' j
        rw [single_apply] at this ⊢
        split_ifs at this ⊢ with hj
        · rw [← hj, hi]
        · omega
    rw [choose_eq_zero_iff.mpr hle, Nat.cast_zero, monomial_zero]

/-! ### One variable and first derivatives -/

/-- In one variable, `D^α` is the Hasse derivative `Polynomial.hasseDeriv` of order `α default` of
Mathlib (Proposition 6.3.2 of Volume 1 of the handbook). The variable set `σ` has one element. -/
theorem uniqueAlgEquiv_hasseDeriv [Unique σ] (α : σ →₀ ℕ) (f : MvPolynomial σ R) :
    uniqueAlgEquiv R σ (hasseDeriv α f) =
      Polynomial.hasseDeriv (α default) (uniqueAlgEquiv R σ f) := by
  classical
  refine MvPolynomial.induction_on' f (fun β r => ?_) fun p q hp hq => ?_
  · have hs : α.support ⊆ {default} := fun j _ => Finset.mem_singleton.mpr (Unique.eq_default j)
    rw [hasseDeriv_monomial, uniqueAlgEquiv_monomial, uniqueAlgEquiv_monomial,
      Polynomial.hasseDeriv_monomial, Finsupp.tsub_apply, choose_eq_prod_of_subset β α hs,
      Finset.prod_singleton]
  · rw [map_add, map_add, hp, hq, map_add, map_add]

/-- `D^(e_i)` is the partial derivative `∂_i`. -/
theorem hasseDeriv_single_one (i : σ) (f : MvPolynomial σ R) :
    hasseDeriv (single i 1) f = pderiv i f := by
  refine MvPolynomial.induction_on' f (fun β r => ?_) fun p q hp hq => ?_
  · rw [hasseDeriv_monomial, pderiv_monomial, choose_single, Nat.choose_one_right, mul_comm]
  · rw [map_add, map_add, hp, hq]

/-! ### The Leibniz rule and the composition rule -/

/-- The Leibniz rule: `D^α (f g) = ∑_(β + γ = α) D^β f D^γ g`. The substitution `x ↦ x + y` is a
homomorphism of rings, and the coefficient of `y^α` in a product is this sum. -/
theorem hasseDeriv_mul [DecidableEq σ] (α : σ →₀ ℕ) (f g : MvPolynomial σ R) :
    hasseDeriv α (f * g) =
      ∑ x ∈ Finset.antidiagonal α, hasseDeriv x.1 f * hasseDeriv x.2 g := by
  simp only [hasseDeriv_apply, map_mul, coeff_mul]

/-- The composition rule: `D^α (D^β f) = binom(α + β, α) D^(α + β) f`. -/
theorem hasseDeriv_comp (α β : σ →₀ ℕ) (f : MvPolynomial σ R) :
    hasseDeriv α (hasseDeriv β f) = choose (α + β) α • hasseDeriv (α + β) f := by
  refine MvPolynomial.induction_on' f (fun γ r => ?_) fun p q hp hq => ?_
  · rw [hasseDeriv_monomial, hasseDeriv_monomial, hasseDeriv_monomial, smul_monomial, tsub_tsub,
      add_comm β α, ← mul_assoc, ← Nat.cast_mul, choose_tsub_mul_choose, nsmul_eq_mul,
      Nat.cast_mul, mul_assoc]
  · rw [map_add, map_add, map_add, hp, hq, smul_add]

/-- The composition rule for the linear maps. -/
theorem hasseDeriv_comp' (α β : σ →₀ ℕ) :
    (hasseDeriv α).comp (hasseDeriv β) =
      choose (α + β) α • (hasseDeriv (α + β) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R) :=
  LinearMap.ext fun f => hasseDeriv_comp α β f

/-! ### Coefficients and the order -/

/-- The coefficient of `x^γ` in `D^α f` is `binom(γ + α, α)` times the coefficient of
`x^(γ + α)` in `f`. -/
theorem coeff_hasseDeriv (α γ : σ →₀ ℕ) (f : MvPolynomial σ R) :
    (hasseDeriv α f).coeff γ = (choose (γ + α) α : R) * f.coeff (γ + α) := by
  classical
  refine MvPolynomial.induction_on' f (fun β r => ?_) fun p q hp hq => ?_
  · rw [hasseDeriv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : β = γ + α
    · subst h
      rw [add_tsub_cancel_right, ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right h, mul_zero]
      split_ifs with h'
      · rw [choose_eq_zero_iff.mpr fun hle => h (by rw [← h', tsub_add_cancel_of_le hle]),
          Nat.cast_zero, zero_mul]
      · rfl
  · rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add]

/-- The value of `D^α f` at the origin is the coefficient of `x^α` in `f`. -/
theorem constantCoeff_hasseDeriv (α : σ →₀ ℕ) (f : MvPolynomial σ R) :
    constantCoeff (hasseDeriv α f) = f.coeff α := by
  rw [constantCoeff_eq, coeff_hasseDeriv, zero_add, choose_self,
    Nat.cast_one, one_mul]

/-- The order criterion at the origin: `ord f ≥ d` if and only if `(D^α f)(0) = 0` for each `α`
with `|α| < d`. -/
theorem le_ord_iff_hasseDeriv {f : MvPolynomial σ R} {d : ℕ} :
    (d : ℕ∞) ≤ ord f ↔ ∀ α : σ →₀ ℕ, degree α < d → constantCoeff (hasseDeriv α f) = 0 := by
  simp only [constantCoeff_hasseDeriv]
  exact le_ord_iff

/-- `D^α f = 0` if `α` is not below the least upper bound of the exponents of `f`. -/
theorem hasseDeriv_eq_zero_of_not_le {α : σ →₀ ℕ} {f : MvPolynomial σ R}
    (h : ¬ α ≤ f.support.sup id) : hasseDeriv α f = 0 := by
  ext γ
  rw [coeff_hasseDeriv, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_cases hc : f.coeff (γ + α) = 0
  · rw [hc, mul_zero]
  · exact absurd
      (le_add_self.trans (Finset.le_sup (f := id) (MvPolynomial.mem_support_iff.mpr hc))) h

/-! ### The Taylor formula -/

/-- The Taylor formula: `f(x + y) = ∑_α (D^α f)(x) y^α`, with a finite sum over the multi-indices
below the exponents of `f`. -/
theorem taylor_eq_sum [DecidableEq σ] (f : MvPolynomial σ R) :
    taylor σ R f = ∑ α ∈ Finset.Iic (f.support.sup id), monomial α (hasseDeriv α f) := by
  refine MvPolynomial.ext _ _ fun γ => ?_
  rw [coeff_taylor, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact hasseDeriv_eq_zero_of_not_le (by simpa using h)

/-- The translation `x ↦ a + y` is the Taylor substitution followed by `x ↦ a`. -/
theorem aeval_X_add_C_eq_map_taylor (a : σ → R) (f : MvPolynomial σ R) :
    aeval (fun i => X i + C (a i)) f = map (eval a) (taylor σ R f) := by
  induction f using MvPolynomial.induction_on
  · rw [aeval_C, taylor_C, map_C, eval_C, algebraMap_eq]
  · rename_i p q hp hq
    rw [map_add, map_add, hp, hq, map_add]
  · rename_i p i hp
    rw [map_mul, map_mul, hp, aeval_X, taylor_X, map_mul, map_add, map_C, map_X, eval_X,
      add_comm (C (a i))]

/-- The Taylor formula at a point `a`: the coefficient of `y^α` in `f(a + y)` is `(D^α f)(a)`. -/
theorem coeff_aeval_X_add_C (a : σ → R) (α : σ →₀ ℕ) (f : MvPolynomial σ R) :
    (aeval (fun i => X i + C (a i)) f).coeff α = eval a (hasseDeriv α f) := by
  rw [aeval_X_add_C_eq_map_taylor, coeff_map, coeff_taylor]

/-- The Taylor formula at a point `a`: `f(a + y) = ∑_α (D^α f)(a) y^α`. -/
theorem aeval_X_add_C_eq_sum [DecidableEq σ] (a : σ → R) (f : MvPolynomial σ R) :
    aeval (fun i => X i + C (a i)) f =
      ∑ α ∈ Finset.Iic (f.support.sup id), monomial α (eval a (hasseDeriv α f)) := by
  rw [aeval_X_add_C_eq_map_taylor, taylor_eq_sum, map_sum]
  simp only [map_monomial]

/-- The order criterion at a point `a` (Proposition 1.1.4 of Volume 7 of the handbook): the
order of `f` at `a`, the order of the translate `f(a + y)`, is at least `d` if and only if
`(D^α f)(a) = 0` for each `α` with `|α| < d`. -/
theorem le_ord_aeval_X_add_C_iff (a : σ → R) {f : MvPolynomial σ R} {d : ℕ} :
    (d : ℕ∞) ≤ ord (aeval (fun i => X i + C (a i)) f) ↔
      ∀ α : σ →₀ ℕ, degree α < d → eval a (hasseDeriv α f) = 0 := by
  simp only [le_ord_iff, coeff_aeval_X_add_C]

/-! ### Polynomials in the `q`-th powers of the variables -/

/-- A polynomial is a polynomial in the `x_i^q` if and only if `q` divides each exponent of each
of its monomials. -/
theorem exists_expand_eq_iff {q : ℕ} (f : MvPolynomial σ R) :
    (∃ g, expand q g = f) ↔ ∀ β ∈ f.support, ∀ i, q ∣ β i := by
  classical
  constructor
  · rintro ⟨g, rfl⟩
    refine MvPolynomial.induction_on' g (fun γ r β hβ i => ?_) fun p₁ p₂ h₁ h₂ β hβ i => ?_
    · rw [expand_monomial, support_monomial] at hβ
      split_ifs at hβ with hr
      · exact absurd hβ (Finset.notMem_empty β)
      · rw [Finset.mem_singleton] at hβ
        subst hβ
        exact Dvd.intro (γ i) (by rw [Finsupp.smul_apply, smul_eq_mul])
    · rw [map_add] at hβ
      rcases Finset.mem_union.mp (MvPolynomial.support_add hβ) with h | h
      · exact h₁ β h i
      · exact h₂ β h i
  · intro h
    refine ⟨∑ β ∈ f.support, monomial (β.mapRange (· / q) (Nat.zero_div q)) (f.coeff β), ?_⟩
    rw [map_sum]
    conv_rhs => rw [f.as_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    have he : q • β.mapRange (· / q) (Nat.zero_div q) = β := by
      ext i
      rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.mapRange_apply, Nat.mul_div_cancel' (h β hβ i)]
    rw [expand_monomial, he]

end Semiring

/-! ### The test for `q`-th powers in characteristic `p` -/

section Lucas

variable (p : ℕ) [hp : Fact p.Prime]

/-- A consequence of the theorem of Lucas: for `q = p^e`, `binom(n, n mod q) ≡ 1` modulo `p`.
The digits of `n mod q` in base `p` are the lowest `e` digits of `n`, and the others are `0`. -/
theorem choose_mod_pow_modEq_one (e n : ℕ) : Nat.choose n (n % p ^ e) ≡ 1 [MOD p] := by
  induction e generalizing n with
  | zero => rw [pow_zero, Nat.mod_one, Nat.choose_zero_right]
  | succ e ih =>
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := n)
      (k := n % p ^ (e + 1))
    rw [pow_succ', Nat.mod_mod_of_dvd n (dvd_mul_right p _), Nat.mod_mul_right_div_self,
      Nat.choose_self, one_mul] at h
    rw [pow_succ']
    exact h.trans (ih (n / p))

/-- A consequence of the theorem of Lucas: for `q = p^e`, if `q ∣ n` and `q ∤ a`, then
`binom(n, a) ≡ 0` modulo `p`. -/
theorem choose_modEq_zero_of_pow_dvd {e n a : ℕ} (hn : p ^ e ∣ n) (ha : ¬ p ^ e ∣ a) :
    Nat.choose n a ≡ 0 [MOD p] := by
  induction e generalizing n a with
  | zero =>
    rw [pow_zero] at ha
    exact absurd (one_dvd a) ha
  | succ e ih =>
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := n) (k := a)
    rw [Nat.mod_eq_zero_of_dvd ((dvd_pow_self p (Nat.succ_ne_zero e)).trans hn)] at h
    by_cases ha0 : a % p = 0
    · have hpa : p ∣ a := Nat.dvd_of_mod_eq_zero ha0
      have hn' : p ^ e ∣ n / p := by
        obtain ⟨c, rfl⟩ := hn
        rw [pow_succ', mul_assoc, Nat.mul_div_cancel_left _ hp.out.pos]
        exact dvd_mul_right _ _
      have ha' : ¬ p ^ e ∣ a / p := fun h' => ha (by
        rw [← Nat.mul_div_cancel' hpa, pow_succ']
        exact mul_dvd_mul_left p h')
      simpa using h.trans ((ih hn' ha').mul_left _)
    · rwa [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero ha0), zero_mul] at h

variable {R : Type*} [CommSemiring R] [CharP R p]

theorem natCast_eq_one_of_modEq {n : ℕ} (h : n ≡ 1 [MOD p]) : (n : R) = 1 := by
  rw [← Nat.mod_add_div n p, Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero R p, zero_mul,
    add_zero,
    show n % p = 1 % p from h, Nat.mod_eq_of_lt hp.out.one_lt, Nat.cast_one]

omit hp in
theorem natCast_eq_zero_of_modEq {n : ℕ} (h : n ≡ 0 [MOD p]) : (n : R) = 0 :=
  (CharP.cast_eq_zero_iff R p n).mpr (Nat.modEq_zero_iff_dvd.mp h)

end Lucas

section CharP

variable {σ R : Type*} [CommSemiring R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]

/-- The test for `q`-th powers. Let `R` have characteristic `p` and let `q = p^e`. Then `f` is a
polynomial in `x_1^q, ..., x_n^q` if and only if `D^α f = 0` for each `α ≠ 0` with `α_i < q` for
each `i`. For the direct implication, `binom(q b, a) ≡ 0` modulo `p` for `0 < a < q`. For the
converse, let `x^β` be a monomial of `f` with `q ∤ β_i`, and let `α = β mod q`. Then
`binom(β, α) ≡ 1` modulo `p`, so `D^α f` has the monomial `x^(β - α)`. -/
theorem exists_expand_eq_iff_hasseDeriv (e : ℕ) (f : MvPolynomial σ R) :
    (∃ g, expand (p ^ e) g = f) ↔
      ∀ α : σ →₀ ℕ, α ≠ 0 → (∀ i, α i < p ^ e) → hasseDeriv α f = 0 := by
  have hq : 0 < p ^ e := pow_pos hp.out.pos e
  rw [exists_expand_eq_iff]
  constructor
  · intro h α hα hαq
    ext γ
    rw [coeff_hasseDeriv, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    by_cases hc : f.coeff (γ + α) = 0
    · rw [hc, mul_zero]
    · obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
        by_contra! h'
        exact hα (Finsupp.ext h')
      have hdvd := h _ (MvPolynomial.mem_support_iff.mpr hc) i
      have hnd : ¬ p ^ e ∣ α i := fun hd => hi (Nat.eq_zero_of_dvd_of_lt hd (hαq i))
      rw [choose, Nat.cast_prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi)
        (natCast_eq_zero_of_modEq p (choose_modEq_zero_of_pow_dvd p hdvd hnd)), zero_mul]
  · intro H β hβ i
    by_contra hi
    let α : σ →₀ ℕ := β.mapRange (· % p ^ e) (Nat.zero_mod _)
    have hαi : α i ≠ 0 := fun h0 => hi (Nat.dvd_of_mod_eq_zero h0)
    have hα0 : α ≠ 0 := fun h0 => hαi (by rw [h0, Finsupp.zero_apply])
    have hαq : ∀ j, α j < p ^ e := fun j => Nat.mod_lt _ hq
    have hle : α ≤ β := Finsupp.le_def.mpr fun j => Nat.mod_le _ _
    have hc := congrArg (fun g : MvPolynomial σ R => g.coeff (β - α)) (H α hα0 hαq)
    rw [coeff_hasseDeriv, tsub_add_cancel_of_le hle, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply] at hc
    have h1 : (choose β α : R) = 1 := by
      rw [choose, Nat.cast_prod]
      exact Finset.prod_eq_one fun j _ =>
        natCast_eq_one_of_modEq p (choose_mod_pow_modEq_one p e (β j))
    rw [h1, one_mul] at hc
    exact MvPolynomial.mem_support_iff.mp hβ hc

/-- For `α` with `α_i < q` for each `i`, `D^α (g(x^q) f) = g(x^q) D^α f`. So these operators are
linear over the polynomials in the `x_i^q` (the first claim of Theorem 6.3.6 of Volume 1 of the
handbook). -/
theorem hasseDeriv_expand_mul (e : ℕ) {α : σ →₀ ℕ} (hα : ∀ i, α i < p ^ e)
    (g f : MvPolynomial σ R) :
    hasseDeriv α (expand (p ^ e) g * f) = expand (p ^ e) g * hasseDeriv α f := by
  classical
  rw [hasseDeriv_mul, Finset.sum_eq_single (0, α)]
  · rw [hasseDeriv_zero_apply]
  · rintro ⟨a, b⟩ hab hne
    obtain hab : a + b = α := Finset.mem_antidiagonal.mp hab
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_add] at hab
      exact hne (by rw [hab])
    have hlt : ∀ i, a i < p ^ e := fun i =>
      (Nat.le_add_right (a i) (b i)).trans_lt (by rw [← Finsupp.add_apply, hab]; exact hα i)
    rw [(exists_expand_eq_iff_hasseDeriv p e _).mp ⟨g, rfl⟩ a ha0 hlt, zero_mul]
  · intro h
    exact absurd (Finset.mem_antidiagonal.mpr (zero_add α)) h

end CharP

end Singularity.Algebra.MvHasse
