/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# The example of Narasimhan in characteristic 2

This file certifies the example of Narasimhan [Nar83] in the form of Example 2.2.1 of Volume 9 of
the handbook. The field `K` has characteristic 2, the variables `x, y, z, w` are
`X 0, X 1, X 2, X 3`, and

  `f = x^2 + y z^3 + z w^3 + y^7 w`.

In characteristic 0 the points of maximal order of a hypersurface lie locally in a smooth
hypersurface, a hypersurface of maximal contact. The example shows that this is false in
characteristic 2, also for formal hypersurfaces. The curve `γ(t) = (t^32, t^7, t^19, t^15)` goes
through the origin, and its points have order 2 for `f`. But no smooth formal hypersurface germ at
the origin contains the curve.

What the file certifies, in `narasimhan`:

* `f(γ(t)) = 0` (`aeval_narasimhanCurve_narasimhanF`). The four terms are `t^64`, and `4 = 0`.
* All partial derivatives of `f` vanish on `γ` (`aeval_narasimhanCurve_pderiv`). Because
  `3 = 1` and `7 = 1` in `K`, they are `0`, `z^3 + y^6 w`, `y z^2 + w^3` and `z w^2 + y^7`
  (`pderiv_zero_narasimhanF` to `pderiv_three_narasimhanF`).
* Let `h` be a formal power series in `K[[x, y, z, w]]` with `h(γ(t)) = 0`. Then the order of `h`
  is at least 2 (`two_le_order_of_subst_eq_zero`). The substitution is `MvPowerSeries.subst`. The
  monomial `x^a y^b z^c w^d` goes to `t^(32a + 7b + 19c + 15d)`. If `a + b + c + d ≤ 1`, then no
  other monomial goes to the same power of `t` (`eq_of_weight_eq`). So the coefficient of this
  power of `t` in `h(γ(t))` is the coefficient of the monomial in `h`.
* A formal power series with a nonzero linear part does not vanish on `γ`
  (`subst_narasimhanCurve_ne_zero`). A smooth formal hypersurface germ at the origin is `h = 0`
  for such a series `h`, so it does not contain the curve.

The third item does not use the characteristic. It also does not need the hypothesis that the
constant coefficient of `h` is 0, because the hypothesis `h(γ(t)) = 0` gives it.

The curve is a family of formal power series in `t` (`narasimhanCurve`). It is a family of
polynomials, so `f(γ(t)) = 0` is also an equation in `K[t]`.

## References

* [Nar83] R. Narasimhan, *Hyperplanarity of the equimultiple locus*, Proc. Amer. Math. Soc. 87
  (1983), 403-408.
-/

open MvPolynomial

namespace Singularity.Examples

/-! ### The polynomial and the curve -/

/-- The polynomial `f = x^2 + y z^3 + z w^3 + y^7 w` of Narasimhan. -/
noncomputable def narasimhanF (K : Type*) [CommRing K] : MvPolynomial (Fin 4) K :=
  X 0 ^ 2 + X 1 * X 2 ^ 3 + X 2 * X 3 ^ 3 + X 1 ^ 7 * X 3

/-- The exponents `(32, 7, 19, 15)` of the curve of Narasimhan. -/
def narasimhanExp : Fin 4 → ℕ := ![32, 7, 19, 15]

/-- The curve `γ(t) = (t^32, t^7, t^19, t^15)`, as a family of formal power series in `t`. -/
noncomputable def narasimhanCurve (K : Type*) [CommRing K] : Fin 4 → PowerSeries K :=
  fun i => PowerSeries.X ^ narasimhanExp i

/-- The weight `32 a + 7 b + 19 c + 15 d` of the monomial `x^a y^b z^c w^d`. The curve sends the
monomial to `t` to the power of its weight. -/
def narasimhanWeight (d : Fin 4 →₀ ℕ) : ℕ := 32 * d 0 + 7 * d 1 + 19 * d 2 + 15 * d 3

section CharTwo

variable {K : Type*} [Field K] [CharP K 2]

/-! ### The curve lies on `f = 0` -/

/-- `f(γ(t)) = 0`. -/
theorem aeval_narasimhanCurve_narasimhanF :
    aeval (narasimhanCurve K) (narasimhanF K) = 0 := by
  have h2 : (2 : PowerSeries K) = 0 := by
    rw [← map_ofNat (algebraMap K (PowerSeries K)) 2, CharTwo.two_eq_zero, map_zero]
  simp only [narasimhanF, narasimhanCurve, narasimhanExp, map_add, map_mul, map_pow, aeval_X]
  simp only [Matrix.cons_val, ← pow_mul, ← pow_add, Nat.reduceMul, Nat.reduceAdd]
  linear_combination (2 * PowerSeries.X ^ 64 : PowerSeries K) * h2

/-! ### The partial derivatives vanish on the curve -/

private theorem two_eq_zero_mvPolynomial : (2 : MvPolynomial (Fin 4) K) = 0 := by
  rw [← map_ofNat (C : K →+* MvPolynomial (Fin 4) K) 2, CharTwo.two_eq_zero, map_zero]

/-- `∂f/∂x = 0`. -/
theorem pderiv_zero_narasimhanF : pderiv 0 (narasimhanF K) = 0 := by
  simp [narasimhanF, pderiv_X]
  exact two_eq_zero_mvPolynomial (K := K)

/-- `∂f/∂y = z^3 + y^6 w`, because `7 = 1` in `K`. -/
theorem pderiv_one_narasimhanF : pderiv 1 (narasimhanF K) = X 2 ^ 3 + X 1 ^ 6 * X 3 := by
  simp [narasimhanF, pderiv_X]
  linear_combination
    (3 * X 1 ^ 6 * X 3 : MvPolynomial (Fin 4) K) * two_eq_zero_mvPolynomial (K := K)

/-- `∂f/∂z = y z^2 + w^3`, because `3 = 1` in `K`. -/
theorem pderiv_two_narasimhanF : pderiv 2 (narasimhanF K) = X 1 * X 2 ^ 2 + X 3 ^ 3 := by
  simp [narasimhanF, pderiv_X]
  linear_combination two_eq_zero_mvPolynomial (K := K)

/-- `∂f/∂w = z w^2 + y^7`, because `3 = 1` in `K`. -/
theorem pderiv_three_narasimhanF : pderiv 3 (narasimhanF K) = X 2 * X 3 ^ 2 + X 1 ^ 7 := by
  simp [narasimhanF, pderiv_X]
  linear_combination two_eq_zero_mvPolynomial (K := K)

/-- All partial derivatives of `f` vanish on `γ`. On `γ` the three nonzero ones are `t^57 + t^57`,
`t^45 + t^45` and `t^49 + t^49`. -/
theorem aeval_narasimhanCurve_pderiv (i : Fin 4) :
    aeval (narasimhanCurve K) (pderiv i (narasimhanF K)) = 0 := by
  have h2 : (2 : PowerSeries K) = 0 := by
    rw [← map_ofNat (algebraMap K (PowerSeries K)) 2, CharTwo.two_eq_zero, map_zero]
  fin_cases i
  · simp [pderiv_zero_narasimhanF]
  all_goals
    simp only [Fin.mk_one, Fin.reduceFinMk, pderiv_one_narasimhanF, pderiv_two_narasimhanF,
      pderiv_three_narasimhanF, narasimhanCurve, narasimhanExp, map_add, map_mul, map_pow, aeval_X,
      Matrix.cons_val, ← pow_mul, ← pow_add, Nat.reduceMul, Nat.reduceAdd]
  · linear_combination (PowerSeries.X ^ 57 : PowerSeries K) * h2
  · linear_combination (PowerSeries.X ^ 45 : PowerSeries K) * h2
  · linear_combination (PowerSeries.X ^ 49 : PowerSeries K) * h2

end CharTwo

/-! ### No smooth formal hypersurface contains the curve -/

section Order

variable {K : Type*} [Field K]

/-- The curve can be substituted in a formal power series, because its constant coefficients
are 0. -/
theorem hasSubst_narasimhanCurve : MvPowerSeries.HasSubst (narasimhanCurve K) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    have hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 :=
      PowerSeries.constantCoeff_X
    fin_cases i <;> simp [narasimhanCurve, narasimhanExp, hX]

/-- The curve sends the monomial with exponent `d` to `t` to the power `narasimhanWeight d`. -/
theorem prod_narasimhanCurve_pow (d : Fin 4 →₀ ℕ) :
    (d.prod fun i e => narasimhanCurve K i ^ e) = PowerSeries.X ^ narasimhanWeight d := by
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_four]
  simp only [narasimhanCurve, narasimhanWeight, ← pow_mul, ← pow_add]
  congr 1

/-- The coefficient of `t^n` in `h(γ(t))` is the sum of the coefficients of `h` at the monomials of
weight `n`. -/
theorem coeff_subst_narasimhanCurve (h : MvPowerSeries (Fin 4) K) (n : ℕ) :
    PowerSeries.coeff n (MvPowerSeries.subst (narasimhanCurve K) h) =
      ∑ᶠ d, if narasimhanWeight d = n then MvPowerSeries.coeff d h else 0 := by
  rw [PowerSeries.coeff_def (s := Finsupp.single () n) (by simp),
    MvPowerSeries.coeff_subst hasSubst_narasimhanCurve]
  refine finsum_congr fun d => ?_
  rw [prod_narasimhanCurve_pow, PowerSeries.coeff_coeToMvPowerSeries, PowerSeries.coeff_X_pow,
    smul_eq_mul]
  by_cases hw : narasimhanWeight d = n
  · simp [hw]
  · simp [hw, Ne.symm hw]

/-- A monomial of total degree at most 1 is the only monomial of its weight. -/
theorem eq_of_weight_eq {d d' : Fin 4 →₀ ℕ} (hd : d.degree ≤ 1)
    (hw : narasimhanWeight d' = narasimhanWeight d) : d' = d := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_four] at hd
  simp only [narasimhanWeight] at hw
  have key : ∀ a b c e a' b' c' e' : ℕ, a + b + c + e ≤ 1 →
      32 * a' + 7 * b' + 19 * c' + 15 * e' = 32 * a + 7 * b + 19 * c + 15 * e →
      a' = a ∧ b' = b ∧ c' = c ∧ e' = e := by
    intro a b c e a' b' c' e' h1 h2
    have ha : a ≤ 1 := by omega
    have hb : b ≤ 1 := by omega
    have hc : c ≤ 1 := by omega
    have he : e ≤ 1 := by omega
    have ha' : a' ≤ 1 := by omega
    have hc' : c' ≤ 1 := by omega
    have he' : e' ≤ 2 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases e <;>
      (try omega) <;> interval_cases a' <;> interval_cases c' <;> interval_cases e' <;> omega
  have e := key _ _ _ _ _ _ _ _ hd hw
  ext i
  fin_cases i
  exacts [e.1, e.2.1, e.2.2.1, e.2.2.2]

/-- For a monomial `d` of total degree at most 1, the coefficient of `t^(weight d)` in `h(γ(t))` is
the coefficient of `d` in `h`. -/
theorem coeff_weight_subst_narasimhanCurve (h : MvPowerSeries (Fin 4) K) {d : Fin 4 →₀ ℕ}
    (hd : d.degree ≤ 1) :
    PowerSeries.coeff (narasimhanWeight d) (MvPowerSeries.subst (narasimhanCurve K) h) =
      MvPowerSeries.coeff d h := by
  rw [coeff_subst_narasimhanCurve, finsum_eq_single _ d]
  · simp
  · intro d' hd'
    simp only [ite_eq_right_iff]
    exact fun hw => absurd (eq_of_weight_eq hd hw) hd'

/-- If `h(γ(t)) = 0`, then the coefficients of `h` of total degree at most 1 are 0. -/
theorem coeff_eq_zero_of_subst_eq_zero {h : MvPowerSeries (Fin 4) K}
    (hγ : MvPowerSeries.subst (narasimhanCurve K) h = 0) {d : Fin 4 →₀ ℕ} (hd : d.degree ≤ 1) :
    MvPowerSeries.coeff d h = 0 := by
  rw [← coeff_weight_subst_narasimhanCurve h hd, hγ, map_zero]

/-- If `h(γ(t)) = 0`, then the order of `h` is at least 2. -/
theorem two_le_order_of_subst_eq_zero {h : MvPowerSeries (Fin 4) K}
    (hγ : MvPowerSeries.subst (narasimhanCurve K) h = 0) : 2 ≤ h.order := by
  exact_mod_cast MvPowerSeries.nat_le_order (n := 2) fun d hd =>
    coeff_eq_zero_of_subst_eq_zero hγ (by omega)

/-- No formal power series with a nonzero linear part vanishes on `γ`. In particular no smooth
formal hypersurface through the origin contains `γ`. -/
theorem subst_narasimhanCurve_ne_zero {h : MvPowerSeries (Fin 4) K}
    (hlin : ∃ i, MvPowerSeries.coeff (Finsupp.single i 1) h ≠ 0) :
    MvPowerSeries.subst (narasimhanCurve K) h ≠ 0 := by
  obtain ⟨i, hi⟩ := hlin
  exact fun hγ => hi (coeff_eq_zero_of_subst_eq_zero hγ (by simp))

end Order

/-! ### The example -/

/-- The example of Narasimhan [Nar83]. Let `K` be a field of characteristic 2, let
`f = x^2 + y z^3 + z w^3 + y^7 w`, and let `γ(t) = (t^32, t^7, t^19, t^15)`. Then `f` and all its
partial derivatives vanish on `γ`, so the points of `γ` have order 2 for `f`. Each formal power
series `h` with `h(γ(t)) = 0` has order at least 2. So a formal power series with a nonzero linear
part does not vanish on `γ`, and no smooth formal hypersurface germ at the origin contains the
points of order 2 of `f`. -/
theorem narasimhan {K : Type*} [Field K] [CharP K 2] :
    aeval (narasimhanCurve K) (narasimhanF K) = 0 ∧
      (∀ i, aeval (narasimhanCurve K) (pderiv i (narasimhanF K)) = 0) ∧
      (∀ h : MvPowerSeries (Fin 4) K,
        MvPowerSeries.subst (narasimhanCurve K) h = 0 → 2 ≤ h.order) ∧
      (∀ h : MvPowerSeries (Fin 4) K, (∃ i, MvPowerSeries.coeff (Finsupp.single i 1) h ≠ 0) →
        MvPowerSeries.subst (narasimhanCurve K) h ≠ 0) :=
  ⟨aeval_narasimhanCurve_narasimhanF, aeval_narasimhanCurve_pderiv,
    fun _ => two_le_order_of_subst_eq_zero, fun _ => subst_narasimhanCurve_ne_zero⟩

end Singularity.Examples
