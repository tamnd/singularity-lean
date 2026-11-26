/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.CharacteristicPolyhedronClean
import Singularity.Invariant.Order
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Order.SuccPred.ENat

/-!
# The equation `z^p + x y w`

This file proves the algebraic part of Example 2.3.4 of Volume 6 of the handbook. The variables
`x, y, w` are `X 0, X 1, X 2`, and in four variables the variable `z` is `X 3`. Let `g = x y w`
(`xyw`).

What the file proves:

* The partial derivatives of `g` are `y w`, `x w` and `x y` (`pderiv_zero_xyw`, `pderiv_one_xyw`,
  `pderiv_two_xyw`). Over a ring without zero divisors they vanish together at a point exactly
  when two of the coordinates are `0` (`eval_pderiv_xyw_eq_zero_iff`).
* In characteristic `p`, the series `x y w` is not a `p`-th power in `k[[x, y, w]]`
  (`pow_ne_X_mul_X_mul_X`), and the polynomial `x y w` is not a `p`-th power in `k[x, y, w]`
  (`pow_ne_xyw`). The reason is that each exponent of a `p`-th power lies in `p ℕ^3`.
* Over a field, the order of `z^p + x y w` at the origin is `min(p, 3)` (`ord_X_pow_add_xyw`),
  and for `a ≠ 0` the order of `(x + a) y w` is `2` (`ord_X_add_C_mul_xyw`).

The handbook also uses Lemma 2.3.2 to turn the orders into multiplicities of the hypersurface
`z^p + x y w = 0`, and it describes the singular locus as a set of points of a scheme. These parts
are not proved here.
-/

open MvPolynomial

namespace Singularity.Examples

/-- The polynomial `g = x y w`, with `x, y, w = X 0, X 1, X 2`. -/
noncomputable def xyw (R : Type*) [CommSemiring R] : MvPolynomial (Fin 3) R :=
  X 0 * X 1 * X 2

section Partial

variable {R : Type*} [CommSemiring R]

/-- `∂(x y w)/∂x = y w`. Volume 6, Example 2.3.4 of the handbook. -/
theorem pderiv_zero_xyw : pderiv 0 (xyw R) = X 1 * X 2 := by
  rw [xyw, pderiv_mul, pderiv_mul, pderiv_X_self, pderiv_X_of_ne (show (1 : Fin 3) ≠ 0 by decide),
    pderiv_X_of_ne (show (2 : Fin 3) ≠ 0 by decide)]
  ring

/-- `∂(x y w)/∂y = x w`. Volume 6, Example 2.3.4 of the handbook. -/
theorem pderiv_one_xyw : pderiv 1 (xyw R) = X 0 * X 2 := by
  rw [xyw, pderiv_mul, pderiv_mul, pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 3) ≠ 1 by decide),
    pderiv_X_of_ne (show (2 : Fin 3) ≠ 1 by decide)]
  ring

/-- `∂(x y w)/∂w = x y`. Volume 6, Example 2.3.4 of the handbook. -/
theorem pderiv_two_xyw : pderiv 2 (xyw R) = X 0 * X 1 := by
  rw [xyw, pderiv_mul, pderiv_mul, pderiv_X_of_ne (show (0 : Fin 3) ≠ 2 by decide),
    pderiv_X_of_ne (show (1 : Fin 3) ≠ 2 by decide), pderiv_X_self]
  ring

end Partial

/-- The partial derivatives of `x y w` vanish together at a point `a` exactly when two of the
coordinates of `a` are `0`. Volume 6, Example 2.3.4 of the handbook. -/
theorem eval_pderiv_xyw_eq_zero_iff {R : Type*} [CommRing R] [NoZeroDivisors R] (a : Fin 3 → R) :
    (∀ i, eval a (pderiv i (xyw R)) = 0) ↔
      (a 0 = 0 ∧ a 1 = 0) ∨ (a 0 = 0 ∧ a 2 = 0) ∨ (a 1 = 0 ∧ a 2 = 0) := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    rw [pderiv_zero_xyw] at h0
    rw [pderiv_one_xyw] at h1
    rw [pderiv_two_xyw] at h2
    simp only [eval_mul, eval_X, mul_eq_zero] at h0 h1 h2
    tauto
  · intro h i
    fin_cases i <;> simp [pderiv_zero_xyw, pderiv_one_xyw, pderiv_two_xyw] <;> tauto

section CharP

variable {k : Type*} [CommRing k] [Nontrivial k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The exponent `(1, 1, 1)` of `x y w`. -/
noncomputable def xywExp : Fin 3 →₀ ℕ :=
  Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1

theorem xywExp_zero : xywExp 0 = 1 := by
  simp [xywExp, Finsupp.single_apply]

/-- In characteristic `p`, the series `x y w` is not a `p`-th power in `k[[x, y, w]]`. The
coefficient of `x y w` in `g^p` is `0`, because each exponent of `g^p` lies in `p ℕ^3`. Volume 6,
Example 2.3.4 of the handbook, the claim `g ∉ R^p` for the power series ring. -/
theorem pow_ne_X_mul_X_mul_X (g : MvPowerSeries (Fin 3) k) :
    g ^ p ≠ MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2 := by
  intro h
  have hd : ¬ ∀ i, p ^ 1 ∣ xywExp i := by
    intro hall
    have h0 := hall 0
    rw [pow_one, xywExp_zero, Nat.dvd_one] at h0
    exact (Fact.out : p.Prime).one_lt.ne' h0
  have h1 := coeff_pow_expChar_pow_eq_zero p 1 g hd
  have hm : (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2 :
      MvPowerSeries (Fin 3) k) = MvPowerSeries.monomial xywExp 1 := by
    simp only [MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, mul_one, xywExp]
  rw [pow_one, h, hm, MvPowerSeries.coeff_monomial_same] at h1
  exact one_ne_zero h1

/-- In characteristic `p`, the polynomial `x y w` is not a `p`-th power in `k[x, y, w]`. Volume 6,
Example 2.3.4 of the handbook, the claim `g ∉ R^p` for the polynomial ring. -/
theorem pow_ne_xyw (g : MvPolynomial (Fin 3) k) : g ^ p ≠ xyw k := by
  intro h
  apply pow_ne_X_mul_X_mul_X p (g : MvPowerSeries (Fin 3) k)
  rw [← MvPolynomial.coe_pow, h, xyw, MvPolynomial.coe_mul, MvPolynomial.coe_mul,
    MvPolynomial.coe_X, MvPolynomial.coe_X, MvPolynomial.coe_X]

end CharP

section Order

variable {k : Type*} [Field k]

theorem ord_X_mul_X_mul_X (i j l : Fin 4) :
    ord (X i * X j * X l : MvPolynomial (Fin 4) k) = 3 := by
  rw [ord_mul, ord_mul, ord_X, ord_X, ord_X]
  norm_num

/-- The order of `z^p + x y w` at the origin is `min(p, 3)`. Here `z = X 3`. Volume 6,
Example 2.3.4 of the handbook, the order at the origin. -/
theorem ord_X_pow_add_xyw (p : ℕ) :
    ord (X 3 ^ p + X 0 * X 1 * X 2 : MvPolynomial (Fin 4) k) = min (p : ℕ∞) 3 := by
  have hp : ord (X 3 ^ p : MvPolynomial (Fin 4) k) = p := ord_X_pow 3 p
  have h3 := ord_X_mul_X_mul_X (k := k) 0 1 2
  rcases lt_trichotomy p 3 with hlt | heq | hgt
  · have hlt' : (p : ℕ∞) < 3 := by exact_mod_cast hlt
    have hlt2 : ord (X 3 ^ p : MvPolynomial (Fin 4) k) < ord (X 0 * X 1 * X 2) := by
      rw [hp, h3]
      exact hlt'
    rw [ord_add_of_lt hlt2, hp, min_eq_left hlt'.le]
  · subst heq
    simp only [Nat.cast_ofNat, min_self] at hp ⊢
    refine le_antisymm ?_ (le_ord_add hp.ge h3.ge)
    have hne : (Finsupp.single (3 : Fin 4) 3 : Fin 4 →₀ ℕ) ≠
        Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1 := by
      intro he
      have := DFunLike.congr_fun he 3
      simp [Finsupp.single_apply] at this
    have hc : (X 3 ^ 3 + X 0 * X 1 * X 2 : MvPolynomial (Fin 4) k).coeff
        (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1) ≠ 0 := by
      rw [coeff_add, coeff_X_pow, if_neg hne, coeff_mul_X, coeff_mul_X, coeff_X, if_pos rfl,
        zero_add]
      exact one_ne_zero
    calc ord _ ≤ _ := ord_le hc
      _ = 3 := by simp [Finsupp.degree_single]
  · have hgt' : (3 : ℕ∞) < p := by exact_mod_cast hgt
    have hgt2 : ord (X 0 * X 1 * X 2 : MvPolynomial (Fin 4) k) < ord (X 3 ^ p) := by
      rw [hp, h3]
      exact hgt'
    rw [add_comm, ord_add_of_lt hgt2, h3, min_eq_right hgt'.le]

/-- For `a ≠ 0`, the order of `(x + a) y w` at the origin is `2`. This is the order of `g` at the
point `(a, 0, 0)` of the line `y = w = 0`. Volume 6, Example 2.3.4 of the handbook, the order on
the lines. -/
theorem ord_X_add_C_mul_xyw {a : k} (ha : a ≠ 0) :
    ord ((X 0 + C a) * X 1 * X 2 : MvPolynomial (Fin 3) k) = 2 := by
  have h0 : ord (X 0 + C a : MvPolynomial (Fin 3) k) = 0 := by
    have hn : ¬ 1 ≤ ord (X 0 + C a : MvPolynomial (Fin 3) k) := by
      rw [one_le_ord_iff]
      simpa using ha
    exact ENat.lt_one_iff_eq_zero.mp (not_le.mp hn)
  rw [ord_mul, ord_mul, h0, ord_X, ord_X]
  norm_num

end Order

end Singularity.Examples
