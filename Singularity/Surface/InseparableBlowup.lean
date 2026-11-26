/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.Ring

/-!
# The blowup of `z^p = x^(p+1) + y^(p+1)`

Let `k` be a field of characteristic `p > 0` and let `f = z^p - x^(p+1) - y^(p+1)`. Volume 4, Example 2.3.5 of the handbook shows that the blowup of `V(f)` at the origin has exactly `p + 1` singular points. This file proves the algebraic steps of the proof.

* `Singularity.inseparable_xChart` and `Singularity.inseparable_zChart`: the substitutions of the `x`-chart and the `z`-chart. With `y = x y_1` and `z = x z_1`, `f = x^p (z_1^p - x h(y_1))` with `h = 1 + y_1^(p+1)`. With `x = z x_1` and `y = z y_1`, `f = z^p (1 - z (x_1^(p+1) + y_1^(p+1)))`. These hold in each commutative ring.
* `Singularity.derivative_one_add_X_pow_succ`: in characteristic `p`, `h' = (p + 1) y_1^p = y_1^p`.
* `Singularity.separable_one_add_X_pow_succ`: `h` is separable, since `1 · h + (-y_1) · h' = 1`.
* `Singularity.card_roots_one_add_X_pow_succ`: over an algebraically closed field of characteristic `p`, `h` has exactly `p + 1` distinct roots `c_1, ..., c_(p+1)`. These give the `p + 1` singular points `P_i = (0, c_i, 0)` of the `x`-chart.

The file does not prove that the points `P_i` are the singular points, the normality of the blowup, or the local form of the blowup at `P_i`.
-/

open Polynomial

namespace Singularity

section Charts

variable {R : Type*} [CommRing R]

/-- The `x`-chart: `y = x y_1` and `z = x z_1` give `f = x^p (z_1^p - x (1 + y_1^(p+1)))` (Volume 4, Example 2.3.5 of the handbook). -/
theorem inseparable_xChart (p : ℕ) (x y₁ z₁ : R) :
    (x * z₁) ^ p - x ^ (p + 1) - (x * y₁) ^ (p + 1) = x ^ p * (z₁ ^ p - x * (1 + y₁ ^ (p + 1))) := by
  ring

/-- The `z`-chart: `x = z x_1` and `y = z y_1` give `f = z^p (1 - z (x_1^(p+1) + y_1^(p+1)))` (Volume 4, Example 2.3.5 of the handbook). -/
theorem inseparable_zChart (p : ℕ) (z x₁ y₁ : R) :
    z ^ p - (z * x₁) ^ (p + 1) - (z * y₁) ^ (p + 1) =
      z ^ p * (1 - z * (x₁ ^ (p + 1) + y₁ ^ (p + 1))) := by
  ring

end Charts

section Roots

variable {R : Type*} [CommRing R] (p : ℕ) [CharP R p]

/-- In characteristic `p`, the derivative of `h = 1 + Y^(p+1)` is `Y^p` (Volume 4, Example 2.3.5 of the handbook). -/
theorem derivative_one_add_X_pow_succ : derivative (1 + X ^ (p + 1) : R[X]) = X ^ p := by
  have hp : ((p + 1 : ℕ) : R) = 1 := by
    rw [Nat.cast_succ, CharP.cast_eq_zero, zero_add]
  rw [derivative_add, derivative_one, zero_add, derivative_X_pow, hp, map_one, one_mul,
    Nat.add_sub_cancel]

/-- In characteristic `p`, the polynomial `h = 1 + Y^(p+1)` is separable (Volume 4, Example 2.3.5 of the handbook). -/
theorem separable_one_add_X_pow_succ : (1 + X ^ (p + 1) : R[X]).Separable := by
  rw [separable_def, derivative_one_add_X_pow_succ p]
  exact ⟨1, -X, by ring⟩

/-- Over an algebraically closed field of characteristic `p`, the polynomial `h = 1 + Y^(p+1)` has exactly `p + 1` distinct roots (Volume 4, Example 2.3.5 of the handbook). -/
theorem card_roots_one_add_X_pow_succ {k : Type*} [Field k] [DecidableEq k] [IsAlgClosed k]
    [CharP k p] :
    (1 + X ^ (p + 1) : k[X]).roots.toFinset.card = p + 1 := by
  have h : (1 + X ^ (p + 1) : k[X]) = X ^ (p + 1) + C 1 := by
    rw [C_1]
    ring
  rw [Multiset.toFinset_card_of_nodup (nodup_roots (separable_one_add_X_pow_succ (R := k) p)),
    IsAlgClosed.card_roots_eq_natDegree, h, natDegree_X_pow_add_C]

end Roots

end Singularity
