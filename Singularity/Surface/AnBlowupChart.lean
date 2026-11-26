/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Tactic.Ring

/-!
# The three charts of the blowup of `xy = z^n`

Let `F = xy - z^n` with `n ≥ 2`, and let `X'` be the blowup of `X_n = V(F)` at the origin. Volume 4, Proposition 2.3.2, part 2 of the handbook computes the three charts of `X'` with Lemma 1.1.6. This file proves the algebraic part of this computation.

* `Singularity.an_xChart`, `Singularity.an_yChart` and `Singularity.an_zChart`: the substitutions of the three charts. In the `x`-chart, `F(x, x y_1, x z_1) = x^2 (y_1 - x^(n-2) z_1^n)`. In the `y`-chart, `F(y x_1, y, y z_1) = y^2 (x_1 - y^(n-2) z_1^n)`. In the `z`-chart, `F(z x_1, z y_1, z) = z^2 (x_1 y_1 - z^(n-2))`, which is the equation of `X_{n-2}` for `n ≥ 3`.
* `Singularity.an_not_X_dvd_xChart`: in `k[x, y_1, z_1]`, the variable `x` does not divide `y_1 - x^(n-2) z_1^n`. So the strict transform in the `x`-chart is `V(y_1 - x^(n-2) z_1^n)`, as in Lemma 1.1.6.
* `Singularity.anXChartEquiv`: the strict transform in the `x`-chart is isomorphic to `A^2`. Its ring is `k[x, z_1][y_1]/(y_1 - x^(n-2) z_1^n)`, and it is isomorphic to `k[x, z_1]`. This is the isomorphism of Mathlib for the quotient by `Y - c`.

The identities hold in each commutative ring. The file does not prove parts 1, 3 and 4 of the proposition.
-/

open MvPolynomial

namespace Singularity

section Identities

variable {R : Type*} [CommRing R]

/-- The `x`-chart of the blowup of `xy = z^n` at the origin: `y = x y_1` and `z = x z_1` give `F = x^2 (y_1 - x^(n-2) z_1^n)` (Volume 4, Proposition 2.3.2, part 2 of the handbook). -/
theorem an_xChart {n : ℕ} (hn : 2 ≤ n) (x y₁ z₁ : R) :
    x * (x * y₁) - (x * z₁) ^ n = x ^ 2 * (y₁ - x ^ (n - 2) * z₁ ^ n) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  rw [Nat.add_sub_cancel]
  ring

/-- The `y`-chart of the blowup of `xy = z^n` at the origin: `x = y x_1` and `z = y z_1` give `F = y^2 (x_1 - y^(n-2) z_1^n)` (Volume 4, Proposition 2.3.2, part 2 of the handbook). -/
theorem an_yChart {n : ℕ} (hn : 2 ≤ n) (y x₁ z₁ : R) :
    (y * x₁) * y - (y * z₁) ^ n = y ^ 2 * (x₁ - y ^ (n - 2) * z₁ ^ n) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  rw [Nat.add_sub_cancel]
  ring

/-- The `z`-chart of the blowup of `xy = z^n` at the origin: `x = z x_1` and `y = z y_1` give `F = z^2 (x_1 y_1 - z^(n-2))`. For `n ≥ 3` the second factor is the equation of `X_{n-2}` (Volume 4, Proposition 2.3.2, part 2 of the handbook). -/
theorem an_zChart {n : ℕ} (hn : 2 ≤ n) (z x₁ y₁ : R) :
    (z * x₁) * (z * y₁) - z ^ n = z ^ 2 * (x₁ * y₁ - z ^ (n - 2)) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  rw [Nat.add_sub_cancel]
  ring

end Identities

section Strict

variable {k : Type*} [CommRing k]

/-- In `k[x, y_1, z_1]`, with `x, y_1, z_1` the variables `X 0, X 1, X 2`, the variable `x` does not divide `y_1 - x^(n-2) z_1^n` when `n ≥ 2`. Thus the strict transform of `X_n` in the `x`-chart is `V(y_1 - x^(n-2) z_1^n)` (Volume 4, Proposition 2.3.2, part 2 of the handbook). -/
theorem an_not_X_dvd_xChart [Nontrivial k] {n : ℕ} (hn : 2 ≤ n) :
    ¬ (X 0 : MvPolynomial (Fin 3) k) ∣ X 1 - X 0 ^ (n - 2) * X 2 ^ n := by
  rintro ⟨c, hc⟩
  have h := congrArg (MvPolynomial.eval ![(0 : k), 1, 0]) hc
  have hn0 : n ≠ 0 := by omega
  simp [zero_pow hn0] at h

variable (k)

/-- The strict transform of `X_n` in the `x`-chart is isomorphic to `A^2` with the coordinates `x, z_1` (Volume 4, Proposition 2.3.2, part 2 of the handbook). The ring of the chart is `k[x, z_1][y_1]`, with `x, z_1` the variables `X 0, X 1` of `k[x, z_1]` and `y_1` the variable of the polynomial ring over it. -/
noncomputable def anXChartEquiv (n : ℕ) :
    (Polynomial (MvPolynomial (Fin 2) k) ⧸
        Ideal.span {Polynomial.X - Polynomial.C (X 0 ^ (n - 2) * X 1 ^ n :
          MvPolynomial (Fin 2) k)}) ≃ₐ[MvPolynomial (Fin 2) k] MvPolynomial (Fin 2) k :=
  Polynomial.quotientSpanXSubCAlgEquiv _

end Strict

end Singularity
