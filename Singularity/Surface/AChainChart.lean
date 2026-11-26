/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Ring

/-!
# The charts of the resolution of the singularity `A_{m-1}`

Let `X_m = V(xy - z^m)`. Volume 4, Proposition 2.3.10, part 1 of the handbook covers the resolution of `X_m` with `m` charts `U_i = Spec k[s_i, t_i]`, for `0 ≤ i ≤ m - 1`. On `U_i` the map to `X_m` is

`x = s_i^(m-i) t_i^(m-1-i)`, `y = s_i^i t_i^(i+1)`, `z = s_i t_i`.

This file proves the algebraic identities of part 1.

* `Singularity.aChain_chart_mul`: the formulas of `U_i` satisfy `xy = z^m`.
* `Singularity.aChainChart` and `Singularity.aChainChart_equation`: the map of `k`-algebras `k[x, y, z] → k[s, t]` of the chart `U_i` sends `xy - z^m` to `0`. `Singularity.aChainChartQuot` is the induced map from `k[x, y, z]/(xy - z^m)`.
* `Singularity.aChain_chart_s_mul` and `Singularity.aChain_chart_t_mul`: `s_i y = z^(i+1)` and `t_i z^i = y`. These are the equations `s_i = z^(i+1)/y` and `t_i = y/z^i` without the division.
* `Singularity.aChain_glue_x`, `Singularity.aChain_glue_y` and `Singularity.aChain_glue_z`: the gluing. Let `1 ≤ i ≤ m - 1`, let `t_i` be a unit with inverse `u`, and put `s_{i-1} = u` and `t_{i-1} = s_i t_i^2`. Then the formulas of `U_{i-1}` give the same `x`, `y` and `z` as the formulas of `U_i`.

The identities hold in each commutative ring. The file does not prove that the charts cover the resolution, and it does not prove parts 2 to 5.
-/

open MvPolynomial

namespace Singularity

section Identities

variable {R : Type*} [CommRing R]

/-- The chart `U_i` of the resolution of `xy = z^m` satisfies `xy = z^m` (Volume 4, Proposition 2.3.10, part 1 of the handbook). -/
theorem aChain_chart_mul {m i : ℕ} (hi : i < m) (s t : R) :
    (s ^ (m - i) * t ^ (m - 1 - i)) * (s ^ i * t ^ (i + 1)) = (s * t) ^ m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = i + 1 + n := ⟨m - i - 1, by omega⟩
  have h1 : i + 1 + n - i = n + 1 := by omega
  have h2 : i + 1 + n - 1 - i = n := by omega
  rw [h1, h2]
  ring

/-- On the chart `U_i`, `s_i y = z^(i+1)`. This is `s_i = z^(i+1)/y` (Volume 4, Proposition 2.3.10, part 1 of the handbook). -/
theorem aChain_chart_s_mul (i : ℕ) (s t : R) :
    s * (s ^ i * t ^ (i + 1)) = (s * t) ^ (i + 1) := by
  ring

/-- On the chart `U_i`, `t_i z^i = y`. This is `t_i = y/z^i` (Volume 4, Proposition 2.3.10, part 1 of the handbook). -/
theorem aChain_chart_t_mul (i : ℕ) (s t : R) :
    t * (s * t) ^ i = s ^ i * t ^ (i + 1) := by
  ring

/-- The gluing of `U_{i-1}` and `U_i` for `x`. If `u t = 1`, then `s_{i-1} = u` and `t_{i-1} = s t^2` give the same `x` (Volume 4, Proposition 2.3.10, part 1 of the handbook). -/
theorem aChain_glue_x {m i : ℕ} (hi1 : 1 ≤ i) (hi : i < m) {s t u : R} (hu : u * t = 1) :
    u ^ (m - (i - 1)) * (s * t ^ 2) ^ (m - 1 - (i - 1)) = s ^ (m - i) * t ^ (m - 1 - i) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = i + 1 + n := ⟨m - i - 1, by omega⟩
  have h1 : i + 1 + n - (i - 1) = n + 2 := by omega
  have h2 : i + 1 + n - 1 - (i - 1) = n + 1 := by omega
  have h3 : i + 1 + n - i = n + 1 := by omega
  have h4 : i + 1 + n - 1 - i = n := by omega
  rw [h1, h2, h3, h4]
  calc u ^ (n + 2) * (s * t ^ 2) ^ (n + 1) = s ^ (n + 1) * t ^ n * (u * t) ^ (n + 2) := by ring
    _ = s ^ (n + 1) * t ^ n := by rw [hu, one_pow, mul_one]

/-- The gluing of `U_{i-1}` and `U_i` for `y` (Volume 4, Proposition 2.3.10, part 1 of the handbook). -/
theorem aChain_glue_y {i : ℕ} (hi1 : 1 ≤ i) {s t u : R} (hu : u * t = 1) :
    u ^ (i - 1) * (s * t ^ 2) ^ (i - 1 + 1) = s ^ i * t ^ (i + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  calc u ^ j * (s * t ^ 2) ^ (j + 1) = s ^ (j + 1) * t ^ (j + 1 + 1) * (u * t) ^ j := by ring
    _ = s ^ (j + 1) * t ^ (j + 1 + 1) := by rw [hu, one_pow, mul_one]

/-- The gluing of `U_{i-1}` and `U_i` for `z` (Volume 4, Proposition 2.3.10, part 1 of the handbook). -/
theorem aChain_glue_z {s t u : R} (hu : u * t = 1) : u * (s * t ^ 2) = s * t := by
  calc u * (s * t ^ 2) = s * t * (u * t) := by ring
    _ = s * t := by rw [hu, mul_one]

end Identities

section Chart

variable (k : Type*) [CommRing k]

/-- The map of `k`-algebras `k[x, y, z] → k[s, t]` of the chart `U_i` of the resolution of `xy = z^m`. The variables `x, y, z` are `X 0, X 1, X 2`, and `s, t` are `X 0, X 1`. -/
noncomputable def aChainChart (m i : ℕ) : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 2) k :=
  aeval ![X 0 ^ (m - i) * X 1 ^ (m - 1 - i), X 0 ^ i * X 1 ^ (i + 1), X 0 * X 1]

variable {k}

/-- The map of the chart `U_i` sends `xy - z^m` to `0` (Volume 4, Proposition 2.3.10, part 1 of the handbook). -/
theorem aChainChart_equation {m i : ℕ} (hi : i < m) :
    aChainChart k m i (X 0 * X 1 - X 2 ^ m) = 0 := by
  have h := aChain_chart_mul (R := MvPolynomial (Fin 2) k) hi (X 0) (X 1)
  rw [map_sub, map_mul, map_pow, sub_eq_zero]
  simpa [aChainChart] using h

variable (k)

/-- The map `k[x, y, z]/(xy - z^m) → k[s, t]` of the chart `U_i`, for `i < m`. It is the morphism `U_i → X_m` of Volume 4, Proposition 2.3.10, part 1 of the handbook. -/
noncomputable def aChainChartQuot {m i : ℕ} (hi : i < m) :
    (MvPolynomial (Fin 3) k ⧸ Ideal.span {(X 0 * X 1 - X 2 ^ m : MvPolynomial (Fin 3) k)}) →ₐ[k]
      MvPolynomial (Fin 2) k :=
  Ideal.Quotient.liftₐ _ (aChainChart k m i) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, aChainChart_equation hi, mul_zero]

end Chart

end Singularity
