/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Degree

/-!
# Perfect and imperfect fields

This file proves Volume 1, Example 6.1.4 of the handbook. A field `K` of characteristic `p` is perfect when its Frobenius `a ↦ a^p` is bijective (`PerfectRing K p` in Mathlib).

* `Singularity.Example.perfectRing_of_finite`: a finite field is perfect.
* `Singularity.Example.perfectRing_of_isAlgClosed`: an algebraically closed field is perfect.
* `Singularity.Example.not_perfectRing_ratFunc`: the field `𝔽_p(t)` is not perfect. More generally, for each field `F` of characteristic `p`, the variable `t` is not a `p`-th power in `F(t)` (`X_ne_pow`).

The proof of the last claim is the proof of the handbook. The degree of `t` is `1`, and the degree of a `p`-th power is a multiple of `p`.
-/

namespace Singularity.Example

/-- A finite field is perfect (Volume 1, Example 6.1.4 of the handbook). -/
theorem perfectRing_of_finite (K : Type*) [Field K] [Finite K] (p : ℕ) [ExpChar K p] :
    PerfectRing K p :=
  inferInstance

/-- An algebraically closed field is perfect (Volume 1, Example 6.1.4 of the handbook). -/
theorem perfectRing_of_isAlgClosed (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [ExpChar K p] :
    PerfectRing K p :=
  inferInstance

/-- Let `F` be a field and let `p ≥ 2`. Then the variable `t` of `F(t)` is not a `p`-th power. -/
theorem X_ne_pow {F : Type*} [Field F] {p : ℕ} (hp : 2 ≤ p) (f : RatFunc F) :
    f ^ p ≠ RatFunc.X := by
  intro h
  have hf : f ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at h
    exact RatFunc.X_ne_zero h.symm
  have hdeg : ∀ n : ℕ, (f ^ n).intDegree = n * f.intDegree := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n hf) hf, ih]
      push_cast
      ring
  have h1 := hdeg p
  rw [h, RatFunc.intDegree_X] at h1
  have hdvd : (p : ℤ) ∣ 1 := ⟨f.intDegree, h1⟩
  have := Int.eq_one_of_dvd_one (by positivity) hdvd
  omega

/-- The field `𝔽_p(t)` is not perfect (Volume 1, Example 6.1.4 of the handbook): the variable `t` is not a `p`-th power. -/
theorem not_perfectRing_ratFunc (p : ℕ) [Fact p.Prime] : ¬ PerfectRing (RatFunc (ZMod p)) p := by
  intro h
  obtain ⟨f, hf⟩ := h.bijective_frobenius.2 RatFunc.X
  exact X_ne_pow (Fact.out : p.Prime).two_le f hf

end Singularity.Example
