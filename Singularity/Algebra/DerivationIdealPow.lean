/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# A derivation lowers the power of an ideal by one

Let `B` be a commutative ring, let `D` be a derivation of `B`, and let `I` be an ideal of `B`. This file proves that `D(I^e) ⊆ I^(e-1)` for each `e` (Volume 6, Lemma 1.2.4 of the handbook).

The handbook takes an additive map `D : B → B` with `D(ab) = a D(b) + b D(a)`. Such a map is a derivation over `ℤ`, so the second theorem below is the statement of the handbook. The first theorem is for a derivation over each commutative ring `R`. The handbook asks `e ≥ 1`. The statement here holds also for `e = 0`, because `0 - 1 = 0` in `ℕ` and `I^0` is the full ring.

The proof is by induction on `e`, as in the handbook. The ideal `I^(e+2)` is `I^(e+1) * I`. For `a ∈ I^(e+1)` and `b ∈ I`, the Leibniz rule gives `D(ab) = a D(b) + b D(a)`. The first term is in `I^(e+1)` because `a` is. The second term is in `I * I^e = I^(e+1)` by the induction hypothesis.

## Main results

* `Singularity.derivation_mem_pow_pred`: `D x ∈ I^(e-1)` for each `x ∈ I^e`, for a derivation `D` over `R`.
* `Singularity.addMonoidHom_mem_pow_pred`: the same statement for an additive map with the Leibniz rule (the form of the handbook).
-/

namespace Singularity

variable {R B : Type*} [CommSemiring R] [CommRing B] [Algebra R B]

/-- A derivation maps `I^(e+1)` into `I^e`. This is Volume 6, Lemma 1.2.4 of the handbook, with `e + 1` in place of `e`. -/
theorem derivation_mem_pow_succ (D : Derivation R B B) (I : Ideal B) :
    ∀ e : ℕ, ∀ x ∈ I ^ (e + 1), D x ∈ I ^ e
  | 0 => fun _ _ => by simp
  | e + 1 => by
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine add_mem (Ideal.mul_mem_right _ _ ha) ?_
      rw [pow_succ']
      exact Ideal.mul_mem_mul hb (derivation_mem_pow_succ D I e a ha)
    · intro y z hy hz
      rw [map_add]
      exact add_mem hy hz

/-- Volume 6, Lemma 1.2.4 of the handbook, for a derivation over a commutative ring `R`: let `I` be an ideal of `B`. Then `D(I^e) ⊆ I^(e-1)`. -/
theorem derivation_mem_pow_pred (D : Derivation R B B) (I : Ideal B) (e : ℕ) :
    ∀ x ∈ I ^ e, D x ∈ I ^ (e - 1) := by
  intro x hx
  cases e with
  | zero => simp
  | succ e => simpa using derivation_mem_pow_succ D I e x hx

/-- Volume 6, Lemma 1.2.4 of the handbook, in the form of the handbook: let `D : B → B` be an additive map with `D(ab) = a D(b) + b D(a)`, and let `I` be an ideal of `B`. Then `D(I^e) ⊆ I^(e-1)`. -/
theorem addMonoidHom_mem_pow_pred (D : B →+ B) (hD : ∀ a b, D (a * b) = a * D b + b * D a)
    (I : Ideal B) (e : ℕ) : ∀ x ∈ I ^ e, D x ∈ I ^ (e - 1) :=
  derivation_mem_pow_pred (Derivation.mk' D.toIntLinearMap hD) I e

end Singularity
