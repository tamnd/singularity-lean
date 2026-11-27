/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Henselian

/-!
# The lemma of Hensel for a complete local ring

This file proves Volume 1, Lemma 4.4.3 of the handbook. Let `(R, m)` be a local ring that is complete for the `m`-adic topology, let `g ∈ R[T]` and let `a₀ ∈ R`. If `g(a₀) ∈ m` and `g'(a₀)` is a unit, then there is exactly one `a ∈ R` with `g(a) = 0` and `a - a₀ ∈ m`.

The classes `HenselianRing` and `HenselianLocalRing` of Mathlib ask for a monic polynomial. The handbook asks for no condition on `g`. The proof of the instance `IsAdicComplete.henselianRing` of Mathlib does not use that `g` is monic, so `exists_root_of_isAdicComplete` repeats it without this hypothesis. This proof is due to Johan Commelin in Mathlib, `Mathlib/RingTheory/Henselian.lean`, under the Apache 2.0 licence. The uniqueness comes from `IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub` of Mathlib. The handbook also asks that `R` is Noetherian. The proof does not need this.

* `Singularity.Algebra.exists_root_of_isAdicComplete`: the existence, for an ideal `I` of a ring that is `I`-adically complete.
* `Singularity.Algebra.isUnit_derivative_eval_of_sub_mem`: `g'(b)` is a unit for each `b` with `b - a₀ ∈ m`.
* `Singularity.Algebra.existsUnique_root_of_isAdicComplete`: Lemma 4.4.3 of the handbook.
-/

open Polynomial IsLocalRing
open scoped Ring

namespace Singularity.Algebra

/-- The existence part of the lemma of Hensel, for each polynomial (Volume 1, Lemma 4.4.3 of the handbook). Let `R` be `I`-adically complete, let `f ∈ R[X]` and let `a₀ ∈ R` with `f(a₀) ∈ I` and `f'(a₀)` a unit. Then there is `a` with `f(a) = 0` and `a - a₀ ∈ I`. The proof is the proof of `IsAdicComplete.henselianRing` of Mathlib, by Johan Commelin, without the hypothesis that `f` is monic. -/
theorem exists_root_of_isAdicComplete {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
    classical
      let f' := derivative f
      let c : ℕ → R := fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * (f'.eval b)⁻¹ʳ
      have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * (f'.eval (c n))⁻¹ʳ := by
        intro n
        simp only [c]
      have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => ?_
        rw [hc, sub_eq_add_neg, ← add_zero a₀]
        refine ih.add ?_
        rw [SModEq.zero, Ideal.neg_mem_iff]
        refine I.mul_mem_right _ ?_
        rw [← SModEq.zero] at h₁ ⊢
        exact (ih.eval f).trans h₁
      have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
        intro n
        have := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
        apply IsUnit.of_map (Ideal.Quotient.mk I)
        convert h₂ using 1
        exact SModEq.def.mp ((hc_mod n).eval _)
      have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
        intro n
        induction n with
        | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using! h₁
        | succ n ih => ?_
        rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
          add_neg_cancel_comm]
        rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
          Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
        swap
        · intro i
          rw [zero_mul]
        refine Ideal.add_mem _ ?_ ?_
        · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
            taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
            mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_cancel]
          exact Ideal.zero_mem _
        · refine Submodule.sum_mem _ ?_
          simp only [Finset.mem_Ico]
          rintro i ⟨h2i, _⟩
          have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith only [h2i]
          refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
          rw [pow_mul']
          exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
      have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
        intro m n hmn
        rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
        clear hmn
        induction k with
        | zero => rw [add_zero]
        | succ k ih => ?_
        rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
        refine ih.add ?_
        symm
        rw [SModEq.zero, Ideal.neg_mem_iff]
        refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
        rw [add_assoc]
        exact le_self_add
      obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
      refine ⟨a, ?_, ?_⟩
      · show f.IsRoot a
        suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
        intro n
        specialize ha n
        rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
        refine (ha.symm.eval f).trans ?_
        rw [SModEq.zero]
        exact Ideal.pow_le_pow_right le_self_add (hfcI _)
      · show a - a₀ ∈ I
        specialize ha (0 + 1)
        rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
        rw [← SModEq.sub_mem, ← add_zero a₀]
        refine ha.symm.trans (SModEq.rfl.add ?_)
        rw [SModEq.zero, Ideal.neg_mem_iff]
        exact Ideal.mul_mem_right _ _ h₁

/-- Let `R` be a local ring, let `g ∈ R[X]` and let `a₀ ∈ R` with `g'(a₀)` a unit. Then `g'(b)` is a unit for each `b` with `b - a₀ ∈ m`. -/
theorem isUnit_derivative_eval_of_sub_mem {R : Type*} [CommRing R] [IsLocalRing R] (g : R[X])
    {a₀ b : R} (h : IsUnit (g.derivative.eval a₀)) (hb : b - a₀ ∈ maximalIdeal R) :
    IsUnit (g.derivative.eval b) := by
  by_contra hn
  have h1 : g.derivative.eval b ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hn
  have h2 : g.derivative.eval b - g.derivative.eval a₀ ∈ maximalIdeal R := by
    obtain ⟨c, hc⟩ := Polynomial.sub_dvd_eval_sub b a₀ g.derivative
    rw [hc]
    exact Ideal.mul_mem_right _ _ hb
  have h3 : g.derivative.eval a₀ ∈ maximalIdeal R := by
    have := Ideal.sub_mem _ h1 h2
    rwa [sub_sub_cancel] at this
  exact (mem_maximalIdeal _).mp h3 h

/-- The lemma of Hensel (Volume 1, Lemma 4.4.3 of the handbook). Let `(R, m)` be a local ring that is complete for the `m`-adic topology, let `g ∈ R[X]` and let `a₀ ∈ R`. If `g(a₀) ∈ m` and `g'(a₀)` is a unit, then there is exactly one `a ∈ R` with `g(a) = 0` and `a - a₀ ∈ m`. The handbook also asks that `R` is Noetherian, and the proof does not need this. -/
theorem existsUnique_root_of_isAdicComplete {R : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (g : R[X]) (a₀ : R) (h₁ : g.eval a₀ ∈ maximalIdeal R)
    (h₂ : IsUnit (g.derivative.eval a₀)) :
    ∃! a : R, g.eval a = 0 ∧ a - a₀ ∈ maximalIdeal R := by
  obtain ⟨a, ha, haa⟩ := exists_root_of_isAdicComplete (maximalIdeal R) g a₀ h₁
    (h₂.map (Ideal.Quotient.mk _))
  refine ⟨a, ⟨ha.eq_zero, haa⟩, fun b ⟨hb, hba⟩ => ?_⟩
  have hab : a - b ∈ maximalIdeal R := by
    have := Ideal.sub_mem _ haa hba
    rwa [sub_sub_sub_cancel_right] at this
  exact (IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub ha.eq_zero hb
    ((mem_maximalIdeal _).mp hab) (isUnit_derivative_eval_of_sub_mem g h₂ haa)).symm

end Singularity.Algebra
