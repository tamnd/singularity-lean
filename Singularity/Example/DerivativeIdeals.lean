/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.DerivativeOrder

/-!
# Derivative ideals and coefficient ideals in examples

This file checks the computations of three examples of Volume 2 of the handbook. The derivative ideal is `Singularity.derivIdeal`.

1. Example 2.3.4. Let `I = (xy - z^n)` on the affine space of dimension 3, with `n ≥ 2` and `n ≠ 0` in `k`. Then `D(I) = (x, y, z^(n-1))` (`derivIdeal_xy_sub_z_pow`).
2. Examples 2.3.4 and 3.2.8. On `H = (x = 0)` with the coordinates `y, z`, the ideal `(z^n) + (y, z^(n-1))^2` is `(y^2, y z^(n-1), z^n)` (`coeffIdeal_H`). On `H' = (x = y)`, the ideal `(y^2 - z^n) + (y, z^(n-1))^2` is the same ideal (`coeffIdeal_H'`). The two hypersurfaces of maximal contact give the same coefficient ideal. These two statements hold over each commutative ring.
3. Example 2.4.2. Let `k` have characteristic `p` and let `f = x^p + y^(p+1)`. Then `∂f/∂x = 0`, `∂f/∂y = y^p` (`pderiv_charPExample`), the order of `f` at the origin is `p` (`ord_charPExample`), `D(f) = (x^p, y^p)` (`derivIdeal_charPExample`), and each `D^j(f)` has order at least `p` at the origin (`le_idealOrd_derivIdeal_iterate_charPExample`). So no `D^j(f)` has an element of order `1`.

The coordinates are `x = X 0`, `y = X 1`, `z = X 2` in three variables, and `y = X 0`, `z = X 1` on the hypersurfaces in two variables. In Example 2.4.2 the coordinates are `x = X 0` and `y = X 1`.
-/

open MvPolynomial

namespace Singularity

namespace DerivativeIdeals

section Example234

variable {k : Type*} [Field k]

/-- **Volume 2, Example 2.3.4 of the handbook**, the derivative ideal. Let `n ≥ 1` with `n ≠ 0` in `k`, and let `I = (xy - z^n)`. Then `D(I) = (x, y, z^(n-1))`. The handbook asks `n ≥ 2`. -/
theorem derivIdeal_xy_sub_z_pow {n : ℕ} (hn : 1 ≤ n) (hnk : (n : k) ≠ 0) :
    derivIdeal (Ideal.span {X 0 * X 1 - X 2 ^ n} : Ideal (MvPolynomial (Fin 3) k)) =
      Ideal.span {X 0, X 1, X 2 ^ (n - 1)} := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  set f : MvPolynomial (Fin 3) k := X 0 * X 1 - X 2 ^ (m + 1) with hf
  have e0 : pderiv 0 f = X 1 := by
    rw [hf, map_sub, pderiv_mul, pderiv_pow, pderiv_X_self,
      pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 0), pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 0)]
    ring
  have e1 : pderiv 1 f = X 0 := by
    rw [hf, map_sub, pderiv_mul, pderiv_pow, pderiv_X_self,
      pderiv_X_of_ne (by decide : (0 : Fin 3) ≠ 1), pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 1)]
    ring
  have e2 : pderiv 2 f = -(C ((m + 1 : ℕ) : k) * X 2 ^ m) := by
    rw [hf, map_sub, pderiv_mul, pderiv_pow, pderiv_X_self,
      pderiv_X_of_ne (by decide : (0 : Fin 3) ≠ 2), pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 2),
      map_natCast, Nat.add_sub_cancel]
    ring
  have hx : (X 0 : MvPolynomial (Fin 3) k) ∈ Ideal.span {X 0, X 1, X 2 ^ m} :=
    Ideal.subset_span (by simp)
  have hy : (X 1 : MvPolynomial (Fin 3) k) ∈ Ideal.span {X 0, X 1, X 2 ^ m} :=
    Ideal.subset_span (by simp)
  have hz : (X 2 ^ m : MvPolynomial (Fin 3) k) ∈ Ideal.span {X 0, X 1, X 2 ^ m} :=
    Ideal.subset_span (by simp)
  apply le_antisymm
  · rw [derivIdeal_span, Ideal.span_le]
    have hfmem : f ∈ Ideal.span {X 0, X 1, X 2 ^ m} := by
      rw [hf, pow_succ']
      exact sub_mem (Ideal.mul_mem_right _ _ hx) (Ideal.mul_mem_left _ _ hz)
    rintro g (hg | ⟨i, f', hf', rfl⟩)
    · rw [Set.mem_singleton_iff.mp hg]
      exact hfmem
    · rw [Set.mem_singleton_iff.mp hf']
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
      rcases hi with rfl | rfl | rfl
      · rw [e0]
        exact hy
      · rw [e1]
        exact hx
      · rw [e2]
        exact neg_mem (Ideal.mul_mem_left _ _ hz)
  · have hf0 : f ∈ Ideal.span {f} := Ideal.mem_span_singleton_self f
    rw [Ideal.span_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · have h := pderiv_mem_derivIdeal hf0 1
      rwa [e1] at h
    · have h := pderiv_mem_derivIdeal hf0 0
      rwa [e0] at h
    · have hmk : ((m + 1 : ℕ) : k) ≠ 0 := hnk
      have : (X 2 ^ m : MvPolynomial (Fin 3) k) = C (((m + 1 : ℕ) : k)⁻¹) * -pderiv 2 f := by
        rw [e2, neg_neg, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hmk, C_1, one_mul]
      rw [this]
      exact Ideal.mul_mem_left _ _ (neg_mem (pderiv_mem_derivIdeal hf0 2))

end Example234

section CoefficientIdeal

variable {R : Type*} [CommRing R]

/-- The square of `(y, z^(n-1))` lies in `(y^2, y z^(n-1), z^n)` if `n ≥ 2`. -/
theorem span_pair_sq_le {n : ℕ} (hn : 2 ≤ n) :
    (Ideal.span {X 0, X 1 ^ (n - 1)} : Ideal (MvPolynomial (Fin 2) R)) ^ 2 ≤
      Ideal.span {X 0 ^ 2, X 0 * X 1 ^ (n - 1), X 1 ^ n} := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hsub : m + 2 - 1 = m + 1 := by omega
  rw [hsub, sq, Ideal.mul_le]
  intro r hr s hs
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hr
  obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.mp hs
  have e : (a * X 0 + b * X 1 ^ (m + 1)) * (c * X 0 + d * X 1 ^ (m + 1)) =
      (a * c) * X 0 ^ 2 + (a * d + b * c) * (X 0 * X 1 ^ (m + 1)) +
        (b * d * X 1 ^ m) * X 1 ^ (m + 2) := by ring
  rw [e]
  refine add_mem (add_mem (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_))
    (Ideal.mul_mem_left _ _ ?_) <;> exact Ideal.subset_span (by simp)

/-- The elements `y^2` and `y z^(n-1)` lie in the square of `(y, z^(n-1))`. -/
theorem le_span_pair_sq {n : ℕ} :
    (X 0 ^ 2 : MvPolynomial (Fin 2) R) ∈ Ideal.span {X 0, X 1 ^ (n - 1)} ^ 2 ∧
      (X 0 * X 1 ^ (n - 1) : MvPolynomial (Fin 2) R) ∈ Ideal.span {X 0, X 1 ^ (n - 1)} ^ 2 := by
  rw [sq, sq]
  exact ⟨Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)),
    Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))⟩

/-- **Volume 2, Examples 2.3.4 and 3.2.8 of the handbook**, on `H = (x = 0)`. Let `n ≥ 2`. In the coordinates `y, z` of `H`, the ideal `I|_H + (D(I)|_H)^2 = (z^n) + (y, z^(n-1))^2` is `(y^2, y z^(n-1), z^n)`. -/
theorem coeffIdeal_H {n : ℕ} (hn : 2 ≤ n) :
    (Ideal.span {X 1 ^ n} ⊔ Ideal.span {X 0, X 1 ^ (n - 1)} ^ 2 :
        Ideal (MvPolynomial (Fin 2) R)) =
      Ideal.span {X 0 ^ 2, X 0 * X 1 ^ (n - 1), X 1 ^ n} := by
  apply le_antisymm
  · refine sup_le ?_ (span_pair_sq_le hn)
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span (by simp)
  · rw [Ideal.span_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact Ideal.mem_sup_right le_span_pair_sq.1
    · exact Ideal.mem_sup_right le_span_pair_sq.2
    · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)

/-- **Volume 2, Example 3.2.8 of the handbook**, on `H' = (x = y)`. Let `n ≥ 2`. In the coordinates `y, z` of `H'`, the ideal `I|_H' + (D(I)|_H')^2 = (y^2 - z^n) + (y, z^(n-1))^2` is `(y^2, y z^(n-1), z^n)`. So it is the ideal of `coeffIdeal_H`. -/
theorem coeffIdeal_H' {n : ℕ} (hn : 2 ≤ n) :
    (Ideal.span {X 0 ^ 2 - X 1 ^ n} ⊔ Ideal.span {X 0, X 1 ^ (n - 1)} ^ 2 :
        Ideal (MvPolynomial (Fin 2) R)) =
      Ideal.span {X 0 ^ 2, X 0 * X 1 ^ (n - 1), X 1 ^ n} := by
  apply le_antisymm
  · refine sup_le ?_ (span_pair_sq_le hn)
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact sub_mem (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
  · rw [Ideal.span_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact Ideal.mem_sup_right le_span_pair_sq.1
    · exact Ideal.mem_sup_right le_span_pair_sq.2
    · have h := sub_mem (Ideal.mem_sup_right (S := Ideal.span {X 0 ^ 2 - X 1 ^ n})
        (le_span_pair_sq (n := n) (R := R)).1)
        (Ideal.mem_sup_left (T := Ideal.span {X 0, X 1 ^ (n - 1)} ^ 2)
          (Ideal.mem_span_singleton_self (X 0 ^ 2 - X 1 ^ n)))
      rwa [sub_sub_cancel] at h

end CoefficientIdeal

section Example242

variable {k : Type*} [Field k] (p : ℕ)

/-- The polynomial `x^p + y^(p+1)` of Volume 2, Example 2.4.2 of the handbook. -/
noncomputable def charPExample : MvPolynomial (Fin 2) k := X 0 ^ p + X 1 ^ (p + 1)

/-- **Volume 2, Example 2.4.2 of the handbook**, the order. The polynomial `f = x^p + y^(p+1)` has order `p` at the origin. -/
theorem ord_charPExample : ord (charPExample (k := k) p) = p := by
  rw [charPExample, ord_add_of_lt, ord_X_pow]
  rw [ord_X_pow, ord_X_pow]
  exact_mod_cast Nat.lt_succ_self p

variable [CharP k p]

theorem natCast_eq_zero_charP : (p : MvPolynomial (Fin 2) k) = 0 := by
  rw [← map_natCast (C : k →+* MvPolynomial (Fin 2) k), CharP.cast_eq_zero, map_zero]

theorem pderiv_X_pow_charP (i j : Fin 2) : pderiv i (X j ^ p : MvPolynomial (Fin 2) k) = 0 := by
  rw [pderiv_pow, natCast_eq_zero_charP, zero_mul, zero_mul]

/-- **Volume 2, Example 2.4.2 of the handbook**, the derivatives. In characteristic `p`, the polynomial `f = x^p + y^(p+1)` has `∂f/∂x = 0` and `∂f/∂y = y^p`. -/
theorem pderiv_charPExample :
    pderiv 0 (charPExample (k := k) p) = 0 ∧ pderiv 1 (charPExample (k := k) p) = X 1 ^ p := by
  refine ⟨?_, ?_⟩
  · rw [charPExample, map_add, pderiv_X_pow_charP p 0 0, pderiv_pow,
      pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0), mul_zero, zero_add]
  · rw [charPExample, map_add, pderiv_X_pow_charP p 1 0, pderiv_pow, pderiv_X_self, Nat.cast_succ,
      natCast_eq_zero_charP p, Nat.add_sub_cancel]
    ring


/-- The ideal `(x^p, y^p)` is stable under the derivative ideal in characteristic `p`. -/
theorem derivIdeal_span_pow_le :
    derivIdeal (Ideal.span {X 0 ^ p, X 1 ^ p} : Ideal (MvPolynomial (Fin 2) k)) ≤
      Ideal.span {X 0 ^ p, X 1 ^ p} := by
  rw [derivIdeal_span, Ideal.span_le]
  rintro g (hg | ⟨i, f, hf, rfl⟩)
  · exact Ideal.subset_span hg
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl <;> rw [pderiv_X_pow_charP (k := k) p] <;> exact zero_mem _

omit [CharP k p] in
theorem charPExample_mem : charPExample (k := k) p ∈ Ideal.span {X 0 ^ p, X 1 ^ p} := by
  rw [charPExample, pow_succ]
  exact add_mem (Ideal.subset_span (by simp)) (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

/-- **Volume 2, Example 2.4.2 of the handbook**, the derivative ideal. In characteristic `p`, `D(f) = (x^p, y^p)` for `f = x^p + y^(p+1)`. -/
theorem derivIdeal_charPExample :
    derivIdeal (Ideal.span {charPExample (k := k) p}) = Ideal.span {X 0 ^ p, X 1 ^ p} := by
  apply le_antisymm
  · refine (derivIdeal_mono ?_).trans (derivIdeal_span_pow_le p)
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact charPExample_mem p
  · have hf0 := Ideal.mem_span_singleton_self (charPExample (k := k) p)
    have hy : (X 1 ^ p : MvPolynomial (Fin 2) k) ∈ derivIdeal (Ideal.span {charPExample p}) :=
      (pderiv_charPExample p).2 ▸ pderiv_mem_derivIdeal hf0 1
    rw [Ideal.span_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · have e : (X 0 ^ p : MvPolynomial (Fin 2) k) = charPExample p - X 1 * X 1 ^ p := by
        rw [charPExample]
        ring
      rw [e]
      exact sub_mem (le_derivIdeal _ hf0) (Ideal.mul_mem_left _ _ hy)
    · exact hy

/-- **Volume 2, Example 2.4.2 of the handbook**, the orders. In characteristic `p`, each element of `D^j(f)` has order at least `p` at the origin, for each `j`. -/
theorem le_idealOrd_derivIdeal_iterate_charPExample (j : ℕ) :
    (p : ℕ∞) ≤ idealOrd (derivIdeal^[j] (Ideal.span {charPExample (k := k) p})) := by
  have hle : derivIdeal^[j] (Ideal.span {charPExample (k := k) p}) ≤
      Ideal.span {X 0 ^ p, X 1 ^ p} := by
    induction j with
    | zero =>
      rw [Function.iterate_zero, id, Ideal.span_le, Set.singleton_subset_iff]
      exact charPExample_mem p
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (derivIdeal_mono ih).trans (derivIdeal_span_pow_le p)
  refine le_idealOrd_iff.mpr (hle.trans ?_)
  rw [Ideal.span_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl <;> exact le_ord_iff_mem_pow.mp (ord_X_pow _ _).ge

end Example242

end DerivativeIdeals

end Singularity
