/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.Order
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.CharP.Lemmas

/-!
# The equations `z^p + g`: derivative, translation and order

This file proves Volume 6, Lemma 2.3.2 of the handbook in part. It proves the algebraic core of
the lemma, for polynomials over a commutative ring `R` of prime characteristic `p`, in variables
indexed by a type `σ` with a distinguished variable `z : σ`. Let `h = z^p + G`, where `G` does not
involve `z`.

* `pderiv_X_pow_add_self`: `∂h/∂z = 0`.
* `pderiv_X_pow_add`: `∂h/∂x_i = ∂G/∂x_i` for each variable `x_i`.
* `shift_X_pow_add`: the translate of `h` by a point `a` is `z^p + (G(x + a) + a_z^p)`. This uses
  `(z + c)^p = z^p + c^p`.
* `notMem_vars_shift_add_C`: the second summand `G(x + a) + a_z^p` does not involve `z`.
* `ord_X_pow_add_of_notMem_vars`: the order of `z^p + G` is `min(p, ord G)`.
* `ord_shift_X_pow_add`, `ord_shift_X_pow_add_le`, `le_ord_shift_X_pow_add_iff`: the order of `h`
  at the point `a` is `min(p, ord (G(x + a) + a_z^p))`. So it is at most `p`, and it equals `p`
  if and only if `G(x + a) + a_z^p` has order at least `p`.

Not proved here: the identification of the order at a point with the multiplicity of the
hypersurface (Section 1.2), and the Jacobian criterion that gives the first claim of the lemma on
the singular locus. The file proves only the derivative identities that feed into that criterion.
-/

open MvPolynomial

namespace Singularity.PurelyInseparableEquation

variable {σ R : Type*} [CommRing R]

/-- The translation `x_i ↦ x_i + a_i`. It moves the point `a` to the origin. -/
noncomputable def shift (a : σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i => X i + C (a i)

theorem shift_X (a : σ → R) (i : σ) : shift a (X i) = X i + C (a i) := by
  simp [shift]

theorem shift_C (a : σ → R) (r : R) : shift a (C r) = C r := by
  simp [shift]

/-- A translation does not create new variables. -/
theorem vars_shift_subset [Nontrivial R] [DecidableEq σ] (a : σ → R) (f : MvPolynomial σ R) :
    (shift a f).vars ⊆ f.vars := by
  intro j hj
  have h1 := vars_bind₁ (fun i => X i + C (a i)) f
  rw [shift, aeval_eq_bind₁] at hj
  obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp (h1 hj)
  have h2 : (X i + C (a i) : MvPolynomial σ R).vars ⊆ {i} := by
    refine (vars_add_subset _ _).trans ?_
    rw [vars_C, Finset.union_empty]
    rw [vars_X]
  rw [Finset.mem_singleton.mp (h2 hji)]
  exact hi

/-- If `G` does not involve `z`, then neither does `G(x + a) + c`. -/
theorem notMem_vars_shift_add_C [Nontrivial R] {z : σ} {G : MvPolynomial σ R} (hG : z ∉ G.vars)
    (a : σ → R) (c : R) : z ∉ (shift a G + C c).vars := by
  classical
  intro h
  rcases Finset.mem_union.mp (vars_add_subset _ _ h) with h1 | h1
  · exact hG (vars_shift_subset a G h1)
  · simp [vars_C] at h1

section CharP

variable (p : ℕ) [Fact p.Prime] [CharP R p]

omit [Fact p.Prime] in
/-- In characteristic `p`, each partial derivative of `z^p` is `0`. -/
theorem pderiv_X_pow_char (i z : σ) : pderiv i (X z ^ p : MvPolynomial σ R) = 0 := by
  rw [Derivation.leibniz_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]

omit [Fact p.Prime] in
/-- The partial derivatives of `z^p + G` are those of `G`. -/
theorem pderiv_X_pow_add (i z : σ) (G : MvPolynomial σ R) :
    pderiv i (X z ^ p + G) = pderiv i G := by
  rw [map_add, pderiv_X_pow_char, zero_add]

omit [Fact p.Prime] in
/-- If `G` does not involve `z`, then `∂(z^p + G)/∂z = 0`. -/
theorem pderiv_X_pow_add_self {z : σ} {G : MvPolynomial σ R} (hG : z ∉ G.vars) :
    pderiv z (X z ^ p + G) = 0 := by
  rw [pderiv_X_pow_add, pderiv_eq_zero_of_notMem_vars hG]

/-- The translate of `z^p + G` by `a` is `z^p + (G(x + a) + a_z^p)`, since
`(z + a_z)^p = z^p + a_z^p` in characteristic `p`. -/
theorem shift_X_pow_add (a : σ → R) (z : σ) (G : MvPolynomial σ R) :
    shift a (X z ^ p + G) = X z ^ p + (shift a G + C (a z ^ p)) := by
  rw [map_add, map_pow, shift_X, add_pow_char, map_pow]
  ring

/-- If `G` does not involve `z` and `p ≠ 0`, the order of `z^p + G` is `min(p, ord G)`. -/
theorem ord_X_pow_add_of_notMem_vars' [Nontrivial R] {n : ℕ} (hn : n ≠ 0) {z : σ}
    {G : MvPolynomial σ R} (hG : z ∉ G.vars) : ord (X z ^ n + G) = min (n : ℕ∞) (ord G) := by
  have hX : ord (X z ^ n : MvPolynomial σ R) = n := ord_X_pow z n
  by_cases hne : ord (X z ^ n : MvPolynomial σ R) = ord G
  · rw [← hX, ← hne, min_self]
    refine le_antisymm ?_ (by simpa [hne] using min_ord_le_ord_add (X z ^ n) G)
    have hc : G.coeff (Finsupp.single z n) = 0 := by
      by_contra h
      apply hG
      rw [mem_vars_iff_mem_support]
      exact ⟨_, mem_support_iff.mpr h, by simp [hn]⟩
    have hc' : (X z ^ n + G).coeff (Finsupp.single z n) ≠ 0 := by
      classical
      have hadd : (X z ^ n + G).coeff (Finsupp.single z n) =
          (X z ^ n).coeff (Finsupp.single z n) + G.coeff (Finsupp.single z n) := rfl
      rw [hadd, hc, add_zero, coeff_X_pow]
      simp
    calc ord _ ≤ _ := ord_le hc'
      _ = ord (X z ^ n : MvPolynomial σ R) := by rw [hX, Finsupp.degree_single]
  · rw [ord_add_of_ord_ne hne, hX]

/-- In characteristic `p`, if `G` does not involve `z`, the order of `z^p + G` is
`min(p, ord G)`. -/
theorem ord_X_pow_add_of_notMem_vars {z : σ} {G : MvPolynomial σ R} (hG : z ∉ G.vars) :
    ord (X z ^ p + G) = min (p : ℕ∞) (ord G) :=
  haveI := CharP.nontrivial_of_char_ne_one (R := R) (Fact.out : p.Prime).ne_one
  ord_X_pow_add_of_notMem_vars' (Fact.out : p.Prime).ne_zero hG

/-- The order of `z^p + G` is at most `p`. -/
theorem ord_X_pow_add_le {z : σ} {G : MvPolynomial σ R} (hG : z ∉ G.vars) :
    ord (X z ^ p + G) ≤ p := by
  rw [ord_X_pow_add_of_notMem_vars p hG]
  exact min_le_left _ _

/-- The order of `z^p + G` is at least `p` if and only if the order of `G` is. -/
theorem le_ord_X_pow_add_iff {z : σ} {G : MvPolynomial σ R} (hG : z ∉ G.vars) :
    (p : ℕ∞) ≤ ord (X z ^ p + G) ↔ (p : ℕ∞) ≤ ord G := by
  rw [ord_X_pow_add_of_notMem_vars p hG, le_min_iff]
  exact and_iff_right le_rfl

/-- **Volume 6, Lemma 2.3.2, the order at a point.** Let `G` not involve `z`. The order of
`h = z^p + G` at the point `a` is `min(p, ord (G(x + a) + a_z^p))`. -/
theorem ord_shift_X_pow_add (a : σ → R) {z : σ} {G : MvPolynomial σ R} (hG : z ∉ G.vars) :
    ord (shift a (X z ^ p + G)) = min (p : ℕ∞) (ord (shift a G + C (a z ^ p))) := by
  have := CharP.nontrivial_of_char_ne_one (R := R) (Fact.out : p.Prime).ne_one
  rw [shift_X_pow_add, ord_X_pow_add_of_notMem_vars p (notMem_vars_shift_add_C hG a _)]

/-- **Volume 6, Lemma 2.3.2, the bound.** The order of `z^p + G` at each point is at most `p`. -/
theorem ord_shift_X_pow_add_le (a : σ → R) {z : σ} {G : MvPolynomial σ R} (hG : z ∉ G.vars) :
    ord (shift a (X z ^ p + G)) ≤ p := by
  rw [ord_shift_X_pow_add p a hG]
  exact min_le_left _ _

/-- **Volume 6, Lemma 2.3.2, the criterion.** The order of `z^p + G` at the point `a` is at
least `p`, and then equal to `p`, if and only if `G(x + a) + a_z^p` has order at least `p`. -/
theorem le_ord_shift_X_pow_add_iff (a : σ → R) {z : σ} {G : MvPolynomial σ R}
    (hG : z ∉ G.vars) :
    (p : ℕ∞) ≤ ord (shift a (X z ^ p + G)) ↔
      (p : ℕ∞) ≤ ord (shift a G + C (a z ^ p)) := by
  rw [ord_shift_X_pow_add p a hG, le_min_iff]
  exact and_iff_right le_rfl

/-- The order of `z^p + G` at `a` equals `p` if and only if `G(x + a) + a_z^p` has order at
least `p`. -/
theorem ord_shift_X_pow_add_eq_iff (a : σ → R) {z : σ} {G : MvPolynomial σ R}
    (hG : z ∉ G.vars) :
    ord (shift a (X z ^ p + G)) = p ↔ (p : ℕ∞) ≤ ord (shift a G + C (a z ^ p)) := by
  rw [← le_ord_shift_X_pow_add_iff p a hG]
  exact ⟨fun h => h.ge, fun h => le_antisymm (ord_shift_X_pow_add_le p a hG) h⟩

end CharP

end Singularity.PurelyInseparableEquation
