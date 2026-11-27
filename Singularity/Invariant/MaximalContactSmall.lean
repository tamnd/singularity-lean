/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.Tschirnhausen
import Mathlib.Tactic.LinearCombination

/-!
# Maximal contact for small multiplicity

This file proves Volume 6, Proposition 1.2.5 of the handbook at the points with coordinates in the base ring. Let `R` be a nontrivial commutative ring, let `m ≥ 1` be a unit in `R`, and let `h = z^m + ∑_{i < m} a_i(x) z^i` in `R[z, x]` (`zMonic m a`). Let `z' = z + a_{m-1}/m` (`maximalContactCoord`).

* At each point `b ∈ R^{1+n}`, the order of `h` is at most `m` (`ord_translate_zMonic_le`). The translated polynomial has the coefficient `1` at `z^m`.
* If the order of `h` at `b` is at least `m`, then `z'(b) = 0` (`eval_maximalContactCoord_eq_zero`). The coefficient of `z^{m-1}` in `h(x + b_x, z + b_z)` has the constant term `a_{m-1}(b_x) + m b_z`, and this term must be `0`.
* The coordinate `z'` is the image of `z` under the change `z ↦ z + a_{m-1}/m` (`zShift_X_none_eq_maximalContactCoord`). So `V(z')` is a regular hypersurface.

The main result is `maximalContact_small_multiplicity`. The handbook asks that `m!` is a unit. The proof here needs only that `m` is a unit.

The file does not treat the points that are not rational over `R`, for example the generic points of subvarieties. The file `Singularity/Invariant/Tschirnhausen.lean` has the same argument for a polynomial in Tschirnhausen form (`eq_zero_of_le_ord_translate`).
-/

open MvPolynomial Finsupp

namespace Singularity

section MaximalContact

variable {σ R : Type*} [CommRing R]

/-- The constant coefficient of `p(x + b)` is `p(b)`. -/
theorem constantCoeff_aeval_translate (b : σ → R) (p : MvPolynomial σ R) :
    constantCoeff (aeval (fun l => X l + C (b l)) p) = eval b p := by
  change ((constantCoeff : MvPolynomial σ R →+* R).comp
    (aeval (fun l => X l + C (b l)) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R).toRingHom) p = _
  congr 1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun l => ?_)
  · simp
  · simp

/-- The translation of `zMonic m a` to the point `b` is again a `zMonic m a'`, and the coefficient `a'_{m-1}` is `a_{m-1}(x + b_x) + m b_z`. -/
theorem exists_translate_zMonic {m : ℕ} (hm : 1 ≤ m) (a : ℕ → MvPolynomial σ R)
    (b : Option σ → R) :
    ∃ a' : ℕ → MvPolynomial σ R,
      aeval (fun o => X o + C (b o)) (zMonic m a) = zMonic m a' ∧
      a' (m - 1) = aeval (fun l => X l + C (b (Option.some l))) (a (m - 1)) + (m : MvPolynomial σ R) * C (b none) := by
  rw [aeval_translate_eq, xTranslate_zMonic]
  exact exists_zShift_zMonic (C (b none)) hm _

/-- **The order is at most `m`.** Let `R` be nontrivial and let `1 ≤ m`. At each point `b ∈ R^{1+n}`, the polynomial `z^m + ∑_{i < m} a_i z^i` has order at most `m`. The reason is that the translated polynomial has the coefficient `1` at `z^m`. -/
theorem ord_translate_zMonic_le [Nontrivial R] {m : ℕ} (hm : 1 ≤ m) (a : ℕ → MvPolynomial σ R)
    (b : Option σ → R) :
    ord (aeval (fun o => X o + C (b o)) (zMonic m a)) ≤ m := by
  obtain ⟨a', he, -⟩ := exists_translate_zMonic hm a b
  rw [he]
  have h1 : (zMonic m a').coeff (Finsupp.single none m) ≠ 0 := by
    rw [coeff_zMonic, single_eq_same, ite_eq_right (lt_irrefl m), ite_eq_left rfl,
      Finsupp.some_single_none]
    simp
  have h2 := ord_le h1
  rwa [degree_single] at h2

/-- The coordinate `z' = z + a_{m-1}/m` of the proposition. -/
noncomputable def maximalContactCoord {m : ℕ} (hm : IsUnit (m : R)) (a : ℕ → MvPolynomial σ R) :
    MvPolynomial (Option σ) R :=
  X none + C (↑hm.unit⁻¹ : R) * rename Option.some (a (m - 1))

/-- The coordinate `z'` is the image of `z` under the change `z ↦ z + a_{m-1}/m`. So `V(z')` is the image of the hyperplane `z = 0` under an automorphism of `R[z, x]`, and it is a regular hypersurface. -/
theorem zShift_X_none_eq_maximalContactCoord {k : Type*} [Field k] {m : ℕ} (hm : IsUnit (m : k))
    (a : ℕ → MvPolynomial σ k) :
    zShift (C (↑hm.unit⁻¹ : k) * a (m - 1)) (X none) = maximalContactCoord hm a := by
  simp [zShift, maximalContactCoord]

/-- **The points of order `m` lie on `V(z')`.** Let `m` be a unit in `R`, and let `f = z^m + ∑_{i < m} a_i z^i`. If `f` has order at least `m` at the point `b ∈ R^{1+n}`, then `z' = z + a_{m-1}/m` is `0` at `b`. -/
theorem eval_maximalContactCoord_eq_zero {m : ℕ} (hm : IsUnit (m : R))
    (a : ℕ → MvPolynomial σ R) (b : Option σ → R)
    (h : (m : ℕ∞) ≤ ord (aeval (fun o => X o + C (b o)) (zMonic m a))) :
    eval b (maximalContactCoord hm a) = 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · rw [Nat.cast_zero, isUnit_zero_iff] at hm
    exact (subsingleton_of_zero_eq_one hm).elim _ _
  obtain ⟨a', he, ha'⟩ := exists_translate_zMonic hm1 a b
  rw [he] at h
  have h0 := le_ord_iff.mp h (Finsupp.single none (m - 1)) (by rw [degree_single]; omega)
  rw [coeff_zMonic, single_eq_same, ite_eq_left (show m - 1 < m by omega),
    Finsupp.some_single_none, ha', ← constantCoeff_eq, map_add, map_mul,
    map_natCast, constantCoeff_C, constantCoeff_aeval_translate] at h0
  have hu : (m : R) * (↑hm.unit⁻¹ : R) = 1 := hm.mul_val_inv
  simp only [maximalContactCoord, map_add, map_mul, eval_X, eval_C, eval_rename, Function.comp_def]
  linear_combination (↑hm.unit⁻¹ : R) * h0 - b none * hu

/-- **Volume 6, Proposition 1.2.5 (maximal contact for small multiplicity).** Let `R` be a nontrivial ring, let `m ≥ 1` with `m` a unit in `R`, and let `h = z^m + ∑_{i < m} a_i z^i` with `a_i ∈ R[x]`. Then at each point `b ∈ R^{1+n}` the order of `h` is at most `m`, and if the order is `m`, then `b` lies on `V(z')` with `z' = z + a_{m-1}/m`. -/
theorem maximalContact_small_multiplicity [Nontrivial R] {m : ℕ} (hm1 : 1 ≤ m)
    (hm : IsUnit (m : R)) (a : ℕ → MvPolynomial σ R) (b : Option σ → R) :
    ord (aeval (fun o => X o + C (b o)) (zMonic m a)) ≤ m ∧
      (ord (aeval (fun o => X o + C (b o)) (zMonic m a)) = m →
        eval b (maximalContactCoord hm a) = 0) :=
  ⟨ord_translate_zMonic_le hm1 a b,
    fun h => eval_maximalContactCoord_eq_zero hm a b h.ge⟩

end MaximalContact

end Singularity
