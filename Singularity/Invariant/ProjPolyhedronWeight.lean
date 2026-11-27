/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.CharacteristicPolyhedron
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The vertices and the weighted minimum of the polyhedron of Hironaka

This file proves Volume 6, Lemma 3.1.2 (1), (2) and (3) of the handbook for the projected polyhedron `Δ(f; x; z)` of `Singularity.Invariant.CharacteristicPolyhedron`. Here `f` is a polynomial of degree `m` in `z` over `k[[x_i : i ∈ σ]]`.

## Main results

* `exists_eq_inv_factorial_smul_of_mem_extremePoints_projPolyhedron`: each vertex of `Δ(f; x; z)` lies in `(1/m!) ℕ^σ`. This is part (1).
* `projPolyhedron_eq_empty_iff_of_monic`: for a monic `f`, the polyhedron is empty if and only if `f = z^m`. This is part (2).
* `le_linWeight_projPolyhedron_iff`: for a weight `w ≥ 0`, a real number `c` is a lower bound of `|·|_w` on `Δ(f; x; z)` if and only if `i c ≤ |a|_w` for each monomial `x^a` of the coefficient of `z^(m-i)`.
* `sInf_linWeight_projPolyhedron`: the infimum of `|·|_w` on a nonempty `Δ(f; x; z)` is the infimum of the values `|a|_w / i`. This is part (3).

The handbook states part (3) with minima. The file states it with infima, and it does not prove that the infimum is attained. For part (4), the file proves only the easy direction (`le_linWeight_of_subset`). The other direction needs that the polyhedron is closed and a separation theorem, and it is not in Lean.
-/

open Polynomial Pointwise

namespace Singularity

variable {σ k : Type*} [CommSemiring k]

/-! ### The vertices lie in `(1/m!) ℕ^σ` -/

/-- Volume 6, Lemma 3.1.2 (1). Each vertex of `Δ(f; x; z)` has the form `a / m!` with `a ∈ ℕ^σ`, where `m = f.natDegree`. -/
theorem exists_eq_inv_factorial_smul_of_mem_extremePoints_projPolyhedron
    {f : (MvPowerSeries σ k)[X]} {u : σ → ℝ} (hu : u ∈ (projPolyhedron f).extremePoints ℝ) :
    ∃ a : σ →₀ ℕ, u = ((f.natDegree.factorial : ℕ) : ℝ)⁻¹ • expToReal a := by
  obtain ⟨i, hi1, him, α, -, rfl⟩ := extremePoints_projPolyhedron_subset f hu
  obtain ⟨q, hq⟩ := Nat.dvd_factorial (by omega) him
  refine ⟨q • α, ?_⟩
  have hi0 : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq0 : (q : ℝ) ≠ 0 := by
    intro h0
    have : q = 0 := by exact_mod_cast h0
    rw [this, mul_zero] at hq
    exact Nat.factorial_ne_zero _ hq
  funext l
  simp only [Pi.smul_apply, expToReal_apply, smul_eq_mul, Finsupp.smul_apply, hq]
  push_cast
  field_simp

/-! ### The empty polyhedron -/

theorem projPolyhedron_eq_empty_iff (f : (MvPowerSeries σ k)[X]) :
    projPolyhedron f = ∅ ↔ ∀ i, 1 ≤ i → i ≤ f.natDegree → f.coeff (f.natDegree - i) = 0 := by
  have hO : (orthant σ).Nonempty := ⟨0, zero_mem_orthant⟩
  rw [projPolyhedron, Set.add_eq_empty, convexHull_eq_empty, or_iff_left hO.ne_empty,
    Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h i hi1 him
    ext α
    by_contra hα
    exact h _ ⟨i, hi1, him, α, by simpa using hα, rfl⟩
  · rintro h _ ⟨i, hi1, him, α, hα, rfl⟩
    rw [h i hi1 him] at hα
    exact hα (map_zero _)

/-- Volume 6, Lemma 3.1.2 (2). For a monic polynomial `f` of degree `m`, the polyhedron `Δ(f; x; z)` is empty if and only if `f = z^m`. -/
theorem projPolyhedron_eq_empty_iff_of_monic {f : (MvPowerSeries σ k)[X]} (hf : f.Monic) :
    projPolyhedron f = ∅ ↔ f = X ^ f.natDegree := by
  rw [projPolyhedron_eq_empty_iff]
  constructor
  · intro h
    refine Polynomial.ext fun d => ?_
    rw [coeff_X_pow]
    rcases lt_trichotomy d f.natDegree with hd | hd | hd
    · rw [ite_eq_right hd.ne]
      have := h (f.natDegree - d) (by omega) (by omega)
      rwa [Nat.sub_sub_self hd.le] at this
    · rw [ite_eq_left hd, hd]
      exact hf.coeff_natDegree
    · rw [ite_eq_right hd.ne', coeff_eq_zero_of_natDegree_lt hd]
  · intro h i hi1 him
    have h2 := congrArg (fun g => g.coeff (f.natDegree - i)) h
    simp only [coeff_X_pow] at h2
    rw [h2, ite_eq_right (by omega)]

/-! ### The weighted minimum -/

theorem projPolyhedron_subset_orthant (f : (MvPowerSeries σ k)[X]) :
    projPolyhedron f ⊆ orthant σ := by
  refine convexHull_add_orthant_subset ?_ convex_orthant (by rw [orthant_add_orthant])
  rintro _ ⟨i, -, -, α, -, rfl⟩ l
  simp only [Pi.smul_apply, expToReal_apply, smul_eq_mul]
  positivity

variable [Fintype σ]

/-- The linear form `|x|_w = ∑_j w_j x_j` on `ℝ^σ`. -/
def linWeight (w : σ → ℝ) (x : σ → ℝ) : ℝ := ∑ j, w j * x j

theorem isLinearMap_linWeight (w : σ → ℝ) : IsLinearMap ℝ (linWeight w) where
  map_add x y := by simp [linWeight, mul_add, Finset.sum_add_distrib]
  map_smul c x := by simp [linWeight, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring

theorem linWeight_nonneg {w x : σ → ℝ} (hw : ∀ j, 0 ≤ w j) (hx : x ∈ orthant σ) :
    0 ≤ linWeight w x :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (hx j)

/-- Volume 6, Lemma 3.1.2 (3), in the form of lower bounds. Let `w ≥ 0`. A real number `c` is a lower bound of `|·|_w` on `Δ(f; x; z)` if and only if `i c ≤ |a|_w` for each `1 ≤ i ≤ m` and each monomial `x^a` of the coefficient `a_i` of `z^(m-i)`. -/
theorem le_linWeight_projPolyhedron_iff (f : (MvPowerSeries σ k)[X]) {w : σ → ℝ}
    (hw : ∀ j, 0 ≤ w j) (c : ℝ) :
    (∀ x ∈ projPolyhedron f, c ≤ linWeight w x) ↔
      ∀ i, 1 ≤ i → i ≤ f.natDegree → ∀ a : σ →₀ ℕ,
        MvPowerSeries.coeff a (f.coeff (f.natDegree - i)) ≠ 0 →
          (i : ℝ) * c ≤ linWeight w (expToReal a) := by
  have hlin := isLinearMap_linWeight w
  constructor
  · intro h i hi1 him a ha
    have hi : (0 : ℝ) < i := Nat.cast_pos.mpr (by omega)
    have := h _ (projPoints_subset_projPolyhedron f ⟨i, hi1, him, a, ha, rfl⟩)
    rw [hlin.map_smul, smul_eq_mul] at this
    rw [le_inv_mul_iff₀ hi] at this
    exact this
  · intro h
    refine convexHull_add_orthant_subset (P := {x | c ≤ linWeight w x}) ?_
      (convex_halfSpace_ge hlin c) ?_
    · rintro _ ⟨i, hi1, him, a, ha, rfl⟩
      have hi : (0 : ℝ) < i := Nat.cast_pos.mpr (by omega)
      show c ≤ linWeight w _
      rw [hlin.map_smul, smul_eq_mul, le_inv_mul_iff₀ hi]
      exact h i hi1 him a ha
    · rintro _ ⟨x, hx, o, ho, rfl⟩
      show c ≤ linWeight w (x + o)
      rw [hlin.map_add]
      have : (0 : ℝ) ≤ linWeight w o := linWeight_nonneg hw ho
      have hx' : c ≤ linWeight w x := hx
      linarith

/-- The values `|a|_w / i` for `1 ≤ i ≤ m` and `x^a` a monomial of the coefficient of `z^(m-i)`. Their infimum is `min_i μ_w(a_i) / i`. -/
def projWeights (f : (MvPowerSeries σ k)[X]) (w : σ → ℝ) : Set ℝ :=
  {r | ∃ i, 1 ≤ i ∧ i ≤ f.natDegree ∧ ∃ a : σ →₀ ℕ,
    MvPowerSeries.coeff a (f.coeff (f.natDegree - i)) ≠ 0 ∧ r = linWeight w (expToReal a) / i}

/-- Volume 6, Lemma 3.1.2 (3). Let `w ≥ 0` and let `Δ(f; x; z)` be nonempty. Then the infimum of `|·|_w` on `Δ(f; x; z)` is the infimum of the values `|a|_w / i`, that is, `δ_w(f) = min_i μ_w(a_i) / i`. -/
theorem sInf_linWeight_projPolyhedron (f : (MvPowerSeries σ k)[X]) {w : σ → ℝ}
    (hw : ∀ j, 0 ≤ w j) (hne : (projPolyhedron f).Nonempty) :
    sInf (linWeight w '' projPolyhedron f) = sInf (projWeights f w) := by
  have hbS : BddBelow (linWeight w '' projPolyhedron f) :=
    ⟨0, by rintro _ ⟨x, hx, rfl⟩; exact linWeight_nonneg hw (projPolyhedron_subset_orthant f hx)⟩
  have hbT : BddBelow (projWeights f w) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨i, -, -, a, -, rfl⟩
    exact div_nonneg (linWeight_nonneg hw fun l => by simp [expToReal_apply]) (Nat.cast_nonneg _)
  have key : ∀ c, (∀ x ∈ projPolyhedron f, c ≤ linWeight w x) ↔ c ∈ lowerBounds (projWeights f w) := by
    intro c
    rw [le_linWeight_projPolyhedron_iff f hw c]
    constructor
    · rintro h _ ⟨i, hi1, him, a, ha, rfl⟩
      have hi : (0 : ℝ) < i := Nat.cast_pos.mpr (by omega)
      rw [le_div_iff₀ hi, mul_comm]
      exact h i hi1 him a ha
    · intro h i hi1 him a ha
      have hi : (0 : ℝ) < i := Nat.cast_pos.mpr (by omega)
      have := h ⟨i, hi1, him, a, ha, rfl⟩
      rw [le_div_iff₀ hi, mul_comm] at this
      exact this
  have hTne : (projWeights f w).Nonempty := by
    by_contra hT
    rw [Set.not_nonempty_iff_eq_empty] at hT
    have h := (key (linWeight w hne.some + 1)).mpr (by rw [hT]; exact fun _ h => h.elim)
    linarith [h _ hne.some_mem]
  apply le_antisymm
  · refine le_csInf hTne fun t ht => ?_
    have : sInf (linWeight w '' projPolyhedron f) ∈ lowerBounds (projWeights f w) :=
      (key _).mp fun x hx => csInf_le hbS ⟨x, hx, rfl⟩
    exact this ht
  · refine le_csInf (hne.image _) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (key _).mpr (fun t ht => csInf_le hbT ht) x hx

/-- One direction of Volume 6, Lemma 3.1.2 (4). If `Δ' ⊆ Δ`, then each lower bound of `|·|_w` on `Δ` is a lower bound on `Δ'`. -/
theorem le_linWeight_of_subset {P Q : Set (σ → ℝ)} (hPQ : P ⊆ Q) (w : σ → ℝ) {c : ℝ}
    (h : ∀ x ∈ Q, c ≤ linWeight w x) : ∀ x ∈ P, c ≤ linWeight w x :=
  fun x hx => h x (hPQ hx)

end Singularity
