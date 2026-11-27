/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Cofinal chains of submodules

This file proves Volume 1, Lemma 4.2.4 of the handbook. Let `M` be an `R`-module, and let `(M_n)` and `(M'_n)` be descending chains of submodules of `M`. Assume that `M'_n ⊆ M_n` for each `n`, and that there is `c` with `M_{n+c} ⊆ M'_n` for each `n`. Then the natural map `lim M / M'_n → lim M / M_n` is bijective.

In Lean the limit `lim M / M_n` is the set `Singularity.Algebra.chainLimit N hN` of the families `x n ∈ M ⧸ N n` such that `x m` is the image of `x n` for each `m ≤ n`.

* `Singularity.Algebra.chainLimit`: the inverse limit of the quotients of `M` by a descending chain.
* `Singularity.Algebra.chainLimitMap`: the natural map between two such limits.
* `Singularity.Algebra.bijOn_chainLimitMap`: Lemma 4.2.4 of the handbook.

The proof is the proof of the handbook. The inverse of the natural map sends `(y_n)` to the family of the images of `y_{n+c}` in `M ⧸ M'_n`.
-/

namespace Singularity.Algebra

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The inverse limit of the quotients `M ⧸ N n` for a descending chain `N`, as the set of the compatible families. -/
def chainLimit (N : ℕ → Submodule R M) (hN : Antitone N) : Set (∀ n, M ⧸ N n) :=
  {x | ∀ m n (h : m ≤ n), Submodule.factor (hN h) (x n) = x m}

/-- The natural map `∏ M ⧸ N' n → ∏ M ⧸ N n` for `N' n ≤ N n`. -/
def chainLimitMap {N N' : ℕ → Submodule R M} (hle : ∀ n, N' n ≤ N n) (x : ∀ n, M ⧸ N' n) :
    ∀ n, M ⧸ N n :=
  fun n => Submodule.factor (hle n) (x n)

theorem chainLimitMap_mem {N N' : ℕ → Submodule R M} (hN : Antitone N) (hN' : Antitone N')
    (hle : ∀ n, N' n ≤ N n) {x : ∀ n, M ⧸ N' n} (hx : x ∈ chainLimit N' hN') :
    chainLimitMap hle x ∈ chainLimit N hN := by
  intro m n h
  simp only [chainLimitMap, Submodule.factor_comp_apply]
  rw [← hx m n h, Submodule.factor_comp_apply]

/-- Let `(N n)` and `(N' n)` be descending chains of submodules of `M` with `N' n ≤ N n` and `N (n + c) ≤ N' n` for each `n`. Then the natural map `lim M ⧸ N' n → lim M ⧸ N n` is bijective (Volume 1, Lemma 4.2.4 of the handbook). -/
theorem bijOn_chainLimitMap {N N' : ℕ → Submodule R M} (hN : Antitone N) (hN' : Antitone N')
    (hle : ∀ n, N' n ≤ N n) (c : ℕ) (hc : ∀ n, N (n + c) ≤ N' n) :
    Set.BijOn (chainLimitMap hle) (chainLimit N' hN') (chainLimit N hN) := by
  refine ⟨fun x hx => chainLimitMap_mem hN hN' hle hx, ?_, ?_⟩
  · intro x hx x' hx' hxx'
    funext n
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x (n + c))
    obtain ⟨y', hy'⟩ := Submodule.Quotient.mk_surjective _ (x' (n + c))
    have h1 := congrFun hxx' (n + c)
    simp only [chainLimitMap, ← hy, ← hy'] at h1
    change Submodule.Quotient.mk y = Submodule.Quotient.mk y' at h1
    rw [Submodule.Quotient.eq] at h1
    rw [← hx n (n + c) (Nat.le_add_right n c), ← hx' n (n + c) (Nat.le_add_right n c), ← hy, ← hy']
    change Submodule.Quotient.mk y = Submodule.Quotient.mk y'
    rw [Submodule.Quotient.eq]
    exact hc n h1
  · intro y hy
    refine ⟨fun n => Submodule.factor (hc n) (y (n + c)), ?_, ?_⟩
    · intro m n h
      simp only [Submodule.factor_comp_apply]
      rw [← hy (m + c) (n + c) (Nat.add_le_add_right h c), Submodule.factor_comp_apply]
    · funext n
      simp only [chainLimitMap, Submodule.factor_comp_apply]
      exact hy n (n + c) (Nat.le_add_right n c)

end Singularity.Algebra
