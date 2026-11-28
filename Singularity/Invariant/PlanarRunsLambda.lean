/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.PlanarRunsFrobenius

/-!
# Theorem 3.18.26, part 3: the form of `Λ`

This file proves part 3 of Theorem 3.18.26 of Volume 7 of the handbook, for the abstract tail
`IsFrobTail` of `PlanarRunsAnyDegree` and for the planar corner runs of the Hahn model.

For `f ≠ 0` put `β_k(f) = v(f^{[k]}(Φ_∞))` and
`Λ(f) = min_{k ≠ 0} (β_k(f) + |k| Θ)`, `Λ_e(f) = min_i β_{p^e e_i}(f) + p^e Θ`.
Part 3 says that `Λ(f) = min_e Λ_e(f)`, and that the minimum is attained only at the indices
`p^e e_i`. In Lean this is the statement that each `k ≠ 0` with `f^{[k]} ≠ 0` has an index
`p^e e_i ≤ k` with `f^{[p^e e_i]} ≠ 0` and
`β_{p^e e_i}(f) + p^e Θ ≤ β_k(f) + |k| Θ`, with a strict inequality if `k ≠ p^e e_i`. The
minimum `Λ(f)` is not a definition here: the statement compares the terms of the minimum, so it
does not need an infimum in `WithTop ℝ`.

## Main results

* `lambda_le_of_frob`: part 3 for the abstract tail `IsFrobTail`.
* `lambda_le_corner`: part 3 for a planar corner run of the Hahn model over a perfect field,
  with the coefficients in `𝔽`.

## Proof

This is Step 1 of the handbook proof. Take `i` with `k_i ≠ 0` and `p^e` the exact power of `p`
in `k_i`. Then `C(k_i, p^e)` is prime to `p`, and
`(f^{[p^e e_i]})^{[k - p^e e_i]} = C(k_i, p^e) f^{[k]}` (`hasse_sub_hasse_single`). Part 1 of
Theorem 3.18.26 for `h = f^{[p^e e_i]}` (`statementD_frob`) gives the strict inequality.
-/

open MvPolynomial Filter Topology

namespace Singularity

namespace PlanarRuns

section Abstract

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]
  {v : AddValuation K (WithTop ℝ)} {F : Subring K} {Φ : ℕ → σ → F} {Φi : σ → K}
  {Θ : ℝ} {γ : ℕ → ℝ}

/-- Theorem 3.18.26, part 3, for the abstract tail `IsFrobTail`: each term
`β_k(f) + |k| Θ` of `Λ(f)` is at least a term `β_{p^e e_i}(f) + p^e Θ` of `Λ_e(f)`, and the
inequality is strict if `k` is not `p^e e_i`. So `Λ(f) = min_e Λ_e(f)`, and the minimum is
attained only at the indices of `p`-power form. -/
theorem lambda_le_of_frob {p : ℕ} [CharP K p] (hp : p.Prime) (hT : IsFrobTail v F Φ Φi p Θ γ)
    (f : MvPolynomial σ F) (k : σ →₀ ℕ) (hk : k ≠ 0) (hk0 : hasse k f ≠ 0) :
    ∃ i a, p ^ a ≤ k i ∧ hasse (Finsupp.single i (p ^ a)) f ≠ 0 ∧
      v (eval₂ F.subtype Φi (hasse (Finsupp.single i (p ^ a)) f)) +
          ((((p ^ a : ℕ) : ℝ) * Θ : ℝ) : WithTop ℝ) ≤
        v (eval₂ F.subtype Φi (hasse k f)) + (((ord k : ℝ) * Θ : ℝ) : WithTop ℝ) ∧
      (k ≠ Finsupp.single i (p ^ a) →
        v (eval₂ F.subtype Φi (hasse (Finsupp.single i (p ^ a)) f)) +
            ((((p ^ a : ℕ) : ℝ) * Θ : ℝ) : WithTop ℝ) <
          v (eval₂ F.subtype Φi (hasse k f)) + (((ord k : ℝ) * Θ : ℝ) : WithTop ℝ)) := by
  set E : MvPolynomial σ F → K := fun g => eval₂ F.subtype Φi g with hE
  obtain ⟨i, hi⟩ := exists_ne_zero_of_ne_zero hk
  obtain ⟨a, ha, hnd⟩ := exists_pow_not_dvd_choose hp hi
  set s := Finsupp.single i (p ^ a) with hs
  have hEk := (statementD_frob hp hT (hasse k f) hk0).1
  have hc : v ((k i).choose (p ^ a) : K) = 0 := v.map_natCast_eq_zero hp hnd
  have hc0 : ((k i).choose (p ^ a) : K) ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hc
    exact WithTop.top_ne_zero hc
  have hE_nsmul : ∀ (c : ℕ) g, E (c • g) = (c : K) * E g := by
    intro c g
    simp [hE, nsmul_eq_mul]
  have heval : E (hasse (k - s) (hasse s f)) = ((k i).choose (p ^ a) : K) * E (hasse k f) := by
    rw [hs, hasse_sub_hasse_single k ha, hE_nsmul]
  have hpoly : hasse (k - s) (hasse s f) ≠ 0 := by
    intro h0
    rw [h0] at heval
    simp only [hE, eval₂_zero] at heval
    exact mul_ne_zero hc0 hEk heval.symm
  have hsx : hasse s f ≠ 0 := fun h0 => hpoly (by rw [h0, hasse_zero_right])
  have hval : v (E (hasse (k - s) (hasse s f))) = v (E (hasse k f)) := by
    rw [heval, AddValuation.map_mul, hc, zero_add]
  have hle : s ≤ k := Finsupp.single_le_iff.mpr ha
  have hord := ord_sub_single' k ha
  have hstrict : k ≠ s →
      v (E (hasse s f)) + ((((p ^ a : ℕ) : ℝ) * Θ : ℝ) : WithTop ℝ) <
        v (E (hasse k f)) + (((ord k : ℝ) * Θ : ℝ) : WithTop ℝ) := by
    intro hke
    have hj : k - s ≠ 0 := by
      intro h0
      apply hke
      rw [← tsub_add_cancel_of_le hle, h0, zero_add]
    have h3 := (statementD_frob hp hT (hasse s f) hsx).2.1 (k - s) hj hpoly
    rw [hval] at h3
    have hreal : ((ord k : ℝ) * Θ : ℝ) =
        ((ord (k - Finsupp.single i (p ^ a)) : ℝ) * Θ : ℝ) + (((p ^ a : ℕ) : ℝ) * Θ : ℝ) := by
      rw [← hord]
      push_cast
      ring
    calc v (E (hasse s f)) + ((((p ^ a : ℕ) : ℝ) * Θ : ℝ) : WithTop ℝ)
        < v (E (hasse k f)) + (((ord (k - s) : ℝ) * Θ : ℝ) : WithTop ℝ) +
            ((((p ^ a : ℕ) : ℝ) * Θ : ℝ) : WithTop ℝ) :=
          WithTop.add_lt_add_right WithTop.coe_ne_top h3
      _ = v (E (hasse k f)) + (((ord k : ℝ) * Θ : ℝ) : WithTop ℝ) := by
          rw [hreal, WithTop.coe_add, add_assoc]
  refine ⟨i, a, ha, hsx, ?_, hstrict⟩
  by_cases hke : k = s
  · have hok : ord k = p ^ a := by rw [hke, hs]; exact ord_single _ _
    rw [hok, hke]
  · exact (hstrict hke).le

end Abstract

section Corner

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {θ : ℝ} {k : Type*} [Field k] {w : ℕ → Bool}

/-- Theorem 3.18.26, part 3, for a planar corner run of the Hahn model over a perfect field, with
`θ` irrational and the coefficients in `𝔽`: `Λ(f) = min_e Λ_e(f)`, and each index `n ≠ 0` not
of the form `p^e e_i` has `β_n(f) + |n|(1 + θ) > Λ(f)`. -/
theorem lambda_le_corner {p : ℕ} [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (hθ : Irrational θ) (hw : IsCornerWord θ w) (t : ℕ → σ → k) (hpl : IsPlanarRun t)
    (f : MvPolynomial σ (finiteTypeSubfield k hθ).toSubring) (n : σ →₀ ℕ) (hn : n ≠ 0)
    (hn0 : hasse n f ≠ 0) :
    ∃ i a, p ^ a ≤ n i ∧ hasse (Finsupp.single i (p ^ a)) f ≠ 0 ∧
      hahnVal θ k (eval₂ (finiteTypeSubfield k hθ).toSubring.subtype
          (fun l => cornerLimit hw (fun j => t j l)) (hasse (Finsupp.single i (p ^ a)) f)) +
          ((((p ^ a : ℕ) : ℝ) * (1 + θ) : ℝ) : WithTop ℝ) ≤
        hahnVal θ k (eval₂ (finiteTypeSubfield k hθ).toSubring.subtype
          (fun l => cornerLimit hw (fun j => t j l)) (hasse n f)) +
          (((ord n : ℝ) * (1 + θ) : ℝ) : WithTop ℝ) ∧
      (n ≠ Finsupp.single i (p ^ a) →
        hahnVal θ k (eval₂ (finiteTypeSubfield k hθ).toSubring.subtype
            (fun l => cornerLimit hw (fun j => t j l)) (hasse (Finsupp.single i (p ^ a)) f)) +
            ((((p ^ a : ℕ) : ℝ) * (1 + θ) : ℝ) : WithTop ℝ) <
          hahnVal θ k (eval₂ (finiteTypeSubfield k hθ).toSubring.subtype
            (fun l => cornerLimit hw (fun j => t j l)) (hasse n f)) +
            (((ord n : ℝ) * (1 + θ) : ℝ) : WithTop ℝ)) :=
  lambda_le_of_frob Fact.out (isFrobTail_corner hθ hw t hpl) f n hn hn0

end Corner

end PlanarRuns

end Singularity
