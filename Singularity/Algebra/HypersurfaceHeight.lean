/-
Copyright (c) 2026 The singularity-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# The heights of the closed points of a hypersurface

This file proves the dimension part of Volume 4, Lemma 1.2.6 of the handbook, and the step of
the proof that gives the condition $R_1$.

Let $k$ be a field and let $P = k[x_1, \dots, x_n]$.

* `height_isMaximal_mvPolynomial`: each maximal ideal of $P$ has height $n$.
* `height_isMaximal_quotient_span_singleton`: let $F \in P$ be nonzero. Then each maximal ideal
  of $A = P/(F)$ has height $n - 1$. For $n = 3$, each closed point of $V(F)$ has a local ring of
  dimension 2.
* `isRegularLocalRing_of_height_le_one`: let $n = 3$, and assume that the local ring of $A$ at
  each prime that is not maximal is regular. Then $A_\mathfrak{p}$ is regular for each prime
  $\mathfrak{p}$ of height at most 1. This is the condition $R_1$.

The condition $S_2$ and the criterion of Serre are not in Lean, because Mathlib does not have
Cohen-Macaulay rings. Thus the normality of $X$ is not in Lean. The lemma assumes that the
singular locus is a finite set of closed points. The proof uses only that each singular point
is a closed point.
-/

namespace Singularity

open Ideal

variable {k : Type*} [Field k]

/-- Each maximal ideal of `k[x_1, ..., x_n]` has height at least `n`. -/
theorem le_height_isMaximal_mvPolynomial :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) k)) [M.IsMaximal], (n : ℕ∞) ≤ M.height
  | 0, _, _ => by simp
  | n + 1, M, hM => by
    let e := (MvPolynomial.finSuccEquiv k n).toRingEquiv
    let M' : Ideal (Polynomial (MvPolynomial (Fin n) k)) := M.map e
    have : M'.IsMaximal := map_isMaximal_of_equiv e
    have hM' : M'.height = M.height := e.height_map M
    have : (M'.under (MvPolynomial (Fin n) k)).IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing M'
    have h := Polynomial.height_eq_height_add_one (M'.under (MvPolynomial (Fin n) k)) M'
    have ih := le_height_isMaximal_mvPolynomial n (M'.under (MvPolynomial (Fin n) k))
    rw [← hM', h]
    push_cast
    exact add_le_add_left ih 1

/-- Each maximal ideal of `k[x_1, ..., x_n]` has height `n`. -/
theorem height_isMaximal_mvPolynomial (n : ℕ) (M : Ideal (MvPolynomial (Fin n) k))
    [M.IsMaximal] : M.height = n := by
  refine le_antisymm ?_ (le_height_isMaximal_mvPolynomial n M)
  have h := Ideal.height_le_ringKrullDim_of_ne_top (IsMaximal.ne_top ‹_›)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  exact_mod_cast h

/-- Let `F` be nonzero. Then each maximal ideal of `k[x_1, ..., x_n]/(F)` has height `n - 1`.
The statement is `N.height + 1 = n`. -/
theorem height_isMaximal_quotient_span_singleton (n : ℕ) {F : MvPolynomial (Fin n) k}
    (hF : F ≠ 0) (N : Ideal (MvPolynomial (Fin n) k ⧸ span {F})) [N.IsMaximal] :
    N.height + 1 = n := by
  set mk := Ideal.Quotient.mk (span {F})
  have : (N.comap mk).IsMaximal := comap_isMaximal_of_surjective mk Ideal.Quotient.mk_surjective
  have h0 : mk F = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (mem_span_singleton_self F)
  have hF' : F ∈ N.comap mk := by
    rw [mem_comap, h0]
    exact N.zero_mem
  have hmap : (N.comap mk).map mk = N := map_comap_of_surjective mk Ideal.Quotient.mk_surjective N
  have lower := Ideal.height_le_height_add_one_of_mem (p := N.comap mk) hF'
  rw [hmap, height_isMaximal_mvPolynomial] at lower
  have hdim : ringKrullDim (MvPolynomial (Fin n) k ⧸ Ideal.span {F}) + 1 ≤ n := by
    have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (R := MvPolynomial (Fin n) k)
      (r := F) (mem_nonZeroDivisors_of_ne_zero hF)
    rwa [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  have upper := Ideal.height_le_ringKrullDim_of_ne_top (IsMaximal.ne_top ‹N.IsMaximal›)
  have upper' : ((N.height + 1 : ℕ∞) : WithBot ℕ∞) ≤ (n : ℕ∞) := by
    push_cast
    exact le_trans (add_le_add_left upper 1) hdim
  exact le_antisymm (by exact_mod_cast upper') lower

/-- For `n = 3`: each closed point of a surface `V(F)` in affine 3-space has height 2. -/
theorem height_isMaximal_quotient_span_singleton_three {F : MvPolynomial (Fin 3) k}
    (hF : F ≠ 0) (N : Ideal (MvPolynomial (Fin 3) k ⧸ span {F})) [N.IsMaximal] :
    N.height = 2 := by
  have h := height_isMaximal_quotient_span_singleton 3 hF N
  cases hN : N.height with
  | top => rw [hN] at h; simp at h
  | coe a =>
    rw [hN] at h
    have : a + 1 = 3 := by exact_mod_cast h
    have : a = 2 := by omega
    simp [this]

/-- The step of Volume 4, Lemma 1.2.6 of the handbook that gives the condition `R_1`. Let
`F ≠ 0` in `k[x, y, z]` and let `A = k[x, y, z]/(F)`. Assume that `A_p` is regular for each
prime `p` that is not maximal. Then `A_p` is regular for each prime `p` of height at most 1. -/
theorem isRegularLocalRing_of_height_le_one {F : MvPolynomial (Fin 3) k} (hF : F ≠ 0)
    (hSing : ∀ (p : Ideal (MvPolynomial (Fin 3) k ⧸ span {F})) [p.IsPrime], ¬ p.IsMaximal →
      IsRegularLocalRing (Localization.AtPrime p))
    (p : Ideal (MvPolynomial (Fin 3) k ⧸ span {F})) [p.IsPrime] (hp : p.height ≤ 1) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  refine hSing p fun hmax => ?_
  have h := height_isMaximal_quotient_span_singleton_three hF p
  rw [h] at hp
  exact absurd hp (by decide)

end Singularity
