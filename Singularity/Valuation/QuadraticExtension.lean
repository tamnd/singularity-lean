/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic.Ring

/-!
# Extensions of a discrete valuation to quadratic extensions

This file proves the key steps of cases 2 and 3 of Volume 3, Example 3.1.7 of the handbook, in a general form. Mathlib writes valuations multiplicatively, so the value `1` of `ord_t(t)` in the handbook is `exp (-1)` in `ℤᵐ⁰` here, and the value `0` is `1`.

1. Case 2, `L = K(√t)`. Let `v` be a valuation of `K` with values in `ℤᵐ⁰` and `v(t) = exp m` with `m` odd, for example `ord_t` on `k(t)` with `m = -1`. Let `w` be a valuation of `L` whose restriction to `K` is equivalent to `v`, and let `s ∈ L` with `s^2 = t`. Then `w(s)` is not the value of an element of `K` (`valuation_ne_of_sq_eq`). So `w(s)` is not in the value group of `v`, and `e ≥ 2`.
2. Case 3, `L = K(√c)` with `c ∈ k` not a square. Let `w` be a valuation of `L` with `w(c) = 1` for each `c ≠ 0` in `k`, and let `s ∈ L` with `s^2 = c`. Then `w(s) = 1` (`valuation_eq_one_of_sq_eq`) and `w(s - b) = 1` for each `b ∈ k` (`valuation_sub_eq_one_of_sq_eq`). So the residue of `s` is not the residue of an element of `k`. If `Kv = k`, as for `ord_t` on `k(t)`, this gives `f ≥ 2`.

The equalities `e = 2` and `f = 2`, which use the fundamental inequality (Theorem 3.1.2), and case 1 are not proved here.

## Main results

* `Singularity.valuation_ne_of_sq_eq`: case 2, `w(√t) ∉ w(K)`.
* `Singularity.valuation_eq_one_of_sq_eq`: case 3, `w(√c) = 1`.
* `Singularity.valuation_sub_eq_one_of_sq_eq`: case 3, `w(√c - b) = 1` for each `b ∈ k`.
-/

open WithZero

namespace Singularity

/-- **Case 2 of Volume 3, Example 3.1.7 of the handbook.** Let `v(t) = exp m` with `m` odd, let the restriction of `w` to `K` be equivalent to `v`, and let `s^2 = t` in `L`. Then `w(s) ≠ w(a)` for each `a ∈ K`. So the ramification index of `w` over `v` is at least `2`. -/
theorem valuation_ne_of_sq_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K ℤᵐ⁰) (w : Valuation L Γ)
    (hw : (w.comap (algebraMap K L)).IsEquiv v) {t : K} {m : ℤ} (hm : Odd m)
    (ht : v t = exp m) {s : L} (hs : s ^ 2 = algebraMap K L t) (a : K) :
    w s ≠ w (algebraMap K L a) := by
  intro h
  have h1 : (w.comap (algebraMap K L)) (a ^ 2) = (w.comap (algebraMap K L)) t := by
    rw [Valuation.comap_apply, Valuation.comap_apply, map_pow, Valuation.map_pow, ← h,
      ← Valuation.map_pow, hs]
  have h2 : v (a ^ 2) = v t := hw.eq_iff.mp h1
  have ha : a ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, Valuation.map_zero, ht] at h2
    exact exp_ne_zero h2.symm
  have hva : v a ≠ 0 := (Valuation.ne_zero_iff v).mpr ha
  rw [Valuation.map_pow, ← exp_log hva, ← exp_nsmul, ht, exp_inj] at h2
  have h3 : 2 * log (v a) = m := by
    rw [← h2, two_nsmul, two_mul]
  obtain ⟨k, hk⟩ := hm
  omega

/-- **Case 3 of Volume 3, Example 3.1.7 of the handbook, the value.** Let `w` be trivial on `k`, and let `s^2 = c` with `c ∈ k` nonzero. Then `w(s) = 1`. -/
theorem valuation_eq_one_of_sq_eq {k L : Type*} [Field k] [Field L] [Algebra k L]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
    (hw : ∀ c : k, c ≠ 0 → w (algebraMap k L c) = 1) {c : k} (hc : c ≠ 0) {s : L}
    (hs : s ^ 2 = algebraMap k L c) : w s = 1 := by
  have h2 : w s * w s = 1 := by
    rw [← Valuation.map_mul, ← sq, hs, hw c hc]
  rcases lt_trichotomy (w s) 1 with hlt | heq | hgt
  · exfalso
    have h3 : w s * w s < 1 := (mul_le_of_le_one_right' hlt.le).trans_lt hlt
    rw [h2] at h3
    exact lt_irrefl _ h3
  · exact heq
  · exfalso
    have h3 : 1 < w s * w s := hgt.trans_le (le_mul_of_one_le_right' hgt.le)
    rw [h2] at h3
    exact lt_irrefl _ h3

/-- **Case 3 of Volume 3, Example 3.1.7 of the handbook, the residue.** Let `w` be trivial on `k`, and let `s^2 = c` with `c ∈ k` not a square in `k`. Then `w(s - b) = 1` for each `b ∈ k`. So the residue of `s` is not the residue of an element of `k`. -/
theorem valuation_sub_eq_one_of_sq_eq {k L : Type*} [Field k] [Field L] [Algebra k L]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
    (hw : ∀ c : k, c ≠ 0 → w (algebraMap k L c) = 1) {c : k} (hc : ¬ IsSquare c) {s : L}
    (hs : s ^ 2 = algebraMap k L c) (b : k) : w (s - algebraMap k L b) = 1 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc ⟨0, (mul_zero 0).symm⟩
  have hws : w s = 1 := valuation_eq_one_of_sq_eq w hw hc0 hs
  have hwb : w (algebraMap k L b) ≤ 1 := by
    by_cases hb : b = 0
    · rw [hb, map_zero, Valuation.map_zero]
      exact zero_le_one
    · exact (hw b hb).le
  have hle : w (s - algebraMap k L b) ≤ 1 :=
    (w.map_sub _ _).trans (max_le hws.le hwb)
  have hle' : w (s + algebraMap k L b) ≤ 1 :=
    (w.map_add _ _).trans (max_le hws.le hwb)
  have hcb : c - b ^ 2 ≠ 0 := by
    intro h0
    exact hc ⟨b, by rw [← sq]; exact sub_eq_zero.mp h0⟩
  have hprod : (s - algebraMap k L b) * (s + algebraMap k L b) =
      algebraMap k L (c - b ^ 2) := by
    rw [map_sub, map_pow, ← hs]
    ring
  refine le_antisymm hle (not_lt.mp fun hlt => ?_)
  have h1 : w ((s - algebraMap k L b) * (s + algebraMap k L b)) < 1 := by
    rw [Valuation.map_mul]
    exact (mul_le_of_le_one_right' hle').trans_lt hlt
  rw [hprod, hw _ hcb] at h1
  exact lt_irrefl _ h1

end Singularity
