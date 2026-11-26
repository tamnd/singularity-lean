/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.LinearCombination

/-!
# Artin-Schreier polynomials

Let `p` be a prime and let `F` be a field of characteristic `p`. For `a ∈ F` the Artin-Schreier polynomial is `X^p - X - a`. This file proves the facts on this polynomial that the handbook uses in Section 3.2 of Volume 3 (proof of Proposition 3.2.5 and Example 3.2.6).

1. If `θ` is a root, then the roots are the elements `θ + n` with `0 ≤ n < p`, and they are distinct. So two roots differ by an element of the prime field (`artinSchreierPoly_roots_toFinset`, `sub_pow_eq_sub_of_artinSchreier`).
2. If the polynomial has a root in `F`, then it splits over `F` (`artinSchreierPoly_splits`).
3. If the polynomial has no root in `F`, then it is irreducible over `F` (`artinSchreierPoly_irreducible`). So the polynomial is irreducible or it splits (`artinSchreierPoly_irreducible_or_splits`).
4. The polynomial `X^p - X - 1` is irreducible over `𝔽_p` (`artinSchreierPoly_one_irreducible_zmod`). This is a part of Example 3.2.6 (2).

The proof of the irreducibility follows the handbook. Let `g` be a monic factor of degree `d`. Each root `r` of `g` in an algebraic closure has `r^p = r + a`. Let `s` be the sum of the roots of `g`, which is in `F`. Then `s^p - s = d a`. If `0 < d < p`, then `s / d` is a root in `F`.
-/

open Polynomial

namespace Singularity

section CommRing

variable {R : Type*} [CommRing R]

/-- The Artin-Schreier polynomial `X^p - X - a` (Volume 3, Section 3.2 of the handbook). -/
noncomputable def artinSchreierPoly (p : ℕ) (a : R) : R[X] :=
  X ^ p - X - C a

theorem artinSchreierPoly_eq (p : ℕ) (a : R) : artinSchreierPoly p a = X ^ p - (X + C a) := by
  unfold artinSchreierPoly
  ring

@[simp]
theorem eval_artinSchreierPoly (p : ℕ) (a x : R) :
    (artinSchreierPoly p a).eval x = x ^ p - x - a := by
  simp [artinSchreierPoly]

theorem map_artinSchreierPoly {S : Type*} [CommRing S] (f : R →+* S) (p : ℕ) (a : R) :
    (artinSchreierPoly p a).map f = artinSchreierPoly p (f a) := by
  simp [artinSchreierPoly]

end CommRing

section Field

variable {F : Type*} [Field F] (p : ℕ) [hp : Fact p.Prime] [CharP F p]

theorem artinSchreierPoly_monic (a : F) : (artinSchreierPoly p a).Monic := by
  rw [artinSchreierPoly_eq]
  apply monic_X_pow_sub
  rw [degree_X_add_C]
  exact_mod_cast hp.out.one_lt

theorem artinSchreierPoly_natDegree (a : F) : (artinSchreierPoly p a).natDegree = p := by
  have h : (X + C a : F[X]).natDegree < (X ^ p : F[X]).natDegree := by
    rw [natDegree_X_add_C, natDegree_X_pow]
    exact hp.out.one_lt
  rw [artinSchreierPoly_eq, natDegree_sub_eq_left_of_natDegree_lt h, natDegree_X_pow]

/-- Two roots of `X^p - X - a` differ by an element `c` with `c^p = c`, that is, by an element of the prime field (Volume 3, proof of Proposition 3.2.5 of the handbook). -/
theorem sub_pow_eq_sub_of_artinSchreier {E : Type*} [CommRing E] [CharP E p] {a x y : E}
    (hx : x ^ p - x - a = 0) (hy : y ^ p - y - a = 0) : (x - y) ^ p = x - y := by
  rw [sub_pow_char]
  linear_combination hx - hy

/-- The natural numbers are fixed by the map `x ↦ x^p`. -/
theorem natCast_pow_char {E : Type*} [CommRing E] [CharP E p] (n : ℕ) : (n : E) ^ p = n := by
  have h := map_natCast (frobenius E p) n
  rwa [frobenius_def] at h

/-- The `p` elements `θ + n` with `0 ≤ n < p` are distinct. -/
theorem card_image_add_natCast {E : Type*} [Field E] [CharP E p] [DecidableEq E] (θ : E) :
    ((Finset.range p).image (fun n : ℕ => θ + n)).card = p := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro m hm n hn h
  simp only [Finset.coe_range, Set.mem_Iio] at hm hn
  have h' : (m : E) = n := add_left_cancel h
  exact ((CharP.natCast_eq_natCast (R := E) (p := p)).mp h').eq_of_lt_of_lt hm hn

/-- Let `θ` be a root of `X^p - X - a` in a field `E` of characteristic `p`. Then the roots of `X^p - X - a` in `E` are the `p` elements `θ + n` with `0 ≤ n < p` (Volume 3, proof of Proposition 3.2.5 of the handbook: the roots are `θ + i` with `i ∈ 𝔽_p`). -/
theorem artinSchreierPoly_roots_toFinset {E : Type*} [Field E] [CharP E p] [DecidableEq E]
    {a θ : E}
    (hθ : θ ^ p - θ - a = 0) :
    (artinSchreierPoly p a).roots.toFinset = (Finset.range p).image (fun n : ℕ => θ + n) := by
  have hf0 : artinSchreierPoly p a ≠ 0 := (artinSchreierPoly_monic p a).ne_zero
  have hsub : (Finset.range p).image (fun n : ℕ => θ + n) ⊆
      (artinSchreierPoly p a).roots.toFinset := by
    intro y hy
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hy
    rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot.def, eval_artinSchreierPoly, add_pow_char,
      natCast_pow_char p n]
    linear_combination hθ
  have hcard := card_image_add_natCast p (E := E) θ
  symm
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [hcard]
  calc (artinSchreierPoly p a).roots.toFinset.card
      ≤ Multiset.card (artinSchreierPoly p a).roots := Multiset.toFinset_card_le _
    _ ≤ (artinSchreierPoly p a).natDegree := card_roots' _
    _ = p := artinSchreierPoly_natDegree p a

/-- If `X^p - X - a` has a root in a field `E` of characteristic `p`, then it splits over `E` (Volume 3, proof of Proposition 3.2.5 of the handbook). -/
theorem artinSchreierPoly_splits {E : Type*} [Field E] [CharP E p] {a θ : E}
    (hθ : θ ^ p - θ - a = 0) : (artinSchreierPoly p a).Splits := by
  classical
  rw [splits_iff_card_roots]
  apply le_antisymm (card_roots' _)
  have hcard := card_image_add_natCast p (E := E) θ
  calc (artinSchreierPoly p a).natDegree = p := artinSchreierPoly_natDegree p a
    _ = ((Finset.range p).image (fun n : ℕ => θ + n)).card := hcard.symm
    _ = (artinSchreierPoly p a).roots.toFinset.card := by
      rw [artinSchreierPoly_roots_toFinset p hθ]
    _ ≤ Multiset.card (artinSchreierPoly p a).roots := Multiset.toFinset_card_le _

/-- Let `g` be a monic factor of `X^p - X - a` over `F`, and let `s = -c` where `c` is the coefficient of `X^(d-1)` in `g` and `d = deg g`. So `s` is the sum of the roots of `g`. Then `s^p - s = d a` (Volume 3, proof of Proposition 3.2.5 of the handbook). -/
theorem neg_nextCoeff_pow_sub_of_dvd {a : F} {g : F[X]} (hg : g.Monic)
    (hdvd : g ∣ artinSchreierPoly p a) :
    (-g.nextCoeff) ^ p - (-g.nextCoeff) = g.natDegree * a := by
  obtain ⟨i, -⟩ : ∃ i : F →+* AlgebraicClosure F, i = algebraMap F (AlgebraicClosure F) :=
    ⟨_, rfl⟩
  have hs : (g.map i).Splits := IsAlgClosed.splits _
  have hsum : i (-g.nextCoeff) = (g.map i).roots.sum := by
    rw [map_neg, ← nextCoeff_map i.injective, hs.nextCoeff_eq_neg_sum_roots_of_monic (hg.map i),
      neg_neg]
  have hcard : Multiset.card (g.map i).roots = g.natDegree := by
    rw [← hs.natDegree_eq_card_roots, natDegree_map]
  have hd : g.map i ∣ artinSchreierPoly p (i a) := by
    rw [← map_artinSchreierPoly]
    exact Polynomial.map_dvd i hdvd
  have hroot : ∀ r ∈ (g.map i).roots, r ^ p = r + i a := by
    intro r hr
    have h1 : (g.map i).eval r = 0 := isRoot_of_mem_roots hr
    have h2 := eval_eq_zero_of_dvd_of_eval_eq_zero hd h1
    rw [eval_artinSchreierPoly] at h2
    linear_combination h2
  have hpow : ((g.map i).roots.sum) ^ p = (g.map i).roots.sum + g.natDegree * i a := by
    rw [multiset_sum_pow_char, Multiset.map_congr rfl hroot]
    simp [Multiset.sum_map_add, hcard]
  apply i.injective
  rw [map_sub, map_pow, hsum, hpow, map_mul, map_natCast]
  ring

/-- If `X^p - X - a` has no root in `F`, then it is irreducible over `F` (Volume 3, proof of Proposition 3.2.5 and Example 3.2.6 of the handbook). -/
theorem artinSchreierPoly_irreducible {a : F} (h : ∀ x : F, x ^ p - x - a ≠ 0) :
    Irreducible (artinSchreierPoly p a) := by
  have hm := artinSchreierPoly_monic p a
  rw [hm.irreducible_iff_natDegree]
  refine ⟨fun h1 => ?_, fun f g hf hg hfg => ?_⟩
  · have h2 := congrArg natDegree h1
    rw [artinSchreierPoly_natDegree, natDegree_one] at h2
    exact hp.out.ne_zero h2
  by_contra hne
  push_neg at hne
  obtain ⟨hf0, hg0⟩ := hne
  have hdeg : f.natDegree + g.natDegree = p := by
    rw [← hf.natDegree_mul hg, hfg, artinSchreierPoly_natDegree]
  have hlt : g.natDegree < p := by omega
  have hpos : 0 < g.natDegree := Nat.pos_of_ne_zero hg0
  have hdvd : g ∣ artinSchreierPoly p a := ⟨f, by rw [← hfg, mul_comm]⟩
  have key := neg_nextCoeff_pow_sub_of_dvd p hg hdvd
  have hd0 : (g.natDegree : F) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff F p] at h0
    exact absurd (Nat.le_of_dvd hpos h0) (not_le.mpr hlt)
  apply h ((-g.nextCoeff) / g.natDegree)
  have key' : (-g.nextCoeff) ^ p = -g.nextCoeff + g.natDegree * a := by
    linear_combination key
  rw [div_pow, natCast_pow_char p g.natDegree, key', ← sub_div, add_sub_cancel_left,
    mul_div_cancel_left₀ _ hd0, sub_self]

/-- The polynomial `X^p - X - a` over `F` is irreducible or it splits (Volume 3, proof of Proposition 3.2.5 and Example 3.2.6 of the handbook). -/
theorem artinSchreierPoly_irreducible_or_splits (a : F) :
    Irreducible (artinSchreierPoly p a) ∨ (artinSchreierPoly p a).Splits := by
  by_cases h : ∃ x : F, x ^ p - x - a = 0
  · obtain ⟨x, hx⟩ := h
    exact Or.inr (artinSchreierPoly_splits p hx)
  · push_neg at h
    exact Or.inl (artinSchreierPoly_irreducible p h)

end Field

/-- The polynomial `X^p - X - 1` is irreducible over `𝔽_p` (Volume 3, Example 3.2.6 (2) of the handbook). It has no root, since `x^p = x` for each `x ∈ 𝔽_p`. -/
theorem artinSchreierPoly_one_irreducible_zmod (p : ℕ) [Fact p.Prime] :
    Irreducible (artinSchreierPoly p (1 : ZMod p)) := by
  apply artinSchreierPoly_irreducible p
  intro x
  rw [ZMod.pow_card, sub_self, zero_sub]
  exact neg_ne_zero.mpr one_ne_zero

end Singularity
