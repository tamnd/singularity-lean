/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Algebra.Order.Monoid.TypeTags
import Mathlib.Data.Nat.Find
import Mathlib.SetTheory.Cardinal.Finite
import Singularity.Valuation.ConvexSubgroup

/-!
# The convex subgroups of the lexicographic group `ℤ^n`

This file proves Volume 3, Example 1.2.7 of the handbook. Order `ℤ^n` lexicographically. For `0 ≤ m ≤ n`, let `Δ'_m` be the subgroup of the vectors whose first `m` entries are `0`. In the notation of the handbook, `Δ'_m` is `Δ_{n-m}`. Then the `Δ'_m` are exactly the convex subgroups of `ℤ^n`, and they are distinct. So `ℤ^n` has exactly `n + 1` convex subgroups, and its rank is `n`.

The file `Singularity.Valuation.ConvexSubgroup` writes the group multiplicatively, so the group here is `Multiplicative (Lex (Fin n → ℤ))` (`Singularity.LexZn`). The proof follows the handbook. Let `H` be a convex subgroup, and let `m` be the first place where an element of `H` has a nonzero entry. Then `H ⊆ Δ'_m`. Let `δ ∈ H` have a positive entry at place `m`. For each `γ ≥ 0` in `Δ'_m` there is an `N` with `γ < N δ`, so `γ ∈ H`.

The handbook also states that the rational rank of `ℤ^n` is `n`. This file does not prove that claim.

## Main results

* `Singularity.LexZn.isConvexSubgroup_delta`: each `Δ'_m` is convex.
* `Singularity.LexZn.isConvexSubgroup_iff`: a subgroup is convex if and only if it is a `Δ'_m` with `m ≤ n`.
* `Singularity.LexZn.natCard_convexSubgroup`: there are exactly `n + 1` convex subgroups.
-/

namespace Singularity

/-- The group `ℤ^n` with the lexicographic order, written multiplicatively. -/
abbrev LexZn (n : ℕ) : Type := Multiplicative (Lex (Fin n → ℤ))

namespace LexZn

variable {n : ℕ}

/-- The entry of `g` at the place `i`. -/
def coord (g : LexZn n) (i : Fin n) : ℤ := ofLex (Multiplicative.toAdd g) i

theorem coord_mul (a b : LexZn n) (i : Fin n) : coord (a * b) i = coord a i + coord b i := rfl

theorem coord_one (i : Fin n) : coord (1 : LexZn n) i = 0 := rfl

theorem coord_inv (a : LexZn n) (i : Fin n) : coord a⁻¹ i = -coord a i := rfl

theorem coord_pow (a : LexZn n) (k : ℕ) (i : Fin n) : coord (a ^ k) i = k * coord a i := by
  induction k with
  | zero => rw [pow_zero, coord_one, Nat.cast_zero, zero_mul]
  | succ k ih => rw [pow_succ, coord_mul, ih, Nat.cast_succ, add_mul, one_mul]

theorem eq_one_of_coord {g : LexZn n} (h : ∀ i, coord g i = 0) : g = 1 := by
  have h' : ofLex (Multiplicative.toAdd g) = ofLex (Multiplicative.toAdd (1 : LexZn n)) :=
    funext fun i => (h i).trans (coord_one i).symm
  exact Multiplicative.toAdd.injective (ofLex.injective h')

/-- If `a ≤ b` and the entries of `a` and `b` agree before the place `i`, then the entry of `a` at `i` is at most the entry of `b` at `i`. -/
theorem coord_le_of_le {a b : LexZn n} (hab : a ≤ b) {i : Fin n}
    (h : ∀ j < i, coord a j = coord b j) : coord a i ≤ coord b i :=
  Pi.apply_le_of_toLex (x := ofLex (Multiplicative.toAdd a)) (y := ofLex (Multiplicative.toAdd b))
    hab h

/-- If the entries of `a` and `b` agree before the place `i`, and the entry of `a` at `i` is less than the entry of `b` at `i`, then `a < b`. -/
theorem lt_of_coord {a b : LexZn n} (i : Fin n) (h : ∀ j < i, coord a j = coord b j)
    (hi : coord a i < coord b i) : a < b := by
  have h' : ∃ i, (∀ j, j < i → coord a j = coord b j) ∧ coord a i < coord b i := ⟨i, h, hi⟩
  exact h'

/-- The subgroup `Δ'_m` of the vectors whose first `m` entries are `0`. In the notation of the handbook it is `Δ_{n-m}` (Volume 3, Example 1.2.7 of the handbook). -/
def delta (n m : ℕ) : Subgroup (LexZn n) where
  carrier := {g | ∀ i : Fin n, (i : ℕ) < m → coord g i = 0}
  mul_mem' := by
    intro a b ha hb
    have ha' : ∀ i : Fin n, (i : ℕ) < m → coord a i = 0 := ha
    have hb' : ∀ i : Fin n, (i : ℕ) < m → coord b i = 0 := hb
    show ∀ i : Fin n, (i : ℕ) < m → coord (a * b) i = 0
    intro i hi
    rw [coord_mul, ha' i hi, hb' i hi, add_zero]
  one_mem' := by
    show ∀ i : Fin n, (i : ℕ) < m → coord (1 : LexZn n) i = 0
    exact fun i _ => coord_one i
  inv_mem' := by
    intro a ha
    have ha' : ∀ i : Fin n, (i : ℕ) < m → coord a i = 0 := ha
    show ∀ i : Fin n, (i : ℕ) < m → coord a⁻¹ i = 0
    intro i hi
    rw [coord_inv, ha' i hi, neg_zero]

theorem mem_delta {m : ℕ} {g : LexZn n} :
    g ∈ delta n m ↔ ∀ i : Fin n, (i : ℕ) < m → coord g i = 0 :=
  Iff.rfl

/-- Each subgroup `Δ'_m` is convex (Volume 3, Example 1.2.7 of the handbook). -/
theorem isConvexSubgroup_delta (m : ℕ) : IsConvexSubgroup (delta n m) := by
  intro a b ha hab hb
  rw [mem_delta] at hb ⊢
  suffices h : ∀ k : ℕ, ∀ i : Fin n, (i : ℕ) = k → k < m → coord a i = 0 from
    fun i hi => h i i rfl hi
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ih i hik hkm
  have hlow : ∀ j < i, coord a j = 0 := by
    intro j hj
    have hj' : (j : ℕ) < k := by
      rw [← hik]
      exact Fin.lt_iff_val_lt_val.mp hj
    exact ih j hj' j rfl (by omega)
  have h1 : coord (1 : LexZn n) i ≤ coord a i :=
    coord_le_of_le ha fun j hj => by rw [coord_one, hlow j hj]
  have h2 : coord a i ≤ coord b i := by
    refine coord_le_of_le hab fun j hj => ?_
    have hj' : (j : ℕ) < m := by
      have := Fin.lt_iff_val_lt_val.mp hj
      omega
    rw [hlow j hj, hb j hj']
  rw [coord_one] at h1
  rw [hb i (by omega)] at h2
  omega

/-- **The convex subgroups of the lexicographic group `ℤ^n`** (Volume 3, Example 1.2.7 of the handbook). A subgroup `H` of `ℤ^n` is convex if and only if `H = Δ'_m` for some `m ≤ n`. -/
theorem isConvexSubgroup_iff (H : Subgroup (LexZn n)) :
    IsConvexSubgroup H ↔ ∃ m ≤ n, H = delta n m := by
  constructor
  swap
  · rintro ⟨m, -, rfl⟩
    exact isConvexSubgroup_delta m
  intro hH
  classical
  have hQ : ∃ k : ℕ, k = n ∨ ∃ i : Fin n, (i : ℕ) = k ∧ ∃ h ∈ H, coord h i ≠ 0 :=
    ⟨n, Or.inl rfl⟩
  refine ⟨Nat.find hQ, Nat.find_min' hQ (Or.inl rfl), ?_⟩
  have hsub : H ≤ delta n (Nat.find hQ) := by
    intro h hh
    rw [mem_delta]
    intro i hi
    by_contra hne
    exact Nat.find_min hQ hi (Or.inr ⟨i, rfl, h, hh, hne⟩)
  apply le_antisymm hsub
  rcases Nat.find_spec hQ with hn | ⟨i0, hi0, h0, hh0, hne0⟩
  · intro g hg
    rw [hn, mem_delta] at hg
    rw [eq_one_of_coord fun i => hg i i.2]
    exact H.one_mem
  · obtain ⟨δ, hδH, hδpos⟩ : ∃ δ ∈ H, 0 < coord δ i0 := by
      rcases lt_or_gt_of_ne hne0 with hlt | hgt
      · exact ⟨h0⁻¹, H.inv_mem hh0, by rw [coord_inv]; omega⟩
      · exact ⟨h0, hh0, hgt⟩
    have hδD := hsub hδH
    have key : ∀ g ∈ delta n (Nat.find hQ), 1 ≤ g → g ∈ H := by
      intro g hg hg1
      have hpow : δ ^ ((coord g i0).natAbs + 1) ∈ H := H.pow_mem hδH _
      refine hH hg1 (le_of_lt (lt_of_coord i0 (fun j hj => ?_) ?_)) hpow
      · have hj' : (j : ℕ) < Nat.find hQ := by
          rw [← hi0]
          exact Fin.lt_iff_val_lt_val.mp hj
        rw [mem_delta.mp hg j hj', coord_pow, mem_delta.mp hδD j hj', mul_zero]
      · rw [coord_pow]
        have h1 : coord g i0 ≤ ((coord g i0).natAbs : ℤ) := Int.le_natAbs
        have h2 : (0 : ℤ) ≤ ((coord g i0).natAbs : ℤ) := by positivity
        have h3 : (1 : ℤ) ≤ coord δ i0 := by omega
        push_cast
        nlinarith
    intro g hg
    rw [← mabs_mem_iff H]
    have hmabs : mabs g ∈ delta n (Nat.find hQ) := by
      rcases mabs_choice g with h | h
      · rw [h]
        exact hg
      · rw [h]
        exact (delta n _).inv_mem hg
    exact key _ hmabs (one_le_mabs g)

/-- The subgroups `Δ'_m` with `m ≤ n` are distinct. -/
theorem delta_ne_of_lt {m m' : ℕ} (hlt : m < m') (hm' : m' ≤ n) : delta n m ≠ delta n m' := by
  intro h
  let i : Fin n := ⟨m, by omega⟩
  let e : LexZn n := Multiplicative.ofAdd (toLex (Pi.single i 1))
  have he : ∀ j, coord e j = Pi.single i (1 : ℤ) j := fun j => rfl
  have hmem : e ∈ delta n m := by
    rw [mem_delta]
    intro j hj
    rw [he, Pi.single_eq_of_ne]
    intro hji
    have hj' : (j : ℕ) = m := congrArg Fin.val hji
    omega
  rw [h, mem_delta] at hmem
  have h1 := hmem i hlt
  rw [he, Pi.single_eq_same] at h1
  exact one_ne_zero h1

theorem delta_injOn {m m' : ℕ} (hm : m ≤ n) (hm' : m' ≤ n) (h : delta n m = delta n m') :
    m = m' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact delta_ne_of_lt hlt hm' h
  · exact delta_ne_of_lt hlt hm h.symm

/-- The map `m ↦ Δ'_m` is a bijection from `{0, ..., n}` to the convex subgroups of `ℤ^n`. -/
noncomputable def finEquivConvexSubgroup (n : ℕ) :
    Fin (n + 1) ≃ {H : Subgroup (LexZn n) // IsConvexSubgroup H} :=
  Equiv.ofBijective (fun m => ⟨delta n m, isConvexSubgroup_delta m⟩) <| by
    constructor
    · intro a b hab
      exact Fin.ext (delta_injOn (Nat.lt_succ_iff.mp a.2) (Nat.lt_succ_iff.mp b.2)
        (congrArg Subtype.val hab))
    · rintro ⟨H, hH⟩
      obtain ⟨m, hm, rfl⟩ := (isConvexSubgroup_iff H).mp hH
      exact ⟨⟨m, Nat.lt_succ_of_le hm⟩, rfl⟩

/-- **The lexicographic group `ℤ^n` has exactly `n + 1` convex subgroups** (Volume 3, Example 1.2.7 of the handbook). So its rank is `n`. -/
theorem natCard_convexSubgroup (n : ℕ) :
    Nat.card {H : Subgroup (LexZn n) // IsConvexSubgroup H} = n + 1 := by
  rw [← Nat.card_congr (finEquivConvexSubgroup n), Nat.card_eq_fintype_card, Fintype.card_fin]

end LexZn

end Singularity
