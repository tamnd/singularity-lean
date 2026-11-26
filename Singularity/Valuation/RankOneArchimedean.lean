/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Archimedean.Basic
import Singularity.Valuation.ConvexSubgroup

/-!
# Groups of rank 1 are the archimedean groups

Let `G` be a totally ordered abelian group with `G ≠ 1`. The group has rank 1 if its only convex subgroups are `1` and `G`. This file proves that `G` has rank 1 if and only if it is archimedean (Volume 3, Lemma 1.2.6 of the handbook). Mathlib writes value groups multiplicatively, so the group is multiplicative here, and archimedean is `MulArchimedean G`.

The proof follows the handbook. For `a > 1` the elements `x` with `|x| ≤ a^n` for some `n` form a convex subgroup (`Singularity.boundedSubgroup`). If `G` has rank 1, this subgroup is `G`, so `G` is archimedean. Conversely, if `G` is archimedean and `H ≠ 1` is convex, take `b ∈ H` with `b ≠ 1`. Each `x` has `|x| ≤ |b|^n` for some `n`, so `x ∈ H`.
-/

namespace Singularity

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]

/-- The subgroup of the elements `x` with `|x| ≤ a^n` for some `n`. -/
def boundedSubgroup (a : G) : Subgroup G where
  carrier := {x | ∃ n : ℕ, mabs x ≤ a ^ n}
  one_mem' := show ∃ n : ℕ, mabs (1 : G) ≤ a ^ n from ⟨0, by simp⟩
  mul_mem' := by
    intro x y hx hy
    obtain ⟨m, hm⟩ : ∃ n : ℕ, mabs x ≤ a ^ n := hx
    obtain ⟨n, hn⟩ : ∃ n : ℕ, mabs y ≤ a ^ n := hy
    show ∃ n : ℕ, mabs (x * y) ≤ a ^ n
    exact ⟨m + n, (mabs_mul_le x y).trans (by rw [pow_add]; exact mul_le_mul' hm hn)⟩
  inv_mem' := by
    intro x hx
    obtain ⟨n, hn⟩ : ∃ n : ℕ, mabs x ≤ a ^ n := hx
    show ∃ n : ℕ, mabs x⁻¹ ≤ a ^ n
    exact ⟨n, by rwa [mabs_inv]⟩

theorem mem_boundedSubgroup {a x : G} : x ∈ boundedSubgroup a ↔ ∃ n : ℕ, mabs x ≤ a ^ n :=
  Iff.rfl

/-- The subgroup `boundedSubgroup a` is convex. -/
theorem isConvexSubgroup_boundedSubgroup (a : G) : IsConvexSubgroup (boundedSubgroup a) := by
  intro x y hx hxy hy
  obtain ⟨n, hn⟩ := mem_boundedSubgroup.mp hy
  refine mem_boundedSubgroup.mpr ⟨n, ?_⟩
  rw [mabs_of_one_le hx]
  exact hxy.trans ((le_mabs_self y).trans hn)

/-- **Rank at most 1 and archimedean groups** (Volume 3, Lemma 1.2.6 of the handbook). The only convex subgroups of `G` are `1` and `G` if and only if `G` is archimedean. -/
theorem forall_isConvexSubgroup_iff_mulArchimedean :
    (∀ H : Subgroup G, IsConvexSubgroup H → H = ⊥ ∨ H = ⊤) ↔ MulArchimedean G := by
  constructor
  · intro h
    refine ⟨fun x y hy => ?_⟩
    have hy' : y ∈ boundedSubgroup y :=
      mem_boundedSubgroup.mpr ⟨1, by rw [pow_one, mabs_of_one_le hy.le]⟩
    rcases h _ (isConvexSubgroup_boundedSubgroup y) with hb | ht
    · rw [hb, Subgroup.mem_bot] at hy'
      exact absurd hy' hy.ne'
    · have hx : x ∈ boundedSubgroup y := by
        rw [ht]
        exact Subgroup.mem_top x
      obtain ⟨n, hn⟩ := mem_boundedSubgroup.mp hx
      exact ⟨n, (le_mabs_self x).trans hn⟩
  · intro _ H hH
    rcases H.bot_or_exists_ne_one with hbot | ⟨b, hb, hb1⟩
    · exact Or.inl hbot
    right
    have ha : 1 < mabs b := one_lt_mabs.mpr hb1
    rw [eq_top_iff]
    intro x _
    obtain ⟨n, hn⟩ := MulArchimedean.arch (mabs x) ha
    exact (mabs_mem_iff H).mp (hH (one_le_mabs x) hn (H.pow_mem ((mabs_mem_iff H).mpr hb) n))

/-- **A group of rank 1 is archimedean, and conversely** (Volume 3, Lemma 1.2.6 of the handbook). Let `G ≠ 1`. Then `G` has exactly the two convex subgroups `1 ≠ G` if and only if `G` is archimedean. -/
theorem rankOne_iff_mulArchimedean [Nontrivial G] :
    ((⊥ : Subgroup G) ≠ ⊤ ∧ ∀ H : Subgroup G, IsConvexSubgroup H → H = ⊥ ∨ H = ⊤) ↔
      MulArchimedean G := by
  rw [← forall_isConvexSubgroup_iff_mulArchimedean]
  refine ⟨fun h => h.2, fun h => ⟨fun hbt => ?_, h⟩⟩
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  have hx' : x ∈ (⊥ : Subgroup G) := by
    rw [hbt]
    exact Subgroup.mem_top x
  exact hx (Subgroup.mem_bot.mp hx')

end Singularity
