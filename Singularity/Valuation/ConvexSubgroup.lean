/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Convex subgroups of an ordered group

Let `Γ` be a totally ordered abelian group. A subgroup `Δ` of `Γ` is convex if `0 ≤ γ ≤ δ` and `δ ∈ Δ` give `γ ∈ Δ`. Mathlib has no notion of a convex subgroup, so this file defines it (`Singularity.IsConvexSubgroup`). Mathlib writes value groups multiplicatively, so the file uses a multiplicative group `G`, and `0` is `1` here.

The file proves two results of the handbook.

1. The convex subgroups are totally ordered by inclusion (Volume 3, Lemma 1.2.2 of the handbook).
2. If `G` has rational rank `r < ∞`, then `G` has at most `r + 1` convex subgroups (Volume 3, Proposition 1.2.5 of the handbook).

The proof of the second result follows the handbook. Let `Δ_0 < Δ_1 < ... < Δ_t` be a chain of convex subgroups. Choose `δ_i ∈ Δ_i` outside `Δ_{i-1}`. If `n δ_i` is in `Δ_{i-1}` for some `n ≠ 0`, then `δ_i` is in `Δ_{i-1}` by convexity. So the `δ_i` are linearly independent over `ℤ`, and `t ≤ r`.

## Main results

* `Singularity.IsConvexSubgroup`: the definition.
* `Singularity.IsConvexSubgroup.le_or_le`: two convex subgroups are comparable.
* `Singularity.IsConvexSubgroup.finite_and_card_le`: there are at most `r + 1` convex subgroups.
-/

open TensorProduct

namespace Singularity

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]

/-- A subgroup `H` of an ordered group `G` is convex if `1 ≤ a ≤ b` and `b ∈ H` give `a ∈ H`. In additive notation, this is the condition `0 ≤ γ ≤ δ`, `δ ∈ Δ` gives `γ ∈ Δ` of the handbook (Volume 3, Section 1.2). -/
def IsConvexSubgroup (H : Subgroup G) : Prop :=
  ∀ ⦃a b : G⦄, 1 ≤ a → a ≤ b → b ∈ H → a ∈ H

/-- An element is in a subgroup if and only if its absolute value is in the subgroup. -/
omit [IsOrderedMonoid G] in
theorem mabs_mem_iff (H : Subgroup G) {a : G} : mabs a ∈ H ↔ a ∈ H := by
  rcases mabs_choice a with h | h
  · rw [h]
  · rw [h, inv_mem_iff]

/-- The trivial subgroup is convex. -/
omit [IsOrderedMonoid G] in
theorem isConvexSubgroup_bot : IsConvexSubgroup (⊥ : Subgroup G) := by
  intro a b ha hab hb
  rw [Subgroup.mem_bot] at hb ⊢
  subst hb
  exact le_antisymm hab ha

/-- The whole group is convex. -/
omit [IsOrderedMonoid G] in
theorem isConvexSubgroup_top : IsConvexSubgroup (⊤ : Subgroup G) :=
  fun _ _ _ _ _ => Subgroup.mem_top _

/-- The convex subgroups of an ordered group are totally ordered by inclusion (Volume 3, Lemma 1.2.2 of the handbook). -/
theorem IsConvexSubgroup.le_or_le {H₁ H₂ : Subgroup G} (h₁ : IsConvexSubgroup H₁)
    (h₂ : IsConvexSubgroup H₂) : H₁ ≤ H₂ ∨ H₂ ≤ H₁ := by
  by_contra h
  rw [not_or, IsConcreteLE.not_le_iff_exists, IsConcreteLE.not_le_iff_exists] at h
  obtain ⟨⟨a, ha₁, ha₂⟩, ⟨b, hb₂, hb₁⟩⟩ := h
  rcases le_total (mabs a) (mabs b) with hab | hab
  · exact ha₂ ((mabs_mem_iff H₂).mp (h₂ (one_le_mabs a) hab ((mabs_mem_iff H₂).mpr hb₂)))
  · exact hb₁ ((mabs_mem_iff H₁).mp (h₁ (one_le_mabs b) hab ((mabs_mem_iff H₁).mpr ha₁)))

/-- Let `H` be a convex subgroup and let `1 ≤ a`. If `a ^ n ∈ H` for some `n ≠ 0`, then `a ∈ H`. -/
theorem IsConvexSubgroup.mem_of_zpow_mem {H : Subgroup G} (hH : IsConvexSubgroup H) {a : G}
    (ha : 1 ≤ a) {n : ℤ} (hn : n ≠ 0) (h : a ^ n ∈ H) : a ∈ H := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast] at h
    exact hH ha (le_self_pow ha (by exact_mod_cast hn)) h
  · rw [zpow_neg, zpow_natCast, inv_mem_iff] at h
    exact hH ha (le_self_pow ha (by simpa using hn)) h

/-- The subgroup `H` of `G` as a `ℤ`-submodule of `Additive G`. -/
def subgroupToIntSubmodule (H : Subgroup G) : Submodule ℤ (Additive G) where
  carrier := {y | Additive.toMul y ∈ H}
  add_mem' := by
    intro a b ha hb
    exact H.mul_mem ha hb
  zero_mem' := H.one_mem
  smul_mem' := by
    intro c y hy
    show Additive.toMul (c • y) ∈ H
    rw [toMul_zsmul]
    exact H.zpow_mem hy c

omit [LinearOrder G] [IsOrderedMonoid G] in
theorem mem_subgroupToIntSubmodule (H : Subgroup G) {y : Additive G} :
    y ∈ subgroupToIntSubmodule H ↔ Additive.toMul y ∈ H :=
  Iff.rfl

/-- A strict chain `H_0 < H_1 < ... < H_t` of convex subgroups gives `t` elements of `H_t` that are linearly independent over `ℤ`. -/
theorem exists_linearIndependent_of_strictMono (t : ℕ) (f : Fin (t + 1) → Subgroup G)
    (hf : StrictMono f) (hc : ∀ i, IsConvexSubgroup (f i)) :
    ∃ v : Fin t → Additive G, LinearIndependent ℤ v ∧
      ∀ i, Additive.toMul (v i) ∈ f (Fin.last t) := by
  induction t with
  | zero => exact ⟨Fin.elim0, linearIndependent_empty_type, fun i => i.elim0⟩
  | succ t ih =>
    obtain ⟨v, hv, hvmem⟩ :=
      ih (f ∘ Fin.castSucc) (hf.comp Fin.strictMono_castSucc) (fun i => hc _)
    have hlt : f (Fin.castSucc (Fin.last t)) < f (Fin.last (t + 1)) :=
      hf (Fin.castSucc_lt_last _)
    obtain ⟨x, hx, hxn⟩ := IsConcreteLE.exists_of_lt hlt
    set H := f (Fin.castSucc (Fin.last t)) with hH
    have hδ : mabs x ∈ f (Fin.last (t + 1)) := (mabs_mem_iff _).mpr hx
    have hδn : mabs x ∉ H := fun h => hxn ((mabs_mem_iff _).mp h)
    have hspan : Submodule.span ℤ (Set.range v) ≤ subgroupToIntSubmodule H := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hvmem i
    refine ⟨Fin.cons (Additive.ofMul (mabs x)) v, ?_, ?_⟩
    · refine hv.finCons' _ _ fun c y hy hsum => ?_
      by_contra hc0
      have hneg : c • Additive.ofMul (mabs x) = -y := eq_neg_of_add_eq_zero_left hsum
      have hmem : c • Additive.ofMul (mabs x) ∈ subgroupToIntSubmodule H := by
        rw [hneg]
        exact Submodule.neg_mem _ (hspan hy)
      rw [mem_subgroupToIntSubmodule, toMul_zsmul, toMul_ofMul] at hmem
      exact hδn ((hc _).mem_of_zpow_mem (one_le_mabs x) hc0 hmem)
    · intro i
      induction i using Fin.cases with
      | zero =>
        rw [Fin.cons_zero, toMul_ofMul]
        exact hδ
      | succ j =>
        rw [Fin.cons_succ]
        exact hlt.le (hvmem j)

/-- A strict chain `H_0 < H_1 < ... < H_t` of convex subgroups has `t ≤ r`, where `r` is the rational rank of `G`. -/
theorem le_of_strictMono {r : ℕ} (hr : Module.rank ℚ (ℚ ⊗[ℤ] Additive G) = r) (t : ℕ)
    (f : Fin (t + 1) → Subgroup G) (hf : StrictMono f) (hc : ∀ i, IsConvexSubgroup (f i)) :
    t ≤ r := by
  obtain ⟨v, hv, -⟩ := exists_linearIndependent_of_strictMono t f hf hc
  rw [(TensorProduct.isBaseChange ℤ (Additive G) ℚ).rank_eq] at hr
  have h := hv.cardinal_lift_le_rank
  rw [Cardinal.mk_fin, hr, Cardinal.lift_natCast, Cardinal.lift_natCast] at h
  exact_mod_cast h

/-- Let `G` be an ordered group of rational rank `r < ∞`. Then `G` has only finitely many convex subgroups, and their number is at most `r + 1` (Volume 3, Proposition 1.2.5 of the handbook). The rational rank is the dimension of `ℚ ⊗ G` over `ℚ`. -/
theorem IsConvexSubgroup.finite_and_card_le {r : ℕ}
    (hr : Module.rank ℚ (ℚ ⊗[ℤ] Additive G) = r) :
    Finite {H : Subgroup G // IsConvexSubgroup H} ∧
      Nat.card {H : Subgroup G // IsConvexSubgroup H} ≤ r + 1 := by
  classical
  letI : LinearOrder {H : Subgroup G // IsConvexSubgroup H} :=
    { (inferInstance : PartialOrder {H : Subgroup G // IsConvexSubgroup H}) with
      le_total := fun a b => a.2.le_or_le b.2
      toDecidableLE := Classical.decRel _ }
  have hcard : ∀ s : Finset {H : Subgroup G // IsConvexSubgroup H}, s.card ≤ r + 1 := by
    intro s
    rcases hs : s.card with _ | t
    · exact Nat.zero_le _
    · let e := s.orderEmbOfFin hs
      have := le_of_strictMono hr t (fun i => (e i).1)
        (fun i j hij => show (e i).1 < (e j).1 from e.strictMono hij) (fun i => (e i).2)
      omega
  have hfin : Finite {H : Subgroup G // IsConvexSubgroup H} := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq {H : Subgroup G // IsConvexSubgroup H} (r + 2)
    have := hcard s
    omega
  refine ⟨hfin, ?_⟩
  have := Fintype.ofFinite {H : Subgroup G // IsConvexSubgroup H}
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  exact hcard _

end Singularity
