/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.RankDimension

/-!
# The coarsening of a valuation along a convex subgroup

Let `V` be a valuation ring of a field `K`, with valuation `v` and value group `Γ`, and let `Δ` be a convex subgroup of `Γ`. This file proves part 1 of Volume 3, Lemma 2.3.2 of the handbook, except for the isomorphism of value groups. The set `W = {x ∈ K | v(x) ≥ δ for some δ ∈ Δ}` is a valuation ring of `K` with `V ⊆ W`. An element `x ≠ 0` is a unit of `W` if and only if `v(x) ∈ Δ`, and the maximal ideal of `W` is `{x | v(x) > Δ}`.

Mathlib writes valuations multiplicatively, so `v(x) ≥ δ` of the handbook is `v x ≤ δ` here, and the value group is the group of units `V.ValueGroupˣ`. The convex subgroups are those of `Singularity.IsConvexSubgroup`, as in `Singularity.Valuation.RankDimension`. The maximal ideal of `W` is the prime ideal `idealOfSubgroup V Δ` of that file, seen in `K`.

The isomorphism `Γ_{v_W} ≅ Γ_v / Δ` of part 1 and part 2 of the lemma are not proved here.

## Main results

* `Singularity.coarsening`: the valuation ring `W`.
* `Singularity.le_coarsening`: `V ⊆ W`.
* `Singularity.mem_coarsening_and_inv_mem_iff`: `x` and `x⁻¹` are in `W` if and only if `v(x) ∈ Δ`.
* `Singularity.mem_nonunits_coarsening_iff`: `x` is in the maximal ideal of `W` if and only if `v(x) > Δ`.
-/

namespace Singularity

variable {K : Type*} [Field K] (V : ValuationSubring K)

/-- Let `H` be a subgroup of the value group of `V`. This is the subring of the `x ∈ K` with `v(x) ≤ h` for some `h ∈ H`. In the additive notation of the handbook it is the ring `W = {x | v(x) ≥ δ for some δ ∈ Δ}` (Volume 3, Lemma 2.3.2 of the handbook). -/
def coarseningSubring (H : Subgroup V.ValueGroupˣ) : Subring K where
  carrier := {x | ∃ h ∈ H, V.valuation x ≤ ((h : V.ValueGroupˣ) : V.ValueGroup)}
  zero_mem' := by
    show ∃ h ∈ H, V.valuation (0 : K) ≤ ((h : V.ValueGroupˣ) : V.ValueGroup)
    refine ⟨1, H.one_mem, ?_⟩
    rw [Valuation.map_zero]
    exact (Units.zero_lt _).le
  one_mem' := by
    show ∃ h ∈ H, V.valuation (1 : K) ≤ ((h : V.ValueGroupˣ) : V.ValueGroup)
    refine ⟨1, H.one_mem, ?_⟩
    rw [Valuation.map_one, Units.val_one]
  add_mem' := by
    intro a b ha hb
    have ha' : ∃ h ∈ H, V.valuation a ≤ ((h : V.ValueGroupˣ) : V.ValueGroup) := ha
    have hb' : ∃ h ∈ H, V.valuation b ≤ ((h : V.ValueGroupˣ) : V.ValueGroup) := hb
    show ∃ h ∈ H, V.valuation (a + b) ≤ ((h : V.ValueGroupˣ) : V.ValueGroup)
    obtain ⟨h₁, hh₁, ha₁⟩ := ha'
    obtain ⟨h₂, hh₂, hb₂⟩ := hb'
    rcases le_total h₁ h₂ with h12 | h21
    · exact ⟨h₂, hh₂, (V.valuation.map_add a b).trans
        (max_le (ha₁.trans (Units.val_le_val.mpr h12)) hb₂)⟩
    · exact ⟨h₁, hh₁, (V.valuation.map_add a b).trans
        (max_le ha₁ (hb₂.trans (Units.val_le_val.mpr h21)))⟩
  mul_mem' := by
    intro a b ha hb
    have ha' : ∃ h ∈ H, V.valuation a ≤ ((h : V.ValueGroupˣ) : V.ValueGroup) := ha
    have hb' : ∃ h ∈ H, V.valuation b ≤ ((h : V.ValueGroupˣ) : V.ValueGroup) := hb
    show ∃ h ∈ H, V.valuation (a * b) ≤ ((h : V.ValueGroupˣ) : V.ValueGroup)
    obtain ⟨h₁, hh₁, ha₁⟩ := ha'
    obtain ⟨h₂, hh₂, hb₂⟩ := hb'
    refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, ?_⟩
    rw [Valuation.map_mul, Units.val_mul]
    exact mul_le_mul' ha₁ hb₂
  neg_mem' := by
    intro a ha
    have ha' : ∃ h ∈ H, V.valuation a ≤ ((h : V.ValueGroupˣ) : V.ValueGroup) := ha
    show ∃ h ∈ H, V.valuation (-a) ≤ ((h : V.ValueGroupˣ) : V.ValueGroup)
    rw [Valuation.map_neg]
    exact ha'

theorem mem_coarseningSubring {H : Subgroup V.ValueGroupˣ} {x : K} :
    x ∈ coarseningSubring V H ↔ ∃ h ∈ H, V.valuation x ≤ ((h : V.ValueGroupˣ) : V.ValueGroup) :=
  Iff.rfl

/-- The ring `V` lies in `coarseningSubring V H`. -/
theorem le_coarseningSubring (H : Subgroup V.ValueGroupˣ) :
    V.toSubring ≤ coarseningSubring V H := by
  intro x hx
  rw [mem_coarseningSubring]
  refine ⟨1, H.one_mem, ?_⟩
  rw [Units.val_one]
  exact (V.valuation_le_one_iff x).mpr hx

/-- The coarsening of `V` along `H`: the ring `W = {x | v(x) ≤ h for some h ∈ H}`. It contains `V`, so it is a valuation ring (Volume 3, Lemma 2.3.2, part 1 of the handbook). -/
def coarsening (H : Subgroup V.ValueGroupˣ) : ValuationSubring K :=
  V.ofLE (coarseningSubring V H) (le_coarseningSubring V H)

theorem mem_coarsening {H : Subgroup V.ValueGroupˣ} {x : K} :
    x ∈ coarsening V H ↔ ∃ h ∈ H, V.valuation x ≤ ((h : V.ValueGroupˣ) : V.ValueGroup) :=
  Iff.rfl

/-- The valuation ring `V` lies in its coarsening `W` (Volume 3, Lemma 2.3.2, part 1 of the handbook). -/
theorem le_coarsening (H : Subgroup V.ValueGroupˣ) : V ≤ coarsening V H :=
  fun _ hx => le_coarseningSubring V H hx

/-- **The units of the coarsening** (Volume 3, Lemma 2.3.2, part 1 of the handbook). Let `H` be a convex subgroup and let `x ≠ 0`. Then `x` and `x⁻¹` are in `W`, that is, `x` is a unit of `W`, if and only if `v(x) ∈ H`. -/
theorem mem_coarsening_and_inv_mem_iff {H : Subgroup V.ValueGroupˣ} (hH : IsConvexSubgroup H)
    {x : K} (hx : x ≠ 0) :
    (x ∈ coarsening V H ∧ x⁻¹ ∈ coarsening V H) ↔
      ∃ γ ∈ H, V.valuation x = ((γ : V.ValueGroupˣ) : V.ValueGroup) := by
  have hx0 : V.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  set γ : V.ValueGroupˣ := Units.mk0 _ hx0
  have hvx : V.valuation x = (γ : V.ValueGroup) := (Units.val_mk0 hx0).symm
  have hvx' : V.valuation x⁻¹ = ((γ⁻¹ : V.ValueGroupˣ) : V.ValueGroup) := by
    rw [map_inv₀, hvx, Units.val_inv_eq_inv_val]
  rw [mem_coarsening, mem_coarsening, hvx, hvx']
  constructor
  · rintro ⟨⟨h₁, hh₁, h1⟩, ⟨h₂, hh₂, h2⟩⟩
    refine ⟨γ, ?_, rfl⟩
    rw [Units.val_le_val] at h1 h2
    rcases le_total 1 γ with hγ1 | hγ1
    · exact hH hγ1 h1 hh₁
    · exact inv_mem_iff.mp (hH (one_le_inv'.mpr hγ1) h2 hh₂)
  · rintro ⟨δ, hδ, hγδ⟩
    have hγδ' : γ = δ := Units.ext hγδ
    rw [hγδ']
    exact ⟨⟨δ, hδ, le_rfl⟩, ⟨δ⁻¹, H.inv_mem hδ, le_rfl⟩⟩

/-- **The maximal ideal of the coarsening** (Volume 3, Lemma 2.3.2, part 1 of the handbook). An element `x` is in the maximal ideal of `W` if and only if `v(x) < h` for each `h ∈ H`. In the additive notation of the handbook this is the condition `v(x) > Δ`, so the maximal ideal of `W` is the prime `𝔭 = idealOfSubgroup V H`. -/
theorem mem_nonunits_coarsening_iff (H : Subgroup V.ValueGroupˣ) {x : K} :
    x ∈ (coarsening V H).nonunits ↔
      ∀ h ∈ H, V.valuation x < ((h : V.ValueGroupˣ) : V.ValueGroup) := by
  rw [ValuationSubring.mem_nonunits_iff_or]
  by_cases hx : x = 0
  · subst hx
    refine iff_of_true (Or.inl rfl) fun h _ => ?_
    rw [Valuation.map_zero]
    exact Units.zero_lt h
  · have hx0 : V.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    set γ : V.ValueGroupˣ := Units.mk0 _ hx0
    have hvx : V.valuation x = (γ : V.ValueGroup) := (Units.val_mk0 hx0).symm
    have hvx' : V.valuation x⁻¹ = ((γ⁻¹ : V.ValueGroupˣ) : V.ValueGroup) := by
      rw [map_inv₀, hvx, Units.val_inv_eq_inv_val]
    rw [or_iff_right hx, mem_coarsening, hvx', hvx]
    push_neg
    constructor
    · intro hlt h hh
      have h1 := hlt h⁻¹ (H.inv_mem hh)
      rw [Units.val_lt_val] at h1
      rw [Units.val_lt_val]
      exact inv_lt_inv_iff.mp h1
    · intro hlt h hh
      have h1 := hlt h⁻¹ (H.inv_mem hh)
      rw [Units.val_lt_val] at h1
      rw [Units.val_lt_val]
      have h2 := inv_lt_inv_iff.mpr h1
      rwa [inv_inv] at h2

end Singularity
