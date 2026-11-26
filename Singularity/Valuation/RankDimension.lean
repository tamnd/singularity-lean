/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Group.Units
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Singularity.Valuation.Abhyankar
import Singularity.Valuation.ConvexSubgroup

/-!
# The dimension of a valuation ring is the rank of the valuation

Let `V` be a valuation ring of a field `K`, with valuation `v` and value group `Γ`. This file proves two results of the handbook.

1. If `Γ` has only finitely many convex subgroups, then `dim V` is the rank of `v`, that is, the number of convex subgroups minus one (Volume 3, Corollary 1.2.4 of the handbook).
2. Let `K/k` be a field extension of transcendence degree `d < ∞`, and let `V` contain `k`. Then the rational rank of `v`, the dimension of `v`, the rank of `v` and `dim V` are at most `d` (Volume 3, Corollary 2.1.6 of the handbook).

Mathlib writes valuations multiplicatively, so `v(x) > δ` of the handbook is `v x < δ` here, and the value group is the group of units `V.ValueGroupˣ`. The proof of the first result follows the handbook. A prime `P` gives the convex subgroup of the `γ` with `v(x) ≤ γ` and `v(x) ≤ γ⁻¹` for some `x ∈ V` outside `P` (`Singularity.subgroupOfIdeal`). A subgroup `H` gives the prime ideal of the `x ∈ V` with `v(x) < h` for each `h ∈ H` (`Singularity.idealOfSubgroup`). These maps are inverse bijections (Volume 3, Proposition 1.2.3 of the handbook). The prime ideals form a chain, so the length of the longest chain is the number of primes minus one.

The handbook assumes that `K/k` is a function field in the second result. The proof here uses only that `trdeg_k K` is finite.

## Main results

* `Singularity.primeSpectrumEquivConvexSubgroup`: the bijection between the primes of `V` and the convex subgroups of the value group.
* `Singularity.ringKrullDim_eq_natCard_convexSubgroup_sub_one`: `dim V` is the number of convex subgroups minus one.
* `Singularity.rank_le_and_ringKrullDim_le_trdeg`: the four invariants are at most `trdeg_k K`.
-/

namespace Singularity

section Order

/-- Let `α` be a finite nonempty partial order in which two elements are always comparable. Then the Krull dimension of `α` is the number of elements of `α` minus one. -/
theorem krullDim_eq_natCard_sub_one {α : Type*} [PartialOrder α] [Finite α] [Nonempty α]
    (h : ∀ a b : α, a ≤ b ∨ b ≤ a) :
    Order.krullDim α = ((Nat.card α - 1 : ℕ) : WithBot ℕ∞) := by
  classical
  letI : LinearOrder α :=
    { (inferInstance : PartialOrder α) with
      le_total := h
      toDecidableLE := Classical.decRel _ }
  letI := Fintype.ofFinite α
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.card α = m + 1 :=
    ⟨Nat.card α - 1, by have := Nat.card_pos (α := α); omega⟩
  have hc : Fintype.card α = m + 1 := by rw [← Nat.card_eq_fintype_card, hm]
  rw [hm, Nat.add_sub_cancel]
  apply le_antisymm
  · have hlt : Order.krullDim α < ((m + 1 : ℕ) : WithBot ℕ∞) :=
      Order.krullDim_lt_coe_iff.mpr fun l => by
        rw [← hc]
        exact l.length_lt_card
    rw [Nat.cast_add, Nat.cast_one] at hlt
    exact ENat.WithBot.lt_add_one_iff.mp hlt
  · let e := Fintype.orderIsoFinOfCardEq α hc
    exact Order.le_krullDim_iff.mpr ⟨LTSeries.mk m (fun i => e i) e.strictMono, rfl⟩

end Order

section ValuationSubring

variable {K : Type*} [Field K] (V : ValuationSubring K)

/-- Let `H` be a subgroup of the value group of `V`. This is the ideal of the `x ∈ V` with `v(x) < h` for each `h ∈ H`. In the additive notation of the handbook it is the ideal `𝔭_Δ = {x ∈ V | v(x) > δ for each δ ∈ Δ}` (Volume 3, Proposition 1.2.3 of the handbook). -/
def idealOfSubgroup (H : Subgroup V.ValueGroupˣ) : Ideal V where
  carrier := {x | ∀ h ∈ H, V.valuation (x : K) < ((h : V.ValueGroupˣ) : V.ValueGroup)}
  add_mem' := by
    intro a b ha hb
    have ha' : ∀ h ∈ H, V.valuation (a : K) < ((h : V.ValueGroupˣ) : V.ValueGroup) := ha
    have hb' : ∀ h ∈ H, V.valuation (b : K) < ((h : V.ValueGroupˣ) : V.ValueGroup) := hb
    show ∀ h ∈ H, V.valuation ((a : K) + b) < ((h : V.ValueGroupˣ) : V.ValueGroup)
    intro h hh
    exact (V.valuation.map_add _ _).trans_lt (max_lt (ha' h hh) (hb' h hh))
  zero_mem' := by
    show ∀ h ∈ H, V.valuation ((0 : V) : K) < ((h : V.ValueGroupˣ) : V.ValueGroup)
    intro h _
    rw [ZeroMemClass.coe_zero, Valuation.map_zero]
    exact Units.zero_lt h
  smul_mem' := by
    intro c a ha
    have ha' : ∀ h ∈ H, V.valuation (a : K) < ((h : V.ValueGroupˣ) : V.ValueGroup) := ha
    show ∀ h ∈ H, V.valuation ((c : K) * a) < ((h : V.ValueGroupˣ) : V.ValueGroup)
    intro h hh
    rw [Valuation.map_mul]
    exact (mul_le_of_le_one_left' (V.valuation_le_one c)).trans_lt (ha' h hh)

theorem mem_idealOfSubgroup (H : Subgroup V.ValueGroupˣ) (x : V) :
    x ∈ idealOfSubgroup V H ↔
      ∀ h ∈ H, V.valuation (x : K) < ((h : V.ValueGroupˣ) : V.ValueGroup) :=
  Iff.rfl

instance isPrime_idealOfSubgroup (H : Subgroup V.ValueGroupˣ) : (idealOfSubgroup V H).IsPrime where
  ne_top' := by
    rw [Ideal.ne_top_iff_one, mem_idealOfSubgroup]
    intro h1
    have h := h1 1 H.one_mem
    rw [OneMemClass.coe_one, Valuation.map_one, Units.val_one] at h
    exact lt_irrefl _ h
  mem_or_mem' := by
    intro a b hab
    by_contra hn
    rw [not_or, mem_idealOfSubgroup, mem_idealOfSubgroup] at hn
    push_neg at hn
    obtain ⟨⟨h₁, hh₁, ha⟩, ⟨h₂, hh₂, hb⟩⟩ := hn
    have h := (mem_idealOfSubgroup V H _).mp hab (h₁ * h₂) (H.mul_mem hh₁ hh₂)
    rw [MulMemClass.coe_mul, Valuation.map_mul, Units.val_mul] at h
    exact not_le.mpr h (mul_le_mul' ha hb)

/-- Let `P` be a prime ideal of `V`. This is the subgroup of the `γ` in the value group with `v(x) ≤ γ` and `v(x) ≤ γ⁻¹` for some `x ∈ V` outside `P`. In the additive notation of the handbook it is the subgroup `Δ_𝔭` of the values `± v(x)` with `x ∈ V \ 𝔭` (Volume 3, Proposition 1.2.3 of the handbook). -/
def subgroupOfIdeal (P : Ideal V) [P.IsPrime] : Subgroup V.ValueGroupˣ where
  carrier := {γ | ∃ x : V, x ∉ P ∧ V.valuation (x : K) ≤ ((γ : V.ValueGroupˣ) : V.ValueGroup) ∧
    V.valuation (x : K) ≤ ((γ⁻¹ : V.ValueGroupˣ) : V.ValueGroup)}
  one_mem' := by
    refine ⟨1, (Ideal.ne_top_iff_one P).mp ‹P.IsPrime›.ne_top, ?_, ?_⟩
    · rw [OneMemClass.coe_one, Valuation.map_one, Units.val_one]
    · rw [OneMemClass.coe_one, Valuation.map_one, inv_one, Units.val_one]
  mul_mem' := by
    rintro a b ⟨x, hx, hxa, hxa'⟩ ⟨y, hy, hyb, hyb'⟩
    refine ⟨x * y, fun h => (‹P.IsPrime›.mem_or_mem h).elim hx hy, ?_, ?_⟩
    · rw [MulMemClass.coe_mul, Valuation.map_mul, Units.val_mul]
      exact mul_le_mul' hxa hyb
    · rw [MulMemClass.coe_mul, Valuation.map_mul, mul_inv, Units.val_mul]
      exact mul_le_mul' hxa' hyb'
  inv_mem' := by
    rintro a ⟨x, hx, hxa, hxa'⟩
    refine ⟨x, hx, hxa', ?_⟩
    rw [inv_inv]
    exact hxa

theorem mem_subgroupOfIdeal (P : Ideal V) [P.IsPrime] (γ : V.ValueGroupˣ) :
    γ ∈ subgroupOfIdeal V P ↔ ∃ x : V, x ∉ P ∧
      V.valuation (x : K) ≤ ((γ : V.ValueGroupˣ) : V.ValueGroup) ∧
        V.valuation (x : K) ≤ ((γ⁻¹ : V.ValueGroupˣ) : V.ValueGroup) :=
  Iff.rfl

/-- The subgroup `subgroupOfIdeal V P` is convex. -/
theorem isConvexSubgroup_subgroupOfIdeal (P : Ideal V) [P.IsPrime] :
    IsConvexSubgroup (subgroupOfIdeal V P) := by
  intro a b ha hab hb
  obtain ⟨x, hx, -, hxb'⟩ := (mem_subgroupOfIdeal V P b).mp hb
  refine (mem_subgroupOfIdeal V P a).mpr ⟨x, hx, ?_, ?_⟩
  · exact (V.valuation_le_one x).trans (Units.val_le_val.mpr ha)
  · exact hxb'.trans (Units.val_le_val.mpr (inv_le_inv_iff.mpr hab))

/-- The map `subgroupOfIdeal` followed by `idealOfSubgroup` is the identity on prime ideals. -/
theorem idealOfSubgroup_subgroupOfIdeal (P : Ideal V) [P.IsPrime] :
    idealOfSubgroup V (subgroupOfIdeal V P) = P := by
  ext x
  rw [mem_idealOfSubgroup]
  constructor
  · intro h
    by_contra hx
    have hx0 : V.valuation (x : K) ≠ 0 := by
      intro h0
      have hx0' : x = 0 := Subtype.ext ((Valuation.zero_iff _).mp h0)
      exact hx (hx0' ▸ P.zero_mem)
    have h1 : Units.mk0 _ hx0 ≤ 1 := by
      rw [← Units.val_le_val, Units.val_mk0, Units.val_one]
      exact V.valuation_le_one x
    have h2 : V.valuation (x : K) ≤ (((Units.mk0 _ hx0)⁻¹ : V.ValueGroupˣ) : V.ValueGroup) := by
      calc V.valuation (x : K) = ((Units.mk0 _ hx0 : V.ValueGroupˣ) : V.ValueGroup) :=
            (Units.val_mk0 hx0).symm
        _ ≤ _ := Units.val_le_val.mpr (h1.trans (one_le_inv'.mpr h1))
    have h3 := h (Units.mk0 _ hx0)
      ((mem_subgroupOfIdeal V P _).mpr ⟨x, hx, (Units.val_mk0 hx0).ge, h2⟩)
    rw [Units.val_mk0] at h3
    exact lt_irrefl _ h3
  · intro hx γ hγ
    obtain ⟨y, hy, hyγ, -⟩ := (mem_subgroupOfIdeal V P γ).mp hγ
    by_contra hle
    rw [not_lt] at hle
    obtain ⟨a, ha⟩ := (V.valuation_le_iff (y : K) (x : K)).mp (hyγ.trans hle)
    have hya : y = a * x := Subtype.ext (by rw [MulMemClass.coe_mul]; exact ha.symm)
    exact hy (hya ▸ P.mul_mem_left a hx)

/-- The map `idealOfSubgroup` followed by `subgroupOfIdeal` is the identity on convex subgroups. -/
theorem subgroupOfIdeal_idealOfSubgroup {H : Subgroup V.ValueGroupˣ} (hH : IsConvexSubgroup H) :
    subgroupOfIdeal V (idealOfSubgroup V H) = H := by
  ext γ
  rw [mem_subgroupOfIdeal]
  constructor
  · rintro ⟨x, hx, hxγ, hxγ'⟩
    rw [mem_idealOfSubgroup] at hx
    push_neg at hx
    obtain ⟨h, hh, hhx⟩ := hx
    have h1 : h ≤ γ := Units.val_le_val.mp (hhx.trans hxγ)
    have h2 : h ≤ γ⁻¹ := Units.val_le_val.mp (hhx.trans hxγ')
    have h3 : γ⁻¹⁻¹ ≤ h⁻¹ := inv_le_inv_iff.mpr h2
    rw [inv_inv] at h3
    have hle : mabs γ ≤ h⁻¹ := mabs_le'.mpr ⟨h3, inv_le_inv_iff.mpr h1⟩
    exact (mabs_mem_iff H).mp (hH (one_le_mabs γ) hle (H.inv_mem hh))
  · intro hγ
    obtain ⟨z, hz⟩ := V.valuation_surjective (((mabs γ)⁻¹ : V.ValueGroupˣ) : V.ValueGroup)
    have hzV : z ∈ V := by
      rw [← V.valuation_le_one_iff, hz, ← Units.val_one, Units.val_le_val]
      exact inv_le_one'.mpr (one_le_mabs γ)
    refine ⟨⟨z, hzV⟩, ?_, ?_, ?_⟩
    · rw [mem_idealOfSubgroup]
      push_neg
      exact ⟨(mabs γ)⁻¹, H.inv_mem ((mabs_mem_iff H).mpr hγ), hz.ge⟩
    · show V.valuation z ≤ _
      rw [hz, Units.val_le_val]
      have h3 : (mabs γ)⁻¹ ≤ γ⁻¹⁻¹ := inv_le_inv_iff.mpr (inv_le_mabs γ)
      rwa [inv_inv] at h3
    · show V.valuation z ≤ _
      rw [hz, Units.val_le_val]
      exact inv_le_inv_iff.mpr (le_mabs_self γ)

/-- **Primes and convex subgroups** (Volume 3, Proposition 1.2.3 of the handbook). The prime ideals of `V` are in bijection with the convex subgroups of the value group. The prime `P` goes to `subgroupOfIdeal V P`, and the convex subgroup `H` goes to `idealOfSubgroup V H`. -/
def primeSpectrumEquivConvexSubgroup :
    PrimeSpectrum V ≃ {H : Subgroup V.ValueGroupˣ // IsConvexSubgroup H} where
  toFun P := ⟨subgroupOfIdeal V P.asIdeal, isConvexSubgroup_subgroupOfIdeal V P.asIdeal⟩
  invFun H := ⟨idealOfSubgroup V H.1, inferInstance⟩
  left_inv P := PrimeSpectrum.ext (idealOfSubgroup_subgroupOfIdeal V P.asIdeal)
  right_inv H := Subtype.ext (subgroupOfIdeal_idealOfSubgroup V H.2)

/-- **The dimension of a valuation ring is the rank** (Volume 3, Corollary 1.2.4 of the handbook). Let the value group of `V` have only finitely many convex subgroups. Then the Krull dimension of `V` is the number of convex subgroups minus one. This number is the rank of the valuation, because the rank counts the convex subgroups other than the whole group. -/
theorem ringKrullDim_eq_natCard_convexSubgroup_sub_one
    [Finite {H : Subgroup V.ValueGroupˣ // IsConvexSubgroup H}] :
    ringKrullDim V =
      ((Nat.card {H : Subgroup V.ValueGroupˣ // IsConvexSubgroup H} - 1 : ℕ) : WithBot ℕ∞) := by
  have : Finite (PrimeSpectrum V) := Finite.of_equiv _ (primeSpectrumEquivConvexSubgroup V).symm
  rw [← Nat.card_congr (primeSpectrumEquivConvexSubgroup V)]
  exact krullDim_eq_natCard_sub_one fun P Q =>
    Std.Total.total (r := fun I J : Ideal V => I ≤ J) P.asIdeal Q.asIdeal

/-- **Corollary 2.1.6 of Volume 3 of the handbook.** Let `K/k` be a field extension with `trdeg_k K = d < ∞`, and let `V` be a valuation ring of `K/k`. Then these invariants are at most `d`.

1. The rational rank of `v`, that is, the dimension of `ℚ ⊗ Γ` over `ℚ`.
2. The dimension of `v`, that is, the transcendence degree of the residue field over `k`.
3. The rank of `v`, that is, the number of convex subgroups minus one. The number of convex subgroups is finite.
4. The Krull dimension of `V`. -/
theorem rank_le_and_ringKrullDim_le_trdeg {k : Type*} [Field k] [Algebra k K] [Algebra k V]
    [IsScalarTower k V K] {d : ℕ} (hd : Algebra.trdeg k K = d) :
    Module.rank ℚ (ℚ ⊗[ℤ] Additive V.ValueGroupˣ) ≤ d ∧
      Algebra.trdeg k (IsLocalRing.ResidueField V) ≤ d ∧
      Finite {H : Subgroup V.ValueGroupˣ // IsConvexSubgroup H} ∧
      Nat.card {H : Subgroup V.ValueGroupˣ // IsConvexSubgroup H} - 1 ≤ d ∧
      ringKrullDim V ≤ d := by
  have h := abhyankar_inequality V (k := k)
  rw [hd] at h
  have hrr : Module.rank ℚ (ℚ ⊗[ℤ] Additive V.ValueGroupˣ) ≤ d := le_self_add.trans h
  have htr : Algebra.trdeg k (IsLocalRing.ResidueField V) ≤ d := le_add_self.trans h
  obtain ⟨r, hr⟩ := Cardinal.lt_aleph0.mp (hrr.trans_lt Cardinal.natCast_lt_aleph0)
  have hrd : r ≤ d := by
    have h' := hrr
    rw [hr] at h'
    exact_mod_cast h'
  obtain ⟨hfin, hcard⟩ := IsConvexSubgroup.finite_and_card_le hr
  refine ⟨hrr, htr, hfin, by omega, ?_⟩
  rw [ringKrullDim_eq_natCard_convexSubgroup_sub_one V]
  exact Nat.cast_le.mpr (by omega)

end ValuationSubring

end Singularity
