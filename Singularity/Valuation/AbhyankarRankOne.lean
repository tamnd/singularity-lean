/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.AbhyankarValueGroup

/-!
# An Abhyankar valuation of rational rank one is discrete

Let `V` be an Abhyankar valuation of a function field `K/k`. Assume that the value group `Γ` has rational rank `1`. This file proves that `Γ` is isomorphic to `ℤ` as an ordered group (Volume 3, Corollary 2.2.4 of the handbook, the last claim).

The proof is short. The group `Γ` is free with a basis of `1` element (`Singularity.IsAbhyankarValuation.exists_basis_valueGroup`). So there is a group isomorphism `Γ ≅ ℤ`. A group isomorphism from an ordered group to `ℤ` either keeps the order or reverses it. In the second case, compose it with `n ↦ -n`.

Mathlib writes the value group multiplicatively. So `ℤ` is `Multiplicative ℤ` here.

## Main results

* `Singularity.IsAbhyankarValuation.nonempty_orderMonoidIso_units_valueGroup`: the value group is order isomorphic to `ℤ`.
* `Singularity.nonempty_orderMonoidIso_multiplicativeInt`: an ordered group that is isomorphic to `ℤ` as a group is isomorphic to `ℤ` as an ordered group.
-/

open IsLocalRing TensorProduct

namespace Singularity

section Ordered

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]

/-- A group isomorphism `f : G ≅ ℤ` keeps the order if the inverse image of `1` is positive. -/
theorem map_le_map_iff_of_mulEquiv_multiplicativeInt (f : G ≃* Multiplicative ℤ)
    (hf : 1 < f.symm (Multiplicative.ofAdd 1)) (a b : G) : f a ≤ f b ↔ a ≤ b := by
  have hpow : ∀ x : G, f.symm (Multiplicative.ofAdd 1) ^ Multiplicative.toAdd (f x) = x := by
    intro x
    rw [← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd, MulEquiv.symm_apply_apply]
  calc f a ≤ f b ↔ Multiplicative.toAdd (f a) ≤ Multiplicative.toAdd (f b) := Iff.rfl
    _ ↔ f.symm (Multiplicative.ofAdd 1) ^ Multiplicative.toAdd (f a) ≤
        f.symm (Multiplicative.ofAdd 1) ^ Multiplicative.toAdd (f b) :=
      (zpow_le_zpow_iff_right hf).symm
    _ ↔ a ≤ b := by rw [hpow, hpow]

/-- An ordered group that is isomorphic to `ℤ` as a group is isomorphic to `ℤ` as an ordered group. -/
theorem nonempty_orderMonoidIso_multiplicativeInt (f : G ≃* Multiplicative ℤ) :
    Nonempty (G ≃*o Multiplicative ℤ) := by
  have hne : f.symm (Multiplicative.ofAdd 1) ≠ 1 := by
    intro h
    have h1 : Multiplicative.ofAdd (1 : ℤ) = 1 := by
      rw [← MulEquiv.apply_symm_apply f (Multiplicative.ofAdd 1), h, map_one]
    exact one_ne_zero (ofAdd_eq_one.mp h1)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · let f' : G ≃* Multiplicative ℤ := f.trans (MulEquiv.inv (Multiplicative ℤ))
    have hf' : ∀ x, f' x = (f x)⁻¹ := fun x => rfl
    have hsymm : f'.symm (Multiplicative.ofAdd 1) = (f.symm (Multiplicative.ofAdd 1))⁻¹ :=
      f'.injective (by
        rw [MulEquiv.apply_symm_apply, hf', map_inv, inv_inv, MulEquiv.apply_symm_apply])
    have hpos : 1 < f'.symm (Multiplicative.ofAdd 1) := by
      rw [hsymm]
      exact one_lt_inv'.mpr hlt
    exact ⟨{ f' with
      map_le_map_iff' := fun {a b} => map_le_map_iff_of_mulEquiv_multiplicativeInt f' hpos a b }⟩
  · exact ⟨{ f with
      map_le_map_iff' := fun {a b} => map_le_map_iff_of_mulEquiv_multiplicativeInt f hgt a b }⟩

/-- An ordered group `G` with a basis of `1` element over `ℤ` is isomorphic to `ℤ` as an ordered group. -/
theorem nonempty_orderMonoidIso_of_basis (b : Module.Basis (Fin 1) ℤ (Additive G)) :
    Nonempty (G ≃*o Multiplicative ℤ) := by
  let e : Additive G ≃ₗ[ℤ] ℤ := b.equivFun.trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ)
  let f : G ≃* Multiplicative ℤ :=
    { toFun := fun x => Multiplicative.ofAdd (e (Additive.ofMul x))
      invFun := fun n => Additive.toMul (e.symm (Multiplicative.toAdd n))
      left_inv := fun x => by simp
      right_inv := fun n => by simp
      map_mul' := fun x y => by rw [ofMul_mul, map_add, ofAdd_add] }
  exact nonempty_orderMonoidIso_multiplicativeInt f

end Ordered

section ValueGroup

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable {V : ValuationSubring K} [Algebra k V] [IsScalarTower k V K]

/-- Let `V` be an Abhyankar valuation of a function field `K/k` with rational rank `1`. Then the value group of `V` is isomorphic to `ℤ` as an ordered group (Volume 3, Corollary 2.2.4 of the handbook, the last claim). Mathlib writes the value group multiplicatively, so its nonzero elements form the group `V.ValueGroupˣ` and `ℤ` is `Multiplicative ℤ`. -/
theorem IsAbhyankarValuation.nonempty_orderMonoidIso_units_valueGroup (hK : IsFunctionField k K)
    (hV : IsAbhyankarValuation k V)
    (hr : Module.rank ℚ (ℚ ⊗[ℤ] Additive V.ValueGroupˣ) = 1) :
    Nonempty (V.ValueGroupˣ ≃*o Multiplicative ℤ) := by
  obtain ⟨b⟩ := hV.exists_basis_valueGroup hK (r := 1) (by rw [hr, Nat.cast_one])
  exact nonempty_orderMonoidIso_of_basis b

end ValueGroup

end Singularity
