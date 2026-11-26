/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# The first properties of a valuation ring

This file collects the properties of a valuation ring `V` of a field `K` of Volume 3, Lemma 1.1.8 of the handbook in one statement.

1. Each ring `W` with `V ⊆ W ⊆ K` is a valuation ring of `K`. Mathlib has this as `ValuationSubring.ofLE`.
2. The ideals of `V` are totally ordered by inclusion. Mathlib has this as `ValuationRing.le_total_ideal`.
3. Each finitely generated ideal of `V` is principal. A valuation ring is a Bezout ring in Mathlib, and this is `IsBezout.isPrincipal_of_FG`.
4. The ring `V` is integrally closed. Mathlib has this as an instance in `Mathlib.RingTheory.Valuation.LocalSubring`.
5. If `V` is Noetherian and `V ≠ K`, then `V` is a discrete valuation ring. The proof uses `IsDiscreteValuationRing.TFAE`: a Noetherian local domain that is not a field is a discrete valuation ring if and only if it is a valuation ring.

The handbook also states in part 5 that the value group is isomorphic to `ℤ`. This file does not prove that claim.

## Main results

* `Singularity.not_isField_of_ne_top`: a valuation ring `V ≠ K` is not a field.
* `Singularity.valuationSubring_properties`: the five properties in one statement.
-/

namespace Singularity

variable {K : Type*} [Field K]

/-- A valuation ring `V` of `K` with `V ≠ K` is not a field. -/
theorem not_isField_of_ne_top {V : ValuationSubring K} (hV : V ≠ ⊤) : ¬IsField V := by
  intro hF
  apply hV
  rw [eq_top_iff]
  intro x _
  rcases V.mem_or_inv_mem x with hx | hx
  · exact hx
  · by_cases h0 : x = 0
    · rw [h0]
      exact V.zero_mem
    · have hne : (⟨x⁻¹, hx⟩ : V) ≠ 0 := by
        intro h
        have h' : (x⁻¹ : K) = 0 := congrArg Subtype.val h
        exact h0 (inv_eq_zero.mp h')
      obtain ⟨y, hy⟩ := hF.mul_inv_cancel hne
      have hy' : (x⁻¹ : K) * y = 1 := congrArg Subtype.val hy
      rw [inv_mul_eq_one₀ h0] at hy'
      rw [hy']
      exact y.2

/-- **The first properties of a valuation ring** (Volume 3, Lemma 1.1.8 of the handbook). Let `V` be a valuation ring of `K`.

1. Each subring `W` of `K` with `V ⊆ W` is a valuation ring of `K`.
2. The ideals of `V` are totally ordered by inclusion.
3. Each finitely generated ideal of `V` is principal.
4. `V` is integrally closed.
5. If `V` is Noetherian and `V ≠ K`, then `V` is a discrete valuation ring.

The claim of the handbook that the value group is `ℤ` in part 5 is not part of this statement. -/
theorem valuationSubring_properties (V : ValuationSubring K) :
    (∀ W : Subring K, V.toSubring ≤ W → ∃ W' : ValuationSubring K, W'.toSubring = W) ∧
      (∀ I J : Ideal V, I ≤ J ∨ J ≤ I) ∧
      (∀ I : Ideal V, I.FG → I.IsPrincipal) ∧
      IsIntegrallyClosed V ∧
      (IsNoetherianRing V → V ≠ ⊤ → IsDiscreteValuationRing V) := by
  refine ⟨fun W hW => ⟨V.ofLE W hW, rfl⟩,
    fun I J => Std.Total.total (r := fun I J : Ideal V => I ≤ J) I J,
    fun I hI => IsBezout.isPrincipal_of_FG I hI, inferInstance, fun hN hV => ?_⟩
  exact ((IsDiscreteValuationRing.TFAE V (not_isField_of_ne_top hV)).out 2 1).mp (inferInstance : ValuationRing V)

end Singularity
