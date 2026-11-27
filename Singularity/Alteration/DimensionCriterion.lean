/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib

/-!
# The algebraic core of the dimension criterion for alterations

This file proves Volume 8, Lemma 1.1.4 of the handbook in part. It proves the two algebraic
steps of the proof. It does not prove the scheme statement.

1. `Singularity.finiteDimensional_iff_trdeg_eq`: let `k ⊆ K ⊆ L` be fields, with `L` finitely
   generated as a field over `K`, and with `trdeg_k K` finite. Then `L` is finite over `K` if
   and only if `trdeg_k L = trdeg_k K`. This is the step "the function fields have the same
   transcendence degree if and only if the extension is finite".
2. `Singularity.exists_ne_zero_moduleFinite_localization`: the generic finiteness step. Let
   `A → B` be a map of rings with `A` a domain and `B` of finite type over `A`, such that each
   element of `B` is algebraic over `A`. Then there is `a ≠ 0` in `A` such that `B_a` is a
   finite `A_a`-module.
3. `Singularity.isAlgebraic_of_isFractionRing`: if `A → B` is injective and `Frac B` is
   algebraic over `Frac A`, then each element of `B` is algebraic over `A`. So the hypothesis
   of the second result holds in the setting of the handbook.

The passage from these algebraic facts to schemes is not in this file: the equality of the
dimension of an integral variety with the transcendence degree of its function field, and the
argument with the properness of the morphism, are not proved here.
-/

namespace Singularity

universe u

open Polynomial Cardinal

section TranscendenceDegree

variable (k : Type*) (K L : Type*) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
  [Algebra K L] [IsScalarTower k K L]

/-- A field extension that is finitely generated as a field is finite if and only if it is
algebraic. -/
theorem finiteDimensional_iff_isAlgebraic_of_fg (hfg : (⊤ : IntermediateField K L).FG) :
    FiniteDimensional K L ↔ Algebra.IsAlgebraic K L := by
  refine ⟨fun _ ↦ Algebra.IsAlgebraic.of_finite K L, fun _ ↦ ?_⟩
  obtain ⟨t, ht⟩ := hfg
  have : FiniteDimensional K (IntermediateField.adjoin K (t : Set L)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  rw [ht] at this
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

/-- Let `k ⊆ K ⊆ L` be fields with `L` finitely generated as a field over `K` and with
`trdeg_k K` finite. Then `L` is finite over `K` if and only if `trdeg_k L = trdeg_k K`. -/
theorem finiteDimensional_iff_trdeg_eq {K L : Type u} [Field K] [Field L] [Algebra k K]
    [Algebra k L] [Algebra K L] [IsScalarTower k K L] (hfg : (⊤ : IntermediateField K L).FG)
    (hK : Algebra.trdeg k K < ℵ₀) :
    FiniteDimensional K L ↔ Algebra.trdeg k L = Algebra.trdeg k K := by
  rw [finiteDimensional_iff_isAlgebraic_of_fg K L hfg, ← trdeg_eq_zero_iff,
    ← trdeg_add_eq (R := k) (S := K) (A := L), Cardinal.add_eq_left_iff]
  refine ⟨Or.inr, ?_⟩
  rintro (h | h)
  · exact absurd ((le_max_left _ _).trans h) (not_le.2 hK)
  · exact h

end TranscendenceDegree

section GenericFiniteness

variable {A B : Type u} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]

/-- Let `A` be a domain and let `s` be a finite set of elements of `B` that are algebraic over
`A`. Then there is `a ≠ 0` in `A` such that each element of `s` is integral over `A_a` in
`B_a`. One takes for `a` the product of the leading coefficients of the equations. -/
theorem exists_ne_zero_forall_isIntegral_localization (s : Finset B)
    (hs : ∀ x ∈ s, IsAlgebraic A x) :
    ∃ a : A, a ≠ 0 ∧ ∀ x ∈ s,
      IsIntegral (Localization.Away a)
        (algebraMap B (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers a))) x) := by
  classical
  let p : B → A[X] := fun x ↦ if h : IsAlgebraic A x then h.choose else 1
  have hp : ∀ x ∈ s, p x ≠ 0 ∧ aeval x (p x) = 0 := fun x hx ↦ by
    simp only [p, hs x hx, dite_true]
    exact (hs x hx).choose_spec
  refine ⟨∏ x ∈ s, (p x).leadingCoeff, ?_, fun x hx ↦ ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun x hx ↦ leadingCoeff_ne_zero.2 (hp x hx).1
  let q := p x * C (∏ y ∈ s.erase x, (p y).leadingCoeff)
  have hq : aeval x q = 0 := by simp [q, (hp x hx).2]
  have hlc : q.leadingCoeff = ∏ x ∈ s, (p x).leadingCoeff := by
    rw [leadingCoeff_mul, leadingCoeff_C]
    exact Finset.mul_prod_erase s (fun y ↦ (p y).leadingCoeff) hx
  exact is_integral_localization_at_leadingCoeff q hq (hlc ▸ Submonoid.mem_powers _)

/-- **Generic finiteness.** Let `A` be a domain and let `B` be an `A`-algebra of finite type
such that each element of `B` is algebraic over `A`. Then there is `a ≠ 0` in `A` such that
`B_a` is a finite `A_a`-module. -/
theorem exists_ne_zero_moduleFinite_localization [Algebra.FiniteType A B]
    [Algebra.IsAlgebraic A B] :
    ∃ a : A, a ≠ 0 ∧ Module.Finite (Localization.Away a)
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers a))) := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B)
  obtain ⟨a, ha, hint⟩ := exists_ne_zero_forall_isIntegral_localization s
    fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic (R := A) x
  refine ⟨a, ha, ?_⟩
  set M := Submonoid.powers a
  set Rₘ := Localization.Away a
  set Sₘ := Localization (Algebra.algebraMapSubmonoid B M)
  have : IsLocalization (M.map (algebraMap A B)) Sₘ :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid B M) Sₘ)
  have hft : Algebra.FiniteType Rₘ Sₘ := by
    rw [← RingHom.finiteType_algebraMap]
    exact RingHom.finiteType_localizationPreserves (algebraMap A B) M Rₘ Sₘ
      (RingHom.finiteType_algebraMap.2 inferInstance)
  let T : Subalgebra A B :=
    ((integralClosure Rₘ Sₘ).restrictScalars A).comap (IsScalarTower.toAlgHom A B Sₘ)
  have hT : ∀ b : B, IsIntegral Rₘ (algebraMap B Sₘ b) := by
    have hle : Algebra.adjoin A (s : Set B) ≤ T := Algebra.adjoin_le_iff.2 fun x hx ↦ hint x hx
    intro b
    exact hle (hs ▸ Algebra.mem_top)
  have : Algebra.IsIntegral Rₘ Sₘ := by
    constructor
    intro y
    obtain ⟨⟨b, ⟨_, c, hc, rfl⟩⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid B M) y
    have h1 : IsLocalization.mk' Sₘ b
        ⟨algebraMap A B c, Algebra.mem_algebraMapSubmonoid_of_mem ⟨c, hc⟩⟩ =
        algebraMap B Sₘ b * algebraMap Rₘ Sₘ (IsLocalization.mk' Rₘ (1 : A) ⟨c, hc⟩) := by
      rw [IsLocalization.algebraMap_mk' (S := B), map_one, ← IsLocalization.mk'_one (M :=
        Algebra.algebraMapSubmonoid B M) Sₘ b, ← IsLocalization.mk'_mul, mul_one, one_mul]
    refine (congrArg (IsIntegral Rₘ) h1).mpr ?_
    exact (hT b).mul isIntegral_algebraMap
  exact Algebra.IsIntegral.finite

end GenericFiniteness

section FractionField

variable (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L] [Algebra K L]
  [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]

/-- Let `A → B` be a map of rings with `A` a domain and `B → L` injective, where `K` is the
fraction field of `A`. If `L` is algebraic over `K`, then each element of `B` is algebraic
over `A`. -/
theorem isAlgebraic_of_isFractionRing (hBL : Function.Injective (algebraMap B L))
    [Algebra.IsAlgebraic K L] : Algebra.IsAlgebraic A B := by
  constructor
  intro b
  rw [← isAlgebraic_algebraMap_iff (A := L) hBL, IsFractionRing.isAlgebraic_iff A K]
  exact Algebra.IsAlgebraic.isAlgebraic _

end FractionField

end Singularity
