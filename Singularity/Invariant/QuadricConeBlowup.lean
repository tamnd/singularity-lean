/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.QuadricConeChart
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The blowup of the quadric cone at the origin

This file proves the algebraic part of Volume 4, Example 2.3.7 (1) and (2) of the handbook. Let `k` be a commutative ring and let `X = V(xy - z^2)` in `𝔸^3_k`. The blowup of the origin is covered by two charts `U = Spec k[x, z_1]` and `V = Spec k[y, z_2]`.

* `Singularity.quadricConeToU` and `Singularity.quadricConeToV`: the maps from `k[x, y, z]/(xy - z^2)` to the polynomial rings of the charts. The first map sends `y` to `x z_1^2` and `z` to `x z_1`. The second map sends `x` to `y z_2^2` and `z` to `y z_2`.
* `Singularity.map_chartU_span_X` and `Singularity.map_chartV_span_X`: the ideal of the origin generates `(x)` in `U` and `(y)` in `V`. So the exceptional divisor `E` is a coordinate line in each chart.
* `Singularity.quadricConeGlueEquiv`: the gluing isomorphism of the overlap `k[x, z_1, z_1^{-1}]`, with `z_2 = z_1^{-1}` and `y = x z_1^2`. The map is an involution (`Singularity.quadricConeGlueAway_comp_self`).
* `Singularity.quadricConeGlue_comp_chartV`: the two maps from the cone agree on the overlap.
* `Singularity.quadricConeGlue_exceptional_generator`: on the overlap the generator `y` of the ideal of `E` in `V` is `z_1^2` times the generator `x` in `U`. So `E` is the line `ℙ^1` glued from `Spec k[z_1]` and `Spec k[z_2]`, and the transition function of its conormal sheaf is `z_1^2`.

The file does not build the blowup as a scheme. It does not prove that the two charts are the charts of the blowup, that their union is the blowup, or that the maps from the cone are injective. It does not prove that the conormal sheaf is `𝒪(2)` as a sheaf, that `E · E = -2`, or the statements of part (3) on `H^0` and `H^1`. The regularity of the charts follows from the fact that they are polynomial rings, and the file does not state it.
-/

namespace Singularity

open MvPolynomial

section QuadricConeBlowup

variable (k : Type*) [CommRing k]

/-- The coordinate ring `k[x, y, z]/(xy - z^2)` of the quadric cone. -/
abbrev QuadricConeRing : Type _ := MvPolynomial (Fin 3) k ⧸ Ideal.span {quadricCone k}

/-- The chart `U` of the blowup, with coordinates `x = X 0` and `z_1 = X 1`. The map sends `x` to
`x`, `y` to `x z_1^2` and `z` to `x z_1`. -/
noncomputable def quadricConeChartU : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 2) k :=
  aeval ![X 0, X 0 * X 1 ^ 2, X 0 * X 1]

/-- The chart `V` of the blowup, with coordinates `y = X 0` and `z_2 = X 1`. The map sends `x` to
`y z_2^2`, `y` to `y` and `z` to `y z_2`. -/
noncomputable def quadricConeChartV : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 2) k :=
  aeval ![X 0 * X 1 ^ 2, X 0, X 0 * X 1]

theorem quadricConeChartU_quadricCone : quadricConeChartU k (quadricCone k) = 0 := by
  simp [quadricCone, quadricConeChartU]
  ring

theorem quadricConeChartV_quadricCone : quadricConeChartV k (quadricCone k) = 0 := by
  simp [quadricCone, quadricConeChartV]
  ring

theorem quadricCone_span_le_ker_chartU :
    Ideal.span {quadricCone k} ≤ RingHom.ker (quadricConeChartU k) := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact quadricConeChartU_quadricCone k

theorem quadricCone_span_le_ker_chartV :
    Ideal.span {quadricCone k} ≤ RingHom.ker (quadricConeChartV k) := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact quadricConeChartV_quadricCone k

/-- The map from the ring of the cone to the polynomial ring `k[x, z_1]` of the chart `U`. -/
noncomputable def quadricConeToU : QuadricConeRing k →ₐ[k] MvPolynomial (Fin 2) k :=
  Ideal.Quotient.liftₐ _ (quadricConeChartU k) fun _ ha =>
    quadricCone_span_le_ker_chartU k ha

/-- The map from the ring of the cone to the polynomial ring `k[y, z_2]` of the chart `V`. -/
noncomputable def quadricConeToV : QuadricConeRing k →ₐ[k] MvPolynomial (Fin 2) k :=
  Ideal.Quotient.liftₐ _ (quadricConeChartV k) fun _ ha =>
    quadricCone_span_le_ker_chartV k ha

/-- In the chart `U`, the ideal of the origin generates the ideal `(x)`. So the exceptional
divisor `E` is `V(x)` in `U`. -/
theorem map_chartU_span_X :
    (Ideal.span (Set.range (X : Fin 3 → MvPolynomial (Fin 3) k))).map (quadricConeChartU k) =
      Ideal.span {X 0} := by
  rw [Ideal.map_span, ← Set.range_comp]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp [quadricConeChartU, Ideal.mem_span_singleton]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span ⟨0, by simp [quadricConeChartU]⟩

/-- In the chart `V`, the ideal of the origin generates the ideal `(y)`. -/
theorem map_chartV_span_X :
    (Ideal.span (Set.range (X : Fin 3 → MvPolynomial (Fin 3) k))).map (quadricConeChartV k) =
      Ideal.span {X 0} := by
  rw [Ideal.map_span, ← Set.range_comp]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp [quadricConeChartV, Ideal.mem_span_singleton]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span ⟨1, by simp [quadricConeChartV]⟩

/-- The ring `k[x, z_1, z_1^{-1}]`, the open set `z_1 ≠ 0` of `U`. -/
abbrev QuadricConeOverlap : Type _ := Localization.Away (X 1 : MvPolynomial (Fin 2) k)

/-- The inverse of `z_1` in the overlap. -/
noncomputable def quadricConeOverlapInv : QuadricConeOverlap k :=
  IsLocalization.Away.invSelf (X 1 : MvPolynomial (Fin 2) k)

theorem quadricConeOverlap_mul_inv :
    algebraMap (MvPolynomial (Fin 2) k) (QuadricConeOverlap k) (X 1) * quadricConeOverlapInv k
      = 1 :=
  IsLocalization.Away.mul_invSelf _

/-- The gluing map `k[y, z_2] → k[x, z_1, z_1^{-1}]`, with `y = x z_1^2` and `z_2 = z_1^{-1}`. -/
noncomputable def quadricConeGlue : MvPolynomial (Fin 2) k →ₐ[k] QuadricConeOverlap k :=
  aeval ![algebraMap (MvPolynomial (Fin 2) k) (QuadricConeOverlap k) (X 0 * X 1 ^ 2), quadricConeOverlapInv k]

theorem quadricConeGlue_X_zero :
    quadricConeGlue k (X 0) = algebraMap (MvPolynomial (Fin 2) k) (QuadricConeOverlap k) (X 0 * X 1 ^ 2) := by
  simp [quadricConeGlue]

theorem quadricConeGlue_X_one : quadricConeGlue k (X 1) = quadricConeOverlapInv k := by
  simp [quadricConeGlue]

/-- The two charts agree on the overlap: the map from the cone through `V` and the gluing map is
the map from the cone through `U` and the localization. -/
theorem quadricConeGlue_comp_chartV :
    (quadricConeGlue k).comp (quadricConeChartV k) =
      (IsScalarTower.toAlgHom k (MvPolynomial (Fin 2) k) (QuadricConeOverlap k)).comp
        (quadricConeChartU k) := by
  have h := quadricConeOverlap_mul_inv k
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i
  · simp [quadricConeChartV, quadricConeChartU, quadricConeGlue_X_zero, quadricConeGlue_X_one]
    linear_combination (algebraMap (MvPolynomial (Fin 2) k) (QuadricConeOverlap k) (X 0) *
      (algebraMap (MvPolynomial (Fin 2) k) (QuadricConeOverlap k) (X 1) * quadricConeOverlapInv k + 1)) * h
  · simp [quadricConeChartV, quadricConeChartU, quadricConeGlue_X_zero]
  · simp [quadricConeChartV, quadricConeChartU, quadricConeGlue_X_zero, quadricConeGlue_X_one]
    linear_combination (algebraMap (MvPolynomial (Fin 2) k) (QuadricConeOverlap k) (X 0) * algebraMap (MvPolynomial (Fin 2) k) (QuadricConeOverlap k) (X 1)) * h

theorem isUnit_quadricConeGlue_X_one : IsUnit (quadricConeGlue k (X 1)) := by
  rw [quadricConeGlue_X_one]
  exact ⟨⟨quadricConeOverlapInv k, _, by rw [mul_comm]; exact quadricConeOverlap_mul_inv k,
    quadricConeOverlap_mul_inv k⟩, rfl⟩

/-- The gluing map, extended to the open set `z_2 ≠ 0` of `V`. -/
noncomputable def quadricConeGlueAway : QuadricConeOverlap k →ₐ[k] QuadricConeOverlap k :=
  { IsLocalization.Away.lift (X 1 : MvPolynomial (Fin 2) k) (isUnit_quadricConeGlue_X_one k) with
    commutes' := fun c => by
      show IsLocalization.Away.lift (X 1 : MvPolynomial (Fin 2) k) (isUnit_quadricConeGlue_X_one k)
        (algebraMap k (QuadricConeOverlap k) c) = algebraMap k (QuadricConeOverlap k) c
      rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 2) k) (QuadricConeOverlap k),
        IsLocalization.Away.lift_eq]
      show quadricConeGlue k (algebraMap k _ c) = _
      rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply] }

theorem quadricConeGlueAway_algebraMap (f : MvPolynomial (Fin 2) k) :
    quadricConeGlueAway k (algebraMap (MvPolynomial (Fin 2) k) (QuadricConeOverlap k) f) = quadricConeGlue k f :=
  IsLocalization.Away.lift_eq _ (isUnit_quadricConeGlue_X_one k) f

theorem quadricConeGlueAway_inv :
    quadricConeGlueAway k (quadricConeOverlapInv k) =
      algebraMap (MvPolynomial (Fin 2) k) (QuadricConeOverlap k) (X 1) := by
  have h1 := quadricConeOverlap_mul_inv k
  have h2 : quadricConeGlueAway k (algebraMap (MvPolynomial (Fin 2) k) (QuadricConeOverlap k) (X 1)) * quadricConeGlueAway k
      (quadricConeOverlapInv k) = 1 := by rw [← map_mul, h1, map_one]
  rw [quadricConeGlueAway_algebraMap, quadricConeGlue_X_one] at h2
  calc quadricConeGlueAway k (quadricConeOverlapInv k)
      = (algebraMap (MvPolynomial (Fin 2) k) (QuadricConeOverlap k) (X 1) * quadricConeOverlapInv k) *
          quadricConeGlueAway k (quadricConeOverlapInv k) := by rw [h1, one_mul]
    _ = algebraMap (MvPolynomial (Fin 2) k) (QuadricConeOverlap k) (X 1) * (quadricConeOverlapInv k *
          quadricConeGlueAway k (quadricConeOverlapInv k)) := by ring
    _ = algebraMap (MvPolynomial (Fin 2) k) (QuadricConeOverlap k) (X 1) := by rw [h2, mul_one]

/-- The gluing map is an involution. So it is an isomorphism `k[y, z_2, z_2^{-1}] ≅
k[x, z_1, z_1^{-1}]`, and the two charts are glued along `z_1 ≠ 0` by `z_2 = z_1^{-1}` and
`y = x z_1^2`. -/
theorem quadricConeGlueAway_comp_self :
    (quadricConeGlueAway k).comp (quadricConeGlueAway k) = AlgHom.id k _ := by
  have h := quadricConeOverlap_mul_inv k
  have key : ((quadricConeGlueAway k).comp (quadricConeGlueAway k)).comp
      (IsScalarTower.toAlgHom k (MvPolynomial (Fin 2) k) (QuadricConeOverlap k)) =
        IsScalarTower.toAlgHom k (MvPolynomial (Fin 2) k) (QuadricConeOverlap k) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    fin_cases i
    · simp [quadricConeGlueAway_algebraMap, quadricConeGlue_X_zero, quadricConeGlue_X_one]
      linear_combination (algebraMap (MvPolynomial (Fin 2) k) (QuadricConeOverlap k) (X 0) *
        (algebraMap (MvPolynomial (Fin 2) k) (QuadricConeOverlap k) (X 1) * quadricConeOverlapInv k + 1)) * h
    · simp [quadricConeGlueAway_algebraMap, quadricConeGlue_X_one, quadricConeGlueAway_inv]
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (X 1 : MvPolynomial (Fin 2) k))
  exact RingHom.ext fun f => by simpa using DFunLike.congr_fun key f

/-- The gluing isomorphism of the overlap. -/
noncomputable def quadricConeGlueEquiv : QuadricConeOverlap k ≃ₐ[k] QuadricConeOverlap k :=
  AlgEquiv.ofAlgHom (quadricConeGlueAway k) (quadricConeGlueAway k)
    (quadricConeGlueAway_comp_self k) (quadricConeGlueAway_comp_self k)

/-- The transition function of the conormal sheaf of `E`. On `V` the ideal of `E` is `(y)`, on
`U` it is `(x)`, and on the overlap `y = z_1^2 x`. So the generators differ by `z_1^2`, and the
conormal sheaf of `E ≅ ℙ^1` has degree 2. -/
theorem quadricConeGlue_exceptional_generator :
    quadricConeGlue k (X 0) = algebraMap (MvPolynomial (Fin 2) k) (QuadricConeOverlap k) (X 1) ^ 2 *
      algebraMap (MvPolynomial (Fin 2) k) (QuadricConeOverlap k) (X 0) := by
  rw [quadricConeGlue_X_zero, map_mul, map_pow, mul_comm]

end QuadricConeBlowup

end Singularity
