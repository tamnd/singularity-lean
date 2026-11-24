/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.Basic
import Singularity.Algebra.GenericRegular
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The regular locus of a scheme in characteristic zero

This file proves that the regular locus of a scheme that is locally of finite type over a field of
characteristic `0` is open.

The proof is local. Let `U` be an affine open set of `X`. The stalk of `X` at a point `x` of `U`
is the localization of `Γ(X, U)` at the prime of `x`. Thus the regular locus of `X` meets `U` in
the image of the regular locus of `Spec Γ(X, U)`. The ring `Γ(X, U)` is of finite type over the
field, so this set is open by `Singularity.Algebra.isOpen_regularLocus_of_charZero`.

## Main results

* `Singularity.mem_regularLocus_iff_of_isAffineOpen`: a point of an affine open set `U` is in the
  regular locus of `X` if and only if its prime is in the regular locus of `Γ(X, U)`.
* `Singularity.regularLocus_isOpen_of_charZero`: the regular locus of a scheme that is locally of
  finite type over a field of characteristic `0` is open.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace Singularity

/-- A point of an affine open set `U` is in the regular locus of `X` if and only if its prime is
in the regular locus of the ring `Γ(X, U)`. -/
theorem mem_regularLocus_iff_of_isAffineOpen {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (x : U) : (x : X) ∈ regularLocus X ↔
      hU.primeIdealOf x ∈ Singularity.Algebra.regularLocus Γ(X, U) := by
  have := hU.isLocalization_stalk x
  let e : Localization.AtPrime (hU.primeIdealOf x).asIdeal ≃+* X.presheaf.stalk (x : X) :=
    (IsLocalization.algEquiv (hU.primeIdealOf x).asIdeal.primeCompl _ _).toRingEquiv
  rw [Singularity.Algebra.mem_regularLocus]
  change IsRegularLocalRing (X.presheaf.stalk (x : X)) ↔ _
  exact ⟨fun _ => IsRegularLocalRing.of_ringEquiv e.symm,
    fun _ => IsRegularLocalRing.of_ringEquiv e⟩

/-- The regular locus of a scheme that is locally of finite type over a field of characteristic
`0` is open. -/
theorem regularLocus_isOpen_of_charZero {k : Type u} [Field k] [CharZero k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] : IsOpen (regularLocus X) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  have e : U ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  let φ : k →+* Γ(X, U) := (f.appLE ⊤ U e).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have hφ : φ.FiniteType := by
    refine RingHom.FiniteType.comp (HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f
      ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ e) ?_
    exact RingHom.FiniteType.of_surjective _ fun y => ⟨(Scheme.ΓSpecIso (.of k)).hom y, by simp⟩
  let _ : Algebra k Γ(X, U) := φ.toAlgebra
  have : Algebra.FiniteType k Γ(X, U) := hφ
  have hopen : IsOpen (hU.primeIdealOf ⁻¹' Singularity.Algebra.regularLocus Γ(X, U)) :=
    (Singularity.Algebra.isOpen_regularLocus_of_charZero k Γ(X, U)).preimage
      hU.isoSpec.hom.continuous
  refine ⟨Subtype.val '' (hU.primeIdealOf ⁻¹' Singularity.Algebra.regularLocus Γ(X, U)), ?_, ?_,
    ⟨⟨x, hxU⟩, (mem_regularLocus_iff_of_isAffineOpen hU ⟨x, hxU⟩).mp hx, rfl⟩⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (mem_regularLocus_iff_of_isAffineOpen hU y).mpr hy
  · exact U.isOpen.isOpenMap_subtype_val _ hopen

end Singularity
