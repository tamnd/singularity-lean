/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Scheme.RegularLocus
import Singularity.Scheme.Reduction
import Singularity.Algebra.RegularLocusField

/-!
# The J-2 property and the openness of the regular locus

This file proves parts of Volume 1, Sections 5.2 and 5.3 of the handbook.

A ring `A` is J-1 if its regular locus is open. It is J-2 if each finitely generated `A`-algebra is
J-1. In the handbook these notions are for Noetherian rings. Here the definitions do not ask for
the Noetherian property, and the results ask for it where they need it.

## Main definitions

* `Singularity.Algebra.IsJ1`: the regular locus of `A` is open (Definition 5.2.1).
* `Singularity.Algebra.IsJ2`: each finitely generated `A`-algebra is J-1 (Definition 5.2.1).

## Main results

* `Singularity.Algebra.IsJ2.isJ1`: a J-2 ring is J-1.
* `Singularity.Algebra.IsJ2.of_finiteType`: a finitely generated algebra over a J-2 ring is J-2.
* `Singularity.Algebra.isJ2_of_field`: a field is J-2. This is Theorem 5.2.3 for a field, and it
  contains Proposition 5.2.2.
* `Singularity.regularLocus_isOpen_of_isJ1_cover`: if each point of `X` has an affine open
  neighbourhood `U` with `Γ(X, U)` J-1, then `Reg(X)` is open. This is Proposition 5.3.2 with the
  J-1 property in place of quasi-excellence.
* `Singularity.regularLocus_isOpen_of_isJ2`: if `A` is J-2 and `X` is locally of finite type over
  `Spec A`, then `Reg(X)` is open. This is Theorem 5.3.3 with the J-2 property in place of
  quasi-excellence.
* `Singularity.subset_regularLocus_of_isIso_restrict`: if `Y` is regular and `π : Y ⟶ X` is an
  isomorphism over the open set `V`, then `V ⊆ Reg(X)` (Proposition 5.3.4).
* `Singularity.isOpen_regularLocus_of_resolution`: Corollary 5.3.5, first part.
* `Singularity.isJ2_of_resolution`: Corollary 5.3.5, second part.

## What is not proved

The G-ring property is not defined here, so quasi-excellent and excellent rings are not defined.
Proposition 5.3.2 and Theorem 5.3.3 are proved for J-1 and J-2 rings. A quasi-excellent ring is
J-2 by definition, so these forms imply the statements of the handbook. The examples of
Theorem 5.3.3 other than a field, such as `ℤ` or a complete local ring, are not proved. Proposition
5.3.4 is proved without the hypotheses that `X` is integral and locally Noetherian. These
hypotheses are not needed. The catenary and universally catenary properties (Definition 5.2.4,
Theorem 5.2.5, Proposition 5.2.6) and Theorems 5.2.8 and 5.3.6 are not proved.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace Singularity

namespace Algebra

/-- A ring `A` is J-1 if its regular locus is open in `Spec A` (Definition 5.2.1). -/
def IsJ1 (A : Type u) [CommRing A] : Prop :=
  IsOpen (regularLocus A)

/-- A ring `A` is J-2 if each finitely generated `A`-algebra is J-1 (Definition 5.2.1). The
algebras are taken in the universe of `A`. -/
def IsJ2 (A : Type u) [CommRing A] : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B], IsJ1 B

/-- A J-2 ring is J-1, because `A` is a finitely generated `A`-algebra. -/
theorem IsJ2.isJ1 {A : Type u} [CommRing A] (h : IsJ2 A) : IsJ1 A :=
  h A

/-- A finitely generated algebra over a J-2 ring is J-2. -/
theorem IsJ2.of_finiteType {A : Type u} [CommRing A] (h : IsJ2 A) (B : Type u) [CommRing B]
    [Algebra A B] [Algebra.FiniteType A B] : IsJ2 B := by
  intro C _ _ _
  let _ : Algebra A C := ((algebraMap B C).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType A C := Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  exact h C

/-- A field is J-2: the regular locus of an algebra of finite type over a field is open. This is
Theorem 5.2.3 for a field. It contains Proposition 5.2.2. -/
theorem isJ2_of_field (k : Type u) [Field k] : IsJ2 k := fun B _ _ _ =>
  isOpen_regularLocus_of_field k B

end Algebra

/-- A point of `Spec R` is in the regular locus of the scheme `Spec R` if and only if it is in the
regular locus of the ring `R`. -/
theorem mem_regularLocus_Spec_iff (R : CommRingCat.{u}) (x : Spec R) :
    x ∈ regularLocus (Spec R) ↔ (x : PrimeSpectrum R) ∈ Singularity.Algebra.regularLocus R := by
  let e := (Spec.stalkIso R x).commRingCatIsoToRingEquiv
  change IsRegularLocalRing ((Spec R).presheaf.stalk x) ↔
    IsRegularLocalRing (Localization.AtPrime (show PrimeSpectrum R from x).asIdeal)
  exact ⟨fun _ => IsRegularLocalRing.of_ringEquiv e,
    fun _ => IsRegularLocalRing.of_ringEquiv e.symm⟩

/-- Let `X` be a scheme. Assume that each point of `X` has an affine open neighbourhood `U` such
that `Γ(X, U)` is J-1. Then the regular locus of `X` is open. This is Proposition 5.3.2, with the
J-1 property in place of quasi-excellence. -/
theorem regularLocus_isOpen_of_isJ1_cover (X : Scheme.{u})
    (h : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ Algebra.IsJ1 Γ(X, U)) :
    IsOpen (regularLocus X) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hU, hxU, hJ⟩ := h x
  have hopen : IsOpen (hU.primeIdealOf ⁻¹' Singularity.Algebra.regularLocus Γ(X, U)) :=
    hJ.preimage hU.isoSpec.hom.continuous
  refine ⟨Subtype.val '' (hU.primeIdealOf ⁻¹' Singularity.Algebra.regularLocus Γ(X, U)), ?_, ?_,
    ⟨⟨x, hxU⟩, (mem_regularLocus_iff_of_isAffineOpen hU ⟨x, hxU⟩).mp hx, rfl⟩⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (mem_regularLocus_iff_of_isAffineOpen hU y).mpr hy
  · exact U.isOpen.isOpenMap_subtype_val _ hopen

/-- Let `X` be a scheme. Assume that each point of `X` has an affine open neighbourhood `U` such
that `Γ(X, U)` is J-2. Then the regular locus of `X` is open. A quasi-excellent ring is J-2, so
this contains Proposition 5.3.2. -/
theorem regularLocus_isOpen_of_isJ2_cover (X : Scheme.{u})
    (h : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ Algebra.IsJ2 Γ(X, U)) :
    IsOpen (regularLocus X) :=
  regularLocus_isOpen_of_isJ1_cover X fun x =>
    let ⟨U, hU, hxU, hJ⟩ := h x
    ⟨U, hU, hxU, hJ.isJ1⟩

/-- Let `A` be a J-2 ring and let `X` be a scheme locally of finite type over `Spec A`. Then the
regular locus of `X` is open. This is Theorem 5.3.3, with the J-2 property in place of
quasi-excellence. -/
theorem regularLocus_isOpen_of_isJ2 {A : Type u} [CommRing A] (hA : Algebra.IsJ2 A)
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
    IsOpen (regularLocus X) := by
  refine regularLocus_isOpen_of_isJ1_cover X fun x => ?_
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  have e : U ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  let φ : A →+* Γ(X, U) := (f.appLE ⊤ U e).hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom
  have hφ : φ.FiniteType := by
    refine RingHom.FiniteType.comp (HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f
      ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ e) ?_
    exact RingHom.FiniteType.of_surjective _ fun y => ⟨(Scheme.ΓSpecIso (.of A)).hom y, by simp⟩
  let _ : Algebra A Γ(X, U) := φ.toAlgebra
  have : Algebra.FiniteType A Γ(X, U) := hφ
  exact ⟨U, hU, hxU, hA Γ(X, U)⟩

/-- Let `Y` be a regular scheme and let `π : Y ⟶ X` be a morphism. Assume that `π` is an
isomorphism over the open set `V` of `X`. Then `V` lies in the regular locus of `X`. This is
Proposition 5.3.4. The hypotheses of the handbook that `X` is integral and locally Noetherian
are not needed. -/
theorem subset_regularLocus_of_isIso_restrict {X Y : Scheme.{u}} (π : Y ⟶ X)
    (hY : IsRegularScheme Y) (V : X.Opens) [IsIso (π ∣_ V)] :
    (V : Set X) ⊆ regularLocus X := by
  intro x hx
  obtain ⟨w, hw⟩ := (π ∣_ V).surjective ⟨x, hx⟩
  have hwx : π w.1 = x := by
    rw [← morphismRestrict_base_coe, hw]
  have hwV : π w.1 ∈ V := hwx ▸ hx
  have := Reduction.isIso_stalkMap_of_isIso_restrict π V w.1 hwV
  have := hY w.1
  let e := (asIso (π.stalkMap w.1)).commRingCatIsoToRingEquiv
  have hreg : IsRegularLocalRing (X.presheaf.stalk (π w.1)) :=
    IsRegularLocalRing.of_ringEquiv e.symm
  rw [← hwx]
  exact hreg

/-- Let `A` be a Noetherian ring. Assume that for each prime `p` of `A`, there are a regular
scheme `Y`, a morphism `π : Y ⟶ Spec (A / p)` and a nonempty open set `V` of `Spec (A / p)` such
that `π` is an isomorphism over `V`. Then the regular locus of `A` is open. This is the first part
of Corollary 5.3.5. -/
theorem isOpen_regularLocus_of_resolution (A : Type u) [CommRing A] [IsNoetherianRing A]
    (h : ∀ p : PrimeSpectrum A, ∃ (Y : Scheme.{u}) (π : Y ⟶ Spec (.of (A ⧸ p.asIdeal)))
      (V : (Spec (.of (A ⧸ p.asIdeal))).Opens),
      IsRegularScheme Y ∧ (V : Set (Spec (.of (A ⧸ p.asIdeal)))).Nonempty ∧ IsIso (π ∣_ V)) :
    IsOpen (Singularity.Algebra.regularLocus A) := by
  refine Singularity.Algebra.isOpen_regularLocus_of_exists_isOpen fun p _ => ?_
  obtain ⟨Y, π, V, hY, hV, hiso⟩ := h p
  refine ⟨(V : Set (Spec (.of (A ⧸ p.asIdeal)))), V.isOpen, hV, fun q hq => ?_⟩
  exact (mem_regularLocus_Spec_iff (.of (A ⧸ p.asIdeal)) q).mp
    (subset_regularLocus_of_isIso_restrict π hY V hq)

/-- Let `A` be a Noetherian ring. Assume that the hypothesis of
`isOpen_regularLocus_of_resolution` holds for each finitely generated `A`-algebra. Then `A` is
J-2. This is the second part of Corollary 5.3.5. -/
theorem isJ2_of_resolution (A : Type u) [CommRing A] [IsNoetherianRing A]
    (h : ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
      (p : PrimeSpectrum B), ∃ (Y : Scheme.{u}) (π : Y ⟶ Spec (.of (B ⧸ p.asIdeal)))
      (V : (Spec (.of (B ⧸ p.asIdeal))).Opens),
      IsRegularScheme Y ∧ (V : Set (Spec (.of (B ⧸ p.asIdeal)))).Nonempty ∧ IsIso (π ∣_ V)) :
    Algebra.IsJ2 A := by
  intro B _ _ _
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  exact isOpen_regularLocus_of_resolution B (h B)

end Singularity
