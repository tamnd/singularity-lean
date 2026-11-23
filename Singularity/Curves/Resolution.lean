/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.NormalLocus
import Singularity.Curves.Affine
import Singularity.Scheme.NormalDimOne
import Singularity.Hypotheses.Integral
import Singularity.Scheme.Reduction
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Resolution of curves

Let `k` be a field of any characteristic, and let `X` be an integral variety over `k` of dimension at most 1. This file proves that the normalization `π : Y ⟶ X` is a resolution of singularities of `X`. This is Theorem 2.5.6 of Volume 1 of the handbook.

The normalization is the relative normalization of the generic point `Spec K ⟶ X` in Mathlib, where `K` is the function field of `X`. Over an affine open `U` of `X`, the ring of sections of `Y` is the integral closure of `Γ(X, U)` in `K`.

The proof has five steps.

1. `π` is finite, so it is proper. This is the theorem of E. Noether (`isFinite_normalizationHom`).
2. Over an affine open `V` with an integrally closed ring of sections, `π` is an isomorphism (`isIso_normalizationHom_restrict`).
3. A point `x` of `X` is regular if and only if it has such an affine neighbourhood. In one direction, the local ring at `x` is integrally closed, so the integral closure has a common denominator `s` with `x ∈ D(s)`. This is `Singularity.Algebra.exists_smul_mem_of_isIntegrallyClosed_localization`. Thus the regular locus is the open set `normalLocus X`, and `π` is an isomorphism over it.
4. `Y` is regular, because its rings of sections over affine opens are Dedekind domains.
5. `Y` is irreducible, and the preimage of the regular locus contains a point over the generic point. Thus the preimage is dense.

## Main results

* `isResolution_normalizationHom`: the normalization of an integral curve is a resolution.
* `integralResolutionInDim_one`: `IntegralResolutionInDim p 1` for each `p`.
* `resolutionInDim_one_of_reductionToIntegral`: `ResolutionInDim p 1` for each `p`, under the hypothesis `ReductionToIntegral`.
* `resolutionInDim_one`: `ResolutionInDim p 1` for each `p`. The reduction to integral varieties is `Singularity.Reduction.reductionToIntegral`, so this theorem takes no hypothesis.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Singularity.Curves

section Generic

variable (X : Scheme.{u}) [IsIntegral X]

/-- The morphism from the spectrum of the function field to `X`. -/
noncomputable abbrev genericHom : Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

lemma genericPoint_mem (U : X.Opens) [h : Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using h)

lemma genericHom_preimage (U : X.Opens) [Nonempty U] : genericHom X ⁻¹ᵁ U = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  have : y = IsLocalRing.closedPoint X.functionField :=
    Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _
  subst this
  change X.fromSpecStalk (genericPoint X) (IsLocalRing.closedPoint _) ∈ U
  rw [Scheme.fromSpecStalk_closedPoint]
  exact genericPoint_mem X U

/-- The sections of `Spec K` over the preimage of `U` are the function field `K`. -/
noncomputable def genericIso (U : X.Opens) [Nonempty U] :
    X.functionField ≅ Γ(Spec X.functionField, genericHom X ⁻¹ᵁ U) :=
  (Scheme.ΓSpecIso _).symm ≪≫
    (Spec X.functionField).presheaf.mapIso (eqToIso (genericHom_preimage X U)).op

lemma genericHom_app (U : X.Opens) [Nonempty U] :
    (genericHom X).app U = X.germToFunctionField U ≫ (genericIso X U).hom := by
  rw [Scheme.fromSpecStalk_app (genericPoint_mem X U)]
  simp only [genericIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]
  rfl

/-- The function field and the sections of `Spec K` over the preimage of `U` are isomorphic as algebras over `Γ(X, U)`. -/
noncomputable def genericAlgEquiv (U : X.Opens) [Nonempty U] :
    letI := ((genericHom X).app U).hom.toAlgebra
    X.functionField ≃ₐ[Γ(X, U)] Γ(Spec X.functionField, genericHom X ⁻¹ᵁ U) :=
  letI := ((genericHom X).app U).hom.toAlgebra
  AlgEquiv.ofRingEquiv (f := (genericIso X U).commRingCatIsoToRingEquiv) fun a => by
    change _ = ((genericHom X).app U).hom a
    rw [genericHom_app]
    rfl

lemma isFractionRing_genericHom (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := ((genericHom X).app U).hom.toAlgebra
    IsFractionRing Γ(X, U) Γ(Spec X.functionField, genericHom X ⁻¹ᵁ U) :=
  letI := ((genericHom X).app U).hom.toAlgebra
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  IsLocalization.isLocalization_of_algEquiv _ (genericAlgEquiv X U)

end Generic

section Variety

variable {k : Type u} [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))

/-- The structure of a `k`-algebra on the sections of `X` over `U`. -/
noncomputable abbrev sectionAlgebra (U : X.Opens) : Algebra k Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra

lemma finiteType_sectionAlgebra [LocallyOfFiniteType f] (U : X.Opens) (hU : IsAffineOpen U) :
    letI := sectionAlgebra X f U
    Algebra.FiniteType k Γ(X, U) := by
  have h := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  have h' : (Scheme.ΓSpecIso (.of k)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
  exact RingHom.FiniteType.comp h h'

/-- If `X` has dimension at most 1, then so has the ring of sections over each affine open. -/
lemma ringKrullDim_sections_le (h : topologicalKrullDim X ≤ 1) (U : X.Opens)
    (hU : IsAffineOpen U) : ringKrullDim Γ(X, U) ≤ 1 := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U)]
  change topologicalKrullDim (Spec Γ(X, U)) ≤ 1
  rw [← IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph]
  exact (topologicalKrullDim_subspace_le X U).trans h

end Variety

lemma dimensionLEOne_of_ringKrullDim_le {R : Type*} [CommRing R] [IsDomain R]
    (h : ringKrullDim R ≤ 1) : Ring.DimensionLEOne R := by
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr h
  exact ⟨fun hne hp => hp.isMaximal_of_ne_bot hne⟩

section Normalization

variable {k : Type u} [Field k] (X : Scheme.{u}) [IsIntegral X] (f : X ⟶ Spec (.of k))

/-- The normalization of `X`: the relative normalization of the generic point. -/
noncomputable abbrev normalizationHom : (genericHom X).normalization ⟶ X :=
  (genericHom X).fromNormalization

lemma finite_integralClosure_sections [LocallyOfFiniteType f] (U : X.Opens) (hU : IsAffineOpen U)
    [Nonempty U] :
    letI := ((genericHom X).app U).hom.toAlgebra
    Module.Finite Γ(X, U) (integralClosure Γ(X, U) Γ(Spec X.functionField, genericHom X ⁻¹ᵁ U)) := by
  let := ((genericHom X).app U).hom.toAlgebra
  let := sectionAlgebra X f U
  have := finiteType_sectionAlgebra X f U hU
  have := isFractionRing_genericHom X U hU
  exact Singularity.Algebra.finite_integralClosure_of_isFractionRing k Γ(X, U) _

/-- The normalization of an integral variety is a finite morphism. -/
lemma isFinite_normalizationHom [LocallyOfFiniteType f] : IsFinite (normalizationHom X) := by
  refine ⟨fun U hU => ?_⟩
  rcases isEmpty_or_nonempty U with hU0 | hU0
  · have hU' : U = ⊥ := by
      ext x
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hU0.false ⟨x, hx⟩
    subst hU'
    have : Subsingleton Γ((genericHom X).normalization, normalizationHom X ⁻¹ᵁ ⊥) :=
      inferInstanceAs (Subsingleton Γ(_, ⊥))
    exact RingHom.Finite.of_surjective _ fun y => ⟨0, Subsingleton.elim _ _⟩
  · rw [Scheme.Hom.fromNormalization_app _ hU]
    let := ((genericHom X).app U).hom.toAlgebra
    have := finite_integralClosure_sections X f U hU
    have h' : ((genericHom X).normalizationObjIso hU).inv.hom.Finite :=
      RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    exact RingHom.Finite.comp h' (RingHom.finite_algebraMap.mpr this)

/-- Over an affine open `V` such that `Γ(X, V)` is integrally closed, the normalization is an isomorphism. -/
lemma isIso_normalizationHom_restrict (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V]
    [IsIntegrallyClosed Γ(X, V)] : IsIso (normalizationHom X ∣_ V) := by
  rw [isIso_morphismRestrict_iff_isIso_app _ hV, Scheme.Hom.fromNormalization_app _ hV]
  let := ((genericHom X).app V).hom.toAlgebra
  have := isFractionRing_genericHom X V hV
  suffices IsIso (CommRingCat.ofHom (algebraMap Γ(X, V)
      (integralClosure Γ(X, V) Γ(Spec X.functionField, genericHom X ⁻¹ᵁ V)))) from inferInstance
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun a b h => IsFractionRing.injective Γ(X, V) Γ(Spec X.functionField, genericHom X ⁻¹ᵁ V)
    (congrArg Subtype.val h), fun b => ?_⟩
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Γ(X, V))
    (K := Γ(Spec X.functionField, genericHom X ⁻¹ᵁ V))).mp b.2
  exact ⟨a, Subtype.ext ha⟩

end Normalization

/-- A regular local ring of dimension at most 1 is integrally closed. -/
lemma isIntegrallyClosed_of_isRegularLocalRing {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (h : ringKrullDim R ≤ 1) : IsIntegrallyClosed R := by
  have := Singularity.Algebra.isDomain_of_isRegularLocalRing R
  obtain ⟨n, hn⟩ := Singularity.Algebra.exists_ringKrullDim_eq_natCast R
  rw [hn] at h
  have hn1 : n ≤ 1 := by exact_mod_cast h
  interval_cases n
  · have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr (by rw [hn])
    exact (isIntegrallyClosed_iff (FractionRing R)).mpr fun {x} _ =>
      (IsFractionRing.surjective_iff_isField.mpr Ring.KrullDimLE.isField_of_isDomain) x
  · exact (Singularity.Algebra.isRegularLocalRing_iff_isIntegrallyClosed (by rw [hn]; rfl)).mp
      inferInstance

section RegularLocus

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))

/-- A regular point of an integral curve has an affine neighbourhood with an integrally closed ring of sections. -/
lemma exists_isIntegrallyClosed_of_mem_regularLocus [LocallyOfFiniteType f]
    (hX : topologicalKrullDim X ≤ 1) {x : X} (hx : x ∈ regularLocus X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ IsIntegrallyClosed Γ(X, V) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : IsRegularLocalRing (X.presheaf.stalk x) := hx
  have : IsIntegrallyClosed (X.presheaf.stalk (⟨x, hxU⟩ : U)) :=
    isIntegrallyClosed_of_isRegularLocalRing ((ringKrullDim_stalk_le_topologicalKrullDim x).trans hX)
  let := sectionAlgebra X f U
  have := finiteType_sectionAlgebra X f U hU
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  have := Singularity.Algebra.finite_integralClosure_of_isFractionRing k Γ(X, U) X.functionField
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  have := functionField_isScalarTower X U ⟨x, hxU⟩
  obtain ⟨s, hs, hsK⟩ := Singularity.Algebra.exists_smul_mem_of_isIntegrallyClosed_localization
    (K := X.functionField) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal (X.presheaf.stalk (⟨x, hxU⟩ : U))
  have hxV : x ∈ X.basicOpen s := by
    have h : hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
    rw [← h]
    change hU.primeIdealOf ⟨x, hxU⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen s
    rw [hU.fromSpec_preimage_basicOpen]
    exact hs
  have : Nonempty (X.basicOpen s) := ⟨⟨x, hxV⟩⟩
  have := hU.isLocalization_basicOpen s
  have := functionField_isFractionRing_of_isAffineOpen X _ (hU.basicOpen s)
  have : IsScalarTower Γ(X, U) Γ(X, X.basicOpen s) X.functionField := by
    apply IsScalarTower.of_algebraMap_eq'
    simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp]
    congr 1
    exact (X.presheaf.germ_res _ _ _).symm
  exact ⟨_, hU.basicOpen s, hxV,
    Singularity.Algebra.isIntegrallyClosed_of_isLocalization_away s hsK _⟩

/-- A point with an affine neighbourhood whose ring of sections is integrally closed is a regular point. -/
lemma mem_regularLocus_of_isIntegrallyClosed [LocallyOfFiniteType f]
    (hX : topologicalKrullDim X ≤ 1) {V : X.Opens} (hV : IsAffineOpen V)
    [IsIntegrallyClosed Γ(X, V)] {x : X} (hxV : x ∈ V) : x ∈ regularLocus X := by
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have := LocallyOfFiniteType.isLocallyNoetherian f
  let := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  have : IsIntegrallyClosed (X.presheaf.stalk (⟨x, hxV⟩ : V)) :=
    isIntegrallyClosed_of_isLocalization (R := Γ(X, V)) (S := X.presheaf.stalk (⟨x, hxV⟩ : V))
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
      (Ideal.primeCompl_le_nonZeroDivisors _)
  exact isRegularLocalRing_of_isIntegrallyClosed
    ((ringKrullDim_stalk_le_topologicalKrullDim x).trans hX)

end RegularLocus

section Resolution

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))

variable (X) in
/-- The affine opens of `X` that are nonempty and have an integrally closed ring of sections. -/
def NormalOpen : Type u :=
  {V : X.Opens // IsAffineOpen V ∧ Nonempty V ∧ IsIntegrallyClosed Γ(X, V)}

variable (X) in
/-- The union of the nonempty affine opens with an integrally closed ring of sections. -/
noncomputable def normalLocus : X.Opens :=
  ⨆ V : NormalOpen X, V.1

/-- For an integral curve, the open set `normalLocus X` is the regular locus. -/
lemma coe_normalLocus [LocallyOfFiniteType f] (hX : topologicalKrullDim X ≤ 1) :
    (normalLocus X : Set X) = regularLocus X := by
  ext x
  change x ∈ normalLocus X ↔ _
  rw [normalLocus, Opens.mem_iSup]
  constructor
  · rintro ⟨⟨V, hV, _, _⟩, hxV⟩
    exact mem_regularLocus_of_isIntegrallyClosed f hX hV hxV
  · intro hx
    obtain ⟨V, hV, hxV, hVc⟩ := exists_isIntegrallyClosed_of_mem_regularLocus f hX hx
    exact ⟨⟨V, hV, ⟨⟨x, hxV⟩⟩, hVc⟩, hxV⟩

variable (X) in
/-- The normalization is an isomorphism over `normalLocus X`. -/
lemma isIso_normalizationHom_restrict_normalLocus :
    IsIso (normalizationHom X ∣_ normalLocus X) := by
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun x => ?_
  obtain ⟨⟨V, hV, hVne, hVc⟩, hxV⟩ := Opens.mem_iSup.mp x.2
  have hVW : V ≤ normalLocus X :=
    le_iSup (fun V : NormalOpen X => V.1) ⟨V, hV, hVne, hVc⟩
  refine ⟨(normalLocus X).ι ⁻¹ᵁ V, hxV, ?_⟩
  rw [(MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict _ _ _ ≪≫ morphismRestrictEq _ ?_)]
  · exact isIso_normalizationHom_restrict X V hV
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hVW]

/-- The normalization of an integral curve is regular. -/
lemma isRegularScheme_normalization [LocallyOfFiniteType f] (hX : topologicalKrullDim X ≤ 1) :
    IsRegularScheme (genericHom X).normalization := fun y => by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (normalizationHom X y)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hyU⟩⟩
  let := ((genericHom X).app U).hom.toAlgebra
  let := sectionAlgebra X f U
  have := finiteType_sectionAlgebra X f U hU
  have := isFractionRing_genericHom X U hU
  have := dimensionLEOne_of_ringKrullDim_le (ringKrullDim_sections_le X hX U hU)
  have hD := isDedekindDomain_integralClosure k Γ(X, U)
  let e : FractionRing Γ(X, U) ≃ₐ[Γ(X, U)] Γ(Spec X.functionField, genericHom X ⁻¹ᵁ U) :=
    IsLocalization.algEquiv (nonZeroDivisors _) _ _
  have : IsRegularRing (integralClosure Γ(X, U) Γ(Spec X.functionField, genericHom X ⁻¹ᵁ U)) :=
    IsRegularRing.of_ringEquiv e.mapIntegralClosure.toRingEquiv
  have hV : IsAffineOpen (normalizationHom X ⁻¹ᵁ U) := hU.preimage _
  have : IsRegularRing Γ((genericHom X).normalization, normalizationHom X ⁻¹ᵁ U) :=
    IsRegularRing.of_ringEquiv
      ((genericHom X).normalizationObjIso hU).commRingCatIsoToRingEquiv.symm
  let := ((genericHom X).normalization).presheaf.algebra_section_stalk
    (U := normalizationHom X ⁻¹ᵁ U) ⟨y, hyU⟩
  have := hV.isLocalization_stalk ⟨y, hyU⟩
  let P := (hV.primeIdealOf ⟨y, hyU⟩).asIdeal
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) _).toRingEquiv

/-- The normalization of an integral curve over a field is a resolution of singularities. -/
theorem isResolution_normalizationHom [LocallyOfFiniteType f] (hX : topologicalKrullDim X ≤ 1) :
    IsResolution (normalizationHom X) where
  regular := isRegularScheme_normalization f hX
  proper := by
    have := isFinite_normalizationHom X f
    infer_instance
  isIso_over := ⟨normalLocus X, coe_normalLocus f hX, isIso_normalizationHom_restrict_normalLocus X⟩
  dense := by
    rw [← coe_normalLocus f hX]
    refine ((normalLocus X).2.preimage (normalizationHom X).continuous).dense ?_
    refine ⟨(genericHom X).toNormalization (IsLocalRing.closedPoint X.functionField), ?_⟩
    have h : normalizationHom X ((genericHom X).toNormalization
        (IsLocalRing.closedPoint X.functionField)) = genericPoint X := by
      change ((genericHom X).toNormalization ≫ (genericHom X).fromNormalization) _ = _
      rw [Scheme.Hom.toNormalization_fromNormalization]
      exact Scheme.fromSpecStalk_closedPoint
    change normalizationHom X _ ∈ (normalLocus X : Set X)
    rw [h, coe_normalLocus f hX]
    exact isRegularLocalRing_of_isField (Field.toIsField X.functionField)

end Resolution

/-- Resolution of singularities for integral curves over a field of each characteristic. -/
theorem integralResolutionInDim_one (p : ℕ) : IntegralResolutionInDim.{u} p 1 := by
  intro k _ _ X f hV _ hX
  have := hV.finiteType
  exact ⟨_, normalizationHom X, isResolution_normalizationHom f (by exact_mod_cast hX)⟩

/-- Resolution of singularities for curves over a field of each characteristic, under the hypothesis `ReductionToIntegral`. -/
theorem resolutionInDim_one_of_reductionToIntegral (h : ReductionToIntegral.{u}) (p : ℕ) :
    ResolutionInDim.{u} p 1 :=
  h p 1 (integralResolutionInDim_one p)

/-- Resolution of singularities for curves over a field of each characteristic. Let `X` be a variety of dimension at most 1 over a field `k`. Then `X` has a resolution. The variety `X` need not be irreducible. -/
theorem resolutionInDim_one (p : ℕ) : ResolutionInDim.{u} p 1 :=
  resolutionInDim_one_of_reductionToIntegral Reduction.reductionToIntegral p

end Singularity.Curves
