/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Scheme.Components
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# The reduction to integral varieties

This file proves `ReductionToIntegral`: if each integral variety of dimension at most `n` over a field of characteristic `p` has a resolution, then each variety of dimension at most `n` has a resolution.

Let `X` be a variety over `k`, and let `X_1, ..., X_r` be the irreducible components of `X` with the reduced structure. Each `X_i` is an integral variety of dimension at most `n`, so it has a resolution `π_i : Y_i ⟶ X_i`. Let `Y` be the disjoint union of the `Y_i`, and let `π : Y ⟶ X` be the map that is `π_i` followed by the inclusion of `X_i` on each `Y_i`.

1. `Y` is regular, because each `Y_i` is regular.
2. `π` is proper. The proof uses the valuative criterion, because Mathlib has no lemma for a disjoint union of proper maps (`isProper_sigmaDesc`).
3. Let `W_i` be the complement in `X` of the components other than `X_i`. A regular local ring is a domain, so a regular point of `X` lies on one component only. Thus the regular locus of `X` is the union of the open sets `W_i ∩ Reg(X_i)`. Over `W_i`, the inclusion of `X_i` is an isomorphism, and over `W_i ∩ Reg(X_i)` the map `π` is an isomorphism. These isomorphisms glue.
4. The preimage of the regular locus of `X` is dense in `Y`. In each `Y_i`, the preimage of `Reg(X_i)` is dense, and `π_i` is a homeomorphism over `Reg(X_i)`. The open set `W_i` meets each nonempty open set of `X_i`, because `X_i` is irreducible.

## Main results

* `isProper_sigmaDesc`: a finite disjoint union of proper maps to one scheme is proper, if the source is quasi-separated.
* `isIso_restrict_iSup`: isomorphisms over open sets glue.
* `reductionToIntegral`: the proof of `ReductionToIntegral`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Singularity.Reduction

section Restrict

variable {X Y : Scheme.{u}}

/-- An isomorphism over `U` is an isomorphism over each open set `V ≤ U`. -/
lemma isIso_restrict_of_le (f : X ⟶ Y) {U V : Y.Opens} (hVU : V ≤ U) [IsIso (f ∣_ U)] :
    IsIso (f ∣_ V) := by
  have h : MorphismProperty.isomorphisms Scheme (f ∣_ U ∣_ U.ι ⁻¹ᵁ V) :=
    IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme)
      (show IsIso (f ∣_ U) from inferInstance) _
  have h2 := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V))).mp h
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hVU
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff (morphismRestrictEq f e)).mp h2

/-- Isomorphisms over open sets glue: if `f` is an isomorphism over each `V i`, then `f` is an isomorphism over the union of the `V i`. -/
lemma isIso_restrict_iSup (f : X ⟶ Y) {ι : Type*} (V : ι → Y.Opens) (H : ∀ i, IsIso (f ∣_ V i)) :
    IsIso (f ∣_ ⨆ i, V i) := by
  set U := ⨆ i, V i
  have hle : ∀ i, V i ≤ U := fun i => le_iSup V i
  have hU : ⨆ i, U.ι ⁻¹ᵁ V i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup]
    exact eq_top_iff.mpr fun x _ => x.2
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    _ hU fun i => ?_
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ V i) = V i := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (hle i)
  refine ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V i))).mpr ?_
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff (morphismRestrictEq f e)).mpr
    (H i)

set_option backward.isDefEq.respectTransparency false in
/-- If `f` is an isomorphism over `U`, then the stalk map of `f` at each point over `U` is an isomorphism. -/
lemma isIso_stalkMap_of_isIso_restrict (f : X ⟶ Y) (U : Y.Opens) [IsIso (f ∣_ U)] (x : X)
    (hx : f x ∈ U) : IsIso (f.stalkMap x) :=
  ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
    (morphismRestrictStalkMap f U ⟨x, hx⟩)).mp
    (show IsIso ((f ∣_ U).stalkMap ⟨x, hx⟩) from inferInstance)

end Restrict

section Sigma

variable {σ : Type u} {Y : σ → Scheme.{u}}

lemma exists_sigmaι_eq (y : (∐ Y : Scheme.{u})) : ∃ i x, Sigma.ι Y i x = y := by
  obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk Y).surjective y
  exact ⟨i, x, (sigmaMk_mk Y i x).symm⟩

lemma sigmaι_eq_sigmaι_iff {i j : σ} (x : Y i) (y : Y j) :
    Sigma.ι Y i x = Sigma.ι Y j y ↔ (⟨i, x⟩ : Σ i, Y i) = ⟨j, y⟩ := by
  rw [← sigmaMk_mk, ← sigmaMk_mk]
  exact (sigmaMk Y).injective.eq_iff

lemma eq_of_sigmaι_eq {i j : σ} (x : Y i) (y : Y j) (h : Sigma.ι Y i x = Sigma.ι Y j y) :
    i = j :=
  congrArg Sigma.fst ((sigmaι_eq_sigmaι_iff x y).mp h)

lemma isClosed_range_sigmaι (i : σ) : IsClosed (Set.range (Sigma.ι Y i)) := by
  have : (Set.range (Sigma.ι Y i))ᶜ = ⋃ (j : σ) (_ : j ≠ i), Set.range (Sigma.ι Y j) := by
    ext y
    obtain ⟨j, x, rfl⟩ := exists_sigmaι_eq y
    simp only [Set.mem_compl_iff, Set.mem_range, Set.mem_iUnion, not_exists]
    constructor
    · intro h
      refine ⟨j, ?_, x, rfl⟩
      rintro rfl
      exact h x rfl
    · rintro ⟨j', hj', x', hx'⟩ x'' hx''
      exact hj' ((eq_of_sigmaι_eq _ _ (hx'.trans hx''.symm)))
  rw [← isOpen_compl_iff, this]
  exact isOpen_iUnion fun j => isOpen_iUnion fun _ => (Sigma.ι Y j).isOpenEmbedding.isOpen_range

instance compactSpace_sigma [Finite σ] [∀ i, CompactSpace (Y i)] :
    CompactSpace (∐ Y : Scheme.{u}) :=
  (sigmaMk Y).compactSpace

end Sigma

section Proper

variable {σ : Type u} {X : Scheme.{u}} {Y : σ → Scheme.{u}} (g : ∀ i, Y i ⟶ X)

lemma sigmaDesc_apply (i : σ) (x : Y i) : Sigma.desc g (Sigma.ι Y i x) = g i x := by
  rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]

/-- A morphism from the spectrum of a field to `∐ Y` factors through one `Y i`. -/
lemma exists_range_subset_of_field (K : Type u) [Field K] (a : Spec (.of K) ⟶ ∐ Y) :
    ∃ i, Set.range a ⊆ Set.range (Sigma.ι Y i) := by
  have : Subsingleton (Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let p : Spec (.of K) := default
  obtain ⟨i, x, hx⟩ := exists_sigmaι_eq (a p)
  refine ⟨i, ?_⟩
  rintro _ ⟨q, rfl⟩
  rw [Subsingleton.elim q p]
  exact ⟨x, hx⟩

/-- A morphism from a connected scheme to `∐ Y` factors through one `Y i`. -/
lemma range_subset_of_preconnected {T : Scheme.{u}} [PreconnectedSpace T] (a : T ⟶ ∐ Y) (i : σ)
    (t : T) (ht : a t ∈ Set.range (Sigma.ι Y i)) : Set.range a ⊆ Set.range (Sigma.ι Y i) := by
  have hc : IsClopen (a ⁻¹' Set.range (Sigma.ι Y i)) :=
    ⟨(isClosed_range_sigmaι i).preimage a.continuous,
      (Sigma.ι Y i).isOpenEmbedding.isOpen_range.preimage a.continuous⟩
  have h := hc.eq_univ ⟨t, ht⟩
  rintro _ ⟨s, rfl⟩
  have hs : s ∈ a ⁻¹' Set.range (Sigma.ι Y i) := by rw [h]; trivial
  exact hs

/-- The valuative criterion for `Sigma.desc g`, from the valuative criterion for each `g i`. -/
lemma valuativeCriterion_sigmaDesc (H : ∀ i, ValuativeCriterion (g i)) :
    ValuativeCriterion (Sigma.desc g) := by
  refine ValuativeCriterion.iff.mpr ⟨fun S => ?_, fun S => ?_⟩
  all_goals
    obtain ⟨i, hi⟩ := exists_range_subset_of_field S.K S.i₁
    let a := IsOpenImmersion.lift (Sigma.ι Y i) S.i₁ hi
    have ha : a ≫ Sigma.ι Y i = S.i₁ := IsOpenImmersion.lift_fac _ _ _
    let S' : ValuativeCommSq (g i) :=
      { R := S.R, K := S.K, i₁ := a, i₂ := S.i₂
        commSq := ⟨by rw [← Sigma.ι_comp_desc g i, ← Category.assoc, ha]; exact S.commSq.w⟩ }
  · obtain ⟨l⟩ := ((H i).existence S').exists_lift
    exact CommSq.HasLift.mk' ⟨l.l ≫ Sigma.ι Y i, by rw [← Category.assoc, l.fac_left, ha],
      by rw [Category.assoc, Sigma.ι_comp_desc, l.fac_right]⟩
  · have hU := (H i).uniqueness S'
    refine ⟨fun l₁ l₂ => ?_⟩
    have hsub : ∀ l : S.commSq.LiftStruct, Set.range l.l ⊆ Set.range (Sigma.ι Y i) := by
      intro l
      let p : Spec (.of S.K) := default
      refine range_subset_of_preconnected l.l i
        (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) p) ?_
      rw [← Scheme.Hom.comp_apply, l.fac_left]
      exact hi ⟨p, rfl⟩
    let b : S.commSq.LiftStruct → S'.commSq.LiftStruct := fun l =>
      { l := IsOpenImmersion.lift (Sigma.ι Y i) l.l (hsub l)
        fac_left := by
          rw [← cancel_mono (Sigma.ι Y i), Category.assoc, IsOpenImmersion.lift_fac, l.fac_left]
          exact ha.symm
        fac_right := by
          calc _ = IsOpenImmersion.lift (Sigma.ι Y i) l.l (hsub l) ≫ Sigma.ι Y i ≫ Sigma.desc g := by
                rw [Sigma.ι_comp_desc]
            _ = l.l ≫ Sigma.desc g := by rw [← Category.assoc, IsOpenImmersion.lift_fac]
            _ = S.i₂ := l.fac_right }
    have h := congrArg CommSq.LiftStruct.l (hU.elim (b l₁) (b l₂))
    have h₁ : (b l₁).l ≫ Sigma.ι Y i = l₁.l := IsOpenImmersion.lift_fac _ _ _
    have h₂ : (b l₂).l ≫ Sigma.ι Y i = l₂.l := IsOpenImmersion.lift_fac _ _ _
    exact CommSq.LiftStruct.ext (h₁.symm.trans ((congrArg (· ≫ Sigma.ι Y i) h).trans h₂))

/-- A finite disjoint union of quasi-compact morphisms to one scheme is quasi-compact. -/
lemma quasiCompact_sigmaDesc [Finite σ] [∀ i, QuasiCompact (g i)] :
    QuasiCompact (Sigma.desc g) := by
  refine ⟨fun U hU hc => ?_⟩
  have : Sigma.desc g ⁻¹' U = ⋃ i, Sigma.ι Y i '' (g i ⁻¹' U) := by
    ext y
    obtain ⟨i, x, rfl⟩ := exists_sigmaι_eq y
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image, sigmaDesc_apply]
    constructor
    · intro h
      exact ⟨i, x, h, rfl⟩
    · rintro ⟨j, x', hx', he⟩
      rw [← sigmaDesc_apply g i x, ← he, sigmaDesc_apply]
      exact hx'
  rw [this]
  exact isCompact_iUnion fun i =>
    (QuasiCompact.isCompact_preimage (f := g i) U hU hc).image (Sigma.ι Y i).continuous

set_option backward.isDefEq.respectTransparency false in
/-- A finite disjoint union of proper morphisms to one scheme is proper, if the source is quasi-separated. -/
theorem isProper_sigmaDesc [Finite σ] [∀ i, IsProper (g i)]
    [QuasiSeparatedSpace (∐ Y : Scheme.{u})] : IsProper (Sigma.desc g) := by
  have := quasiCompact_sigmaDesc g
  have : LocallyOfFiniteType (Sigma.desc g) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFiniteType) fun i => inferInstance
  refine IsProper.of_valuativeCriterion _ (valuativeCriterion_sigmaDesc g fun i => ?_)
  have h := (inferInstance : IsProper (g i))
  rw [IsProper.eq_valuativeCriterion] at h
  exact h.1.1.1

end Proper

section Main

open Singularity.Components

/-- A variety over a field is a Noetherian scheme. -/
lemma isNoetherian_of_isVariety {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsVariety X f] : IsNoetherian X := by
  have := IsVariety.finiteType (f := f)
  have := IsVariety.quasiCompact (f := f)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact {}

variable {X : Scheme.{u}} [IsNoetherian X]

/-- An irreducible component `Z` of a Noetherian scheme meets the open set `irreducibleComponentOpen X Z`: the generic point of `Z` is in it. -/
lemma nonempty_irreducibleComponentOpen {Z : Set X} (hZ : Z ∈ irreducibleComponents X) :
    ∃ x, x ∈ Z ∧ x ∈ X.irreducibleComponentOpen Z := by
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hη := hZ.1.isGenericPoint_genericPoint_closure
  rw [hZc.closure_eq] at hη
  refine ⟨hZ.1.genericPoint, hη.mem, mem_irreducibleComponentOpen X Z fun Z' hZ' hx => ?_⟩
  have : Z ⊆ Z' := by
    rw [← hη.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hx) (isClosed_of_mem_irreducibleComponents Z' hZ')
  exact (hZ.eq_of_subset hZ'.1 this).symm

set_option backward.isDefEq.respectTransparency false in
/-- **The reduction to integral varieties.** Let `X` be a variety over `k`. Resolve each irreducible component of `X`, and let `Y` be the disjoint union of the resolutions. Then the map `Y ⟶ X` is a resolution of `X`. -/
theorem reductionToIntegral : ReductionToIntegral.{u} := by
  intro p n hint k _ _ X f _ hX
  have := IsVariety.reduced (f := f)
  have := IsVariety.finiteType (f := f)
  have := IsVariety.quasiCompact (f := f)
  have := IsVariety.separated (f := f)
  have : IsNoetherian X := isNoetherian_of_isVariety f
  let σ := (irreducibleComponents X : Set (Set X))
  have : Finite σ := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  let Xc : σ → Scheme.{u} := fun Z => X.irreducibleComponent Z.1 Z.2
  let j : ∀ Z : σ, Xc Z ⟶ X := fun Z => X.irreducibleComponentι Z.1 Z.2
  have hvar : ∀ Z : σ, IsVariety (Xc Z) (j Z ≫ f) := fun Z =>
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hdim : ∀ Z : σ, topologicalKrullDim (Xc Z) ≤ n := fun Z =>
    ((j Z).isClosedEmbedding.isInducing.topologicalKrullDim_le).trans hX
  have hres : ∀ Z : σ, ∃ (Y : Scheme.{u}) (π : Y ⟶ Xc Z), IsResolution π := fun Z =>
    @hint k _ _ (Xc Z) (j Z ≫ f) (hvar Z) inferInstance (hdim Z)
  choose Yc πc hπ using hres
  have : ∀ Z, IsProper (πc Z) := fun Z => (hπ Z).proper
  let π : (∐ Yc : Scheme.{u}) ⟶ X := Sigma.desc fun Z => πc Z ≫ j Z
  have hπapp : ∀ Z (y : Yc Z), π (Sigma.ι Yc Z y) = j Z (πc Z y) := fun Z y => by
    rw [sigmaDesc_apply]; rfl
  -- The open sets over which the components are isomorphic to `X`.
  let W : σ → X.Opens := fun Z => X.irreducibleComponentOpen Z.1
  have hjW : ∀ Z, IsIso (j Z ∣_ W Z) := fun Z =>
    isIso_irreducibleComponentι_restrict X Z.1 Z.2 (W Z) le_rfl
  have hWrange : ∀ Z x, x ∈ W Z → ∃ x', j Z x' = x := fun Z x hx => by
    have : x ∈ Set.range (j Z) := by
      rw [range_irreducibleComponentι]; exact irreducibleComponentOpen_subset X Z.1 hx
    exact this
  have hstalk : ∀ Z (x' : Xc Z), j Z x' ∈ W Z →
      (IsRegularLocalRing (X.presheaf.stalk (j Z x')) ↔
        IsRegularLocalRing ((Xc Z).presheaf.stalk x')) := fun Z x' hx => by
    have := hjW Z
    have := isIso_stalkMap_of_isIso_restrict (j Z) (W Z) x' hx
    let e := (asIso ((j Z).stalkMap x')).commRingCatIsoToRingEquiv
    exact ⟨fun _ => IsRegularLocalRing.of_ringEquiv e, fun _ => IsRegularLocalRing.of_ringEquiv e.symm⟩
  have hother : ∀ Z Z' (x' : Xc Z'), j Z' x' ∈ W Z → Z' = Z := fun Z Z' x' hx => by
    by_contra hne
    refine hx ⟨Z'.1, ⟨Z'.2, fun h => hne (Subtype.ext h)⟩, ?_⟩
    have : j Z' x' ∈ Set.range (j Z') := ⟨x', rfl⟩
    rwa [range_irreducibleComponentι] at this
  -- The regular loci of the components and their resolutions.
  choose UZ hUZ hisoZ using fun Z => (hπ Z).isIso_over
  have hO : ∀ Z, ∃ t : Set X, IsOpen t ∧ j Z ⁻¹' t = UZ Z := fun Z =>
    (j Z).isClosedEmbedding.isInducing.isOpen_iff.mp (UZ Z).isOpen
  choose O hOo hjO using hO
  let V : σ → X.Opens := fun Z => ⟨O Z, hOo Z⟩ ⊓ W Z
  have hmemU : ∀ Z (x' : Xc Z), x' ∈ UZ Z ↔ j Z x' ∈ O Z := fun Z x' => by
    rw [← SetLike.mem_coe, ← hjO Z]; rfl
  have hR : ∀ x : X, x ∈ regularLocus X ↔ ∃ Z, x ∈ V Z := by
    intro x
    constructor
    · intro hx
      have : IsRegularLocalRing (X.presheaf.stalk x) := hx
      have := Singularity.Algebra.isDomain_of_isRegularLocalRing (X.presheaf.stalk x)
      obtain ⟨Z0, hZ0, hxZ0⟩ := exists_mem_irreducibleComponents x
      let Z : σ := ⟨Z0, hZ0⟩
      have hxW : x ∈ W Z := mem_irreducibleComponentOpen X Z0 fun Z' hZ' hx' =>
        eq_of_mem_of_isDomain hZ' hZ0 hx' hxZ0
      obtain ⟨x', rfl⟩ := hWrange Z x hxW
      have hreg : x' ∈ UZ Z := by
        rw [← SetLike.mem_coe, hUZ Z]
        exact (hstalk Z x' hxW).mp hx
      exact ⟨Z, (hmemU Z x').mp hreg, hxW⟩
    · rintro ⟨Z, hxO, hxW⟩
      obtain ⟨x', rfl⟩ := hWrange Z x hxW
      have hreg : x' ∈ UZ Z := (hmemU Z x').mpr hxO
      rw [← SetLike.mem_coe, hUZ Z] at hreg
      exact (hstalk Z x' hxW).mpr hreg
  refine ⟨∐ Yc, π, ⟨?_, ?_, ?_, ?_⟩⟩
  · -- `Y` is regular.
    intro y
    obtain ⟨Z, y', rfl⟩ := exists_sigmaι_eq y
    have := (hπ Z).regular y'
    let e := (asIso ((Sigma.ι Yc Z).stalkMap y')).commRingCatIsoToRingEquiv
    exact IsRegularLocalRing.of_ringEquiv e.symm
  · -- `π` is proper.
    have : LocallyOfFiniteType (Sigma.desc fun Z => πc Z ≫ j Z ≫ f) :=
      IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFiniteType) fun Z => inferInstance
    have : IsLocallyNoetherian (∐ Yc : Scheme.{u}) :=
      LocallyOfFiniteType.isLocallyNoetherian (Sigma.desc fun Z => πc Z ≫ j Z ≫ f)
    exact isProper_sigmaDesc _
  · -- `π` is an isomorphism over the regular locus.
    refine ⟨⨆ Z, V Z, ?_, isIso_restrict_iSup π V fun Z => ?_⟩
    · ext x
      simp only [Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
      exact (hR x).symm
    have := hisoZ Z
    have : IsIso (j Z ∣_ V Z) :=
      isIso_irreducibleComponentι_restrict X Z.1 Z.2 (V Z) inf_le_right
    have hA : j Z ⁻¹ᵁ V Z ≤ UZ Z := fun x' hx' => (hmemU Z x').mpr hx'.1
    have : IsIso (πc Z ∣_ j Z ⁻¹ᵁ V Z) := isIso_restrict_of_le (πc Z) hA
    have hg : IsIso ((πc Z ≫ j Z) ∣_ V Z) := by
      rw [morphismRestrict_comp]; infer_instance
    have hsurj : Surjective (Sigma.ι Yc Z ∣_ π ⁻¹ᵁ V Z) := by
      refine ⟨fun v => ?_⟩
      obtain ⟨Z', y', hy'⟩ := exists_sigmaι_eq v.1
      have hv : π (Sigma.ι Yc Z' y') ∈ V Z := by rw [hy']; exact v.2
      rw [hπapp] at hv
      have hZ := (hother Z Z' (πc Z' y') hv.2).symm
      subst hZ
      refine ⟨⟨y', show _ ∈ V Z by rw [hy']; exact v.2⟩, ?_⟩
      apply Subtype.ext
      exact (morphismRestrict_base_coe _ _ _).trans hy'
    have : IsIso (Sigma.ι Yc Z ∣_ π ⁻¹ᵁ V Z) :=
      (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, hsurj⟩
    have hg' : IsIso ((Sigma.ι Yc Z ≫ π) ∣_ V Z) := by
      rw [show Sigma.ι Yc Z ≫ π = πc Z ≫ j Z from Sigma.ι_comp_desc _ _]
      exact hg
    rw [morphismRestrict_comp] at hg'
    exact IsIso.of_isIso_comp_left (Sigma.ι Yc Z ∣_ π ⁻¹ᵁ V Z) (π ∣_ V Z)
  · -- The preimage of the regular locus is dense.
    refine dense_iff_inter_open.mpr fun G hG ⟨y, hy⟩ => ?_
    obtain ⟨Z, y₀, rfl⟩ := exists_sigmaι_eq y
    let G' : Set (Yc Z) := Sigma.ι Yc Z ⁻¹' G
    have hG' : IsOpen G' := hG.preimage (Sigma.ι Yc Z).continuous
    obtain ⟨y₁, hy₁G, hy₁R⟩ := dense_iff_inter_open.mp (hπ Z).dense G' hG' ⟨y₀, hy⟩
    have hy₁U : πc Z y₁ ∈ UZ Z := by rw [← SetLike.mem_coe, hUZ Z]; exact hy₁R
    have := hisoZ Z
    let T : Set (πc Z ⁻¹ᵁ UZ Z) := (πc Z ⁻¹ᵁ UZ Z).ι ⁻¹' G'
    let S : Set (Xc Z) := (UZ Z).ι '' ((πc Z ∣_ UZ Z) '' T)
    have hS : IsOpen S := (UZ Z).ι.isOpenEmbedding.isOpenMap _
      ((πc Z ∣_ UZ Z).isOpenEmbedding.isOpenMap _ (hG'.preimage (πc Z ⁻¹ᵁ UZ Z).ι.continuous))
    have hSne : S.Nonempty := ⟨_, ⟨_, ⟨⟨y₁, hy₁U⟩, hy₁G, rfl⟩, rfl⟩⟩
    obtain ⟨x₀, hx₀, hx₀W⟩ := nonempty_irreducibleComponentOpen Z.2
    obtain ⟨x₀', rfl⟩ := hWrange Z x₀ hx₀W
    have hWne : ((j Z) ⁻¹' (W Z : Set X)).Nonempty := ⟨x₀', hx₀W⟩
    obtain ⟨x, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, hxW⟩ := nonempty_preirreducible_inter hS
      ((W Z).isOpen.preimage (j Z).continuous) hSne hWne
    have hux : (UZ Z).ι ((πc Z ∣_ UZ Z) u) = πc Z u.1 := morphismRestrict_base_coe _ _ _
    rw [hux] at hxW
    have hU' : πc Z u.1 ∈ UZ Z := by rw [← hux]; exact ((πc Z ∣_ UZ Z) u).2
    refine ⟨Sigma.ι Yc Z u.1, hu, ?_⟩
    show π (Sigma.ι Yc Z u.1) ∈ regularLocus X
    rw [hπapp, hR]
    exact ⟨Z, (hmemU Z _).mp hU', hxW⟩

end Main

end Singularity.Reduction
