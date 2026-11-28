/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.SchemeCenter
import Singularity.Valuation.EtaleGenerator
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# The center on a resolution, and étale generators for the trivial valuation

This file proves two results of Volume 5 of the handbook.

**Proposition 1.4.5, first part.** Let `π : X' ⟶ X` be a proper morphism of integral schemes, and
let `V` be a valuation ring of the function field `K'` of `X'`. Let `x` be a center of `V` on `X`.
Then `V` has a center `x'` on `X'` with `π x' = x`. If `X` is separated, this center is unique. If
each local ring of `X'` is regular, then `x'` is a regular point. For a resolution `π`, this is the
first claim of Proposition 1.4.5.

The function field of `X` does not appear in the statement. A center of `V` on `X` along `π` is a
point `x` that is a specialization of `π(η')`, where `η'` is the generic point of `X'`, such that
`V` dominates the local ring `𝒪_{X,x}` under the map `𝒪_{X,x} → 𝒪_{X,π(η')} → K'`. If `π` is
dominant, then `π(η')` is the generic point of `X`, and this map is `𝒪_{X,x} → K → K'`. If `π` is
birational, then `K → K'` is an isomorphism, and this is the center of the handbook.

The proof uses the existence part of the valuative criterion of properness, as in
`Singularity.Scheme.exists_isCenter`. The center `x` gives a morphism `Spec V ⟶ X` that extends
`Spec K' ⟶ X' ⟶ X`. The criterion lifts it to `Spec V ⟶ X'`. The image of the closed point is the
center on `X'`.

**Theorem 3.1.5 and Proposition 3.1.4, case of the trivial valuation.** Let `K/K₀` be a finite
extension, and let `V = K` be the trivial valuation ring. Then there is an étale generator of
`K/K₀` at `V` if and only if `K/K₀` is separable. The direction "only if" is Proposition 3.1.4 for
the trivial valuation: then `e = d = 1`, and the residue extension is `K/K₀`.

## Main definitions

* `Singularity.Scheme.stalkToFunctionFieldAlong`: the map `𝒪_{X,x} → K'` along `π`.
* `Singularity.Scheme.IsCenterAlong`: the point `x` of `X` is a center of `V` along `π`.

## Main results

* `Singularity.Scheme.map_genericPoint_of_isDominant`: a dominant morphism maps the generic point
  to the generic point.
* `Singularity.Scheme.exists_isCenter_of_isCenterAlong`: a center on `X` lifts to a center on `X'`
  along a proper morphism.
* `Singularity.Scheme.existsUnique_isCenter_of_isCenterAlong`: the lift is unique if `X` is
  separated.
* `Singularity.Scheme.exists_isCenter_isRegularLocalRing_of_isCenterAlong`: Proposition 1.4.5, first
  part. The center on a regular `X'` is a regular point.
* `Singularity.isEtaleGenerator_top_iff`: for the trivial valuation, `z` is an étale generator if
  and only if `K = K₀(z)` and `P'(z) ≠ 0`.
* `Singularity.exists_isEtaleGenerator_top_iff_isSeparable`: Theorem 3.1.5 for the trivial
  valuation.
* `Singularity.isSeparable_of_isEtaleGenerator_top`: Proposition 3.1.4 for the trivial valuation.

## What is not proved

* The second claim of Proposition 1.4.5: if each model has a resolution, then each valuation has
  local uniformization. This needs the passage from scheme models to the affine models of
  `Singularity.HasLocalUniformization`, and the existence of a model on which `V` has a center.
* Proposition 3.1.4 for a nontrivial valuation. The proof of the handbook uses the henselization,
  which is not in the library.
* Theorem 3.1.5 for a nontrivial valuation. It needs Proposition 3.1.4 and the second part of
  Lemma 1.3.3. Local uniformization for the trivial valuation is
  `Singularity.hasLocalUniformization_top`.
* Theorems 3.1.1 and 3.1.2, Theorem 1.4.1, Corollary 1.4.6, and Theorems 5.1.1, 5.1.2 and 5.1.3.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Singularity

namespace Scheme

variable {X X' : AlgebraicGeometry.Scheme.{u}} [IsIntegral X] [IsIntegral X'] (π : X' ⟶ X)

/-- A dominant morphism of integral schemes maps the generic point to the generic point. -/
theorem map_genericPoint_of_isDominant [IsDominant π] :
    π (genericPoint X') = genericPoint X := by
  symm
  apply (genericPoint_spec X).eq
  rw [isGenericPoint_def]
  refine Set.eq_univ_of_univ_subset ?_
  have hd : closure (Set.range π) = Set.univ := π.denseRange.closure_range
  rw [← hd]
  refine closure_minimal ?_ isClosed_closure
  rintro _ ⟨y, rfl⟩
  have hy : genericPoint X' ⤳ y := (genericPoint_spec X').specializes trivial
  exact specializes_iff_mem_closure.mp (hy.map π.continuous)

/-- The map `𝒪_{X,x} → 𝒪_{X,π(η')} → K'` along `π`, where `η'` is the generic point of `X'` and
`K'` is the function field of `X'`. -/
noncomputable def stalkToFunctionFieldAlong {x : X} (hx : π (genericPoint X') ⤳ x) :
    X.presheaf.stalk x →+* X'.functionField :=
  (X.presheaf.stalkSpecializes hx ≫ π.stalkMap (genericPoint X')).hom

/-- The point `x` of `X` is a center of the valuation ring `V` of the function field `K'` of `X'`
along `π`: it is a specialization of `π(η')`, and `V` dominates `𝒪_{X,x}` under the map
`𝒪_{X,x} → K'`. For a birational `π` this is a center of `V` on `X`. -/
def IsCenterAlong (V : ValuationSubring X'.functionField) (x : X) : Prop :=
  ∃ hx : π (genericPoint X') ⤳ x,
    (∀ f : X.presheaf.stalk x, stalkToFunctionFieldAlong π hx f ∈ V) ∧
      ∀ f ∈ maximalIdeal (X.presheaf.stalk x), V.valuation (stalkToFunctionFieldAlong π hx f) < 1

variable {π}

/-- The map `𝒪_{X,x} → V` for a center `x` of `V` on `X` along `π`. -/
noncomputable def stalkToCenterAlong {V : ValuationSubring X'.functionField} {x : X}
    (hx : π (genericPoint X') ⤳ x) (h : ∀ f, stalkToFunctionFieldAlong π hx f ∈ V) :
    X.presheaf.stalk x →+* V :=
  (stalkToFunctionFieldAlong π hx).codRestrict V.toSubring h

/-- A center `x` of `V` on `X` along `π` gives the morphism `Spec V ⟶ Spec 𝒪_{X,x} ⟶ X`. -/
noncomputable def specToCenterAlong {V : ValuationSubring X'.functionField} {x : X}
    (hx : π (genericPoint X') ⤳ x) (h : ∀ f, stalkToFunctionFieldAlong π hx f ∈ V) :
    Spec (CommRingCat.of V) ⟶ X :=
  Spec.map (CommRingCat.ofHom (stalkToCenterAlong hx h)) ≫ X.fromSpecStalk x

omit [IsIntegral X] in
theorem specToCenterAlong_fac {V : ValuationSubring X'.functionField} {x : X}
    (hx : π (genericPoint X') ⤳ x) (h : ∀ f, stalkToFunctionFieldAlong π hx f ∈ V) :
    X'.fromSpecStalk (genericPoint X') ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap V X'.functionField)) ≫ specToCenterAlong hx h := by
  rw [specToCenterAlong, ← Category.assoc, ← Spec.map_comp]
  have : CommRingCat.ofHom (stalkToCenterAlong hx h) ≫
      CommRingCat.ofHom (algebraMap V X'.functionField) =
      X.presheaf.stalkSpecializes hx ≫ π.stalkMap (genericPoint X') := by
    ext f
    rfl
  rw [this, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

omit [IsIntegral X] in
theorem specToCenterAlong_closedPoint {V : ValuationSubring X'.functionField} {x : X}
    (hx : π (genericPoint X') ⤳ x) (h : ∀ f, stalkToFunctionFieldAlong π hx f ∈ V)
    (h' : ∀ f ∈ maximalIdeal (X.presheaf.stalk x),
      V.valuation (stalkToFunctionFieldAlong π hx f) < 1) :
    specToCenterAlong hx h (closedPoint (CommRingCat.of V)) = x := by
  have : IsLocalHom (stalkToCenterAlong hx h) := by
    refine ⟨fun f hf => ?_⟩
    by_contra hu
    have hlt := h' f ((mem_maximalIdeal f).mpr hu)
    have hv : V.valuation ((stalkToCenterAlong hx h f : V) : X'.functionField) = 1 :=
      (V.valuation_eq_one_iff _).mp hf
    exact (ne_of_lt hlt) hv
  show X.fromSpecStalk x (Spec.map (CommRingCat.ofHom (stalkToCenterAlong hx h))
    (closedPoint (CommRingCat.of V))) = x
  have hc : Spec.map (CommRingCat.ofHom (stalkToCenterAlong hx h))
      (closedPoint (CommRingCat.of V)) = closedPoint (X.presheaf.stalk x) :=
    Spec_closedPoint
  rw [hc, Scheme.fromSpecStalk_closedPoint]

/-- The valuative square `Spec K' ⟶ X'`, `Spec V ⟶ X` of a center of `V` on `X` along `π`. -/
noncomputable def valuativeCommSqAlong {V : ValuationSubring X'.functionField} {x : X}
    (hx : π (genericPoint X') ⤳ x) (h : ∀ f, stalkToFunctionFieldAlong π hx f ∈ V) :
    ValuativeCommSq π where
  R := V
  K := X'.functionField
  i₁ := X'.fromSpecStalk (genericPoint X')
  i₂ := specToCenterAlong hx h
  commSq := ⟨specToCenterAlong_fac hx h⟩

omit [IsIntegral X] in
/-- Let `π : X' ⟶ X` be a proper morphism of integral schemes, and let `V` be a valuation ring of
the function field of `X'`. If `V` has a center `x` on `X` along `π`, then `V` has a center `x'` on
`X'` with `π x' = x`. -/
theorem exists_isCenter_of_isCenterAlong [IsProper π] {V : ValuationSubring X'.functionField}
    {x : X} (hc : IsCenterAlong π V x) : ∃ x' : X', IsCenter V x' ∧ π x' = x := by
  obtain ⟨hx, h, h'⟩ := hc
  have hE : ValuativeCriterion.Existence π := by
    have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) π := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact this.1
  obtain ⟨l⟩ := (hE (valuativeCommSqAlong hx h)).exists_lift
  let g : Spec (CommRingCat.of V) ⟶ X' := l.l
  have hg : Spec.map (CommRingCat.ofHom (algebraMap V X'.functionField)) ≫ g =
      X'.fromSpecStalk (genericPoint X') := l.fac_left
  have hg' : g ≫ π = specToCenterAlong hx h := l.fac_right
  refine ⟨g (closedPoint (CommRingCat.of V)), ?_, ?_⟩
  · set y := g (closedPoint (CommRingCat.of V))
    let φ : X'.presheaf.stalk y ⟶ CommRingCat.of V :=
      AlgebraicGeometry.Scheme.stalkClosedPointTo g
    have hφ : IsLocalHom φ.hom := AlgebraicGeometry.Scheme.isLocalHom_stalkClosedPointTo g
    have hspec : X'.presheaf.stalkSpecializes ((genericPoint_spec X').specializes trivial) =
        CommRingCat.ofHom (algebraMap (X'.presheaf.stalk y) X'.functionField) := by
      ext a
      rfl
    have key : φ ≫ CommRingCat.ofHom (algebraMap V X'.functionField) =
        CommRingCat.ofHom (algebraMap (X'.presheaf.stalk y) X'.functionField) := by
      apply Spec.map_injective
      rw [← cancel_mono (X'.fromSpecStalk y), Spec.map_comp, Category.assoc,
        AlgebraicGeometry.Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hg, ← hspec,
        AlgebraicGeometry.Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    have heq : ∀ s : X'.presheaf.stalk y,
        algebraMap (X'.presheaf.stalk y) X'.functionField s = ((φ.hom s : V) : X'.functionField) :=
      fun s => (congrArg (fun ψ => ψ.hom s) key).symm
    refine ⟨fun s => heq s ▸ (φ.hom s).2, fun s hs => ?_⟩
    rw [heq s]
    exact (ValuationSubring.valuation_lt_one_iff V (φ.hom s)).1
      (map_nonunit φ.hom s ((mem_maximalIdeal s).mp hs))
  · calc π (g (closedPoint (CommRingCat.of V)))
        = (g ≫ π) (closedPoint (CommRingCat.of V)) := rfl
      _ = specToCenterAlong hx h (closedPoint (CommRingCat.of V)) := by rw [hg']
      _ = x := specToCenterAlong_closedPoint hx h h'

omit [IsIntegral X] in
/-- Let `π : X' ⟶ X` be a proper morphism of integral schemes with `X` separated. If `V` has a
center `x` on `X` along `π`, then `V` has exactly one center on `X'`, and it maps to `x`. -/
theorem existsUnique_isCenter_of_isCenterAlong [IsProper π] [X.IsSeparated]
    {V : ValuationSubring X'.functionField} {x : X} (hc : IsCenterAlong π V x) :
    ∃! x' : X', IsCenter V x' ∧ π x' = x := by
  have : X'.IsSeparated := ⟨by rw [← terminal.comp_from π]; infer_instance⟩
  obtain ⟨x', hx', hπ⟩ := exists_isCenter_of_isCenterAlong hc
  exact ⟨x', ⟨hx', hπ⟩, fun y hy => eq_of_isCenter hy.1 hx'⟩

omit [IsIntegral X] in
/-- **The center on a resolution** (Volume 5, Proposition 1.4.5 of the handbook, first part). Let
`π : X' ⟶ X` be a proper morphism of integral schemes, and assume that each local ring of `X'` is
a regular local ring. Let `V` be a valuation ring of the function field of `X'` with a center `x`
on `X` along `π`. Then `V` has a center `x'` on `X'` over `x`, and `x'` is a regular point. -/
theorem exists_isCenter_isRegularLocalRing_of_isCenterAlong [IsProper π]
    (hreg : ∀ y : X', IsRegularLocalRing (X'.presheaf.stalk y))
    {V : ValuationSubring X'.functionField} {x : X} (hc : IsCenterAlong π V x) :
    ∃ x' : X', IsCenter V x' ∧ π x' = x ∧ IsRegularLocalRing (X'.presheaf.stalk x') := by
  obtain ⟨x', hx', hπ⟩ := exists_isCenter_of_isCenterAlong hc
  exact ⟨x', hx', hπ, hreg x'⟩

end Scheme

/-! ### Étale generators for the trivial valuation -/

section Trivial

open Polynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {K₀ : IntermediateField k K}

/-- For the trivial valuation ring `V = K`, an element `z` is an étale generator of `K/K₀` if and
only if `K = K₀(z)` and `P'(z) ≠ 0`, where `P` is the minimal polynomial of `z` over `K₀`. -/
theorem isEtaleGenerator_top_iff {z : K} :
    IsEtaleGenerator K₀ ⊤ z ↔
      IntermediateField.adjoin K₀ {z} = ⊤ ∧ aeval z (derivative (minpoly K₀ z)) ≠ 0 := by
  refine ⟨fun hz => ⟨hz.adjoin_eq_top, hz.aeval_derivative_ne_zero⟩, fun ⟨h1, h2⟩ => ?_⟩
  refine ⟨ValuationSubring.mem_top z, h1, fun i => ValuationSubring.mem_top _, ?_⟩
  exact ((⊤ : ValuationSubring K).valuation_eq_one_iff
    ⟨_, ValuationSubring.mem_top _⟩).mp (Ne.isUnit fun h0 => h2 (congrArg Subtype.val h0))

/-- **Proposition 3.1.4 for the trivial valuation** (Volume 5 of the handbook). If `K/K₀` has an
étale generator at the trivial valuation ring `K`, then `K/K₀` is separable. -/
theorem isSeparable_of_isEtaleGenerator_top {z : K} (hz : IsEtaleGenerator K₀ ⊤ z) :
    Algebra.IsSeparable K₀ K := by
  have hint : IsIntegral K₀ z := by
    by_contra hni
    have h := hz.aeval_derivative_ne_zero
    rw [minpoly.eq_zero hni, derivative_zero, map_zero] at h
    exact h rfl
  have hsep : IsSeparable K₀ z :=
    (separable_iff_derivative_ne_zero (minpoly.irreducible hint)).mpr fun h0 =>
      hz.aeval_derivative_ne_zero (by rw [h0, map_zero])
  have : Algebra.IsSeparable K₀ (IntermediateField.adjoin K₀ {z}) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K₀ K).mpr hsep
  refine ⟨fun x => ?_⟩
  have hx : x ∈ IntermediateField.adjoin K₀ {z} := by rw [hz.adjoin_eq_top]; trivial
  exact IntermediateField.isSeparable_of_mem_isSeparable K₀ K hx

/-- **Theorem 3.1.5 for the trivial valuation** (Volume 5 of the handbook). Let `K/K₀` be a finite
extension. Then `K/K₀` has an étale generator at the trivial valuation ring `K` if and only if
`K/K₀` is separable. -/
theorem exists_isEtaleGenerator_top_iff_isSeparable [FiniteDimensional K₀ K] :
    (∃ z, IsEtaleGenerator K₀ ⊤ z) ↔ Algebra.IsSeparable K₀ K := by
  refine ⟨fun ⟨z, hz⟩ => isSeparable_of_isEtaleGenerator_top hz, fun hs => ?_⟩
  obtain ⟨z, hz⟩ := Field.exists_primitive_element K₀ K
  refine ⟨z, isEtaleGenerator_top_iff.mpr ⟨hz, ?_⟩⟩
  exact (Algebra.IsSeparable.isSeparable K₀ z).aeval_derivative_ne_zero (minpoly.aeval K₀ z)

end Trivial

end Singularity
