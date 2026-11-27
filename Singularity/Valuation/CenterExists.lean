/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.SchemeCenter

/-!
# The center of a valuation on a proper scheme

This file proves Volume 3, Proposition 1.4.4 of the handbook. Let `k` be a field, let `X` be an integral scheme that is proper over `k`, and let `K` be its function field. Then each valuation ring `V` of `K` with `k ⊆ V` has exactly one center on `X`.

In Lean the scheme `X` comes with a proper morphism `f : X ⟶ Spec k`. The map `k → K` is `Singularity.Scheme.structureMap f`, the ring map of the composite `Spec K ⟶ X ⟶ Spec k`. The condition `k ⊆ V` states that the image of this map is in `V`.

* `Singularity.Scheme.structureMap`: the map `k → K` of a scheme `X` over `Spec k`.
* `Singularity.Scheme.exists_isCenter`: the existence part of Proposition 1.4.4.
* `Singularity.Scheme.existsUnique_isCenter`: Proposition 1.4.4 of the handbook.

The proof is the proof of the handbook. The existence part of the valuative criterion of properness in Mathlib gives a morphism `g : Spec V ⟶ X` over `k` that extends `Spec K ⟶ X`. Let `x` be the image of the closed point. The local homomorphism `𝒪_{X,x} → V` of `g` composed with `V ⊆ K` is the map `𝒪_{X,x} → K`, because the morphism `Spec 𝒪_{X,x} ⟶ X` is a monomorphism. So `x` is a center of `V`. Uniqueness is Proposition 1.4.3 (`Singularity.Scheme.eq_of_isCenter`).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Singularity.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}} [IsIntegral X] {k : Type u} [Field k]

/-- The map `k → K` of a scheme `X` over `Spec k`, where `K` is the function field of `X`. It is the ring map of the composite `Spec K ⟶ X ⟶ Spec k`. -/
noncomputable def structureMap (f : X ⟶ Spec (CommRingCat.of k)) : k →+* X.functionField :=
  (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ f)).hom

/-- The valuative square of a valuation ring `V` of the function field with `k ⊆ V`. -/
noncomputable def valuativeCommSqOver (f : X ⟶ Spec (CommRingCat.of k))
    (V : ValuationSubring X.functionField) (hV : ∀ a : k, structureMap f a ∈ V) :
    ValuativeCommSq f where
  R := V
  K := X.functionField
  i₁ := X.fromSpecStalk (genericPoint X)
  i₂ := Spec.map (CommRingCat.ofHom ((structureMap f).codRestrict V.toSubring hV))
  commSq := ⟨by
    rw [← Spec.map_comp]
    have : CommRingCat.ofHom ((structureMap f).codRestrict V.toSubring hV) ≫
        CommRingCat.ofHom (algebraMap V X.functionField) =
        Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ f) := by
      ext a
      rfl
    rw [this, Spec.map_preimage]⟩

/-- Let `X` be an integral scheme that is proper over a field `k` with function field `K`. Then each valuation ring `V` of `K` with `k ⊆ V` has a center on `X` (Volume 3, Proposition 1.4.4 of the handbook, existence). -/
theorem exists_isCenter (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (V : ValuationSubring X.functionField) (hV : ∀ a : k, structureMap f a ∈ V) :
    ∃ x : X, IsCenter V x := by
  have hE : ValuativeCriterion.Existence f := by
    have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) f := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact this.1
  obtain ⟨l⟩ := (hE (valuativeCommSqOver f V hV)).exists_lift
  let g : Spec (CommRingCat.of V) ⟶ X := l.l
  have hg : Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ g =
      X.fromSpecStalk (genericPoint X) := l.fac_left
  refine ⟨g (closedPoint (CommRingCat.of V)), ?_⟩
  set x := g (closedPoint (CommRingCat.of V))
  let φ : X.presheaf.stalk x ⟶ CommRingCat.of V := AlgebraicGeometry.Scheme.stalkClosedPointTo g
  have hφ : IsLocalHom φ.hom := AlgebraicGeometry.Scheme.isLocalHom_stalkClosedPointTo g
  have hspec : X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) := by
    ext a
    rfl
  have key : φ ≫ CommRingCat.ofHom (algebraMap V X.functionField) =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk x), Spec.map_comp, Category.assoc,
      AlgebraicGeometry.Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hg, ← hspec,
      AlgebraicGeometry.Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have heq : ∀ s : X.presheaf.stalk x,
      algebraMap (X.presheaf.stalk x) X.functionField s = ((φ.hom s : V) : X.functionField) :=
    fun s => (congrArg (fun ψ => ψ.hom s) key).symm
  refine ⟨fun s => heq s ▸ (φ.hom s).2, fun s hs => ?_⟩
  rw [heq s]
  exact (ValuationSubring.valuation_lt_one_iff V (φ.hom s)).1
    (map_nonunit φ.hom s ((mem_maximalIdeal s).mp hs))

/-- Let `k` be a field, let `X` be an integral scheme that is proper over `k`, and let `K` be its function field. Then each valuation ring `V` of `K` with `k ⊆ V` has exactly one center on `X` (Volume 3, Proposition 1.4.4 of the handbook). -/
theorem existsUnique_isCenter (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (V : ValuationSubring X.functionField) (hV : ∀ a : k, structureMap f a ∈ V) :
    ∃! x : X, IsCenter V x := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  obtain ⟨x, hx⟩ := exists_isCenter f V hV
  exact ⟨x, hx, fun y hy => eq_of_isCenter hy hx⟩

end Singularity.Scheme
