/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# The center of a valuation on a separated scheme

This file proves Volume 3, Proposition 1.4.3 of the handbook. Let `X` be an integral separated scheme with function field `K`. Then each valuation ring of `K` has at most one center on `X`.

A point `x` of `X` is a center of the valuation ring `V ⊆ K` if `V` dominates the local ring `𝒪_{X,x} ⊆ K` (Volume 3, Definition 1.4.1 of the handbook). In Lean this is `Singularity.Scheme.IsCenter`: the image of `𝒪_{X,x}` in `K` is in `V`, and the image of the maximal ideal of `𝒪_{X,x}` has valuation less than `1`.

* `Singularity.Scheme.IsCenter`: the center of a valuation ring.
* `Singularity.Scheme.eq_of_isCenter`: Proposition 1.4.3 of the handbook.

The handbook proof uses affine open sets and [Har, Chapter II, Exercise 4.3]. The proof here uses the uniqueness part of the valuative criterion of separatedness in Mathlib. A center `x` of `V` gives the morphism `Spec V → Spec 𝒪_{X,x} → X`. This morphism extends the morphism `Spec K → X` at the generic point, and it sends the closed point of `Spec V` to `x`. Since `X` is separated, there is at most one such extension.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Singularity.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}} [IsIntegral X]

/-- A point `x` of `X` is a center of the valuation ring `V` of the function field of `X` if `V` dominates the local ring `𝒪_{X,x}` (Volume 3, Definition 1.4.1 of the handbook). -/
def IsCenter (V : ValuationSubring X.functionField) (x : X) : Prop :=
  (∀ f : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField f ∈ V) ∧
    ∀ f ∈ maximalIdeal (X.presheaf.stalk x),
      V.valuation (algebraMap (X.presheaf.stalk x) X.functionField f) < 1

/-- The map `𝒪_{X,x} → V` for a center `x` of `V`. -/
noncomputable def stalkToCenter {V : ValuationSubring X.functionField} {x : X}
    (h : IsCenter V x) : X.presheaf.stalk x →+* V :=
  (algebraMap (X.presheaf.stalk x) X.functionField).codRestrict V.toSubring h.1

theorem isLocalHom_stalkToCenter {V : ValuationSubring X.functionField} {x : X}
    (h : IsCenter V x) : IsLocalHom (stalkToCenter h) := by
  refine ⟨fun f hf => ?_⟩
  by_contra hu
  have hlt := h.2 f ((mem_maximalIdeal f).mpr hu)
  have hv : V.valuation ((stalkToCenter h f : V) : X.functionField) = 1 :=
    (V.valuation_eq_one_iff (stalkToCenter h f)).mp hf
  exact (ne_of_lt hlt) hv

/-- The valuative square `Spec K → X`, `Spec V → ⊤` of a valuation ring `V` of the function field `K` of `X`. -/
noncomputable def valuativeCommSq (V : ValuationSubring X.functionField) :
    ValuativeCommSq (terminal.from X) where
  R := V
  K := X.functionField
  i₁ := X.fromSpecStalk (genericPoint X)
  i₂ := terminal.from _
  commSq := ⟨terminal.hom_ext _ _⟩

/-- A center `x` of `V` gives the morphism `Spec V → Spec 𝒪_{X,x} → X`. -/
noncomputable def specToCenter {V : ValuationSubring X.functionField} {x : X}
    (h : IsCenter V x) : Spec (CommRingCat.of V) ⟶ X :=
  Spec.map (CommRingCat.ofHom (stalkToCenter h)) ≫ X.fromSpecStalk x

theorem specToCenter_fac {V : ValuationSubring X.functionField} {x : X} (h : IsCenter V x) :
    Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ specToCenter h =
      X.fromSpecStalk (genericPoint X) := by
  rw [specToCenter, ← Category.assoc, ← Spec.map_comp]
  have : CommRingCat.ofHom (stalkToCenter h) ≫
      CommRingCat.ofHom (algebraMap V X.functionField) =
      X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) := by
    ext f
    rfl
  rw [this, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

theorem specToCenter_closedPoint {V : ValuationSubring X.functionField} {x : X}
    (h : IsCenter V x) : specToCenter h (closedPoint (CommRingCat.of V)) = x := by
  have := isLocalHom_stalkToCenter h
  show X.fromSpecStalk x
    (Spec.map (CommRingCat.ofHom (stalkToCenter h)) (closedPoint (CommRingCat.of V))) = x
  have hc : Spec.map (CommRingCat.ofHom (stalkToCenter h)) (closedPoint (CommRingCat.of V)) =
      closedPoint (X.presheaf.stalk x) :=
    Spec_closedPoint
  rw [hc, Scheme.fromSpecStalk_closedPoint]

/-- The morphism `specToCenter` is a lift of the valuative square. -/
noncomputable def liftOfIsCenter {V : ValuationSubring X.functionField} {x : X}
    (h : IsCenter V x) : (valuativeCommSq V).commSq.LiftStruct where
  l := specToCenter h
  fac_left := specToCenter_fac h
  fac_right := terminal.hom_ext _ _

/-- Let `X` be an integral separated scheme with function field `K`. Then each valuation ring `V` of `K` has at most one center on `X` (Volume 3, Proposition 1.4.3 of the handbook). -/
theorem eq_of_isCenter [X.IsSeparated] {V : ValuationSubring X.functionField} {x y : X}
    (hx : IsCenter V x) (hy : IsCenter V y) : x = y := by
  have := IsSeparated.valuativeCriterion (terminal.from X) (valuativeCommSq V)
  have hl : specToCenter hx = specToCenter hy :=
    congrArg CommSq.LiftStruct.l (Subsingleton.elim (liftOfIsCenter hx) (liftOfIsCenter hy))
  rw [← specToCenter_closedPoint hx, ← specToCenter_closedPoint hy, hl]

end Singularity.Scheme
