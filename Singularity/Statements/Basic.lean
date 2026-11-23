/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.KrullDimension

/-!
# The vocabulary of the statements

This file has the definitions that the main statements use: the regular locus of a scheme, a regular scheme, a resolution of singularities and a variety over a field. The text is in spec 06.1 of the project.

Where Mathlib has a notion, this file uses it. `IsRegularLocalRing` is the class of Mathlib (Stacks tag 00KU): a Noetherian local ring whose maximal ideal has `dim R` generators.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace Singularity

/-- The points of `X` whose local ring is a regular local ring. -/
def regularLocus (X : Scheme.{u}) : Set X :=
  {x | IsRegularLocalRing (X.presheaf.stalk x)}

/-- The scheme `X` is regular: each local ring of `X` is a regular local ring. -/
def IsRegularScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

/-- A morphism `π : Y ⟶ X` is a resolution of singularities of `X`.

The four conditions are:
* `Y` is regular;
* `π` is proper;
* the regular locus of `X` is open, and `π` is an isomorphism over it;
* the preimage of the regular locus is dense in `Y`.

The last condition stops `Y` from having a component that lies over the singular locus only. -/
structure IsResolution {X Y : Scheme.{u}} (π : Y ⟶ X) : Prop where
  regular : IsRegularScheme Y
  proper : IsProper π
  isIso_over : ∃ U : X.Opens, (U : Set X) = regularLocus X ∧ IsIso (π ∣_ U)
  dense : Dense (π.base ⁻¹' regularLocus X)

/-- A variety over the field `k`, in the sense of the project: a reduced scheme that is separated and of finite type over `k`. A variety need not be irreducible. -/
class IsVariety {k : Type u} [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) : Prop where
  reduced : IsReduced X
  finiteType : LocallyOfFiniteType f
  quasiCompact : QuasiCompact f
  separated : IsSeparated f

lemma regularLocus_eq_univ_iff (X : Scheme.{u}) : regularLocus X = Set.univ ↔ IsRegularScheme X := by
  simp [regularLocus, IsRegularScheme, Set.eq_univ_iff_forall]

end Singularity
