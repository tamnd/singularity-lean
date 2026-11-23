/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.

The definition `HasResolution` is copied from FormalConjectures/Wikipedia/ResolutionOfSingularities.lean of google-deepmind/formal-conjectures (Copyright 2026 The Formal Conjectures Authors, Apache License 2.0). The copy changes only the namespace.
-/
import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.Perfect
import Singularity.Statements.Main

/-!
# The statement of formal-conjectures

google-deepmind/formal-conjectures states resolution of singularities as `Scheme.HasResolution`: an integral scheme `Y`, smooth over the base, with a proper morphism `Y ⟶ X` that is birational over `X`. Its open statement `resolution_of_singularities` is for integral schemes, separated and of finite type over a perfect field of characteristic `p > 0`.

formal-conjectures uses a different Lean toolchain, so this package cannot depend on it. This file copies the definition and writes the statements as propositions. The proofs that connect them to the statements of the project are in the package `base/`, because they use the equivalence of regular and smooth over a perfect field from resolutionorg/hironaka.

The statement of the project is stronger in one way: a resolution must be an isomorphism over the whole regular locus, and not only over some dense open set. So the bridge goes in one direction. A resolution in the sense of `IsResolution` of an integral variety over a perfect field gives a resolution in the sense of `HasResolution`.
-/

open CategoryTheory

universe u

namespace Singularity.Bridge

open AlgebraicGeometry

/-- The definition `Scheme.HasResolution` of formal-conjectures. A scheme `X` over `S` has a resolution if there is an integral scheme `Y`, smooth over `S`, with a proper morphism `Y ⟶ X` that is birational over `X`. -/
def HasResolution {S X : Scheme.{u}} (sX : X ⟶ S) : Prop :=
  ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
    IsIntegral Y ∧ IsProper f ∧ Smooth (f ≫ sX) ∧ Scheme.BirationalOver f (𝟙 X)

/-- The statement `resolution_of_singularities` of formal-conjectures, in dimension at most `n`. It is open for `n ≥ 4`. -/
def FCResolutionInDim (p n : ℕ) : Prop :=
  ∀ (k : Type u) [Field k] [PerfectField k] [CharP k p] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [LocallyOfFiniteType sX] [QuasiCompact sX] [IsSeparated sX],
    topologicalKrullDim X ≤ n → HasResolution sX

/-- The statement `resolution_of_singularities_of_charZero` of formal-conjectures: Hironaka's theorem. -/
def FCResolutionCharZero : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [LocallyOfFiniteType sX] [QuasiCompact sX] [IsSeparated sX],
    HasResolution sX

end Singularity.Bridge
