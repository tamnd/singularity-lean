/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.Basic

/-!
# The main statements

This file states resolution of singularities in a given dimension and characteristic, the full problem and the first open case. The text is in spec 06.2 of the project.

These are definitions of propositions. This file proves none of them. The case of dimension at most 3 is known (Abhyankar for `p > 5`, Cossart and Piltant for all `p`). The case of dimension 4 and more in characteristic `p > 0` is open.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace Singularity

/-- Resolution of singularities holds for varieties of dimension at most `n` over fields of characteristic `p`: each such variety `X` has a resolution `π : Y ⟶ X`.

The field `k` is any field with `CharP k p`. It need not be perfect. -/
def ResolutionInDim (p n : ℕ) : Prop :=
  ∀ (k : Type u) [Field k] [CharP k p] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsVariety X f],
    topologicalKrullDim X ≤ n → ∃ (Y : Scheme.{u}) (π : Y ⟶ X), IsResolution π

/-- Resolution of singularities in each dimension and each characteristic. This is open. -/
def ResolutionOfSingularities : Prop :=
  ∀ p n : ℕ, (p = 0 ∨ p.Prime) → ResolutionInDim.{u} p n

/-- The first open case: resolution of singularities of varieties of dimension at most 4 over fields of prime characteristic. This is open. -/
def ResolutionDimFourCharP : Prop :=
  ∀ p : ℕ, p.Prime → ResolutionInDim.{u} p 4

end Singularity
