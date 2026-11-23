/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.Basic

/-!
# The core problem P1

The hypersurfaces `z ^ p + g(x_1, ..., x_n) = 0` in characteristic `p` are the first test of each method in characteristic `p` (spec 03.4). The cycles of Hauser and Perlega and the failure of the order of the coefficient ideal both occur in this family.

This file states resolution for the family. It proves nothing.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace Singularity

/-- The ring `k[x_1, ..., x_n, z] / (z ^ p + g)`. The variable `z` is `MvPolynomial.X none` and the variable `x_i` is `MvPolynomial.X (some i)`. -/
abbrev P1Ring (k : Type u) [Field k] (p n : ℕ) (g : MvPolynomial (Fin n) k) : Type u :=
  MvPolynomial (Option (Fin n)) k ⧸
    Ideal.span {(MvPolynomial.X none : MvPolynomial (Option (Fin n)) k) ^ p + MvPolynomial.rename some g}

/-- The affine hypersurface `z ^ p + g(x_1, ..., x_n) = 0` over `k`. -/
noncomputable abbrev P1Hypersurface (k : Type u) [Field k] (p n : ℕ) (g : MvPolynomial (Fin n) k) :
    Scheme.{u} :=
  Spec (.of (P1Ring k p n g))

/-- The core problem P1: each reduced hypersurface `z ^ p + g(x_1, ..., x_n) = 0` over a field of characteristic `p` has a resolution. For `n ≥ 4` this is open. -/
def PurelyInseparableHypersurfaceResolution (p n : ℕ) : Prop :=
  ∀ (k : Type u) [Field k] [CharP k p] (g : MvPolynomial (Fin n) k),
    IsReduced (P1Hypersurface k p n g) →
      ∃ (Y : Scheme.{u}) (π : Y ⟶ P1Hypersurface k p n g), IsResolution π

end Singularity
