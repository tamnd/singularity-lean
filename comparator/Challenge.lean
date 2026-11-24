/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.Main
import Singularity.Statements.Core

/-!
# The challenge of the comparator

This file is the challenge of `lake comparator` (spec 14, row Q4). It states again, with `sorry`, the theorems of the package that prove a statement of `Singularity/Statements/`. It imports the statement files only. The file `comparator.json` names these theorems, and the comparator checks that the theorems of the same names in `Singularity` have the same types, use only the permitted axioms, and are accepted by the kernel.

This file is not part of the library `Singularity`, and no module of the library imports it. Do not change a statement here without the same change in the proof.
-/

universe u

namespace Singularity

/-- `Singularity/Known/DimZero.lean`: resolution in dimension 0, in each characteristic. -/
theorem resolutionInDim_dim_zero (p : ℕ) : ResolutionInDim.{u} p 0 := sorry

/-- `Singularity/Curves/Resolution.lean`: resolution of curves, in each characteristic. -/
theorem Curves.resolutionInDim_one (p : ℕ) : ResolutionInDim.{u} p 1 := sorry

/-- `Singularity/Fidelity/Core.lean`: the core problem P1 is a special case of the main statement. -/
theorem purelyInseparableHypersurfaceResolution_of_resolutionInDim {p n : ℕ} (hp : p ≠ 0)
    (h : ResolutionInDim.{u} p n) : PurelyInseparableHypersurfaceResolution.{u} p n := sorry

/-- `Singularity/Fidelity/Core.lean`: the first open case implies P1 in dimension 4. -/
theorem purelyInseparableHypersurfaceResolution_four (h : ResolutionDimFourCharP.{u}) (p : ℕ)
    (hp : p.Prime) : PurelyInseparableHypersurfaceResolution.{u} p 4 := sorry

end Singularity
