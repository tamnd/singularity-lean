/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.Main

/-!
# The challenge of the comparator for the base

This file is the challenge of `lake comparator` in the package `SingularityBase` (spec 14, row Q4). It states again, with `sorry`, the theorem of the base that proves a statement of `Singularity/Statements/`. It imports the statement files only. The file `base/comparator.json` names the theorem.

This file is not part of the library `SingularityBase`, and no module of the library imports it.
-/

universe u

namespace Singularity

/-- `base/SingularityBase/CharZero.lean`: resolution in characteristic 0, in each dimension. -/
theorem resolutionInDim_charZero (n : ℕ) : ResolutionInDim.{u} 0 n := sorry

end Singularity
