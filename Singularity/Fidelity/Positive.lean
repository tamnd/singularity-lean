/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.Basic

/-!
# Fidelity check F2: positive instances

A correct statement must hold in the cases that are known. This file proves the first one: the identity of a regular scheme is a resolution. The other positive instances of spec 06.3 (curves, the cusp and the node, characteristic 0) come in later milestones.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace Singularity.Fidelity

/-- The identity of a regular scheme is a resolution of singularities. -/
theorem isResolution_id {X : Scheme.{u}} (hX : IsRegularScheme X) : IsResolution (𝟙 X) where
  regular := hX
  proper := inferInstance
  isIso_over := ⟨⊤, by simp [(regularLocus_eq_univ_iff X).mpr hX], inferInstance⟩
  dense := by simp [(regularLocus_eq_univ_iff X).mpr hX]

end Singularity.Fidelity
