/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.Main

/-!
# The reduction to integral varieties

A variety in the sense of `IsVariety` is reduced, but it need not be irreducible. The characteristic 0 base, resolutionorg/hironaka, resolves integral varieties only. This file states the integral case of `ResolutionInDim` and the reduction from the reduced case to the integral case.

The reduction is true, and the proof is known. Let `X_1, ..., X_r` be the irreducible components of `X`, with the reduced structure. Resolve each `X_i`, and let `Y` be the disjoint union of the resolutions. A regular point of `X` lies on one component only, because a regular local ring is a domain. Thus the map `Y ⟶ X` is an isomorphism over the regular locus of `X`. The proof in Lean is planned. Until then, each theorem that uses the reduction takes `ReductionToIntegral` as a hypothesis, and the map lists that hypothesis.
-/

open AlgebraicGeometry

universe u

namespace Singularity

/-- The integral case of `ResolutionInDim p n`: each integral variety of dimension at most `n` over a field of characteristic `p` has a resolution. -/
def IntegralResolutionInDim (p n : ℕ) : Prop :=
  ∀ (k : Type u) [Field k] [CharP k p] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsVariety X f]
    [IsIntegral X], topologicalKrullDim X ≤ n → ∃ (Y : Scheme.{u}) (π : Y ⟶ X), IsResolution π

/-- The reduction to integral varieties: for each `p` and `n`, the integral case of `ResolutionInDim p n` implies the full case. This is a named hypothesis. It is true, but its proof in Lean is planned. -/
def ReductionToIntegral : Prop :=
  ∀ p n : ℕ, IntegralResolutionInDim.{u} p n → ResolutionInDim.{u} p n

/-- The full case implies the integral case. -/
theorem integralResolutionInDim_of_resolutionInDim {p n : ℕ} (h : ResolutionInDim.{u} p n) :
    IntegralResolutionInDim.{u} p n :=
  fun k _ _ X f _ _ hX => h k X f hX

end Singularity
