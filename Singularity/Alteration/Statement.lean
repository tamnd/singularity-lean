/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Alteration.Basic
import Singularity.Hypotheses.Integral
import Singularity.Statements.Embedded

/-!
# The theorem of de Jong

This file states the theorem of de Jong on regular alterations [dJ96, Theorem 4.1], Theorem 1.2.1 of Volume 8 of the handbook (node SG0000001K). The statement `deJongAlteration` is a definition of a proposition. This file does not prove it.

The file also states the weak form in a fixed dimension and characteristic, `RegularAlterationInDim p n`: each integral variety of dimension at most `n` over a field of characteristic `p` has a regular alteration. It proves two implications.

1. `regularAlterationInDim_of_deJongAlteration`: the theorem of de Jong implies the weak form in each dimension and characteristic. Take the empty closed set. The source of the alteration is open in a regular scheme, so it is regular.
2. `regularAlterationInDim_of_integralResolutionInDim`: resolution of integral varieties in dimension `n` implies the weak form in dimension `n`, because a resolution of an integral variety is a regular alteration (`Singularity.IsResolution.isAlteration`). The same holds with `ResolutionInDim` (`regularAlterationInDim_of_resolutionInDim`).

## The moduli of stable curves

Open question Q-08 of the project proposes a first form of the theorem with the moduli of stable curves as a named hypothesis. Volume 8, Chapter 4 proposes Hypothesis 2.2.5 (node SG0000004J): a smooth proper pointed curve over a dense open set extends to a stable pointed curve after a projective generically étale alteration of the base. A Lean form of this hypothesis needs the definitions of a semistable curve and of a stable pointed curve over a base scheme: a flat proper morphism whose geometric fibres are connected curves with at most ordinary double points, with sections in the smooth locus, and the stability condition on the components. Mathlib has no curves with ordinary double points and no projective morphisms. So this file does not state the hypothesis, and it does not prove the theorem from any hypothesis.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace Singularity

/-- Regular alterations in dimension at most `n` over fields of characteristic `p`: each integral variety `X` of dimension at most `n` over such a field has an alteration `φ : X' ⟶ X` with `X'` regular.

This is the first part of the theorem of de Jong (Corollary 1.2.2 of Volume 8, for an integral variety). The field `k` need not be perfect. -/
def RegularAlterationInDim (p n : ℕ) : Prop :=
  ∀ (k : Type u) [Field k] [CharP k p] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsVariety X f]
    [IsIntegral X], topologicalKrullDim X ≤ n →
      ∃ (X' : Scheme.{u}) (φ : X' ⟶ X), IsAlteration φ ∧ IsRegularScheme X'

/-- **The theorem of de Jong** [dJ96, Theorem 4.1], Theorem 1.2.1 of Volume 8, as a proposition. Let `X` be an integral variety over a field `k`, and let `Z` be a closed subset of `X` with `Z ≠ X`. Then there are an alteration `φ : X₁ ⟶ X`, an open immersion `j : X₁ ⟶ Xbar` over `k`, and an ideal sheaf `D` on `Xbar`, such that `Xbar` is an integral scheme that is proper over `k` and regular, the support of `D` is `j(φ⁻¹(Z)) ∪ (Xbar \ j(X₁))`, and `D` is a divisor with strict normal crossings in the sense of `Singularity.IsSncDivisor`.

The statement differs from [dJ96, Theorem 4.1] in two points, and in both points it is weaker.
* De Jong proves that `Xbar` is projective over `k`. Mathlib has no projective morphisms, so the statement asks that `Xbar` is proper over `k`.
* De Jong also proves that `φ` can be chosen generically étale if `k` is perfect. The statement leaves this part out.

The divisor `D` is reduced, because `IsSncDivisor` asks for a product of distinct members of a regular system of parameters, so `D` is the ideal of the closed set. This file does not prove the statement. -/
def deJongAlteration : Prop :=
  ∀ (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsVariety X f] [IsIntegral X]
    (Z : Set X), IsClosed Z → Z ≠ Set.univ →
      ∃ (X₁ Xbar : Scheme.{u}) (φ : X₁ ⟶ X) (j : X₁ ⟶ Xbar) (g : Xbar ⟶ Spec (.of k))
        (D : Xbar.IdealSheafData),
        IsAlteration φ ∧ IsOpenImmersion j ∧ j ≫ g = φ ≫ f ∧ IsIntegral Xbar ∧ IsProper g ∧
          IsRegularScheme Xbar ∧
          (D.support : Set Xbar) = j '' (φ ⁻¹' Z) ∪ (Set.range j)ᶜ ∧ IsSncDivisor D

/-- An open subscheme of a regular scheme is regular: if `j : X₁ ⟶ X` is an open immersion and `X` is regular, then `X₁` is regular. -/
theorem isRegularScheme_of_isOpenImmersion {X₁ X : Scheme.{u}} (j : X₁ ⟶ X) [IsOpenImmersion j]
    (hX : IsRegularScheme X) : IsRegularScheme X₁ := fun x => by
  have := hX (j x)
  exact IsRegularLocalRing.of_ringEquiv (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv

/-- The theorem of de Jong implies regular alterations in each dimension and each characteristic. -/
theorem regularAlterationInDim_of_deJongAlteration (h : deJongAlteration.{u}) (p n : ℕ) :
    RegularAlterationInDim.{u} p n := by
  intro k _ _ X f _ _ _
  obtain ⟨X₁, Xbar, φ, j, g, D, hφ, hj, -, -, -, hreg, -, -⟩ :=
    h k X f ∅ isClosed_empty Set.empty_ne_univ
  exact ⟨X₁, φ, hφ, isRegularScheme_of_isOpenImmersion j hreg⟩

/-- Resolution of integral varieties in dimension `n` implies regular alterations in dimension `n`: a resolution of an integral variety is a regular alteration. -/
theorem regularAlterationInDim_of_integralResolutionInDim {p n : ℕ}
    (h : IntegralResolutionInDim.{u} p n) : RegularAlterationInDim.{u} p n := by
  intro k _ _ X f _ _ hX
  obtain ⟨Y, π, hπ⟩ := h k X f hX
  exact ⟨Y, π, hπ.isAlteration, hπ.regular⟩

/-- Resolution in dimension `n` implies regular alterations in dimension `n`. -/
theorem regularAlterationInDim_of_resolutionInDim {p n : ℕ} (h : ResolutionInDim.{u} p n) :
    RegularAlterationInDim.{u} p n :=
  regularAlterationInDim_of_integralResolutionInDim (integralResolutionInDim_of_resolutionInDim h)

end Singularity
