/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.Main
import Singularity.Statements.Core
import Singularity.Statements.Embedded
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Inductions

/-!
# The challenge of the comparator

This file is the challenge of `lake comparator` (spec 14, row Q4). It states again, with `sorry`, the theorems of the package that prove a statement of `Singularity/Statements/`. It imports the statement files, and the Mathlib files that `Singularity/Valuation/Abhyankar.lean`, `Singularity/Valuation/ZariskiRiemann.lean` and `Singularity/Valuation/KeyPolynomials.lean` import. A statement that uses a definition of the package states this definition again, with the same name and the same body. The file `comparator.json` names these theorems, and the comparator checks that the theorems of the same names in `Singularity` have the same types, use only the permitted axioms, and are accepted by the kernel.

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

open AlgebraicGeometry CategoryTheory

/-- `Singularity/Fidelity/Embedded.lean`: the identity is an embedded resolution of the empty subscheme of a regular scheme. -/
theorem Fidelity.isEmbeddedResolution_id_top {Z : Scheme.{u}} (hZ : IsRegularScheme Z) :
    IsEmbeddedResolution (⊤ : Z.IdealSheafData) (𝟙 Z) ⊤ ⊤ := sorry

/-- `Singularity/Fidelity/Embedded.lean`: the zero ideal sheaf on a nonempty regular scheme is not a divisor with simple normal crossings. -/
theorem Fidelity.not_isSncDivisor_bot {Z : Scheme.{u}} (hZ : IsRegularScheme Z) (z : Z) :
    ¬ IsSncDivisor (⊥ : Z.IdealSheafData) := sorry

/-- `Singularity/Scheme/Embedded.lean`: a closed point is a permissible center (node SG0000000T). -/
theorem isPermissible_vanishingIdeal_singleton {Z : Scheme.{u}} {X : Z.IdealSheafData} {z : Z}
    (hz : IsClosed ({z} : Set Z)) (hzX : z ∈ X.support) :
    IsPermissible X (Scheme.IdealSheafData.vanishingIdeal ⟨{z}, hz⟩) := sorry

/-- `Singularity/Scheme/Embedded.lean`: a regular closed subscheme of codimension 1 in a regular scheme is a divisor with simple normal crossings (node SG0000000V). -/
theorem isSncDivisor_of_codim_one {Z : Scheme.{u}} (hZ : IsRegularScheme Z)
    {D : Z.IdealSheafData} (hD : IsRegularCodimOne D) : IsSncDivisor D := sorry

/-- `Singularity/Scheme/Embedded.lean`: the identity is an embedded resolution of a reduced regular closed subscheme of codimension 1. -/
theorem isEmbeddedResolution_id_of_codim_one {Z : Scheme.{u}} (hZ : IsRegularScheme Z)
    {X : Z.IdealSheafData} (hX : IsRegularCodimOne X) (hrad : X.radical = X) :
    IsEmbeddedResolution X (𝟙 Z) ⊤ ⊤ := sorry

section Abhyankar

open MvPolynomial Cardinal TensorProduct

/-- `Singularity/Valuation/Abhyankar.lean`: units with values that are independent over `ℤ`, together with elements of `A` with algebraically independent residues, are algebraically independent. -/
theorem algebraicIndependent_sumElim_of_valuationSubring {K : Type*} [Field K]
    (A : ValuationSubring K) {k : Type*} [CommRing k] [Algebra k K]
    [Algebra k A] [IsScalarTower k A K] {ι κ : Type*} (x : ι → Kˣ)
    (hx : LinearIndependent ℤ
      (fun i => Additive.ofMul (Units.map (A.valuation : K →* A.ValueGroup) (x i))))
    (y : κ → A) (hy : AlgebraicIndependent k (fun j => IsLocalRing.residue A (y j))) :
    AlgebraicIndependent k (Sum.elim (fun i => (x i : K)) (fun j => (y j : K))) := sorry

/-- `Singularity/Valuation/Abhyankar.lean`: the inequality of Abhyankar (node SG0000000Y). -/
theorem abhyankar_inequality {K : Type*} [Field K] (A : ValuationSubring K) {k : Type*} [Field k]
    [Algebra k K] [Algebra k A] [IsScalarTower k A K] :
    Module.rank ℚ (ℚ ⊗[ℤ] Additive A.ValueGroupˣ) +
        Algebra.trdeg k (IsLocalRing.ResidueField A) ≤ Algebra.trdeg k K := sorry

open IsLocalRing

/-- `Singularity/Valuation/Abhyankar.lean`: Theorem 2.1.4 of Volume 3 of the handbook, for an extension of valued fields. -/
theorem algebraicIndependent_sumElim_of_hasExtension {K L : Type*} [Field K] [Field L]
    [Algebra K L] {Γ₀ Γ₁ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ₁] (vK : Valuation K Γ₀) (vL : Valuation L Γ₁)
    [vK.HasExtension vL] {ι κ : Type*} (x : ι → Lˣ)
    (hx : LinearIndependent ℤ (fun i => Additive.ofMul
      (QuotientGroup.mk' (vL.comap (algebraMap K L) : K →*₀ Γ₁).valueGroup
        (Units.map (vL : L →* Γ₁) (x i)))))
    (y : κ → vL.valuationSubring)
    (hy : AlgebraicIndependent (ResidueField vK.valuationSubring) (fun j => residue _ (y j))) :
    AlgebraicIndependent K (Sum.elim (fun i => (x i : L)) (fun j => (y j : L))) := sorry

universe uL uΓ

/-- `Singularity/Valuation/Abhyankar.lean`: the relative inequality of Abhyankar for an extension of valued fields. -/
theorem abhyankar_inequality_relative {K : Type*} {L : Type uL} [Field K] [Field L]
    [Algebra K L] {Γ₀ : Type*} {Γ₁ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ₁] (vK : Valuation K Γ₀) (vL : Valuation L Γ₁)
    [vK.HasExtension vL] :
    lift.{uL} (Module.rank ℚ (ℚ ⊗[ℤ] Additive ((vL : L →*₀ Γ₁).valueGroup.map
        (QuotientGroup.mk' (vL.comap (algebraMap K L) : K →*₀ Γ₁).valueGroup)))) +
      lift.{uΓ} (Algebra.trdeg (ResidueField vK.valuationSubring)
        (ResidueField vL.valuationSubring)) ≤ lift.{uΓ} (Algebra.trdeg K L) := sorry

end Abhyankar

section ZariskiRiemann

universe v

open TopologicalSpace

/-- `Singularity/Valuation/ZariskiRiemann.lean`: the Zariski-Riemann space `ZR(K/A)`, the set of valuation subrings of `K` that contain the image of `A`. -/
def ZariskiRiemann (A : Type u) (K : Type v) [CommRing A] [Field K] [Algebra A K] : Type v :=
  {V : ValuationSubring K // ∀ a : A, algebraMap A K a ∈ V}

namespace ZariskiRiemann

variable {A : Type u} {K : Type v} [CommRing A] [Field K] [Algebra A K]

/-- `Singularity/Valuation/ZariskiRiemann.lean`: the valuation subring of a point of `ZR(K/A)`. -/
def toValuationSubring (V : ZariskiRiemann A K) : ValuationSubring K :=
  Subtype.val (p := fun V : ValuationSubring K => ∀ a : A, algebraMap A K a ∈ V) V

/-- `Singularity/Valuation/ZariskiRiemann.lean`: the basic open set `U(F)` for a finite set `F` of `K`. -/
def basicOpen (F : Finset K) : Set (ZariskiRiemann A K) :=
  {V | ∀ x ∈ F, x ∈ V.toValuationSubring}

/-- `Singularity/Valuation/ZariskiRiemann.lean`: the Zariski topology, generated by the sets `U(F)`. -/
instance instTopologicalSpace : TopologicalSpace (ZariskiRiemann A K) :=
  generateFrom (Set.range basicOpen)

/-- `Singularity/Valuation/ZariskiRiemann.lean`: the theorem of Zariski. The space `ZR(K/A)` is quasi-compact (node SG0000000X). -/
theorem compactSpace : CompactSpace (ZariskiRiemann A K) := sorry

end ZariskiRiemann

end ZariskiRiemann

section KeyPolynomials

open Polynomial

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

section Equiv

variable (μ : Valuation K[X] Γ₀)

/-- `Singularity/Valuation/KeyPolynomials.lean`: `f` and `g` are `μ`-equivalent, that is `μ (f - g) < μ f`. -/
def MuEquiv (f g : K[X]) : Prop :=
  μ (f - g) < μ f

/-- `Singularity/Valuation/KeyPolynomials.lean`: `φ` `μ`-divides `f`. -/
def MuDvd (φ f : K[X]) : Prop :=
  ∃ h : K[X], MuEquiv μ f (φ * h)

/-- `Singularity/Valuation/KeyPolynomials.lean`: `φ` is `μ`-irreducible. -/
def IsMuIrreducible (φ : K[X]) : Prop :=
  ¬ MuDvd μ φ 1 ∧ ∀ f g : K[X], MuDvd μ φ (f * g) → MuDvd μ φ f ∨ MuDvd μ φ g

/-- `Singularity/Valuation/KeyPolynomials.lean`: `φ` is `μ`-minimal. -/
def IsMuMinimal (φ : K[X]) : Prop :=
  ∀ f : K[X], f ≠ 0 → MuDvd μ φ f → φ.natDegree ≤ f.natDegree

/-- `Singularity/Valuation/KeyPolynomials.lean`: a key polynomial for `μ` (Definition 3.3.3 of Volume 3 of the handbook, node SG0000000Z). -/
structure KeyPolynomial (φ : K[X]) : Prop where
  monic : φ.Monic
  isMuIrreducible : IsMuIrreducible μ φ
  isMuMinimal : IsMuMinimal μ φ

variable {μ}

/-- `Singularity/Valuation/KeyPolynomials.lean`: a key polynomial has positive degree. -/
theorem KeyPolynomial.natDegree_pos {φ : K[X]} (hφ : KeyPolynomial μ φ) : 0 < φ.natDegree :=
  sorry

end Equiv

section Monomial

variable (v : Valuation K Γ₀) (γ : Γ₀)

/-- `Singularity/Valuation/KeyPolynomials.lean`: the monomial valuation `[v; X, γ]` as a function. -/
noncomputable def monomialValuationFun (f : K[X]) : Γ₀ :=
  f.support.sup fun i => v (f.coeff i) * γ ^ i

variable {v γ}

/-- `Singularity/Valuation/KeyPolynomials.lean`: Lemma 3.3.2, the monomial valuation is multiplicative. -/
theorem monomialValuationFun_mul (f g : K[X]) :
    monomialValuationFun v γ (f * g) =
      monomialValuationFun v γ f * monomialValuationFun v γ g := sorry

/-- `Singularity/Valuation/KeyPolynomials.lean`: `X` is a key polynomial for a valuation with the values of `[v; X, γ]`. -/
theorem keyPolynomial_X_of_forall_eq {μ : Valuation K[X] Γ₀}
    (hμ : ∀ f, μ f = monomialValuationFun v γ f) : KeyPolynomial μ X := sorry

end Monomial

section Expansion

variable (φ : K[X])

/-- `Singularity/Valuation/KeyPolynomials.lean`: the coefficient `aⱼ` of the `φ`-expansion of `f`. -/
noncomputable def expansionCoeff (f : K[X]) (j : ℕ) : K[X] :=
  ((fun g => g /ₘ φ)^[j] f) %ₘ φ

variable {φ}

/-- `Singularity/Valuation/KeyPolynomials.lean`: the `φ`-expansion `f = ∑ aⱼ φ ^ j`. -/
theorem eq_sum_expansionCoeff (hφ : φ.Monic) (hd : 0 < φ.natDegree) (f : K[X]) :
    f = ∑ j ∈ Finset.range (f.natDegree + 1), expansionCoeff φ f j * φ ^ j := sorry

end Expansion

section Augmented

variable (μ : Valuation K[X] Γ₀) (φ : K[X]) (γ : Γ₀)

/-- `Singularity/Valuation/KeyPolynomials.lean`: the augmented valuation `[μ; φ, γ]` as a function. -/
noncomputable def augmentedValuationFun (f : K[X]) : Γ₀ :=
  (Finset.range (f.natDegree + 1)).sup fun j => μ (expansionCoeff φ f j) * γ ^ j

variable {μ φ γ}

/-- `Singularity/Valuation/Augmentation.lean`: `φ` is `μ`-minimal if and only if `μ` is equal to the augmentation `[μ; φ, μ φ]`. -/
theorem isMuMinimal_iff (hφ : φ.Monic) (hd : 0 < φ.natDegree) :
    IsMuMinimal μ φ ↔ ∀ f, μ f = augmentedValuationFun μ φ (μ φ) f := sorry

/-- `Singularity/Valuation/Augmentation.lean`: for `γ ≤ μ φ`, the augmented value of `f` is at most `μ f`. This is `μ ≤ [μ; φ, γ]` in additive notation (Theorem 3.3.5 (2)). -/
theorem IsMuMinimal.augmentedValuationFun_le (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hmin : IsMuMinimal μ φ) (hγ : γ ≤ μ φ) (f : K[X]) :
    augmentedValuationFun μ φ γ f ≤ μ f := sorry

/-- `Singularity/Valuation/Augmentation.lean`: Theorem 3.3.5 (1) of MacLane-Vaquié, the augmented valuation is multiplicative. -/
theorem KeyPolynomial.augmentedValuationFun_mul (hφ : KeyPolynomial μ φ) (hγ : γ ≤ μ φ)
    (f g : K[X]) : augmentedValuationFun μ φ γ (f * g) =
      augmentedValuationFun μ φ γ f * augmentedValuationFun μ φ γ g := sorry

end Augmented

end KeyPolynomials

end Singularity
