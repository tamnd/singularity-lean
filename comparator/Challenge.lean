/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.Main
import Singularity.Statements.Core
import Singularity.Statements.Embedded
import Singularity.Statements.LocalUniformization
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
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Basic.Real.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.Expand
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Data.Finsupp.Interval

/-!
# The challenge of the comparator

This file is the challenge of `lake comparator` (spec 14, row Q4). It states again, with `sorry`, the theorems of the package that prove a statement of `Singularity/Statements/`. It imports the statement files, and the Mathlib files that `Singularity/Valuation/Abhyankar.lean`, `Singularity/Valuation/ZariskiRiemann.lean`, `Singularity/Valuation/KeyPolynomials.lean`, `Singularity/Invariant/CharacteristicPolyhedron.lean`, `Singularity/Invariant/Order.lean`, `Singularity/Invariant/Residual.lean`, `Singularity/Invariant/RigidLayer.lean`, `Singularity/Invariant/LogJacobian.lean`, `Singularity/Invariant/Newton.lean`, `Singularity/Invariant/FrobeniusNewton.lean` and `Singularity/Algebra/MvHasse.lean` import. A statement that uses a definition of the package states this definition again, with the same name and the same body. The file `comparator.json` names these theorems, and the comparator checks that the theorems of the same names in `Singularity` have the same types, use only the permitted axioms, and are accepted by the kernel.

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

section LocalUniformization

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- `Singularity/Fidelity/LocalUniformization.lean`: the trivial valuation of a function field has local uniformization. -/
theorem Fidelity.hasLocalUniformization_top (hK : IsFunctionField k K) :
    HasLocalUniformization k (⊤ : ValuationSubring K) := sorry

/-- `Singularity/Fidelity/LocalUniformization.lean`: a valuation subring with local uniformization over `k` contains `k`. -/
theorem Fidelity.algebraMap_mem_of_hasLocalUniformization {V : ValuationSubring K}
    (h : HasLocalUniformization k V) (a : k) : algebraMap k K a ∈ V := sorry

/-- `Singularity/Fidelity/LocalUniformization.lean`: a field with a valuation that has local uniformization over `k` is a function field over `k`. -/
theorem Fidelity.isFunctionField_of_hasLocalUniformization {V : ValuationSubring K}
    (h : HasLocalUniformization k V) : IsFunctionField k K := sorry

/-- `Singularity/Fidelity/LocalUniformization.lean`: local uniformization implies that the center is regular on one affine model. -/
theorem Fidelity.exists_regularCenter_of_hasLocalUniformization {V : ValuationSubring K}
    (h : HasLocalUniformization k V) :
    ∃ (A : Subalgebra k K) (hA : ∀ a : A, (a : K) ∈ V), IsAffineModel A ∧
      IsRegularLocalRing (Localization.AtPrime (valuationCenter V A hA)) := sorry

end LocalUniformization

section LocalUniformizationCurves

/-- `Singularity/Valuation/LocalUniformizationCurves.lean`: each valuation of a function field of transcendence degree at most 1 has local uniformization. -/
theorem hasLocalUniformization_of_trdeg_le_one {k K : Type u} [Field k] [Field K] [Algebra k K]
    (hK : IsFunctionField k K) (htr : Algebra.trdeg k K ≤ 1) (V : ValuationSubring K)
    [Algebra k V] [IsScalarTower k V K] : HasLocalUniformization k V := sorry

/-- `Singularity/Valuation/LocalUniformizationCurves.lean`: local uniformization in transcendence degree 0. -/
theorem localUniformizationInDim_zero (p : ℕ) : LocalUniformizationInDim.{u} p 0 := sorry

/-- `Singularity/Valuation/LocalUniformizationCurves.lean`: local uniformization in transcendence degree 1. -/
theorem localUniformizationInDim_one (p : ℕ) : LocalUniformizationInDim.{u} p 1 := sorry

end LocalUniformizationCurves

section LocalUniformizationDivisorial

open IsLocalRing

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- `Singularity/Valuation/LocalUniformizationDivisorial.lean`: a valuation ring that is essentially of finite type over `k` has local uniformization. -/
theorem hasLocalUniformization_of_essFiniteType (V : ValuationSubring K) [Algebra k V]
    [IsScalarTower k V K] [Algebra.EssFiniteType k V] : HasLocalUniformization k V := sorry

/-- `Singularity/Valuation/LocalUniformizationDivisorial.lean`: if `trdeg_k K ≤ trdeg_k κ_V + 1`, then `V` is essentially of finite type over `k`. -/
theorem essFiniteType_of_trdeg_le_trdeg_residueField_add_one (hK : IsFunctionField k K)
    (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K]
    (htr : Algebra.trdeg k K ≤ Algebra.trdeg k (ResidueField V) + 1) :
    Algebra.EssFiniteType k V := sorry

/-- `Singularity/Valuation/LocalUniformizationDivisorial.lean`: if `trdeg_k K ≤ trdeg_k κ_V + 1`, then `V` has local uniformization. -/
theorem hasLocalUniformization_of_trdeg_le_trdeg_residueField_add_one (hK : IsFunctionField k K)
    (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K]
    (htr : Algebra.trdeg k K ≤ Algebra.trdeg k (ResidueField V) + 1) :
    HasLocalUniformization k V := sorry

/-- `Singularity/Valuation/LocalUniformizationDivisorial.lean`: each divisorial valuation has local uniformization. -/
theorem hasLocalUniformization_of_divisorial (hK : IsFunctionField k K)
    (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K]
    (hdiv : Algebra.trdeg k (ResidueField V) + 1 = Algebra.trdeg k K) :
    HasLocalUniformization k V := sorry

end LocalUniformizationDivisorial

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

/-- `Singularity/Valuation/Augmentation.lean`: Theorem 3.3.5 (3) of MacLane-Vaquié, first claim. A key polynomial `φ` for `μ` is a key polynomial for each valuation with the values of the augmentation `[μ; φ, γ]`. -/
theorem KeyPolynomial.keyPolynomial_of_forall_eq (hφ : KeyPolynomial μ φ)
    {ν : Valuation K[X] Γ₀} (hν : ∀ f, ν f = augmentedValuationFun μ φ γ f) :
    KeyPolynomial ν φ := sorry

end Augmented

section MacLaneStep

/-- `Singularity/Valuation/MacLaneStep.lean`: under the hypotheses of the step of MacLane, `φ` `μ`-divides `f` if and only if `ν f < μ f`. -/
theorem muDvd_iff_map_lt {μ ν : Valuation K[X] Γ₀} {φ : K[X]} (hle : ∀ f, ν f ≤ μ f)
    (hφ : φ.Monic) (hlt : ν φ < μ φ) (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f)
    {f : K[X]} :
    MuDvd μ φ f ↔ ν f < μ f := sorry

/-- `Singularity/Valuation/MacLaneStep.lean`: the step of MacLane-Vaquié, part (a). A monic `φ` of least degree with `μ(φ) < ν(φ)` in additive notation is a key polynomial for `μ`. -/
theorem keyPolynomial_of_map_lt {μ ν : Valuation K[X] Γ₀} {φ : K[X]} (hle : ∀ f, ν f ≤ μ f)
    (hφ : φ.Monic) (hlt : ν φ < μ φ) (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f) :
    KeyPolynomial μ φ := sorry

/-- `Singularity/Valuation/MacLaneStep.lean`: the step of MacLane-Vaquié, part (b). The augmentation `[μ; φ, ν(φ)]` is at most `ν` in additive notation. -/
theorem map_le_augmentedValuationFun_of_map_eq {μ ν : Valuation K[X] Γ₀} {φ : K[X]}
    (hφ : φ.Monic) (hd : 0 < φ.natDegree) (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f)
    (f : K[X]) :
    ν f ≤ augmentedValuationFun μ φ (ν φ) f := sorry

/-- `Singularity/Valuation/MacLaneStep.lean`: a monic `φ` of least degree with `μ(φ) < ν(φ)` in additive notation exists if `μ ≠ ν`. -/
theorem exists_monic_map_lt {μ ν : Valuation K[X] Γ₀} (hC : ∀ c, ν (C c) = μ (C c))
    (hle : ∀ f, ν f ≤ μ f) (hne : μ ≠ ν) : ∃ φ : K[X], φ.Monic ∧ ν φ < μ φ ∧
      ∀ f : K[X], f.degree < φ.degree → ν f = μ f := sorry

/-- `Singularity/Valuation/MacLaneStep.lean`: the first step of the chain of MacLane, `[v; X, ν(X)] ≤ ν` in additive notation. -/
theorem map_le_monomialValuationFun {v : Valuation K Γ₀} {ν : Valuation K[X] Γ₀}
    (hν : ∀ a, ν (C a) = v a) (f : K[X]) : ν f ≤ monomialValuationFun v (ν X) f := sorry

end MacLaneStep

section MacLaneChain

/-- `Singularity/Valuation/MacLaneChain.lean`: under the hypotheses of the step of MacLane, the augmentation `[μ; φ, ν φ]` changes the value of `f` if and only if `ν f < μ f`. -/
theorem augmentedValuationFun_lt_iff_map_lt {μ ν : Valuation K[X] Γ₀} {φ : K[X]}
    (hle : ∀ f, ν f ≤ μ f) (hφ : φ.Monic)
    (hlt : ν φ < μ φ) (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f) (f : K[X]) :
    augmentedValuationFun μ φ (ν φ) f < μ f ↔ ν f < μ f := sorry

/-- `Singularity/Valuation/MacLaneChain.lean`: the next key polynomial of the chain of MacLane has degree at least the degree of `φ`. -/
theorem natDegree_le_of_map_lt_augmentedValuationFun {μ ν : Valuation K[X] Γ₀} {φ ψ : K[X]}
    (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f)
    (hlt : ν ψ < augmentedValuationFun μ φ (ν φ) ψ) : φ.natDegree ≤ ψ.natDegree := sorry

/-- `Singularity/Valuation/MacLaneChain.lean`: if the next key polynomial `ψ` of the chain of MacLane has the same degree as `φ`, then `ν(φ) < ν(ψ)` in additive notation. -/
theorem map_lt_map_of_natDegree_eq {μ ν : Valuation K[X] Γ₀} {φ ψ : K[X]}
    (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f) (hψ : ψ.Monic)
    (hdeg : ψ.natDegree = φ.natDegree) (hlt : ν ψ < augmentedValuationFun μ φ (ν φ) ψ) :
    ν ψ < ν φ := sorry

/-- `Singularity/Valuation/MacLaneChain.lean`: the limit principle of MacLane for a value group of `ν` that is discrete of rank 1. -/
theorem eventually_le_of_succ_lt {ν : Valuation K[X] Γ₀}
    (hdisc : ∀ c d : Γ₀, c ≠ 0 → (Set.Icc c d ∩ Set.range ν).Finite)
    {μ : ℕ → Valuation K[X] Γ₀} (hsucc : ∀ n f, μ (n + 1) f ≤ μ n f)
    (hlt : ∀ n f, ν f < μ n f → μ (n + 1) f < μ n f) (hr : ∀ n f, μ n f ∈ Set.range ν)
    (f : K[X]) {c : Γ₀} (hc : c ≠ 0) (hfc : ν f ≤ c) :
    ∃ N, ∀ n, N ≤ n → μ n f ≤ c := sorry

/-- `Singularity/Valuation/MacLaneChain.lean`: the limit principle of MacLane. The values `μₙ f` reach `ν f` if `ν f ≠ 0`. -/
theorem eventually_eq_of_succ_lt {ν : Valuation K[X] Γ₀}
    (hdisc : ∀ c d : Γ₀, c ≠ 0 → (Set.Icc c d ∩ Set.range ν).Finite)
    {μ : ℕ → Valuation K[X] Γ₀} (hle : ∀ n f, ν f ≤ μ n f) (hsucc : ∀ n f, μ (n + 1) f ≤ μ n f)
    (hlt : ∀ n f, ν f < μ n f → μ (n + 1) f < μ n f) (hr : ∀ n f, μ n f ∈ Set.range ν)
    (f : K[X]) (hf : ν f ≠ 0) :
    ∃ N, ∀ n, N ≤ n → μ n f = ν f := sorry

end MacLaneChain

section MacLaneUnique

/-- `Singularity/Valuation/MacLaneUnique.lean`: two monic polynomials of least degree with `μ(f) < ν(f)` in additive notation have the same degree. -/
theorem natDegree_eq_of_map_lt {μ ν : Valuation K[X] Γ₀} {φ ψ : K[X]} (hlt : ν φ < μ φ)
    (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f) (hψlt : ν ψ < μ ψ)
    (hψlow : ∀ f : K[X], f.degree < ψ.degree → ν f = μ f) : ψ.natDegree = φ.natDegree := sorry

/-- `Singularity/Valuation/MacLaneUnique.lean`: a monic `ψ` of the degree of `φ` has `μ(ψ) < ν(ψ)` in additive notation if and only if `ψ` is `μ`-equivalent to `φ`. -/
theorem muEquiv_iff_map_lt {μ ν : Valuation K[X] Γ₀} {φ ψ : K[X]} (hφ : φ.Monic)
    (hlt : ν φ < μ φ) (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f) (hψ : ψ.Monic)
    (hdeg : ψ.natDegree = φ.natDegree) : MuEquiv μ φ ψ ↔ ν ψ < μ ψ := sorry

/-- `Singularity/Valuation/MacLaneUnique.lean`: if `ν(ψ) ≤ ν(φ)` in additive notation, then `μ(ψ - φ) ≥ ν(ψ)`. -/
theorem map_sub_le_of_map_le {μ ν : Valuation K[X] Γ₀} {φ ψ : K[X]} (hφ : φ.Monic)
    (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f) (hψ : ψ.Monic)
    (hdeg : ψ.natDegree = φ.natDegree) (hν : ν φ ≤ ν ψ) : μ (ψ - φ) ≤ ν ψ := sorry

/-- `Singularity/Valuation/MacLaneUnique.lean`: key polynomials `φ` and `ψ` of the same degree with `μ(ψ - φ) ≥ γ` in additive notation give the same augmentation. -/
theorem KeyPolynomial.augmentedValuationFun_eq_of_map_sub_le {μ : Valuation K[X] Γ₀}
    {φ ψ : K[X]} {γ : Γ₀} (hφ : KeyPolynomial μ φ) (hψ : KeyPolynomial μ ψ)
    (hdeg : ψ.natDegree = φ.natDegree) (hγφ : γ ≤ μ φ) (hγψ : γ ≤ μ ψ) (h : μ (ψ - φ) ≤ γ)
    (f : K[X]) : augmentedValuationFun μ φ γ f = augmentedValuationFun μ ψ γ f := sorry

/-- `Singularity/Valuation/MacLaneUnique.lean`: if `μ(ψ) < ν(ψ) ≤ ν(φ)` in additive notation, then `[μ; ψ, ν(ψ)] ≤ [μ; φ, ν(φ)]`. -/
theorem augmentedValuationFun_le_of_map_le {μ ν : Valuation K[X] Γ₀} {φ ψ : K[X]}
    (hle : ∀ f, ν f ≤ μ f) (hφ : φ.Monic)
    (hlt : ν φ < μ φ) (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f) (hψ : ψ.Monic)
    (hdeg : ψ.natDegree = φ.natDegree) (hψlt : ν ψ < μ ψ) (hν : ν φ ≤ ν ψ) (f : K[X]) :
    augmentedValuationFun μ φ (ν φ) f ≤ augmentedValuationFun μ ψ (ν ψ) f := sorry

/-- `Singularity/Valuation/MacLaneUnique.lean`: Theorem 3.3.5 (3), the graded algebra in elementwise form. The terms of least value of the `φ`-expansion of `f` give the initial form of `f`. -/
theorem KeyPolynomial.augmentedValuationFun_sub_sum_filter_lt {μ : Valuation K[X] Γ₀}
    {φ : K[X]} {γ : Γ₀} (hφ : KeyPolynomial μ φ)
    (hγ : γ ≤ μ φ) {f : K[X]} (hf : augmentedValuationFun μ φ γ f ≠ 0) :
    augmentedValuationFun μ φ γ (f - ∑ j ∈ (Finset.range (f.natDegree + 1)).filter
        (fun j => μ (expansionCoeff φ f j) * γ ^ j = augmentedValuationFun μ φ γ f),
        expansionCoeff φ f j * φ ^ j) < augmentedValuationFun μ φ γ f := sorry

end MacLaneUnique

section LimitAugmentation

/-- `Singularity/Valuation/LimitAugmentation.lean`: a continuous family of augmented valuations `μᵢ = [μ; φᵢ, γᵢ]` of constant degree (Vaquié, [Vaq07]). -/
structure ContinuousFamily (μ : Valuation K[X] Γ₀) (ι : Type*) [LinearOrder ι] where
  /-- The key polynomial `φᵢ`. -/
  key : ι → K[X]
  /-- The value `γᵢ`. -/
  value : ι → Γ₀
  keyPolynomial : ∀ i, KeyPolynomial μ (key i)
  natDegree_eq : ∀ i j, (key i).natDegree = (key j).natDegree
  value_lt : ∀ i, value i < μ (key i)
  value_strictAnti : StrictAnti value
  map_sub_le : ∀ i j, i < j → μ (key j - key i) ≤ value i

namespace ContinuousFamily

variable {μ : Valuation K[X] Γ₀} {ι : Type*} [LinearOrder ι] (F : ContinuousFamily μ ι)

/-- `Singularity/Valuation/LimitAugmentation.lean`: the polynomial `f` is stable for the family if the value `μᵢ f` is constant for `i` large. -/
def IsStable (f : K[X]) : Prop :=
  ∃ i, ∀ j, i ≤ j → augmentedValuationFun μ (F.key j) (F.value j) f =
    augmentedValuationFun μ (F.key i) (F.value i) f

open Classical in
/-- `Singularity/Valuation/LimitAugmentation.lean`: the limit `μ_∞ f`, the eventual value of `μᵢ f` for a stable `f`, and `0` otherwise. -/
noncomputable def stableValue (f : K[X]) : Γ₀ :=
  if h : F.IsStable f then augmentedValuationFun μ (F.key h.choose) (F.value h.choose) f else 0

/-- `Singularity/Valuation/LimitAugmentation.lean`: a limit key polynomial, a monic polynomial of least degree among the polynomials that are not stable. -/
structure IsLimitKeyPolynomial (φ : K[X]) : Prop where
  monic : φ.Monic
  not_isStable : ¬ F.IsStable φ
  natDegree_le : ∀ f, ¬ F.IsStable f → φ.natDegree ≤ f.natDegree

/-- `Singularity/Valuation/LimitAugmentation.lean`: `φ` divides `f` in the limit. -/
def LimitDvd (φ f : K[X]) : Prop :=
  ∃ i, ∀ j, i ≤ j → ∃ h : K[X], augmentedValuationFun μ (F.key j) (F.value j) (f - φ * h) <
    augmentedValuationFun μ (F.key j) (F.value j) f

/-- `Singularity/Valuation/LimitAugmentation.lean`: the limit augmentation `[μ_∞; φ, γ]` as a function. -/
noncomputable def limitAugmentedValuationFun (φ : K[X]) (γ : Γ₀) (f : K[X]) : Γ₀ :=
  (Finset.range (f.natDegree + 1)).sup fun j => F.stableValue (expansionCoeff φ f j) * γ ^ j

section Stable

variable {F}

/-- `Singularity/Valuation/LimitAugmentation.lean`: if `μᵢ ≤ ν` for each `i` in additive notation and `ν` agrees with `μ` in degree less than `d`, then the limit value of a stable polynomial is its value for `ν`. -/
theorem stableValue_eq_of_isStable [NoMaxOrder ι] {ν : Valuation K[X] Γ₀}
    (hν : ∀ i f, ν f ≤ augmentedValuationFun μ (F.key i) (F.value i) f)
    (hlow : ∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = μ a) {f : K[X]}
    (hf : F.IsStable f) : F.stableValue f = ν f := sorry

/-- `Singularity/Valuation/LimitAugmentation.lean`: under the same hypotheses, some polynomial is not stable if and only if the family does not reach `ν`. -/
theorem exists_not_isStable_iff [NoMaxOrder ι] {ν : Valuation K[X] Γ₀}
    (hν : ∀ i f, ν f ≤ augmentedValuationFun μ (F.key i) (F.value i) f)
    (hlow : ∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = μ a) :
    (∃ f, ¬ F.IsStable f) ↔ ∃ f, ∀ i, augmentedValuationFun μ (F.key i) (F.value i) f ≠ ν f :=
  sorry

end Stable

section LimitKey

variable {F}

/-- `Singularity/Valuation/LimitAugmentation.lean`: if some polynomial is not stable, then a limit key polynomial exists. -/
theorem exists_isLimitKeyPolynomial [Nonempty ι] (h : ∃ f, ¬ F.IsStable f) :
    ∃ φ, F.IsLimitKeyPolynomial φ := sorry

namespace IsLimitKeyPolynomial

variable {φ : K[X]} (hφ : F.IsLimitKeyPolynomial φ)
include hφ

variable [Nonempty ι] [NoMaxOrder ι]

/-- `Singularity/Valuation/LimitAugmentation.lean`: a limit key polynomial divides `f` in the limit if and only if `f` is not stable. -/
theorem limitDvd_iff {f : K[X]} : F.LimitDvd φ f ↔ ¬ F.IsStable f := sorry

end IsLimitKeyPolynomial

end LimitKey

section Augmentation

variable {F} [Nonempty ι] {φ : K[X]} {γ : Γ₀}

namespace IsLimitKeyPolynomial

variable (hφ : F.IsLimitKeyPolynomial φ)
include hφ

/-- `Singularity/Valuation/LimitAugmentation.lean`: the limit augmentation satisfies the ultrametric inequality. -/
theorem limitAugmentedValuationFun_add_le_max (f g : K[X]) :
    F.limitAugmentedValuationFun φ γ (f + g) ≤
      max (F.limitAugmentedValuationFun φ γ f) (F.limitAugmentedValuationFun φ γ g) := sorry

variable [NoMaxOrder ι]

/-- `Singularity/Valuation/LimitAugmentation.lean`: the limit augmentation is multiplicative for `γ ≥ μᵢ(φ)` for each `i` in additive notation. -/
theorem limitAugmentedValuationFun_mul
    (hγ : ∀ i, γ ≤ augmentedValuationFun μ (F.key i) (F.value i) φ) (f g : K[X]) :
    F.limitAugmentedValuationFun φ γ (f * g) =
      F.limitAugmentedValuationFun φ γ f * F.limitAugmentedValuationFun φ γ g := sorry

end IsLimitKeyPolynomial

variable [NoMaxOrder ι]

namespace IsLimitKeyPolynomial

variable (hφ : F.IsLimitKeyPolynomial φ)
include hφ

/-- `Singularity/Valuation/LimitAugmentation.lean`: `μᵢ ≤ [μ_∞; φ, γ]` for each `i` in additive notation. -/
theorem limitAugmentedValuationFun_le
    (hγ : ∀ i, γ ≤ augmentedValuationFun μ (F.key i) (F.value i) φ) (i : ι) (f : K[X]) :
    F.limitAugmentedValuationFun φ γ f ≤ augmentedValuationFun μ (F.key i) (F.value i) f :=
  sorry

/-- `Singularity/Valuation/LimitAugmentation.lean`: `[μ_∞; φ, γ] ≤ ν` in additive notation for `γ ≤ ν(φ)`. -/
theorem map_le_limitAugmentedValuationFun {ν : Valuation K[X] Γ₀}
    (hν : ∀ i f, ν f ≤ augmentedValuationFun μ (F.key i) (F.value i) f)
    (hlow : ∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = μ a) (hγ : ν φ ≤ γ)
    (f : K[X]) : ν f ≤ F.limitAugmentedValuationFun φ γ f := sorry

end IsLimitKeyPolynomial

end Augmentation

end ContinuousFamily

end LimitAugmentation

end KeyPolynomials

section CharacteristicPolyhedron

open Polynomial Pointwise

/-- `Singularity/Invariant/Newton.lean`: an exponent vector as a point of `σ → ℝ`. -/
noncomputable def expToReal {σ : Type*} : (σ →₀ ℕ) →+ (σ → ℝ) where
  toFun d i := d i
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

/-- `Singularity/Invariant/Newton.lean`: the positive orthant of `σ → ℝ`. -/
def orthant (σ : Type*) : Set (σ → ℝ) := {v | ∀ i, 0 ≤ v i}

/-- `Singularity/Invariant/CharacteristicPolyhedron.lean`: the translation formula for a polynomial in `z`. -/
theorem coeff_taylor_eq_sum {A : Type*} [CommSemiring A] (f : A[X]) (h : A) (d : ℕ) :
    (taylor h f).coeff d =
      ∑ e ∈ Finset.range (f.natDegree + 1), (e.choose d : A) * f.coeff e * h ^ (e - d) := sorry

variable {σ k : Type*}

section Semiring

variable [CommSemiring k]

/-- `Singularity/Invariant/CharacteristicPolyhedron.lean`: the points `α / i` of `f`. -/
def projPoints (f : (MvPowerSeries σ k)[X]) : Set (σ → ℝ) :=
  {u | ∃ i : ℕ, 1 ≤ i ∧ i ≤ f.natDegree ∧ ∃ α : σ →₀ ℕ,
    MvPowerSeries.coeff α (f.coeff (f.natDegree - i)) ≠ 0 ∧ u = (i : ℝ)⁻¹ • expToReal α}

/-- `Singularity/Invariant/CharacteristicPolyhedron.lean`: the projected Newton polyhedron `Δ(f; x; z)`. -/
noncomputable def projPolyhedron (f : (MvPowerSeries σ k)[X]) : Set (σ → ℝ) :=
  convexHull ℝ (projPoints f) + orthant σ

/-- `Singularity/Invariant/CharacteristicPolyhedron.lean`: the initial polynomial of `f` at `v`. -/
noncomputable def vertexPoly (f : (MvPowerSeries σ k)[X]) (v : σ →₀ ℕ) : k[X] :=
  ∑ d ∈ Finset.range (f.natDegree + 1),
    Polynomial.monomial d (MvPowerSeries.coeff ((f.natDegree - d) • v) (f.coeff d))

/-- `Singularity/Invariant/CharacteristicPolyhedron.lean`: the characteristic polyhedron `Δ(f; x)`. -/
noncomputable def charPolyhedron (f : (MvPowerSeries σ k)[X]) : Set (σ → ℝ) :=
  ⋂ φ : MvPowerSeries σ k, ⋂ (_ : MvPowerSeries.constantCoeff φ = 0),
    projPolyhedron (taylor φ f)

/-- `Singularity/Invariant/CharacteristicPolyhedron.lean`: the translation `z ↦ z + c x^β` moves `Δ(f; x; z)` into the convex hull of `Δ(f; x; z)` and `β + ℝ_{≥0}^σ`. -/
theorem projPolyhedron_taylor_monomial_subset (f : (MvPowerSeries σ k)[X]) (β : σ →₀ ℕ) (c : k) :
    projPolyhedron (taylor (MvPowerSeries.monomial β c) f) ⊆
      convexHull ℝ (projPolyhedron f ∪ ({expToReal β} + orthant σ)) := sorry

/-- `Singularity/Invariant/CharacteristicPolyhedron.lean`: the initial polynomial at `v` of `f(z + c x^v)` is the shift by `c` of the initial polynomial of `f` at `v`. -/
theorem vertexPoly_taylor_monomial (f : (MvPowerSeries σ k)[X]) (v : σ →₀ ℕ) (c : k) :
    vertexPoly (taylor (MvPowerSeries.monomial v c) f) v = taylor c (vertexPoly f v) := sorry

end Semiring

section Ring

variable [CommRing k]

/-- `Singularity/Invariant/CharacteristicPolyhedron.lean`: the vertex `v` is solvable with the constant `c`. -/
def IsSolvableVertex (f : (MvPowerSeries σ k)[X]) (v : σ →₀ ℕ) (c : k) : Prop :=
  vertexPoly f v = (X + C c) ^ f.natDegree

/-- `Singularity/Invariant/CharacteristicPolyhedron.lean`: the translation `z ↦ z - c x^v` at a solvable vertex `v` makes `Δ(f; x; z)` smaller. -/
theorem projPolyhedron_taylor_ssubset_of_isSolvable {f : (MvPowerSeries σ k)[X]} {v : σ →₀ ℕ}
    {c : k} (hv : expToReal v ∈ (projPolyhedron f).extremePoints ℝ)
    (hs : IsSolvableVertex f v c) :
    projPolyhedron (taylor (MvPowerSeries.monomial v (-c)) f) ⊂ projPolyhedron f := sorry

/-- `Singularity/Invariant/CharacteristicPolyhedron.lean`: one direction of the vertex criterion of Hironaka. -/
theorem not_isSolvableVertex_of_charPolyhedron_eq {f : (MvPowerSeries σ k)[X]} {v : σ →₀ ℕ}
    (h : charPolyhedron f = projPolyhedron f) (hv0 : v ≠ 0)
    (hv : expToReal v ∈ (projPolyhedron f).extremePoints ℝ) (c : k) :
    ¬ IsSolvableVertex f v c := sorry

end Ring

end CharacteristicPolyhedron

section Moh

open MvPolynomial Finsupp

section Defs

variable {σ R : Type*} [CommSemiring R]

/-- `Singularity/Invariant/Order.lean`: the order of a polynomial at the origin. -/
noncomputable def ord (f : MvPolynomial σ R) : ℕ∞ :=
  (f : MvPowerSeries σ R).order

/-- `Singularity/Invariant/Residual.lean`: no exponent of `F` lies in `q ℕ^σ`. -/
def IsClean (q : ℕ) (F : MvPolynomial σ R) : Prop :=
  ∀ d ∈ F.support, ¬ ∀ i, q ∣ d i

open Classical in
/-- `Singularity/Invariant/Residual.lean`: the clean part of `F` for `q`. -/
noncomputable def cleanPart (q : ℕ) (F : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ d ∈ F.support.filter (fun d => ¬ ∀ i, q ∣ d i), monomial d (F.coeff d)

open Classical in
/-- `Singularity/Invariant/Residual.lean`: the exponents of the monomial factor along `Δ`. -/
noncomputable def divisorExponent (Δ : Finset σ) (F : MvPolynomial σ R) : σ →₀ ℕ :=
  ∑ i ∈ Δ, Finsupp.single i (sInf ((fun d : σ →₀ ℕ => d i) '' (F.support : Set (σ →₀ ℕ))))

/-- `Singularity/Invariant/Residual.lean`: the residual factor of `F` along `Δ`. -/
noncomputable def residualFactor (Δ : Finset σ) (F : MvPolynomial σ R) : MvPolynomial σ R :=
  divMonomial F (divisorExponent Δ F)

/-- `Singularity/Invariant/Residual.lean`: the residual order of `z^q + F` along `Δ`. -/
noncomputable def residualOrderAlong (Δ : Finset σ) (q : ℕ) (F : MvPolynomial σ R) : ℕ∞ :=
  ord (residualFactor Δ (cleanPart q F))

variable [DecidableEq σ]

/-- `Singularity/Invariant/Residual.lean`: the `x_j`-chart of the point blowup with translations `t`. -/
noncomputable def pointChart (j : σ) (t : σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i => if i = j then X j else X j * (X i + C (t i))

/-- `Singularity/Invariant/Residual.lean`: the transform of the divisor under the chart. -/
noncomputable def blowupDivisor [DecidableEq R] (Δ : Finset σ) (j : σ) (t : σ → R) : Finset σ :=
  insert j (Δ.filter fun i => i ≠ j ∧ t i = 0)

end Defs

/-- `Singularity/Invariant/Residual.lean`: the statement of Moh's bound for one blowup. -/
def moh_bound : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [DecidableEq k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (e n : ℕ) (Δ : Finset (Fin n)) (j : Fin n) (t : Fin n → k) (F F' : MvPolynomial (Fin n) k),
    1 ≤ e → IsClean (p ^ e) F → ((p ^ e : ℕ) : ℕ∞) ≤ ord F →
    pointChart j t F = X j ^ p ^ e * F' → ((p ^ e : ℕ) : ℕ∞) ≤ ord F' →
    residualOrderAlong (blowupDivisor Δ j t) (p ^ e) F' ≤
      residualOrderAlong Δ (p ^ e) F + ((p ^ (e - 1) : ℕ) : ℕ∞)

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- `Singularity/Invariant/MohBound.lean`: Moh's bound, the residual order goes up by at most `p^(e-1)`. -/
theorem residualOrderAlong_pointChart_le (Δ : Finset σ) (j : σ) (t : σ → k) {e : ℕ}
    {F F' : MvPolynomial σ k} (hF : IsClean (p ^ e) F) (hord : ((p ^ e : ℕ) : ℕ∞) ≤ ord F)
    (hπ : pointChart j t F = X j ^ p ^ e * F') :
    residualOrderAlong (blowupDivisor Δ j t) (p ^ e) F' ≤
      residualOrderAlong Δ (p ^ e) F + ((p ^ (e - 1) : ℕ) : ℕ∞) := sorry

/-- `Singularity/Invariant/MohBound.lean`: if `q ∤ ord F`, the residual order does not go up. -/
theorem residualOrderAlong_pointChart_le_of_not_dvd (Δ : Finset σ) (j : σ) (t : σ → k) {e m : ℕ}
    {F F' : MvPolynomial σ k} (hF : IsClean (p ^ e) F) (hord : ((p ^ e : ℕ) : ℕ∞) ≤ ord F)
    (hm : ord F = m) (hdvd : ¬ p ^ e ∣ m) (hπ : pointChart j t F = X j ^ p ^ e * F') :
    residualOrderAlong (blowupDivisor Δ j t) (p ^ e) F' ≤ residualOrderAlong Δ (p ^ e) F := sorry

/-- `Singularity/Invariant/MohBound.lean`: the proposition `moh_bound` holds. -/
theorem moh_bound_holds : moh_bound := sorry

end Moh

section CharacteristicPolyhedronClean

open Polynomial Pointwise

variable {σ k : Type*}

/-- `Singularity/Invariant/Newton.lean`: the Newton polyhedron of a polynomial. -/
noncomputable def newtonPolyhedron {R : Type*} [CommSemiring R] (f : MvPolynomial σ R) :
    Set (σ → ℝ) :=
  convexHull ℝ (expToReal '' (f.support : Set (σ →₀ ℕ))) + orthant σ

/-- `Singularity/Invariant/CharacteristicPolyhedronClean.lean`: for a polynomial `F`, `Δ(z^n + F; x; z) = (1/n) N(F)`. -/
theorem projPolyhedron_X_pow_add_C_coe [CommSemiring k] [Nontrivial k] {n : ℕ} (hn : 1 ≤ n)
    (F : MvPolynomial σ k) :
    projPolyhedron (X ^ n + C (F : MvPowerSeries σ k)) = (n : ℝ)⁻¹ • newtonPolyhedron F := sorry

variable [CommRing k] (p : ℕ) [ExpChar k p]

/-- `Singularity/Invariant/CharacteristicPolyhedronClean.lean`: every exponent of `φ^(p^e)` lies in `p^e ℕ^σ`. -/
theorem coeff_pow_expChar_pow_eq_zero (e : ℕ) (φ : MvPowerSeries σ k) {d : σ →₀ ℕ}
    (hd : ¬ ∀ i, p ^ e ∣ d i) : MvPowerSeries.coeff d (φ ^ p ^ e) = 0 := sorry

/-- `Singularity/Invariant/CharacteristicPolyhedronClean.lean`: `(z + φ)^q + F = z^q + (φ^q + F)` for `q = p^e`. -/
theorem taylor_X_pow_add_C (e : ℕ) (φ F : MvPowerSeries σ k) :
    taylor φ (X ^ p ^ e + C F) = X ^ p ^ e + C (φ ^ p ^ e + F) := sorry

variable [Nontrivial k]

/-- `Singularity/Invariant/CharacteristicPolyhedronClean.lean`: for clean `F`, the coordinate `z` attains the characteristic polyhedron of `z^q + F`. -/
theorem charPolyhedron_X_pow_add_C_of_clean (e : ℕ) {F : MvPowerSeries σ k}
    (hF : ∀ α, MvPowerSeries.coeff α F ≠ 0 → ¬ ∀ i, p ^ e ∣ α i) :
    charPolyhedron (X ^ p ^ e + C F) = projPolyhedron (X ^ p ^ e + C F) := sorry

/-- `Singularity/Invariant/CharacteristicPolyhedronClean.lean`: for a clean polynomial `F`, the characteristic polyhedron of `z^q + F` is `(1/q) N(F)`. -/
theorem charPolyhedron_X_pow_add_C_eq_smul_newtonPolyhedron (e : ℕ) {F : MvPolynomial σ k}
    (hF : IsClean (p ^ e) F) :
    charPolyhedron (X ^ p ^ e + C (F : MvPowerSeries σ k)) =
      ((p ^ e : ℕ) : ℝ)⁻¹ • newtonPolyhedron F := sorry

/-- `Singularity/Invariant/CharacteristicPolyhedronClean.lean`: for clean `F`, no vertex `v ≠ 0` of `Δ(z^q + F; x; z)` is solvable. -/
theorem not_isSolvableVertex_of_clean (e : ℕ) {F : MvPowerSeries σ k}
    (hF : ∀ α, MvPowerSeries.coeff α F ≠ 0 → ¬ ∀ i, p ^ e ∣ α i) {v : σ →₀ ℕ} (hv0 : v ≠ 0)
    (hv : expToReal v ∈ (projPolyhedron (X ^ p ^ e + C F)).extremePoints ℝ) (c : k) :
    ¬ IsSolvableVertex (X ^ p ^ e + C F) v c := sorry

end CharacteristicPolyhedronClean

section RigidLayer

open Polynomial

section Semiring

variable {R : Type*} [CommSemiring R]

/-- `Singularity/Invariant/RigidLayer.lean`: the Frobenius form of the translation. -/
theorem X_add_C_pow_pow_mul (p : ℕ) [ExpChar R p] (c : R) (e m₀ : ℕ) :
    (X + C c) ^ (p ^ e * m₀) = (X ^ p ^ e + C (c ^ p ^ e)) ^ m₀ := sorry

/-- `Singularity/Invariant/RigidLayer.lean`: `binom(p^e m_0, n) = 0` if `p^e` does not divide `n`. -/
theorem cast_choose_pow_mul_eq_zero (p : ℕ) [ExpChar R p] {e m₀ n : ℕ} (hn : ¬ p ^ e ∣ n) :
    (((p ^ e * m₀).choose n : ℕ) : R) = 0 := sorry

/-- `Singularity/Invariant/RigidLayer.lean`: the translation formula for the coefficients. -/
theorem coeff_taylor_natDegree_sub (f : R[X]) (c : R) {i : ℕ} (hi : i ≤ f.natDegree) :
    (taylor c f).coeff (f.natDegree - i) =
      ∑ j ∈ Finset.range (i + 1),
        ((f.natDegree - j).choose (i - j) : R) * f.coeff (f.natDegree - j) * c ^ (i - j) := sorry

/-- `Singularity/Invariant/RigidLayer.lean`: the inseparable layer is rigid. -/
theorem coeff_taylor_sub_of_lt_pow (p : ℕ) [ExpChar R p] {f : R[X]} {e m₀ m : ℕ}
    (hm : m = p ^ e * m₀) (hf : f.natDegree = m) (c : R) {i : ℕ} (hi₀ : 0 < i) (hi : i < p ^ e) :
    (taylor c f).coeff (m - i) = f.coeff (m - i) +
      ∑ j ∈ Finset.Ioo 0 i, ((m - j).choose (i - j) : R) * f.coeff (m - j) * c ^ (i - j) := sorry

/-- `Singularity/Invariant/RigidLayer.lean`: if `a_1 = ... = a_(i-1) = 0`, then `a'_i = a_i`. -/
theorem coeff_taylor_sub_of_lt_pow_of_eq_zero (p : ℕ) [ExpChar R p] {f : R[X]} {e m₀ m : ℕ}
    (hm : m = p ^ e * m₀) (hf : f.natDegree = m) (c : R) {i : ℕ} (hi₀ : 0 < i) (hi : i < p ^ e)
    (h : ∀ j, 0 < j → j < i → f.coeff (m - j) = 0) :
    (taylor c f).coeff (m - i) = f.coeff (m - i) := sorry

/-- `Singularity/Invariant/RigidLayer.lean`: if `p` divides the degree, then `a'_1 = a_1`. -/
theorem coeff_taylor_natDegree_sub_one (p : ℕ) [ExpChar R p] [Fact p.Prime] {f : R[X]}
    (hdvd : p ∣ f.natDegree) (c : R) :
    (taylor c f).coeff (f.natDegree - 1) = f.coeff (f.natDegree - 1) := sorry

/-- `Singularity/Invariant/RigidLayer.lean`: the step of Lucas and Tschirnhausen. -/
theorem coeff_taylor_sub_pow (p : ℕ) [ExpChar R p] {f : R[X]} (hmonic : f.Monic) {e m₀ m : ℕ}
    (hm : m = p ^ e * m₀) (hf : f.natDegree = m) (c : R) :
    (taylor c f).coeff (m - p ^ e) = f.coeff (m - p ^ e) + m₀ * c ^ p ^ e +
      ∑ j ∈ Finset.Ioo 0 (p ^ e),
        ((m - j).choose (p ^ e - j) : R) * f.coeff (m - j) * c ^ (p ^ e - j) := sorry

/-- `Singularity/Invariant/RigidLayer.lean`: if `a_1 = ... = a_(p^e - 1) = 0`, then `a'_(p^e) = a_(p^e) + m_0 c^(p^e)`. -/
theorem coeff_taylor_sub_pow_of_eq_zero (p : ℕ) [ExpChar R p] {f : R[X]} (hmonic : f.Monic)
    {e m₀ m : ℕ} (hm : m = p ^ e * m₀) (hf : f.natDegree = m) (c : R)
    (h : ∀ j, 0 < j → j < p ^ e → f.coeff (m - j) = 0) :
    (taylor c f).coeff (m - p ^ e) = f.coeff (m - p ^ e) + m₀ * c ^ p ^ e := sorry

end Semiring

/-- `Singularity/Invariant/RigidLayer.lean`: the lifting test. -/
theorem X_pow_add_C_mem_pow_iff {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p] (I : Ideal R)
    (g h : R) (e : ℕ) :
    X ^ p ^ e + C g ∈ (Ideal.span {X - C h} ⊔ I.map (C : R →+* R[X])) ^ p ^ e ↔
      g + h ^ p ^ e ∈ I ^ p ^ e := sorry

end RigidLayer

section LogJacobian

open MvPolynomial Finsupp

section Defs

variable {σ k : Type*} [CommSemiring k]

/-- `Singularity/Invariant/Order.lean`: the order of an ideal at the origin. -/
noncomputable def idealOrd (I : Ideal (MvPolynomial σ k)) : ℕ∞ :=
  sInf (ord '' (I : Set (MvPolynomial σ k)))

/-- `Singularity/Invariant/LogJacobian.lean`: the log-Jacobian ideal `Θ(g)` along `Δ`. -/
noncomputable def logJacobian (Δ : Finset σ) (g : MvPolynomial σ k) : Ideal (MvPolynomial σ k) :=
  Ideal.span ((fun i => X i * pderiv i g) '' (Δ : Set σ) ∪ (fun j => pderiv j g) '' (Δ : Set σ)ᶜ)

/-- `Singularity/Invariant/LogJacobian.lean`: the residual log-Jacobian ideal `Θ̃(G)`. -/
noncomputable def residualLogJacobian (Δ : Finset σ) (r : σ →₀ ℕ) (G : MvPolynomial σ k) :
    Ideal (MvPolynomial σ k) :=
  Ideal.span ((fun i => (r i : k) • G + X i * pderiv i G) '' (Δ : Set σ) ∪
    (fun j => pderiv j G) '' (Δ : Set σ)ᶜ)

/-- `Singularity/Invariant/LogJacobian.lean`: the order `ρ` of `Θ̃(G)` for `g = x^r G`. -/
noncomputable def logJacobianOrder (Δ : Finset σ) (g : MvPolynomial σ k) : ℕ∞ :=
  idealOrd (residualLogJacobian Δ (divisorExponent Δ g) (residualFactor Δ g))

end Defs

/-- `Singularity/Invariant/LogJacobian.lean`: `Θ(g + h^p) = Θ(g)`. -/
theorem logJacobian_add_pow {σ k : Type*} [CommSemiring k] (p : ℕ) [CharP k p] (Δ : Finset σ)
    (g h : MvPolynomial σ k) : logJacobian Δ (g + h ^ p) = logJacobian Δ g := sorry

/-- `Singularity/Invariant/LogJacobian.lean`: `Θ(x^r G) = (x^r) Θ̃(G)`. -/
theorem logJacobian_monomial_mul {σ k : Type*} [CommSemiring k] {Δ : Finset σ} {r : σ →₀ ℕ}
    (hr : ∀ i, i ∉ Δ → r i = 0) (G : MvPolynomial σ k) :
    logJacobian Δ (monomial r 1 * G) = Ideal.span {monomial r 1} * residualLogJacobian Δ r G :=
  sorry

variable {σ k : Type*} [Field k] (p : ℕ) [CharP k p] {Δ : Finset σ} {g : MvPolynomial σ k}

/-- `Singularity/Invariant/LogJacobian.lean`: `Θ̃(G)` is not contained in `(x_i)` for `i ∈ Δ`. -/
theorem residualLogJacobian_not_le_span_X (hg : g ≠ 0) (hc : IsClean p g) {i : σ} (hi : i ∈ Δ) :
    ¬ residualLogJacobian Δ (divisorExponent Δ g) (residualFactor Δ g) ≤ Ideal.span {X i} := sorry

/-- `Singularity/Invariant/LogJacobian.lean`: the monomial factor of `Θ(g)` is `x^r`. -/
theorem le_divisorExponent_of_logJacobian_le (hg : g ≠ 0) (hc : IsClean p g) {s : σ →₀ ℕ}
    (hs : ∀ i, i ∉ Δ → s i = 0) (h : logJacobian Δ g ≤ Ideal.span {monomial s 1}) :
    s ≤ divisorExponent Δ g := sorry

/-- `Singularity/Invariant/LogJacobian.lean`: `ρ ≤ d`. -/
theorem logJacobianOrder_le_residualOrderAlong (hc : IsClean p g) :
    logJacobianOrder Δ g ≤ residualOrderAlong Δ p g := sorry

/-- `Singularity/Invariant/LogJacobian.lean`: `d ≤ ρ + 1`. -/
theorem residualOrderAlong_le_logJacobianOrder_add_one (hc : IsClean p g) :
    residualOrderAlong Δ p g ≤ logJacobianOrder Δ g + 1 := sorry

/-- `Singularity/Invariant/LogJacobian.lean`: the dichotomy `ρ ∈ {d - 1, d}`. -/
theorem logJacobianOrder_eq_or (hc : IsClean p g) :
    logJacobianOrder Δ g = residualOrderAlong Δ p g ∨
      logJacobianOrder Δ g + 1 = residualOrderAlong Δ p g := sorry

/-- `Singularity/Invariant/LogJacobian.lean`: `ρ + 1 = d` if and only if `∂_j in(G) ≠ 0` for some
`j ∉ Δ`. -/
theorem logJacobianOrder_add_one_eq_iff (hc : IsClean p g) {d : ℕ}
    (hd : ord (residualFactor Δ g) = d) :
    logJacobianOrder Δ g + 1 = d ↔
      ∃ j ∉ Δ, pderiv j (homogeneousComponent d (residualFactor Δ g)) ≠ 0 := sorry

end LogJacobian

section FrobeniusNewton

open MvPolynomial Finsupp

section Defs

variable {σ R : Type*} [CommSemiring R]

/-- `Singularity/Invariant/Residual.lean`: the polynomial `z^q + F` in `k[z, x]`. -/
noncomputable def purelyInseparable (q : ℕ) (F : MvPolynomial σ R) : MvPolynomial (Option σ) R :=
  X none ^ q + rename Option.some F

/-- `Singularity/Invariant/Newton.lean`: the order of `f` for the weight vector `w`. -/
noncomputable def weightedOrd (w : σ → ℕ) (f : MvPolynomial σ R) : ℕ∞ :=
  (f : MvPowerSeries σ R).weightedOrder w

/-- `Singularity/Invariant/Newton.lean`: the initial form of `f` for `w`. -/
noncomputable def initialForm (w : σ → ℕ) (f : MvPolynomial σ R) : MvPolynomial σ R :=
  weightedHomogeneousComponent w (weightedOrd w f).toNat f

/-- `Singularity/Invariant/FrobeniusNewton.lean`: each partial derivative of `h` vanishes at `v`. -/
def IsCriticalPoint (h : MvPolynomial σ R) (v : σ → R) : Prop :=
  ∀ i, eval v (pderiv i h) = 0

/-- `Singularity/Invariant/FrobeniusNewton.lean`: `h` and each partial derivative of `h` vanish at `v`. -/
def IsSingularPoint (h : MvPolynomial σ R) (v : σ → R) : Prop :=
  eval v h = 0 ∧ IsCriticalPoint h v

/-- `Singularity/Invariant/FrobeniusNewton.lean`: no `w : σ → ZMod p` has `∑ w_i a_i = 1` for each `a ∈ S`. -/
def IsResonant (p : ℕ) (S : Finset (σ →₀ ℕ)) : Prop :=
  ¬ ∃ w : σ → ZMod p, ∀ a ∈ S, ∑ i ∈ a.support, w i * (a i : ZMod p) = 1

end Defs

/-- `Singularity/Invariant/FrobeniusNewton.lean`: `(z, v)` is a singular point of `z^p + h` if and only if `z^p + h(v) = 0` and `v` is a critical point of `h`. -/
theorem isSingularPoint_purelyInseparable_iff {σ k : Type*} [CommSemiring k] (p : ℕ) [CharP k p]
    (h : MvPolynomial σ k) (z : k) (v : σ → k) :
    IsSingularPoint (purelyInseparable p h) (fun o => Option.elim o z v) ↔
      z ^ p + eval v h = 0 ∧ IsCriticalPoint h v := sorry

/-- `Singularity/Invariant/FrobeniusNewton.lean`: some `z ≠ 0` makes `(z, v)` a singular point of `z^p + h` if and only if `h(v) ≠ 0` and `v` is critical. -/
theorem exists_isSingularPoint_purelyInseparable_iff {σ k : Type*} [CommRing k] [IsReduced k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] (h : MvPolynomial σ k) (v : σ → k) :
    (∃ z ≠ 0, IsSingularPoint (purelyInseparable p h) (fun o => Option.elim o z v)) ↔
      eval v h ≠ 0 ∧ IsCriticalPoint h v := sorry

/-- `Singularity/Invariant/FrobeniusNewton.lean`: the torus criterion for one face. -/
theorem exists_torus_isCriticalPoint_iff {σ k : Type*} [CommRing k] [IsReduced k] (p : ℕ)
    [Fact p.Prime] [CharP k p] [PerfectRing k p] (h : MvPolynomial σ k) :
    (∃ v : σ → k, (∀ i, v i ≠ 0) ∧ IsCriticalPoint h v) ↔
      (∃ v : σ → k, (∀ i, v i ≠ 0) ∧ IsSingularPoint h v) ∨
        ∃ u : Option σ → k, (∀ o, u o ≠ 0) ∧ IsSingularPoint (purelyInseparable p h) u := sorry

/-- `Singularity/Invariant/FrobeniusNewton.lean`: the mod `p` Euler identity. -/
theorem eq_sum_smul_X_mul_pderiv {σ k : Type*} [Fintype σ] [CommSemiring k] (w : σ → k)
    {h : MvPolynomial σ k} (hw : ∀ a ∈ h.support, ∑ i ∈ a.support, w i * (a i : k) = 1) :
    h = ∑ i, w i • (X i * pderiv i h) := sorry

/-- `Singularity/Invariant/FrobeniusNewton.lean`: the Euler identity for a weighted homogeneous polynomial. -/
theorem eq_inv_smul_sum_X_mul_pderiv {σ k : Type*} [Fintype σ] [Field k] {w : σ → ℕ} {D : ℕ}
    {h : MvPolynomial σ k} (hh : IsWeightedHomogeneous w h D) (hD : (D : k) ≠ 0) :
    h = (D : k)⁻¹ • ∑ i, (w i : k) • (X i * pderiv i h) := sorry

/-- `Singularity/Invariant/FrobeniusNewton.lean`: a critical point of a weighted homogeneous `h` of degree `D ≠ 0` in `k` lies on `{h = 0}`. -/
theorem eval_eq_zero_of_isCriticalPoint_of_isWeightedHomogeneous {σ k : Type*} [Fintype σ]
    [Field k] {w : σ → ℕ} {D : ℕ} {h : MvPolynomial σ k} (hh : IsWeightedHomogeneous w h D)
    (hD : (D : k) ≠ 0) {v : σ → k} (hv : IsCriticalPoint h v) : eval v h = 0 := sorry

/-- `Singularity/Invariant/FrobeniusNewton.lean`: each partial derivative of `c x^a` with `a ∈ p ℕ^σ` is `0`. -/
theorem pderiv_monomial_eq_zero_of_dvd {σ k : Type*} [CommSemiring k] (p : ℕ) [CharP k p]
    {a : σ →₀ ℕ} (ha : ∀ i, p ∣ a i) (c : k) (i : σ) : pderiv i (monomial a c) = 0 := sorry

/-- `Singularity/Invariant/FrobeniusNewton.lean`: `z^p + c x^a` with `a ∈ p ℕ^σ` and `c ≠ 0` has a singular point in the torus. -/
theorem exists_torus_isSingularPoint_purelyInseparable_monomial {σ k : Type*} [CommRing k]
    [IsReduced k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] {a : σ →₀ ℕ}
    (ha : ∀ i, p ∣ a i) {c : k} (hc : c ≠ 0) :
    ∃ u : Option σ → k, (∀ o, u o ≠ 0) ∧ IsSingularPoint (purelyInseparable p (monomial a c)) u :=
  sorry

/-- `Singularity/Invariant/FrobeniusNewton.lean`: a support that is not resonant gives a mod `p` Euler identity. -/
theorem exists_eq_sum_smul_X_mul_pderiv_of_not_isResonant {σ k : Type*} [CommRing k] (p : ℕ)
    [CharP k p] [Fintype σ] {h : MvPolynomial σ k} (hh : ¬ IsResonant p h.support) :
    ∃ w : σ → k, h = ∑ i, w i • (X i * pderiv i h) := sorry

/-- `Singularity/Invariant/FrobeniusNewton.lean`: a critical point of a polynomial with a support that is not resonant lies on its zero set. -/
theorem eval_eq_zero_of_isCriticalPoint_of_not_isResonant {σ k : Type*} [CommRing k] (p : ℕ)
    [CharP k p] [Fintype σ] {h : MvPolynomial σ k} (hh : ¬ IsResonant p h.support) {v : σ → k}
    (hv : IsCriticalPoint h v) : eval v h = 0 := sorry

/-- `Singularity/Invariant/FrobeniusNewton.lean`: a weighted homogeneous polynomial of degree `D` with `p ∤ D` is not resonant. -/
theorem not_isResonant_of_isWeightedHomogeneous {σ R : Type*} [CommSemiring R] (p : ℕ)
    [Fact p.Prime] {w : σ → ℕ} {D : ℕ} {h : MvPolynomial σ R} (hh : IsWeightedHomogeneous w h D)
    (hD : ¬ p ∣ D) : ¬ IsResonant p h.support := sorry

/-- `Singularity/Invariant/FrobeniusNewton.lean`: the initial form is not resonant if `p` does not divide the weighted order. -/
theorem not_isResonant_initialForm {σ R : Type*} [CommSemiring R] (p : ℕ) [Fact p.Prime]
    (w : σ → ℕ) (g : MvPolynomial σ R) (hD : ¬ p ∣ (weightedOrd w g).toNat) :
    ¬ IsResonant p (initialForm w g).support := sorry

end FrobeniusNewton

section LogJacobianBlowup

open MvPolynomial

section Defs

variable {σ k : Type*} [CommSemiring k]

/-- `Singularity/Invariant/LogJacobianBlowup.lean`: the log-Jacobian ideal `Θ₀(g)` tangent to the
origin. -/
noncomputable def logJacobianTangent (Δ : Finset σ) (g : MvPolynomial σ k) :
    Ideal (MvPolynomial σ k) :=
  Ideal.span ((fun i => X i * pderiv i g) '' (Δ : Set σ) ∪
    (fun a : σ × σ => X a.1 * pderiv a.2 g) '' {a | a.2 ∉ Δ})

/-- `Singularity/Invariant/LogJacobianBlowup.lean`: the unit `u` of the transformation law. -/
noncomputable def blowupUnit [DecidableEq σ] [DecidableEq k] (Δ : Finset σ) (j : σ) (t : σ → k) :
    MvPolynomial σ k :=
  ∏ i ∈ Δ.filter (fun i => i ≠ j ∧ t i ≠ 0), (X i + C (t i))

end Defs

section Chain

variable {σ k : Type*} [CommSemiring k] [DecidableEq σ]

/-- `Singularity/Invariant/LogJacobianBlowup.lean`: `∂_i π(h) = x_j π(∂_i h)` for `i ≠ j`. -/
theorem pderiv_pointChart_of_ne {i j : σ} (hij : i ≠ j) (t : σ → k) (h : MvPolynomial σ k) :
    pderiv i (pointChart j t h) = X j * pointChart j t (pderiv i h) := sorry

/-- `Singularity/Invariant/LogJacobianBlowup.lean`: `x_j ∂_j π(h) = π(∑_i x_i ∂_i h)`. -/
theorem X_mul_pderiv_pointChart [Fintype σ] (j : σ) (t : σ → k) (h : MvPolynomial σ k) :
    X j * pderiv j (pointChart j t h) = pointChart j t (∑ i, X i * pderiv i h) := sorry

end Chain

section Factor

variable {σ k : Type*} [CommSemiring k]

/-- `Singularity/Invariant/LogJacobianBlowup.lean`: `∂_i (x_j^n u) = x_j^n ∂_i u` for `i ≠ j`. -/
theorem pderiv_X_pow_mul_of_ne {i j : σ} (hij : i ≠ j) (n : ℕ) (u : MvPolynomial σ k) :
    pderiv i (X j ^ n * u) = X j ^ n * pderiv i u := sorry

/-- `Singularity/Invariant/LogJacobianBlowup.lean`: `x_j ∂_j (x_j^p u) = x_j^p (x_j ∂_j u)`. -/
theorem X_mul_pderiv_X_pow_mul (p : ℕ) [CharP k p] (j : σ) (u : MvPolynomial σ k) :
    X j * pderiv j (X j ^ p * u) = X j ^ p * (X j * pderiv j u) := sorry

end Factor

section Law

variable {σ k : Type*} [CommRing k] [DecidableEq σ] [DecidableEq k] [Fintype σ]

/-- `Singularity/Invariant/LogJacobianBlowup.lean`: `π(Θ₀(g)) ⊆ Θ'(π(g))`. -/
theorem map_pointChart_logJacobianTangent_le (Δ : Finset σ) (j : σ) (t : σ → k)
    (g : MvPolynomial σ k) :
    Ideal.map (pointChart j t) (logJacobianTangent Δ g) ≤
      logJacobian (blowupDivisor Δ j t) (pointChart j t g) := sorry

/-- `Singularity/Invariant/LogJacobianBlowup.lean`: `u Θ'(π(g)) ⊆ π(Θ₀(g))`. -/
theorem span_mul_logJacobian_pointChart_le (Δ : Finset σ) (j : σ) (t : σ → k)
    (g : MvPolynomial σ k) :
    Ideal.span {blowupUnit Δ j t} * logJacobian (blowupDivisor Δ j t) (pointChart j t g) ≤
      Ideal.map (pointChart j t) (logJacobianTangent Δ g) := sorry

variable (p : ℕ) [CharP k p] {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- `Singularity/Invariant/LogJacobianBlowup.lean`: `π(Θ₀(g)) ⊆ (x_j^p) Θ'(g')`. -/
theorem map_pointChart_logJacobianTangent_le_span_mul (hg : pointChart j t g = X j ^ p * g') :
    Ideal.map (pointChart j t) (logJacobianTangent Δ g) ≤
      Ideal.span {X j ^ p} * logJacobian (blowupDivisor Δ j t) g' := sorry

/-- `Singularity/Invariant/LogJacobianBlowup.lean`: `(x_j^p u) Θ'(g') ⊆ π(Θ₀(g))`. -/
theorem span_mul_logJacobian_le_map_pointChart (hg : pointChart j t g = X j ^ p * g') :
    Ideal.span {X j ^ p * blowupUnit Δ j t} * logJacobian (blowupDivisor Δ j t) g' ≤
      Ideal.map (pointChart j t) (logJacobianTangent Δ g) := sorry

end Law

end LogJacobianBlowup

section LogJacobianCenter

open MvPolynomial

section Defs

variable {σ k : Type*} [CommSemiring k]

/-- `Singularity/Invariant/LogJacobianCenter.lean`: the `x_j`-chart of the blowup of the center
`V(x_i : i ∈ S)` with translations `t`. -/
noncomputable def centerChart [DecidableEq σ] (S : Finset σ) (j : σ) (t : σ → k) :
    MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval fun i => if i = j then X j else if i ∈ S then X j * (X i + C (t i)) else X i

/-- `Singularity/Invariant/LogJacobianCenter.lean`: the log-Jacobian ideal `Θ_C(g)` tangent to the
center. -/
noncomputable def logJacobianCenter (Δ S : Finset σ) (g : MvPolynomial σ k) :
    Ideal (MvPolynomial σ k) :=
  Ideal.span ((fun i => X i * pderiv i g) '' (Δ : Set σ) ∪
    (fun l => pderiv l g) '' {l | l ∉ Δ ∧ l ∉ S} ∪
    (fun a : σ × σ => X a.1 * pderiv a.2 g) '' {a | a.2 ∉ Δ ∧ a.2 ∈ S ∧ a.1 ∈ S})

/-- `Singularity/Invariant/LogJacobianCenter.lean`: the transform of the divisor under the chart. -/
noncomputable def centerDivisor [DecidableEq σ] [DecidableEq k] (Δ S : Finset σ) (j : σ)
    (t : σ → k) : Finset σ :=
  insert j (Δ.filter fun i => i ≠ j ∧ (i ∉ S ∨ t i = 0))

/-- `Singularity/Invariant/LogJacobianCenter.lean`: the unit `u` of the transformation law for the
center. -/
noncomputable def centerUnit [DecidableEq σ] [DecidableEq k] (Δ S : Finset σ) (j : σ)
    (t : σ → k) : MvPolynomial σ k :=
  ∏ i ∈ Δ.filter (fun i => i ≠ j ∧ i ∈ S ∧ t i ≠ 0), (X i + C (t i))

/-- `Singularity/Invariant/LogJacobianCenter.lean`: `Θ_C(g) ⊆ Θ(g)`. -/
theorem logJacobianCenter_le (Δ S : Finset σ) (g : MvPolynomial σ k) :
    logJacobianCenter Δ S g ≤ logJacobian Δ g := sorry

/-- `Singularity/Invariant/LogJacobianCenter.lean`: `I_C Θ(g) ⊆ Θ_C(g)`. -/
theorem span_X_mul_logJacobian_le (Δ S : Finset σ) (g : MvPolynomial σ k) :
    Ideal.span (X '' (S : Set σ)) * logJacobian Δ g ≤ logJacobianCenter Δ S g := sorry

/-- `Singularity/Invariant/LogJacobianCenter.lean`: for the origin, `Θ_C(g) = Θ₀(g)`. -/
theorem logJacobianCenter_univ [Fintype σ] (Δ : Finset σ) (g : MvPolynomial σ k) :
    logJacobianCenter Δ Finset.univ g = logJacobianTangent Δ g := sorry

variable [DecidableEq σ]

/-- `Singularity/Invariant/LogJacobianCenter.lean`: for the origin, the chart of the point blowup. -/
theorem centerChart_univ [Fintype σ] (j : σ) (t : σ → k) :
    centerChart Finset.univ j t = pointChart j t := sorry

end Defs

section Chain

variable {σ k : Type*} [CommSemiring k] [DecidableEq σ]

/-- `Singularity/Invariant/LogJacobianCenter.lean`: `∂_i π(h) = π(∂_i h)` for `i ∉ S`. -/
theorem pderiv_centerChart_of_notMem {S : Finset σ} {i j : σ} (hj : j ∈ S) (hi : i ∉ S)
    (t : σ → k) (h : MvPolynomial σ k) :
    pderiv i (centerChart S j t h) = centerChart S j t (pderiv i h) := sorry

/-- `Singularity/Invariant/LogJacobianCenter.lean`: `∂_i π(h) = x_j π(∂_i h)` for `i ∈ S`,
`i ≠ j`. -/
theorem pderiv_centerChart_of_mem {S : Finset σ} {i j : σ} (hi : i ∈ S) (hij : i ≠ j)
    (t : σ → k) (h : MvPolynomial σ k) :
    pderiv i (centerChart S j t h) = X j * centerChart S j t (pderiv i h) := sorry

/-- `Singularity/Invariant/LogJacobianCenter.lean`: `x_j ∂_j π(h) = π(∑_{i ∈ S} x_i ∂_i h)`. -/
theorem X_mul_pderiv_centerChart {S : Finset σ} {j : σ} (hj : j ∈ S) (t : σ → k)
    (h : MvPolynomial σ k) :
    X j * pderiv j (centerChart S j t h) = centerChart S j t (∑ i ∈ S, X i * pderiv i h) := sorry

end Chain

section Law

variable {σ k : Type*} [CommRing k] [DecidableEq σ] [DecidableEq k]

/-- `Singularity/Invariant/LogJacobianCenter.lean`: `π(Θ_C(g)) ⊆ Θ'(π(g))`. -/
theorem map_centerChart_logJacobianCenter_le (Δ S : Finset σ) {j : σ} (hj : j ∈ S) (t : σ → k)
    (g : MvPolynomial σ k) :
    Ideal.map (centerChart S j t) (logJacobianCenter Δ S g) ≤
      logJacobian (centerDivisor Δ S j t) (centerChart S j t g) := sorry

/-- `Singularity/Invariant/LogJacobianCenter.lean`: `u Θ'(π(g)) ⊆ π(Θ_C(g))`. -/
theorem span_mul_logJacobian_centerChart_le (Δ S : Finset σ) {j : σ} (hj : j ∈ S) (t : σ → k)
    (g : MvPolynomial σ k) :
    Ideal.span {centerUnit Δ S j t} * logJacobian (centerDivisor Δ S j t) (centerChart S j t g) ≤
      Ideal.map (centerChart S j t) (logJacobianCenter Δ S g) := sorry

variable (p : ℕ) [CharP k p] {Δ S : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- `Singularity/Invariant/LogJacobianCenter.lean`: `π(Θ_C(g)) ⊆ (x_j^p) Θ'(g')`. -/
theorem map_centerChart_logJacobianCenter_le_span_mul (hj : j ∈ S)
    (hg : centerChart S j t g = X j ^ p * g') :
    Ideal.map (centerChart S j t) (logJacobianCenter Δ S g) ≤
      Ideal.span {X j ^ p} * logJacobian (centerDivisor Δ S j t) g' := sorry

/-- `Singularity/Invariant/LogJacobianCenter.lean`: `(x_j^p u) Θ'(g') ⊆ π(Θ_C(g))`. -/
theorem span_mul_logJacobian_le_map_centerChart (hj : j ∈ S)
    (hg : centerChart S j t g = X j ^ p * g') :
    Ideal.span {X j ^ p * centerUnit Δ S j t} * logJacobian (centerDivisor Δ S j t) g' ≤
      Ideal.map (centerChart S j t) (logJacobianCenter Δ S g) := sorry

end Law

section Weak

variable {σ k : Type*} [Field k] [DecidableEq σ]

/-- `Singularity/Invariant/LogJacobianCenter.lean`: if `f ∈ I_C^s`, then `π(f) = x_j^s f'`. -/
theorem exists_centerChart_eq_X_pow_mul {S : Finset σ} {j : σ} (t : σ → k) {s : ℕ}
    {f : MvPolynomial σ k} (hS : f ∈ Ideal.span (X '' (S : Set σ)) ^ s) :
    ∃ f', centerChart S j t f = X j ^ s * f' := sorry

/-- `Singularity/Invariant/LogJacobianCenter.lean`: the equimultiple weak transform. If
`f ∈ I_C^s`, `ord f = s` and `π(f) = x_j^s f'`, then `ord f' ≤ s`. -/
theorem ord_le_of_centerChart {S : Finset σ} {j : σ} (hj : j ∈ S) {t : σ → k} {s : ℕ}
    {f f' : MvPolynomial σ k} (hS : f ∈ Ideal.span (X '' (S : Set σ)) ^ s) (hf : ord f = s)
    (h : centerChart S j t f = X j ^ s * f') : ord f' ≤ s := sorry

end Weak

end LogJacobianCenter

section MvHasse

namespace Algebra.MvHasse

open MvPolynomial Finsupp

section Defs

variable {σ : Type*}

/-- `Singularity/Algebra/MvHasse.lean`: the binomial coefficient of two multi-indices. -/
def choose (β α : σ →₀ ℕ) : ℕ :=
  ∏ i ∈ α.support, (β i).choose (α i)

end Defs

section Defs

variable {σ R : Type*} [CommSemiring R]

variable (σ R) in
/-- `Singularity/Algebra/MvHasse.lean`: the Taylor substitution `x_i ↦ x_i + y_i`. -/
noncomputable def taylor : MvPolynomial σ R →ₐ[R] MvPolynomial σ (MvPolynomial σ R) :=
  aeval fun i => C (X i) + X i

/-- `Singularity/Algebra/MvHasse.lean`: the Hasse-Schmidt derivative `D^α`. -/
noncomputable def hasseDeriv (α : σ →₀ ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R where
  toFun f := (taylor σ R f).coeff α
  map_add' f g := by rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  map_smul' c f := by rw [map_smul, coeff_smul, RingHom.id_apply]

end Defs

/-- `Singularity/Algebra/MvHasse.lean`: `D^α (r x^β) = binom(β, α) r x^(β - α)`. -/
theorem hasseDeriv_monomial {σ R : Type*} [CommSemiring R] (α β : σ →₀ ℕ) (r : R) :
    hasseDeriv α (monomial β r) = monomial (β - α) ((choose β α : R) * r) := sorry

/-- `Singularity/Algebra/MvHasse.lean`: `D^0` is the identity. -/
theorem hasseDeriv_zero {σ R : Type*} [CommSemiring R] :
    (hasseDeriv 0 : MvPolynomial σ R →ₗ[R] MvPolynomial σ R) = LinearMap.id := sorry

/-- `Singularity/Algebra/MvHasse.lean`: `D^α` on the constants. -/
theorem hasseDeriv_C {σ R : Type*} [CommSemiring R] [DecidableEq σ] (α : σ →₀ ℕ) (r : R) :
    hasseDeriv α (C r : MvPolynomial σ R) = if α = 0 then C r else 0 := sorry

/-- `Singularity/Algebra/MvHasse.lean`: `D^α` on the variables. -/
theorem hasseDeriv_X {σ R : Type*} [CommSemiring R] [DecidableEq σ] (α : σ →₀ ℕ) (i : σ) :
    hasseDeriv α (X i : MvPolynomial σ R) =
      if α = 0 then X i else if α = single i 1 then 1 else 0 := sorry

/-- `Singularity/Algebra/MvHasse.lean`: in one variable, `D^α` is `Polynomial.hasseDeriv`. -/
theorem uniqueAlgEquiv_hasseDeriv {σ R : Type*} [CommSemiring R] [Unique σ] (α : σ →₀ ℕ)
    (f : MvPolynomial σ R) :
    uniqueAlgEquiv R σ (hasseDeriv α f) =
      Polynomial.hasseDeriv (α default) (uniqueAlgEquiv R σ f) := sorry

/-- `Singularity/Algebra/MvHasse.lean`: `D^(e_i)` is the partial derivative `∂_i`. -/
theorem hasseDeriv_single_one {σ R : Type*} [CommSemiring R] (i : σ) (f : MvPolynomial σ R) :
    hasseDeriv (single i 1) f = pderiv i f := sorry

/-- `Singularity/Algebra/MvHasse.lean`: the Leibniz rule. -/
theorem hasseDeriv_mul {σ R : Type*} [CommSemiring R] [DecidableEq σ] (α : σ →₀ ℕ)
    (f g : MvPolynomial σ R) :
    hasseDeriv α (f * g) =
      ∑ x ∈ Finset.antidiagonal α, hasseDeriv x.1 f * hasseDeriv x.2 g := sorry

/-- `Singularity/Algebra/MvHasse.lean`: the composition rule. -/
theorem hasseDeriv_comp {σ R : Type*} [CommSemiring R] (α β : σ →₀ ℕ) (f : MvPolynomial σ R) :
    hasseDeriv α (hasseDeriv β f) = choose (α + β) α • hasseDeriv (α + β) f := sorry

/-- `Singularity/Algebra/MvHasse.lean`: the coefficients of `D^α f`. -/
theorem coeff_hasseDeriv {σ R : Type*} [CommSemiring R] (α γ : σ →₀ ℕ) (f : MvPolynomial σ R) :
    (hasseDeriv α f).coeff γ = (choose (γ + α) α : R) * f.coeff (γ + α) := sorry

/-- `Singularity/Algebra/MvHasse.lean`: `(D^α f)(0)` is the coefficient of `x^α` in `f`. -/
theorem constantCoeff_hasseDeriv {σ R : Type*} [CommSemiring R] (α : σ →₀ ℕ)
    (f : MvPolynomial σ R) :
    constantCoeff (hasseDeriv α f) = f.coeff α := sorry

/-- `Singularity/Algebra/MvHasse.lean`: the order criterion at the origin. -/
theorem le_ord_iff_hasseDeriv {σ R : Type*} [CommSemiring R] {f : MvPolynomial σ R} {d : ℕ} :
    (d : ℕ∞) ≤ ord f ↔ ∀ α : σ →₀ ℕ, degree α < d → constantCoeff (hasseDeriv α f) = 0 := sorry

/-- `Singularity/Algebra/MvHasse.lean`: the Taylor formula. -/
theorem taylor_eq_sum {σ R : Type*} [CommSemiring R] [DecidableEq σ] (f : MvPolynomial σ R) :
    taylor σ R f = ∑ α ∈ Finset.Iic (f.support.sup id), monomial α (hasseDeriv α f) := sorry

/-- `Singularity/Algebra/MvHasse.lean`: the coefficients of `f(a + y)`. -/
theorem coeff_aeval_X_add_C {σ R : Type*} [CommSemiring R] (a : σ → R) (α : σ →₀ ℕ)
    (f : MvPolynomial σ R) :
    (aeval (fun i => X i + C (a i)) f).coeff α = eval a (hasseDeriv α f) := sorry

/-- `Singularity/Algebra/MvHasse.lean`: the Taylor formula at a point `a`. -/
theorem aeval_X_add_C_eq_sum {σ R : Type*} [CommSemiring R] [DecidableEq σ] (a : σ → R)
    (f : MvPolynomial σ R) :
    aeval (fun i => X i + C (a i)) f =
      ∑ α ∈ Finset.Iic (f.support.sup id), monomial α (eval a (hasseDeriv α f)) := sorry

/-- `Singularity/Algebra/MvHasse.lean`: the order criterion at a point `a`. -/
theorem le_ord_aeval_X_add_C_iff {σ R : Type*} [CommSemiring R] (a : σ → R)
    {f : MvPolynomial σ R} {d : ℕ} :
    (d : ℕ∞) ≤ ord (aeval (fun i => X i + C (a i)) f) ↔
      ∀ α : σ →₀ ℕ, degree α < d → eval a (hasseDeriv α f) = 0 := sorry

/-- `Singularity/Algebra/MvHasse.lean`: the polynomials in the `x_i^q`. -/
theorem exists_expand_eq_iff {σ R : Type*} [CommSemiring R] {q : ℕ} (f : MvPolynomial σ R) :
    (∃ g, expand q g = f) ↔ ∀ β ∈ f.support, ∀ i, q ∣ β i := sorry

/-- `Singularity/Algebra/MvHasse.lean`: the test for `q`-th powers in characteristic `p`. -/
theorem exists_expand_eq_iff_hasseDeriv {σ R : Type*} [CommSemiring R] (p : ℕ) [Fact p.Prime]
    [CharP R p] (e : ℕ) (f : MvPolynomial σ R) :
    (∃ g, expand (p ^ e) g = f) ↔
      ∀ α : σ →₀ ℕ, α ≠ 0 → (∀ i, α i < p ^ e) → hasseDeriv α f = 0 := sorry

/-- `Singularity/Algebra/MvHasse.lean`: `D^α (g(x^q) f) = g(x^q) D^α f` for `α_i < q`. -/
theorem hasseDeriv_expand_mul {σ R : Type*} [CommSemiring R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (e : ℕ) {α : σ →₀ ℕ} (hα : ∀ i, α i < p ^ e) (g f : MvPolynomial σ R) :
    hasseDeriv α (expand (p ^ e) g * f) = expand (p ^ e) g * hasseDeriv α f := sorry

end Algebra.MvHasse

end MvHasse

section LogJacobianNonincrease

open MvPolynomial Finsupp

section Divisibility

variable {σ k : Type*} [Field k]

/-- `Singularity/Invariant/LogJacobianNonincrease.lean`: `x^b` divides `f` if and only if each
monomial of `f` is divisible by `x^b`. -/
theorem monomial_one_dvd_iff {b : σ →₀ ℕ} {f : MvPolynomial σ k} :
    monomial b (1 : k) ∣ f ↔ ∀ a ∈ f.support, b ≤ a := sorry

/-- `Singularity/Invariant/LogJacobianNonincrease.lean`: the cancellation of a factor `u` with a
nonzero constant term. -/
theorem monomial_one_dvd_of_dvd_mul {b : σ →₀ ℕ} {u f : MvPolynomial σ k}
    (hu : constantCoeff u ≠ 0) (h : monomial b (1 : k) ∣ u * f) : monomial b (1 : k) ∣ f := sorry

end Divisibility

section Chart

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k]

/-- `Singularity/Invariant/MohBound.lean`: the exponents of the factors `x_l` of `π(x^r)` for
`l ≠ j` with `t_l = 0`. -/
noncomputable def chartExponent (j : σ) (t : σ → k) (r : σ →₀ ℕ) : σ →₀ ℕ :=
  r.filter fun l => l ≠ j ∧ t l = 0

/-- `Singularity/Invariant/LogJacobianNonincrease.lean`: `x_j^(|r| + c) x^e` divides `π(h)`. -/
theorem dvd_pointChart_of_monomial_one_dvd {j : σ} {t : σ → k} {r : σ →₀ ℕ} {c : ℕ}
    {h : MvPolynomial σ k} (hr : monomial r (1 : k) ∣ h)
    (hc : ((degree r + c : ℕ) : ℕ∞) ≤ ord h) :
    X j ^ (degree r + c) * monomial (chartExponent j t r) (1 : k) ∣ pointChart j t h := sorry

/-- `Singularity/Invariant/LogJacobianNonincrease.lean`: the image of an ideal under the chart,
through its generators. -/
theorem map_pointChart_span_le {j : σ} {t : σ → k} {S : Set (MvPolynomial σ k)} {r : σ →₀ ℕ}
    {c : ℕ} (hS : ∀ s ∈ S, monomial r (1 : k) ∣ s ∧ ((degree r + c : ℕ) : ℕ∞) ≤ ord s) :
    Ideal.map (pointChart j t) (Ideal.span S) ≤
      Ideal.span {X j ^ (degree r + c) * monomial (chartExponent j t r) (1 : k)} := sorry

/-- `Singularity/Invariant/LogJacobianNonincrease.lean`: the constant term of `u` is not `0`. -/
theorem constantCoeff_blowupUnit_ne_zero (Δ : Finset σ) (j : σ) (t : σ → k) :
    constantCoeff (blowupUnit Δ j t) ≠ 0 := sorry

end Chart

section Order

variable {σ k : Type*} [Field k] {Δ : Finset σ} {g : MvPolynomial σ k}

/-- `Singularity/Invariant/LogJacobianNonincrease.lean`: `ord Θ₀(g) ≥ ord g`. -/
theorem le_idealOrd_logJacobianTangent {n : ℕ} (hn : (n : ℕ∞) ≤ ord g) :
    (n : ℕ∞) ≤ idealOrd (logJacobianTangent Δ g) := sorry

variable (p : ℕ) [CharP k p]

/-- `Singularity/Invariant/LogJacobianNonincrease.lean`: the cancellation of a monomial factor in
the residual ideal. -/
theorem logJacobianOrder_le_of_mem (hg : g ≠ 0) (hc : IsClean p g) {b : σ →₀ ℕ}
    (hb : ∀ i, i ∉ Δ → b i = 0) (hle : logJacobian Δ g ≤ Ideal.span {monomial b 1})
    {φ : MvPolynomial σ k} (hφ : φ ∈ logJacobian Δ g) {n : ℕ∞} (hn : ord φ ≤ degree b + n) :
    logJacobianOrder Δ g ≤ n := sorry

end Order

section Nonincrease

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- `Singularity/Invariant/LogJacobianNonincrease.lean`: `ρ` does not go up, Theorem 3.2.4. -/
theorem logJacobianOrder_cleanPart_le (hg : g ≠ 0) (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g)
    (h : pointChart j t g = X j ^ p * g') :
    cleanPart p g' ≠ 0 ∧
      logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') ≤ logJacobianOrder Δ g := sorry

/-- `Singularity/Invariant/LogJacobianNonincrease.lean`: `d' ≤ ρ(g'_c) + 1 ≤ ρ + 1 ≤ d + 1`,
Corollary 3.2.5. -/
theorem residualOrderAlong_pointChart_le_logJacobianOrder (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') :
    residualOrderAlong (blowupDivisor Δ j t) p g' ≤
        logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') + 1 ∧
      logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') + 1 ≤ logJacobianOrder Δ g + 1 ∧
      logJacobianOrder Δ g + 1 ≤ residualOrderAlong Δ p g + 1 := sorry

/-- `Singularity/Invariant/LogJacobianNonincrease.lean`: `d' ≤ d + 1`, Corollary 3.2.5. -/
theorem residualOrderAlong_pointChart_le_add_one (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') :
    residualOrderAlong (blowupDivisor Δ j t) p g' ≤ residualOrderAlong Δ p g + 1 := sorry

end Nonincrease

end LogJacobianNonincrease

end Singularity
