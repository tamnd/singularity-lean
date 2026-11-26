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
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.NNReal.Basic
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.Basic.Real.Embedding
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Localization.Integral
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# The challenge of the comparator

This file is the challenge of `lake comparator` (spec 14, row Q4). It states again, with `sorry`, the theorems of the package that prove a statement of `Singularity/Statements/`. It imports the statement files, and the Mathlib files that `Singularity/Valuation/Abhyankar.lean`, `Singularity/Valuation/ZariskiRiemann.lean`, `Singularity/Valuation/KeyPolynomials.lean`, `Singularity/Invariant/CharacteristicPolyhedron.lean`, `Singularity/Invariant/Order.lean`, `Singularity/Invariant/Residual.lean`, `Singularity/Invariant/RigidLayer.lean`, `Singularity/Invariant/LogJacobian.lean`, `Singularity/Invariant/Newton.lean`, `Singularity/Invariant/FrobeniusNewton.lean`, `Singularity/Algebra/MvHasse.lean` and `Singularity/Alteration/Basic.lean`, `Singularity/Valuation/LatticeLemma.lean`, `Singularity/Valuation/LatticeLemmaOrdered.lean`, `Singularity/Valuation/LocalUniformizationMonomial.lean`, `Singularity/Valuation/MonomialGroundField.lean`, `Singularity/Valuation/EtaleRegular.lean`, `Singularity/Valuation/EtaleGenerator.lean`, `Singularity/Valuation/EtaleGeneratorExistence.lean`, `Singularity/Valuation/MonomialFiniteExtension.lean`, `Singularity/Valuation/DegreePTowers.lean`, `Singularity/Valuation/InertiaField.lean` and `Singularity/Valuation/AbhyankarSubfield.lean` import. A statement that uses a definition of the package states this definition again, with the same name and the same body. The file `comparator.json` names these theorems, and the comparator checks that the theorems of the same names in `Singularity` have the same types, use only the permitted axioms, and are accepted by the kernel.

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

section LatticeLemma

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Singularity/Valuation/LatticeLemma.lean`: the lattice lemma for positive real weights that are linearly independent over `ℤ`. -/
theorem latticeLemma_real_of_pos (γ : ι → ℝ) (hγ : ∀ i, 0 < γ i)
    (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * γ i = 0 → a = 0) (E : Finset (ι → ℤ))
    (hE : ∀ a ∈ E, 0 ≤ ∑ i, (a i : ℝ) * γ i) :
    ∃ B C : Matrix ι ι ℤ, B * C = 1 ∧ C * B = 1 ∧ (∀ l, 0 < ∑ i, (B l i : ℝ) * γ i) ∧
      ∀ a ∈ E, ∀ l, 0 ≤ (a ᵥ* C) l := sorry

/-- `Singularity/Valuation/LatticeLemma.lean`: the lattice lemma for real weights that are linearly independent over `ℤ`. -/
theorem latticeLemma_real (γ : ι → ℝ)
    (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * γ i = 0 → a = 0) (E : Finset (ι → ℤ))
    (hE : ∀ a ∈ E, 0 ≤ ∑ i, (a i : ℝ) * γ i) :
    ∃ B C : Matrix ι ι ℤ, B * C = 1 ∧ C * B = 1 ∧ (∀ l, 0 < ∑ i, (B l i : ℝ) * γ i) ∧
      ∀ a ∈ E, ∀ l, 0 ≤ (a ᵥ* C) l := sorry

end LatticeLemma

section LatticeLemmaOrdered

open Matrix

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  {ι : Type*} [Fintype ι]

/-- `Singularity/Valuation/LatticeLemmaOrdered.lean`: the lattice lemma for a free abelian group of finite rank with a total order compatible with addition. -/
theorem latticeLemma (b : Module.Basis ι ℤ Γ) (D : Finset Γ) (hD : ∀ d ∈ D, 0 ≤ d) :
    ∃ m : Module.Basis ι ℤ Γ, (∀ i, 0 < m i) ∧ ∀ d ∈ D, ∀ i, 0 ≤ m.repr d i := sorry

/-- `Singularity/Valuation/LatticeLemmaOrdered.lean`: the lattice lemma in matrix form. -/
theorem latticeLemma_of_injective [DecidableEq ι] {G : Type*} [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] (w : (ι → ℤ) →+ G) (hw : Function.Injective w)
    (E : Finset (ι → ℤ)) (hE : ∀ a ∈ E, 0 ≤ w a) :
    ∃ B C : Matrix ι ι ℤ, B * C = 1 ∧ C * B = 1 ∧ (∀ l, 0 < w (B l)) ∧
      ∀ a ∈ E, ∀ l, 0 ≤ (a ᵥ* C) l := sorry

end LatticeLemmaOrdered

section LocalUniformizationMonomial

open Matrix
open scoped NNReal

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- The Laurent monomial `x^a = ∏ x_i ^ a_i` in elements `x_i` of a field. -/
def laurentMonomial (x : ι → K) (a : ι → ℤ) : K :=
  ∏ i, x i ^ a i

variable {k : Type*} [Field k] [Algebra k K]

variable (k) in
/-- The valuation `V` of `K/k` is a monomial valuation in the elements `x_1, ..., x_n` of `K`. -/
structure IsMonomialValuation (V : ValuationSubring K) (x : ι → K) : Prop where
  ne_zero : ∀ i, x i ≠ 0
  adjoin_eq_top : IntermediateField.adjoin k (Set.range x) = ⊤
  independent : ∀ a : ι → ℤ, V.valuation (laurentMonomial x a) = 1 → a = 0

variable {V : ValuationSubring K} [Algebra k V] [IsScalarTower k V K]

/-- `Singularity/Valuation/LocalUniformizationMonomial.lean`: a monomial valuation has local uniformization, if the lattice lemma holds for its values. -/
theorem hasLocalUniformization_of_isMonomialValuation_of_lattice [DecidableEq ι] {x : ι → K}
    (hV : IsMonomialValuation k V x)
    (hlat : ∀ E : Finset (ι → ℤ), (∀ a ∈ E, V.valuation (laurentMonomial x a) ≤ 1) →
      ∃ B C : Matrix ι ι ℤ, B * C = 1 ∧ C * B = 1 ∧
        (∀ l, V.valuation (laurentMonomial x (B l)) < 1) ∧ ∀ a ∈ E, ∀ l, 0 ≤ (a ᵥ* C) l) :
    HasLocalUniformization k V := sorry

/-- `Singularity/Valuation/LocalUniformizationMonomial.lean`: a monomial valuation of rank 1 has local uniformization. -/
theorem hasLocalUniformization_of_isMonomialValuation_of_rankOne {x : ι → K}
    (hV : IsMonomialValuation k V x) (φ : V.ValueGroup →*₀ ℝ≥0) (hφ : StrictMono φ) :
    HasLocalUniformization k V := sorry

/-- `Singularity/Valuation/LocalUniformizationMonomial.lean`: a monomial valuation has local uniformization. -/
theorem hasLocalUniformization_of_isMonomialValuation {x : ι → K}
    (hV : IsMonomialValuation k V x) : HasLocalUniformization k V := sorry

/-- `Singularity/Valuation/LocalUniformizationMonomial.lean`: a monomial valuation is an Abhyankar valuation. -/
theorem IsMonomialValuation.isAbhyankarValuation {x : ι → K}
    (hV : IsMonomialValuation k V x) : IsAbhyankarValuation k V := sorry

end LocalUniformizationMonomial

section MonomialGroundField

open IsLocalRing

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- `Singularity/Valuation/MonomialGroundField.lean`: local uniformization over a finitely generated subfield `F ⊆ V` gives local uniformization over `k`. -/
theorem HasLocalUniformization.of_intermediateField {V : ValuationSubring K}
    {F : IntermediateField k K} (hF : F.FG) (hFV : ∀ c ∈ F, c ∈ V)
    (h : HasLocalUniformization F V) : HasLocalUniformization k V := sorry

/-- `Singularity/Valuation/MonomialGroundField.lean`: elements of `V` with algebraically independent residues are algebraically independent. -/
theorem algebraicIndependent_of_residue {V : ValuationSubring K} [Algebra k V]
    [IsScalarTower k V K] {κ : Type*} {y : κ → V}
    (hy : AlgebraicIndependent k fun i => residue V (y i)) :
    AlgebraicIndependent k fun i => (y i : K) := sorry

/-- `Singularity/Valuation/MonomialGroundField.lean`: if `y_1, ..., y_m ∈ V` have algebraically independent residues, then `k(y_1, ..., y_m) ⊆ V`. -/
theorem mem_of_mem_adjoin_residue {V : ValuationSubring K} [Algebra k V]
    [IsScalarTower k V K] {κ : Type*} {y : κ → V}
    (hy : AlgebraicIndependent k fun i => residue V (y i)) {c : K}
    (hc : c ∈ IntermediateField.adjoin k (Set.range fun i => (y i : K))) : c ∈ V := sorry

/-- `Singularity/Valuation/MonomialGroundField.lean`: if `y_1, ..., y_m` are algebraically independent and `k(y_1, ..., y_m) ⊆ V`, then their residues are algebraically independent. -/
theorem algebraicIndependent_residue {V : ValuationSubring K} [Algebra k V]
    [IsScalarTower k V K] {κ : Type*} {y : κ → K} (hy : AlgebraicIndependent k y)
    (hyV : ∀ c ∈ IntermediateField.adjoin k (Set.range y), c ∈ V) :
    AlgebraicIndependent k fun i =>
      residue V ⟨y i, hyV _ (IntermediateField.subset_adjoin k _ (Set.mem_range_self i))⟩ := sorry

variable {ι : Type*} [Fintype ι]

/-- `Singularity/Valuation/MonomialGroundField.lean`: each element of the value group of a monomial valuation is the value of exactly one Laurent monomial. -/
theorem IsMonomialValuation.existsUnique_valuation_eq {V : ValuationSubring K} [Algebra k V]
    [IsScalarTower k V K] {x : ι → K} (hV : IsMonomialValuation k V x) (γ : V.ValueGroupˣ) :
    ∃! a : ι → ℤ, V.valuation (laurentMonomial x a) = γ := sorry

/-- `Singularity/Valuation/MonomialGroundField.lean`: the residue field of a monomial valuation is `k`. -/
theorem IsMonomialValuation.algebraMap_residueField_bijective {V : ValuationSubring K}
    [Algebra k V] [IsScalarTower k V K] {x : ι → K} (hV : IsMonomialValuation k V x) :
    Function.Bijective (algebraMap k (ResidueField V)) := sorry

variable {V : ValuationSubring K} [Algebra k V] [IsScalarTower k V K] {κ : Type*} [Fintype κ]

/-- `Singularity/Valuation/MonomialGroundField.lean`: a monomial valuation over `k(y)` that is trivial on `k(y)` has local uniformization over `k`. -/
theorem hasLocalUniformization_of_isMonomialValuation_adjoin {V : ValuationSubring K}
    {y : κ → K} {x : ι → K} (hyV : ∀ c ∈ IntermediateField.adjoin k (Set.range y), c ∈ V)
    (hV : IsMonomialValuation (IntermediateField.adjoin k (Set.range y)) V x) :
    HasLocalUniformization k V := sorry

/-- `Singularity/Valuation/MonomialGroundField.lean`: a monomial valuation over `k(y)` that is trivial on `k(y)` is an Abhyankar valuation of `K/k`. -/
theorem IsMonomialValuation.isAbhyankarValuation_adjoin {y : κ → K} {x : ι → K}
    (hy : AlgebraicIndependent k y)
    (hyV : ∀ c ∈ IntermediateField.adjoin k (Set.range y), c ∈ V)
    (hV : IsMonomialValuation (IntermediateField.adjoin k (Set.range y)) V x) :
    IsAbhyankarValuation k V := sorry

omit [Fintype κ] in
/-- `Singularity/Valuation/MonomialGroundField.lean`: the residue field of a monomial valuation over `k(y)` that is trivial on `k(y)` is generated over `k` by the residues of the `y_i`. -/
theorem IsMonomialValuation.adjoin_residue_eq_top {y : κ → K} {x : ι → K}
    (hyV : ∀ c ∈ IntermediateField.adjoin k (Set.range y), c ∈ V)
    (hV : IsMonomialValuation (IntermediateField.adjoin k (Set.range y)) V x) :
    IntermediateField.adjoin k (Set.range fun i =>
      residue V ⟨y i, hyV _ (IntermediateField.subset_adjoin k _ (Set.mem_range_self i))⟩) = ⊤ :=
  sorry

end MonomialGroundField

section EtaleGenerator

open Polynomial IsLocalRing

/-- `Singularity/Valuation/EtaleRegular.lean`: let `P ∈ A[X]` be monic and let `Q` be a prime of `A[X]/(P)` with `P' ∉ Q`. If the localization of `A` at `p = Q ∩ A` is regular, then the localization of `A[X]/(P)` at `Q` is regular. -/
theorem isRegularLocalRing_localization_adjoinRoot {A : Type*} [CommRing A] [IsNoetherianRing A]
    {P : A[X]} (hP : P.Monic)
    (Q : Ideal (AdjoinRoot P)) [Q.IsPrime]
    (hQ : AdjoinRoot.mk P (derivative P) ∉ Q) (p : Ideal A) [p.IsPrime]
    (hp : Q.comap (algebraMap A (AdjoinRoot P)) = p)
    (hreg : IsRegularLocalRing (Localization.AtPrime p)) :
    IsRegularLocalRing (Localization.AtPrime Q) := sorry

/-- `Singularity/Valuation/EtaleGenerator.lean`: the Euler lemma. If `x` is integral over `A` with `L = F[x]` and `u ∈ L` is integral over `A`, then `P'(x) u ∈ A[x]`. -/
theorem aeval_derivative_minpoly_mul_mem_adjoin {A F L : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field F] [Field L] [Algebra A F] [IsFractionRing A F] [Algebra F L]
    [Algebra A L] [IsScalarTower A F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
    {x : L} (hx : Algebra.adjoin F {x} = ⊤) (hxA : IsIntegral A x) {u : L}
    (hu : IsIntegral A u) :
    aeval x (derivative (minpoly F x)) * u ∈ Algebra.adjoin A {x} := sorry

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The subring `T_R` of `K` of the elements `z` with `z c ∈ R` for some `c ∈ R` with `v(c) = 1`. -/
def centerSubring (V : ValuationSubring K) (R : Subring K) : Subring K where
  carrier := {z | ∃ a ∈ R, ∃ c ∈ R, V.valuation c = 1 ∧ z * c = a}
  mul_mem' := by
    rintro z w ⟨a, ha, c, hc, hc1, hz⟩ ⟨b, hb, d, hd, hd1, hw⟩
    refine ⟨a * b, R.mul_mem ha hb, c * d, R.mul_mem hc hd, by rw [map_mul, hc1, hd1, one_mul], ?_⟩
    rw [← hz, ← hw]
    ring
  one_mem' := ⟨1, R.one_mem, 1, R.one_mem, map_one _, one_mul 1⟩
  add_mem' := by
    rintro z w ⟨a, ha, c, hc, hc1, hz⟩ ⟨b, hb, d, hd, hd1, hw⟩
    refine ⟨a * d + b * c, R.add_mem (R.mul_mem ha hd) (R.mul_mem hb hc), c * d, R.mul_mem hc hd,
      by rw [map_mul, hc1, hd1, one_mul], ?_⟩
    rw [← hz, ← hw]
    ring
  zero_mem' := ⟨0, R.zero_mem, 1, R.one_mem, map_one _, zero_mul 1⟩
  neg_mem' := by
    rintro z ⟨a, ha, c, hc, hc1, hz⟩
    refine ⟨-a, R.neg_mem ha, c, hc, hc1, ?_⟩
    rw [← hz]
    ring

/-- An étale generator `z` of `K` over `K₀` for `V` (Volume 5, Definition 1.3.2 of the handbook). -/
structure IsEtaleGenerator (K₀ : IntermediateField k K) (V : ValuationSubring K) (z : K) :
    Prop where
  mem : z ∈ V
  adjoin_eq_top : IntermediateField.adjoin K₀ {z} = ⊤
  coeff_mem : ∀ i, ((minpoly K₀ z).coeff i : K) ∈ V
  valuation_derivative : V.valuation (aeval z (derivative (minpoly K₀ z))) = 1

/-- `Singularity/Valuation/EtaleGenerator.lean`: `V` is the localization of `V₀[z]` at the center of `V` (Lemma 1.3.3, part 1). -/
theorem IsEtaleGenerator.centerSubring_closure_eq {K₀ : IntermediateField k K}
    {V : ValuationSubring K} {z : K} (hz : IsEtaleGenerator K₀ V z) :
    centerSubring V (Subring.closure (insert z ((K₀ : Set K) ∩ V))) = V.toSubring := sorry

/-- `Singularity/Valuation/EtaleGenerator.lean`: local uniformization lifts along an étale generator (Theorem 1.3.4). -/
theorem hasLocalUniformization_of_etaleGenerator {K₀ : IntermediateField k K}
    {V : ValuationSubring K} {z : K} (hz : IsEtaleGenerator K₀ V z)
    (h : HasLocalUniformization k (V.comap (algebraMap K₀ K))) : HasLocalUniformization k V := sorry

/-- `Singularity/Valuation/EtaleGeneratorExistence.lean`: if the residue extension is separable of degree `[K : K₀]`, then there is an étale generator (Lemma 1.3.3, part 2, in the case of one extension). -/
theorem exists_isEtaleGenerator_of_finrank_residueField_eq {K₀ : IntermediateField k K}
    {Γ₀ Γ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ]
    (v₀ : Valuation K₀ Γ₀) (v : Valuation K Γ) [v₀.HasExtension v] [FiniteDimensional K₀ K]
    [Algebra.IsSeparable (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring)]
    (hf : Module.finrank (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring) =
      Module.finrank K₀ K) :
    Algebra.IsSeparable K₀ K ∧ ∃ z, IsEtaleGenerator K₀ v.valuationSubring z := sorry

/-- `Singularity/Valuation/MonomialFiniteExtension.lean`: if the residue extension is separable of degree `[K : K₀]`, then local uniformization lifts from `v₀` to `v` (Lemma 1.3.3 and Theorem 1.3.4, the case of one extension). -/
theorem hasLocalUniformization_of_finrank_residueField_eq {K₀ : IntermediateField k K}
    {Γ₀ Γ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ]
    (v₀ : Valuation K₀ Γ₀) (v : Valuation K Γ) [v₀.HasExtension v] [FiniteDimensional K₀ K]
    [Algebra.IsSeparable (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring)]
    (hf : Module.finrank (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring) =
      Module.finrank K₀ K)
    (h : HasLocalUniformization k v₀.valuationSubring) :
    HasLocalUniformization k v.valuationSubring := sorry

/-- `Singularity/Valuation/MonomialFiniteExtension.lean`: local uniformization over a subfield `K₀` with a monomial valuation over `k(y)`, in the case without ramification, defect and splitting (Theorem 2.2.1 in this case). -/
theorem hasLocalUniformization_of_monomial_of_finrank_residueField_eq
    {K₀ : IntermediateField k K}
    {Γ₀ Γ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ]
    (v₀ : Valuation K₀ Γ₀) (v : Valuation K Γ) [v₀.HasExtension v] [FiniteDimensional K₀ K]
    [Algebra.IsSeparable (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring)]
    (hf : Module.finrank (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring) =
      Module.finrank K₀ K)
    {κ ι : Type*} [Fintype κ] [Fintype ι] {y : κ → K₀} {x : ι → K₀}
    (hyV : ∀ c ∈ IntermediateField.adjoin k (Set.range y), c ∈ v₀.valuationSubring)
    (hV : IsMonomialValuation (IntermediateField.adjoin k (Set.range y)) v₀.valuationSubring x) :
    HasLocalUniformization k v.valuationSubring := sorry

/-- `Singularity/Valuation/MonomialFiniteExtension.lean`: the same for a monomial valuation of `K₀` over `k`. -/
theorem hasLocalUniformization_of_isMonomialValuation_of_finrank_residueField_eq
    {K₀ : IntermediateField k K}
    {Γ₀ Γ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ]
    (v₀ : Valuation K₀ Γ₀) (v : Valuation K Γ) [v₀.HasExtension v] [FiniteDimensional K₀ K]
    [Algebra.IsSeparable (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring)]
    (hf : Module.finrank (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring) =
      Module.finrank K₀ K)
    [Algebra k v₀.valuationSubring] [IsScalarTower k v₀.valuationSubring K₀]
    {ι : Type*} [Fintype ι] {x : ι → K₀} (hV : IsMonomialValuation k v₀.valuationSubring x) :
    HasLocalUniformization k v.valuationSubring := sorry

end EtaleGenerator

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

/-- `Singularity/Valuation/MacLaneDiscrete.lean`: a strictly decreasing family of values of `ν`, indexed by a nonempty totally ordered set without a largest element and bounded below by `c ≠ 0`, does not exist if the values of `ν` are discrete of rank 1. -/
theorem false_of_strictAnti_of_noMaxOrder {ν : Valuation K[X] Γ₀}
    (hdisc : ∀ c d : Γ₀, c ≠ 0 → (Set.Icc c d ∩ Set.range ν).Finite)
    {ι : Type*} [LinearOrder ι] [Nonempty ι] [NoMaxOrder ι] {s : ι → Γ₀} (hs : StrictAnti s)
    {c : Γ₀} (hc : c ≠ 0) (hcs : ∀ i, c ≤ s i) (hr : ∀ i, s i ∈ Set.range ν) : False := sorry

/-- `Singularity/Valuation/MacLaneDiscrete.lean`: the hypothesis of discreteness holds for a valuation with values in `ℤᵐ⁰`. -/
theorem finite_Icc_inter_range_int (ν : Valuation K[X] (WithZero (Multiplicative ℤ)))
    (c d : WithZero (Multiplicative ℤ)) (hc : c ≠ 0) : (Set.Icc c d ∩ Set.range ν).Finite :=
  sorry

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

section LimitKeyPolynomial

variable {F} {φ : K[X]} {γ : Γ₀}

namespace IsLimitKeyPolynomial

variable [Nonempty ι] [NoMaxOrder ι] (hφ : F.IsLimitKeyPolynomial φ)
include hφ

omit [NoMaxOrder ι] in
/-- `Singularity/Valuation/LimitKeyPolynomial.lean`: for a valuation `w` with the values of the limit augmentation `[μ_∞; φ, γ]`, the limit key polynomial `φ` `w`-divides `f` if and only if `μ_∞ (f %ₘ φ) < w f`. -/
theorem muDvd_iff_of_forall_eq {w : Valuation K[X] Γ₀}
    (hw : ∀ f, w f = F.limitAugmentedValuationFun φ γ f) {f : K[X]} :
    MuDvd w φ f ↔ F.stableValue (f %ₘ φ) < w f := sorry

/-- `Singularity/Valuation/LimitKeyPolynomial.lean`: a limit key polynomial is a key polynomial for each valuation with the values of the limit augmentation `[μ_∞; φ, γ]`. -/
theorem keyPolynomial_of_forall_eq {w : Valuation K[X] Γ₀}
    (hw : ∀ f, w f = F.limitAugmentedValuationFun φ γ f) : KeyPolynomial w φ := sorry

variable {ν : Valuation K[X] Γ₀}
  (hν : ∀ i f, ν f ≤ augmentedValuationFun μ (F.key i) (F.value i) f)
  (hlow : ∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = μ a)

include hν hlow in
/-- `Singularity/Valuation/LimitKeyPolynomial.lean`: a monic polynomial of the degree of `φ` with a value at least `ν(φ)` in additive notation is a limit key polynomial. -/
theorem of_map_le {ψ : K[X]} (hψ : ψ.Monic) (hdeg : ψ.natDegree = φ.natDegree)
    (hle : ν ψ ≤ ν φ) : F.IsLimitKeyPolynomial ψ := sorry

include hν hlow in
/-- `Singularity/Valuation/LimitKeyPolynomial.lean`: if `φ` has the largest `ν`-value among the monic polynomials of its degree, then `[μ_∞; φ, ν(φ)]` agrees with `ν` in degree at most `deg φ`. -/
theorem limitAugmentedValuationFun_eq_of_natDegree_le
    (hopt : ∀ ψ : K[X], ψ.Monic → ψ.natDegree = φ.natDegree → ν φ ≤ ν ψ) {f : K[X]}
    (hf : f.natDegree ≤ φ.natDegree) : F.limitAugmentedValuationFun φ (ν φ) f = ν f := sorry

omit [NoMaxOrder ι] in
/-- `Singularity/Valuation/LimitKeyPolynomial.lean`: the converse. If `[μ_∞; φ, ν(φ)]` agrees with `ν` in degree at most `deg φ`, then `φ` has the largest `ν`-value among the monic polynomials of its degree. -/
theorem map_le_of_forall_eq
    (h : ∀ f : K[X], f.natDegree ≤ φ.natDegree → F.limitAugmentedValuationFun φ (ν φ) f = ν f)
    {ψ : K[X]} (hψ : ψ.Monic) (hdeg : ψ.natDegree = φ.natDegree) : ν φ ≤ ν ψ := sorry

include hν hlow in
/-- `Singularity/Valuation/LimitKeyPolynomial.lean`: `[μ_∞; φ, ν(φ)]` agrees with `ν` in degree at most `deg φ` if and only if `φ` has the largest `ν`-value among the monic polynomials of its degree. -/
theorem forall_limitAugmentedValuationFun_eq_iff :
    (∀ f : K[X], f.natDegree ≤ φ.natDegree → F.limitAugmentedValuationFun φ (ν φ) f = ν f) ↔
      ∀ ψ : K[X], ψ.Monic → ψ.natDegree = φ.natDegree → ν φ ≤ ν ψ := sorry

include hν hlow in
/-- `Singularity/Valuation/LimitKeyPolynomial.lean`: the limit step of MacLane-Vaquié for a limit key polynomial of largest `ν`-value in its degree. -/
theorem limitStep
    (hopt : ∀ ψ : K[X], ψ.Monic → ψ.natDegree = φ.natDegree → ν φ ≤ ν ψ) :
    ∃ w : Valuation K[X] Γ₀, (∀ f, w f = F.limitAugmentedValuationFun φ (ν φ) f) ∧
      KeyPolynomial w φ ∧ (∀ i f, w f ≤ augmentedValuationFun μ (F.key i) (F.value i) f) ∧
      (∀ f, ν f ≤ w f) ∧ ∀ f : K[X], f.natDegree ≤ φ.natDegree → w f = ν f := sorry

end IsLimitKeyPolynomial

end LimitKeyPolynomial

section MacLaneDiscrete

variable {F} {ν : Valuation K[X] Γ₀}

variable (hlow : ∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = μ a)
  (hval : ∀ i, F.value i ∈ Set.range ν)
include hlow hval

/-- `Singularity/Valuation/MacLaneDiscrete.lean`: each value `μᵢ f` of a continuous family is a value of `ν`. -/
theorem val_mem_range (i : ι) (f : K[X]) :
    augmentedValuationFun μ (F.key i) (F.value i) f ∈ Set.range ν := sorry

variable [Nonempty ι] [NoMaxOrder ι]
  (hdisc : ∀ c d : Γ₀, c ≠ 0 → (Set.Icc c d ∩ Set.range ν).Finite)
include hdisc

omit hlow in
/-- `Singularity/Valuation/MacLaneDiscrete.lean`: in the discrete case of rank 1, the values `γᵢ` tend to `∞` in additive notation. -/
theorem eventually_value_lt {c : Γ₀} (hc : c ≠ 0) : ∃ i, ∀ j, i ≤ j → F.value j < c := sorry

/-- `Singularity/Valuation/MacLaneDiscrete.lean`: in the discrete case of rank 1, if `φ` is unstable and `γ ≤ μᵢ φ` for each `i`, then `γ = 0`. -/
theorem eq_zero_of_not_isStable {φ : K[X]} (hφ : ¬ F.IsStable φ) {γ : Γ₀}
    (hγ : ∀ i, γ ≤ augmentedValuationFun μ (F.key i) (F.value i) φ) : γ = 0 := sorry

variable (hν : ∀ i f, ν f ≤ augmentedValuationFun μ (F.key i) (F.value i) f)
include hν

/-- `Singularity/Valuation/MacLaneDiscrete.lean`: in the discrete case of rank 1, each `f` with `ν f ≠ 0` is stable. -/
theorem isStable_of_map_ne_zero {f : K[X]} (hf : ν f ≠ 0) : F.IsStable f := sorry

/-- `Singularity/Valuation/MacLaneDiscrete.lean`: in the discrete case of rank 1, `μᵢ f = ν f` for all large `i` if `ν f ≠ 0`. -/
theorem eventually_val_eq_of_map_ne_zero {f : K[X]} (hf : ν f ≠ 0) :
    ∃ i, ∀ j, i ≤ j → augmentedValuationFun μ (F.key j) (F.value j) f = ν f := sorry

section Support

variable (hsupp : ∀ f, ν f = 0 → f = 0)
include hsupp

/-- `Singularity/Valuation/MacLaneDiscrete.lean`: in the discrete case of rank 1 with support `0`, each polynomial is stable. -/
theorem isStable_of_supp_eq_bot (f : K[X]) : F.IsStable f := sorry

/-- `Singularity/Valuation/MacLaneDiscrete.lean`: in the discrete case of rank 1 with support `0`, the limit `μ_∞` is `ν`. -/
theorem stableValue_eq_of_supp_eq_bot (f : K[X]) : F.stableValue f = ν f := sorry

/-- `Singularity/Valuation/MacLaneDiscrete.lean`: in the discrete case of rank 1 with support `0`, there is no limit key polynomial. -/
theorem not_isLimitKeyPolynomial (φ : K[X]) : ¬ F.IsLimitKeyPolynomial φ := sorry

end Support

namespace IsLimitKeyPolynomial

variable {φ : K[X]} (hφ : F.IsLimitKeyPolynomial φ)
include hφ

/-- `Singularity/Valuation/MacLaneDiscrete.lean`: in the discrete case of rank 1, a limit key polynomial `φ` has `ν φ = 0`. -/
theorem map_eq_zero : ν φ = 0 := sorry

omit hν in
/-- `Singularity/Valuation/MacLaneDiscrete.lean`: in the discrete case of rank 1, the only admissible value of the limit augmentation is `γ = 0`. -/
theorem eq_zero_of_le {γ : Γ₀} (hγ : ∀ i, γ ≤ augmentedValuationFun μ (F.key i) (F.value i) φ) :
    γ = 0 := sorry

/-- `Singularity/Valuation/MacLaneDiscrete.lean`: in the discrete case of rank 1, `[μ_∞; φ, ν(φ)]` takes the values of `ν`. -/
theorem limitAugmentedValuationFun_eq (f : K[X]) : F.limitAugmentedValuationFun φ (ν φ) f = ν f :=
  sorry

/-- `Singularity/Valuation/MacLaneDiscrete.lean`: in the discrete case of rank 1, each limit augmentation `[μ_∞; φ, γ]` takes the values of `ν`. -/
theorem limitAugmentedValuationFun_eq_of_le {γ : Γ₀}
    (hγ : ∀ i, γ ≤ augmentedValuationFun μ (F.key i) (F.value i) φ) (f : K[X]) :
    F.limitAugmentedValuationFun φ γ f = ν f := sorry

end IsLimitKeyPolynomial

end MacLaneDiscrete

end ContinuousFamily

end LimitAugmentation

end KeyPolynomials

section MacLaneVaquie

universe uV

open Polynomial

variable {K : Type*} [Field K] {Γ₀ : Type uV} [LinearOrderedCommGroupWithZero Γ₀]

/-- `Singularity/Valuation/MacLaneVaquie.lean`: a step of MacLane-Vaquié towards `ν`, an ordinary augmentation or a limit augmentation of a continuous family below `ν` with a limit key polynomial of larger degree. -/
inductive MacLaneVaquieStep (ν μ μ' : Valuation K[X] Γ₀) : Prop
  | augment (φ : K[X]) (hle : ∀ f, ν f ≤ μ f) (hφ : φ.Monic) (hlt : ν φ < μ φ)
      (hlow : ∀ f : K[X], f.degree < φ.degree → ν f = μ f)
      (h : ∀ f, μ' f = augmentedValuationFun μ φ (ν φ) f)
  | limit (ι : Type uV) [LinearOrder ι] [Nonempty ι] [NoMaxOrder ι] (F : ContinuousFamily μ ι)
      (hν : ∀ i f, ν f ≤ augmentedValuationFun μ (F.key i) (F.value i) f)
      (hlow : ∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = μ a) (φ : K[X])
      (hφ : F.IsLimitKeyPolynomial φ) (hdeg : ∀ i, (F.key i).natDegree < φ.natDegree)
      (h : ∀ f, μ' f = F.limitAugmentedValuationFun φ (ν φ) f)

/-- `Singularity/Valuation/MacLaneVaquie.lean`: one round of the chain of MacLane-Vaquié in degree `d`. One step makes `w` agree with `ν` in degree at most `d`, or `ν` is the limit of a continuous family over `w`. -/
theorem exists_macLaneVaquieStep_or_forall_isStable {ν w : Valuation K[X] Γ₀}
    (hC : ∀ c, ν (C c) = w (C c)) (hle : ∀ f, ν f ≤ w f) (hne : w ≠ ν) :
    ∃ d : ℕ, (∀ f : K[X], f.natDegree < d → w f = ν f) ∧
      (∃ φ : K[X], φ.Monic ∧ φ.natDegree = d ∧ ν φ < w φ) ∧
      ((∃ w' : Valuation K[X] Γ₀, MacLaneVaquieStep ν w w' ∧
          ∀ f : K[X], f.natDegree ≤ d → w' f = ν f) ∨
        ∃ (ι : Type uV) (_ : LinearOrder ι) (_ : Nonempty ι) (_ : NoMaxOrder ι)
          (F : ContinuousFamily w ι),
          (∀ i f, ν f ≤ augmentedValuationFun w (F.key i) (F.value i) f) ∧
          (∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = w a) ∧
          ∀ f, F.IsStable f ∧ F.stableValue f = ν f) := sorry

/-- `Singularity/Valuation/MacLaneVaquie.lean`: the chain of MacLane-Vaquié. Either `ν` is the limit of a chain `wₙ` of steps with `wₙ = ν` in degree at most `n`, or `ν` is the limit of a continuous family over a valuation of the chain. -/
theorem exists_macLaneVaquie_seq_or_forall_isStable {ν w₀ : Valuation K[X] Γ₀}
    (hC : ∀ c, ν (C c) = w₀ (C c)) (hle : ∀ f, ν f ≤ w₀ f) :
    (∃ w : ℕ → Valuation K[X] Γ₀, w 0 = w₀ ∧
        (∀ n, Relation.ReflTransGen (MacLaneVaquieStep ν) (w n) (w (n + 1))) ∧
        ∀ n (f : K[X]), f.natDegree ≤ n → w n f = ν f) ∨
      ∃ μ : Valuation K[X] Γ₀, Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ μ ∧ μ ≠ ν ∧
        ∃ (ι : Type uV) (_ : LinearOrder ι) (_ : Nonempty ι) (_ : NoMaxOrder ι)
          (F : ContinuousFamily μ ι),
          (∀ i f, ν f ≤ augmentedValuationFun μ (F.key i) (F.value i) f) ∧
          (∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = μ a) ∧
          ∀ f, F.IsStable f ∧ F.stableValue f = ν f := sorry

/-- `Singularity/Valuation/MacLaneVaquie.lean`: part 4 of the theorem of MacLane-Vaquié for a valuation with nonzero support. Finitely many steps lead from `w₀` to `ν`. -/
theorem reflTransGen_macLaneVaquieStep_of_map_eq_zero {ν w₀ : Valuation K[X] Γ₀}
    (hC : ∀ c, ν (C c) = w₀ (C c)) (hle : ∀ f, ν f ≤ w₀ f) {F : K[X]} (hF : F ≠ 0)
    (hF0 : ν F = 0) : Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ ν := sorry

/-- `Singularity/Valuation/MacLaneVaquie.lean`: part 4 of the theorem of MacLane-Vaquié for a valuation with a monic `ν`-minimal polynomial of positive degree. Finitely many steps lead from `w₀` to `ν`. -/
theorem reflTransGen_macLaneVaquieStep_of_isMuMinimal {ν w₀ : Valuation K[X] Γ₀}
    (hC : ∀ c, ν (C c) = w₀ (C c)) (hle : ∀ f, ν f ≤ w₀ f) {φ : K[X]} (hm : φ.Monic)
    (hd : 0 < φ.natDegree) (hmin : IsMuMinimal ν φ) :
    Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ ν := sorry

/-- `Singularity/Valuation/MacLaneVaquie.lean`: the criterion for a finite chain of MacLane-Vaquié. For `w₀ ≠ ν`, finitely many steps lead from `w₀` to `ν` if and only if `ν` has a key polynomial. -/
theorem reflTransGen_macLaneVaquieStep_iff_exists_keyPolynomial {ν w₀ : Valuation K[X] Γ₀}
    (hC : ∀ c, ν (C c) = w₀ (C c)) (hle : ∀ f, ν f ≤ w₀ f) (hne : w₀ ≠ ν) :
    Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ ν ↔ ∃ φ, KeyPolynomial ν φ := sorry

/-- `Singularity/Valuation/MacLaneVaquie.lean`: part 4 of the theorem of MacLane-Vaquié with three cases. A finite chain reaches `ν`, or `ν` has no key polynomial and `ν` is the limit of an infinite chain or of a continuous family over a valuation of the chain. -/
theorem reflTransGen_macLaneVaquieStep_or_forall_not_keyPolynomial {ν w₀ : Valuation K[X] Γ₀}
    (hC : ∀ c, ν (C c) = w₀ (C c)) (hle : ∀ f, ν f ≤ w₀ f) :
    Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ ν ∨
      ((∀ φ, ¬ KeyPolynomial ν φ) ∧
        ((∃ w : ℕ → Valuation K[X] Γ₀, w 0 = w₀ ∧
            (∀ n, Relation.ReflTransGen (MacLaneVaquieStep ν) (w n) (w (n + 1))) ∧
            (∀ n (f : K[X]), f.natDegree ≤ n → w n f = ν f) ∧ ∀ n, w n ≠ ν) ∨
          ∃ μ : Valuation K[X] Γ₀, Relation.ReflTransGen (MacLaneVaquieStep ν) w₀ μ ∧ μ ≠ ν ∧
            ∃ (ι : Type uV) (_ : LinearOrder ι) (_ : Nonempty ι) (_ : NoMaxOrder ι)
              (F : ContinuousFamily μ ι),
              (∀ i f, ν f ≤ augmentedValuationFun μ (F.key i) (F.value i) f) ∧
              (∀ i (a : K[X]), a.degree < (F.key i).degree → ν a = μ a) ∧
              ∀ f, F.IsStable f ∧ F.stableValue f = ν f)) := sorry

end MacLaneVaquie

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

section LogJacobianCenterNonincrease

open MvPolynomial

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ S : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

omit [Fintype σ] in
/-- `Singularity/Invariant/LogJacobianCenterNonincrease.lean`: the core of Theorem 3.4.5 of
Volume 7, Section 3.4 of the handbook, for a general exponent `s`. -/
theorem logJacobianOrder_cleanPart_le_of_mem_center (hj : j ∈ S)
    (hgS : g ∈ Ideal.span (X '' (S : Set σ)) ^ p) (h : centerChart S j t g = X j ^ p * g')
    {r : σ →₀ ℕ} (hr : ∀ i, i ∉ Δ → r i = 0) {s ρ : ℕ}
    (hs : ∀ f ∈ logJacobianCenter Δ S g, ∃ q ∈ Ideal.span (X '' (S : Set σ)) ^ s,
      f = monomial r 1 * q)
    {q : MvPolynomial σ k} (hq : monomial r 1 * q ∈ logJacobianCenter Δ S g) (hqo : ord q = s)
    (hqc : ord (centerChart S j t q) ≤ ((s + ρ : ℕ) : ℕ∞)) :
    cleanPart p g' ≠ 0 ∧ logJacobianOrder (centerDivisor Δ S j t) (cleanPart p g') ≤ ρ := sorry

omit [DecidableEq σ] [DecidableEq k] [Fintype σ] in
/-- `Singularity/Invariant/LogJacobianCenterNonincrease.lean`: for a clean `g ≠ 0`, the order `ρ`
is finite. -/
theorem exists_logJacobianOrder_eq (hg : g ≠ 0) (hc : IsClean p g) :
    ∃ ρ : ℕ, logJacobianOrder Δ g = ρ := sorry

omit [Fintype σ] in
/-- `Singularity/Invariant/LogJacobianCenterNonincrease.lean`: Theorem 3.4.5 of Volume 7,
Section 3.4 of the handbook. Under (H1) and (H2), `g'_c ≠ 0` and `ρ(g'_c) ≤ ρ(g)`. -/
theorem logJacobianOrder_cleanPart_le_center (hj : j ∈ S)
    (hgS : g ∈ Ideal.span (X '' (S : Set σ)) ^ p) (h : centerChart S j t g = X j ^ p * g')
    {ρ : ℕ} (hρ : logJacobianOrder Δ g = ρ)
    (H1 : ∀ f ∈ logJacobian Δ g, ∃ q ∈ Ideal.span (X '' (S : Set σ)) ^ ρ,
      f = monomial (divisorExponent Δ g) 1 * q)
    (H2 : (∀ f ∈ logJacobianCenter Δ S g, ∃ q ∈ Ideal.span (X '' (S : Set σ)) ^ (ρ + 1),
        f = monomial (divisorExponent Δ g) 1 * q) ∨
      ∃ q, monomial (divisorExponent Δ g) 1 * q ∈ logJacobianCenter Δ S g ∧ ord q = ρ) :
    cleanPart p g' ≠ 0 ∧
      logJacobianOrder (centerDivisor Δ S j t) (cleanPart p g') ≤ logJacobianOrder Δ g := sorry

/-- `Singularity/Invariant/LogJacobianCenterNonincrease.lean`: Example 3.4.6, the data. -/
theorem centerExample_hyp :
    (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) ≠ 0 ∧
      IsClean 2 (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) ∧
      (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) ∈
        Ideal.span (X '' (({0, 1} : Finset (Fin 3)) : Set (Fin 3))) ^ 2 := sorry

/-- `Singularity/Invariant/LogJacobianCenterNonincrease.lean`: Example 3.4.6, the chart. -/
theorem centerExample_centerChart :
    centerChart {0, 1} 0 (0 : Fin 3 → ZMod 2) (X 1 ^ 2 * X 2 + X 1 ^ 3) =
      X 0 ^ 2 * (X 1 ^ 2 * X 2 + X 0 * X 1 ^ 3) := sorry

/-- `Singularity/Invariant/LogJacobianCenterNonincrease.lean`: Example 3.4.6, `ρ(g) = 2`. -/
theorem centerExample_logJacobianOrder :
    logJacobianOrder {2} (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) = 2 := sorry

/-- `Singularity/Invariant/LogJacobianCenterNonincrease.lean`: Example 3.4.6, (H1) holds. -/
theorem centerExample_H1 :
    ∀ f ∈ logJacobian {2} (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)),
      ∃ q ∈ Ideal.span (X '' (({0, 1} : Finset (Fin 3)) : Set (Fin 3))) ^ 2,
        f = monomial (divisorExponent {2} (X 1 ^ 2 * X 2 + X 1 ^ 3 :
          MvPolynomial (Fin 3) (ZMod 2))) 1 * q := sorry

/-- `Singularity/Invariant/LogJacobianCenterNonincrease.lean`: Example 3.4.6, (H2) fails. -/
theorem centerExample_not_H2 :
    ¬ ((∀ f ∈ logJacobianCenter {2} {0, 1}
          (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)),
        ∃ q ∈ Ideal.span (X '' (({0, 1} : Finset (Fin 3)) : Set (Fin 3))) ^ (2 + 1),
          f = monomial (divisorExponent {2} (X 1 ^ 2 * X 2 + X 1 ^ 3 :
            MvPolynomial (Fin 3) (ZMod 2))) 1 * q) ∨
      ∃ q, monomial (divisorExponent {2} (X 1 ^ 2 * X 2 + X 1 ^ 3 :
          MvPolynomial (Fin 3) (ZMod 2))) 1 * q ∈ logJacobianCenter {2} {0, 1}
            (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) ∧ ord q = (2 : ℕ)) := sorry

/-- `Singularity/Invariant/LogJacobianCenterNonincrease.lean`: Example 3.4.6, `ρ(g'_c) = 3`. -/
theorem centerExample_logJacobianOrder_cleanPart :
    logJacobianOrder (centerDivisor ({2} : Finset (Fin 3)) {0, 1} 0 (0 : Fin 3 → ZMod 2))
      (cleanPart 2 (X 1 ^ 2 * X 2 + X 0 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2))) = 3 := sorry

end LogJacobianCenterNonincrease

section LogJacobianEndCase

open MvPolynomial Finsupp

/-- `Singularity/Invariant/LogJacobianEndCase.lean`: `ρ = 0` if and only if `r_i G(0) ≠ 0` for some
`i ∈ Δ` or `∂_j G(0) ≠ 0` for some `j ∉ Δ`. -/
theorem logJacobianOrder_eq_zero_iff_exists {σ k : Type*} [CommSemiring k] (Δ : Finset σ)
    (g : MvPolynomial σ k) :
    logJacobianOrder Δ g = 0 ↔
      (∃ i ∈ Δ, (divisorExponent Δ g i : k) * constantCoeff (residualFactor Δ g) ≠ 0) ∨
        ∃ j ∉ Δ, constantCoeff (pderiv j (residualFactor Δ g)) ≠ 0 := sorry

variable {σ k : Type*} [Field k] (p : ℕ) [CharP k p] {Δ : Finset σ} {g : MvPolynomial σ k}

omit [CharP k p] in
/-- `Singularity/Invariant/LogJacobianEndCase.lean`: for a clean `g` with `G(0) ≠ 0`, `p ∤ r_i`
for some `i ∈ Δ`. -/
theorem exists_not_dvd_divisorExponent_of_constantCoeff_ne_zero (hc : IsClean p g)
    (h0 : constantCoeff (residualFactor Δ g) ≠ 0) : ∃ i ∈ Δ, ¬ p ∣ divisorExponent Δ g i := sorry

/-- `Singularity/Invariant/LogJacobianEndCase.lean`: the converse for type 0. -/
theorem logJacobianOrder_eq_zero_of_type_zero (h0 : constantCoeff (residualFactor Δ g) ≠ 0)
    {i : σ} (hi : i ∈ Δ) (hp : ¬ p ∣ divisorExponent Δ g i) : logJacobianOrder Δ g = 0 := sorry

omit [CharP k p] in
/-- `Singularity/Invariant/LogJacobianEndCase.lean`: the converse for type 1. -/
theorem logJacobianOrder_eq_zero_of_type_one {j : σ} (hj : j ∉ Δ)
    (h : constantCoeff (pderiv j (residualFactor Δ g)) ≠ 0) : logJacobianOrder Δ g = 0 := sorry

/-- `Singularity/Invariant/LogJacobianEndCase.lean`: type 0 of Proposition 3.5.1 of Volume 7,
Section 3.5 of the handbook. -/
theorem logJacobianOrder_eq_zero_type_zero (hc : IsClean p g) (hd : ord (residualFactor Δ g) = 0) :
    logJacobianOrder Δ g = 0 ∧ constantCoeff (residualFactor Δ g) ≠ 0 ∧
      ∃ i ∈ Δ, ¬ p ∣ divisorExponent Δ g i := sorry

omit [CharP k p] in
/-- `Singularity/Invariant/LogJacobianEndCase.lean`: if `ρ = 0` and `G(0) = 0`, then
`∂_j G(0) ≠ 0` for some `j ∉ Δ`. -/
theorem exists_constantCoeff_pderiv_ne_zero_of_constantCoeff_eq_zero
    (hρ : logJacobianOrder Δ g = 0) (h0 : constantCoeff (residualFactor Δ g) = 0) :
    ∃ j ∉ Δ, constantCoeff (pderiv j (residualFactor Δ g)) ≠ 0 := sorry

omit [CharP k p] in
/-- `Singularity/Invariant/LogJacobianEndCase.lean`: type 1 of Proposition 3.5.1 of Volume 7,
Section 3.5 of the handbook. -/
theorem exists_constantCoeff_pderiv_ne_zero (hρ : logJacobianOrder Δ g = 0)
    (hd : ord (residualFactor Δ g) = 1) :
    ∃ j ∉ Δ, constantCoeff (pderiv j (residualFactor Δ g)) ≠ 0 := sorry

omit [CharP k p] in
/-- `Singularity/Invariant/LogJacobianEndCase.lean`: if `ρ = 0`, then `ord G ≤ 1`. -/
theorem ord_residualFactor_le_one (hρ : logJacobianOrder Δ g = 0) :
    ord (residualFactor Δ g) ≤ 1 := sorry

/-- `Singularity/Invariant/LogJacobianEndCase.lean`: Proposition 3.5.1 of Volume 7, Section 3.5 of
the handbook. For a clean `g`, `ρ = 0` if and only if type 0 or type 1 holds. -/
theorem logJacobianOrder_eq_zero_iff (hc : IsClean p g) :
    logJacobianOrder Δ g = 0 ↔
      (constantCoeff (residualFactor Δ g) ≠ 0 ∧ ∃ i ∈ Δ, ¬ p ∣ divisorExponent Δ g i) ∨
        (constantCoeff (residualFactor Δ g) = 0 ∧
          ∃ j ∉ Δ, constantCoeff (pderiv j (residualFactor Δ g)) ≠ 0) := sorry

/-- `Singularity/Invariant/LogJacobianEndCase.lean`: Proposition 3.5.1 of Volume 7, Section 3.5 of
the handbook, with the order of `G`. -/
theorem logJacobianOrder_eq_zero_iff_ord (hc : IsClean p g) :
    logJacobianOrder Δ g = 0 ↔
      (ord (residualFactor Δ g) = 0 ∧ ∃ i ∈ Δ, ¬ p ∣ divisorExponent Δ g i) ∨
        (ord (residualFactor Δ g) = 1 ∧
          ∃ j ∉ Δ, constantCoeff (pderiv j (residualFactor Δ g)) ≠ 0) := sorry

end LogJacobianEndCase

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
section Tschirnhausen

open MvPolynomial

/-- `Singularity/Invariant/Residual.lean`: the coordinate change `z ↦ z + h(x)`. -/
noncomputable def zShift {σ k : Type*} [CommSemiring k] (h : MvPolynomial σ k) :
    MvPolynomial (Option σ) k →ₐ[k] MvPolynomial (Option σ) k :=
  aeval fun o => Option.elim o (X none + rename Option.some h) fun i => X (Option.some i)

/-- `Singularity/Invariant/Tschirnhausen.lean`: the polynomial `z^m + ∑_{i < m} a_i(x) z^i`. -/
noncomputable def zMonic {σ R : Type*} [CommRing R] (m : ℕ) (a : ℕ → MvPolynomial σ R) :
    MvPolynomial (Option σ) R :=
  X none ^ m + ∑ i ∈ Finset.range m, rename Option.some (a i) * X none ^ i

/-- `Singularity/Invariant/Tschirnhausen.lean`: the order of `zMonic` at the origin. -/
theorem le_ord_zMonic_iff {σ R : Type*} [CommRing R] {m : ℕ} {a : ℕ → MvPolynomial σ R} :
    (m : ℕ∞) ≤ ord (zMonic m a) ↔ ∀ i < m, ((m - i : ℕ) : ℕ∞) ≤ ord (a i) := sorry

/-- `Singularity/Invariant/Tschirnhausen.lean`: the Tschirnhausen transformation. -/
theorem tschirnhausen_transformation {σ R : Type*} [CommRing R] {m : ℕ} (hm : IsUnit (m : R))
    (a : ℕ → MvPolynomial σ R) :
    ∃ a' : ℕ → MvPolynomial σ R,
      zShift (-(C (↑hm.unit⁻¹ : R) * a (m - 1))) (zMonic m a) = zMonic m a' ∧ a' (m - 1) = 0 :=
  sorry

/-- `Singularity/Invariant/Tschirnhausen.lean`: the points of order `m` lie in `z = 0`. -/
theorem eq_zero_of_le_ord_translate {σ R : Type*} [CommRing R] {m : ℕ} (hm : IsUnit (m : R))
    {a : ℕ → MvPolynomial σ R} (ha : a (m - 1) = 0) (b : Option σ → R)
    (h : (m : ℕ∞) ≤ ord (aeval (fun o => X o + C (b o)) (zMonic m a))) : b none = 0 := sorry

/-- `Singularity/Invariant/Tschirnhausen.lean`: the locus of order `m`. -/
theorem le_ord_translate_zMonic_iff {σ R : Type*} [CommRing R] {m : ℕ} (hm : IsUnit (m : R))
    {a : ℕ → MvPolynomial σ R} (ha : a (m - 1) = 0) (b : Option σ → R) :
    (m : ℕ∞) ≤ ord (aeval (fun o => X o + C (b o)) (zMonic m a)) ↔
      b none = 0 ∧ ∀ i < m, ((m - i : ℕ) : ℕ∞) ≤
        ord (aeval (fun l => X l + C (b (some l))) (a i)) := sorry

/-- `Singularity/Invariant/Tschirnhausen.lean`: the lemma of Tschirnhausen for a point blowup. -/
theorem tschirnhausen_pointChart {σ k : Type*} [Field k] [DecidableEq σ] {m : ℕ}
    (hm : (m : k) ≠ 0) {a : ℕ → MvPolynomial σ k}
    (ha : a (m - 1) = 0) (hord : ∀ i < m, ((m - i : ℕ) : ℕ∞) ≤ ord (a i)) {c : Option σ}
    {t : Option σ → k} {f' : MvPolynomial (Option σ) k}
    (h : pointChart c t (zMonic m a) = X c ^ m * f') (hf' : (m : ℕ∞) ≤ ord f') :
    ∃ j : σ, c = some j ∧ t none = 0 ∧ ∃ a' : ℕ → MvPolynomial σ k, f' = zMonic m a' ∧
      a' (m - 1) = 0 ∧ (∀ i < m, ((m - i : ℕ) : ℕ∞) ≤ ord (a' i)) ∧
      ∀ i < m, pointChart j (fun l => t (some l)) (a i) = X j ^ (m - i) * a' i := sorry

/-- `Singularity/Invariant/Tschirnhausen.lean`: in characteristic `2` the points of order `m` need not lie in `z = 0`. -/
theorem not_tschirnhausen_charTwo (K : Type*) [Field K] [CharP K 2] :
    ¬ ∀ (m : ℕ) (a : ℕ → MvPolynomial (Fin 3) K) (b : Option (Fin 3) → K), a (m - 1) = 0 →
      (∀ i < m, ((m - i : ℕ) : ℕ∞) ≤ ord (a i)) →
      (m : ℕ∞) ≤ ord (aeval (fun o => X o + C (b o)) (zMonic m a)) → b none = 0 := sorry

end Tschirnhausen

section Alteration

open AlgebraicGeometry CategoryTheory

/-- `Singularity/Alteration/Basic.lean`: an alteration of an integral scheme. -/
structure IsAlteration {X X' : Scheme.{u}} (f : X' ⟶ X) : Prop where
  integral_source : IsIntegral X'
  integral_target : IsIntegral X
  proper : IsProper f
  dominant : IsDominant f
  finite_over : ∃ U : X.Opens, (U : Set X).Nonempty ∧ IsFinite (f ∣_ U)

/-- `Singularity/Alteration/Basic.lean`: the fibre over the generic point. -/
theorem IsAlteration.eq_genericPoint {X X' : Scheme.{u}} [IsIntegral X] [IsIntegral X']
    {f : X' ⟶ X} (hf : IsAlteration f) {x : X'} (hx : f x = genericPoint X) :
    x = genericPoint X' := sorry

/-- `Singularity/Alteration/Basic.lean`: the identity is an alteration. -/
protected theorem IsAlteration.id (X : Scheme.{u}) [IsIntegral X] : IsAlteration (𝟙 X) := sorry

/-- `Singularity/Alteration/Basic.lean`: a composite of two alterations is an alteration. -/
protected theorem IsAlteration.comp {X X' X'' : Scheme.{u}} {g : X'' ⟶ X'} {f : X' ⟶ X}
    (hg : IsAlteration g) (hf : IsAlteration f) : IsAlteration (g ≫ f) := sorry

/-- `Singularity/Alteration/Basic.lean`: an isomorphism over a nonempty open set is an alteration. -/
theorem IsAlteration.of_isIso_restrict {X X' : Scheme.{u}} [IsIntegral X] [IsIntegral X']
    (f : X' ⟶ X) [IsProper f] (U : X.Opens) (hU : (U : Set X).Nonempty) [IsIso (f ∣_ U)] :
    IsAlteration f := sorry

/-- `Singularity/Alteration/Basic.lean`: a resolution of an integral scheme has an integral source. -/
theorem IsResolution.isIntegral {X Y : Scheme.{u}} [IsIntegral X] {π : Y ⟶ X} (h : IsResolution π) :
    IsIntegral Y := sorry

/-- `Singularity/Alteration/Basic.lean`: a resolution of an integral scheme is an alteration. -/
theorem IsResolution.isAlteration {X Y : Scheme.{u}} [IsIntegral X] {π : Y ⟶ X}
    (h : IsResolution π) : IsAlteration π := sorry

/-- `Singularity/Alteration/Statement.lean`: regular alterations in dimension at most `n`. -/
def RegularAlterationInDim (p n : ℕ) : Prop :=
  ∀ (k : Type u) [Field k] [CharP k p] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsVariety X f]
    [IsIntegral X], topologicalKrullDim X ≤ n →
      ∃ (X' : Scheme.{u}) (φ : X' ⟶ X), IsAlteration φ ∧ IsRegularScheme X'

/-- `Singularity/Alteration/Statement.lean`: the theorem of de Jong, as a proposition. -/
def deJongAlteration : Prop :=
  ∀ (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsVariety X f] [IsIntegral X]
    (Z : Set X), IsClosed Z → Z ≠ Set.univ →
      ∃ (X₁ Xbar : Scheme.{u}) (φ : X₁ ⟶ X) (j : X₁ ⟶ Xbar) (g : Xbar ⟶ Spec (.of k))
        (D : Xbar.IdealSheafData),
        IsAlteration φ ∧ IsOpenImmersion j ∧ j ≫ g = φ ≫ f ∧ IsIntegral Xbar ∧ IsProper g ∧
          IsRegularScheme Xbar ∧
          (D.support : Set Xbar) = j '' (φ ⁻¹' Z) ∪ (Set.range j)ᶜ ∧ IsSncDivisor D

/-- `Singularity/Alteration/Statement.lean`: de Jong implies regular alterations in each dimension. -/
theorem regularAlterationInDim_of_deJongAlteration (h : deJongAlteration.{u}) (p n : ℕ) :
    RegularAlterationInDim.{u} p n := sorry

/-- `Singularity/Alteration/Statement.lean`: resolution implies regular alterations. -/
theorem regularAlterationInDim_of_resolutionInDim {p n : ℕ} (h : ResolutionInDim.{u} p n) :
    RegularAlterationInDim.{u} p n := sorry

end Alteration

section DegreePSteps

open Polynomial IntermediateField Module

section PowMem

variable {K : Type*} [Field K]

theorem valuationSubring_pow_mem_iff (V : ValuationSubring K) {b : K} {n : ℕ} (hn : n ≠ 0) :
    b ^ n ∈ V ↔ b ∈ V := sorry

end PowMem

section Kummer

variable {K : Type*} [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]

theorem irreducible_X_pow_sub_C_iff (a : K) :
    Irreducible (X ^ p - C a : K[X]) ↔ ∀ b : K, b ^ p ≠ a := sorry

end Kummer

section Extension

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (p : ℕ) [ExpChar K p]

include p in
theorem existsUnique_valuationSubring_comap_eq [IsPurelyInseparable K L] (V : ValuationSubring K) :
    ∃! W : ValuationSubring L, W.comap (algebraMap K L) = V := sorry

end Extension

section ArtinSchreier

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (p : ℕ) [hp : Fact p.Prime] [CharP K p]

theorem exists_artinSchreier_generator [FiniteDimensional K L] [IsGalois K L]
    (hd : finrank K L = p) :
    ∃ θ : L, θ ^ p - θ ∈ (⊥ : IntermediateField K L) ∧ K⟮θ⟯ = ⊤ ∧
      ∃ σ : L ≃ₐ[K] L, σ θ = θ + 1 := sorry

theorem artinSchreier_integral {R : Type*} [CommRing R] (θ a g : R) (h : θ ^ p - θ = a) :
    (g * θ) ^ p - g ^ (p - 1) * (g * θ) - g ^ p * a = 0 := sorry

end ArtinSchreier

section TowerMain

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (p : ℕ) [hp : Fact p.Prime] [CharP K p]

theorem exists_purelyInseparable_tower [FiniteDimensional K L] [IsPurelyInseparable K L]
    (V : ValuationSubring K) :
    ∃ W : ValuationSubring L, W.comap (algebraMap K L) = V ∧
      (∀ W' : ValuationSubring L, W'.comap (algebraMap K L) = V → W' = W) ∧
      ∃ (r : ℕ) (E : ℕ → IntermediateField K L) (θ : ℕ → L), E 0 = ⊥ ∧ E r = ⊤ ∧
        finrank K L = p ^ r ∧ ∀ i < r, E (i + 1) = E i ⊔ K⟮θ i⟯ ∧ θ i ∉ E i ∧ θ i ^ p ∈ E i ∧
          (E i).relfinrank (E (i + 1)) = p ∧ θ i ∈ W := sorry

end TowerMain

section Model

variable (p : ℕ) [hp : Fact p.Prime] {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem exists_inseparableStep_model (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K]
    (hV : HasLocalUniformization k V) {c : K} (hc : ∀ b : K, b ^ p ≠ c) :
    ∃ x : K, (x = c ∨ x = c⁻¹) ∧ x ∈ V ∧ (∀ b : K, b ^ p ≠ x) ∧
      Irreducible (X ^ p - C x : K[X]) ∧ HasRegularCenter k V {x} := sorry

theorem mem_valuationSubring_of_pow_eq {L : Type*} [Field L] [Algebra K L] (V : ValuationSubring K)
    (W : ValuationSubring L) (hW : W.comap (algebraMap K L) = V) {x : K} (hx : x ∈ V) {θ : L}
    (hθ : θ ^ p = algebraMap K L x) : θ ∈ W := sorry

end Model

section Reduced

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R] [IsDomain R] [CharP R p]

variable [IsIntegrallyClosed R]

theorem X_pow_add_C_tfae (g : R) :
    List.TFAE [IsReduced (R[X] ⧸ Ideal.span {X ^ p + C g}),
      IsDomain (R[X] ⧸ Ideal.span {X ^ p + C g}),
      Irreducible (X ^ p + C g : R[X]), ∀ a : R, a ^ p ≠ g] := sorry

theorem X_pow_add_C_tfae_threefold (k : Type*) [Field k] [CharP k p] (g : MvPolynomial (Fin 3) k) :
    List.TFAE [IsReduced ((MvPolynomial (Fin 3) k)[X] ⧸ Ideal.span {X ^ p + C g}),
      IsDomain ((MvPolynomial (Fin 3) k)[X] ⧸ Ideal.span {X ^ p + C g}),
      Irreducible (X ^ p + C g : (MvPolynomial (Fin 3) k)[X]),
      ∀ a : MvPolynomial (Fin 3) k, a ^ p ≠ g] := sorry

end Reduced

end DegreePSteps

section DegreePTowers

universe v

open IntermediateField Module

/-- `Singularity/Valuation/DegreePTowers.lean`: local uniformization is invariant under an isomorphism of `k`-algebras. -/
theorem HasLocalUniformization.of_algEquiv {k K K' : Type*} [Field k] [Field K] [Field K']
    [Algebra k K] [Algebra k K'] (e : K ≃ₐ[k] K') {V' : ValuationSubring K'}
    (h : HasLocalUniformization k (V'.comap (e : K →+* K'))) : HasLocalUniformization k V' :=
  sorry

/-- The explicit hypothesis for one purely inseparable step of degree `p`. The library does not prove it. -/
def LocalUniformizationInseparableStep (p n : ℕ) (k : Type v) [Field k] [CharP k p] : Prop :=
  ∀ (E E' : Type u) [Field E] [Field E'] [Algebra k E] [Algebra k E'] [Algebra E E']
    [IsScalarTower k E E'], Algebra.trdeg k E = n → finrank E E' = p → IsPurelyInseparable E E' →
      ∀ W : ValuationSubring E', HasLocalUniformization k (W.comap (algebraMap E E')) →
        HasLocalUniformization k W

/-- The explicit hypothesis for one Galois step of degree `p`. The library does not prove it. -/
def LocalUniformizationGaloisStep (p n : ℕ) (k : Type v) [Field k] [CharP k p] : Prop :=
  ∀ (E E' : Type u) [Field E] [Field E'] [Algebra k E] [Algebra k E'] [Algebra E E']
    [IsScalarTower k E E'], Algebra.trdeg k E = n → finrank E E' = p → IsGalois E E' →
      ∀ W : ValuationSubring E', HasLocalUniformization k (W.comap (algebraMap E E')) →
        HasLocalUniformization k W

/-- `Singularity/Valuation/DegreePTowers.lean`: a Galois extension of degree `p ^ (r + 1)` has a Galois subextension of degree `p`. -/
theorem exists_isGalois_finrank_eq_prime (p : ℕ) [hp : Fact p.Prime] {K L : Type u} [Field K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] {r : ℕ}
    (hd : finrank K L = p ^ (r + 1)) :
    ∃ M : IntermediateField K L, IsGalois K M ∧ finrank K M = p ∧ finrank M L = p ^ r := sorry

/-- `Singularity/Valuation/DegreePTowers.lean`: Proposition 2.1.4 of Volume 6, a tower of Artin-Schreier steps. -/
theorem exists_artinSchreier_tower (p : ℕ) [hp : Fact p.Prime] {K L : Type u} [Field K]
    [Field L] [Algebra K L] [CharP K p] [FiniteDimensional K L] [IsGalois K L] {r : ℕ}
    (hd : finrank K L = p ^ r) :
    ∃ (E : ℕ → IntermediateField K L) (θ : ℕ → L), E 0 = ⊥ ∧ E r = ⊤ ∧
      ∀ i < r, E (i + 1) = E i ⊔ K⟮θ i⟯ ∧ θ i ∉ E i ∧ θ i ^ p - θ i ∈ E i ∧
        (E i).relfinrank (E (i + 1)) = p := sorry

/-- `Singularity/Valuation/DegreePTowers.lean`: Step 3 of the reduction of Cossart-Piltant, with the step of degree `p` as a hypothesis. -/
theorem hasLocalUniformization_of_isPurelyInseparable (p n : ℕ) [hp : Fact p.Prime] {k : Type v}
    [Field k] [CharP k p]
    (hstep : LocalUniformizationInseparableStep.{u} p n k) {K L : Type u} [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L]
    [IsPurelyInseparable K L] (hK : Algebra.trdeg k K = n) (W : ValuationSubring L)
    (hW : HasLocalUniformization k (W.comap (algebraMap K L))) : HasLocalUniformization k W :=
  sorry

/-- `Singularity/Valuation/DegreePTowers.lean`: Step 3 of the reduction of Cossart-Piltant, from the separable closure. -/
theorem hasLocalUniformization_of_separableClosure (p n : ℕ) [hp : Fact p.Prime] {k : Type v}
    [Field k] [CharP k p]
    (hstep : LocalUniformizationInseparableStep.{u} p n k) {F K : Type u} [Field F] [Field K]
    [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K]
    (hF : Algebra.trdeg k F = n) (V : ValuationSubring K)
    (hV : HasLocalUniformization k (V.comap (algebraMap (separableClosure F K) K))) :
    HasLocalUniformization k V := sorry

/-- `Singularity/Valuation/DegreePTowers.lean`: the last part of Step 4 of the reduction of Cossart-Piltant, with the Galois step of degree `p` as a hypothesis. -/
theorem hasLocalUniformization_of_isGalois (p n : ℕ) [hp : Fact p.Prime] {k : Type v} [Field k]
    [CharP k p]
    (hstep : LocalUniformizationGaloisStep.{u} p n k) {K L : Type u} [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L]
    [IsGalois K L] {r : ℕ} (hd : finrank K L = p ^ r) (hK : Algebra.trdeg k K = n)
    (W : ValuationSubring L) (hW : HasLocalUniformization k (W.comap (algebraMap K L))) :
    HasLocalUniformization k W := sorry

end DegreePTowers

section InertiaField

open IntermediateField IsLocalRing Module

/-- `Singularity/Valuation/InertiaField.lean`: the residue degree is at most the degree. -/
theorem finiteDimensional_residueField_and_finrank_le {E E' : Type*} [Field E] [Field E']
    [Algebra E E'] {Γ₀ Γ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ] (v₀ : Valuation E Γ₀) (v : Valuation E' Γ)
    [v₀.HasExtension v] [FiniteDimensional E E'] :
    FiniteDimensional (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring) ∧
      finrank (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring) ≤
        finrank E E' := sorry

/-- For fields `K ⊆ M ⊆ L` and a valuation `w` of `L`, the restriction of `w` to `M` extends the restriction of `w` to `K`. -/
instance hasExtension_comap_comap {K M L : Type*} [Field K] [Field M] [Field L] [Algebra K M]
    [Algebra M L] [Algebra K L] [IsScalarTower K M L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ) :
    (w.comap (algebraMap K L)).HasExtension (w.comap (algebraMap M L)) :=
  ⟨fun r s => by simp only [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply]⟩

/-- `Singularity/Valuation/InertiaField.lean`: the lifting theorem for an extension `E'/E` that is given as an algebra. -/
theorem hasLocalUniformization_of_finrank_residueField_eq_of_algebra {k E E' : Type*} [Field k]
    [Field E] [Field E'] [Algebra k E] [Algebra k E'] [Algebra E E'] [IsScalarTower k E E']
    {Γ₀ Γ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ]
    (v₀ : Valuation E Γ₀) (v : Valuation E' Γ) [v₀.HasExtension v] [FiniteDimensional E E']
    [Algebra.IsSeparable (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring)]
    (hf : finrank (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring) =
      finrank E E')
    (h : HasLocalUniformization k v₀.valuationSubring) :
    HasLocalUniformization k v.valuationSubring := sorry

/-- The inertia group of a valuation subring `W` of `L` in the group of `K`-automorphisms of `L`. -/
def inertiaGroup (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (W : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) where
  carrier := {σ | (∀ x, σ x ∈ W ↔ x ∈ W) ∧ ∀ x ∈ W, W.valuation (σ x - x) < 1}
  mul_mem' {σ τ} hσ hτ := by
    refine ⟨fun x => (hσ.1 _).trans (hτ.1 x), fun x hx => ?_⟩
    have : (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x) := by
      rw [AlgEquiv.mul_apply]
      ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans_lt (max_lt (hσ.2 _ ((hτ.1 x).2 hx)) (hτ.2 x hx))
  one_mem' := ⟨fun x => Iff.rfl, fun x _ => by simp⟩
  inv_mem' {σ} hσ := by
    have hss : ∀ x, σ (σ⁻¹ x) = x := fun x => by
      rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    have h1 : ∀ x, σ⁻¹ x ∈ W ↔ x ∈ W := fun x => by
      rw [← hσ.1 (σ⁻¹ x), hss]
    refine ⟨h1, fun x hx => ?_⟩
    have := hσ.2 (σ⁻¹ x) ((h1 x).2 hx)
    rwa [hss, ← Valuation.map_neg, neg_sub] at this

/-- The inertia field of a valuation subring `W` of `L` over `K`. -/
def inertiaField (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (W : ValuationSubring L) : IntermediateField K L :=
  fixedField (inertiaGroup K W)

/-- `Singularity/Valuation/InertiaField.lean`: the residue extension of the inertia field over a field that contains the decomposition field is separable of degree `[K^T : K]`. -/
theorem isSeparable_and_finrank_residueField_inertiaField {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (W : ValuationSubring L)
    (hW : ∀ σ : L ≃ₐ[K] L, ∀ x ∈ W, σ x ∈ W) :
    Algebra.IsSeparable (ResidueField (W.valuation.comap (algebraMap K L)).valuationSubring)
        (ResidueField (W.valuation.comap (algebraMap (inertiaField K W) L)).valuationSubring) ∧
      finrank (ResidueField (W.valuation.comap (algebraMap K L)).valuationSubring)
        (ResidueField (W.valuation.comap (algebraMap (inertiaField K W) L)).valuationSubring) =
        finrank K (inertiaField K W) := sorry

/-- `Singularity/Valuation/InertiaField.lean`: local uniformization goes up to the inertia field over a field that contains the decomposition field (part of Step 4 of the reduction of Cossart-Piltant). -/
theorem hasLocalUniformization_inertiaField {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L]
    [IsGalois K L] (W : ValuationSubring L) (hW : ∀ σ : L ≃ₐ[K] L, ∀ x ∈ W, σ x ∈ W)
    (h : HasLocalUniformization k (W.comap (algebraMap K L))) :
    HasLocalUniformization k (W.comap (algebraMap (inertiaField K W) L)) := sorry

/-- The `k`-algebra structure of an intermediate field `M` of `L/K` is compatible with `L`. -/
theorem isScalarTower_intermediateField {k : Type*} [Field k] {K L : Type*} [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (M : IntermediateField K L) :
    IsScalarTower k M L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

attribute [local instance] isScalarTower_intermediateField

/-- `Singularity/Valuation/InertiaField.lean`: local uniformization goes up from the decomposition field to the inertia field (part of Step 4 of the reduction of Cossart-Piltant). -/
theorem hasLocalUniformization_inertiaField_decompositionField {k K L : Type*} [Field k]
    [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L] (W : ValuationSubring L)
    (h : HasLocalUniformization k
      (W.comap (algebraMap (fixedField (W.decompositionSubgroup K)) L))) :
    HasLocalUniformization k
      (W.comap (algebraMap (inertiaField (fixedField (W.decompositionSubgroup K)) W) L)) :=
  sorry

end InertiaField

section CossartPiltantOmega

open MvPolynomial Finsupp

section Def

variable {σ k : Type*} [CommSemiring k]

open Classical in
/-- `Singularity/Invariant/CossartPiltantOmega.lean`: the invariant `ω` of Cossart and Piltant,
Volume 6, Definition 3.2.5 of the handbook. -/
noncomputable def cpOmega (Δ : Finset σ) (g : MvPolynomial σ k) : ℕ∞ :=
  if ∃ j ∉ Δ, pderiv j (homogeneousComponent (ord g).toNat g) ≠ 0 then
    ord (residualFactor Δ g) - 1
  else ord (residualFactor Δ g)

/-- `Singularity/Invariant/CossartPiltantOmega.lean`: the first case of Definition 3.2.5. -/
theorem cpOmega_of_exists {Δ : Finset σ} {g : MvPolynomial σ k}
    (h : ∃ j ∉ Δ, pderiv j (homogeneousComponent (ord g).toNat g) ≠ 0) :
    cpOmega Δ g = ord (residualFactor Δ g) - 1 := sorry

/-- `Singularity/Invariant/CossartPiltantOmega.lean`: the second case of Definition 3.2.5. -/
theorem cpOmega_of_forall {Δ : Finset σ} {g : MvPolynomial σ k}
    (h : ∀ j ∉ Δ, pderiv j (homogeneousComponent (ord g).toNat g) = 0) :
    cpOmega Δ g = ord (residualFactor Δ g) := sorry

end Def

section Main

variable {σ k : Type*} [Field k] (p : ℕ) [CharP k p] {Δ : Finset σ} {g : MvPolynomial σ k}

/-- `Singularity/Invariant/CossartPiltantOmega.lean`: Proposition 3.6.1 of Volume 7, Section 3.6
of the handbook, `ω = ρ` for a clean `g ≠ 0`. -/
theorem cpOmega_eq_logJacobianOrder (hg : g ≠ 0) (hc : IsClean p g) :
    cpOmega Δ g = logJacobianOrder Δ g := sorry

end Main

section PointBlowup

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- `Singularity/Invariant/CossartPiltantOmega.lean`: Corollary 3.6.2 of Volume 7, Section 3.6 of
the handbook, `ω` does not go up under a point blowup. -/
theorem cpOmega_cleanPart_le (hg : g ≠ 0) (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g)
    (h : pointChart j t g = X j ^ p * g') :
    cpOmega (blowupDivisor Δ j t) (cleanPart p g') ≤ cpOmega Δ g := sorry

end PointBlowup

section CenterBlowup

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] (p : ℕ) [CharP k p]
  {Δ S : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- `Singularity/Invariant/CossartPiltantOmega.lean`: Corollary 3.6.3 of Volume 7, Section 3.6 of
the handbook, `ω` does not go up under the blowup of a regular center with (H1) and (H2). -/
theorem cpOmega_cleanPart_le_center (hc : IsClean p g) (hj : j ∈ S)
    (hgS : g ∈ Ideal.span (X '' (S : Set σ)) ^ p) (h : centerChart S j t g = X j ^ p * g')
    {ρ : ℕ} (hρ : logJacobianOrder Δ g = ρ)
    (H1 : ∀ f ∈ logJacobian Δ g, ∃ q ∈ Ideal.span (X '' (S : Set σ)) ^ ρ,
      f = monomial (divisorExponent Δ g) 1 * q)
    (H2 : (∀ f ∈ logJacobianCenter Δ S g, ∃ q ∈ Ideal.span (X '' (S : Set σ)) ^ (ρ + 1),
        f = monomial (divisorExponent Δ g) 1 * q) ∨
      ∃ q, monomial (divisorExponent Δ g) 1 * q ∈ logJacobianCenter Δ S g ∧ ord q = ρ) :
    cpOmega (centerDivisor Δ S j t) (cleanPart p g') ≤ cpOmega Δ g := sorry

end CenterBlowup

/-- `Singularity/Invariant/CossartPiltantOmega.lean`: Example 3.6.4, `ω(g) = 2`. -/
theorem centerExample_cpOmega :
    cpOmega {2} (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) = 2 := sorry

/-- `Singularity/Invariant/CossartPiltantOmega.lean`: Example 3.6.4, `ω(g'_c) = 3`. -/
theorem centerExample_cpOmega_cleanPart :
    cpOmega (centerDivisor ({2} : Finset (Fin 3)) {0, 1} 0 (0 : Fin 3 → ZMod 2))
      (cleanPart 2 (X 1 ^ 2 * X 2 + X 0 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2))) = 3 := sorry

/-- `Singularity/Invariant/CossartPiltantOmega.lean`: Example 3.6.4, `ω` goes up from `2` to `3`. -/
theorem centerExample_cpOmega_lt :
    cpOmega {2} (X 1 ^ 2 * X 2 + X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) <
      cpOmega (centerDivisor ({2} : Finset (Fin 3)) {0, 1} 0 (0 : Fin 3 → ZMod 2))
        (cleanPart 2 (X 1 ^ 2 * X 2 + X 0 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2))) := sorry

end CossartPiltantOmega

section LogJacobianNearPoint

open MvPolynomial Finsupp

section Directrix

variable {σ k : Type*} [Field k]

/-- `Singularity/Invariant/Directrix.lean`: the substitution `x_i ↦ x_i + v_i s`. -/
noncomputable def translate (v : σ → k) : MvPolynomial σ k →ₐ[k] MvPolynomial (Option σ) k :=
  aeval fun i => X (some i) + C (v i) * X none

/-- `Singularity/Invariant/Directrix.lean`: the translation by `0`. -/
theorem translate_zero : translate (0 : σ → k) = rename some := by
  refine algHom_ext fun i => ?_
  simp [translate]

/-- `Singularity/Invariant/Directrix.lean`: the substitution `s ↦ c s` after a translation. -/
theorem scaleVar_comp_translate (c : k) (v : σ → k) :
    (aeval fun o : Option σ => Option.elim o (C c * X none) fun i => X (some i)).comp
      (translate v) = translate (c • v) := by
  refine algHom_ext fun i => ?_
  simp [translate]
  ring

/-- `Singularity/Invariant/Directrix.lean`: the substitution `s ↦ c s` after `rename some`. -/
theorem scaleVar_comp_rename (c : k) :
    (aeval fun o : Option σ => Option.elim o (C c * X none) fun i => X (some i)).comp
      (rename some : MvPolynomial σ k →ₐ[k] MvPolynomial (Option σ) k) = rename some := by
  refine algHom_ext fun i => ?_
  simp

/-- `Singularity/Invariant/Directrix.lean`: the substitution `x ↦ x + s w` after a translation. -/
theorem shiftVar_comp_translate (v w : σ → k) :
    (aeval fun o : Option σ => Option.elim o (X none) fun i => X (some i) + C (w i) * X none).comp
      (translate v) = translate (v + w) := by
  refine algHom_ext fun i => ?_
  simp [translate]
  ring

/-- `Singularity/Invariant/Directrix.lean`: the substitution `x ↦ x + s w` after `rename some`. -/
theorem shiftVar_comp_rename (w : σ → k) :
    (aeval fun o : Option σ => Option.elim o (X none) fun i => X (some i) + C (w i) * X none).comp
      (rename some : MvPolynomial σ k →ₐ[k] MvPolynomial (Option σ) k) = translate w := by
  refine algHom_ext fun i => ?_
  simp [translate]

/-- `Singularity/Invariant/Directrix.lean`: the directrix `T(g)` [Hir67], the vectors `v` with
`g(x + s v) = g(x)`. -/
noncomputable def directrix (g : MvPolynomial σ k) : Submodule k (σ → k) where
  carrier := {v | translate v g = rename some g}
  zero_mem' := by
    show translate 0 g = rename some g
    rw [translate_zero]
  add_mem' := by
    intro v w hv hw
    show translate (v + w) g = rename some g
    have hv' : translate v g = rename some g := hv
    have hw' : translate w g = rename some g := hw
    rw [← shiftVar_comp_translate, AlgHom.comp_apply, hv', ← AlgHom.comp_apply,
      shiftVar_comp_rename, hw']
  smul_mem' := by
    intro c v hv
    show translate (c • v) g = rename some g
    have hv' : translate v g = rename some g := hv
    rw [← scaleVar_comp_translate, AlgHom.comp_apply, hv', ← AlgHom.comp_apply,
      scaleVar_comp_rename]

variable [DecidableEq σ]

/-- `Singularity/Invariant/Directrix.lean`: the vector of the `x_j`-chart with translations `t`. -/
def chartVector (j : σ) (t : σ → k) : σ → k :=
  fun i => if i = j then 1 else t i

end Directrix

section NearPoint

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- `Singularity/Invariant/LogJacobianNearPoint.lean`: Theorem 3.7.1, part 1, of Volume 7,
Section 3.7 of the handbook. -/
theorem chartVector_mem_directrix_of_logJacobianOrder_eq (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m) {ψ : MvPolynomial σ k}
    (hψ : monomial (divisorExponent Δ g) 1 * ψ ∈ logJacobianTangent Δ g) (hψo : ord ψ = m) :
    chartVector j t ∈ directrix (homogeneousComponent m ψ) := sorry

/-- `Singularity/Invariant/LogJacobianNearPoint.lean`: Theorem 3.7.1, part 2, of Volume 7,
Section 3.7 of the handbook. -/
theorem chartVector_mem_directrix_of_logJacobianOrder_eq_of_idealOrd (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m)
    (hτ : idealOrd (logJacobianTangent Δ g) = ((degree (divisorExponent Δ g) + m + 1 : ℕ) : ℕ∞))
    {ψ : MvPolynomial σ k} (hψ : monomial (divisorExponent Δ g) 1 * ψ ∈ logJacobian Δ g)
    (hψo : ord ψ = m) :
    chartVector j t ∈ directrix (homogeneousComponent m ψ) := sorry

/-- `Singularity/Invariant/LogJacobianNearPoint.lean`: Corollary 3.7.2, case A, of Volume 7,
Section 3.7 of the handbook. -/
theorem logJacobianOrder_cleanPart_lt_of_directrix_eq_bot (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m) {ψ : MvPolynomial σ k}
    (hψ : monomial (divisorExponent Δ g) 1 * ψ ∈ logJacobianTangent Δ g) (hψo : ord ψ = m)
    (hT : directrix (homogeneousComponent m ψ) = ⊥) :
    logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') < m := sorry

/-- `Singularity/Invariant/LogJacobianNearPoint.lean`: Corollary 3.7.2, case B, of Volume 7,
Section 3.7 of the handbook. -/
theorem logJacobianOrder_cleanPart_lt_of_directrix_eq_bot_of_idealOrd (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hτ : idealOrd (logJacobianTangent Δ g) = ((degree (divisorExponent Δ g) + m + 1 : ℕ) : ℕ∞))
    {ψ : MvPolynomial σ k} (hψ : monomial (divisorExponent Δ g) 1 * ψ ∈ logJacobian Δ g)
    (hψo : ord ψ = m) (hT : directrix (homogeneousComponent m ψ) = ⊥) :
    logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') < m := sorry

/-- `Singularity/Invariant/LogJacobianNearPoint.lean`: Corollary 3.7.3, the case `ρ = ord G`, of
Volume 7, Section 3.7 of the handbook. -/
theorem chartVector_mem_directrix_initialForm_of_logJacobianOrder_eq (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hG : ord (residualFactor Δ g) = d) (hρ : logJacobianOrder Δ g = d)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d)
    (hpd : ((degree (divisorExponent Δ g) + d : ℕ) : k) ≠ 0) :
    chartVector j t ∈ directrix (homogeneousComponent d (residualFactor Δ g)) := sorry

/-- `Singularity/Invariant/LogJacobianNearPoint.lean`: Corollary 3.7.3, the case `ρ = ord G - 1`,
of Volume 7, Section 3.7 of the handbook. -/
theorem chartVector_mem_directrix_pderiv_initialForm_of_logJacobianOrder_eq (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hG : ord (residualFactor Δ g) = d) {l : σ} (hl : l ∉ Δ)
    (hne : pderiv l (homogeneousComponent d (residualFactor Δ g)) ≠ 0)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = (d - 1 : ℕ)) :
    chartVector j t ∈ directrix (pderiv l (homogeneousComponent d (residualFactor Δ g))) := sorry

end NearPoint

/-- `Singularity/Invariant/LogJacobianNearPoint.lean`: Example 3.7.4 of Volume 7, Section 3.7 of
the handbook. Part 1 of Theorem 3.7.1 fails with `Θ(g)` in the place of `Θ₀(g)`. -/
theorem nearPointExample_not_mem_directrix :
    logJacobianOrder {0} (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3)) = 1 ∧
      logJacobianOrder (blowupDivisor {0} 1 (0 : Fin 2 → ZMod 3))
        (cleanPart 3 (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 * X 1 : MvPolynomial (Fin 2) (ZMod 3))) = 1 ∧
      monomial (divisorExponent {0} (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 :
          MvPolynomial (Fin 2) (ZMod 3))) 1 * (2 * X 1) ∈
        logJacobian {0} (X 0 ^ 3 * X 1 ^ 2 + X 0 ^ 4 : MvPolynomial (Fin 2) (ZMod 3)) ∧
      ord (2 * X 1 : MvPolynomial (Fin 2) (ZMod 3)) = 1 ∧
      chartVector 1 (0 : Fin 2 → ZMod 3) ∉
        directrix (homogeneousComponent 1 (2 * X 1 : MvPolynomial (Fin 2) (ZMod 3))) := sorry

end LogJacobianNearPoint

section LogJacobianDirectrix

open MvPolynomial Finsupp Module

section Linear

variable {σ k : Type*} [Field k]

/-- `Singularity/Invariant/LogJacobianDirectrix.lean`: the part of degree `n` of an element of an
ideal of order at least `n` is a `k`-linear combination of the parts of degree `n` of the
generators. -/
theorem homogeneousComponent_mem_span_of_mem_span {S : Set (MvPolynomial σ k)} {n : ℕ}
    (hS : ∀ s ∈ S, (n : ℕ∞) ≤ ord s) {f : MvPolynomial σ k} (hf : f ∈ Ideal.span S) :
    homogeneousComponent n f ∈ Submodule.span k (homogeneousComponent n '' S) := sorry

/-- `Singularity/Invariant/LogJacobianDirectrix.lean`: the directrix of the part of degree `n` of
an element of an ideal of order at least `n`. -/
theorem le_directrix_homogeneousComponent_of_mem_span {S : Set (MvPolynomial σ k)} {n : ℕ}
    (hS : ∀ s ∈ S, (n : ℕ∞) ≤ ord s) {W : Submodule k (σ → k)}
    (hW : ∀ s ∈ S, W ≤ directrix (homogeneousComponent n s)) {f : MvPolynomial σ k}
    (hf : f ∈ Ideal.span S) : W ≤ directrix (homogeneousComponent n f) := sorry

end Linear

section Restriction

variable {σ k : Type*} [Field k] [DecidableEq σ]

/-- `Singularity/Invariant/LogJacobianDirectrix.lean`: the dimension inequality for the weak
transforms (Volume 7, Section 3.8 of the handbook). -/
theorem finrank_iInf_directrix_pointChart_le [Fintype σ] {ι : Type*} {j : σ} {t : σ → k} {m : ℕ}
    {ψ ψ' : ι → MvPolynomial σ k} (hψ : ∀ i, (m : ℕ∞) ≤ ord (ψ i))
    (h : ∀ i, pointChart j t (ψ i) = X j ^ m * ψ' i) (hψ' : ∀ i, (m : ℕ∞) ≤ ord (ψ' i)) :
    finrank k (⨅ i, directrix (homogeneousComponent m (ψ' i)) : Submodule k (σ → k)) ≤
      finrank k (⨅ i, directrix (homogeneousComponent m (ψ i)) : Submodule k (σ → k)) := sorry

end Restriction

section Def

variable {σ k : Type*} [Field k]

/-- `Singularity/Invariant/LogJacobianDirectrix.lean`: `Θ₀(g)` in case A and `Θ(g)` in case B. -/
noncomputable def logJacobianCaseIdeal (Δ : Finset σ) (g : MvPolynomial σ k) :
    Ideal (MvPolynomial σ k) :=
  if idealOrd (logJacobianTangent Δ g) = degree (divisorExponent Δ g) + logJacobianOrder Δ g then
    logJacobianTangent Δ g
  else logJacobian Δ g

/-- `Singularity/Invariant/LogJacobianDirectrix.lean`: the polynomials `ψ` of the definition of
`T_ρ(g)`. -/
def logJacobianDirectrixSet (Δ : Finset σ) (g : MvPolynomial σ k) : Set (MvPolynomial σ k) :=
  {ψ | ord ψ = logJacobianOrder Δ g ∧
    monomial (divisorExponent Δ g) 1 * ψ ∈ logJacobianCaseIdeal Δ g}

/-- `Singularity/Invariant/LogJacobianDirectrix.lean`: the directrix `T_ρ(g)` of the
log-Jacobian order (Volume 7, Section 3.8 of the handbook). -/
noncomputable def logJacobianDirectrix (Δ : Finset σ) (g : MvPolynomial σ k) :
    Submodule k (σ → k) :=
  ⨅ ψ ∈ logJacobianDirectrixSet Δ g,
    directrix (homogeneousComponent (logJacobianOrder Δ g).toNat ψ)

/-- `Singularity/Invariant/LogJacobianDirectrix.lean`: the codimension `τ_ρ(g)` of `T_ρ(g)`. -/
noncomputable def logJacobianDirectrixCodim [Fintype σ] (Δ : Finset σ) (g : MvPolynomial σ k) :
    ℕ :=
  Fintype.card σ - finrank k (logJacobianDirectrix Δ g)

end Def

section Proposition

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- `Singularity/Invariant/LogJacobianDirectrix.lean`: Proposition 3.8.2 of Volume 7,
Section 3.8 of the handbook. -/
theorem finrank_logJacobianDirectrix_cleanPart_le (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m)
    (hB : idealOrd (logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g')) =
      ((degree (divisorExponent (blowupDivisor Δ j t) (cleanPart p g')) + m + 1 : ℕ) : ℕ∞)) :
    finrank k (logJacobianDirectrix (blowupDivisor Δ j t) (cleanPart p g')) ≤
      finrank k (logJacobianDirectrix Δ g) := sorry

/-- `Singularity/Invariant/LogJacobianDirectrix.lean`: Proposition 3.8.2 of Volume 7,
Section 3.8 of the handbook, the form with the codimension. -/
theorem logJacobianDirectrixCodim_le_cleanPart (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m)
    (hB : idealOrd (logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g')) =
      ((degree (divisorExponent (blowupDivisor Δ j t) (cleanPart p g')) + m + 1 : ℕ) : ℕ∞)) :
    logJacobianDirectrixCodim Δ g ≤
      logJacobianDirectrixCodim (blowupDivisor Δ j t) (cleanPart p g') := sorry

end Proposition

/-- `Singularity/Invariant/LogJacobianDirectrix.lean`: Example 3.8.3 of Volume 7, Section 3.8 of
the handbook, the cases. -/
theorem tauRhoExample_cases :
    idealOrd (logJacobianTangent ∅
        (X 0 * X 1 * X 2 ^ 2 + X 1 ^ 2 * X 2 + X 0 * X 2 ^ 2 : MvPolynomial (Fin 3) (ZMod 2))) ≠
        degree (divisorExponent ∅
          (X 0 * X 1 * X 2 ^ 2 + X 1 ^ 2 * X 2 + X 0 * X 2 ^ 2 : MvPolynomial (Fin 3) (ZMod 2))) +
          logJacobianOrder ∅
            (X 0 * X 1 * X 2 ^ 2 + X 1 ^ 2 * X 2 + X 0 * X 2 ^ 2 : MvPolynomial (Fin 3) (ZMod 2)) ∧
      idealOrd (logJacobianTangent (blowupDivisor ∅ 0 (0 : Fin 3 → ZMod 2))
          (cleanPart 2 (X 0 ^ 2 * X 1 * X 2 ^ 2 + X 0 * X 1 ^ 2 * X 2 + X 0 * X 2 ^ 2 :
            MvPolynomial (Fin 3) (ZMod 2)))) =
        degree (divisorExponent (blowupDivisor ∅ 0 (0 : Fin 3 → ZMod 2))
          (cleanPart 2 (X 0 ^ 2 * X 1 * X 2 ^ 2 + X 0 * X 1 ^ 2 * X 2 + X 0 * X 2 ^ 2 :
            MvPolynomial (Fin 3) (ZMod 2)))) +
          logJacobianOrder (blowupDivisor ∅ 0 (0 : Fin 3 → ZMod 2))
            (cleanPart 2 (X 0 ^ 2 * X 1 * X 2 ^ 2 + X 0 * X 1 ^ 2 * X 2 + X 0 * X 2 ^ 2 :
              MvPolynomial (Fin 3) (ZMod 2))) := sorry

/-- `Singularity/Invariant/LogJacobianDirectrix.lean`: Example 3.8.3 of Volume 7, Section 3.8 of
the handbook. The case condition of Proposition 3.8.2 is necessary. -/
theorem tauRhoExample_finrank :
    logJacobianOrder ∅
        (X 0 * X 1 * X 2 ^ 2 + X 1 ^ 2 * X 2 + X 0 * X 2 ^ 2 : MvPolynomial (Fin 3) (ZMod 2)) = 2 ∧
      logJacobianOrder (blowupDivisor ∅ 0 (0 : Fin 3 → ZMod 2))
        (cleanPart 2 (X 0 ^ 2 * X 1 * X 2 ^ 2 + X 0 * X 1 ^ 2 * X 2 + X 0 * X 2 ^ 2 :
          MvPolynomial (Fin 3) (ZMod 2))) = 2 ∧
      finrank (ZMod 2) (logJacobianDirectrix ∅
        (X 0 * X 1 * X 2 ^ 2 + X 1 ^ 2 * X 2 + X 0 * X 2 ^ 2 : MvPolynomial (Fin 3) (ZMod 2))) = 1 ∧
      finrank (ZMod 2) (logJacobianDirectrix (blowupDivisor ∅ 0 (0 : Fin 3 → ZMod 2))
        (cleanPart 2 (X 0 ^ 2 * X 1 * X 2 ^ 2 + X 0 * X 1 ^ 2 * X 2 + X 0 * X 2 ^ 2 :
          MvPolynomial (Fin 3) (ZMod 2)))) = 2 := sorry

end LogJacobianDirectrix

section LogJacobianDirectrixCaseA

open MvPolynomial Finsupp Module

section Lemma

variable {σ k : Type*} [Field k]

/-- `Singularity/Invariant/LogJacobianDirectrixCaseA.lean`: Lemma 3.9.2 of Volume 7, Section 3.9
of the handbook. -/
theorem pderiv_eq_zero_of_mem_directrix {F : MvPolynomial σ k} {v : σ → k} {i : σ} (c : k)
    (hF : v ∈ directrix F) (hΦ : v ∈ directrix (c • F + X i * pderiv i F)) (hv : v i ≠ 0) :
    pderiv i F = 0 := sorry

end Lemma

section Theorem

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- `Singularity/Invariant/LogJacobianDirectrixCaseA.lean`: Theorem 3.9.1 of Volume 7,
Section 3.9 of the handbook. -/
theorem finrank_logJacobianDirectrix_cleanPart_le_of_caseA (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hG : ord (residualFactor Δ g) = d) (hρ : logJacobianOrder Δ g = d)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d)
    (hA' : idealOrd (logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g')) =
      ((degree (divisorExponent (blowupDivisor Δ j t) (cleanPart p g')) + d : ℕ) : ℕ∞))
    (hpd : ((degree (divisorExponent Δ g) + d : ℕ) : k) ≠ 0) :
    finrank k (logJacobianDirectrix (blowupDivisor Δ j t) (cleanPart p g')) ≤
      finrank k (logJacobianDirectrix Δ g) := sorry

/-- `Singularity/Invariant/LogJacobianDirectrixCaseA.lean`: Theorem 3.9.1 of Volume 7,
Section 3.9 of the handbook, the form with the codimension. -/
theorem logJacobianDirectrixCodim_le_cleanPart_of_caseA (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hG : ord (residualFactor Δ g) = d) (hρ : logJacobianOrder Δ g = d)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d)
    (hA' : idealOrd (logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g')) =
      ((degree (divisorExponent (blowupDivisor Δ j t) (cleanPart p g')) + d : ℕ) : ℕ∞))
    (hpd : ((degree (divisorExponent Δ g) + d : ℕ) : k) ≠ 0) :
    logJacobianDirectrixCodim Δ g ≤
      logJacobianDirectrixCodim (blowupDivisor Δ j t) (cleanPart p g') := sorry

end Theorem

/-- `Singularity/Invariant/LogJacobianDirectrixCaseA.lean`: Example 3.9.4 of Volume 7,
Section 3.9 of the handbook, the data. -/
theorem tauRhoCaseAExample_hyp :
    divisorExponent {0}
        (X 0 * X 2 ^ 2 + X 0 ^ 2 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) = single 0 1 ∧
      residualFactor {0} (X 0 * X 2 ^ 2 + X 0 ^ 2 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) =
        X 2 ^ 2 + X 0 * X 1 ^ 3 ∧
      ((divisorExponent {0}
          (X 0 * X 2 ^ 2 + X 0 ^ 2 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) 0 : ZMod 2) •
          residualFactor {0} (X 0 * X 2 ^ 2 + X 0 ^ 2 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) +
        X 0 * pderiv 0 (residualFactor {0}
          (X 0 * X 2 ^ 2 + X 0 ^ 2 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2))) = X 2 ^ 2) ∧
      pointChart 1 (![1, 0, 0] : Fin 3 → ZMod 2)
          (X 0 * X 2 ^ 2 + X 0 ^ 2 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 2)) =
        X 1 ^ 2 * (X 1 * ((X 0 + 1) * X 2 ^ 2 + X 1 ^ 2 * (X 0 ^ 2 + 1))) ∧
      blowupDivisor {0} 1 (![1, 0, 0] : Fin 3 → ZMod 2) = {1} := sorry

/-- `Singularity/Invariant/LogJacobianDirectrixCaseA.lean`: Example 3.9.4 of Volume 7,
Section 3.9 of the handbook. The plain transports of `e_x` are not in `Θ₀(g'_c)`. -/
theorem tauRhoCaseAExample_not_mem :
    IsClean 2 (X 1 * ((X 0 + 1) * X 2 ^ 2 + X 1 ^ 2 * (X 0 ^ 2 + 1)) :
      MvPolynomial (Fin 3) (ZMod 2)) ∧
      X 1 * X 2 ^ 2 ∉ logJacobianTangent (blowupDivisor {0} 1 (![1, 0, 0] : Fin 3 → ZMod 2))
        (cleanPart 2 (X 1 * ((X 0 + 1) * X 2 ^ 2 + X 1 ^ 2 * (X 0 ^ 2 + 1)) :
          MvPolynomial (Fin 3) (ZMod 2))) ∧
      X 1 * ((X 0 + 1) * X 2 ^ 2) ∉
        logJacobianTangent (blowupDivisor {0} 1 (![1, 0, 0] : Fin 3 → ZMod 2))
          (cleanPart 2 (X 1 * ((X 0 + 1) * X 2 ^ 2 + X 1 ^ 2 * (X 0 ^ 2 + 1)) :
            MvPolynomial (Fin 3) (ZMod 2))) := sorry

end LogJacobianDirectrixCaseA

section LogJacobianDirectrixDrop

open MvPolynomial Finsupp Module

/-- `Singularity/Invariant/LogJacobianDirectrixDrop.lean`: Example 3.9.5 of Volume 7,
Section 3.9 of the handbook, the data. -/
theorem tauRhoDropExample_hyp :
    (X 0 * X 2 ^ 2 * X 3 * X 4 ^ 2 + X 0 * X 1 * X 2 * X 3 * X 4 ^ 2 :
        MvPolynomial (Fin 5) (ZMod 2)) ≠ 0 ∧
      IsClean 2 (X 0 * X 2 ^ 2 * X 3 * X 4 ^ 2 + X 0 * X 1 * X 2 * X 3 * X 4 ^ 2 :
        MvPolynomial (Fin 5) (ZMod 2)) ∧
      ((2 : ℕ) : ℕ∞) ≤ ord (X 0 * X 2 ^ 2 * X 3 * X 4 ^ 2 + X 0 * X 1 * X 2 * X 3 * X 4 ^ 2 :
        MvPolynomial (Fin 5) (ZMod 2)) ∧
      pointChart 3 (Pi.single 0 1 : Fin 5 → ZMod 2)
          (X 0 * X 2 ^ 2 * X 3 * X 4 ^ 2 + X 0 * X 1 * X 2 * X 3 * X 4 ^ 2 :
            MvPolynomial (Fin 5) (ZMod 2)) =
        X 3 ^ 2 * (X 3 ^ 4 * (X 0 + 1) * (X 2 ^ 2 + X 1 * X 2) * X 4 ^ 2) ∧
      blowupDivisor ({0, 1, 2, 3} : Finset (Fin 5)) 3 (Pi.single 0 1 : Fin 5 → ZMod 2) =
        {1, 2, 3} ∧
      cleanPart 2 (X 3 ^ 4 * (X 0 + 1) * (X 2 ^ 2 + X 1 * X 2) * X 4 ^ 2 :
          MvPolynomial (Fin 5) (ZMod 2)) =
        X 3 ^ 4 * (X 0 * X 2 ^ 2 * X 4 ^ 2 + (X 0 + 1) * X 1 * X 2 * X 4 ^ 2) ∧
      divisorExponent ({0, 1, 2, 3} : Finset (Fin 5))
          (X 0 * X 2 ^ 2 * X 3 * X 4 ^ 2 + X 0 * X 1 * X 2 * X 3 * X 4 ^ 2 :
            MvPolynomial (Fin 5) (ZMod 2)) =
        single 0 1 + single 2 1 + single 3 1 ∧
      residualFactor ({0, 1, 2, 3} : Finset (Fin 5))
          (X 0 * X 2 ^ 2 * X 3 * X 4 ^ 2 + X 0 * X 1 * X 2 * X 3 * X 4 ^ 2 :
            MvPolynomial (Fin 5) (ZMod 2)) =
        (X 1 + X 2) * X 4 ^ 2 ∧
      ((degree (divisorExponent ({0, 1, 2, 3} : Finset (Fin 5))
          (X 0 * X 2 ^ 2 * X 3 * X 4 ^ 2 + X 0 * X 1 * X 2 * X 3 * X 4 ^ 2 :
            MvPolynomial (Fin 5) (ZMod 2))) + 3 : ℕ) : ZMod 2) = 0 := sorry

/-- `Singularity/Invariant/LogJacobianDirectrixDrop.lean`: Example 3.9.5 of Volume 7,
Section 3.9 of the handbook. The old and the new points are of case A. -/
theorem tauRhoDropExample_cases :
    idealOrd (logJacobianTangent ({0, 1, 2, 3} : Finset (Fin 5))
        (X 0 * X 2 ^ 2 * X 3 * X 4 ^ 2 + X 0 * X 1 * X 2 * X 3 * X 4 ^ 2 :
          MvPolynomial (Fin 5) (ZMod 2))) =
        degree (divisorExponent ({0, 1, 2, 3} : Finset (Fin 5))
          (X 0 * X 2 ^ 2 * X 3 * X 4 ^ 2 + X 0 * X 1 * X 2 * X 3 * X 4 ^ 2 :
            MvPolynomial (Fin 5) (ZMod 2))) +
          logJacobianOrder ({0, 1, 2, 3} : Finset (Fin 5))
            (X 0 * X 2 ^ 2 * X 3 * X 4 ^ 2 + X 0 * X 1 * X 2 * X 3 * X 4 ^ 2 :
              MvPolynomial (Fin 5) (ZMod 2)) ∧
      idealOrd (logJacobianTangent
          (blowupDivisor ({0, 1, 2, 3} : Finset (Fin 5)) 3 (Pi.single 0 1 : Fin 5 → ZMod 2))
          (cleanPart 2 (X 3 ^ 4 * (X 0 + 1) * (X 2 ^ 2 + X 1 * X 2) * X 4 ^ 2 :
            MvPolynomial (Fin 5) (ZMod 2)))) =
        degree (divisorExponent
          (blowupDivisor ({0, 1, 2, 3} : Finset (Fin 5)) 3 (Pi.single 0 1 : Fin 5 → ZMod 2))
          (cleanPart 2 (X 3 ^ 4 * (X 0 + 1) * (X 2 ^ 2 + X 1 * X 2) * X 4 ^ 2 :
            MvPolynomial (Fin 5) (ZMod 2)))) +
          logJacobianOrder
            (blowupDivisor ({0, 1, 2, 3} : Finset (Fin 5)) 3 (Pi.single 0 1 : Fin 5 → ZMod 2))
            (cleanPart 2 (X 3 ^ 4 * (X 0 + 1) * (X 2 ^ 2 + X 1 * X 2) * X 4 ^ 2 :
              MvPolynomial (Fin 5) (ZMod 2))) := sorry

/-- `Singularity/Invariant/LogJacobianDirectrixDrop.lean`: Example 3.9.5 of Volume 7,
Section 3.9 of the handbook. `ρ` stays `3`, and the dimension of `T_ρ` goes up from `2` to `3`. -/
theorem tauRhoDropExample_finrank :
    logJacobianOrder ({0, 1, 2, 3} : Finset (Fin 5))
        (X 0 * X 2 ^ 2 * X 3 * X 4 ^ 2 + X 0 * X 1 * X 2 * X 3 * X 4 ^ 2 :
          MvPolynomial (Fin 5) (ZMod 2)) = 3 ∧
      logJacobianOrder
          (blowupDivisor ({0, 1, 2, 3} : Finset (Fin 5)) 3 (Pi.single 0 1 : Fin 5 → ZMod 2))
          (cleanPart 2 (X 3 ^ 4 * (X 0 + 1) * (X 2 ^ 2 + X 1 * X 2) * X 4 ^ 2 :
            MvPolynomial (Fin 5) (ZMod 2))) = 3 ∧
      finrank (ZMod 2) (logJacobianDirectrix ({0, 1, 2, 3} : Finset (Fin 5))
        (X 0 * X 2 ^ 2 * X 3 * X 4 ^ 2 + X 0 * X 1 * X 2 * X 3 * X 4 ^ 2 :
          MvPolynomial (Fin 5) (ZMod 2))) = 2 ∧
      finrank (ZMod 2) (logJacobianDirectrix
          (blowupDivisor ({0, 1, 2, 3} : Finset (Fin 5)) 3 (Pi.single 0 1 : Fin 5 → ZMod 2))
          (cleanPart 2 (X 3 ^ 4 * (X 0 + 1) * (X 2 ^ 2 + X 1 * X 2) * X 4 ^ 2 :
            MvPolynomial (Fin 5) (ZMod 2)))) = 3 := sorry

/-- `Singularity/Invariant/LogJacobianDirectrixDrop.lean`: Example 3.9.5 of Volume 7,
Section 3.9 of the handbook, the form with the codimension. `τ_ρ` goes down from `3` to `2`. -/
theorem tauRhoDropExample_codim :
    logJacobianDirectrixCodim ({0, 1, 2, 3} : Finset (Fin 5))
        (X 0 * X 2 ^ 2 * X 3 * X 4 ^ 2 + X 0 * X 1 * X 2 * X 3 * X 4 ^ 2 :
          MvPolynomial (Fin 5) (ZMod 2)) = 3 ∧
      logJacobianDirectrixCodim
          (blowupDivisor ({0, 1, 2, 3} : Finset (Fin 5)) 3 (Pi.single 0 1 : Fin 5 → ZMod 2))
          (cleanPart 2 (X 3 ^ 4 * (X 0 + 1) * (X 2 ^ 2 + X 1 * X 2) * X 4 ^ 2 :
            MvPolynomial (Fin 5) (ZMod 2))) = 2 := sorry

end LogJacobianDirectrixDrop

section LogJacobianCaseAStable

open MvPolynomial Finsupp Module

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- `Singularity/Invariant/LogJacobianCaseAStable.lean`: Proposition 3.9.7 of Volume 7,
Section 3.9 of the handbook. -/
theorem idealOrd_logJacobianTangent_cleanPart_of_caseA (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hG : ord (residualFactor Δ g) = d) (hρ : logJacobianOrder Δ g = d)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d)
    (hpd : ((degree (divisorExponent Δ g) + d : ℕ) : k) ≠ 0) :
    idealOrd (logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g')) =
      ((degree (divisorExponent (blowupDivisor Δ j t) (cleanPart p g')) + d : ℕ) : ℕ∞) := sorry

/-- `Singularity/Invariant/LogJacobianCaseAStable.lean`: Corollary 3.9.8 of Volume 7,
Section 3.9 of the handbook. -/
theorem finrank_logJacobianDirectrix_cleanPart_le_of_ne_zero (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hG : ord (residualFactor Δ g) = d) (hρ : logJacobianOrder Δ g = d)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d)
    (hpd : ((degree (divisorExponent Δ g) + d : ℕ) : k) ≠ 0) :
    finrank k (logJacobianDirectrix (blowupDivisor Δ j t) (cleanPart p g')) ≤
      finrank k (logJacobianDirectrix Δ g) := sorry

/-- `Singularity/Invariant/LogJacobianCaseAStable.lean`: Corollary 3.9.8 of Volume 7,
Section 3.9 of the handbook, the form with the codimension. -/
theorem logJacobianDirectrixCodim_le_cleanPart_of_ne_zero (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hG : ord (residualFactor Δ g) = d) (hρ : logJacobianOrder Δ g = d)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d)
    (hpd : ((degree (divisorExponent Δ g) + d : ℕ) : k) ≠ 0) :
    logJacobianDirectrixCodim Δ g ≤
      logJacobianDirectrixCodim (blowupDivisor Δ j t) (cleanPart p g') := sorry

end LogJacobianCaseAStable

section LogJacobianCaseAUnstable

open MvPolynomial Finsupp Module

/-- `Singularity/Invariant/LogJacobianCaseAUnstable.lean`: Example 3.9.9 of Volume 7,
Section 3.9 of the handbook, the data. The hypothesis `hpd` of
`idealOrd_logJacobianTangent_cleanPart_of_caseA` fails. -/
theorem caseAToCaseBExample_hyp :
    (X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 3 + 2 * X 0 ^ 2 * X 1 ^ 3 * X 2 :
        MvPolynomial (Fin 3) (ZMod 3)) ≠ 0 ∧
      IsClean 3 (X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 3 + 2 * X 0 ^ 2 * X 1 ^ 3 * X 2 :
        MvPolynomial (Fin 3) (ZMod 3)) ∧
      ((3 : ℕ) : ℕ∞) ≤ ord (X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 3 + 2 * X 0 ^ 2 * X 1 ^ 3 * X 2 :
        MvPolynomial (Fin 3) (ZMod 3)) ∧
      pointChart 0 (Pi.single 2 1 : Fin 3 → ZMod 3)
          (X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 3 + 2 * X 0 ^ 2 * X 1 ^ 3 * X 2 :
            MvPolynomial (Fin 3) (ZMod 3)) =
        X 0 ^ 3 * (X 0 ^ 5 * X 1 ^ 2 * (X 2 + 1) ^ 3 + 2 * X 0 ^ 3 * X 1 ^ 3 * (X 2 + 1)) ∧
      blowupDivisor ({0, 2} : Finset (Fin 3)) 0 (Pi.single 2 1 : Fin 3 → ZMod 3) = {0} ∧
      cleanPart 3 (X 0 ^ 5 * X 1 ^ 2 * (X 2 + 1) ^ 3 + 2 * X 0 ^ 3 * X 1 ^ 3 * (X 2 + 1) :
          MvPolynomial (Fin 3) (ZMod 3)) =
        X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 3 + X 0 ^ 5 * X 1 ^ 2 + 2 * X 0 ^ 3 * X 1 ^ 3 * X 2 ∧
      divisorExponent ({0, 2} : Finset (Fin 3))
          (X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 3 + 2 * X 0 ^ 2 * X 1 ^ 3 * X 2 :
            MvPolynomial (Fin 3) (ZMod 3)) =
        single 0 2 + single 2 1 ∧
      residualFactor ({0, 2} : Finset (Fin 3))
          (X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 3 + 2 * X 0 ^ 2 * X 1 ^ 3 * X 2 :
            MvPolynomial (Fin 3) (ZMod 3)) =
        X 0 * X 1 ^ 2 * X 2 ^ 2 + 2 * X 1 ^ 3 ∧
      ord (X 0 * X 1 ^ 2 * X 2 ^ 2 + 2 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 3)) = 3 ∧
      ((degree (divisorExponent ({0, 2} : Finset (Fin 3))
          (X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 3 + 2 * X 0 ^ 2 * X 1 ^ 3 * X 2 :
            MvPolynomial (Fin 3) (ZMod 3))) + 3 : ℕ) : ZMod 3) = 0 ∧
      divisorExponent ({0} : Finset (Fin 3))
          (X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 3 + X 0 ^ 5 * X 1 ^ 2 + 2 * X 0 ^ 3 * X 1 ^ 3 * X 2 :
            MvPolynomial (Fin 3) (ZMod 3)) =
        single 0 3 ∧
      residualFactor ({0} : Finset (Fin 3))
          (X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 3 + X 0 ^ 5 * X 1 ^ 2 + 2 * X 0 ^ 3 * X 1 ^ 3 * X 2 :
            MvPolynomial (Fin 3) (ZMod 3)) =
        X 0 ^ 2 * X 1 ^ 2 * (X 2 ^ 3 + 1) + 2 * X 1 ^ 3 * X 2 := sorry

/-- `Singularity/Invariant/LogJacobianCaseAUnstable.lean`: Example 3.9.9 of Volume 7,
Section 3.9 of the handbook. The old point is of case A, and the new point is of case B. -/
theorem caseAToCaseBExample_cases :
    idealOrd (logJacobianTangent ({0, 2} : Finset (Fin 3))
        (X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 3 + 2 * X 0 ^ 2 * X 1 ^ 3 * X 2 :
          MvPolynomial (Fin 3) (ZMod 3))) =
        degree (divisorExponent ({0, 2} : Finset (Fin 3))
          (X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 3 + 2 * X 0 ^ 2 * X 1 ^ 3 * X 2 :
            MvPolynomial (Fin 3) (ZMod 3))) +
          logJacobianOrder ({0, 2} : Finset (Fin 3))
            (X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 3 + 2 * X 0 ^ 2 * X 1 ^ 3 * X 2 :
              MvPolynomial (Fin 3) (ZMod 3)) ∧
      idealOrd (logJacobianTangent
          (blowupDivisor ({0, 2} : Finset (Fin 3)) 0 (Pi.single 2 1 : Fin 3 → ZMod 3))
          (cleanPart 3 (X 0 ^ 5 * X 1 ^ 2 * (X 2 + 1) ^ 3 + 2 * X 0 ^ 3 * X 1 ^ 3 * (X 2 + 1) :
            MvPolynomial (Fin 3) (ZMod 3)))) =
        degree (divisorExponent
          (blowupDivisor ({0, 2} : Finset (Fin 3)) 0 (Pi.single 2 1 : Fin 3 → ZMod 3))
          (cleanPart 3 (X 0 ^ 5 * X 1 ^ 2 * (X 2 + 1) ^ 3 + 2 * X 0 ^ 3 * X 1 ^ 3 * (X 2 + 1) :
            MvPolynomial (Fin 3) (ZMod 3)))) +
          logJacobianOrder
            (blowupDivisor ({0, 2} : Finset (Fin 3)) 0 (Pi.single 2 1 : Fin 3 → ZMod 3))
            (cleanPart 3 (X 0 ^ 5 * X 1 ^ 2 * (X 2 + 1) ^ 3 + 2 * X 0 ^ 3 * X 1 ^ 3 * (X 2 + 1) :
              MvPolynomial (Fin 3) (ZMod 3))) + 1 := sorry

/-- `Singularity/Invariant/LogJacobianCaseAUnstable.lean`: Example 3.9.9 of Volume 7,
Section 3.9 of the handbook. `ρ` stays `3`. -/
theorem caseAToCaseBExample_rho :
    logJacobianOrder ({0, 2} : Finset (Fin 3))
        (X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 3 + 2 * X 0 ^ 2 * X 1 ^ 3 * X 2 :
          MvPolynomial (Fin 3) (ZMod 3)) = 3 ∧
      logJacobianOrder
          (blowupDivisor ({0, 2} : Finset (Fin 3)) 0 (Pi.single 2 1 : Fin 3 → ZMod 3))
          (cleanPart 3 (X 0 ^ 5 * X 1 ^ 2 * (X 2 + 1) ^ 3 + 2 * X 0 ^ 3 * X 1 ^ 3 * (X 2 + 1) :
            MvPolynomial (Fin 3) (ZMod 3))) = 3 := sorry

/-- `Singularity/Invariant/LogJacobianCaseAUnstable.lean`: Example 3.9.9 of Volume 7,
Section 3.9 of the handbook. The hypothesis `hpd` of
`idealOrd_logJacobianTangent_cleanPart_of_caseA` fails, and its conclusion fails. So `hpd` is
necessary. -/
theorem caseAToCaseBExample_not_caseA :
    ((degree (divisorExponent ({0, 2} : Finset (Fin 3))
        (X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 3 + 2 * X 0 ^ 2 * X 1 ^ 3 * X 2 :
          MvPolynomial (Fin 3) (ZMod 3))) + 3 : ℕ) : ZMod 3) = 0 ∧
      idealOrd (logJacobianTangent
          (blowupDivisor ({0, 2} : Finset (Fin 3)) 0 (Pi.single 2 1 : Fin 3 → ZMod 3))
          (cleanPart 3 (X 0 ^ 5 * X 1 ^ 2 * (X 2 + 1) ^ 3 + 2 * X 0 ^ 3 * X 1 ^ 3 * (X 2 + 1) :
            MvPolynomial (Fin 3) (ZMod 3)))) ≠
        ((degree (divisorExponent
          (blowupDivisor ({0, 2} : Finset (Fin 3)) 0 (Pi.single 2 1 : Fin 3 → ZMod 3))
          (cleanPart 3 (X 0 ^ 5 * X 1 ^ 2 * (X 2 + 1) ^ 3 + 2 * X 0 ^ 3 * X 1 ^ 3 * (X 2 + 1) :
            MvPolynomial (Fin 3) (ZMod 3)))) + 3 : ℕ) : ℕ∞) := sorry

/-- `Singularity/Invariant/LogJacobianCaseAUnstable.lean`: Example 3.9.9 of Volume 7,
Section 3.9 of the handbook. The dimension of `T_ρ` goes down from `2` to `1`. -/
theorem caseAToCaseBExample_finrank :
    finrank (ZMod 3) (logJacobianDirectrix ({0, 2} : Finset (Fin 3))
        (X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 3 + 2 * X 0 ^ 2 * X 1 ^ 3 * X 2 :
          MvPolynomial (Fin 3) (ZMod 3))) = 2 ∧
      finrank (ZMod 3) (logJacobianDirectrix
          (blowupDivisor ({0, 2} : Finset (Fin 3)) 0 (Pi.single 2 1 : Fin 3 → ZMod 3))
          (cleanPart 3 (X 0 ^ 5 * X 1 ^ 2 * (X 2 + 1) ^ 3 + 2 * X 0 ^ 3 * X 1 ^ 3 * (X 2 + 1) :
            MvPolynomial (Fin 3) (ZMod 3)))) = 1 := sorry

/-- `Singularity/Invariant/LogJacobianCaseAUnstable.lean`: Example 3.9.9 of Volume 7,
Section 3.9 of the handbook, the form with the codimension. `τ_ρ` goes up from `1` to `2`. -/
theorem caseAToCaseBExample_codim :
    logJacobianDirectrixCodim ({0, 2} : Finset (Fin 3))
        (X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 3 + 2 * X 0 ^ 2 * X 1 ^ 3 * X 2 :
          MvPolynomial (Fin 3) (ZMod 3)) = 1 ∧
      logJacobianDirectrixCodim
          (blowupDivisor ({0, 2} : Finset (Fin 3)) 0 (Pi.single 2 1 : Fin 3 → ZMod 3))
          (cleanPart 3 (X 0 ^ 5 * X 1 ^ 2 * (X 2 + 1) ^ 3 + 2 * X 0 ^ 3 * X 1 ^ 3 * (X 2 + 1) :
            MvPolynomial (Fin 3) (ZMod 3))) = 2 := sorry

end LogJacobianCaseAUnstable

section LogJacobianNoLeave

open MvPolynomial Finsupp Module

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- `Singularity/Invariant/LogJacobianNoLeave.lean`: Theorem 3.9.10 of Volume 7, Section 3.9 of the
handbook, the form with the index `i`. -/
theorem idealOrd_logJacobianTangent_cleanPart_of_ne_of_eq_zero (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hA : idealOrd (logJacobianTangent Δ g) = ((degree (divisorExponent Δ g) + d : ℕ) : ℕ∞))
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d) {i : σ} (hi : i ∈ Δ)
    (hij : i ≠ j) (hti : t i = 0)
    (hio : ord ((divisorExponent Δ g i : k) • residualFactor Δ g +
      X i * pderiv i (residualFactor Δ g)) = d) :
    idealOrd (logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g')) =
      ((degree (divisorExponent (blowupDivisor Δ j t) (cleanPart p g')) + d : ℕ) : ℕ∞) := sorry

/-- `Singularity/Invariant/LogJacobianNoLeave.lean`: Theorem 3.9.10 of Volume 7, Section 3.9 of the
handbook, the form with `R = {j}`. -/
theorem idealOrd_logJacobianTangent_cleanPart_of_lt_ord (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hρ : logJacobianOrder Δ g = d)
    (hA : idealOrd (logJacobianTangent Δ g) = ((degree (divisorExponent Δ g) + d : ℕ) : ℕ∞))
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d)
    (hjo : ord ((divisorExponent Δ g j : k) • residualFactor Δ g +
      X j * pderiv j (residualFactor Δ g)) = d)
    (hlt : ∀ i ∈ Δ, i ≠ j → (d : ℕ∞) < ord ((divisorExponent Δ g i : k) • residualFactor Δ g +
      X i * pderiv i (residualFactor Δ g))) :
    idealOrd (logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g')) =
      ((degree (divisorExponent (blowupDivisor Δ j t) (cleanPart p g')) + d : ℕ) : ℕ∞) := sorry

/-- `Singularity/Invariant/LogJacobianNoLeave.lean`: Theorem 3.9.10 of Volume 7, Section 3.9 of the
handbook, the form with no leaving component. -/
theorem idealOrd_logJacobianTangent_cleanPart_of_forall_eq_zero (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hρ : logJacobianOrder Δ g = d)
    (hA : idealOrd (logJacobianTangent Δ g) = ((degree (divisorExponent Δ g) + d : ℕ) : ℕ∞))
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d)
    (ht : ∀ i ∈ Δ, i ≠ j → t i = 0) :
    idealOrd (logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g')) =
      ((degree (divisorExponent (blowupDivisor Δ j t) (cleanPart p g')) + d : ℕ) : ℕ∞) := sorry

/-- `Singularity/Invariant/LogJacobianNoLeave.lean`: Theorem 3.9.11 of Volume 7, Section 3.9 of the
handbook. -/
theorem finrank_logJacobianDirectrix_cleanPart_le_of_forall_eq_zero (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hG : ord (residualFactor Δ g) = d) (hρ : logJacobianOrder Δ g = d)
    (hA : idealOrd (logJacobianTangent Δ g) = ((degree (divisorExponent Δ g) + d : ℕ) : ℕ∞))
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d)
    (ht : ∀ i ∈ Δ, i ≠ j → t i = 0) :
    finrank k (logJacobianDirectrix (blowupDivisor Δ j t) (cleanPart p g')) ≤
      finrank k (logJacobianDirectrix Δ g) := sorry

/-- `Singularity/Invariant/LogJacobianNoLeave.lean`: Theorem 3.9.11 of Volume 7, Section 3.9 of the
handbook, the form with the codimension. -/
theorem logJacobianDirectrixCodim_le_cleanPart_of_forall_eq_zero (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {d : ℕ}
    (hG : ord (residualFactor Δ g) = d) (hρ : logJacobianOrder Δ g = d)
    (hA : idealOrd (logJacobianTangent Δ g) = ((degree (divisorExponent Δ g) + d : ℕ) : ℕ∞))
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = d)
    (ht : ∀ i ∈ Δ, i ≠ j → t i = 0) :
    logJacobianDirectrixCodim Δ g ≤
      logJacobianDirectrixCodim (blowupDivisor Δ j t) (cleanPart p g') := sorry

end LogJacobianNoLeave

section LogJacobianFullDirectrix

open MvPolynomial Finsupp Module

section Def

variable {σ k : Type*} [Field k]

/-- `Singularity/Invariant/LogJacobianFullDirectrix.lean`: the polynomials `ψ` of the definition
of `T̃(g)`. -/
def logJacobianFullDirectrixSet (Δ : Finset σ) (g : MvPolynomial σ k) : Set (MvPolynomial σ k) :=
  {ψ | ord ψ = logJacobianOrder Δ g ∧ monomial (divisorExponent Δ g) 1 * ψ ∈ logJacobian Δ g}

/-- `Singularity/Invariant/LogJacobianFullDirectrix.lean`: the full directrix `T̃(g)` of the
log-Jacobian order (Volume 7, Section 3.8 of the handbook). -/
noncomputable def logJacobianFullDirectrix (Δ : Finset σ) (g : MvPolynomial σ k) :
    Submodule k (σ → k) :=
  ⨅ ψ ∈ logJacobianFullDirectrixSet Δ g,
    directrix (homogeneousComponent (logJacobianOrder Δ g).toNat ψ)

/-- `Singularity/Invariant/LogJacobianFullDirectrix.lean`: the codimension `τ̃(g)` of `T̃(g)`. -/
noncomputable def logJacobianFullDirectrixCodim [Fintype σ] (Δ : Finset σ)
    (g : MvPolynomial σ k) : ℕ :=
  Fintype.card σ - finrank k (logJacobianFullDirectrix Δ g)

/-- `Singularity/Invariant/LogJacobianFullDirectrix.lean`: `T̃(g) ⊆ T_ρ(g)`. -/
theorem logJacobianFullDirectrix_le_logJacobianDirectrix (Δ : Finset σ) (g : MvPolynomial σ k) :
    logJacobianFullDirectrix Δ g ≤ logJacobianDirectrix Δ g := sorry

/-- `Singularity/Invariant/LogJacobianFullDirectrix.lean`: `T̃(g) = T_ρ(g)` in case B. -/
theorem logJacobianFullDirectrix_eq_of_ne {Δ : Finset σ} {g : MvPolynomial σ k}
    (h : idealOrd (logJacobianTangent Δ g) ≠ degree (divisorExponent Δ g) + logJacobianOrder Δ g) :
    logJacobianFullDirectrix Δ g = logJacobianDirectrix Δ g := sorry

/-- `Singularity/Invariant/LogJacobianFullDirectrix.lean`: `τ_ρ(g) ≤ τ̃(g)`. -/
theorem logJacobianDirectrixCodim_le_fullDirectrixCodim [Fintype σ] (Δ : Finset σ)
    (g : MvPolynomial σ k) :
    logJacobianDirectrixCodim Δ g ≤ logJacobianFullDirectrixCodim Δ g := sorry

end Def

variable {σ k : Type*} [Field k] [DecidableEq σ] [Fintype σ] [DecidableEq k] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- `Singularity/Invariant/LogJacobianFullDirectrix.lean`: `dim T̃(g'_c) ≤ dim T_ρ(g)` if `ρ`
stays (Volume 7, Section 3.8 of the handbook). -/
theorem finrank_logJacobianFullDirectrix_cleanPart_le_logJacobianDirectrix (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m) :
    finrank k (logJacobianFullDirectrix (blowupDivisor Δ j t) (cleanPart p g')) ≤
      finrank k (logJacobianDirectrix Δ g) := sorry

/-- `Singularity/Invariant/LogJacobianFullDirectrix.lean`: Theorem 3.8.4 of Volume 7, Section 3.8
of the handbook. -/
theorem finrank_logJacobianFullDirectrix_cleanPart_le (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m)
    (hB : idealOrd (logJacobianTangent Δ g) =
      ((degree (divisorExponent Δ g) + m + 1 : ℕ) : ℕ∞)) :
    finrank k (logJacobianFullDirectrix (blowupDivisor Δ j t) (cleanPart p g')) ≤
      finrank k (logJacobianFullDirectrix Δ g) := sorry

/-- `Singularity/Invariant/LogJacobianFullDirectrix.lean`: Theorem 3.8.4 of Volume 7, Section 3.8
of the handbook, the form with the codimension. -/
theorem logJacobianFullDirectrixCodim_le_cleanPart (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m)
    (hB : idealOrd (logJacobianTangent Δ g) =
      ((degree (divisorExponent Δ g) + m + 1 : ℕ) : ℕ∞)) :
    logJacobianFullDirectrixCodim Δ g ≤
      logJacobianFullDirectrixCodim (blowupDivisor Δ j t) (cleanPart p g') := sorry

/-- `Singularity/Invariant/LogJacobianFullDirectrix.lean`: Theorem 3.8.4 of Volume 7, Section 3.8
of the handbook, the form with the hypothesis that the order of `Θ₀(g)` is not `|r| + ρ`. -/
theorem finrank_logJacobianFullDirectrix_cleanPart_le_of_ne (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m)
    (hB : idealOrd (logJacobianTangent Δ g) ≠ degree (divisorExponent Δ g) + logJacobianOrder Δ g) :
    finrank k (logJacobianFullDirectrix (blowupDivisor Δ j t) (cleanPart p g')) ≤
      finrank k (logJacobianFullDirectrix Δ g) := sorry

/-- `Singularity/Invariant/LogJacobianFullDirectrix.lean`: Theorem 3.8.4 of Volume 7, Section 3.8
of the handbook, the form with the codimension and with the hypothesis that the order of `Θ₀(g)`
is not `|r| + ρ`. -/
theorem logJacobianFullDirectrixCodim_le_cleanPart_of_ne (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m)
    (hB : idealOrd (logJacobianTangent Δ g) ≠ degree (divisorExponent Δ g) + logJacobianOrder Δ g) :
    logJacobianFullDirectrixCodim Δ g ≤
      logJacobianFullDirectrixCodim (blowupDivisor Δ j t) (cleanPart p g') := sorry

/-- `Singularity/Invariant/LogJacobianFullDirectrix.lean`: Example 3.8.5 of Volume 7, Section 3.8
of the handbook, the data. -/
theorem fullDirectrixExample_hyp :
    (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) ≠ 0 ∧
      IsClean 2 (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) ∧
      ((2 : ℕ) : ℕ∞) ≤ ord (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) ∧
      pointChart 1 (0 : Fin 3 → ZMod 2)
          (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) =
        X 1 ^ 2 * (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) ∧
      blowupDivisor ({0, 2} : Finset (Fin 3)) 1 (0 : Fin 3 → ZMod 2) =
        ({0, 1, 2} : Finset (Fin 3)) ∧
      cleanPart 2 (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) =
        (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) ∧
      divisorExponent ({0, 2} : Finset (Fin 3))
          (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) =
        (single 2 1 : Fin 3 →₀ ℕ) ∧
      residualFactor ({0, 2} : Finset (Fin 3))
          (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) =
        (X 1 * X 2 + X 0 : MvPolynomial (Fin 3) (ZMod 2)) ∧
      divisorExponent ({0, 1, 2} : Finset (Fin 3))
          (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) =
        (single 2 1 : Fin 3 →₀ ℕ) ∧
      residualFactor ({0, 1, 2} : Finset (Fin 3))
          (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) =
        (X 1 * X 2 + X 0 : MvPolynomial (Fin 3) (ZMod 2)) := sorry

/-- `Singularity/Invariant/LogJacobianFullDirectrix.lean`: Example 3.8.5 of Volume 7, Section 3.8
of the handbook, the order `ρ`. -/
theorem fullDirectrixExample_rho :
    logJacobianOrder ({0, 2} : Finset (Fin 3))
        (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) = 1 ∧
      logJacobianOrder (blowupDivisor ({0, 2} : Finset (Fin 3)) 1 (0 : Fin 3 → ZMod 2))
          (cleanPart 2 (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2))) = 1 := sorry

/-- `Singularity/Invariant/LogJacobianFullDirectrix.lean`: Example 3.8.5 of Volume 7, Section 3.8
of the handbook, the cases. The old and the new points are of case A. -/
theorem fullDirectrixExample_cases :
    idealOrd (logJacobianTangent ({0, 2} : Finset (Fin 3))
        (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2))) =
        degree (divisorExponent ({0, 2} : Finset (Fin 3))
          (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2))) +
        logJacobianOrder ({0, 2} : Finset (Fin 3))
          (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) ∧
      idealOrd (logJacobianTangent
          (blowupDivisor ({0, 2} : Finset (Fin 3)) 1 (0 : Fin 3 → ZMod 2))
          (cleanPart 2 (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)))) =
        degree (divisorExponent
          (blowupDivisor ({0, 2} : Finset (Fin 3)) 1 (0 : Fin 3 → ZMod 2))
          (cleanPart 2 (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)))) +
        logJacobianOrder (blowupDivisor ({0, 2} : Finset (Fin 3)) 1 (0 : Fin 3 → ZMod 2))
          (cleanPart 2 (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2))) := sorry

/-- `Singularity/Invariant/LogJacobianFullDirectrix.lean`: Example 3.8.5 of Volume 7, Section 3.8
of the handbook, the dimensions. -/
theorem fullDirectrixExample_finrank :
    finrank (ZMod 2) (logJacobianDirectrix ({0, 2} : Finset (Fin 3))
        (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2))) = 2 ∧
      finrank (ZMod 2) (logJacobianFullDirectrix ({0, 2} : Finset (Fin 3))
        (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2))) = 1 ∧
      finrank (ZMod 2) (logJacobianDirectrix
        (blowupDivisor ({0, 2} : Finset (Fin 3)) 1 (0 : Fin 3 → ZMod 2))
        (cleanPart 2 (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)))) = 2 ∧
      finrank (ZMod 2) (logJacobianFullDirectrix
        (blowupDivisor ({0, 2} : Finset (Fin 3)) 1 (0 : Fin 3 → ZMod 2))
        (cleanPart 2 (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)))) = 2 := sorry

/-- `Singularity/Invariant/LogJacobianFullDirectrix.lean`: Example 3.8.5 of Volume 7, Section 3.8
of the handbook, the form with the codimension. `τ̃` goes down from `2` to `1` at a step from
case A. -/
theorem fullDirectrixExample_codim :
    logJacobianDirectrixCodim ({0, 2} : Finset (Fin 3))
        (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) = 1 ∧
      logJacobianFullDirectrixCodim ({0, 2} : Finset (Fin 3))
        (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) = 2 ∧
      logJacobianDirectrixCodim
        (blowupDivisor ({0, 2} : Finset (Fin 3)) 1 (0 : Fin 3 → ZMod 2))
        (cleanPart 2 (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2))) = 1 ∧
      logJacobianFullDirectrixCodim
        (blowupDivisor ({0, 2} : Finset (Fin 3)) 1 (0 : Fin 3 → ZMod 2))
        (cleanPart 2 (X 1 * X 2 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2))) = 1 := sorry

end LogJacobianFullDirectrix

section AbhyankarSubfield

open IsLocalRing TensorProduct

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

variable (k) in
/-- The element `z_i` of `K` as an element of the subfield `k(z)` of `K` that the family `z` generates over `k`. -/
def adjoinRangeElem {ι : Type*} (z : ι → K) (i : ι) : IntermediateField.adjoin k (Set.range z) :=
  ⟨z i, IntermediateField.subset_adjoin k _ (Set.mem_range_self i)⟩

section SumElim

variable {ι κ : Type*} [Fintype ι] {V : ValuationSubring K}

/-- `Singularity/Valuation/AbhyankarSubfield.lean`: the restriction of `V` to `k(x, y)` is a monomial valuation over `k(y)` in the `x_i`, if the values of the `x_i` are independent over `ℤ`. -/
theorem isMonomialValuation_comap_adjoin_sumElim {x : ι → K} {y : κ → K}
    (hx0 : ∀ i, x i ≠ 0)
    (hx : ∀ a : ι → ℤ, V.valuation (laurentMonomial x a) = 1 → a = 0) :
    IsMonomialValuation
      (IntermediateField.adjoin k (Set.range fun j => adjoinRangeElem k (Sum.elim x y) (.inr j)))
      (V.comap (algebraMap (IntermediateField.adjoin k (Set.range (Sum.elim x y))) K))
      (fun i => adjoinRangeElem k (Sum.elim x y) (.inl i)) := sorry

omit [Fintype ι] in
/-- `Singularity/Valuation/AbhyankarSubfield.lean`: the restriction of `V` to `k(x, y)` is trivial on `k(y)`, if the residues of the `y_j` are algebraically independent over `k`. -/
theorem mem_comap_adjoin_sumElim_of_residue [Algebra k V] [IsScalarTower k V K] {x : ι → K}
    {y : κ → V} (hy : AlgebraicIndependent k fun j => residue V (y j)) :
    ∀ c ∈ IntermediateField.adjoin k
        (Set.range fun j => adjoinRangeElem k (Sum.elim x fun j => (y j : K)) (.inr j)),
      c ∈ V.comap (algebraMap
        (IntermediateField.adjoin k (Set.range (Sum.elim x fun j => (y j : K)))) K) := sorry

/-- `Singularity/Valuation/AbhyankarSubfield.lean`: the elements `x, y` are algebraically independent over `k`. -/
theorem algebraicIndependent_sumElim_of_laurentMonomial [Algebra k V] [IsScalarTower k V K]
    {x : ι → K} {y : κ → V} (hx0 : ∀ i, x i ≠ 0)
    (hx : ∀ a : ι → ℤ, V.valuation (laurentMonomial x a) = 1 → a = 0)
    (hy : AlgebraicIndependent k fun j => residue V (y j)) :
    AlgebraicIndependent k (Sum.elim x fun j => (y j : K)) := sorry

end SumElim

section Abhyankar

variable {V : ValuationSubring K} [Algebra k V] [IsScalarTower k V K]

/-- `Singularity/Valuation/AbhyankarSubfield.lean`: for an Abhyankar valuation, `K` is a finite extension of `k(x, y)` (Volume 3, proof of Theorem 2.2.2). -/
theorem finiteDimensional_adjoin_sumElim_of_isAbhyankarValuation (hK : IsFunctionField k K)
    (hV : IsAbhyankarValuation k V) {ι κ : Type*} [Fintype ι] [Fintype κ] {x : ι → K}
    {y : κ → V} (hx0 : ∀ i, x i ≠ 0)
    (hx : ∀ a : ι → ℤ, V.valuation (laurentMonomial x a) = 1 → a = 0)
    (hy : AlgebraicIndependent k fun j => residue V (y j))
    (hr : Module.rank ℚ (ℚ ⊗[ℤ] Additive V.ValueGroupˣ) = Fintype.card ι)
    (ht : Algebra.trdeg k (ResidueField V) = Fintype.card κ) :
    FiniteDimensional
      (IntermediateField.adjoin k (Set.range (Sum.elim x fun j => (y j : K)))) K := sorry

/-- `Singularity/Valuation/AbhyankarSubfield.lean`: the choice of the monomial subfield `k(x, y)` of an Abhyankar valuation (Volume 5, proof of Theorem 2.2.1, with values that are independent over `ℤ`). -/
theorem IsAbhyankarValuation.exists_isMonomialValuation_comap (hK : IsFunctionField k K)
    (hV : IsAbhyankarValuation k V) :
    ∃ (r t : ℕ) (x : Fin r → K) (y : Fin t → V),
      Module.rank ℚ (ℚ ⊗[ℤ] Additive V.ValueGroupˣ) = r ∧
      Algebra.trdeg k (ResidueField V) = t ∧
      (∀ i, x i ≠ 0) ∧
      (∀ a : Fin r → ℤ, V.valuation (laurentMonomial x a) = 1 → a = 0) ∧
      AlgebraicIndependent k (fun j => residue V (y j)) ∧
      AlgebraicIndependent k (Sum.elim x fun j => (y j : K)) ∧
      FiniteDimensional
        (IntermediateField.adjoin k (Set.range (Sum.elim x fun j => (y j : K)))) K ∧
      (∀ c ∈ IntermediateField.adjoin k
          (Set.range fun j => adjoinRangeElem k (Sum.elim x fun j => (y j : K)) (.inr j)),
        c ∈ V.comap (algebraMap
          (IntermediateField.adjoin k (Set.range (Sum.elim x fun j => (y j : K)))) K)) ∧
      IsMonomialValuation
        (IntermediateField.adjoin k
          (Set.range fun j => adjoinRangeElem k (Sum.elim x fun j => (y j : K)) (.inr j)))
        (V.comap (algebraMap
          (IntermediateField.adjoin k (Set.range (Sum.elim x fun j => (y j : K)))) K))
        (fun i => adjoinRangeElem k (Sum.elim x fun j => (y j : K)) (.inl i)) := sorry

end Abhyankar

/-- `Singularity/Valuation/AbhyankarSubfield.lean`: an Abhyankar valuation has local uniformization if the residue extension over its monomial subfield `k(x, y)` is separable of degree `[K : k(x, y)]` (Volume 5, Theorem 2.2.1 in the case of one extension with `e = d = 1`). -/
theorem hasLocalUniformization_of_isAbhyankarValuation_of_finrank_residueField_eq
    (hK : IsFunctionField k K) {Γ₀ Γ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) [Algebra k v.valuationSubring]
    [IsScalarTower k v.valuationSubring K] (hv : IsAbhyankarValuation k v.valuationSubring)
    {ι κ : Type*} [Fintype ι] [Fintype κ] {x : ι → K} {y : κ → v.valuationSubring}
    (hx0 : ∀ i, x i ≠ 0) (hx : ∀ a : ι → ℤ, v (laurentMonomial x a) = 1 → a = 0)
    (hy : AlgebraicIndependent k fun j => residue v.valuationSubring (y j))
    (hr : Module.rank ℚ (ℚ ⊗[ℤ] Additive v.valuationSubring.ValueGroupˣ) = Fintype.card ι)
    (ht : Algebra.trdeg k (ResidueField v.valuationSubring) = Fintype.card κ)
    (v₀ : Valuation
      (IntermediateField.adjoin k (Set.range (Sum.elim x fun j => (y j : K)))) Γ₀)
    [v₀.HasExtension v]
    [Algebra.IsSeparable (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring)]
    (hf : Module.finrank (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring) =
      Module.finrank
        (IntermediateField.adjoin k (Set.range (Sum.elim x fun j => (y j : K)))) K) :
    HasLocalUniformization k v.valuationSubring := sorry

end AbhyankarSubfield

section LogJacobianType

open MvPolynomial Finsupp Module

section LemmaA

variable {σ k : Type*} [Field k] (p : ℕ) [CharP k p] {Δ : Finset σ} {g : MvPolynomial σ k}

/-- `Singularity/Invariant/LogJacobianType.lean`: the order of `g = x^r G` is `|r| + ord G`. -/
theorem ord_eq_degree_divisorExponent_add (Δ : Finset σ) (g : MvPolynomial σ k) :
    ord g = degree (divisorExponent Δ g) + ord (residualFactor Δ g) := sorry

/-- `Singularity/Invariant/LogJacobianType.lean`: Lemma 3.10.1 of Volume 7, Section 3.10 of the
handbook. For a clean `g ≠ 0`, the order of `Θ₀(g)` is `ord g`. -/
theorem idealOrd_logJacobianTangent_eq_ord (hg : g ≠ 0) (hc : IsClean p g) :
    idealOrd (logJacobianTangent Δ g) = ord g := sorry

/-- `Singularity/Invariant/LogJacobianType.lean`: Lemma 3.10.1 of Volume 7, Section 3.10 of the
handbook, the form with the residual order. -/
theorem idealOrd_logJacobianTangent_eq_degree_add_residualOrderAlong (hg : g ≠ 0)
    (hc : IsClean p g) :
    idealOrd (logJacobianTangent Δ g) =
      degree (divisorExponent Δ g) + residualOrderAlong Δ p g := sorry

/-- `Singularity/Invariant/LogJacobianType.lean`: Lemma 3.10.1 of Volume 7, Section 3.10 of the
handbook. Case A is the type `0`. -/
theorem idealOrd_logJacobianTangent_eq_degree_add_iff (hg : g ≠ 0) (hc : IsClean p g) :
    idealOrd (logJacobianTangent Δ g) = degree (divisorExponent Δ g) + logJacobianOrder Δ g ↔
      logJacobianOrder Δ g = residualOrderAlong Δ p g := sorry

/-- `Singularity/Invariant/LogJacobianType.lean`: Lemma 3.10.1 of Volume 7, Section 3.10 of the
handbook. Case B is the type `1`. -/
theorem idealOrd_logJacobianTangent_eq_degree_add_add_one_iff (hg : g ≠ 0) (hc : IsClean p g) :
    idealOrd (logJacobianTangent Δ g) =
        degree (divisorExponent Δ g) + logJacobianOrder Δ g + 1 ↔
      logJacobianOrder Δ g + 1 = residualOrderAlong Δ p g := sorry

end LemmaA

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- `Singularity/Invariant/LogJacobianType.lean`: Theorem 3.10.3 of Volume 7, Section 3.10 of the
handbook, the form `d' ≤ d`. -/
theorem residualOrderAlong_cleanPart_le_of_forall_eq_zero (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m)
    (ht : ∀ i ∈ Δ, i ≠ j → t i = 0) :
    residualOrderAlong (blowupDivisor Δ j t) p g' ≤ residualOrderAlong Δ p g := sorry

/-- `Singularity/Invariant/LogJacobianType.lean`: Theorem 3.10.3 of Volume 7, Section 3.10 of the
handbook, the form with `τ_ρ` if `d' = d`. -/
theorem logJacobianDirectrixCodim_le_cleanPart_of_residualOrderAlong_eq (hg : g ≠ 0)
    (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m)
    (ht : ∀ i ∈ Δ, i ≠ j → t i = 0)
    (hdd : residualOrderAlong (blowupDivisor Δ j t) p g' = residualOrderAlong Δ p g) :
    logJacobianDirectrixCodim Δ g ≤
      logJacobianDirectrixCodim (blowupDivisor Δ j t) (cleanPart p g') := sorry

end LogJacobianType

section LogJacobianKangaroo

open MvPolynomial Finsupp

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]

/-- `Singularity/Invariant/LogJacobianKangaroo.lean`: a step of a point blowup where `ρ` stays
`m`. -/
def RhoStep (m : ℕ) (P Q : Finset σ × MvPolynomial σ k) : Prop :=
  ∃ (j : σ) (t : σ → k) (g' : MvPolynomial σ k), P.2 ≠ 0 ∧ IsClean p P.2 ∧
    (p : ℕ∞) ≤ ord P.2 ∧ pointChart j t P.2 = X j ^ p * g' ∧
    Q = (blowupDivisor P.1 j t, cleanPart p g') ∧
    logJacobianOrder P.1 P.2 = m ∧ logJacobianOrder Q.1 Q.2 = m

/-- `Singularity/Invariant/LogJacobianKangaroo.lean`: a point of case B. -/
def IsLogJacobianCaseB (P : Finset σ × MvPolynomial σ k) : Prop :=
  idealOrd (logJacobianTangent P.1 P.2) =
    ((degree (divisorExponent P.1 P.2) : ℕ) : ℕ∞) + logJacobianOrder P.1 P.2 + 1

variable {p}

/-- `Singularity/Invariant/LogJacobianKangaroo.lean`: one step into a point of case B
(Proposition 3.8.2 of Volume 7 of the handbook). -/
theorem logJacobianDirectrixCodim_le_of_rhoStep {m : ℕ} {P Q : Finset σ × MvPolynomial σ k}
    (hs : RhoStep p m P Q) (hB : IsLogJacobianCaseB Q) :
    logJacobianDirectrixCodim P.1 P.2 ≤ logJacobianDirectrixCodim Q.1 Q.2 := sorry

/-- `Singularity/Invariant/LogJacobianKangaroo.lean`: the last step of a kangaroo path. -/
theorem logJacobianDirectrixCodim_le_fullDirectrixCodim_of_rhoStep {m : ℕ}
    {P Q : Finset σ × MvPolynomial σ k} (hs : RhoStep p m P Q) :
    logJacobianDirectrixCodim P.1 P.2 ≤ logJacobianFullDirectrixCodim Q.1 Q.2 := sorry

/-- `Singularity/Invariant/LogJacobianKangaroo.lean`: `τ_ρ` along a run of points of case B
(Proposition 3.11.1 of Volume 7, Section 3.11 of the handbook). -/
theorem logJacobianDirectrixCodim_le_of_reflTransGen {m : ℕ}
    {P Q : Finset σ × MvPolynomial σ k}
    (h : Relation.ReflTransGen (fun A B => RhoStep p m A B ∧ IsLogJacobianCaseB B) P Q) :
    logJacobianDirectrixCodim P.1 P.2 ≤ logJacobianDirectrixCodim Q.1 Q.2 := sorry

/-- `Singularity/Invariant/LogJacobianKangaroo.lean`: the kangaroo path (Proposition 3.11.1 of
Volume 7, Section 3.11 of the handbook). -/
theorem logJacobianDirectrixCodim_le_fullDirectrixCodim_of_reflTransGen {m : ℕ}
    {P Q R : Finset σ × MvPolynomial σ k}
    (h : Relation.ReflTransGen (fun A B => RhoStep p m A B ∧ IsLogJacobianCaseB B) P Q)
    (hQR : RhoStep p m Q R) :
    logJacobianDirectrixCodim P.1 P.2 ≤ logJacobianFullDirectrixCodim R.1 R.2 := sorry

end LogJacobianKangaroo

section LogJacobianCaseAForms

open MvPolynomial Finsupp

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ]

/-- `Singularity/Invariant/LogJacobianKangaroo.lean`: a point of case A. -/
def IsLogJacobianCaseA (P : Finset σ × MvPolynomial σ k) : Prop :=
  idealOrd (logJacobianTangent P.1 P.2) =
    ((degree (divisorExponent P.1 P.2) : ℕ) : ℕ∞) + logJacobianOrder P.1 P.2

/-- `Singularity/Invariant/LogJacobianCaseAForms.lean`: the form `E_i F = r_i F + x_i ∂_i F`. -/
noncomputable def caseAForm (Δ : Finset σ) (g : MvPolynomial σ k) (m : ℕ) (i : σ) :
    MvPolynomial σ k :=
  (divisorExponent Δ g i : k) • homogeneousComponent m (residualFactor Δ g) +
    X i * pderiv i (homogeneousComponent m (residualFactor Δ g))

omit [Fintype σ] in
/-- `Singularity/Invariant/LogJacobianCaseAForms.lean`: the forms of `H` in case A (Lemma 3.11.4
of Volume 7, Section 3.11 of the handbook). -/
theorem logJacobianDirectrix_eq_iInf_caseAForm {Δ : Finset σ} {g : MvPolynomial σ k} {m : ℕ}
    (hρ : logJacobianOrder Δ g = m) (hA : IsLogJacobianCaseA (Δ, g)) :
    logJacobianDirectrix Δ g = ⨅ i ∈ Δ, directrix (caseAForm Δ g m i) := sorry

end LogJacobianCaseAForms

section LogJacobianKangarooSmall

open MvPolynomial Finsupp

section KillVar

variable {σ k : Type*} [Field k] [DecidableEq σ]

/-- `Singularity/Invariant/LogJacobianKangarooSmall.lean`: a polynomial with constant term `0` and
with the full space as directrix is `0`. -/
theorem eq_zero_of_directrix_eq_top {F : MvPolynomial σ k} (h0 : constantCoeff F = 0)
    (h : directrix F = ⊤) : F = 0 := sorry

end KillVar

section Small

variable {σ k : Type*} [Field k] [Fintype σ]

/-- `Singularity/Invariant/LogJacobianKangarooSmall.lean`: if `ρ = 0`, then `τ_ρ = 0`. -/
theorem logJacobianDirectrixCodim_eq_zero_of_order_eq_zero {Δ : Finset σ}
    {g : MvPolynomial σ k} (hρ : logJacobianOrder Δ g = 0) :
    logJacobianDirectrixCodim Δ g = 0 := sorry

/-- `Singularity/Invariant/LogJacobianKangarooSmall.lean`: in case A with `ρ ≥ 1`, `τ_ρ ≥ 1`. -/
theorem one_le_logJacobianDirectrixCodim_of_caseA {Δ : Finset σ} {g : MvPolynomial σ k} {m : ℕ}
    (hρ : logJacobianOrder Δ g = m) (hm : m ≠ 0) (hA : IsLogJacobianCaseA (Δ, g)) :
    1 ≤ logJacobianDirectrixCodim Δ g := sorry

/-- `Singularity/Invariant/LogJacobianKangarooSmall.lean`: the comparison if `τ_ρ(P) ≤ 1`. -/
theorem logJacobianDirectrixCodim_le_of_le_one {m : ℕ} {P R : Finset σ × MvPolynomial σ k}
    (hP : logJacobianOrder P.1 P.2 = m) (hR : logJacobianOrder R.1 R.2 = m)
    (hA : IsLogJacobianCaseA R) (h1 : logJacobianDirectrixCodim P.1 P.2 ≤ 1) :
    logJacobianDirectrixCodim P.1 P.2 ≤ logJacobianDirectrixCodim R.1 R.2 := sorry

end Small

section Path

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ]

/-- `Singularity/Invariant/LogJacobianKangarooSmall.lean`: the kangaroo path if `τ_ρ(P_0) ≤ 1`
(Proposition 3.11.5 of Volume 7, Section 3.11 of the handbook). -/
theorem kangarooPath_of_codim_le_one {p : ℕ} [CharP k p] {m : ℕ}
    {P Q R : Finset σ × MvPolynomial σ k}
    (hPQ : Relation.TransGen (fun A B => RhoStep p m A B ∧ IsLogJacobianCaseB B) P Q)
    (hQR : RhoStep p m Q R) (hR : IsLogJacobianCaseA R)
    (h1 : logJacobianDirectrixCodim P.1 P.2 ≤ 1) :
    logJacobianDirectrixCodim P.1 P.2 ≤ logJacobianDirectrixCodim R.1 R.2 := sorry

end Path

end LogJacobianKangarooSmall

section LogJacobianKangarooCounterexample

open MvPolynomial Finsupp

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]

/-- `Singularity/Invariant/LogJacobianKangaroo.lean`: the kangaroo path conjecture (Conjecture
3.11.3 of Volume 7, Section 3.11 of the handbook). -/
def KangarooPathConjecture : Prop :=
  ∀ (m : ℕ) (P Q R : Finset σ × MvPolynomial σ k), IsLogJacobianCaseA P →
    Relation.TransGen (fun A B => RhoStep p m A B ∧ IsLogJacobianCaseB B) P Q →
    RhoStep p m Q R → IsLogJacobianCaseA R →
    logJacobianDirectrixCodim P.1 P.2 ≤ logJacobianDirectrixCodim R.1 R.2

/-- `Singularity/Invariant/LogJacobianKangarooCounterexample.lean`: the kangaroo path conjecture
is false for `p = 2`, three variables and the field `ZMod 2` (Example 3.11.6 of Volume 7, Section
3.11 of the handbook). -/
theorem KangarooCounterexample.not_kangarooPathConjecture :
    ¬ KangarooPathConjecture (σ := Fin 3) (k := ZMod 2) 2 := sorry

end LogJacobianKangarooCounterexample

end Singularity
