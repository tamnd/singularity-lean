/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.LocalUniformization
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The fundamental theorem of Zariski in dimension 4

This file states the global step of resolution of 4-folds: the fundamental theorem of Zariski `Fund_4`, the purely inseparable step of local uniformization `PILU_4`, and Theorems 3.24.4 and 3.24.5 of the handbook. The text is in Volume 9, Section 3.24 of the handbook (nodes SG000000BQ, SG000000BR, SG000000BS and SG000000BT). The statements are definitions of propositions. This file does not prove them.

## Main definitions

* `centerLocalRing`: the local ring of an affine model at the center of a valuation, as a subset of the function field.
* `IsCompleteNormalModel`: a complete normal model of a function field, as a finite set of affine models in the sense of Zariski.
* `ModelDominates`: a birational morphism of models, as domination of local rings.
* `HasRegularCenterOn`: a valuation has a regular center on a model.
* `WeakLocalUniformizationInDim`: `LU_n^-` of Definition 3.24.1.
* `AffineLocalUniformizationInDim`: `LU_n` of Definition 3.24.1.
* `PurelyInseparableLocalUniformizationInDim`: `PILU_n` of Conjecture 3.24.2 (node SG000000BR).
* `FundamentalTheoremInDim`: `Fund_n` of Conjecture 3.24.3 (node SG000000BQ).
* `IsRegularModification`, `RegularModificationInDim`: `Res_n^pr` of Section 3.24.
* `resolution_iff_weakLocalUniformization_fundamental_four`: Theorem 3.24.4 (node SG000000BS).
* `resolution_iff_pilu_fundamental_four`: Theorem 3.24.5 (node SG000000BT).

## The choices

The handbook works over an algebraically closed field `k` of characteristic `p > 0`. The statements here do the same: `[IsAlgClosed k] [CharP k p]`, with `p` a prime. A function field is `IsFunctionField k K`, and its dimension is `Algebra.trdeg k K`.

A valuation of `K/k` is a valuation subring `V` of `K` that contains the image of `k`. As in `Singularity/Statements/LocalUniformization.lean`, a regular local ring `A ⊂ K`, essentially of finite type over `k`, with fraction field `K` and dominated by `V`, is the localization of an affine model `B ⊆ V` of `K/k` at the center `m_V ∩ B`. Each such ring `A` has this form: write `A = B_q` with `B` finitely generated, then `B ⊆ A ⊆ V`, and `q = m_A ∩ B = m_V ∩ B` because `V` dominates `A`. Thus `HasRegularCenter k V ∅` is `LU_n^-` for `V`, and `HasRegularCenter k V s` for each finite subset `s` of `V` is `LU_n`.

Mathlib has no function field of a scheme over `k` as a field extension of `k` together with an identification with a given field `K`, and no projective morphisms. Thus `Fund_n` uses models in the sense of Zariski ([ZS60, Chapter VI, Section 17]). A model is a finite set `M` of affine models of `K/k`, the charts. Its points are the local rings `B_q` for `B ∈ M` and `q` a prime of `B`. The center of a valuation `V` on `M` is a local ring `B_q` that `V` dominates. `IsCompleteNormalModel` asks for these conditions.
* Each chart is integrally closed. Then the model is normal.
* Each valuation of `K/k` contains a chart. This is the valuative criterion of properness: each valuation has a center.
* If a valuation `V` contains two charts `A` and `A'`, then `A` is contained in the local ring of `A'` at the center of `V`. Then the local rings of `A` and `A'` at the centers of `V` are the same, so the center of `V` is unique. This is the valuative criterion of separatedness.
Such a set of charts glues to a complete normal variety with function field `K`, and each complete normal variety with function field `K` comes from such a set, its affine charts. A morphism `W → M` of such models that is the identity on `K` exists if and only if each local ring of `W` dominates a local ring of `M`. Each prime of a chart is the center of a valuation (a local domain is dominated by a valuation ring of its fraction field, [ZS60, Chapter VI, Section 4, Theorem 5]), so `ModelDominates W M` states this with valuations.

The handbook asks for projective models in `Fund_4` and projective morphisms in `Res_4^pr`. This file asks for complete models and proper morphisms. This is a simplification. With this change, the proof of Theorem 3.24.4 in the handbook stays correct. In Step 1 the projective model `W_v` is complete. In Step 4 the model `W` is complete and dominates `V_0`, so `W → V_0` is proper. In the converse, the closure of the graph of `V_0 ⇢ V_1` is complete, and a proper resolution of its normalization is a complete regular model. The forms with projective and with complete models are not known to be equivalent. In `Res_n^pr` the morphism `π : Y ⟶ X` is proper, `Y` is regular, and `π` is an isomorphism over a nonempty open set `U` of `X` whose preimage is dense. For an integral `X` this is a proper birational morphism.

In `PILU_n` the regular local ring `A` is the localization of an affine model `B` of `L` at the center of the restriction of `V` to `L`. The handbook takes `a ∈ A`. Here `a ∈ B`. This is no loss: if `a = c / s` with `c, s ∈ B` and `s` a unit of `A`, then `b s` is a `p`-th root of `c s ^ (p - 1) ∈ B`, it generates the same field `L(b)`, and `A[b s] = A[b]`. The field `L(b)` is a field `M` with an algebra structure over `L`, an element `b` with `b ^ p = a` that is not in the image of `L`, and `L(b) = M`. The conclusion is `HasRegularCenter k V S` for the set `S` of `b` and the image of `B`. Then the localization `A'` of the new model at the center of `V` contains `B` and `b`. An element of `B` outside the center of `V` on `B` is a unit of `V`, so it is a unit of `A'`, and `A[b] ⊆ A'`.

## References

* [Cut09] S. D. Cutkosky, *Resolution of singularities for 3-folds in positive characteristic*, Amer. J. Math. 131 (2009).
* [Tem13] M. Temkin, *Inseparable local uniformization*, J. Algebra 373 (2013).
* [ZS60] O. Zariski and P. Samuel, *Commutative algebra, Volume II*, 1960.
-/

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Singularity

section Model

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The local ring of the affine model `B` at the center of the valuation subring `V`, as a subset of `K`: the fractions `a / s` with `a` and `s` in `B` and `s` a unit of `V`. If `B ⊆ V`, this is the localization of `B` at the prime `m_V ∩ B`. -/
def centerLocalRing (V : ValuationSubring K) (B : Subalgebra k K) : Set K :=
  {z | ∃ a ∈ B, ∃ s ∈ B, s ≠ 0 ∧ s⁻¹ ∈ V ∧ z = a / s}

variable (k) in
/-- The set `M` of affine models of `K/k` is a complete normal model of `K` in the sense of Zariski ([ZS60, Chapter VI, Section 17]):
* `M` is finite;
* each member of `M` is an affine model of `K/k` and is integrally closed;
* each valuation of `K/k` contains a member of `M` (the model is complete);
* if a valuation `V` contains two members `A` and `A'` of `M`, then `A` is contained in the local ring of `A'` at the center of `V` (the model is separated).

The docstring of the file explains why this is the same as a complete normal variety with function field `K`. -/
def IsCompleteNormalModel (M : Set (Subalgebra k K)) : Prop :=
  M.Finite ∧ (∀ A ∈ M, IsAffineModel A ∧ IsIntegrallyClosed A) ∧
    (∀ V : ValuationSubring K, (∀ c : k, algebraMap k K c ∈ V) →
      ∃ A ∈ M, ∀ a : A, (a : K) ∈ V) ∧
    ∀ A ∈ M, ∀ A' ∈ M, ∀ V : ValuationSubring K, (∀ a : A, (a : K) ∈ V) →
      (∀ a : A', (a : K) ∈ V) → (A : Set K) ⊆ centerLocalRing V A'

/-- The model `W` dominates the model `M`: for each chart `B` of `W` and each valuation `V` that contains `B`, a chart of `M` is contained in the local ring of `B` at the center of `V`. For complete models this is a birational morphism `W → M` that is the identity on `K`. -/
def ModelDominates (W M : Set (Subalgebra k K)) : Prop :=
  ∀ B ∈ W, ∀ V : ValuationSubring K, (∀ b : B, (b : K) ∈ V) →
    ∃ A ∈ M, (A : Set K) ⊆ centerLocalRing V B

/-- The valuation subring `V` has a regular center on the model `M`: there is a chart `B ⊆ V` of `M` such that the localization of `B` at the center `m_V ∩ B` is a regular local ring. If `M` is separated, then the local rings of all charts that `V` contains are the same, so this does not depend on the chart. -/
def HasRegularCenterOn (V : ValuationSubring K) (M : Set (Subalgebra k K)) : Prop :=
  ∃ B ∈ M, ∃ h : ∀ b : B, (b : K) ∈ V,
    IsRegularLocalRing (Localization.AtPrime (valuationCenter V B h))

end Model

/-! ### Local uniformization -/

/-- `LU_n^-` of Definition 3.24.1 (node SG000000BS), over algebraically closed fields of characteristic `p`: for each function field `K` of dimension `n` over `k` and each valuation `V` of `K/k`, there is a regular local ring, essentially of finite type over `k`, with fraction field `K`, dominated by `V`. -/
def WeakLocalUniformizationInDim (p n : ℕ) : Prop :=
  ∀ (k K : Type u) [Field k] [IsAlgClosed k] [CharP k p] [Field K] [Algebra k K],
    IsFunctionField k K → Algebra.trdeg k K = n → ∀ V : ValuationSubring K,
      (∀ c : k, algebraMap k K c ∈ V) → HasRegularCenter k V ∅

/-- `LU_n` of Definition 3.24.1 (node SG000000BS), over algebraically closed fields of characteristic `p`: `LU_n^-`, and in addition the regular local ring contains a given finite subset `s` of `V`. This is `LocalUniformizationInDim p n` for algebraically closed fields. -/
def AffineLocalUniformizationInDim (p n : ℕ) : Prop :=
  ∀ (k K : Type u) [Field k] [IsAlgClosed k] [CharP k p] [Field K] [Algebra k K],
    IsFunctionField k K → Algebra.trdeg k K = n → ∀ V : ValuationSubring K,
      (∀ c : k, algebraMap k K c ∈ V) → ∀ s : Finset K, (∀ x ∈ s, x ∈ V) → HasRegularCenter k V s

/-- `PILU_n`, the purely inseparable step of local uniformization (Conjecture 3.24.2 for `n = 4`, node SG000000BR). Let `k` be algebraically closed of characteristic `p`, and let `L` be a function field of dimension `n` over `k`. Let `B` be an affine model of `L`, let `M = L(b)` with `b ^ p = a` for an element `a ∈ B` and `b ∉ L`, and let `V` be a valuation subring of `M` whose restriction to `L` contains `B` and has a regular center on `B`. Then `V` has a regular center on an affine model of `M/k` that contains `B` and `b`.

The localization `A` of `B` at the center is the regular local ring of Conjecture 3.24.2, and the hypothesis on `V` says that `V` dominates `A`. The docstring of the file explains the choice `a ∈ B`. -/
def PurelyInseparableLocalUniformizationInDim (p n : ℕ) : Prop :=
  ∀ (k L M : Type u) [Field k] [IsAlgClosed k] [CharP k p] [Field L] [Algebra k L] [Field M]
    [Algebra k M] [Algebra L M] [IsScalarTower k L M], IsFunctionField k L →
    Algebra.trdeg k L = n → ∀ (B : Subalgebra k L) (V : ValuationSubring M)
    (hB : ∀ x : B, (x : L) ∈ V.comap (algebraMap L M)), IsAffineModel B →
    IsRegularLocalRing (Localization.AtPrime (valuationCenter (V.comap (algebraMap L M)) B hB)) →
    ∀ a ∈ B, ∀ b : M, b ^ p = algebraMap L M a → b ∉ Set.range (algebraMap L M) →
      IntermediateField.adjoin L {b} = ⊤ →
        HasRegularCenter k V (insert b (algebraMap L M '' (B : Set L)))

/-- `PILU_4` (Conjecture 3.24.2, node SG000000BR) for each prime `p`. This is open. -/
def PurelyInseparableLocalUniformizationFour : Prop :=
  ∀ p : ℕ, p.Prime → PurelyInseparableLocalUniformizationInDim.{u} p 4

/-! ### The fundamental theorem -/

/-- `Fund_n`, the fundamental theorem of Zariski in dimension `n` (Conjecture 3.24.3 for `n = 4`, node SG000000BQ), over algebraically closed fields of characteristic `p`. Let `K` be a function field of dimension `n`, let `M₀` and `M₁` be complete normal models of `K`, and let `N` be the set of valuations with a regular center on `M₀` or on `M₁`. Then there is a complete normal model `W` of `K` that dominates `M₀` and `M₁`, such that each valuation in `N` has a regular center on `W`.

The handbook asks for projective models. The docstring of the file explains why this statement uses complete models. -/
def FundamentalTheoremInDim (p n : ℕ) : Prop :=
  ∀ (k K : Type u) [Field k] [IsAlgClosed k] [CharP k p] [Field K] [Algebra k K],
    IsFunctionField k K → Algebra.trdeg k K = n → ∀ M₀ M₁ : Set (Subalgebra k K),
      IsCompleteNormalModel k M₀ → IsCompleteNormalModel k M₁ →
        ∃ W : Set (Subalgebra k K), IsCompleteNormalModel k W ∧ ModelDominates W M₀ ∧
          ModelDominates W M₁ ∧ ∀ V : ValuationSubring K,
            HasRegularCenterOn V M₀ ∨ HasRegularCenterOn V M₁ → HasRegularCenterOn V W

/-- `Fund_4` (Conjecture 3.24.3, node SG000000BQ) for each prime `p`. This is open. -/
def FundamentalTheoremFour : Prop :=
  ∀ p : ℕ, p.Prime → FundamentalTheoremInDim.{u} p 4

/-! ### Resolution by a proper birational morphism -/

/-- The morphism `π : Y ⟶ X` is a regular modification of `X`: `Y` is regular, `π` is proper, and `π` is an isomorphism over a nonempty open set `U` of `X` whose preimage is dense in `Y`. For an integral scheme `X` this is a proper birational morphism with `Y` regular.

Unlike `IsResolution`, this does not ask that `π` is an isomorphism over the regular locus of `X`. -/
structure IsRegularModification {X Y : Scheme.{u}} (π : Y ⟶ X) : Prop where
  regular : IsRegularScheme Y
  proper : IsProper π
  isIso_over : ∃ U : X.Opens, (U : Set X).Nonempty ∧ IsIso (π ∣_ U) ∧ Dense (π.base ⁻¹' U)

/-- `Res_n^pr` of Section 3.24, over algebraically closed fields of characteristic `p`: each integral variety `X` of dimension `n` has a regular modification `π : Y ⟶ X`.

The handbook asks for a projective morphism. This statement asks for a proper morphism. -/
def RegularModificationInDim (p n : ℕ) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharP k p] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IsVariety X f] [IsIntegral X], topologicalKrullDim X = n →
      ∃ (Y : Scheme.{u}) (π : Y ⟶ X), IsRegularModification π

/-! ### Theorems 3.24.4 and 3.24.5 -/

/-- Theorem 3.24.4 (node SG000000BS): for each prime `p`, `LU_4^-` and `Fund_4` imply `Res_4^pr`, and `Res_4^pr` implies `LU_4` and `Fund_4`.

The proof in the handbook uses the quasi-compactness of the Zariski-Riemann space, the openness of the regular locus of an excellent scheme, normalization and Chow's lemma. This file does not prove the statement. -/
def resolution_iff_weakLocalUniformization_fundamental_four : Prop :=
  ∀ p : ℕ, p.Prime →
    (WeakLocalUniformizationInDim.{u} p 4 → FundamentalTheoremInDim.{u} p 4 →
      RegularModificationInDim.{u} p 4) ∧
    (RegularModificationInDim.{u} p 4 →
      AffineLocalUniformizationInDim.{u} p 4 ∧ FundamentalTheoremInDim.{u} p 4)

/-- Theorem 3.24.5 (node SG000000BT): for each prime `p`, `Res_4^pr` holds if and only if `PILU_4` and `Fund_4` hold.

The direction from `PILU_4` and `Fund_4` uses the theorem of Temkin (`localUniformization_inseparable`) and the descent of research note 02, Theorem 2.6. The converse direction follows from Theorem 3.24.4 (`Singularity.Fidelity.pilu_fundamental_of_resolution`). This file does not prove the statement. -/
def resolution_iff_pilu_fundamental_four : Prop :=
  ∀ p : ℕ, p.Prime → (RegularModificationInDim.{u} p 4 ↔
    PurelyInseparableLocalUniformizationInDim.{u} p 4 ∧ FundamentalTheoremInDim.{u} p 4)

end Singularity
