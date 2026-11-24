/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.Main
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.TranscendentalSeparable
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Local uniformization

This file states local uniformization of valuations of function fields, the known cases and two open cases. The text is in Volume 3 of the handbook (nodes SG0000001E, SG0000001F, SG0000001G, SG0000001H and SG0000001J). The statements are definitions of propositions. This file does not prove them.

## Main definitions

* `IsFunctionField`: a finitely generated field extension `K` of `k`.
* `IsAffineModel`: a finitely generated `k`-subalgebra `A` of `K` with fraction field `K`.
* `valuationCenter`: the center `m_V ∩ A` of a valuation subring `V` on such a model.
* `HasLocalUniformization`: there is an affine model on which the center of `V` is a regular point.
* `IsAbhyankarValuation`: equality holds in the inequality of Abhyankar (node SG0000000Y).
* `LocalUniformizationInDim`: local uniformization for function fields of a given transcendence degree over fields of a given characteristic.
* `localUniformization_abhyankar`: the theorem of Knaf-Kuhlmann [KK05] (node SG0000001E).
* `localUniformization_inseparable`: the theorem of Temkin [Tem13] (node SG0000001G).
* `localUniformization_three`: the theorem of Cossart-Piltant in dimension 3 (node SG0000001F).
* `LocalUniformizationFour`: local uniformization in dimension 4 and characteristic `p` (node SG0000001H). This is open.
* `resolution_of_localUniformization_four`: local uniformization gives resolution in dimension 4 (node SG0000001J). This is open.

## The choices

A valuation of `K/k` is a valuation subring `V` of `K` together with a structure `Algebra k V` such that `k → V → K` is the map `k → K` (`IsScalarTower k V K`). Such a structure exists if and only if `V` contains the image of `k`, and then it is unique, because `V → K` is injective. A valuation is trivial on `k` if and only if its valuation subring contains `k`, so this is the usual notion. The structure on `V` gives the structure of a `k`-algebra on the residue field of `V`. The inequality of Abhyankar in `Singularity/Valuation/Abhyankar.lean` (`Singularity.abhyankar_inequality`) uses the same hypotheses, and `IsAbhyankarValuation` uses the same expression. A statement file imports only Mathlib and other statement files, so the expression is written here again.

The field `K` is a function field over `k` if it is finitely generated over `k` as a field extension: `(⊤ : IntermediateField k K).FG`. Mathlib also has `Algebra.EssFiniteType k K`, and `IntermediateField.fg_top_iff` shows that the two notions agree.

The usual form of local uniformization (Zariski [Zar40]) asks for a projective integral model `X` of `K/k` such that the center `x` of `V` on `X` is a regular point, that is, the local ring `𝒪_{X,x}` is a regular local ring. Here the model is affine. `HasLocalUniformization k V` asks for a finitely generated `k`-subalgebra `A` of `K` with fraction field `K` and `A ⊆ V` such that the localization of `A` at the prime `m_V ∩ A` is a regular local ring. The two forms are equivalent. If `X` is a projective model and `x` is the center of `V`, then take an affine open `Spec A` of `X` that contains `x`. Then `A` is finitely generated over `k`, its fraction field is `K`, `A ⊆ 𝒪_{X,x} ⊆ V`, the point `x` is the prime `m_V ∩ A`, and `𝒪_{X,x}` is the localization of `A` at this prime. Conversely, let `A` be such an algebra, with generators `a_1, ..., a_n`. Embed `Spec A` in `𝔸^n` and take the closure `X` of `Spec A` in `ℙ^n`. Then `Spec A` is an open subscheme of `X`, because `Spec A` is closed in `𝔸^n`. The valuation `V` has a unique center on `X`, because `X` is proper and separated. Since `A ⊆ V`, this center is the point `m_V ∩ A` of `Spec A`, and its local ring is the localization of `A` at this point. A regular local ring is the class `IsRegularLocalRing` of Mathlib, as in `Singularity/Statements/Basic.lean`.

The theorem of Knaf-Kuhlmann [KK05] needs the hypothesis that the residue field of `V` is separable over `k`. The residue field of an Abhyankar valuation is finitely generated over `k`, so separable means separably generated (`Algebra.IsSeparablyGenerated`, Stacks tag 030O). The hypothesis holds when `k` is perfect, in particular in characteristic 0.

In the theorem of Temkin [Tem13], a finite purely inseparable extension `L` of `K` is taken, and the valuation `V` has a unique extension `W` to `L`. The statement asks for an extension `W` of `V`, that is, a valuation subring `W` of `L` with `W ∩ K = V` (`W.comap (algebraMap K L) = V`). The model of `L` is a `k`-algebra, with the structure of `k`-algebra on `L` that comes from `K`.

The patching statement `resolution_of_localUniformization_four` takes local uniformization in each transcendence degree at most 4 as the hypothesis, because a variety of dimension at most 4 can have components of smaller dimension. Local uniformization in transcendence degree at most 3 is known in characteristic `p > 0` (Abhyankar in transcendence degree at most 2, Cossart-Piltant in transcendence degree 3). Thus, as a statement of mathematics, the hypothesis is the same as local uniformization in transcendence degree 4.

## References

* [CP08] V. Cossart and O. Piltant, *Resolution of singularities of threefolds in positive characteristic I*, J. Algebra 320 (2008).
* [CP09] V. Cossart and O. Piltant, *Resolution of singularities of threefolds in positive characteristic II*, J. Algebra 321 (2009).
* [CP19] V. Cossart and O. Piltant, *Resolution of singularities of arithmetical threefolds*, J. Algebra 529 (2019).
* [KK05] H. Knaf and F.-V. Kuhlmann, *Abhyankar places admit local uniformization in any characteristic*, Ann. Sci. École Norm. Sup. 38 (2005).
* [Tem13] M. Temkin, *Inseparable local uniformization*, J. Algebra 373 (2013).
* [Zar40] O. Zariski, *Local uniformization on algebraic varieties*, Ann. of Math. 41 (1940).
* [Zar44] O. Zariski, *Reduction of the singularities of algebraic three dimensional varieties*, Ann. of Math. 45 (1944).
-/

open IsLocalRing TensorProduct

universe u

namespace Singularity

section Model

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/-- The field `K` is a function field over `k`: it is finitely generated over `k` as a field extension. The transcendence degree can be any finite number. -/
def IsFunctionField : Prop :=
  (⊤ : IntermediateField k K).FG

variable {k K}

/-- The `k`-subalgebra `A` of `K` is an affine model of `K/k`: it is finitely generated over `k`, and `K` is the fraction field of `A`. Then `Spec A` is an integral affine variety over `k` with function field `K`. -/
def IsAffineModel (A : Subalgebra k K) : Prop :=
  A.FG ∧ IsFractionRing A K

/-- The center of the valuation subring `V` on the affine model `Spec A`, where `A ⊆ V`: the prime ideal `m_V ∩ A` of `A`, the inverse image of the maximal ideal of `V`. -/
def valuationCenter (V : ValuationSubring K) (A : Subalgebra k K) (h : ∀ a : A, (a : K) ∈ V) :
    Ideal A :=
  (maximalIdeal V).comap ((A.val : A →+* K).codRestrict V h)

/-- The center of a valuation subring on an affine model is a prime ideal, because it is the inverse image of a maximal ideal. -/
instance isPrime_valuationCenter (V : ValuationSubring K) (A : Subalgebra k K)
    (h : ∀ a : A, (a : K) ∈ V) : (valuationCenter V A h).IsPrime :=
  Ideal.IsPrime.comap _

variable (k)

/-- The valuation subring `V` of `K` has local uniformization over `k`: there is an affine model `A` of `K/k` with `A ⊆ V` such that the localization of `A` at the center `m_V ∩ A` is a regular local ring.

The docstring of the file explains why this affine form is equivalent to the form with a projective model. If `V` has local uniformization over `k`, then `V` contains `k`, because `k ⊆ A ⊆ V`. -/
def HasLocalUniformization (V : ValuationSubring K) : Prop :=
  ∃ (A : Subalgebra k K) (h : ∀ a : A, (a : K) ∈ V), IsAffineModel A ∧
    IsRegularLocalRing (Localization.AtPrime (valuationCenter V A h))

/-- The valuation subring `V` of `K` is an Abhyankar valuation of `K/k`: equality holds in the inequality of Abhyankar (node SG0000000Y). The rational rank of the value group of `V`, plus the transcendence degree of the residue field of `V` over `k`, is the transcendence degree of `K` over `k`.

The rational rank of a group `Γ` is the dimension over `ℚ` of `ℚ ⊗[ℤ] Γ`. The expression is the left side of `Singularity.abhyankar_inequality`. -/
def IsAbhyankarValuation (V : ValuationSubring K) [Algebra k V] : Prop :=
  Module.rank ℚ (ℚ ⊗[ℤ] Additive V.ValueGroupˣ) + Algebra.trdeg k (ResidueField V) =
    Algebra.trdeg k K

end Model

/-! ### The known cases -/

/-- Local uniformization of Abhyankar valuations (Knaf-Kuhlmann [KK05], node SG0000001E): let `K` be a function field over a field `k` of any characteristic, and let `V` be an Abhyankar valuation of `K/k` whose residue field is separable over `k`. Then `V` has local uniformization.

The theorem of [KK05] is stated for places of `K/k`, and a place is the same as a valuation subring. This file does not prove the statement. -/
def localUniformization_abhyankar : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K], IsFunctionField k K →
    ∀ (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K],
      IsAbhyankarValuation k V → Algebra.IsSeparablyGenerated k (ResidueField V) →
        HasLocalUniformization k V

/-- Inseparable local uniformization (Temkin [Tem13], node SG0000001G): let `K` be a function field over a field `k`, and let `V` be a valuation of `K/k`. Then there is a finite purely inseparable extension `L` of `K` such that the extension `W` of `V` to `L` has local uniformization over `k`.

In characteristic 0 the extension `L` is `K`, and this is the theorem of Zariski [Zar40]. This file does not prove the statement. -/
def localUniformization_inseparable : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K], IsFunctionField k K →
    ∀ (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K],
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra k L) (_ : IsScalarTower k K L),
        FiniteDimensional K L ∧ IsPurelyInseparable K L ∧
          ∃ W : ValuationSubring L, W.comap (algebraMap K L) = V ∧ HasLocalUniformization k W

/-- Local uniformization holds for function fields of transcendence degree `n` over fields of characteristic `p`: let `k` be a field with `CharP k p`, let `K` be a function field over `k` with `trdeg_k K = n`, and let `V` be a valuation of `K/k`. Then `V` has local uniformization.

The field `k` is any field with `CharP k p`. It need not be perfect. -/
def LocalUniformizationInDim (p n : ℕ) : Prop :=
  ∀ (k K : Type u) [Field k] [CharP k p] [Field K] [Algebra k K], IsFunctionField k K →
    Algebra.trdeg k K = n → ∀ (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K],
      HasLocalUniformization k V

/-- Local uniformization in dimension 3 (Cossart-Piltant, node SG0000001F): each valuation of a function field of transcendence degree 3 over a field of characteristic `p > 0` has local uniformization.

[CP08] and [CP09] prove this when `[k : k ^ p]` is finite, for example when `k` is perfect. The general case follows from the resolution of quasi-excellent schemes of dimension 3 of [CP19]: resolve a projective model, and take the center of the valuation on the resolution. This file does not prove the statement. -/
def localUniformization_three : Prop :=
  ∀ p : ℕ, p.Prime → LocalUniformizationInDim.{u} p 3

/-! ### The open cases -/

/-- Local uniformization in dimension 4 (node SG0000001H): each valuation of a function field of transcendence degree 4 over a field of characteristic `p > 0` has local uniformization. This is open. -/
def LocalUniformizationFour : Prop :=
  ∀ p : ℕ, p.Prime → LocalUniformizationInDim.{u} p 4

/-- Patching in dimension 4 (node SG0000001J): let `p` be a prime. If local uniformization holds in each transcendence degree at most 4 over fields of characteristic `p`, then each variety of dimension at most 4 over a field of characteristic `p` has a resolution (`ResolutionInDim`).

In dimension at most 3 the patching is known: Zariski [Zar44] did it in characteristic 0, and Abhyankar and Cossart-Piltant [CP08] did it in characteristic `p > 0`. In dimension 4 it is open. -/
def resolution_of_localUniformization_four : Prop :=
  ∀ p : ℕ, p.Prime → (∀ n ≤ 4, LocalUniformizationInDim.{u} p n) → ResolutionInDim.{u} p 4

end Singularity
