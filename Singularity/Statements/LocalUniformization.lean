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
* `HasRegularCenter`: there is an affine model that contains a given set, on which the center of `V` is a regular point.
* `HasLocalUniformization`: for each finite subset `s` of `V`, there is an affine model that contains `s`, on which the center of `V` is a regular point.
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

Definition 4.1.1 of Volume 3 of the handbook uses models that are varieties: a valuation `v` of `K/k` has local uniformization if for each model `X` of `K/k` on which `v` has a center, there are a model `X'` and a proper birational morphism `X' → X` such that the center of `v` on `X'` is a regular point. Here the models are affine. `HasRegularCenter k V S` asks for a finitely generated `k`-subalgebra `A` of `K` with fraction field `K`, `S ⊆ A` and `A ⊆ V`, such that the localization of `A` at the prime `m_V ∩ A` is a regular local ring. `HasLocalUniformization k V` asks for `HasRegularCenter k V s` for each finite subset `s` of `V`. This is the form of Zariski [Zar40]. Knaf-Kuhlmann [KK05] state it in the same form: for each finite set `Z ⊆ 𝒪_v` there is a model on which `v` is centered at a regular point `x` with `Z ⊆ 𝒪_{X,x}`. A regular local ring is the class `IsRegularLocalRing` of Mathlib, as in `Singularity/Statements/Basic.lean`.

The affine form is equivalent to Definition 4.1.1. First assume Definition 4.1.1, and let `s` be a finite subset of `V`. Choose elements `t_1, ..., t_n` that generate `K` over `k` as a field. If `t_i` is not in `V`, then `t_i⁻¹` is in `V`, and we replace `t_i` by `t_i⁻¹`. Let `A₀ = k[s, t_1, ..., t_n]`. Then `A₀ ⊆ V`, so `V` has a center on the model `Spec A₀`. Definition 4.1.1 gives a proper birational morphism `X' → Spec A₀` such that the center `x'` of `V` on `X'` is a regular point. Take an affine open `Spec A` of `X'` that contains `x'`. Then `A` is finitely generated over `k`, its fraction field is `K`, and `A ⊆ 𝒪_{X',x'} ⊆ V`. Also `s ⊆ A₀ ⊆ A`, because `X'` maps to `Spec A₀`. The point `x'` is the prime `m_V ∩ A`, and its local ring is the localization of `A` at this prime. So `HasRegularCenter k V s` holds.

Conversely, assume `HasLocalUniformization k V`, and let `X` be a model on which `V` has a center `x`. Take an affine open `Spec A₀` of `X` that contains `x`, and let `s` be a finite set of generators of `A₀` over `k`. Then `s ⊆ A₀ ⊆ 𝒪_{X,x} ⊆ V`. The hypothesis gives an affine model `A` with `A₀ ⊆ A ⊆ V` on which the center of `V` is regular. Let `Y` be a projective closure of `Spec A`: embed `Spec A` in `𝔸^m` by a set of generators, and take the closure in `ℙ^m`. Let `X'` be the closure of the image of `Spec K` in `X ×_k Y`. The projection `X' → X` is proper, because `Y` is proper over `k`, and it is birational. The center of `V` on `X'` maps to the center `x` on `X` and to the center of `V` on `Y`, and this center lies in `Spec A` because `A ⊆ V`. So the center of `V` on `X'` lies in the open set `Spec A₀ ×_k Spec A`. In this open set, `X'` is the spectrum of the image of `A₀ ⊗_k A` in `K`, and this image is `A` because `A₀ ⊆ A`. Thus the local ring of `X'` at the center of `V` is the localization of `A` at `m_V ∩ A`, a regular local ring.

The condition `s ⊆ A` matters. Without it, the definition asks only that the center of `V` is regular on one affine model. `HasLocalUniformization k V` implies this weak form (`Singularity.Fidelity.exists_regularCenter_of_hasLocalUniformization`). The converse is not known in general: a regular center on one model does not give a regular center on a model that dominates a given model `X`.

The theorem of Knaf-Kuhlmann [KK05] needs the hypothesis that the residue field of `V` is separable over `k`. The residue field of an Abhyankar valuation is finitely generated over `k`, so separable means separably generated (`Algebra.IsSeparablyGenerated`, Stacks tag 030O). The hypothesis holds when `k` is perfect, in particular in characteristic 0.

In the theorem of Temkin [Tem13, Theorem 1.3.2], a finite purely inseparable extension `L` of `K` is taken, and the valuation `V` has a unique extension `W` to `L`. The extension `L` depends on the model: for each affine model `Spec A₀` of `K` with `A₀ ⊆ V`, there are `L` and an affine model `X'` of `K` over `Spec A₀` such that `W` is centered on a smooth point of the normalization of `X'` in `L`. This normalization is an affine model of `L/k` that contains `A₀`. So the statement takes a finite subset `s` of `V` first. Then it asks for `L`, and for an extension `W` of `V`, that is, a valuation subring `W` of `L` with `W ∩ K = V` (`W.comap (algebraMap K L) = V`), such that `W` has a regular center on an affine model of `L/k` that contains the image of `s` (`HasRegularCenter`). The model of `L` is a `k`-algebra, with the structure of `k`-algebra on `L` that comes from `K`.

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

/-- The valuation subring `V` of `K` has a regular center on an affine model of `K/k` that contains the set `S`: there is an affine model `A` of `K/k` with `S ⊆ A` and `A ⊆ V` such that the localization of `A` at the center `m_V ∩ A` is a regular local ring. -/
def HasRegularCenter (V : ValuationSubring K) (S : Set K) : Prop :=
  ∃ (A : Subalgebra k K) (h : ∀ a : A, (a : K) ∈ V), IsAffineModel A ∧ S ⊆ (A : Set K) ∧
    IsRegularLocalRing (Localization.AtPrime (valuationCenter V A h))

/-- The valuation subring `V` of `K` has local uniformization over `k`: for each finite subset `s` of `V`, there is an affine model `A` of `K/k` with `s ⊆ A ⊆ V` such that the localization of `A` at the center `m_V ∩ A` is a regular local ring.

The docstring of the file explains why this affine form is equivalent to Definition 4.1.1 of Volume 3 of the handbook, the form with models that are varieties. If `V` has local uniformization over `k`, then `V` contains `k`, because `k ⊆ A ⊆ V` for the model `A` of the empty set. -/
def HasLocalUniformization (V : ValuationSubring K) : Prop :=
  ∀ s : Finset K, (∀ x ∈ s, x ∈ V) → HasRegularCenter k V s

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

/-- Inseparable local uniformization (Temkin [Tem13, Theorem 1.3.2], node SG0000001G): let `K` be a function field over a field `k`, let `V` be a valuation of `K/k`, and let `s` be a finite subset of `V`. Then there are a finite purely inseparable extension `L` of `K` and an extension `W` of `V` to `L` such that `W` has a regular center on an affine model of `L/k` that contains `s`.

The extension `L` depends on `s`. In characteristic 0 the extension `L` is `K`, and this is the theorem of Zariski [Zar40]. This file does not prove the statement. -/
def localUniformization_inseparable : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K], IsFunctionField k K →
    ∀ (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K] (s : Finset K), (∀ x ∈ s, x ∈ V) →
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra k L) (_ : IsScalarTower k K L),
        FiniteDimensional K L ∧ IsPurelyInseparable K L ∧ ∃ W : ValuationSubring L,
          W.comap (algebraMap K L) = V ∧ HasRegularCenter k W (algebraMap K L '' s)

/-- Local uniformization holds for function fields of transcendence degree `n` over fields of characteristic `p`: let `k` be a field with `CharP k p`, let `K` be a function field over `k` with `trdeg_k K = n`, and let `V` be a valuation of `K/k`. Then `V` has local uniformization.

The field `k` is any field with `CharP k p`. It need not be perfect. -/
def LocalUniformizationInDim (p n : ℕ) : Prop :=
  ∀ (k K : Type u) [Field k] [CharP k p] [Field K] [Algebra k K], IsFunctionField k K →
    Algebra.trdeg k K = n → ∀ (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K],
      HasLocalUniformization k V

/-- Local uniformization in dimension 3 (Cossart-Piltant, node SG0000001F): each valuation of a function field of transcendence degree 3 over a field of characteristic `p > 0` has local uniformization.

[CP08] and [CP09] prove this when `[k : k ^ p]` is finite, for example when `k` is perfect. The general case follows from the resolution of quasi-excellent schemes of dimension 3 of [CP19]: resolve the given model, and take an affine open neighbourhood of the center of the valuation on the resolution. This file does not prove the statement. -/
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
