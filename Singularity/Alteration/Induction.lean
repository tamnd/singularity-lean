/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Alteration.Statement
import Singularity.Algebra.NodeBlowupCharts
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The reductions of the proof of the theorem of de Jong

This file proves parts of Volume 8, Lemmas 2.3.1, 2.3.2 and 2.3.5, and the algebraic cores of
Proposition 2.4.2 and Proposition 2.4.4 of the handbook. It follows [dJ96, 4.3 to 4.27].

## Main declarations

* `DeJongSolution k X f Z`: the conclusion of Theorem 1.2.1 for one pair `(X, Z)`, in the form
  of `Singularity.deJongAlteration`. The lemma `deJongAlteration_iff` says that the theorem is
  this conclusion for all pairs.
* `IsAlteration.isClosed_preimage` and `IsAlteration.preimage_ne_univ`: Lemma 2.3.1, first
  part. The inverse image of a proper closed subset under an alteration is a proper closed subset.
* `DeJongSolution.of_isAlteration`: Lemma 2.3.1, second part. If the theorem holds for
  `(X', φ⁻¹(Z))`, then it holds for `(X, Z)`.
* `exists_eq_of_isIrreducible_subset_iUnion`: the topological core of Lemma 2.3.2. An
  irreducible closed set of codimension 1 that lies in a finite union of proper irreducible
  closed sets is one of them.
* `exists_eq_biUnion_of_subset_iUnion`: a closed set whose components have codimension 1 and
  that lies in such a finite union is the union of some of the members.
* `isSncAt_span_prod_of_subset`: the local core of the last step of Lemma 2.3.2. A union of
  some components of a divisor with strict normal crossings has strict normal crossings.
* `isReduced_tensorProduct_of_isSeparable`, `finrank_tensorProduct_of_isSeparable`,
  `isSeparable_of_tensorProduct_equiv`: the algebraic core of the degree statement of Lemma
  2.3.5. The generic fibre of `φ` is `k(X) ⊗ k(Y')`. It is reduced, of degree `[k(Y') : k(Y)]`,
  and if it is a field, then it is separable over `k(X)` of this degree.
* `isField_tensorProduct_of_isDomain`: if this generic fibre is a domain, then it is a field.
* `algebraMap_bijective_of_isIntegral_of_birational`: the last step of Proposition 2.4.2 and of
  Step 5. A finite birational extension of a normal domain is trivial.
* `nodeBlowupQOneEquiv`: Proposition 2.4.4, the case `μ = 2` of the chart `t₁`. The chart
  `R[u', v', t₁, t₂'] / (u' v' - t₂')` is the polynomial ring `R[u', v', t₁]`, so it is regular.

## What is not proved

* Lemma 2.3.1 for generically étale alterations. The statement `deJongAlteration` of the
  repository has no generically étale part.
* Lemma 2.3.2 for schemes. We prove the topological part and the local part. We do not prove
  that the components of `φ⁻¹(Z)` have codimension 1 (this needs the principal ideal theorem
  for the Cartier divisor `φ*D`), and we do not glue the local statement to ideal sheaves.
* Lemmas 2.3.3 and 2.3.4. They need projective space, blowups of schemes, linear projections
  and a Bertini argument. Mathlib has none of these.
* Lemma 2.3.5 for schemes. We prove only the algebra of the generic fibre. The irreducibility of
  `Y' ×_Y X` and the stability of the properties (vi)(a) to (e) are not proved.
* Lemma 2.4.1. It is a statement on the fibres of a stable curve, and Mathlib has no curves with
  ordinary double points.
* Proposition 2.4.2 for schemes. We prove the commutative algebra of its last step. The finite
  fibres of `pr₁` and the normality of the stable curve (Serre's criterion) are not proved.
* Proposition 2.4.4 beyond the local computation for `μ = 2`. The singular locus of the chart
  `t₁` for `μ ≥ 3`, the count of the components of `Sing(X')` and the global statement are not
  proved.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace Singularity

/-! ### Lemma 2.3.1 -/

section Method

/-- The conclusion of Theorem 1.2.1 of Volume 8 for one pair `(X, Z)`, as in
`Singularity.deJongAlteration`: there are an alteration `φ : X₁ ⟶ X`, an open immersion
`j : X₁ ⟶ Xbar` over `k`, and a divisor `D` with strict normal crossings on the proper regular
integral scheme `Xbar`, whose support is `j(φ⁻¹(Z)) ∪ (Xbar \ j(X₁))`. -/
def DeJongSolution (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (Z : Set X) : Prop :=
  ∃ (X₁ Xbar : Scheme.{u}) (φ : X₁ ⟶ X) (j : X₁ ⟶ Xbar) (g : Xbar ⟶ Spec (.of k))
    (D : Xbar.IdealSheafData),
    IsAlteration φ ∧ IsOpenImmersion j ∧ j ≫ g = φ ≫ f ∧ IsIntegral Xbar ∧ IsProper g ∧
      IsRegularScheme Xbar ∧
      (D.support : Set Xbar) = j '' (φ ⁻¹' Z) ∪ (Set.range j)ᶜ ∧ IsSncDivisor D

/-- The theorem of de Jong is the statement `DeJongSolution` for all pairs `(X, Z)`. -/
theorem deJongAlteration_iff : deJongAlteration.{u} ↔
    ∀ (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsVariety X f]
      [IsIntegral X] (Z : Set X), IsClosed Z → Z ≠ Set.univ → DeJongSolution k X f Z :=
  Iff.rfl

variable {X X' : Scheme.{u}} {φ : X' ⟶ X}

/-- Lemma 2.3.1, first part: the inverse image of a closed set under an alteration is closed. -/
theorem IsAlteration.isClosed_preimage {Z : Set X} (hZ : IsClosed Z) : IsClosed (φ ⁻¹' Z) :=
  hZ.preimage φ.continuous

/-- Lemma 2.3.1, first part: the inverse image of a proper closed set under an alteration is a
proper subset. The alteration is dominant, so it maps the generic point of `X'` to the generic
point of `X`, and this point is not in `Z`. -/
theorem IsAlteration.preimage_ne_univ (hφ : IsAlteration φ) {Z : Set X} (hZ : IsClosed Z)
    (hZne : Z ≠ Set.univ) : φ ⁻¹' Z ≠ Set.univ := by
  have := hφ.integral_source
  have := hφ.integral_target
  have := hφ.dominant
  intro h
  have hmem : φ (genericPoint X') ∈ Z := by
    have : genericPoint X' ∈ φ ⁻¹' Z := h ▸ Set.mem_univ _
    exact this
  rw [apply_genericPoint_of_isDominant φ, (genericPoint_spec X).mem_closed_set_iff hZ] at hmem
  exact hZne (Set.eq_univ_of_univ_subset hmem)

/-- Lemma 2.3.1, second part: let `φ : X' ⟶ X` be an alteration. If the theorem of de Jong holds
for `(X', φ⁻¹(Z))`, with the structure morphism `φ ≫ f`, then it holds for `(X, Z)`. The new
alteration is the composite. -/
theorem DeJongSolution.of_isAlteration {k : Type u} [Field k] {f : X ⟶ Spec (.of k)}
    (hφ : IsAlteration φ) {Z : Set X} (h : DeJongSolution k X' (φ ≫ f) (φ ⁻¹' Z)) :
    DeJongSolution k X f Z := by
  obtain ⟨X₁, Xbar, ψ, j, g, D, hψ, hj, hcomm, hint, hprop, hreg, hsupp, hsnc⟩ := h
  refine ⟨X₁, Xbar, ψ ≫ φ, j, g, D, hψ.comp hφ, hj, by rw [hcomm, Category.assoc], hint, hprop,
    hreg, ?_, hsnc⟩
  rw [hsupp]
  rfl

end Method

/-! ### Lemma 2.3.2 -/

section Enlarge

variable {T : Type*} [TopologicalSpace T]

/-- The topological core of Lemma 2.3.2. Let `C` be an irreducible closed set of codimension 1:
the only irreducible closed sets that contain `C` are `C` and the whole space. If `C` lies in a
finite union of proper irreducible closed sets `Zs i`, then `C` is one of them. -/
theorem exists_eq_of_isIrreducible_subset_iUnion {ι : Type*} [Finite ι] {Zs : ι → Set T}
    (hZc : ∀ i, IsClosed (Zs i)) (hZirr : ∀ i, IsIrreducible (Zs i))
    (hZne : ∀ i, Zs i ≠ Set.univ) {C : Set T} (hC : IsIrreducible C)
    (hmax : ∀ W : Set T, IsIrreducible W → IsClosed W → C ⊆ W → W = C ∨ W = Set.univ)
    (hsub : C ⊆ ⋃ i, Zs i) : ∃ i, C = Zs i := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨z, hz, hCz⟩ := (isIrreducible_iff_sUnion_isClosed.mp hC)
    (Finset.univ.image Zs) (by simpa using hZc) (by simpa using hsub)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  refine ⟨i, ?_⟩
  rcases hmax (Zs i) (hZirr i) (hZc i) hCz with h | h
  · exact h.symm
  · exact absurd h (hZne i)

/-- The set version of Lemma 2.3.2. Let `W` be a finite union of irreducible closed sets `Cs j`
of codimension 1. If `W` lies in a finite union of proper irreducible closed sets `Zs i`, then
`W` is the union of the `Zs i` for `i` in some set `S`. -/
theorem exists_eq_biUnion_of_subset_iUnion {ι κ : Type*} [Finite ι] {Zs : ι → Set T}
    (hZc : ∀ i, IsClosed (Zs i)) (hZirr : ∀ i, IsIrreducible (Zs i))
    (hZne : ∀ i, Zs i ≠ Set.univ) {Cs : κ → Set T} (hC : ∀ j, IsIrreducible (Cs j))
    (hmax : ∀ j, ∀ W : Set T, IsIrreducible W → IsClosed W → Cs j ⊆ W →
      W = Cs j ∨ W = Set.univ)
    (hsub : (⋃ j, Cs j) ⊆ ⋃ i, Zs i) : ∃ S : Set ι, (⋃ j, Cs j) = ⋃ i ∈ S, Zs i := by
  choose e he using fun j => exists_eq_of_isIrreducible_subset_iUnion hZc hZirr hZne (hC j)
    (hmax j) ((Set.subset_iUnion Cs j).trans hsub)
  refine ⟨Set.range e, ?_⟩
  rw [Set.biUnion_range]
  exact Set.iUnion_congr he

/-- The local core of the last step of Lemma 2.3.2. Let `I` be the ideal of a divisor with
strict normal crossings at a point, generated by the product of a subset `t` of a regular system
of parameters `s`. A union of some of its components is given by the product of a subset `t'`
of `t`, and this ideal again has strict normal crossings. -/
theorem isSncAt_span_prod_of_subset {R : Type*} [CommRing R] [IsLocalRing R] {s t t' : Finset R}
    (hs : IsRegularSystemOfParameters s) (ht : t ⊆ s) (ht' : t' ⊆ t) :
    IsSncAt (Ideal.span {∏ x ∈ t', x}) :=
  ⟨s, hs, t', ht'.trans ht, rfl⟩

end Enlarge

/-! ### Lemma 2.3.5: the generic fibre -/

section GenericFibre

open TensorProduct

variable (K L E : Type*) [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]

/-- Lemma 2.3.5, the generic fibre. Let `L / K` be a finite separable extension, the extension
`k(Y') / k(Y)`, and let `E` be a field over `K`, the field `k(X)`. Then `E ⊗[K] L` is reduced. -/
theorem isReduced_tensorProduct_of_isSeparable [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsReduced (E ⊗[K] L) := by
  have : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
  exact Algebra.FormallyUnramified.isReduced_of_field E (E ⊗[K] L)

/-- Lemma 2.3.5, the generic fibre: the degree of `E ⊗[K] L` over `E` is `[L : K]`. -/
theorem finrank_tensorProduct_of_isSeparable :
    Module.finrank E (E ⊗[K] L) = Module.finrank K L :=
  Module.finrank_baseChange

/-- Lemma 2.3.5, the generic fibre: if `E ⊗[K] L` is a domain, then it is a field. This is the
case where `Y' ×_Y X` is integral. -/
theorem isField_tensorProduct_of_isDomain [FiniteDimensional K L] [IsDomain (E ⊗[K] L)] :
    IsField (E ⊗[K] L) :=
  isField_of_isIntegral_of_isField' (R := E) (Field.toIsField E)

/-- Lemma 2.3.5, the degree of `φ`. Let `L / K` be finite separable, and let `M` be a field with
an isomorphism `E ⊗[K] L ≃ M` over `E`. This is the function field `k(X')`. Then `M / E` is
separable of degree `[L : K]`. So `φ` is generically étale of degree `[k(Y') : k(Y)]`. -/
theorem isSeparable_of_tensorProduct_equiv [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {M : Type*} [Field M] [Algebra E M] (e : E ⊗[K] L ≃ₐ[E] M) :
    Algebra.IsSeparable E M ∧ Module.finrank E M = Module.finrank K L := by
  have : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
  have : Algebra.FormallyUnramified E M := Algebra.FormallyUnramified.of_equiv e
  have : Module.Finite E M := Module.Finite.equiv e.toLinearEquiv
  refine ⟨Algebra.FormallyUnramified.isSeparable E M, ?_⟩
  rw [← e.toLinearEquiv.finrank_eq]
  exact Module.finrank_baseChange

end GenericFibre

/-! ### Proposition 2.4.2: a finite birational extension of a normal domain -/

section Birational

open Polynomial

/-- The last step of Proposition 2.4.2 and of Step 5 of Section 2.3. Let `A` be an integrally
closed domain and let `B` be a domain that is integral over `A`, with `A → B` injective. Assume
that `A → B` is birational: each `b` in `B` is a fraction `a / s` of elements of `A`. Then
`A → B` is bijective. So a finite birational morphism to a normal integral scheme is an
isomorphism. -/
theorem algebraMap_bijective_of_isIntegral_of_birational {A B : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B]
    (hinj : Function.Injective (algebraMap A B))
    (hbir : ∀ b : B, ∃ a s : A, s ≠ 0 ∧ algebraMap A B s * b = algebraMap A B a) :
    Function.Bijective (algebraMap A B) := by
  refine ⟨hinj, fun b => ?_⟩
  obtain ⟨a, s, hs, hb⟩ := hbir b
  obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := A) b
  set K := FractionRing A
  have hq : aeval a (scaleRoots p s) = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.aeval_algebraMap_apply, ← hb]
    exact scaleRoots_aeval_eq_zero (by rwa [aeval_def])
  have hsK : algebraMap A K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hs)
  set x : K := algebraMap A K a / algebraMap A K s
  have hx : algebraMap A K s * x = algebraMap A K a := by
    exact mul_div_cancel₀ _ hsK
  have hpx : eval₂ (algebraMap A K) x p = 0 := by
    have h := scaleRoots_eval₂_mul (p := p) (algebraMap A K) x s
    rw [hx, ← aeval_def, Polynomial.aeval_algebraMap_apply, hq, map_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ hsK)
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := A) (K := K)
    ⟨p, hpm, hpx⟩
  have hac : s * c = a := by
    apply IsFractionRing.injective A K
    rw [map_mul, hc, hx]
  refine ⟨c, ?_⟩
  have hsB : algebraMap A B s ≠ 0 := by
    intro h
    exact hs (hinj (by rw [h, map_zero]))
  apply mul_left_cancel₀ hsB
  rw [hb, ← map_mul, hac]

end Birational

/-! ### Proposition 2.4.4: the chart `t₁` for `μ = 2` -/

section NodeChart

open MvPolynomial Singularity.Algebra

variable (R : Type*) [CommRing R]

/-- The images of the variables of `Q` in `R[u', v', t₁]`, with `t₂' ↦ u' v'`. The variables
`0, 1, 2` of `Fin 3` are `u', v', t₁`. -/
noncomputable def nodeBlowupQOneImage : NodeBlowupQVar → MvPolynomial (Fin 3) R
  | none => X 2
  | some .u => X 0
  | some .v => X 1
  | some .s₂ => X 0 * X 1

/-- The map `Q → R[u', v', t₁]` for `c = 1`, with `t₂' ↦ u' v'`. -/
noncomputable def nodeBlowupQOneHom : NodeBlowupQ (1 : R) →ₐ[R] MvPolynomial (Fin 3) R :=
  Ideal.Quotient.liftₐ _ (aeval (nodeBlowupQOneImage R)) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [nodeBlowupQOneImage])

/-- The map `Q → R[u', v', t₁]` on the variables. -/
theorem nodeBlowupQOneHom_X (i : NodeBlowupQVar) :
    nodeBlowupQOneHom R (nodeBlowupQX (1 : R) i) = nodeBlowupQOneImage R i :=
  aeval_X _ i

/-- The map `R[u', v', t₁] → Q` for `c = 1`. -/
noncomputable def nodeBlowupQOneInv : MvPolynomial (Fin 3) R →ₐ[R] NodeBlowupQ (1 : R) :=
  aeval ![nodeBlowupQX (1 : R) (some .u), nodeBlowupQX (1 : R) (some .v),
    nodeBlowupQX (1 : R) none]

/-- Proposition 2.4.4, the case `μ = 2`: if `c = 1`, the chart
`Q = R[u', v', t₁, t₂'] / (u' v' - t₂')` of the blowup is the polynomial ring `R[u', v', t₁]`.
So the chart `t₁` is regular when `R` is a polynomial ring over a field. -/
noncomputable def nodeBlowupQOneEquiv : NodeBlowupQ (1 : R) ≃ₐ[R] MvPolynomial (Fin 3) R :=
  AlgEquiv.ofAlgHom (nodeBlowupQOneHom R) (nodeBlowupQOneInv R)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i <;>
        simp only [AlgHom.comp_apply, nodeBlowupQOneInv, aeval_X, AlgHom.id_apply] <;>
        exact nodeBlowupQOneHom_X R _)
    (by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      change nodeBlowupQOneInv R (nodeBlowupQOneHom R (nodeBlowupQX (1 : R) i)) =
        nodeBlowupQX (1 : R) i
      rw [nodeBlowupQOneHom_X]
      rcases i with _ | ⟨_ | _ | _⟩
      · simp [nodeBlowupQOneInv, nodeBlowupQOneImage]
      · simp [nodeBlowupQOneInv, nodeBlowupQOneImage]
      · simp [nodeBlowupQOneInv, nodeBlowupQOneImage]
      · have h := nodeBlowupQX_rel (1 : R)
        rw [map_one, mul_one] at h
        simpa [nodeBlowupQOneInv, nodeBlowupQOneImage] using h)

end NodeChart

end Singularity
