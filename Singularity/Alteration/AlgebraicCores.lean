/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Etale.Field
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.CharP.Basic
import Singularity.Alteration.TraceSplitting
import Singularity.Alteration.GaloisDegree
import Singularity.Alteration.Induction

/-!
# Degrees, splittings and group actions for alterations

This file proves the algebraic cores of several results of Volume 8 of the handbook. It reuses
`Singularity.exists_leftInverse_algebraMap_of_isUnit_finrank` (Proposition 1.3.2),
`Singularity.not_dvd_finrank_fixedField_sylow` (Lemma 3.2.2) and
`Singularity.isField_tensorProduct_of_isDomain` (Lemma 2.3.5). No statement on schemes,
sheaves or cohomology is proved.

## Main results

* Proposition 1.2.3: `isSeparable_of_finrank_eq_one` says that an extension of degree 1 is
  separable. `finrank_eq_one_comp_of_finrank_eq_one` says that a composite of two extensions of
  degree 1 has degree 1 and is separable. Chow's lemma, the normalization of the curve and its
  regularity are not proved.
* Proposition 1.3.4: `bijective_algebraMap_of_finrank_eq_one` (degree 1 means birational),
  `finrank_eq_one_of_algHom` and `isEmpty_algHom_of_one_lt_finrank` (if `d > 1`, there is no
  map of function fields `L → K` over `K`). The scheme statements are not proved.
* Degrees of composites: `finrank_comp_alteration`, `[M : K] = [L : K] [M : L]`.
* Proposition 1.3.6: `exists_leftInverse_tensorOneMap` (a left inverse `s` of `A → B` gives
  the left inverse `id ⊗ s` of `M → M ⊗[A] B`), its affine case
  `exists_leftInverse_tensorOneMap_of_isUnit_finrank`, and `isSplitMono_map_of_leftInverse`
  (a functor maps a split injection of modules to a split monomorphism). The identification
  of the cohomology of `X'` with that of `φ_* φ^* F` and the gluing are not proved.
* Proposition 1.3.8: `trace_leftInverse_of_isUnit` and `exists_leftInverse_algebraMap_of_free`:
  for a finite free algebra of rank `d` with `d` a unit, `d⁻¹ Tr` is a left inverse of the
  structure map. Étale sheaves and étale cohomology are not treated.
* Proposition 3.1.7: `exists_eq_tmul_one_of_forall_fixed` and `galTensorAction_tmul_one` (the
  invariants of `Γ = Gal(L/K)` acting on `F ⊗[K] L` by `1 ⊗ γ` are `F`),
  `finrank_tensorProduct_eq_card_gal` (`[F ⊗[K] L : F] = |Γ|`), and
  `isField_tensorProduct_of_isDomain'` (a domain `F ⊗[K] L` is a field). The scheme part,
  namely the generic fibre, the closure `X'` and the action on it, is not proved.
* Lemma 2.2.9: `isGalois_and_finrank_fixedPoints` (Artin: a field with a faithful action of a
  finite group `H` is Galois of degree `|H|` over the invariants) and
  `card_group_eq_card_components_mul` (`|G| = |components| · |H|` for a transitive action).
  The torsor property of the level structures and the identification `k(W)^H = k(U)` are not
  proved.
* Proposition 2.2.6: `exists_prime_three_le_ne_zero`, the choice of a prime `ℓ ≥ 3` invertible
  in `k`. The rest of the proof, which uses Hypothesis 2.2.4, is not proved.
* Example 2.2.3: `fourPoints_counts` (the stability numbers and the genus of the fibre over
  `λ = 0`) and `fourPoints_chart` (the strict transforms of `x = 0` and `x = λ` in the chart
  `x = λ t` are `t = 0` and `t = 1`). The blowup itself is not constructed.
* Lemma 2.4.1: `not_three_disjoint_of_card_le_two`, the counting step: three pairwise disjoint
  nonempty sets of components through a point with at most two components do not exist. The
  geometry of the lemma is not proved.
* Proposition 3.2.3: `not_dvd_finrank_fixedField_sylow_of_isPurelyInseparable` (the degree
  `[k(X')^P : k(X)]` is prime to `ℓ` when `k(X')^G / k(X)` is purely inseparable) and
  `finrank_eq_card_mul_finrank_fixedField` (`[L' : K] = |P| · [L'^P : K]`). The existence of the
  quotient `X'/P` is not proved.
* Corollary 3.2.5: `not_dvd_finrank_tower_iff`, a degree in a tower is prime to `ℓ` if and only
  if both factors are. Gabber's theorem 3.2.4 is not proved.

Lemmas 2.3.3 and 2.3.4 are not treated in this file: their content is general position and
Bertini arguments, and they have no honest algebraic core of the kinds above.
-/

open Module

universe u

namespace Singularity

/-! ### Propositions 1.2.3 and 1.3.4: extensions of degree one -/

section DegreeOne

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- An extension of degree 1 is trivial: the map `K → L` is bijective. -/
theorem bijective_algebraMap_of_finrank_eq_one (h : finrank K L = 1) :
    Function.Bijective (algebraMap K L) := by
  refine ⟨(algebraMap K L).injective, fun x => ?_⟩
  have hx : x ∈ (⊥ : Subalgebra K L) := by
    rw [Subalgebra.bot_eq_top_of_finrank_eq_one h]
    exact Algebra.mem_top
  exact Algebra.mem_bot.mp hx

/-- Volume 8, Proposition 1.2.3 of the handbook, the last step: an extension of degree 1 is
separable. So a modification is generically étale. -/
theorem isSeparable_of_finrank_eq_one (h : finrank K L = 1) : Algebra.IsSeparable K L :=
  AlgEquiv.Algebra.isSeparable
    (AlgEquiv.ofBijective (Algebra.ofId K L) (bijective_algebraMap_of_finrank_eq_one h))

/-- Volume 8, Proposition 1.3.4 of the handbook, the field part. A `K`-algebra map `L → K`
forces `[L : K] = 1`. This is the case of an open subset of `X₁` that maps isomorphically onto
an open subset of `X`: then the function field `L` of `X₁` maps to the function field `K` of
`X` over `K`. -/
theorem finrank_eq_one_of_algHom (f : L →ₐ[K] K) : finrank K L = 1 := by
  have hinj : Function.Injective f.toLinearMap := f.toRingHom.injective
  have : Module.Finite K L := Module.Finite.of_injective f.toLinearMap hinj
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_self] at h1
  have h2 : 0 < finrank K L := Module.finrank_pos
  omega

/-- Volume 8, Proposition 1.3.4 of the handbook, second claim, in field form: if `[L : K] > 1`,
then there is no `K`-algebra map `L → K`. -/
theorem isEmpty_algHom_of_one_lt_finrank (h : 1 < finrank K L) : IsEmpty (L →ₐ[K] K) :=
  ⟨fun f => by rw [finrank_eq_one_of_algHom f] at h; exact lt_irrefl 1 h⟩

/-- The degree of a composite is the product of the degrees: `[M : K] = [L : K] [M : L]`.
This is the degree of a composite of two alterations. -/
theorem finrank_comp_alteration (M : Type*) [Field M] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] : finrank K M = finrank K L * finrank L M :=
  (Module.finrank_mul_finrank K L M).symm

/-- Volume 8, Proposition 1.2.3 of the handbook, in field form: a composite of two
modifications has degree 1, so it is separable. -/
theorem finrank_eq_one_comp_of_finrank_eq_one {M : Type*} [Field M] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] (h1 : finrank K L = 1) (h2 : finrank L M = 1) :
    finrank K M = 1 ∧ Algebra.IsSeparable K M := by
  have h : finrank K M = 1 := by rw [← Module.finrank_mul_finrank K L M, h1, h2]
  exact ⟨h, isSeparable_of_finrank_eq_one h⟩

end DegreeOne

/-! ### Proposition 1.3.6: tensoring a split injection -/

section SplitTensor

open TensorProduct

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (M : Type*) [AddCommGroup M] [Module A M]

variable (A B) in
/-- The map `M → M ⊗[A] B`, `m ↦ m ⊗ 1`. -/
noncomputable def tensorOneMap : M →ₗ[A] M ⊗[A] B := (TensorProduct.mk A M B).flip 1

@[simp]
theorem tensorOneMap_apply (m : M) : tensorOneMap A B M m = m ⊗ₜ 1 := rfl

/-- Volume 8, Proposition 1.3.6 of the handbook, the module part. Let `s : B → A` be an
`A`-linear left inverse of `A → B`. Then `id ⊗ s`, followed by `M ⊗[A] A ≅ M`, is a left
inverse of `m ↦ m ⊗ 1`. -/
theorem rid_comp_lTensor_comp_tensorOneMap {s : B →ₗ[A] A}
    (hs : ∀ a : A, s (algebraMap A B a) = a) :
    (TensorProduct.rid A M).toLinearMap ∘ₗ s.lTensor M ∘ₗ tensorOneMap A B M =
      LinearMap.id := by
  ext m
  have h1 : s 1 = 1 := by simpa using hs 1
  simp only [LinearMap.comp_apply, tensorOneMap_apply, LinearEquiv.coe_coe,
    LinearMap.lTensor_tmul, TensorProduct.rid_tmul, h1, one_smul, LinearMap.id_apply]

/-- Volume 8, Proposition 1.3.6 of the handbook, the module part: `m ↦ m ⊗ 1` has a left
inverse, so it is injective. -/
theorem exists_leftInverse_tensorOneMap {s : B →ₗ[A] A}
    (hs : ∀ a : A, s (algebraMap A B a) = a) :
    ∃ r : M ⊗[A] B →ₗ[A] M, r ∘ₗ tensorOneMap A B M = LinearMap.id ∧
      Function.Injective (tensorOneMap A B M) := by
  have e := rid_comp_lTensor_comp_tensorOneMap M hs
  refine ⟨(TensorProduct.rid A M).toLinearMap ∘ₗ s.lTensor M, e, ?_⟩
  exact Function.LeftInverse.injective
    (g := (TensorProduct.rid A M).toLinearMap ∘ₗ s.lTensor M) fun m => LinearMap.congr_fun e m

/-- Volume 8, Proposition 1.3.6 of the handbook, the affine case. Let `A` be a normal domain with
field of fractions `K`, let `L/K` be finite of degree `d`, and let `B ⊆ L` be an `A`-subalgebra
of elements integral over `A`. If `d` is a unit of `A`, then for each `A`-module `M` the map
`M → M ⊗[A] B` is split injective. The left inverse is `id ⊗ d⁻¹ Tr_{L/K}`, from
`Singularity.exists_leftInverse_algebraMap_of_isUnit_finrank`. -/
theorem exists_leftInverse_tensorOneMap_of_isUnit_finrank {A K L : Type*} [CommRing A]
    [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    {B : Subalgebra A L} (hB : B ≤ integralClosure A L) (hd : IsUnit (finrank K L : A))
    (M : Type*) [AddCommGroup M] [Module A M] :
    ∃ r : M ⊗[A] B →ₗ[A] M, r ∘ₗ tensorOneMap A B M = LinearMap.id := by
  obtain ⟨s, hs⟩ := exists_leftInverse_algebraMap_of_isUnit_finrank (K := K) hB hd
  obtain ⟨r, hr, -⟩ := exists_leftInverse_tensorOneMap M hs
  exact ⟨r, hr⟩

open CategoryTheory in
/-- Volume 8, Proposition 1.3.6 of the handbook, the last step: each functor, for example a
cohomology functor, maps a split injection to a split monomorphism. -/
theorem isSplitMono_map_of_leftInverse {A' : Type u} [CommRing A'] {D : Type*}
    [Category D] (F : ModuleCat.{u} A' ⥤ D) {X Y : ModuleCat.{u} A'}
    (ι : X ⟶ Y) (r : Y ⟶ X) (h : ι ≫ r = 𝟙 X) : IsSplitMono (F.map ι) := by
  have : IsSplitMono ι := ⟨⟨⟨r, h⟩⟩⟩
  infer_instance

end SplitTensor

/-! ### Proposition 1.3.8: the normalized trace -/

section NormalizedTrace

variable {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S] [Algebra R S] [Module.Free R S]

/-- Volume 8, Proposition 1.3.8 of the handbook, the algebraic core. Let `S` be a finite free
`R`-algebra of rank `d`, the ring of a finite locally free morphism of degree `d` over an
affine open subset. If `d` is a unit of `R`, then `d⁻¹ Tr_{S/R}` is an `R`-linear left inverse of
`R → S`. -/
theorem trace_leftInverse_of_isUnit (hd : IsUnit (finrank R S : R)) (a : R) :
    ((↑hd.unit⁻¹ : R) • Algebra.trace R S) (algebraMap R S a) = a := by
  rw [LinearMap.smul_apply, Algebra.trace_algebraMap, nsmul_eq_mul, smul_eq_mul, ← mul_assoc,
    hd.val_inv_mul, one_mul]

/-- Volume 8, Proposition 1.3.8 of the handbook, the algebraic core: `R → S` is a split
injection of `R`-modules. -/
theorem exists_leftInverse_algebraMap_of_free (hd : IsUnit (finrank R S : R)) :
    ∃ ρ : S →ₗ[R] R, ∀ a : R, ρ (algebraMap R S a) = a :=
  ⟨_, trace_leftInverse_of_isUnit hd⟩

end NormalizedTrace

/-! ### Proposition 3.1.7: the group of the base passes to the total space -/

section BaseChangeGalois

open TensorProduct

variable (K L F : Type*) [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F]

/-- The action of `γ ∈ Gal(L/K)` on `F ⊗[K] L` by `1 ⊗ γ`. -/
noncomputable def galTensorAction (γ : Gal(L/K)) : F ⊗[K] L →ₗ[K] F ⊗[K] L :=
  γ.toLinearMap.lTensor F

/-- The `K`-linear map `L → ∏_γ L`, `b ↦ (γ b - b)_γ`. Its kernel is `K` when `L/K` is
Galois. -/
noncomputable def galDiff : L →ₗ[K] (Gal(L/K) → L) :=
  LinearMap.pi fun γ => γ.toLinearMap - LinearMap.id

theorem exact_algebraMap_galDiff [IsGalois K L] [FiniteDimensional K L] :
    Function.Exact (Algebra.linearMap K L) (galDiff K L) := by
  intro b
  constructor
  · intro h
    have hb : ∀ γ : Gal(L/K), γ b = b := fun γ => by
      have := congrFun h γ
      simpa [galDiff, sub_eq_zero] using this
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed b).mpr hb)
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    funext γ
    simp [galDiff]

/-- Volume 8, Proposition 3.1.7 of the handbook, the invariants. Let `L/K` be finite Galois with
group `Γ`, and let `F` be a field over `K`. If `x ∈ F ⊗[K] L` is fixed by `1 ⊗ γ` for each
`γ ∈ Γ`, then `x = y ⊗ 1` for some `y ∈ F`. So `(F ⊗[K] L)^Γ = F`. -/
theorem exists_eq_tmul_one_of_forall_fixed [IsGalois K L] [FiniteDimensional K L]
    (x : F ⊗[K] L) (hx : ∀ γ : Gal(L/K), galTensorAction K L F γ x = x) :
    ∃ y : F, x = y ⊗ₜ 1 := by
  classical
  have hdiff : (galDiff K L).lTensor F x = 0 := by
    apply (TensorProduct.piRight K K F (fun _ : Gal(L/K) => L)).injective
    rw [map_zero]
    funext γ
    have e : (LinearMap.proj γ ∘ₗ (TensorProduct.piRight K K F
        (fun _ : Gal(L/K) => L)).toLinearMap ∘ₗ (galDiff K L).lTensor F) =
        galTensorAction K L F γ - LinearMap.id := by
      apply TensorProduct.ext'
      intro f b
      simp [galTensorAction, galDiff, TensorProduct.tmul_sub]
    have := congrArg (fun φ => φ x) e
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, hx γ,
      sub_self] at this
    simpa using this
  obtain ⟨z, hz⟩ := (Module.Flat.lTensor_exact F (exact_algebraMap_galDiff K L) x).mp hdiff
  refine ⟨TensorProduct.rid K F z, ?_⟩
  rw [← hz]
  have e : (Algebra.linearMap K L).lTensor F =
      (TensorProduct.mk K F L).flip 1 ∘ₗ (TensorProduct.rid K F).toLinearMap := by
    apply TensorProduct.ext'
    intro f k
    simp [Algebra.algebraMap_eq_smul_one]
  rw [e]
  rfl

/-- Volume 8, Proposition 3.1.7 of the handbook, the converse: `y ⊗ 1` is fixed by `1 ⊗ γ`. -/
theorem galTensorAction_tmul_one (γ : Gal(L/K)) (y : F) :
    galTensorAction K L F γ (y ⊗ₜ 1) = y ⊗ₜ 1 := by
  simp [galTensorAction]

/-- Volume 8, Proposition 3.1.7 of the handbook, the degree: `[F ⊗[K] L : F] = [L : K] = |Γ|`.
-/
theorem finrank_tensorProduct_eq_card_gal [IsGalois K L] [FiniteDimensional K L] :
    finrank F (F ⊗[K] L) = Nat.card Gal(L/K) := by
  rw [Module.finrank_baseChange, IsGalois.card_aut_eq_finrank]

/-- Volume 8, Proposition 3.1.7 of the handbook, part 1, in algebraic form: if `F ⊗[K] L` is a
domain, it is a field. This is `Singularity.isField_tensorProduct_of_isDomain` of Lemma 2.3.5. -/
theorem isField_tensorProduct_of_isDomain' [FiniteDimensional K L] [IsDomain (F ⊗[K] L)] :
    IsField (F ⊗[K] L) :=
  isField_tensorProduct_of_isDomain K L F

end BaseChangeGalois

/-! ### Lemma 2.2.9: the Galois group of a component of the level cover -/

section LevelCover

/-- Volume 8, Lemma 2.2.9 of the handbook, the field part (Artin's theorem). Let a finite group
`H` act faithfully on a field `E` by ring automorphisms, as `H` acts on `k(W)`. Then `E` is
Galois over the fixed field `E^H`, of degree `|H|`. -/
theorem isGalois_and_finrank_fixedPoints (H E : Type*) [Group H] [Fintype H] [Field E]
    [MulSemiringAction H E] [FaithfulSMul H E] :
    IsGalois (FixedPoints.subfield H E) E ∧
      finrank (FixedPoints.subfield H E) E = Fintype.card H :=
  ⟨inferInstance, FixedPoints.finrank_eq_card H E⟩

/-- Volume 8, Lemma 2.2.9 of the handbook, the counting part. Let `G` act transitively on the
set `C` of connected components of `L`, and let `H` be the stabilizer of the component `W`. Then
`|G| = |C| · |H|`. So the degree `|G|` of `L → U` is the number of components times the degree
`|H|` of `W → U`. -/
theorem card_group_eq_card_components_mul {G C : Type*} [Group G] [MulAction G C]
    [MulAction.IsPretransitive G C] (W : C) :
    Nat.card G = Nat.card C * Nat.card (MulAction.stabilizer G W) := by
  rw [← MulAction.index_stabilizer_of_transitive G W, Subgroup.index_mul_card]

end LevelCover

/-! ### Proposition 2.2.6: the choice of the prime `ℓ` -/

/-- Volume 8, Proposition 2.2.6 of the handbook, the first step. For a field `k` of
characteristic `p`, there is a prime `ℓ ≥ 3` that is invertible in `k`. -/
theorem exists_prime_three_le_ne_zero (k : Type*) [Field k] (p : ℕ) [CharP k p] :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 3 ≤ ℓ ∧ (ℓ : k) ≠ 0 := by
  obtain ⟨ℓ, hle, hℓ⟩ := Nat.exists_infinite_primes (p + 3)
  refine ⟨ℓ, hℓ, by omega, fun h => ?_⟩
  rw [CharP.cast_eq_zero_iff k p] at h
  rcases hℓ.eq_one_or_self_of_dvd p h with h1 | h1
  · subst h1
    have h0 := CharP.cast_eq_zero k 1
    rw [Nat.cast_one] at h0
    exact one_ne_zero h0
  · omega

/-! ### Example 2.2.3: the counts for four points on a line -/

section FourPoints

/-- The number `2g - 2 + n` of a curve of genus `g` with `n` special points. A component is
stable when this number is positive. -/
def stabilityNumber (g n : ℕ) : ℤ := 2 * (g : ℤ) - 2 + n

/-- The arithmetic genus of a nodal curve whose components have genera `gs`, with `e` nodes
and connected dual graph: `∑ gᵢ + e - v + 1`, where `v` is the number of components. -/
def nodalGenus (gs : List ℕ) (e : ℕ) : ℤ := (gs.sum : ℤ) + e - gs.length + 1

/-- Volume 8, Example 2.2.3 of the handbook, the counts. The pair `(g, n) = (0, 4)` is stable.
The fibre over `λ = 0` has two components of genus 0 with one node, so it has genus 0. Each
component has two marked points and the node, so 3 special points, and it is stable. -/
theorem fourPoints_counts :
    0 < stabilityNumber 0 4 ∧ nodalGenus [0, 0] 1 = 0 ∧ 2 + 1 = 3 ∧
      0 < stabilityNumber 0 (2 + 1) := by
  simp [stabilityNumber, nodalGenus]

/-- Volume 8, Example 2.2.3 of the handbook, the chart of the blowup. In the chart `x = λ t`
of the blowup of `(0, 0)`, the section `x = 0` is `λ t` and the section `x = λ` is
`λ (t - 1)`. After removing the factor `λ` of the exceptional curve, the strict transforms are
`t = 0` and `t = 1`, and they meet the exceptional curve `λ = 0` at two different points. -/
theorem fourPoints_chart (k : Type*) [CommRing k] [Nontrivial k] :
    let lam : MvPolynomial (Fin 2) k := MvPolynomial.X 0
    let t : MvPolynomial (Fin 2) k := MvPolynomial.X 1
    lam * t - lam = lam * (t - 1) ∧ (0 : k) ≠ 1 := by
  exact ⟨by ring, zero_ne_one⟩

end FourPoints

/-! ### Lemma 2.4.1: three branches through a node -/

/-- Volume 8, Lemma 2.4.1 of the handbook, the counting step. At most two components of a
nodal curve pass through a point `c`. So three pairwise disjoint nonempty sets of components
through `c` do not exist. In the proof these are the components of `pr₁(T_α)`, `pr₁(T_β')`
and `pr₁(T_γ)` through `c`. -/
theorem not_three_disjoint_of_card_le_two {ι : Type*} [DecidableEq ι] {S a b c : Finset ι}
    (hS : S.card ≤ 2) (ha : a.Nonempty) (hb : b.Nonempty) (hc : c.Nonempty) (haS : a ⊆ S)
    (hbS : b ⊆ S) (hcS : c ⊆ S) (hab : Disjoint a b) (hac : Disjoint a c) (hbc : Disjoint b c) :
    False := by
  have h1 : (a ∪ b ∪ c).card = a.card + b.card + c.card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hac, hbc⟩),
      Finset.card_union_of_disjoint hab]
  have h2 : (a ∪ b ∪ c).card ≤ S.card :=
    Finset.card_le_card (Finset.union_subset (Finset.union_subset haS hbS) hcS)
  have := ha.card_pos
  have := hb.card_pos
  have := hc.card_pos
  omega

/-! ### Proposition 3.2.3 and Corollary 3.2.5: degrees prime to `ℓ` -/

section PrimeToEll

open IntermediateField

/-- Volume 8, Proposition 3.2.3 of the handbook, the degree. Let `L'/M` be finite Galois, let
`P` be an `ℓ`-Sylow subgroup of `Gal(L'/M)`, and let `M/K` be finite purely inseparable, with
`K` of exponential characteristic `q ≠ ℓ`. Then `ℓ ∤ [L'^P : K]`. Here `L' = k(X')`,
`M = k(X')^G`, `K = k(X)`, and `[L'^P : K]` is the degree of `X'/P → X`. This uses
`Singularity.not_dvd_finrank_fixedField_sylow`; the case `q = 1` is reduced to it with a prime
different from `ℓ` and exponent 0. -/
theorem not_dvd_finrank_fixedField_sylow_of_isPurelyInseparable {K M L' : Type*} [Field K]
    [Field M] [Field L'] [Algebra K M] [Algebra M L'] [Algebra K L'] [IsScalarTower K M L']
    [FiniteDimensional K M] [IsPurelyInseparable K M] [FiniteDimensional M L'] [IsGalois M L']
    {ℓ q : ℕ} [Fact ℓ.Prime] [ExpChar K q] (hqℓ : q ≠ ℓ) (P : Sylow ℓ Gal(L'/M)) :
    ¬ ℓ ∣ finrank K (fixedField (P : Subgroup Gal(L'/M))) := by
  obtain ⟨e, he⟩ := IsPurelyInseparable.finrank_eq_pow K M q
  rcases expChar_is_prime_or_one K q with hq | hq
  · exact not_dvd_finrank_fixedField_sylow hq hqℓ he P
  · subst hq
    rw [one_pow] at he
    have hℓ : ℓ.Prime := Fact.out
    by_cases h2 : ℓ = 2
    · exact not_dvd_finrank_fixedField_sylow (p := 3) (e := 0) Nat.prime_three (by omega)
        (by rw [he, pow_zero]) P
    · exact not_dvd_finrank_fixedField_sylow (p := 2) (e := 0) Nat.prime_two (Ne.symm h2)
        (by rw [he, pow_zero]) P

/-- Volume 8, Proposition 3.2.3 of the handbook, the multiplicativity. The degree of
`X' → X'/P` is `|P|`, so `[L' : K] = |P| · [L'^P : K]`. -/
theorem finrank_eq_card_mul_finrank_fixedField {K M L' : Type*} [Field K] [Field M] [Field L']
    [Algebra K M] [Algebra M L'] [Algebra K L'] [IsScalarTower K M L'] [FiniteDimensional M L']
    (P : Subgroup Gal(L'/M)) :
    finrank K L' = Nat.card P * finrank K (fixedField P) := by
  have h1 := Module.finrank_mul_finrank M (fixedField P) L'
  rw [finrank_fixedField_eq_card] at h1
  rw [← Module.finrank_mul_finrank K M L', ← Module.finrank_mul_finrank K M (fixedField P),
    ← h1]
  ring

/-- Volume 8, Corollary 3.2.5 of the handbook, the degrees. For a prime `ℓ` and a tower
`K ⊆ M ⊆ L`, the degree `[L : K]` is prime to `ℓ` if and only if `[M : K]` and `[L : M]` are.
So a composite of alterations of degree prime to `ℓ` has degree prime to `ℓ`, and a factor of
such an alteration has degree prime to `ℓ`. -/
theorem not_dvd_finrank_tower_iff {K M L : Type*} [Field K] [Field M] [Field L] [Algebra K M]
    [Algebra M L] [Algebra K L] [IsScalarTower K M L] {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ¬ ℓ ∣ finrank K L ↔ ¬ ℓ ∣ finrank K M ∧ ¬ ℓ ∣ finrank M L := by
  rw [← Module.finrank_mul_finrank K M L, hℓ.dvd_mul, not_or]

end PrimeToEll

end Singularity
