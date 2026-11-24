/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.LocalUniformization
import Singularity.Algebra.NormalizationCharP
import Singularity.Scheme.NormalDimOne
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Local uniformization in transcendence degree at most 1

Let `k` be a field of any characteristic, and let `K` be a function field over `k` with `trdeg_k K ≤ 1`. This file proves that each valuation of `K/k` has local uniformization. This is the paragraph after Definition 4.1.1 of Volume 3 of the handbook, in the affine form of Proposition 4.1.6.

The proof has four steps. Let `V` be a valuation subring of `K` that contains `k`, and let `s` be a finite subset of `V`.

1. Choose a finite set `t` that generates `K` as a field. If an element of `t` is not in `V`, then its inverse is in `V`, and we replace the element by its inverse. Let `A₀ = k[s, t]`. Then `A₀ ⊆ V`, and `K` is the fraction field of `A₀`.
2. Let `A` be the integral closure of `A₀` in `K`. Then `A ⊆ V`, because `V` is integrally closed. By the theorem of E. Noether, `A` is a finite `A₀`-module (`Singularity.Algebra.finite_integralClosure`), so `A` is an affine model of `K/k`.
3. The dimension of `A` is at most `trdeg_k K`. Noether normalization gives a finite injective map `k[X₁, ..., Xₙ] → A`. An integral extension does not increase the dimension, so `dim A ≤ n`. The images of the `Xᵢ` in `K` are algebraically independent over `k`, so `n ≤ trdeg_k K`.
4. The localization of `A` at the center `m_V ∩ A` is a Noetherian local domain of dimension at most 1, and it is integrally closed. So it is a regular local ring (`Singularity.isRegularLocalRing_of_isIntegrallyClosed`).

## Main results

* `Singularity.ringKrullDim_le_of_isIntegral`: an integral extension does not increase the Krull dimension.
* `Singularity.ringKrullDim_le_of_trdeg_le`: the dimension of a finitely generated domain over `k` that embeds in `K` is at most `trdeg_k K`.
* `Singularity.hasLocalUniformization_of_trdeg_le_one`: local uniformization in transcendence degree at most 1.
* `Singularity.localUniformizationInDim_zero` and `Singularity.localUniformizationInDim_one`: the statements `LocalUniformizationInDim p 0` and `LocalUniformizationInDim p 1`.
-/

open IsLocalRing

universe u v

namespace Singularity

/-- An integral extension does not increase the Krull dimension: if `S` is integral over `R`, then `dim S ≤ dim R`. The map `Spec S → Spec R` is strictly monotone by incomparability. -/
theorem ringKrullDim_le_of_isIntegral (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] : ringKrullDim S ≤ ringKrullDim R := by
  refine Order.krullDim_le_of_strictMono
    (fun p : PrimeSpectrum S => (⟨p.asIdeal.under R, inferInstance⟩ : PrimeSpectrum R)) ?_
  intro p q hpq
  exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp (Ideal.IsIntegral.under_lt_under
    ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hpq))

/-- Let `A` be a finitely generated algebra over a field `k`, and let `f : A → K` be an injective map of `k`-algebras. If `trdeg_k K ≤ n`, then `dim A ≤ n`. -/
theorem ringKrullDim_le_of_trdeg_le {k : Type u} {A : Type v} {K : Type*} [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] [Field K] [Algebra k K] (f : A →ₐ[k] K)
    (hf : Function.Injective f) {n : ℕ} (h : Algebra.trdeg k K ≤ n) : ringKrullDim A ≤ n := by
  have : Nontrivial A := ⟨0, 1, fun h0 => (zero_ne_one (α := K)) (by simpa using congrArg f h0)⟩
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have : Module.Finite (MvPolynomial (Fin s) k) A := hfin
  have hdim := ringKrullDim_le_of_isIntegral (MvPolynomial (Fin s) k) A
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at hdim
  refine hdim.trans ?_
  have hind : AlgebraicIndependent k fun i : Fin s => f (g (MvPolynomial.X i)) := by
    rw [algebraicIndependent_iff_injective_aeval]
    have : MvPolynomial.aeval (fun i : Fin s => f (g (MvPolynomial.X i))) = f.comp g :=
      MvPolynomial.algHom_ext fun i => by simp
    rw [this]
    exact hf.comp hinj
  have hs := hind.lift_cardinalMk_le_trdeg
  rw [Cardinal.mk_fin, Cardinal.lift_natCast] at hs
  have hsn : s ≤ n := by
    have := hs.trans (Cardinal.lift_le.mpr h)
    rw [Cardinal.lift_natCast] at this
    exact_mod_cast this
  exact_mod_cast hsn

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- **Local uniformization in transcendence degree at most 1.** Let `K` be a function field over a field `k` of any characteristic with `trdeg_k K ≤ 1`, and let `V` be a valuation of `K/k`. Then `V` has local uniformization: for each finite subset `s` of `V`, the integral closure `A` of a suitable affine model `k[s, t] ⊆ V` is an affine model with `s ⊆ A ⊆ V`, and the localization of `A` at the center of `V` is a regular local ring. -/
theorem hasLocalUniformization_of_trdeg_le_one (hK : IsFunctionField k K)
    (htr : Algebra.trdeg k K ≤ 1) (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K] :
    HasLocalUniformization k V := by
  classical
  obtain ⟨t, ht⟩ := hK
  intro s hs
  -- Step 1: the affine model `A₀ = k[s, t']` inside `V`.
  have hk : ∀ a : k, algebraMap k K a ∈ V := fun a => by
    rw [IsScalarTower.algebraMap_apply k V K]
    exact (algebraMap k V a).2
  let Vk : Subalgebra k K := { V.toSubring.toSubsemiring with algebraMap_mem' := hk }
  set t' : Finset K := t.image fun x => if x ∈ V then x else x⁻¹
  have ht' : ∀ x ∈ t', x ∈ V := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    split_ifs with hy
    · exact hy
    · exact (V.mem_or_inv_mem y).resolve_left hy
  have hgen : IntermediateField.adjoin k (t' : Set K) = ⊤ := by
    rw [eq_top_iff, ← ht, IntermediateField.adjoin_le_iff]
    intro x hx
    by_cases hxV : x ∈ V
    · refine IntermediateField.subset_adjoin k _ (Finset.mem_coe.mpr ?_)
      exact Finset.mem_image.mpr ⟨x, Finset.mem_coe.mp hx, by simp [hxV]⟩
    · have hmem : x⁻¹ ∈ IntermediateField.adjoin k (t' : Set K) :=
        IntermediateField.subset_adjoin k _ (Finset.mem_coe.mpr
          (Finset.mem_image.mpr ⟨x, Finset.mem_coe.mp hx, by simp [hxV]⟩))
      simpa using inv_mem hmem
  set A₀ := Algebra.adjoin k ((s ∪ t' : Finset K) : Set K)
  have hA₀V : ∀ a : A₀, (a : K) ∈ V := by
    have hle : A₀ ≤ Vk := by
      refine Algebra.adjoin_le fun x hx => ?_
      rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with hx | hx
      · exact hs x hx
      · exact ht' x hx
    exact fun a => hle a.2
  have hfrac₀ : IsFractionRing A₀ K := by
    refine IsFractionRing.of_field A₀ K fun z => ?_
    have hz : z ∈ IntermediateField.adjoin k (t' : Set K) := by
      rw [hgen]
      exact IntermediateField.mem_top
    obtain ⟨x, hx, y, hy, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
    have hle : Algebra.adjoin k (t' : Set K) ≤ A₀ :=
      Algebra.adjoin_mono (Finset.coe_subset.mpr Finset.subset_union_right)
    exact ⟨⟨x, hle hx⟩, ⟨y, hle hy⟩, rfl⟩
  have hft₀ : Algebra.FiniteType k A₀ := (Subalgebra.fg_iff_finiteType A₀).mp ⟨s ∪ t', rfl⟩
  -- Step 2: the integral closure `A` of `A₀` in `K`.
  let B : Subalgebra A₀ K := integralClosure A₀ K
  let A : Subalgebra k K := B.restrictScalars k
  have hmemA : ∀ x : K, x ∈ A ↔ IsIntegral A₀ x := fun x => Iff.rfl
  have hA₀A : ∀ x ∈ A₀, x ∈ A := fun x hx =>
    (hmemA x).mpr (isIntegral_algebraMap (R := A₀) (x := (⟨x, hx⟩ : A₀)))
  have hAV : ∀ a : A, (a : K) ∈ V := by
    intro a
    let φ : A₀ →+* V := (A₀.val : A₀ →+* K).codRestrict V hA₀V
    have hint : IsIntegral V (RingHom.id K a) :=
      IsIntegral.map_of_comp_eq φ (RingHom.id K) (by ext; rfl) ((hmemA a).mp a.2)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    rw [RingHom.id_apply] at hy
    rw [← hy]
    exact y.2
  have hfinB : Module.Finite A₀ B := by
    have hfin := Singularity.Algebra.finite_integralClosure k A₀
    let e : FractionRing A₀ ≃ₐ[A₀] K := IsLocalization.algEquiv (nonZeroDivisors A₀) _ _
    have hmap := integralClosure_map_algEquiv (R := A₀) e
    have : Module.Finite A₀ ((integralClosure A₀ (FractionRing A₀)).map (e : FractionRing A₀ →ₐ[A₀] K)) :=
      Module.Finite.equiv (Subalgebra.equivMapOfInjective _ _ e.injective).toLinearEquiv
    rw [hmap] at this
    exact this
  have hftB : Algebra.FiniteType k B := Algebra.FiniteType.trans (S := A₀) hft₀ inferInstance
  have hftA : Algebra.FiniteType k A := hftB
  have hfracA : IsFractionRing A K := by
    refine IsFractionRing.of_field A K fun z => ?_
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := A₀) z
    exact ⟨⟨x, hA₀A x x.2⟩, ⟨y, hA₀A y y.2⟩, rfl⟩
  refine ⟨A, hAV, ⟨(Subalgebra.fg_iff_finiteType A).mpr hftA, hfracA⟩,
    fun x hx => hA₀A x (Algebra.subset_adjoin (Finset.mem_coe.mpr
      (Finset.mem_union_left t' (Finset.mem_coe.mp hx)))), ?_⟩
  -- Steps 3 and 4: the local ring at the center is a normal Noetherian domain of dimension at most 1.
  set P := valuationCenter V A hAV
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hicB : IsIntegrallyClosed B := integralClosure.isIntegrallyClosedOfFiniteExtension K
  have hicA : IsIntegrallyClosed A := hicB
  have : IsIntegrallyClosed (Localization.AtPrime P) :=
    isIntegrallyClosed_of_isLocalization _ P.primeCompl P.primeCompl_le_nonZeroDivisors
  have hdimA : ringKrullDim A ≤ 1 := by
    have := ringKrullDim_le_of_trdeg_le A.val Subtype.val_injective (n := 1) (by simpa using htr)
    exact_mod_cast this
  refine isRegularLocalRing_of_isIntegrallyClosed ?_
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)]
  exact P.height_le_ringKrullDim_of_isPrime.trans hdimA

/-- Local uniformization in transcendence degree 1, over fields of each characteristic `p`. -/
theorem localUniformizationInDim_one (p : ℕ) : LocalUniformizationInDim.{u} p 1 := by
  intro k K _ _ _ _ hK htr V _ _
  exact hasLocalUniformization_of_trdeg_le_one hK (by simp [htr]) V

/-- Local uniformization in transcendence degree 0, over fields of each characteristic `p`. -/
theorem localUniformizationInDim_zero (p : ℕ) : LocalUniformizationInDim.{u} p 0 := by
  intro k K _ _ _ _ hK htr V _ _
  exact hasLocalUniformization_of_trdeg_le_one hK (by simp [htr]) V

end Singularity
