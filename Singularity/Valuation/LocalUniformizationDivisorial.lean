/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.LocalUniformizationCurves
import Singularity.Valuation.Abhyankar
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Local uniformization of divisorial valuations

Let `k` be a field of any characteristic, let `K` be a function field over `k`, and let `V` be a valuation of `K/k`. This file proves two results.

1. If the valuation ring `V` is essentially of finite type over `k`, then `V` has local uniformization. Here `V` is essentially of finite type if it is the localization of a finitely generated `k`-subalgebra of `V` (`Algebra.EssFiniteType k V`).
2. If `trdeg_k K ≤ trdeg_k κ_V + 1`, where `κ_V` is the residue field of `V`, then `V` is essentially of finite type over `k`. This is a theorem of Zariski. A divisorial valuation is a valuation with `trdeg_k κ_V = trdeg_k K - 1`, so each divisorial valuation has local uniformization.

The text is Proposition 4.1.8 of Volume 3 of the handbook.

## The proofs

For the first result, let `s` be a finite subset of `V`. The ring `V` is the localization of `k[σ]` for a finite subset `σ` of `V`, at the elements of `k[σ]` that are units of `V`. Let `A = k[σ, s]`. Then `A ⊆ V`, and `V` is also the localization of `A` at the center `m_V ∩ A` of `V`. The ring `V` is Noetherian, because it is a localization of a Noetherian ring. A Noetherian valuation ring is a principal ideal ring, so it is a regular local ring. Thus the local ring of `A` at the center is regular.

For the second result, choose `y_1, ..., y_m` in `V` whose residues form a transcendence basis of `κ_V` over `k`. Then `m ≤ trdeg_k K`, so `m` is finite.

1. Let `k' = k(y_1, ..., y_m) ⊆ K`. A nonzero polynomial in the `y_i` has a nonzero residue, so it is a unit of `V`. Thus `k' ⊆ V`, and `V` is a valuation of `K/k'`.
2. The tower law for the transcendence degree gives `trdeg_k' K ≤ 1`.
3. By local uniformization in transcendence degree at most 1 (`Singularity.hasLocalUniformization_of_trdeg_le_one`), there is an affine model `A` of `K/k'` with `A ⊆ V` such that the local ring `R` of `A` at the center of `V` is regular. The dimension of `R` is at most 1, so `R` is a field or a discrete valuation ring. In both cases `R` is a valuation ring.
4. The ring `V` dominates `R`. A valuation ring is maximal for domination, so `R = V`. Thus `V` is essentially of finite type over `k'`, and `k'` is essentially of finite type over `k`.

## Main results

* `Singularity.hasLocalUniformization_of_essFiniteType`: a valuation ring that is essentially of finite type over `k` has local uniformization.
* `Singularity.essFiniteType_of_trdeg_le_trdeg_residueField_add_one`: if `trdeg_k K ≤ trdeg_k κ_V + 1`, then `V` is essentially of finite type over `k`.
* `Singularity.hasLocalUniformization_of_trdeg_le_trdeg_residueField_add_one`: if `trdeg_k K ≤ trdeg_k κ_V + 1`, then `V` has local uniformization.
* `Singularity.hasLocalUniformization_of_divisorial`: a divisorial valuation has local uniformization.
-/

open IsLocalRing Cardinal

universe u

namespace Singularity

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- **Local uniformization of a valuation ring essentially of finite type.** Let `V` be a valuation of `K/k`. If `V` is the localization of a finitely generated `k`-subalgebra, then `V` has local uniformization. For a finite subset `s` of `V`, the model is `A = k[σ, s]`, where `σ` generates the subalgebra, and the local ring of `A` at the center of `V` is `V`. -/
theorem hasLocalUniformization_of_essFiniteType (V : ValuationSubring K) [Algebra k V]
    [IsScalarTower k V K] [Algebra.EssFiniteType k V] : HasLocalUniformization k V := by
  classical
  -- The ring `V` is Noetherian, so it is a principal ideal ring and a regular local ring.
  have : IsNoetherianRing V := by
    have : IsNoetherianRing (Algebra.EssFiniteType.subalgebra k V) :=
      Algebra.FiniteType.isNoetherianRing k _
    exact IsLocalization.isNoetherianRing (Algebra.EssFiniteType.submonoid k V) V this
  have hreg : IsRegularLocalRing V := inferInstance
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff k V).mp inferInstance
  intro s hs
  have hk : ∀ a : k, algebraMap k K a ∈ V := fun a => by
    rw [IsScalarTower.algebraMap_apply k V K]
    exact (algebraMap k V a).2
  let Vk : Subalgebra k K := { V.toSubring.toSubsemiring with algebraMap_mem' := hk }
  set T : Finset K := σ.image (fun x : V => (x : K)) ∪ s
  set A := Algebra.adjoin k (T : Set K)
  have hAV : ∀ a : A, (a : K) ∈ V := by
    have hle : A ≤ Vk := by
      refine Algebra.adjoin_le fun x hx => ?_
      rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with hx | hx
      · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
        exact y.2
      · exact hs x hx
    exact fun a => hle a.2
  -- The image in `K` of `k[σ] ⊆ V` lies in `A`.
  have himg : ∀ x ∈ Algebra.adjoin k (σ : Set V), (x : K) ∈ A := by
    intro x hx
    have hmap : IsScalarTower.toAlgHom k V K x ∈
        (Algebra.adjoin k (σ : Set V)).map (IsScalarTower.toAlgHom k V K) := ⟨x, hx, rfl⟩
    rw [AlgHom.map_adjoin] at hmap
    refine Algebra.adjoin_mono ?_ hmap
    rintro _ ⟨y, hy, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_union_left s (Finset.mem_image.mpr ⟨y, hy, rfl⟩))
  set q := valuationCenter V A hAV
  let φ : A →+* V := (A.val : A →+* K).codRestrict V hAV
  let : Algebra A V := φ.toAlgebra
  have hmemq : ∀ a : A, a ∈ q ↔ φ a ∈ maximalIdeal V := fun a => Iff.rfl
  have hloc : IsLocalization q.primeCompl V := by
    refine (isLocalization_iff q.primeCompl V).mpr ⟨fun a => ?_, fun v => ?_, fun {x y} h => ⟨1, ?_⟩⟩
    · by_contra h
      exact a.2 ((hmemq a).mpr (by_contra fun h' => h (notMem_maximalIdeal.mp h')))
    · obtain ⟨t, ht, htu, hvt⟩ := hσ v
      refine ⟨⟨⟨(v * t : V), himg _ hvt⟩, ⟨⟨(t : K), himg t ht⟩, fun h => ?_⟩⟩, ?_⟩
      · apply (hmemq _).mp h
        convert htu
        exact Subtype.ext rfl
      · exact Subtype.ext rfl
    · have h' := congrArg Subtype.val h
      have : x = y := Subtype.ext h'
      rw [this]
  have hfrac : IsFractionRing A K := by
    refine IsFractionRing.of_field A K fun z => ?_
    have key : ∀ w : V, ∃ a b : A, b ∉ q ∧ (w : K) = a / b := by
      intro w
      obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj q.primeCompl w
      refine ⟨a, b, b.2, ?_⟩
      have hb : (b : A) ∉ q := b.2
      have hb0 : ((b : A) : K) ≠ 0 := by
        intro h0
        apply hb
        rw [hmemq]
        have : φ b = 0 := Subtype.ext h0
        rw [this]
        exact zero_mem _
      rw [eq_div_iff hb0]
      exact congrArg Subtype.val hab
    rcases V.mem_or_inv_mem z with hz | hz
    · obtain ⟨a, b, -, h⟩ := key ⟨z, hz⟩
      exact ⟨a, b, h⟩
    · by_cases hz0 : z = 0
      · exact ⟨0, 1, by simp [hz0]⟩
      obtain ⟨a, b, -, h⟩ := key ⟨z⁻¹, hz⟩
      refine ⟨b, a, ?_⟩
      change z = ((b : A) : K) / ((a : A) : K)
      rw [← inv_inv z, show z⁻¹ = ((a : A) : K) / ((b : A) : K) from h, inv_div]
  refine ⟨A, hAV, ⟨⟨T, rfl⟩, hfrac⟩, fun x hx => Algebra.subset_adjoin
    (Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_coe.mp hx))), ?_⟩
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl V (Localization.AtPrime q)).toRingEquiv

/-- A regular local domain of dimension at most 1 is a valuation ring: it is a field or a discrete valuation ring. -/
theorem valuationRing_of_isRegularLocalRing (R : Type*) [CommRing R] [IsDomain R]
    [IsRegularLocalRing R] (hR : ringKrullDim R ≤ 1) : ValuationRing R := by
  by_cases hf : IsField R
  · let := hf.toField
    infer_instance
  · have hfin := (IsRegularLocalRing.iff_finrank_cotangentSpace (R := R)).mp inferInstance
    have h1 : Module.finrank (ResidueField R) (CotangentSpace R) = 1 := by
      have hle : Module.finrank (ResidueField R) (CotangentSpace R) ≤ 1 := by
        have : (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) ≤ 1 :=
          hfin ▸ hR
        exact_mod_cast this
      have hne : Module.finrank (ResidueField R) (CotangentSpace R) ≠ 0 :=
        fun h => hf (finrank_cotangentSpace_eq_zero_iff.mp h)
      omega
    exact ((IsDiscreteValuationRing.TFAE R hf).out 6 2).mp h1

/-- **A theorem of Zariski.** Let `K` be a function field over `k`, and let `V` be a valuation of `K/k` with `trdeg_k K ≤ trdeg_k κ_V + 1`. Then `V` is essentially of finite type over `k`: it is the local ring of an affine model of `K/k` at the center of `V`. -/
theorem essFiniteType_of_trdeg_le_trdeg_residueField_add_one (hK : IsFunctionField k K)
    (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K]
    (htr : Algebra.trdeg k K ≤ Algebra.trdeg k (ResidueField V) + 1) :
    Algebra.EssFiniteType k V := by
  classical
  have hKft : Algebra.EssFiniteType k K := IntermediateField.fg_top_iff.mp hK
  have hfinK : Algebra.trdeg k K < ℵ₀ := trdeg_lt_aleph0 k K
  -- Step 0: elements `y j` of `V` whose residues form a transcendence basis of `κ_V`.
  obtain ⟨b, hb⟩ := exists_isTranscendenceBasis k (ResidueField V)
  choose y hy using fun e : b => residue_surjective (R := V) (e : ResidueField V)
  have hyres : AlgebraicIndependent k (fun j => residue V (y j)) := by
    convert hb.1 using 1
    funext j
    simp [hy j]
  have hyV : AlgebraicIndependent k y := by
    refine AlgebraicIndependent.of_comp (IsScalarTower.toAlgHom k V (ResidueField V)) ?_
    convert hyres using 1
    funext j
    rfl
  set f : b → K := fun j => (y j : K)
  have hf : AlgebraicIndependent k f :=
    hyV.map' (f := IsScalarTower.toAlgHom k V K) Subtype.val_injective
  have hbκ : #b = Algebra.trdeg k (ResidueField V) := hb.cardinalMk_eq_trdeg
  -- Step 1: the field `k' = k(y)` lies in `V`.
  set k' : IntermediateField k K := IntermediateField.adjoin k (Set.range f)
  have h1 : ∀ P : MvPolynomial b k, MvPolynomial.aeval f P = ((MvPolynomial.aeval y P : V) : K) :=
    fun P => (MvPolynomial.comp_aeval_apply (f := y) (IsScalarTower.toAlgHom k V K) P).symm
  have h2 : ∀ P : MvPolynomial b k, MvPolynomial.aeval (fun j => residue V (y j)) P =
      residue V (MvPolynomial.aeval y P) := fun P => by
    have := MvPolynomial.comp_aeval_apply (f := y)
      (IsScalarTower.toAlgHom k V (ResidueField V)) P
    simpa using this.symm
  have hk'V : ∀ z ∈ k', z ∈ V := by
    intro z hz
    obtain ⟨r, hr, t, ht, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
    rw [Algebra.adjoin_range_eq_range_aeval] at hr ht
    obtain ⟨P, rfl⟩ := hr
    obtain ⟨Q, rfl⟩ := ht
    by_cases hQ : Q = 0
    · simp [hQ]
    have hres : residue V (MvPolynomial.aeval y Q) ≠ 0 := by
      rw [← h2]
      exact fun h => hQ (algebraicIndependent_iff.mp hyres Q h)
    obtain ⟨u, hu⟩ := (residue_ne_zero_iff_isUnit _).mp hres
    have hu0 : ((u : V) : K) ≠ 0 := fun h0 => u.ne_zero (Subtype.ext h0)
    have : ((MvPolynomial.aeval y P : V) : K) / ((u : V) : K) =
        ((MvPolynomial.aeval y P * ↑u⁻¹ : V) : K) := by
      rw [div_eq_iff hu0]
      push_cast
      rw [mul_assoc, ← MulMemClass.coe_mul, Units.inv_mul, OneMemClass.coe_one, mul_one]
    change MvPolynomial.aeval f P / MvPolynomial.aeval f Q ∈ V
    rw [h1, h1, ← hu, this]
    exact SetLike.coe_mem _
  -- The structures of `k'`-algebra on `V`.
  let ι : k' →+* V := (k'.val : k' →+* K).codRestrict V (fun z => hk'V z z.2)
  let : Algebra k' V := ι.toAlgebra
  have : IsScalarTower k' V K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower k k' V := IsScalarTower.of_algebraMap_eq (fun a => Subtype.ext (by
    change (algebraMap k V a : K) = algebraMap k K a
    exact (IsScalarTower.algebraMap_apply k V K a).symm))
  -- Step 2: `K` is a function field over `k'` of transcendence degree at most 1.
  have hK' : IsFunctionField k' K := by
    have : Algebra.EssFiniteType k' K := Algebra.EssFiniteType.of_comp k k' K
    exact IntermediateField.fg_top_iff.mpr this
  have hadd := trdeg_add_eq k k' (A := K)
  have hbk' : #b ≤ Algebra.trdeg k k' := by
    let g : b → k' := fun j => ⟨f j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩
    have hg : AlgebraicIndependent k g := AlgebraicIndependent.of_comp k'.val hf
    exact hg.cardinalMk_le_trdeg
  have hfin' : Algebra.trdeg k k' < ℵ₀ :=
    lt_of_le_of_lt (hadd ▸ le_self_add) hfinK
  have htr' : Algebra.trdeg k' K ≤ 1 := by
    have : Algebra.trdeg k' K + Algebra.trdeg k k' ≤ 1 + Algebra.trdeg k k' := by
      rw [add_comm, hadd, add_comm 1]
      exact htr.trans (by rw [← hbκ]; gcongr)
    exact (add_le_add_iff_of_lt_aleph0 hfin').mp this
  -- Step 3: an affine model `A` of `K/k'` with a regular center.
  obtain ⟨A, hAV, ⟨hfg, hfrac⟩, -, hreg⟩ :=
    hasLocalUniformization_of_trdeg_le_one hK' htr' V ∅ (by simp)
  set q := valuationCenter V A hAV
  have : Algebra.FiniteType k' A := (Subalgebra.fg_iff_finiteType A).mp hfg
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k' A
  have : IsFractionRing A K := hfrac
  let R := Localization.AtPrime q
  have hdimA : ringKrullDim A ≤ 1 := by
    have := ringKrullDim_le_of_trdeg_le A.val Subtype.val_injective (n := 1) (by simpa using htr')
    exact_mod_cast this
  have hdim : ringKrullDim R ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q R]
    exact q.height_le_ringKrullDim_of_isPrime.trans hdimA
  have : ValuationRing R := valuationRing_of_isRegularLocalRing R hdim
  -- Step 4: `V` dominates `R`, so `R = V`.
  let φ : A →+* V := (A.val : A →+* K).codRestrict V hAV
  have hmemq : ∀ a : A, a ∈ q ↔ φ a ∈ maximalIdeal V := fun a => Iff.rfl
  have hunits : ∀ t : q.primeCompl, IsUnit (φ t) := fun t =>
    by_contra fun h => t.2 ((hmemq t).mpr h)
  let F : R →+* V := IsLocalization.lift (M := q.primeCompl) (S := R) hunits
  have hF : ∀ a : A, F (algebraMap A R a) = φ a := IsLocalization.lift_eq hunits
  have hFloc : IsLocalHom F := by
    refine ⟨fun r hr => ?_⟩
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl r
    have hspec := congrArg F (IsLocalization.mk'_spec R a t)
    rw [map_mul, hF, hF] at hspec
    have ha : IsUnit (φ a) := hspec ▸ hr.mul (hunits t)
    exact (IsLocalization.AtPrime.isUnit_mk'_iff R q a t).mpr
      (fun h => ((hmemq a).mp h) ha)
  let : Algebra R K := (V.subtype.comp F).toAlgebra
  have : IsScalarTower A R K := IsScalarTower.of_algebraMap_eq (fun a => by
    change (a : K) = V.subtype (F (algebraMap A R a))
    rw [hF]
    rfl)
  have : IsFractionRing R K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl R K
  have hbij := bijective_rangeRestrict_comp_of_valuationRing (R := R) (S := V) (K := K) F
    V.subtype rfl
  have hFbij : Function.Bijective F := by
    refine ⟨fun a c hac => hbij.1 (by rw [RingHom.comp_apply, RingHom.comp_apply, hac]),
      fun v => ?_⟩
    obtain ⟨r, hr⟩ := hbij.2 (V.subtype.rangeRestrict v)
    have hr' := congrArg Subtype.val hr
    exact ⟨r, Subtype.ext hr'⟩
  let : Algebra A V := φ.toAlgebra
  let e : R ≃ₐ[A] V :=
    AlgEquiv.ofBijective { F with commutes' := fun a => hF a } hFbij
  have : IsLocalization q.primeCompl V := IsLocalization.isLocalization_of_algEquiv q.primeCompl e
  have : Algebra.EssFiniteType A V := .of_isLocalization V q.primeCompl
  have : IsScalarTower k' A V := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Algebra.EssFiniteType k' V := .comp k' A V
  -- The field `k'` is essentially of finite type over `k`.
  have : Finite b := Cardinal.lt_aleph0_iff_finite.mp (hbk'.trans_lt hfin')
  have : Algebra.EssFiniteType k k' := IntermediateField.essFiniteType_iff.mpr
    (IntermediateField.fg_adjoin_of_finite (Set.finite_range f))
  exact .comp k k' V

/-- **Local uniformization when `trdeg_k K ≤ trdeg_k κ_V + 1`.** Let `K` be a function field over a field `k` of any characteristic, and let `V` be a valuation of `K/k` whose residue field has transcendence degree at least `trdeg_k K - 1` over `k`. Then `V` has local uniformization. -/
theorem hasLocalUniformization_of_trdeg_le_trdeg_residueField_add_one (hK : IsFunctionField k K)
    (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K]
    (htr : Algebra.trdeg k K ≤ Algebra.trdeg k (ResidueField V) + 1) :
    HasLocalUniformization k V := by
  have := essFiniteType_of_trdeg_le_trdeg_residueField_add_one hK V htr
  exact hasLocalUniformization_of_essFiniteType V

/-- **Local uniformization of divisorial valuations.** Let `K` be a function field over a field `k` of any characteristic, and let `V` be a valuation of `K/k` with `trdeg_k κ_V + 1 = trdeg_k K`. Then `V` has local uniformization. -/
theorem hasLocalUniformization_of_divisorial (hK : IsFunctionField k K)
    (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K]
    (hdiv : Algebra.trdeg k (ResidueField V) + 1 = Algebra.trdeg k K) :
    HasLocalUniformization k V :=
  hasLocalUniformization_of_trdeg_le_trdeg_residueField_add_one hK V hdiv.ge

end Singularity
