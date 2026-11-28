/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.LocalUniformization
import Singularity.Valuation.AbhyankarResidueField
import Singularity.Valuation.LocalUniformizationDivisorial
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Cores of some reductions of Volumes 5 and 6

This file proves honest cores of results of Volumes 5 and 6 of the handbook. Each result is
either a part of the proof, or the implication that the result draws from a theorem that the
library does not prove. In the second case the theorem is an explicit hypothesis.

## Volume 5

* `exists_isAffineModel_subset_valuationSubring`: the first step of the proof of Proposition
  4.1.2. For a finite subset `s` of `𝒪_v` there is an affine model `A` of `K/k` with
  `s ⊆ A ⊆ 𝒪_v`.
* `mem_valuationSubring_of_isIntegral`: the step `B ⊆ 𝒪_w` of the proof of Proposition 4.1.2.
  An element that is integral over a subalgebra of `𝒪_w` lies in `𝒪_w`.
* `hasRegularCenter_of_bijective`: a regular center moves down along a bijective map `K → L`.
* `hasLocalUniformization_of_localUniformization_inseparable`: Corollary 4.1.3. The Lean form
  of the theorem of Temkin (`localUniformization_inseparable`) implies local uniformization in
  characteristic 0, the theorem of Zariski.
* `AffineResolution`, `hasLocalUniformization_of_affineResolution`: the affine form of
  Proposition 1.4.5 and of Corollary 1.4.6. If each affine model inside `𝒪_v` lies in a regular
  affine model inside `𝒪_v`, then `v` has local uniformization.
* `hasLocalUniformization_of_isAbhyankarValuation_of_perfectField`: Corollary 2.2.3, with the
  theorem of Knaf-Kuhlmann (`localUniformization_abhyankar`) as a hypothesis.
* `hasLocalUniformization_of_trdeg_eq_two_of_one_le`: Proposition 3.1.2 for the valuations whose
  residue field is not algebraic over `k`.

## Volume 6

* `flat_of_injective_algebraMap`: the flatness step of Corollary 1.1.5. A domain that contains
  a Dedekind domain `𝒪` is flat over `𝒪`.
* `minpoly_eq_X_pow_sub_C`, `coeff_X_pow_sub_C_eq_zero`, `finrank_adjoin_eq_of_pow`: the form
  of the purely inseparable steps of Step 3 of Proposition 2.2.1. For `c ∉ K` with
  `c ^ p ∈ K` the equation of `c` is `X ^ p - c ^ p`, so it is in case 1 of Theorem 1.2.6.
* `taylor_X_pow_sub_C_char`: case 1 of Theorem 1.2.6 is stable under `X ↦ X + θ`.
* `order_eval_sq_add_X_pow_three_le`: Theorem 3.1.5 for `h = X ^ 2 + u ^ 3` over `k[[u]]`.

## What is not proved

* Volume 5, Corollary 1.4.6: the theorem of Hironaka, and the passage from a resolution of a
  model to an affine regular model around the center of `v`, are not proved. The hypothesis
  `AffineResolution` stands for both.
* Volume 5, Corollary 2.2.3: the theorem of Knaf-Kuhlmann is a hypothesis.
* Volume 5, Proposition 3.1.2: the valuations with a residue field algebraic over `k` are not
  covered. They need the resolution of surfaces of Lipman.
* Volume 5, Proposition 4.1.2: the theorem of Temkin in the form with smooth points, the
  finiteness of the integral closure `B`, and the regularity of smooth points are not proved.
* Volume 5, Corollary 4.1.3: the Lean form of the theorem of Temkin is a hypothesis.
* Volume 6, Corollary 1.1.5: only the flatness step is proved, for an affine piece.
* Volume 6, Proposition 2.2.1: only the form of the inseparable steps is proved. The patching,
  the Noether normalization, the tame part and Theorem 1.2.6 itself are not proved.
* Volume 6, Theorem 3.1.5: only the example `h = X ^ 2 + u ^ 3` is proved. The general
  existence of a minimal polyhedron and the vertex criterion are not proved.
* Volume 6, Corollaries 1.1.4 and 4.3.2 are not treated in this file.
-/

open IsLocalRing Polynomial

universe u

namespace Singularity

section AffineModel

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **The first step of Volume 5, Proposition 4.1.2.** Let `K` be a function field over `k`,
let `V` be a valuation of `K/k`, and let `s` be a finite subset of `V`. Then there is an affine
model `A` of `K/k` with `s ⊆ A ⊆ V`. One writes `K = k(t_1, ..., t_m)`, replaces `t_i` by
`t_i⁻¹` when `t_i ∉ V`, and takes `A = k[s, t_1, ..., t_m]`. -/
theorem exists_isAffineModel_subset_valuationSubring (hK : IsFunctionField k K)
    (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K] (s : Finset K)
    (hs : ∀ x ∈ s, x ∈ V) :
    ∃ (A : Subalgebra k K) (_ : ∀ a : A, (a : K) ∈ V), IsAffineModel A ∧ (s : Set K) ⊆ A := by
  classical
  obtain ⟨t, ht⟩ := hK
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
  refine ⟨A₀, hA₀V, ⟨⟨s ∪ t', rfl⟩, hfrac₀⟩, fun x hx => ?_⟩
  exact Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_union_left t' hx))

/-- **The step `B ⊆ 𝒪_w` of Volume 5, Proposition 4.1.2.** Let `W` be a valuation subring of a
field `L`, and let `A` be a subalgebra of `L` with `A ⊆ W`. Each element of `L` that is integral
over `A` lies in `W`, because `W` is integrally closed. So the integral closure of `A` in `L`
lies in `W`. -/
theorem mem_valuationSubring_of_isIntegral {L : Type*} [Field L] [Algebra k L]
    {W : ValuationSubring L} {A : Subalgebra k L} (hA : ∀ a : A, (a : L) ∈ W) {x : L}
    (hx : IsIntegral A x) : x ∈ W := by
  let φ : A →+* W := (A.val : A →+* L).codRestrict W hA
  have hint : IsIntegral W (RingHom.id L x) :=
    IsIntegral.map_of_comp_eq φ (RingHom.id L) (by ext; rfl) hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [RingHom.id_apply] at hy
  rw [← hy]
  exact y.2

end AffineModel

section Transport

variable {k K L : Type*} [Field k] [Field K] [Algebra k K] [Field L] [Algebra K L] [Algebra k L]
  [IsScalarTower k K L]

/-- A regular center moves down along a bijective map `K → L` of `k`-algebras. Let `W` be a
valuation subring of `L` with `W ∩ K = V`. If `W` has a regular center on an affine model of
`L/k` that contains the image of `S`, then `V` has a regular center on an affine model of `K/k`
that contains `S`. The model of `K` is the inverse image of the model of `L`. -/
theorem hasRegularCenter_of_bijective (hbij : Function.Bijective (algebraMap K L))
    {V : ValuationSubring K} {W : ValuationSubring L} (hW : W.comap (algebraMap K L) = V)
    {S : Set K} (h : HasRegularCenter k W (algebraMap K L '' S)) : HasRegularCenter k V S := by
  obtain ⟨A', hA'W, ⟨hfg, hfrac⟩, hS, hreg⟩ := h
  let e : K ≃ₐ[k] L := AlgEquiv.ofBijective (IsScalarTower.toAlgHom k K L) hbij
  have he : ∀ x : K, e x = algebraMap K L x := fun x => rfl
  have hmemV : ∀ x : K, algebraMap K L x ∈ W → x ∈ V := fun x hx => by
    rw [← hW]
    exact hx
  let A : Subalgebra k K := A'.comap (IsScalarTower.toAlgHom k K L)
  have hmemA : ∀ x : K, x ∈ A ↔ algebraMap K L x ∈ A' := fun x => Iff.rfl
  have hAV : ∀ a : A, (a : K) ∈ V := fun a => hmemV a (hA'W ⟨_, (hmemA a).mp a.2⟩)
  have hAmap : A = A'.map (e.symm : L →ₐ[k] K) := by
    ext x
    rw [hmemA, Subalgebra.mem_map]
    constructor
    · intro hx
      exact ⟨algebraMap K L x, hx, by rw [← he]; exact e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      rw [← he]
      change e (e.symm y) ∈ A'
      rwa [e.apply_symm_apply]
  have hfgA : A.FG := by
    rw [hAmap]
    exact hfg.map _
  -- The ring isomorphism `A ≃ A'`.
  let φ₀ : A →+* A' :=
    ((algebraMap K L).comp (A.val : A →+* K)).codRestrict A' fun a => (hmemA a).mp a.2
  have hφ₀ : Function.Bijective φ₀ := by
    refine ⟨fun a b hab => Subtype.ext (hbij.1 (congrArg Subtype.val hab)), fun y => ?_⟩
    obtain ⟨x, hx⟩ := hbij.2 (y : L)
    refine ⟨⟨x, (hmemA x).mpr (hx ▸ y.2)⟩, Subtype.ext ?_⟩
    exact hx
  let φ : A ≃+* A' := RingEquiv.ofBijective φ₀ hφ₀
  have hφ : ∀ a : A, ((φ a : A') : L) = algebraMap K L a := fun a => rfl
  have hfracA : IsFractionRing A K := by
    refine IsFractionRing.of_field A K fun z => ?_
    obtain ⟨x, y, -, hz⟩ := IsFractionRing.div_surjective (A := A') (e z)
    have hxA : e.symm x ∈ A := by
      rw [hmemA, ← he, e.apply_symm_apply]
      exact x.2
    have hyA : e.symm y ∈ A := by
      rw [hmemA, ← he, e.apply_symm_apply]
      exact y.2
    refine ⟨⟨_, hxA⟩, ⟨_, hyA⟩, ?_⟩
    change z = e.symm x / e.symm y
    rw [← map_div₀, ← e.symm_apply_apply z]
    congr 1
    exact hz.symm
  -- The ring isomorphism `V ≃ W`.
  have hVW : ∀ v : V, algebraMap K L v ∈ W := fun v =>
    show (v : K) ∈ W.comap (algebraMap K L) by rw [hW]; exact v.2
  let ψ₀ : V →+* W := ((algebraMap K L).comp V.subtype).codRestrict W hVW
  have hψ₀ : Function.Bijective ψ₀ := by
    refine ⟨fun a b hab => Subtype.ext (hbij.1 (congrArg Subtype.val hab)), fun y => ?_⟩
    obtain ⟨x, hx⟩ := hbij.2 (y : L)
    refine ⟨⟨x, hmemV x (hx ▸ y.2)⟩, Subtype.ext ?_⟩
    exact hx
  let ψ : V ≃+* W := RingEquiv.ofBijective ψ₀ hψ₀
  have hcenter : valuationCenter V A hAV = (valuationCenter W A' hA'W).comap (φ : A →+* A') := by
    ext a
    change (⟨a, hAV a⟩ : V) ∈ maximalIdeal V ↔ (⟨(φ a : L), hA'W (φ a)⟩ : W) ∈ maximalIdeal W
    have hψa : ψ ⟨a, hAV a⟩ = ⟨(φ a : L), hA'W (φ a)⟩ := Subtype.ext rfl
    rw [← hψa, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      isUnit_map_iff]
  refine ⟨A, hAV, ⟨hfgA, hfracA⟩, fun x hx => (hmemA x).mpr (hS ⟨x, hx, rfl⟩), ?_⟩
  have key : ∀ (Q : Ideal A) [Q.IsPrime], Q = (valuationCenter W A' hA'W).comap (φ : A →+* A') →
      IsRegularLocalRing (Localization.AtPrime Q) := by
    intro Q _ hQ
    subst hQ
    exact IsRegularLocalRing.of_ringEquiv (IsLocalization.ringEquivOfRingEquiv
      (Localization.AtPrime ((valuationCenter W A' hA'W).comap φ))
      (Localization.AtPrime (valuationCenter W A' hA'W)) φ
      (φ.map_primeCompl_comap_eq (valuationCenter W A' hA'W))).symm
  exact key (valuationCenter V A hAV) hcenter

end Transport

section Temkin

/-- **Volume 5, Corollary 4.1.3 of the handbook.** The Lean form of the theorem of Temkin
(`localUniformization_inseparable`) implies the theorem of Zariski: if `k` has characteristic
0, then each valuation of a function field `K/k` has local uniformization. A finite purely
inseparable extension `L/K` in characteristic 0 is trivial, so the regular center on a model of
`L` moves down to `K`. The theorem of Temkin is a hypothesis here, and it is not proved. -/
theorem hasLocalUniformization_of_localUniformization_inseparable
    (H : localUniformization_inseparable.{u}) {k K : Type u} [Field k] [CharZero k] [Field K]
    [Algebra k K] (hK : IsFunctionField k K) (V : ValuationSubring K) [Algebra k V]
    [IsScalarTower k V K] : HasLocalUniformization k V := by
  intro s hs
  obtain ⟨L, _, _, _, _, hfin, hpi, W, hW, hreg⟩ := H k K hK V s hs
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have : Algebra.IsSeparable K L := inferInstance
  have hbij : Function.Bijective (algebraMap K L) :=
    ⟨(algebraMap K L).injective, IsPurelyInseparable.surjective_algebraMap_of_isSeparable K L⟩
  exact hasRegularCenter_of_bijective hbij hW hreg

end Temkin

section Resolution

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/-- The affine form of the hypothesis of Volume 5, Corollary 1.4.6: for each valuation subring
`V` of `K` and each affine model `A ⊆ V` of `K/k`, there is an affine model `A'` of `K/k` with
`A ⊆ A' ⊆ V` that is a regular ring. A resolution `X' → Spec A` gives such an `A'`: take an
affine open neighbourhood of the center of `V` on `X'`. This passage, and the theorem of
Hironaka that gives the resolution in characteristic 0, are not proved here. -/
def AffineResolution : Prop :=
  ∀ (V : ValuationSubring K) (A : Subalgebra k K) (_ : ∀ a : A, (a : K) ∈ V), IsAffineModel A →
    ∃ (A' : Subalgebra k K) (_ : ∀ a : A', (a : K) ∈ V), A ≤ A' ∧ IsAffineModel A' ∧
      IsRegularRing A'

variable {k K}

/-- **Volume 5, Proposition 1.4.5 and Corollary 1.4.6, in affine form.** If each affine model
inside a valuation ring lies in a regular affine model inside it (`AffineResolution`), then each
valuation of the function field `K/k` has local uniformization. The center of `V` on a regular
model is a regular point. -/
theorem hasLocalUniformization_of_affineResolution (H : AffineResolution k K)
    (hK : IsFunctionField k K) (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K] :
    HasLocalUniformization k V := by
  intro s hs
  obtain ⟨A, hAV, hA, hsA⟩ := exists_isAffineModel_subset_valuationSubring hK V s hs
  obtain ⟨A', hA'V, hle, hA', hreg⟩ := H V A hAV hA
  exact ⟨A', hA'V, hA', hsA.trans hle, inferInstance⟩

end Resolution

section Abhyankar

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Volume 5, Corollary 2.2.3, when the residue field is known to be finitely generated. If `k`
is perfect, then a finitely generated residue field is separably generated over `k`, so the
theorem of Knaf-Kuhlmann applies. The theorem of Knaf-Kuhlmann is a hypothesis. -/
theorem hasLocalUniformization_of_isAbhyankarValuation_of_fg (H : localUniformization_abhyankar.{u})
    [PerfectField k] (hK : IsFunctionField k K) (V : ValuationSubring K) [Algebra k V]
    [IsScalarTower k V K] (hV : IsAbhyankarValuation k V)
    (hfg : (⊤ : IntermediateField k (ResidueField V)).FG) : HasLocalUniformization k V := by
  have : Algebra.EssFiniteType k (ResidueField V) := IntermediateField.fg_top_iff.mp hfg
  exact H k K hK V hV inferInstance

/-- **Volume 5, Corollary 2.2.3 of the handbook.** Let `k` be a perfect field. If the theorem of
Knaf-Kuhlmann holds (`localUniformization_abhyankar`), then each Abhyankar valuation of a
function field `K/k` has local uniformization. The residue field is finitely generated over `k`
by Volume 3, Corollary 2.2.4 (`Singularity.IsAbhyankarValuation.fg_residueField`). The theorem
of Knaf-Kuhlmann is a hypothesis, and it is not proved. -/
theorem hasLocalUniformization_of_isAbhyankarValuation_of_perfectField
    (H : localUniformization_abhyankar.{u}) [PerfectField k] (hK : IsFunctionField k K)
    (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K]
    (hV : IsAbhyankarValuation k V) : HasLocalUniformization k V :=
  hasLocalUniformization_of_isAbhyankarValuation_of_fg H hK V hV (hV.fg_residueField hK)

end Abhyankar

section Surfaces

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- **Volume 5, Proposition 3.1.2, for valuations with a transcendental residue.** Let `K/k` be a
function field of transcendence degree 2, and let `V` be a valuation of `K/k` whose residue field
has transcendence degree at least 1 over `k`. Then `V` has local uniformization. This is Volume 3,
Proposition 4.1.8 (`Singularity.hasLocalUniformization_of_trdeg_le_trdeg_residueField_add_one`).
The valuations with a residue field algebraic over `k` are not covered. -/
theorem hasLocalUniformization_of_trdeg_eq_two_of_one_le (hK : IsFunctionField k K)
    (htr : Algebra.trdeg k K = 2) (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K]
    (hres : 1 ≤ Algebra.trdeg k (ResidueField V)) : HasLocalUniformization k V := by
  refine hasLocalUniformization_of_trdeg_le_trdeg_residueField_add_one hK V ?_
  rw [htr, ← one_add_one_eq_two]
  exact add_le_add hres (le_refl 1)

end Surfaces

section Flat

/-- **The flatness step of Volume 6, Corollary 1.1.5.** Let `𝒪` be a Dedekind domain, and let
`B` be a domain that contains `𝒪`. Then `B` is flat over `𝒪`, because a module over a Dedekind
domain is flat if it has no torsion. This is the affine form of the claim that an integral scheme
that dominates `Spec 𝒪` is flat over `𝒪`. -/
theorem flat_of_injective_algebraMap {O B : Type*} [CommRing O] [IsDedekindDomain O]
    [CommRing B] [IsDomain B] [Algebra O B] (h : Function.Injective (algebraMap O B)) :
    Module.Flat O B := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  intro b hb
  obtain ⟨⟨a, ha⟩, hab⟩ := (Submodule.mem_torsion_iff b).mp hb
  have ha0 : algebraMap O B a ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap O B)]
    exact fun h' => (mem_nonZeroDivisors_iff_ne_zero.mp ha) (h h')
  change a • b = 0 at hab
  rw [Algebra.smul_def] at hab
  exact (Submodule.mem_bot O).mpr ((mul_eq_zero.mp hab).resolve_left ha0)

end Flat

section InseparableStep

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {p : ℕ}

/-- **The equation of a purely inseparable step of Volume 6, Proposition 2.2.1.** Let `L/K` be
an extension of fields of characteristic `p`, and let `c ∈ L` with `c ∉ K` and `c ^ p = a ∈ K`.
Then the minimal polynomial of `c` over `K` is `X ^ p - a`. This is the polynomial `h` of Step 3
of the proof. -/
theorem minpoly_eq_X_pow_sub_C (hp : p.Prime) [CharP L p] {c : L} {a : K}
    (hc : c ^ p = algebraMap K L a) (hcK : c ∉ Set.range (algebraMap K L)) :
    minpoly K c = X ^ p - C a := by
  have hroot : ∀ b : K, b ^ p ≠ a := by
    intro b hb
    have : Fact p.Prime := ⟨hp⟩
    apply hcK
    refine ⟨b, ?_⟩
    apply frobenius_inj L p
    simp only [frobenius_def]
    rw [← map_pow, hb, hc]
  have hirr := X_pow_sub_C_irreducible_of_prime hp hroot
  refine (minpoly.eq_of_irreducible_of_monic hirr ?_ (monic_X_pow_sub_C a hp.ne_zero)).symm
  simp [hc]

/-- The polynomial `X ^ p - a` has no terms in `X ^ 1, ..., X ^ (p - 1)`. So the equation of a
purely inseparable step is in case 1 of Volume 6, Theorem 1.2.6. -/
theorem coeff_X_pow_sub_C_eq_zero (a : K) {i : ℕ} (hi0 : 0 < i) (hip : i < p) :
    (X ^ p - C a).coeff i = 0 := by
  simp [coeff_X_pow, coeff_C, hip.ne, hi0.ne']

/-- A purely inseparable step `K ⊆ K(c)` with `c ∉ K` and `c ^ p ∈ K` has degree `p`. -/
theorem finrank_adjoin_eq_of_pow (hp : p.Prime) [CharP L p] {c : L} {a : K}
    (hc : c ^ p = algebraMap K L a) (hcK : c ∉ Set.range (algebraMap K L)) :
    Module.finrank K (IntermediateField.adjoin K {c}) = p := by
  have hint : IsIntegral K c := by
    refine ⟨X ^ p - C a, monic_X_pow_sub_C a hp.ne_zero, ?_⟩
    simp [hc]
  rw [IntermediateField.adjoin.finrank hint, minpoly_eq_X_pow_sub_C hp hc hcK,
    natDegree_X_pow_sub_C]

/-- Case 1 of Volume 6, Theorem 1.2.6, is stable under a translation: in characteristic `p`,
`(X + θ) ^ p - f = X ^ p - (f - θ ^ p)`. This is part 5 of the remark on the hypotheses of the
theorem. -/
theorem taylor_X_pow_sub_C_char {R : Type*} [CommRing R] [Fact p.Prime] [CharP R p]
    (θ f : R) : taylor θ (X ^ p - C f) = X ^ p - C (f - θ ^ p) := by
  rw [map_sub, taylor_pow, taylor_X, taylor_C, add_pow_char, ← C_pow, C_sub]
  ring

end InseparableStep

section Polyhedron

variable {k : Type*} [Field k]

/-- **Volume 6, Theorem 3.1.5, for `h = X ^ 2 + u ^ 3` over `S = k[[u]]`.** For each `φ` in
`k[[u]]`, the constant term `f_2 = h(φ) = φ ^ 2 + u ^ 3` of `h` in the coordinate `Z = X - φ`
has order at most 3.

In one variable the polyhedron `Δ(h; u; X - φ)` is the half line `[δ, ∞)`, where `δ` is the least
value of `ord f_1` and `ord f_2 / 2`. For `φ = 0` we have `f_1 = 0` and `f_2 = u ^ 3`, so `δ = 3/2`.
The theorem gives `δ ≤ 3/2` for each `φ`, so `Δ(h; u; X) ⊆ Δ(h; u; X - φ)`. This is part 1 of
Theorem 3.1.5 with `θ = 0 ∈ S`, so also part 3. The only vertex `3/2` is not in `ℕ`, so it is not
solvable, as part 2 says. The identification of the polyhedron with a half line is not
formalized here. The proof holds in each characteristic. -/
theorem order_eval_sq_add_X_pow_three_le (φ : PowerSeries k) :
    ((taylor φ (X ^ 2 + C (PowerSeries.X ^ 3))).coeff 0).order ≤ 3 := by
  rw [taylor_coeff_zero, eval_add, eval_pow, eval_X, eval_C]
  have hne : (φ ^ 2).order ≠ (PowerSeries.X ^ 3 : PowerSeries k).order := by
    rw [PowerSeries.order_pow, PowerSeries.order_X_pow]
    cases h : φ.order with
    | top => simp
    | coe n =>
      intro h'
      rw [two_nsmul] at h'
      have : n + n = 3 := by exact_mod_cast h'
      omega
  rw [PowerSeries.order_add_of_order_ne _ _ hne, PowerSeries.order_X_pow]
  exact min_le_right _ _

end Polyhedron

end Singularity
