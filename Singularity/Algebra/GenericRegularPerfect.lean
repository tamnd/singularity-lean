/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.GenericRegular
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.InvSubmonoid

/-!
# Generic regularity over a perfect field

Let `D` be a domain of finite type over a perfect field `k`. This file proves that the regular
locus of `D` contains a nonempty open set `D(f)`. With the criterion of Nagata, this gives that
the regular locus of an algebra of finite type over `k` is open.

The proof has these steps.

* Let `K` be the fraction field of `D`. Because `k` is perfect, `K` has a finite separating
  transcendence basis `s` over `k`. Thus `K` is separable over `k(s)`.
* A nonzero element `b` of `D` multiplies each element of `s` into `D`. Thus `s` is in `D_b`.
  Let `A₀ = k[X_s]`. The map `A₀ → D_b` is injective, because `s` is algebraically independent.
* Each generator of `D_b` is algebraic over `A₀`. Thus a nonzero element `g` of `A₀` makes each
  generator integral over `A = (A₀)_g`. Then `B = (D_b)_g` is finite over `A`.
* The ring `A` is regular and integrally closed, and `Frac B / Frac A` is `K / k(s)`, which is
  separable. The result over a regular base gives a nonempty open set `D(f)` in the regular locus
  of `B`.
* Each local ring of `B` is a local ring of `D`. Thus `D(f)` gives a nonempty open set in the
  regular locus of `D`.

## Main results

* `Singularity.Algebra.isRegularRing_of_isLocalization`: a localization of a regular ring is
  regular.
* `Singularity.Algebra.exists_ne_zero_basicOpen_subset_regularLocus_of_away`: generic regularity
  descends from a localization `D_h` to `D`.
* `Singularity.Algebra.exists_ne_zero_basicOpen_subset_regularLocus_of_perfectField`: generic
  regularity for a domain of finite type over a perfect field.
* `Singularity.Algebra.isOpen_regularLocus_of_perfectField`: the regular locus of an algebra of
  finite type over a perfect field is open.

## References

* [Mat89] H. Matsumura, *Commutative Ring Theory*, Section 24 and Theorem 26.2.
* [Stacks] The Stacks project, Tag 030W.
-/

universe u

open scoped nonZeroDivisors

namespace Singularity.Algebra

/-- A localization of a regular ring is regular. -/
theorem isRegularRing_of_isLocalization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsRegularRing R] (M : Submonoid R) [IsLocalization M S] : IsRegularRing S := by
  have : IsNoetherianRing S := IsLocalization.isNoetherianRing M S inferInstance
  rw [isRegularRing_iff]
  intro Q _
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
    (Localization.AtPrime Q) Q
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (Q.comap (algebraMap R S)).primeCompl
      (Localization.AtPrime (Q.comap (algebraMap R S))) (Localization.AtPrime Q)).toRingEquiv

/-- Let `B` be the localization of a domain `D` away from `h`. Suppose that the regular locus of
`B` contains a set `D(f)` with `f ≠ 0`. Then the regular locus of `D` contains a set `D(f')` with
`f' ≠ 0`. -/
theorem exists_ne_zero_basicOpen_subset_regularLocus_of_away {D B : Type*} [CommRing D]
    [IsDomain D] [CommRing B] [Algebra D B] (h : D) [IsLocalization.Away h B]
    (hB : ∃ f : B, f ≠ 0 ∧ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) ⊆ regularLocus B) :
    ∃ f : D, f ≠ 0 ∧ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆ regularLocus D := by
  obtain ⟨f, hf0, hf⟩ := hB
  obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers h) f
  have ha : a ≠ 0 := by
    rintro rfl
    exact hf0 (IsLocalization.mk'_zero _)
  have hh : h ≠ 0 := by
    rintro rfl
    have : Subsingleton B := IsLocalization.subsingleton (M := Submonoid.powers (0 : D))
      ⟨1, pow_one 0⟩
    exact hf0 (Subsingleton.elim _ _)
  refine ⟨h * a, mul_ne_zero hh ha, fun P hP => ?_⟩
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hP
  have hhP : h ∉ P.asIdeal := fun H => hP (P.asIdeal.mul_mem_right a H)
  have haP : a ∉ P.asIdeal := fun H => hP (P.asIdeal.mul_mem_left h H)
  have hdisj : Disjoint (Submonoid.powers h : Set D) P.asIdeal := by
    rw [Set.disjoint_left]
    rintro _ ⟨m, rfl⟩ hm
    exact hhP (P.isPrime.mem_of_pow_mem m hm)
  let Q : Ideal B := P.asIdeal.map (algebraMap D B)
  have hQ : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers h) B P.asIdeal P.isPrime hdisj
  have hQP : Q.comap (algebraMap D B) = P.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers h) B P.isPrime hdisj
  have hfQ : (⟨Q, hQ⟩ : PrimeSpectrum B) ∈ regularLocus B := by
    apply hf
    rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
    intro H
    apply haP
    rw [← hQP, Ideal.mem_comap, ← IsLocalization.mk'_spec B a m]
    exact Q.mul_mem_right _ H
  rw [mem_regularLocus] at hfQ ⊢
  have hloc := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Submonoid.powers h) (Localization.AtPrime Q) Q
  have hM : (Q.comap (algebraMap D B)).primeCompl = P.asIdeal.primeCompl := by
    ext z
    simp only [Ideal.mem_primeCompl_iff, hQP]
  have : IsLocalization P.asIdeal.primeCompl (Localization.AtPrime Q) := by
    rw [← hM]
    exact hloc
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv P.asIdeal.primeCompl
    (Localization.AtPrime P.asIdeal) (Localization.AtPrime Q)).toRingEquiv.symm

section Separable

attribute [local instance] FractionRing.liftAlgebra

variable {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
  [FaithfulSMul A B]

/-- Let `K_A` and `K_B` be fraction fields of `A` and `B` with compatible maps. Suppose that `K_B`
is separable over `K_A`. Then the fraction field of `B` is separable over the fraction field of
`A`. -/
theorem isSeparable_fractionRing_of_isFractionRing (KA KB : Type*) [Field KA] [Field KB]
    [Algebra A KA] [IsFractionRing A KA] [Algebra B KB] [IsFractionRing B KB] [Algebra KA KB]
    [Algebra A KB] [IsScalarTower A KA KB] [IsScalarTower A B KB] [Algebra.IsSeparable KA KB] :
    Algebra.IsSeparable (FractionRing A) (FractionRing B) := by
  have := FractionRing.isScalarTower_liftAlgebra A (FractionRing B)
  refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv A KA).symm.toRingEquiv
    (FractionRing.algEquiv B KB).symm.toRingEquiv ?_
  apply IsLocalization.ringHom_ext A⁰
  ext a
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv]
  rw [← IsScalarTower.algebraMap_apply A KA KB, IsScalarTower.algebraMap_apply A B KB,
    AlgEquiv.commutes, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply A B (FractionRing B)]

end Separable

section Perfect

attribute [local instance] FractionRing.liftAlgebra

/-- Generic regularity from a separating transcendence basis. Let `D` be a domain of finite type
over a field `k`, with fraction field `K`. Let `y` be a finite family in `D` whose image in `K` is
algebraically independent over `k`, such that `K` is separable over the field that this image
generates. Then there is `f ≠ 0` in `D` such that `D(f)` is in the regular locus of `D`. -/
theorem exists_ne_zero_basicOpen_subset_regularLocus_of_algebraicIndependent {k D K ι : Type u}
    [Field k] [CommRing D] [IsDomain D] [Algebra k D] [Algebra.FiniteType k D] [Field K]
    [Algebra D K] [IsFractionRing D K] [Algebra k K] [IsScalarTower k D K] [Finite ι]
    (y : ι → D) (hx : AlgebraicIndependent k (algebraMap D K ∘ y))
    [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range (algebraMap D K ∘ y))) K] :
    ∃ f : D, f ≠ 0 ∧ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆ regularLocus D := by
  classical
  set x := algebraMap D K ∘ y with hxdef
  let A0 := MvPolynomial ι k
  let φ : A0 →ₐ[k] D := MvPolynomial.aeval y
  let _ : Algebra A0 D := φ.toRingHom.toAlgebra
  let _ : Algebra A0 K := (MvPolynomial.aeval x).toRingHom.toAlgebra
  have hφK : ∀ p : A0, algebraMap D K (algebraMap A0 D p) = algebraMap A0 K p := fun p =>
    (MvPolynomial.comp_aeval_apply y (IsScalarTower.toAlgHom k D K) p).trans rfl
  have : IsScalarTower A0 D K := IsScalarTower.of_algebraMap_eq fun p => (hφK p).symm
  have : IsScalarTower k A0 D := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have hinj0 : Function.Injective (algebraMap A0 K) :=
    algebraicIndependent_iff_injective_aeval.mp hx
  have hφinj : Function.Injective (algebraMap A0 D) := by
    intro p q hpq
    apply hinj0
    rw [← hφK, ← hφK, hpq]
  have : FaithfulSMul A0 K := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj0
  have := FractionRing.isScalarTower_liftAlgebra A0 K
  -- The field `K` is separable over the fraction field of `A0`.
  have hsep0 : Algebra.IsSeparable (FractionRing A0) K := by
    refine Algebra.IsSeparable.of_equiv_equiv hx.aevalEquivField.symm.toRingEquiv
      (RingEquiv.refl K) ?_
    ext z
    exact hx.lift_reprField z
  -- Each element of `D` is algebraic over `A0`.
  have halg : ∀ z : D, IsAlgebraic A0 z := fun z => by
    have h1 : IsAlgebraic A0 (algebraMap D K z) :=
      (IsFractionRing.isAlgebraic_iff A0 (FractionRing A0) K).mpr
        (Algebra.IsAlgebraic.isAlgebraic _)
    exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom A0 D K)
      (IsFractionRing.injective D K)).mp h1
  choose c hc0 hc using fun z : D => (halg z).exists_integral_multiple
  obtain ⟨T, hT⟩ := Algebra.FiniteType.out (R := k) (A := D)
  let g : A0 := ∏ t ∈ T, c t
  have hg0 : g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ => hc0 t
  have hφg : algebraMap A0 D g ≠ 0 := fun h => hg0 (hφinj (h.trans (map_zero _).symm))
  let A := Localization.Away g
  let B := Localization.Away (algebraMap A0 D g)
  have hleA : Submonoid.powers g ≤ A0⁰ := powers_le_nonZeroDivisors_of_noZeroDivisors hg0
  have hleB : Submonoid.powers (algebraMap A0 D g) ≤ D⁰ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hφg
  have : IsDomain A := IsLocalization.isDomain_localization hleA
  have : IsDomain B := IsLocalization.isDomain_localization hleB
  -- The algebra structures.
  let _ : Algebra A B := (Localization.awayMap (algebraMap A0 D) g).toAlgebra
  have : IsScalarTower A0 A B := IsScalarTower.of_algebraMap_eq' <| by
    rw [IsScalarTower.algebraMap_eq A0 D B]
    have hy : Submonoid.powers g ≤
        (Submonoid.powers (algebraMap A0 D g)).comap (algebraMap A0 D) := by
      rintro _ ⟨n, rfl⟩
      exact ⟨n, (map_pow _ _ _).symm⟩
    exact RingHom.ext fun p => (IsLocalization.map_eq (S := A) (Q := B) hy p).symm
  let _ : Algebra B K := IsLocalization.localizationAlgebraOfSubmonoidLe B K _ _ hleB
  have : IsScalarTower D B K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le B K _ _ hleB
  have : IsFractionRing B K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers (algebraMap A0 D g)) B K
  let _ : Algebra A (FractionRing A0) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe A (FractionRing A0) _ _ hleA
  have : IsScalarTower A0 A (FractionRing A0) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le A (FractionRing A0) _ _ hleA
  have : IsFractionRing A (FractionRing A0) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers g) A _
  let _ : Algebra A K :=
    ((algebraMap (FractionRing A0) K).comp (algebraMap A (FractionRing A0))).toAlgebra
  have : IsScalarTower A (FractionRing A0) K := IsScalarTower.of_algebraMap_eq' rfl
  have hAB : (algebraMap B K).comp (algebraMap A B) =
      (algebraMap (FractionRing A0) K).comp (algebraMap A (FractionRing A0)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    rw [RingHom.comp_assoc, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq A0 A B,
      ← IsScalarTower.algebraMap_eq A0 A (FractionRing A0),
      ← IsScalarTower.algebraMap_eq A0 (FractionRing A0) K, IsScalarTower.algebraMap_eq A0 D B,
      ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq D B K,
      ← IsScalarTower.algebraMap_eq A0 D K]
  have : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq' hAB.symm
  have : FaithfulSMul A B := by
    rw [faithfulSMul_iff_algebraMap_injective]
    refine Function.Injective.of_comp (f := algebraMap B K) ?_
    rw [← RingHom.coe_comp, hAB, RingHom.coe_comp]
    exact (RingHom.injective _).comp (IsFractionRing.injective A (FractionRing A0))
  -- The ring `B` is finite over `A`.
  have hT' : ∀ t ∈ T, IsIntegral A (algebraMap D B t) := by
    intro t ht
    obtain ⟨u, hu⟩ := isUnit_of_dvd_unit (map_dvd (algebraMap A0 A) (Finset.dvd_prod_of_mem c ht))
      (IsLocalization.Away.algebraMap_isUnit g)
    refine IsIntegral.of_mul_unit (r := ↑u⁻¹) (y := algebraMap A B u) ?_ ?_
    · rw [← map_mul, Units.inv_mul, map_one]
    · rw [hu, ← IsScalarTower.algebraMap_apply A0 A B, IsScalarTower.algebraMap_apply A0 D B,
        ← map_mul, mul_comm, ← Algebra.smul_def]
      exact ((hc t).map (IsScalarTower.toAlgHom A0 D B)).tower_top
  have hD : ∀ z : D, IsIntegral A (algebraMap D B z) := by
    intro z
    have hz : z ∈ Algebra.adjoin k (T : Set D) := hT ▸ Algebra.mem_top
    induction hz using Algebra.adjoin_induction with
    | mem t ht => exact hT' t ht
    | algebraMap r =>
      rw [IsScalarTower.algebraMap_apply k A0 D, ← IsScalarTower.algebraMap_apply A0 D B,
        IsScalarTower.algebraMap_apply A0 A B]
      exact isIntegral_algebraMap
    | add _ _ _ _ h1 h2 =>
      rw [map_add]
      exact h1.add h2
    | mul _ _ _ _ h1 h2 =>
      rw [map_mul]
      exact h1.mul h2
  have : Algebra.IsIntegral A B := by
    constructor
    intro z
    obtain ⟨⟨w, _, n, rfl⟩, hw⟩ := IsLocalization.surj (Submonoid.powers (algebraMap A0 D g)) z
    obtain ⟨u, hu⟩ := (IsLocalization.Away.algebraMap_isUnit (S := A) g).pow n
    refine IsIntegral.of_mul_unit (r := ↑u⁻¹) (y := algebraMap A B u) ?_ ?_
    · rw [← map_mul, Units.inv_mul, map_one]
    · rw [hu, ← map_pow, ← IsScalarTower.algebraMap_apply A0 A B,
        IsScalarTower.algebraMap_apply A0 D B, map_pow]
      have hw' : z * algebraMap D B (algebraMap A0 D g ^ n) = algebraMap D B w := hw
      rw [hw']
      exact hD w
  have : Algebra.FiniteType D B :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (algebraMap A0 D g)) B
  have : Algebra.FiniteType k B := Algebra.FiniteType.trans (S := D) inferInstance inferInstance
  have : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply k A0 A, ← IsScalarTower.algebraMap_apply A0 A B,
      IsScalarTower.algebraMap_apply A0 D B, ← IsScalarTower.algebraMap_apply k A0 D,
      ← IsScalarTower.algebraMap_apply k D B]
  have : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType k A B
  have : Module.Finite A B := Algebra.IsIntegral.finite
  -- The ring `A` is regular and integrally closed.
  have : IsRegularRing A := isRegularRing_of_isLocalization (Submonoid.powers g)
  have : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A (Submonoid.powers g) hleA
  -- The extension of fraction fields is separable.
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    isSeparable_fractionRing_of_isFractionRing (FractionRing A0) K
  exact exists_ne_zero_basicOpen_subset_regularLocus_of_away (algebraMap A0 D g)
    (exists_ne_zero_basicOpen_subset_regularLocus_of_isSeparable (A := A) (B := B))

end Perfect

/-- Generic regularity over a perfect field. Let `D` be a domain of finite type over a perfect
field `k`. Then there is `f ≠ 0` in `D` such that `D(f)` is in the regular locus of `D`. -/
theorem exists_ne_zero_basicOpen_subset_regularLocus_of_perfectField (k : Type u) [Field k]
    [PerfectField k] (D : Type u) [CommRing D] [IsDomain D] [Algebra k D]
    [Algebra.FiniteType k D] :
    ∃ f : D, f ≠ 0 ∧ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆ regularLocus D := by
  classical
  let K := FractionRing D
  have : Algebra.EssFiniteType k K := inferInstanceAs (Algebra.EssFiniteType k (Localization D⁰))
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  obtain ⟨⟨b, hb⟩, hbs⟩ := IsLocalization.exist_integer_multiples_of_finset D⁰ s
  choose a ha using fun z hz => RingHom.mem_rangeS.mp (hbs z hz)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hle : Submonoid.powers b ≤ D⁰ := powers_le_nonZeroDivisors_of_noZeroDivisors hb0
  let D₁ := Localization.Away b
  have : IsDomain D₁ := IsLocalization.isDomain_localization hle
  let _ : Algebra D₁ K := IsLocalization.localizationAlgebraOfSubmonoidLe D₁ K _ _ hle
  have : IsScalarTower D D₁ K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le D₁ K _ _ hle
  have : IsFractionRing D₁ K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers b) D₁ K
  have : IsScalarTower k D₁ K := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply k D D₁, ← IsScalarTower.algebraMap_apply D D₁ K,
      ← IsScalarTower.algebraMap_apply k D K]
  have : Algebra.FiniteType D D₁ := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers b) D₁
  have : Algebra.FiniteType k D₁ := Algebra.FiniteType.trans (S := D) inferInstance inferInstance
  let y : s → D₁ := fun z => IsLocalization.mk' D₁ (a z z.2) (⟨b, 1, pow_one b⟩ :
    Submonoid.powers b)
  have hy : algebraMap D₁ K ∘ y = Subtype.val := by
    funext z
    simp only [Function.comp_apply, y]
    rw [← IsLocalization.mk'_eq_algebraMap_mk'_of_submonoid_le (S := D₁) (T := K) (h := hle),
      IsLocalization.mk'_eq_iff_eq_mul, ha, Algebra.smul_def, mul_comm]
  have hrange : Set.range (algebraMap D₁ K ∘ y) = (s : Set K) := by
    rw [hy]
    ext z
    simp
  have : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range (algebraMap D₁ K ∘ y))) K := by
    rw [hrange]
    exact hsep
  have hx : AlgebraicIndependent k (algebraMap D₁ K ∘ y) := by
    rw [hy]
    exact hs.1
  exact exists_ne_zero_basicOpen_subset_regularLocus_of_away b
    (exists_ne_zero_basicOpen_subset_regularLocus_of_algebraicIndependent y hx)

/-- The regular locus of an algebra of finite type over a perfect field is open. This follows
from generic regularity and the criterion of Nagata. -/
theorem isOpen_regularLocus_of_perfectField (k : Type u) [Field k] [PerfectField k] (R : Type u)
    [CommRing R] [Algebra k R] [Algebra.FiniteType k R] : IsOpen (regularLocus R) := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  refine isOpen_regularLocus_of_exists_isOpen fun p _ => ?_
  obtain ⟨f, hf, hsub⟩ :=
    exists_ne_zero_basicOpen_subset_regularLocus_of_perfectField k (R ⧸ p.asIdeal)
  refine ⟨_, (PrimeSpectrum.basicOpen f).isOpen, ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩, hsub⟩
  simpa [PrimeSpectrum.mem_basicOpen] using hf

end Singularity.Algebra
