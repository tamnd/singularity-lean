/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.FlatDescent
import Singularity.Algebra.GenericRegularPerfect
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.TranscendentalSeparable
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.RingHom.Flat

/-!
# The regular locus over an arbitrary field

Let `k` be a field, possibly imperfect. This file proves that the regular locus of an algebra of
finite type over `k` is open. By the criterion of Nagata, it is enough to show that each domain
`D` of finite type over `k` is generically regular: there is `f ≠ 0` in `D` such that `D(f)` is
in the regular locus of `D`.

If `k` is perfect, this is in `Singularity.Algebra.GenericRegularPerfect`. The proof uses a
separating transcendence basis of the fraction field of `D`. Over an imperfect field, such a basis
need not exist. The proof here follows the Stacks project (Lemma 07PJ and its preparation).

## The proof

* Generic regularity holds for a domain `D` whose fraction field `K` has a finite separating
  transcendence basis over `k`. The proof is the one for a perfect field.
* Generic regularity goes down along a finite injective map `D → S` of Noetherian domains. A
  nonzero element `c` of `D` is in the ideal `g S`, where `D(g)` is in the regular locus of `S`.
  By generic freeness, there is `r ≠ 0` in `D` such that `S_r` is free over `D_r`. For a prime
  `p` of `D` with `c r ∉ p`, take a prime `q` of `S` over `p`. The map `D_p → S_q` is flat and
  local, and `S_q` is regular. By flat descent ([Mat89, Theorem 23.7 (i)]), `D_p` is regular.
* Let `Ω` be an algebraic closure of `K`, and let `P` be the perfect closure of `k` in `Ω`. Let
  `X` be a finite set of generators of `D` over `k`, and let `F = P(X)`. Because `P` is perfect,
  `F` has a finite separating transcendence basis `s` over `P`. Only finitely many elements of `P`
  are needed to write the elements of `s` in terms of `X`, and to write the coefficients of the
  minimal polynomials of the elements of `X` over `P(s)` in terms of `s`. These elements generate
  a finite extension `L` of `k` in `P`.
* Let `S = L[X]`, a domain in `F`. Its fraction field `L(X)` contains `s`, and `s` is a separating
  transcendence basis of `L(X)` over `L`. Thus `S` is generically regular. The ring `S` is finite
  over `D`, because `L` is finite over `k`. Generic regularity goes down from `S` to `D`.

## Main results

* `Singularity.Algebra.basicOpen_subset_regularLocus_of_flat`: the regular locus goes down along a
  flat injective integral map.
* `Singularity.Algebra.exists_ne_zero_basicOpen_subset_regularLocus_of_finite`: generic regularity
  goes down along a finite injective map of Noetherian domains.
* `Singularity.Algebra.exists_ne_zero_basicOpen_subset_regularLocus_of_isSeparablyGenerated`:
  generic regularity for a domain whose fraction field is separably generated over `k`.
* `Singularity.Algebra.exists_ne_zero_basicOpen_subset_regularLocus_of_finiteType`: generic
  regularity for a domain of finite type over an arbitrary field.
* `Singularity.Algebra.isOpen_regularLocus_of_field`: the regular locus of an algebra of finite
  type over an arbitrary field is open.

## References

* [Mat89] H. Matsumura, *Commutative Ring Theory*, Theorem 23.7 and Section 24.
* [Stacks] The Stacks project, Tags 07P7, 07PJ, 030W, 051R.
* [EGA IV] A. Grothendieck, *Éléments de géométrie algébrique IV*, 6.12.5.
-/

universe u

open scoped nonZeroDivisors

namespace Singularity.Algebra

/-- Let `S` be a localization of `R`. A prime of `S` is in the regular locus of `S` if the prime
of `R` under it is in the regular locus of `R`. -/
theorem mem_regularLocus_of_isLocalization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (Q : PrimeSpectrum S)
    (h : PrimeSpectrum.comap (algebraMap R S) Q ∈ regularLocus R) : Q ∈ regularLocus S := by
  rw [mem_regularLocus] at h ⊢
  have : IsRegularLocalRing (Localization.AtPrime (Q.asIdeal.comap (algebraMap R S))) := h
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
    (Localization.AtPrime Q.asIdeal) Q.asIdeal
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (Q.asIdeal.comap (algebraMap R S)).primeCompl
      (Localization.AtPrime (Q.asIdeal.comap (algebraMap R S)))
      (Localization.AtPrime Q.asIdeal)).toRingEquiv

/-- The regular locus goes down along a flat injective integral map. Let `D → S` be flat,
injective and integral, with `D` Noetherian. Let `g ∈ S` divide the image of `c ∈ D`. If `D(g)`
is in the regular locus of `S`, then `D(c)` is in the regular locus of `D`. -/
theorem basicOpen_subset_regularLocus_of_flat {D S : Type u} [CommRing D] [IsNoetherianRing D]
    [CommRing S] [Algebra D S] [Module.Flat D S] [Algebra.IsIntegral D S]
    (hinj : Function.Injective (algebraMap D S)) {c : D} {g : S} (hcg : g ∣ algebraMap D S c)
    (hg : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆ regularLocus S) :
    (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum D)) ⊆ regularLocus D := by
  intro P hP
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hP
  have hbot : (⊥ : Ideal S).comap (algebraMap D S) ≤ P.asIdeal := by
    rw [Ideal.comap_bot_of_injective _ hinj]
    exact bot_le
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P.asIdeal (⊥ : Ideal S) hbot
  have hgQ : g ∉ Q := by
    intro h
    apply hP
    rw [← hQP]
    obtain ⟨u, hu⟩ := hcg
    change algebraMap D S c ∈ Q
    rw [hu]
    exact Q.mul_mem_right u h
  have hreg : IsRegularLocalRing (Localization.AtPrime Q) :=
    mem_regularLocus.mp (@hg ⟨Q, hQ⟩ ((PrimeSpectrum.mem_basicOpen _ _).mpr hgQ))
  rw [mem_regularLocus]
  have hQP' : P.asIdeal = Q.comap (algebraMap D S) := hQP.symm
  have hφ : (Localization.localRingHom P.asIdeal Q (algebraMap D S) hQP').Flat :=
    RingHom.Flat.localRingHom (RingHom.flat_algebraMap_iff.mpr inferInstance) Q P.asIdeal hQP'
  let _ : Algebra (Localization.AtPrime P.asIdeal) (Localization.AtPrime Q) :=
    (Localization.localRingHom P.asIdeal Q (algebraMap D S) hQP').toAlgebra
  have : Module.Flat (Localization.AtPrime P.asIdeal) (Localization.AtPrime Q) := hφ
  have : IsLocalHom (algebraMap (Localization.AtPrime P.asIdeal) (Localization.AtPrime Q)) :=
    Localization.isLocalHom_localRingHom P.asIdeal Q (algebraMap D S) hQP'
  have : IsNoetherianRing (Localization.AtPrime P.asIdeal) :=
    IsLocalization.isNoetherianRing P.asIdeal.primeCompl _ inferInstance
  exact isRegularLocalRing_of_flat (B := Localization.AtPrime Q)

/-- Generic regularity goes down along a finite injective map of Noetherian domains. Let
`D → S` be finite and injective, where `D` and `S` are domains and `D` is Noetherian. Suppose
that the regular locus of `S` contains a set `D(g)` with `g ≠ 0`. Then the regular locus of `D`
contains a set `D(f)` with `f ≠ 0`. -/
theorem exists_ne_zero_basicOpen_subset_regularLocus_of_finite {D S : Type u} [CommRing D]
    [IsDomain D] [IsNoetherianRing D] [CommRing S] [IsDomain S] [Algebra D S] [Module.Finite D S]
    (hinj : Function.Injective (algebraMap D S))
    (hS : ∃ g : S, g ≠ 0 ∧ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆ regularLocus S) :
    ∃ f : D, f ≠ 0 ∧ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆ regularLocus D := by
  obtain ⟨g, hg0, hg⟩ := hS
  have hI := Ideal.under_ne_bot_of_algebraic_mem hg0 (Ideal.mem_span_singleton_self g)
    (Algebra.IsIntegral.isIntegral (R := D) g).isAlgebraic
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hcg : g ∣ algebraMap D S c := Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp hc)
  have : Module.FinitePresentation D S := Module.finitePresentation_of_finite D S
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers D⁰
    (LocalizedModule.mkLinearMap D⁰ S) (FractionRing D)
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  have hle : Submonoid.powers r ≤ D⁰ := powers_le_nonZeroDivisors_of_noZeroDivisors hr0
  let Dr := Localization.Away r
  let Sr := Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers r))
  have : IsDomain Dr := IsLocalization.isDomain_localization hle
  have : IsNoetherianRing Dr :=
    IsLocalization.isNoetherianRing (Submonoid.powers r) Dr inferInstance
  have : Module.Flat Dr Sr := by
    let e := (IsLocalizedModule.iso (Submonoid.powers r)
      (IsScalarTower.toAlgHom D S Sr).toLinearMap).extendScalarsOfIsLocalization
        (Submonoid.powers r) Dr
    have : Module.Free Dr Sr := Module.Free.of_equiv e
    infer_instance
  have : Algebra.IsIntegral Dr Sr := ⟨isIntegral_localization⟩
  have hinjr : Function.Injective (algebraMap Dr Sr) :=
    localizationAlgebra_injective (M := Submonoid.powers r) (S := S) (Rₘ := Dr) (Sₘ := Sr) hinj
  have hDr : ∃ f : Dr, f ≠ 0 ∧
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum Dr)) ⊆ regularLocus Dr := by
    refine ⟨algebraMap D Dr c, (map_ne_zero_iff _ (IsLocalization.injective Dr hle)).mpr hc0,
      basicOpen_subset_regularLocus_of_flat hinjr (g := algebraMap S Sr g) ?_ ?_⟩
    · rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply D S Sr]
      exact map_dvd _ hcg
    · intro Q hQ
      apply mem_regularLocus_of_isLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers r))
      apply hg
      rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hQ ⊢
      exact hQ
  exact exists_ne_zero_basicOpen_subset_regularLocus_of_away r hDr

/-- Generic regularity from a separating transcendence basis in the fraction field. Let `D` be a
domain of finite type over a field `k`, with fraction field `K`. Let `x` be a finite family in `K`
that is algebraically independent over `k`, such that `K` is separable over `k(x)`. Then there is
`f ≠ 0` in `D` such that `D(f)` is in the regular locus of `D`. -/
theorem exists_ne_zero_basicOpen_subset_regularLocus_of_isSeparable_adjoin {k D K ι : Type u}
    [Field k] [CommRing D] [IsDomain D] [Algebra k D] [Algebra.FiniteType k D] [Field K]
    [Algebra D K] [IsFractionRing D K] [Algebra k K] [IsScalarTower k D K] [Finite ι]
    (x : ι → K) (hx : AlgebraicIndependent k x)
    [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K] :
    ∃ f : D, f ≠ 0 ∧ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆ regularLocus D := by
  classical
  obtain ⟨⟨b, hb⟩, hbx⟩ := IsLocalization.exist_integer_multiples_of_finite D⁰ x
  choose a ha using fun i => RingHom.mem_rangeS.mp (hbx i)
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
  let y : ι → D₁ := fun i => IsLocalization.mk' D₁ (a i) (⟨b, 1, pow_one b⟩ :
    Submonoid.powers b)
  have hy : algebraMap D₁ K ∘ y = x := by
    funext i
    simp only [Function.comp_apply, y]
    rw [← IsLocalization.mk'_eq_algebraMap_mk'_of_submonoid_le (S := D₁) (T := K) (h := hle),
      IsLocalization.mk'_eq_iff_eq_mul, ha, Algebra.smul_def, mul_comm]
  have : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range (algebraMap D₁ K ∘ y))) K := by
    rw [hy]
    infer_instance
  have hx' : AlgebraicIndependent k (algebraMap D₁ K ∘ y) := by
    rw [hy]
    exact hx
  exact exists_ne_zero_basicOpen_subset_regularLocus_of_away b
    (exists_ne_zero_basicOpen_subset_regularLocus_of_algebraicIndependent y hx')

/-- Generic regularity for a separably generated fraction field. Let `D` be a domain of finite
type over a field `k`, whose fraction field is separably generated over `k`. Then there is
`f ≠ 0` in `D` such that `D(f)` is in the regular locus of `D`. -/
theorem exists_ne_zero_basicOpen_subset_regularLocus_of_isSeparablyGenerated (k : Type u)
    [Field k] (D : Type u) [CommRing D] [IsDomain D] [Algebra k D] [Algebra.FiniteType k D]
    [Algebra.IsSeparablyGenerated k (FractionRing D)] :
    ∃ f : D, f ≠ 0 ∧ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆ regularLocus D := by
  obtain ⟨s, hs, hsep⟩ :=
    (Algebra.isSeparablyGenerated_iff k (FractionRing D)).mp inferInstance
  have : Algebra.EssFiniteType k (FractionRing D) :=
    inferInstanceAs (Algebra.EssFiniteType k (Localization D⁰))
  have : Finite s := finite_of_isTranscendenceBasis hs
  have : Algebra.IsSeparable (IntermediateField.adjoin k
      (Set.range ((↑) : s → FractionRing D))) (FractionRing D) := by
    rwa [Subtype.range_coe]
  exact exists_ne_zero_basicOpen_subset_regularLocus_of_isSeparable_adjoin
    (D := D) ((↑) : s → FractionRing D) hs.1

/-- Let `P` be a field over `k`, and let `F` be a field over `P`. Each element of the field
generated by a set `T` over `P` is in the field generated over `k` by `T` and finitely many
elements of `P`. -/
theorem exists_finset_mem_adjoin_union {k P F : Type*} [Field k] [Field P] [Field F]
    [Algebra k P] [Algebra P F] [Algebra k F] [IsScalarTower k P F] {T : Set F} {z : F}
    (hz : z ∈ IntermediateField.adjoin P T) :
    ∃ E : Finset P, z ∈ IntermediateField.adjoin k (algebraMap P F '' (E : Set P) ∪ T) := by
  classical
  let N := IntermediateField.adjoin k (Set.range (algebraMap P F) ∪ T)
  let N' : IntermediateField P F := N.toSubfield.toIntermediateField fun p =>
    IntermediateField.subset_adjoin k _ (Or.inl ⟨p, rfl⟩)
  have hle : IntermediateField.adjoin P T ≤ N' :=
    IntermediateField.adjoin_le_iff.mpr fun t ht => IntermediateField.subset_adjoin k _ (Or.inr ht)
  have hzN : z ∈ N := hle hz
  obtain ⟨t, ht, hzt⟩ := IntermediateField.exists_finset_of_mem_adjoin hzN
  refine ⟨t.preimage (algebraMap P F) fun _ _ _ _ h => (algebraMap P F).injective h, ?_⟩
  refine IntermediateField.adjoin.mono k _ _ ?_ hzt
  intro w hw
  rcases ht hw with ⟨p, rfl⟩ | hT
  · exact Or.inl ⟨p, Finset.mem_preimage.mpr hw, rfl⟩
  · exact Or.inr hT

/-- Let `z` be separable over a field `A`. If the coefficients of the minimal polynomial of `z`
over `A` come from a field `B`, then `z` is separable over `B`. -/
theorem isSeparable_of_coeff_mem_range {A B E : Type*} [Field A] [Field B] [Field E]
    [Algebra A E] [Algebra B E] {z : E} (hz : IsSeparable A z)
    (hc : ∀ n, algebraMap A E ((minpoly A z).coeff n) ∈ Set.range (algebraMap B E)) :
    IsSeparable B z := by
  have hl : (minpoly A z).map (algebraMap A E) ∈ Polynomial.lifts (algebraMap B E) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    exact hc n
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts _).mp hl
  have hsep : q.Separable := by
    rw [← Polynomial.separable_map (algebraMap B E), hq, Polynomial.separable_map]
    exact hz
  have hq0 : Polynomial.aeval z q = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hq, Polynomial.eval_map,
      ← Polynomial.aeval_def, minpoly.aeval]
  exact hsep.of_dvd (minpoly.dvd B z hq0)

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- Generic regularity after a finite extension of the base field. Let `D` be a domain of finite
type over `k`, generated by a finite set `X`. Let `φ : D → F` be an injective map to a field, and
let `L ⊆ F` be a finite extension of `k`. Let `y` be a finite family in `L(φ X)` that is
algebraically independent over `L`, such that each element of `φ X` is separable over `L(y)`.
Then there is `f ≠ 0` in `D` such that `D(f)` is in the regular locus of `D`.

The proof applies generic regularity to the domain `L[φ X]`, whose fraction field is separably
generated over `L`. This domain is finite over `D`, so generic regularity goes down to `D`. -/
theorem exists_ne_zero_basicOpen_subset_regularLocus_of_finiteDimensional {k D L F ι : Type u}
    [Field k] [CommRing D] [IsDomain D] [Algebra k D] [Algebra.FiniteType k D] [Field L]
    [Algebra k L] [FiniteDimensional k L] [Field F] [Algebra k F] [Algebra L F]
    [IsScalarTower k L F] [Finite ι] (φ : D →ₐ[k] F) (hφ : Function.Injective φ) (X : Finset D)
    (hX : Algebra.adjoin k (X : Set D) = ⊤) (y : ι → F)
    (hyK : ∀ i, y i ∈ IntermediateField.adjoin L (φ '' (X : Set D)))
    (hyalg : AlgebraicIndependent L y)
    (hsep : ∀ x ∈ X, IsSeparable (IntermediateField.adjoin L (Set.range y)) (φ x)) :
    ∃ f : D, f ≠ 0 ∧ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆ regularLocus D := by
  classical
  have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing k D
  let T : Set F := φ '' (X : Set D)
  let K_L := IntermediateField.adjoin L T
  let S_L := Algebra.adjoin L T
  -- The finite injective map `D → L[φ X]`.
  have hDS : ∀ d, φ d ∈ S_L := by
    intro d
    have hd : d ∈ Algebra.adjoin k (X : Set D) := hX ▸ Algebra.mem_top
    induction hd using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | algebraMap r =>
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply k L F]
      exact S_L.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact S_L.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact S_L.mul_mem hx hy
  let _ : Algebra D S_L := (φ.toRingHom.codRestrict S_L hDS).toAlgebra
  have hinj : Function.Injective (algebraMap D S_L) :=
    fun a b h => hφ (congrArg Subtype.val h)
  have : IsScalarTower k D S_L := IsScalarTower.of_algebraMap_eq fun r =>
    Subtype.ext (φ.commutes r).symm
  have : Algebra.FiniteType L S_L :=
    Algebra.FiniteType.adjoin_of_finite (X.finite_toSet.image φ)
  have : Algebra.FiniteType k S_L := Algebra.FiniteType.trans (S := L) inferInstance inferInstance
  have : Algebra.FiniteType D S_L := Algebra.FiniteType.of_restrictScalars_finiteType k D S_L
  have : Algebra.IsIntegral D S_L := by
    constructor
    rintro ⟨w, hw⟩
    induction hw using Algebra.adjoin_induction with
    | mem w hw =>
      obtain ⟨x, -, rfl⟩ := hw
      exact isIntegral_algebraMap (x := x)
    | algebraMap l =>
      have hl : IsIntegral k (algebraMap L S_L l) :=
        (Algebra.IsIntegral.isIntegral l).map (IsScalarTower.toAlgHom k L S_L)
      exact hl.tower_top
    | add w₁ w₂ _ _ i₁ i₂ => exact IsIntegral.add i₁ i₂
    | mul w₁ w₂ _ _ i₁ i₂ => exact IsIntegral.mul i₁ i₂
  have : Module.Finite D S_L := Algebra.IsIntegral.finite
  -- The family `y` is a separating transcendence basis of `L(φ X)` over `L`.
  let y' : ι → K_L := fun i => ⟨y i, hyK i⟩
  have hyalg' : AlgebraicIndependent L y' := AlgebraicIndependent.of_comp K_L.val hyalg
  let M := IntermediateField.adjoin L (Set.range y')
  have hMmap : IntermediateField.adjoin L (Set.range y) ≤ M.map K_L.val := by
    change _ ≤ (IntermediateField.adjoin L (Set.range y')).map K_L.val
    rw [IntermediateField.adjoin_map, ← Set.range_comp]
    exact le_rfl
  let xK : X → K_L := fun x => ⟨φ x, IntermediateField.subset_adjoin L T ⟨x, x.2, rfl⟩⟩
  have hsepx : ∀ x : X, IsSeparable M (xK x) := by
    intro x
    have hB : IsSeparable M (algebraMap K_L F (xK x)) := by
      apply isSeparable_of_coeff_mem_range (hsep x x.2)
      intro n
      have h := hMmap ((minpoly (IntermediateField.adjoin L (Set.range y)) (φ x)).coeff n).2
      rw [IntermediateField.mem_map] at h
      obtain ⟨m, hm, hmz⟩ := h
      exact ⟨⟨m, hm⟩, hmz⟩
    unfold IsSeparable at hB ⊢
    rwa [minpoly.algebraMap_eq (algebraMap K_L F).injective] at hB
  have hKtop : IntermediateField.adjoin L (Set.range xK) = ⊤ := by
    apply IntermediateField.map_injective K_L.val
    rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val, ← Set.range_comp]
    change IntermediateField.adjoin L (Set.range fun x : X => φ x) = IntermediateField.adjoin L T
    congr 1
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have : Algebra.IsSeparable (IntermediateField.adjoin L (Set.range y')) K_L := by
    rw [← separableClosure.eq_top_iff, eq_top_iff]
    intro z _
    have hle : IntermediateField.adjoin L (Set.range xK) ≤
        (separableClosure M K_L).restrictScalars L := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      exact hsepx x
    exact hle (by rw [hKtop]; exact IntermediateField.mem_top)
  exact exists_ne_zero_basicOpen_subset_regularLocus_of_finite hinj
    (exists_ne_zero_basicOpen_subset_regularLocus_of_isSeparable_adjoin (k := L) (D := S_L)
      (K := K_L) y' hyalg')

/-- Generic regularity over an arbitrary field. Let `D` be a domain of finite type over a field
`k`. Then there is `f ≠ 0` in `D` such that `D(f)` is in the regular locus of `D`.

Let `P` be the perfect closure of `k` in an algebraic closure of the fraction field of `D`. Let
`X` generate `D`, and let `s` be a separating transcendence basis of `F = P(X)` over `P`. A finite
extension `L` of `k` in `P` is enough to write `s` in terms of `X`, and the minimal polynomials
of `X` over `P(s)` in terms of `s`. Then `exists_ne_zero_basicOpen_subset_regularLocus_of_finiteDimensional`
applies. -/
theorem exists_ne_zero_basicOpen_subset_regularLocus_of_finiteType (k : Type u) [Field k]
    (D : Type u) [CommRing D] [IsDomain D] [Algebra k D] [Algebra.FiniteType k D] :
    ∃ f : D, f ≠ 0 ∧ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆ regularLocus D := by
  classical
  -- The field `F = P(X)`, where `P` is the perfect closure of `k` in `Ω`.
  let K := FractionRing D
  let Ω := AlgebraicClosure K
  let ι : D →ₐ[k] Ω := (IsScalarTower.toAlgHom k K Ω).comp (IsScalarTower.toAlgHom k D K)
  have hι : Function.Injective ι :=
    (algebraMap K Ω).injective.comp (IsFractionRing.injective D K)
  obtain ⟨X, hX⟩ := Algebra.FiniteType.out (R := k) (A := D)
  let P := perfectClosure k Ω
  let F := IntermediateField.adjoin P (ι '' (X : Set D))
  have hιF : ∀ d, ι d ∈ F := by
    intro d
    have hd : d ∈ Algebra.adjoin k (X : Set D) := hX ▸ Algebra.mem_top
    induction hd using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
    | algebraMap r =>
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply k P Ω]
      exact F.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact F.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact F.mul_mem hx hy
  let ιF : D →ₐ[k] F :=
    { toFun := fun d => ⟨ι d, hιF d⟩
      map_one' := Subtype.ext (map_one ι)
      map_mul' := fun a b => Subtype.ext (map_mul ι a b)
      map_zero' := Subtype.ext (map_zero ι)
      map_add' := fun a b => Subtype.ext (map_add ι a b)
      commutes' := fun r => Subtype.ext (ι.commutes r) }
  have hιF_inj : Function.Injective ιF := fun a b h => hι (congrArg Subtype.val h)
  let T : Set F := ιF '' (X : Set D)
  have hFtop : IntermediateField.adjoin P T = ⊤ := by
    apply IntermediateField.map_injective F.val
    rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val, Set.image_image]
    rfl
  -- A separating transcendence basis `s` of `F` over `P`.
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField P F
  let A := IntermediateField.adjoin P (s : Set F)
  -- Finitely many elements of `P` are needed.
  have h1 : ∀ i : s, ∃ E : Finset P,
      (i : F) ∈ IntermediateField.adjoin k (algebraMap P F '' (E : Set P) ∪ T) :=
    fun i => exists_finset_mem_adjoin_union (by rw [hFtop]; exact IntermediateField.mem_top)
  have h2 : ∀ (x : X) (n : ℕ), ∃ E : Finset P, algebraMap A F ((minpoly A (ιF x)).coeff n) ∈
      IntermediateField.adjoin k (algebraMap P F '' (E : Set P) ∪ (s : Set F)) :=
    fun x n => exists_finset_mem_adjoin_union ((minpoly A (ιF x)).coeff n).2
  choose E1 hE1 using h1
  choose E2 hE2 using h2
  obtain ⟨E, hE1sub, hE2sub⟩ : ∃ E : Finset P, (∀ i, E1 i ⊆ E) ∧
      ∀ (x : X) n, n ∈ (minpoly A (ιF x)).support → E2 x n ⊆ E := by
    refine ⟨Finset.univ.biUnion E1 ∪
      Finset.univ.biUnion fun x : X => (minpoly A (ιF x)).support.biUnion (E2 x), ?_, ?_⟩
    · intro i p hp
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hp⟩)
    · intro x n hn p hp
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨x, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨n, hn, hp⟩⟩)
  -- The finite extension `L` of `k`.
  let L := IntermediateField.adjoin k (E : Set P)
  have : FiniteDimensional k L :=
    IntermediateField.finiteDimensional_adjoin fun p _ => Algebra.IsIntegral.isIntegral p
  have hmono : ∀ E' : Finset P, E' ⊆ E → ∀ (T' : Set F) (z : F),
      z ∈ IntermediateField.adjoin k (algebraMap P F '' (E' : Set P) ∪ T') →
        z ∈ IntermediateField.adjoin L T' := by
    intro E' hE' T' z hz
    have hle : IntermediateField.adjoin k (algebraMap P F '' (E' : Set P) ∪ T') ≤
        (IntermediateField.adjoin L T').restrictScalars k := by
      rw [IntermediateField.adjoin_le_iff]
      rintro w (⟨p, hp, rfl⟩ | hw)
      · have hpL : p ∈ L := IntermediateField.subset_adjoin k _ (hE' hp)
        exact (IntermediateField.adjoin L T').algebraMap_mem ⟨p, hpL⟩
      · exact IntermediateField.subset_adjoin L T' hw
    exact hle hz
  refine exists_ne_zero_basicOpen_subset_regularLocus_of_finiteDimensional (L := L) ιF hιF_inj X
    hX ((↑) : s → F) (fun i => hmono (E1 i) (hE1sub i) _ _ (hE1 i))
    (hs.1.restrictScalars (K := P) (algebraMap L P).injective) fun x hx => ?_
  apply isSeparable_of_coeff_mem_range (Algebra.IsSeparable.isSeparable A (ιF x))
  intro n
  by_cases hn : n ∈ (minpoly A (ιF x)).support
  · have hz := hmono (E2 ⟨x, hx⟩ n) (hE2sub ⟨x, hx⟩ n hn) _ _ (hE2 ⟨x, hx⟩ n)
    have hrange : Set.range ((↑) : s → F) = (s : Set F) := Subtype.range_coe
    rw [← hrange] at hz
    exact ⟨⟨_, hz⟩, rfl⟩
  · rw [Polynomial.notMem_support_iff.mp hn, map_zero]
    exact ⟨0, map_zero _⟩

/-- The regular locus of an algebra of finite type over an arbitrary field is open. This follows
from generic regularity and the criterion of Nagata. -/
theorem isOpen_regularLocus_of_field (k : Type u) [Field k] (R : Type u) [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] : IsOpen (regularLocus R) := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  refine isOpen_regularLocus_of_exists_isOpen fun p _ => ?_
  obtain ⟨f, hf, hsub⟩ :=
    exists_ne_zero_basicOpen_subset_regularLocus_of_finiteType k (R ⧸ p.asIdeal)
  refine ⟨_, (PrimeSpectrum.basicOpen f).isOpen, ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩, hsub⟩
  simpa [PrimeSpectrum.mem_basicOpen] using hf

end Singularity.Algebra
