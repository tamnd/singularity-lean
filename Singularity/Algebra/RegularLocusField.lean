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

end Singularity.Algebra
