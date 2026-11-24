/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.Jacobian
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Generic regularity

Let `D` be a domain of finite type over a field `k` of characteristic `0`. This file proves that
the regular locus of `D` contains a nonempty open set `D(f)`. With the criterion of Nagata, this
gives that the regular locus of an algebra of finite type over `k` is open.

The proof has these steps.

* By Noether normalization, `D` is finite over a polynomial ring `A = k[x_1, ..., x_s]`.
* The field extension `Frac D / Frac A` is finite and separable, because `k` has characteristic
  `0`. Thus it has a primitive element, and we can take this element `z` in `D`.
* Let `F` be the minimal polynomial of `z` over `A`. Then `A[z]` is isomorphic to `A[X]/(F)`.
* A nonzero element `c` of `A` multiplies `D` into `A[z]`. Away from `c`, the rings `D` and
  `A[z]` have the same local rings.
* The Jacobian criterion for the hypersurface `A[X]/(F)` gives regularity away from `F'(z)`.
* Thus `f = c F'(z)` is a solution.

## Main results

* `Singularity.Algebra.exists_ne_zero_basicOpen_subset_regularLocus`: the result over a regular
  integrally closed base whose fraction field has characteristic `0`.
* `Singularity.Algebra.exists_ne_zero_basicOpen_subset_regularLocus_of_field`: generic regularity
  for a domain of finite type over a field of characteristic `0`.
* `Singularity.Algebra.isOpen_regularLocus_of_charZero`: the regular locus of an algebra of finite
  type over a field of characteristic `0` is open.

## References

* [Mat89] H. Matsumura, *Commutative Ring Theory*, Section 24 and Section 30.
-/

universe u v

open IsLocalRing Ideal Polynomial

namespace Singularity.Algebra

/-- The regular locus is invariant under a ring isomorphism. -/
theorem mem_regularLocus_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (p : PrimeSpectrum S) (h : (⟨p.asIdeal.comap e, inferInstance⟩ : PrimeSpectrum R) ∈
      regularLocus R) : p ∈ regularLocus S := by
  rw [mem_regularLocus] at h ⊢
  exact IsRegularLocalRing.of_ringEquiv <| IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime (p.asIdeal.comap e)) (Localization.AtPrime p.asIdeal) e
    (e.map_primeCompl_comap_eq p.asIdeal)

/-- Let `R → S` be injective and let `c ∈ R` with `c S ⊆ R`. Then for each prime `P` of `S` with
`c ∉ P`, the ring `S_P` is the localization of `R` at `P ∩ R`. -/
theorem isLocalization_atPrime_of_conductor {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S)) (P : Ideal S) [P.IsPrime] (c : R)
    (hc : algebraMap R S c ∉ P) (hcS : ∀ s : S, ∃ r : R, algebraMap R S r = algebraMap R S c * s) :
    IsLocalization.AtPrime (Localization.AtPrime P) (P.comap (algebraMap R S)) := by
  rw [IsLocalization.AtPrime, isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨r, hr⟩
    rw [IsScalarTower.algebraMap_apply R S]
    exact IsLocalization.map_units (Localization.AtPrime P) (⟨algebraMap R S r, hr⟩ : P.primeCompl)
  · intro z
    obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl z
    obtain ⟨r₁, hr₁⟩ := hcS s
    obtain ⟨r₂, hr₂⟩ := hcS t
    have ht : algebraMap R S r₂ ∉ P := by
      rw [hr₂]
      exact fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hc t.2
    refine ⟨⟨r₁, ⟨r₂, ht⟩⟩, ?_⟩
    simp only [IsScalarTower.algebraMap_apply R S (Localization.AtPrime P), hr₁, hr₂, map_mul]
    rw [mul_left_comm, IsLocalization.mk'_spec_mk]
  · intro x y hxy
    rw [IsScalarTower.algebraMap_apply R S, IsScalarTower.algebraMap_apply R S (Localization.AtPrime P) y] at hxy
    obtain ⟨u, hu⟩ := IsLocalization.exists_of_eq (M := P.primeCompl) hxy
    obtain ⟨r, hr⟩ := hcS u
    have hrP : algebraMap R S r ∉ P := by
      rw [hr]
      exact fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hc u.2
    refine ⟨⟨r, hrP⟩, hinj ?_⟩
    simp only [map_mul, hr]
    rw [mul_assoc, mul_assoc, hu]

/-- The localization of `S` at `P` is isomorphic to the localization of `R` at `P ∩ R`. -/
theorem mem_regularLocus_of_conductor {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S)) (P : PrimeSpectrum S) (c : R)
    (hc : algebraMap R S c ∉ P.asIdeal)
    (hcS : ∀ s : S, ∃ r : R, algebraMap R S r = algebraMap R S c * s)
    (h : (⟨P.asIdeal.comap (algebraMap R S), inferInstance⟩ : PrimeSpectrum R) ∈ regularLocus R) :
    P ∈ regularLocus S := by
  rw [mem_regularLocus] at h ⊢
  have := isLocalization_atPrime_of_conductor hinj P.asIdeal c hc hcS
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (P.asIdeal.comap (algebraMap R S)).primeCompl
      (Localization.AtPrime (P.asIdeal.comap (algebraMap R S)))
      (Localization.AtPrime P.asIdeal)).toRingEquiv

/-- Let `A` be a regular ring and let `F ∈ A[X]`. Then the open set `D(F')` of
`Spec A[X]/(F)` is in the regular locus. -/
theorem regularLocus_adjoinRoot {A : Type u} [CommRing A] [IsRegularRing A] (F : A[X]) :
    (PrimeSpectrum.basicOpen (AdjoinRoot.mk F (derivative F)) :
      Set (PrimeSpectrum (AdjoinRoot F))) ⊆ regularLocus (AdjoinRoot F) := by
  have := regularLocus_quotient_of_derivation (Polynomial.derivative' (R := A)) F
  rw [Polynomial.derivative'_apply] at this
  exact this

section Generic

open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra

variable {A : Type u} {B : Type u} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [FaithfulSMul A B]

/-- Let `z ∈ B` generate the fraction field of `B` over the fraction field of `A`. Then each
`d ∈ B` has a multiple `b d` with `b ∈ A`, `b ≠ 0` and `b d ∈ A[z]`. -/
theorem exists_mul_mem_adjoin (z : B) (hz : IsIntegral A z)
    (hprim : IntermediateField.adjoin (FractionRing A)
      {algebraMap B (FractionRing B) z} = ⊤) (d : B) :
    ∃ b : A, b ≠ 0 ∧ algebraMap A B b * d ∈ Algebra.adjoin A {z} := by
  have := FractionRing.isScalarTower_liftAlgebra A (FractionRing B)
  have hzK : IsIntegral (FractionRing A) (algebraMap B (FractionRing B) z) :=
    (hz.map (IsScalarTower.toAlgHom A B (FractionRing B))).tower_top
  have hd : algebraMap B (FractionRing B) d ∈
      (IntermediateField.adjoin (FractionRing A) {algebraMap B (FractionRing B) z}).toSubalgebra := by
    rw [hprim]
    trivial
  rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun x hx => by
    rw [Set.mem_singleton_iff.mp hx]; exact hzK.isAlgebraic),
    Algebra.adjoin_singleton_eq_range_aeval] at hd
  obtain ⟨p, hp⟩ := hd
  obtain ⟨b, hb, hbp⟩ := IsLocalization.integerNormalization_spec A⁰ p
  refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
  have key : aeval z (IsLocalization.integerNormalization A⁰ p) = algebraMap A B b * d := by
    apply IsFractionRing.injective B (FractionRing B)
    rw [← aeval_algebraMap_apply, ← aeval_map_algebraMap (FractionRing A), hbp,
      ← algebraMap_smul (FractionRing A) b p, map_smul]
    rw [show aeval (algebraMap B (FractionRing B) z) p = algebraMap B (FractionRing B) d from hp,
      Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply A (FractionRing A) (FractionRing B),
      ← IsScalarTower.algebraMap_apply A B (FractionRing B)]
  rw [← key]
  exact Polynomial.aeval_mem_adjoin_singleton A z

/-- The conductor of `A[z]` in `B` contains a nonzero element of `A`. -/
theorem exists_conductor [Module.Finite A B] (z : B) (hz : IsIntegral A z)
    (hprim : IntermediateField.adjoin (FractionRing A)
      {algebraMap B (FractionRing B) z} = ⊤) :
    ∃ c : A, c ≠ 0 ∧ ∀ d : B, algebraMap A B c * d ∈ Algebra.adjoin A {z} := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := B)
  choose b hb0 hbd using exists_mul_mem_adjoin z hz hprim
  refine ⟨∏ x ∈ s, b x, Finset.prod_ne_zero_iff.mpr fun x _ => hb0 x, fun d => ?_⟩
  have hdm : d ∈ Submodule.span A (s : Set B) := by
    rw [hs]
    trivial
  induction hdm using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.mul_prod_erase s b hx, map_mul, mul_comm (algebraMap A B (b x)), mul_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hbd x)
  | zero =>
    rw [mul_zero]
    exact Subalgebra.zero_mem _
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact Subalgebra.add_mem _ hx hy
  | smul a x _ hx =>
    rw [mul_smul_comm]
    exact Subalgebra.smul_mem _ hx a

/-- Generic regularity over a regular base. Let `A ⊆ B` be a finite extension of domains, where
`A` is a regular ring that is integrally closed and whose fraction field has characteristic `0`.
Then there is `f ≠ 0` in `B` such that the open set `D(f)` is in the regular locus of `B`. -/
theorem exists_ne_zero_basicOpen_subset_regularLocus [IsRegularRing A] [IsIntegrallyClosed A]
    [Module.Finite A B] [CharZero (FractionRing A)] :
    ∃ f : B, f ≠ 0 ∧ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) ⊆ regularLocus B := by
  have := FractionRing.isScalarTower_liftAlgebra A (FractionRing B)
  have hinj := FaithfulSMul.algebraMap_injective A B
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (FractionRing A) (FractionRing B)
  obtain ⟨⟨y, t⟩, rfl⟩ := IsLocalization.mk'_surjective B⁰ α
  dsimp only at hα ⊢
  have ht : (t : B) ≠ 0 := nonZeroDivisors.ne_zero t.2
  have hI := Ideal.under_ne_bot_of_algebraic_mem ht (Ideal.mem_span_singleton_self (t : B))
    (Algebra.IsIntegral.isIntegral (R := A) (t : B)).isAlgebraic
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp ha)
  set z := u * y
  have haL : algebraMap A (FractionRing A) a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr ha0
  have hzK : algebraMap B (FractionRing B) z = algebraMap (FractionRing A) (FractionRing B)
      (algebraMap A (FractionRing A) a) * IsLocalization.mk' (FractionRing B) y t := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B (FractionRing B), ← hu,
      map_mul, map_mul, mul_assoc, mul_comm (algebraMap B (FractionRing B) (t : B)),
      IsLocalization.mk'_spec]
  have hprim : IntermediateField.adjoin (FractionRing A)
      {algebraMap B (FractionRing B) z} = ⊤ := by
    rw [eq_top_iff, ← hα, IntermediateField.adjoin_simple_le_iff]
    have : IsLocalization.mk' (FractionRing B) y t =
        (algebraMap A (FractionRing A) a)⁻¹ • algebraMap B (FractionRing B) z := by
      rw [hzK, Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ haL, map_one, one_mul]
    rw [this]
    exact IntermediateField.smul_mem _ (IntermediateField.mem_adjoin_simple_self _ _)
  have hz : IsIntegral A z := Algebra.IsIntegral.isIntegral z
  obtain ⟨c, hc0, hc⟩ := exists_conductor z hz hprim
  have hmin : minpoly (FractionRing A) (algebraMap B (FractionRing B) z) =
      (minpoly A z).map (algebraMap A (FractionRing A)) :=
    minpoly.isIntegrallyClosed_eq_field_fractions (FractionRing A) (FractionRing B) hz
  have hsep : (minpoly (FractionRing A) (algebraMap B (FractionRing B) z)).Separable :=
    Algebra.IsSeparable.isSeparable (FractionRing A) _
  have hder : aeval z (derivative (minpoly A z)) ≠ 0 := by
    intro h0
    apply hsep.aeval_derivative_ne_zero (minpoly.aeval (FractionRing A) (algebraMap B (FractionRing B) z))
    rw [hmin, derivative_map, aeval_map_algebraMap, aeval_algebraMap_apply, h0, map_zero]
  let e := minpoly.equivAdjoin hz
  refine ⟨algebraMap A B c * aeval z (derivative (minpoly A z)),
    mul_ne_zero ((map_ne_zero_iff _ hinj).mpr hc0) hder, fun P hP => ?_⟩
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hP
  have hcP : algebraMap A B c ∉ P.asIdeal := fun h => hP (P.asIdeal.mul_mem_right _ h)
  have hdP : aeval z (derivative (minpoly A z)) ∉ P.asIdeal :=
    fun h => hP (P.asIdeal.mul_mem_left _ h)
  refine mem_regularLocus_of_conductor (R := Algebra.adjoin A {z}) Subtype.val_injective P
    ⟨algebraMap A B c, Subalgebra.algebraMap_mem _ c⟩ hcP (fun d => ⟨⟨_, hc d⟩, rfl⟩) ?_
  apply mem_regularLocus_of_ringEquiv e.toRingEquiv
  apply regularLocus_adjoinRoot (minpoly A z)
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
  intro h
  apply hdP
  rw [Ideal.mem_comap, Ideal.mem_comap] at h
  convert h using 1
  change _ = ((AdjoinRoot.Minpoly.toAdjoin A z (AdjoinRoot.mk _ (derivative (minpoly A z))) :
    Algebra.adjoin A {z}) : B)
  rw [← AdjoinRoot.aeval_eq, ← aeval_algHom_apply, aeval_subalgebra_coe]
  exact congrArg (fun w => aeval w (derivative (minpoly A z)))
    (AdjoinRoot.Minpoly.coe_toAdjoin_mk_X (R := A) (x := z)).symm

end Generic

/-- Generic regularity in characteristic `0`. Let `D` be a domain of finite type over a field `k`
of characteristic `0`. Then there is `f ≠ 0` in `D` such that `D(f)` is in the regular locus. -/
theorem exists_ne_zero_basicOpen_subset_regularLocus_of_field (k : Type u) [Field k] [CharZero k]
    (D : Type u) [CommRing D] [IsDomain D] [Algebra k D] [Algebra.FiniteType k D] :
    ∃ f : D, f ≠ 0 ∧ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆ regularLocus D := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k D
  let _ : Algebra (MvPolynomial (Fin s) k) D := g.toRingHom.toAlgebra
  have : Module.Finite (MvPolynomial (Fin s) k) D := hfin
  have : FaithfulSMul (MvPolynomial (Fin s) k) D :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : CharZero (FractionRing (MvPolynomial (Fin s) k)) :=
    charZero_of_injective_algebraMap
      (algebraMap k (FractionRing (MvPolynomial (Fin s) k))).injective
  exact exists_ne_zero_basicOpen_subset_regularLocus (A := MvPolynomial (Fin s) k)

/-- The regular locus of an algebra of finite type over a field of characteristic `0` is open.
This follows from generic regularity and the criterion of Nagata. -/
theorem isOpen_regularLocus_of_charZero (k : Type u) [Field k] [CharZero k] (R : Type u)
    [CommRing R] [Algebra k R] [Algebra.FiniteType k R] : IsOpen (regularLocus R) := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  refine isOpen_regularLocus_of_exists_isOpen fun p _ => ?_
  obtain ⟨f, hf, hsub⟩ := exists_ne_zero_basicOpen_subset_regularLocus_of_field k (R ⧸ p.asIdeal)
  refine ⟨_, (PrimeSpectrum.basicOpen f).isOpen, ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩, hsub⟩
  simpa [PrimeSpectrum.mem_basicOpen] using hf

end Singularity.Algebra
