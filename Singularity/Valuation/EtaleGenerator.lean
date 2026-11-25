/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.EtaleRegular
import Singularity.Valuation.MonomialGroundField
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Local uniformization along an étale generator

Let `K₀ ⊆ K` be fields that contain `k`, let `V` be a valuation subring of `K`, and let `V₀ = V ∩ K₀`. An element `z ∈ V` is an étale generator if `K = K₀(z)`, the minimal polynomial `P` of `z` over `K₀` has coefficients in `V₀`, and `P'(z)` is a unit of `V` (Volume 5, Definition 1.3.2 of the handbook). This file proves that local uniformization of `V₀` lifts to `V` along an étale generator (Volume 5, Theorem 1.3.4, node SG0000004C).

The proof follows Section 1.3 of Volume 5 of the handbook.

1. **Kronecker.** If `f = ∑ a_i X^i` has `f(β) = 0`, then each partial sum `∑_{i ≥ m} a_i β^(i - m)` is integral over the ring of coefficients (`Singularity.isIntegral_aeval_divX_iterate`).
2. **Euler** (Lemma 1.3.1). If `u` is integral over `V₀`, then `P'(z) u ∈ V₀[z]` (`Singularity.aeval_derivative_minpoly_mul_mem_adjoin`). The proof uses the trace dual of `V₀[z]`, which is `P'(z)⁻¹ V₀[z]`.
3. **Lemma 1.3.3, first part.** Let `β ∈ V`. Divide the minimal polynomial of `β` by a coefficient of largest value, and let `j` be the largest index with `v(b_j) = 1`. Then `u = ∑_{i ≥ j} b_i β^(i - j)` has `v(u) = 1`, and `u` and `u β` are integral over `V₀`. By Euler, `β = P'(z) u β / P'(z) u` is a quotient of elements of `V₀[z]` with a denominator of value 1. So `V` is the localization of `V₀[z]` at the center of `V` (`Singularity.IsEtaleGenerator.centerSubring_closure_eq`).
4. **Theorem 1.3.4.** Let `s ⊆ V` be finite. Step 3 writes each element of `s` as a quotient of polynomials in `z` with coefficients in `V₀`. Local uniformization of `V₀` gives an affine model `A₀` of `K₀/k` that contains these coefficients and the coefficients of `P`, with a regular center. The ring `A₀[X]/(P)` embeds in `K`, and its localization at the center of `V` is regular by `Singularity.isRegularLocalRing_localization_adjoinRoot`, because `P'(z)` is a unit of `V`. The model `A' = k[A₀, z, s]` has the same local ring at the center of `V`.

## Main definitions

* `Singularity.IsEtaleGenerator`: the element `z` is an étale generator of `K` over `K₀` for `V` (Definition 1.3.2).

## Main results

* `Singularity.aeval_derivative_minpoly_mul_mem_adjoin`: the lemma of Euler (Lemma 1.3.1).
* `Singularity.IsEtaleGenerator.centerSubring_closure_eq`: `V` is the localization of `V₀[z]` at the center of `V` (Lemma 1.3.3, first part).
* `Singularity.hasLocalUniformization_of_etaleGenerator`: local uniformization of `V₀` over `k` gives local uniformization of `V` over `k` (Theorem 1.3.4).
* `Singularity.isRegularLocalRing_localization_iff_of_injective`: the local ring at the center of `V` of a ring `S ⊆ V` is the subring `T_S` of `K`.

The second part of Lemma 1.3.3 is not in this file. It says that an étale generator exists if `v` is not trivial, `e = 1`, the extension of residue fields is separable and the defect is 1.
-/

open Polynomial IsLocalRing

namespace Singularity

/-! ### Integrality of the partial sums (Kronecker) -/

section Kronecker

variable {R L : Type*} [CommRing R] [CommRing L] [Algebra R L]

/-- The partial sums of a polynomial: `aeval β (divX^[m] f) = ∑_{i ≥ m} a_i β^(i - m)`. -/
theorem aeval_divX_iterate_succ (f : R[X]) (β : L) (m : ℕ) :
    aeval β (divX^[m] f) = aeval β (divX^[m + 1] f) * β + algebraMap R L (f.coeff m) := by
  have hc : (divX^[m] f).coeff 0 = f.coeff m := by
    induction m generalizing f with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply, ih, coeff_divX]
  have h := divX_mul_X_add (divX^[m] f)
  conv_lhs => rw [← h]
  rw [map_add, map_mul, aeval_X, aeval_C, hc, Function.iterate_succ_apply']

theorem aeval_eq_pow_mul_aeval_divX_iterate_add (f : R[X]) (β : L) (m : ℕ) :
    aeval β f = β ^ m * aeval β (divX^[m] f) +
      ∑ i ∈ Finset.range m, algebraMap R L (f.coeff i) * β ^ i := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [ih, aeval_divX_iterate_succ f β n, Finset.sum_range_succ]
    ring

theorem divX_iterate_eq_zero (f : R[X]) {n : ℕ} (hn : f.natDegree < n) : divX^[n] f = 0 := by
  induction n generalizing f with
  | zero => omega
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    rcases Nat.eq_zero_or_pos f.natDegree with h0 | hpos
    · rw [divX_eq_zero_iff.mpr (eq_C_of_natDegree_eq_zero h0)]
      clear ih hn h0
      induction n with
      | zero => rfl
      | succ n ihn => rw [Function.iterate_succ_apply, divX_zero, ihn]
    · exact ih _ (by rw [natDegree_divX_eq_natDegree_tsub_one]; omega)

/-- **Kronecker.** Let `f = ∑ a_i X^i` be a polynomial over `R` with `f(β) = 0`. Then each partial sum `∑_{i ≥ m} a_i β^(i - m)` is integral over `R`. -/
theorem isIntegral_aeval_divX_iterate {f : R[X]} {β : L} (hf : aeval β f = 0) (m : ℕ) :
    IsIntegral R (aeval β (divX^[m] f)) := by
  set N := f.natDegree + 1
  have hN : divX^[N] f = 0 := divX_iterate_eq_zero f (Nat.lt_succ_self _)
  rcases le_or_gt N m with hm | hm
  · rw [divX_iterate_eq_zero f (by omega), map_zero]
    exact isIntegral_zero
  suffices key : ∀ d j, j + d = N → IsIntegral R (aeval β (divX^[j] f)) from
    key (N - m) m (by omega)
  intro d
  induction d with
  | zero =>
    intro j hj
    rw [show j = N by omega, hN, map_zero]
    exact isIntegral_zero
  | succ d ihd =>
    intro j hjd
    have hj := ihd (j + 1) (by omega)
    -- From `e_{j+1}` integral to `e_j` integral.
    set e := aeval β (divX^[j + 1] f)
    rw [aeval_divX_iterate_succ f β j]
    refine IsIntegral.add ?_ isIntegral_algebraMap
    let R' := integralClosure R L
    let e' : R' := ⟨e, hj⟩
    let g : R'[X] := C e' * X ^ (j + 1) +
      ∑ i ∈ Finset.range (j + 1), C (algebraMap R R' (f.coeff i)) * X ^ i
    have hg : aeval β g = 0 := by
      have h := aeval_eq_pow_mul_aeval_divX_iterate_add f β (j + 1)
      rw [hf] at h
      have he'' : algebraMap R' L e' = e := rfl
      simp only [g, map_add, map_mul, aeval_C, map_pow, aeval_X, map_sum, he'',
        ← IsScalarTower.algebraMap_apply R R' L]
      linear_combination -h
    by_cases he : e = 0
    · have he0 : aeval β (divX^[j + 1] f) = 0 := he
      rw [he0, zero_mul]
      exact isIntegral_zero
    have hdeg : (∑ i ∈ Finset.range (j + 1), C (algebraMap R R' (f.coeff i)) * X ^ i).degree <
        (C e' * X ^ (j + 1)).degree := by
      have he' : e' ≠ 0 := fun h => he (congrArg Subtype.val h)
      rw [degree_C_mul_X_pow _ he']
      refine lt_of_le_of_lt (degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
      intro i hi
      refine lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) ?_
      exact_mod_cast Finset.mem_range.mp hi
    have hlc : g.leadingCoeff = e' := by
      simp only [g]
      rw [leadingCoeff_add_of_degree_lt' hdeg, leadingCoeff_C_mul_X_pow]
    have h1 : IsIntegral R' (g.leadingCoeff • β) := isIntegral_leadingCoeff_smul g β hg
    rw [hlc] at h1
    exact isIntegral_trans (e' • β) h1

end Kronecker

/-! ### Values of the partial sums -/

section Values

variable {K : Type*} [Field K] (V : ValuationSubring K)

/-- If the coefficients `a_i` with `i ≥ m` have value `< 1` and `β ∈ V`, then the partial sum `∑_{i ≥ m} a_i β^(i - m)` has value `< 1`. -/
theorem valuation_aeval_divX_iterate_lt_one {R : Type*} [CommRing R] [Algebra R K] (f : R[X])
    {β : K} (hβ : β ∈ V) (m : ℕ)
    (hf : ∀ i, m ≤ i → V.valuation (algebraMap R K (f.coeff i)) < 1) :
    V.valuation (aeval β (divX^[m] f)) < 1 := by
  set N := f.natDegree + 1
  rcases le_or_gt N m with hm | hm
  · rw [divX_iterate_eq_zero f (by omega), map_zero, map_zero]
    exact zero_lt_one
  suffices key : ∀ d j, j + d = N → m ≤ j → V.valuation (aeval β (divX^[j] f)) < 1 from
    key (N - m) m (by omega) le_rfl
  intro d
  induction d with
  | zero =>
    intro j hj _
    rw [divX_iterate_eq_zero f (show f.natDegree < j by omega), map_zero, map_zero]
    exact zero_lt_one
  | succ d ihd =>
    intro j hjd hmj
    rw [aeval_divX_iterate_succ f β j]
    refine Valuation.map_add_lt _ ?_ (hf j hmj)
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' ((V.valuation_le_one_iff β).mpr hβ))
      (ihd (j + 1) (by omega) (by omega))

end Values

/-! ### The lemma of Euler -/

section Euler

/-- **Euler** (Volume 5, Lemma 1.3.1 of the handbook). Let `A` be an integrally closed domain with fraction field `F`, let `L/F` be a finite separable extension, and let `x ∈ L` be integral over `A` with `L = F[x]`. Let `P` be the minimal polynomial of `x` over `F`. If `u ∈ L` is integral over `A`, then `P'(x) u ∈ A[x]`. -/
theorem aeval_derivative_minpoly_mul_mem_adjoin {A F L : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field F] [Field L] [Algebra A F] [IsFractionRing A F] [Algebra F L]
    [Algebra A L] [IsScalarTower A F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
    {x : L} (hx : Algebra.adjoin F {x} = ⊤) (hxA : IsIntegral A x) {u : L}
    (hu : IsIntegral A u) :
    aeval x (derivative (minpoly F x)) * u ∈ Algebra.adjoin A {x} := by
  have hmem : u ∈ (Algebra.traceForm F L).dualSubmodule
      (Subalgebra.toSubmodule (Algebra.adjoin A {x})) := by
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    have hyi : IsIntegral A y := adjoin_le_integralClosure hxA hy
    rw [Algebra.traceForm_apply]
    obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      (Algebra.isIntegral_trace (R := A) (L := F) (F := L) (hu.mul hyi))
    exact Submodule.mem_one.mpr ⟨c, hc⟩
  rw [traceForm_dualSubmodule_adjoin A F hx hxA] at hmem
  obtain ⟨c, hc, hcu⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hmem
  have hd : aeval x (derivative (minpoly F x)) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable F x).aeval_derivative_ne_zero (minpoly.aeval F x)
  rw [← hcu, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  exact hc

end Euler

/-! ### The local ring at the center for an injective map -/

section Center

variable {K : Type*} [Field K] {V : ValuationSubring K}

theorem centerSubring_le_toSubring {R : Subring K} (h : R ≤ V.toSubring) :
    centerSubring V R ≤ V.toSubring := by
  rintro y ⟨a, ha, c, hc, hc1, hy⟩
  have h1 : V.valuation y * V.valuation c = V.valuation a := by rw [← map_mul, hy]
  rw [hc1, mul_one] at h1
  exact (V.valuation_le_one_iff y).mp (h1 ▸ (V.valuation_le_one_iff a).mpr (h ha))

/-- Let `φ : S → K` be an injective ring map with image in `V`. Then the localization of `S` at the center `φ⁻¹(m_V)` is regular if and only if the subring `T_{φ(S)}` of `K` is regular. -/
theorem isRegularLocalRing_localization_iff_of_injective {S : Type*} [CommRing S]
    {φ : S →+* K} (hφ : Function.Injective φ) (hV : ∀ y, φ y ∈ V) :
    IsRegularLocalRing (Localization.AtPrime ((maximalIdeal V).comap (φ.codRestrict V hV))) ↔
      IsRegularLocalRing (centerSubring V φ.range) := by
  set T := centerSubring V φ.range
  set q := (maximalIdeal V).comap (φ.codRestrict V hV)
  have hmemq : ∀ a : S, a ∈ q ↔ V.valuation (φ a) < 1 := fun a =>
    V.valuation_lt_one_iff ⟨φ a, hV a⟩
  have hAT : ∀ a : S, φ a ∈ T := fun a => le_centerSubring φ.range ⟨a, rfl⟩
  let j : S →+* T := φ.codRestrict T hAT
  let _ : Algebra S T := j.toAlgebra
  have hloc : IsLocalization q.primeCompl T := by
    refine (isLocalization_iff q.primeCompl T).mpr ⟨fun a => ?_, fun w => ?_,
      fun {a b} hab => ⟨1, ?_⟩⟩
    · have ha1 : V.valuation (φ a) = 1 := by
        have h2 := a.2
        rw [Ideal.mem_primeCompl_iff, hmemq] at h2
        exact le_antisymm (V.valuation_le_one ⟨_, hV a⟩) (not_lt.mp h2)
      have ha0 : φ a ≠ 0 := fun h0 => by
        rw [h0, map_zero] at ha1
        exact zero_ne_one ha1
      have hinv : (φ a)⁻¹ ∈ T := inv_mem_centerSubring (hAT a) ha1
      refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
      change φ a * (φ a)⁻¹ = 1
      exact mul_inv_cancel₀ ha0
    · obtain ⟨b, hb, c, hc, hc1, hz⟩ := mem_centerSubring.mp w.2
      obtain ⟨b', rfl⟩ := RingHom.mem_range.mp hb
      obtain ⟨c', rfl⟩ := RingHom.mem_range.mp hc
      have hcq : c' ∈ q.primeCompl := by
        rw [Ideal.mem_primeCompl_iff, hmemq, hc1]
        exact lt_irrefl _
      exact ⟨(b', ⟨c', hcq⟩), Subtype.ext hz⟩
    · have hab' : φ a = φ b := congrArg (fun t : T => (t : K)) hab
      rw [hφ hab']
  constructor
  · intro hreg
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) T).toRingEquiv
  · intro hreg
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv q.primeCompl T (Localization.AtPrime q)).toRingEquiv

end Center

/-! ### Étale generators -/

section EtaleGenerator

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Étale generator** (Volume 5, Definition 1.3.2 of the handbook). Let `K₀` be a subfield of `K` that contains `k`, let `V` be a valuation subring of `K`, and let `V₀ = V ∩ K₀`. An element `z` of `V` is an étale generator of `K` over `K₀` for `V` if `K = K₀(z)`, the minimal polynomial `P` of `z` over `K₀` has coefficients in `V₀`, and `P'(z)` is a unit of `V`. These conditions imply that `z` is algebraic and separable over `K₀`, so `K/K₀` is finite and separable. -/
structure IsEtaleGenerator (K₀ : IntermediateField k K) (V : ValuationSubring K) (z : K) :
    Prop where
  mem : z ∈ V
  adjoin_eq_top : IntermediateField.adjoin K₀ {z} = ⊤
  coeff_mem : ∀ i, ((minpoly K₀ z).coeff i : K) ∈ V
  valuation_derivative : V.valuation (aeval z (derivative (minpoly K₀ z))) = 1

variable {K₀ : IntermediateField k K} {V : ValuationSubring K} {z : K}

namespace IsEtaleGenerator

theorem aeval_derivative_ne_zero (hz : IsEtaleGenerator K₀ V z) :
    aeval z (derivative (minpoly K₀ z)) ≠ 0 := fun h0 => by
  have h := hz.valuation_derivative
  rw [h0, map_zero] at h
  exact zero_ne_one h

theorem isIntegral (hz : IsEtaleGenerator K₀ V z) : IsIntegral K₀ z := by
  by_contra h
  apply hz.aeval_derivative_ne_zero
  rw [minpoly.eq_zero h, derivative_zero, map_zero]

theorem separable (hz : IsEtaleGenerator K₀ V z) : (minpoly K₀ z).Separable :=
  (separable_iff_derivative_ne_zero (minpoly.irreducible hz.isIntegral)).mpr fun h0 =>
    hz.aeval_derivative_ne_zero (by rw [h0, map_zero])

theorem algebra_adjoin_eq_top (hz : IsEtaleGenerator K₀ V z) : Algebra.adjoin K₀ {z} = ⊤ := by
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hz.isIntegral.isAlgebraic,
    hz.adjoin_eq_top, IntermediateField.top_toSubalgebra]

theorem finiteDimensional (hz : IsEtaleGenerator K₀ V z) : FiniteDimensional K₀ K := by
  refine ⟨?_⟩
  rw [← Algebra.top_toSubmodule, ← hz.algebra_adjoin_eq_top]
  exact hz.isIntegral.fg_adjoin_singleton

theorem isSeparable (hz : IsEtaleGenerator K₀ V z) : Algebra.IsSeparable K₀ K := by
  have h := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K₀ K).mpr hz.separable
  rw [hz.adjoin_eq_top] at h
  exact Algebra.IsSeparable.of_algHom K₀ _
    (IntermediateField.topEquiv (F := K₀) (E := K)).symm.toAlgHom

/-- The main step of Volume 5, Lemma 1.3.3 of the handbook. Let `z` be an étale generator and let `x ∈ V`. Then `x = a / c` with `a, c ∈ V₀[z]` and `v(c) = 1`. The elements `a` and `c` are given as polynomials in `z` with coefficients in `V₀ = V ∩ K₀`. -/
theorem exists_mul_eq (hz : IsEtaleGenerator K₀ V z) {x : K} (hx : x ∈ V) :
    ∃ p q : K₀[X], (∀ i, (p.coeff i : K) ∈ V) ∧ (∀ i, (q.coeff i : K) ∈ V) ∧
      V.valuation (aeval z q) = 1 ∧ x * aeval z q = aeval z p := by
  classical
  set V₀ := V.comap (algebraMap K₀ K) with hV₀
  let _ : Algebra V₀ K := ((algebraMap K₀ K).comp (algebraMap V₀ K₀)).toAlgebra
  have : IsScalarTower V₀ K₀ K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional K₀ K := hz.finiteDimensional
  have : Algebra.IsSeparable K₀ K := hz.isSeparable
  have hV0 : ∀ c : K₀, c ∈ V₀ ↔ (c : K) ∈ V := fun c => Iff.rfl
  -- `z` is integral over `V₀`.
  have hzi : IsIntegral V₀ z := by
    have hlifts : minpoly K₀ z ∈ lifts (algebraMap V₀ K₀) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, (hV0 _).mpr (hz.coeff_mem n)⟩, rfl⟩
    obtain ⟨P, hP, -, hPm⟩ := lifts_and_natDegree_eq_and_monic hlifts (minpoly.monic hz.isIntegral)
    exact ⟨P, hPm, by rw [← aeval_def, ← aeval_map_algebraMap K₀, hP, minpoly.aeval]⟩
  -- The elements of `V₀[z]` are polynomials in `z` with coefficients in `V₀`.
  have hadj : ∀ w ∈ Algebra.adjoin V₀ {z},
      ∃ p : K₀[X], (∀ i, (p.coeff i : K) ∈ V) ∧ aeval z p = w := by
    intro w hw
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hw
    obtain ⟨p, rfl⟩ := hw
    refine ⟨p.map (algebraMap V₀ K₀), fun i => ?_, aeval_map_algebraMap K₀ z p⟩
    rw [coeff_map]
    exact (p.coeff i).2
  -- The minimal polynomial `f` of `x`, divided by a coefficient of largest value.
  have hxi : IsIntegral K₀ x := Algebra.IsIntegral.isIntegral x
  set f := minpoly K₀ x with hf
  have hf0 : f ≠ 0 := minpoly.ne_zero hxi
  obtain ⟨t, ht, htmax⟩ := Finset.exists_max_image f.support
    (fun i => V.valuation (f.coeff i : K)) (support_nonempty.mpr hf0)
  set a := f.coeff t
  have ha0 : a ≠ 0 := mem_support_iff.mp ht
  have ha0' : (a : K) ≠ 0 := fun h0 => ha0 (Subtype.ext h0)
  have hva : ∀ i, V.valuation (f.coeff i : K) ≤ V.valuation (a : K) := by
    intro i
    by_cases hi : i ∈ f.support
    · exact htmax i hi
    · rw [notMem_support_iff.mp hi]
      simp
  set g := C a⁻¹ * f with hg
  have hgc : ∀ i, (g.coeff i : K) = (a : K)⁻¹ * f.coeff i := by
    intro i
    rw [hg, coeff_C_mul]
    push_cast
    rfl
  have hvg : ∀ i, V.valuation (g.coeff i : K) ≤ 1 := by
    intro i
    rw [hgc, map_mul]
    calc V.valuation (a : K)⁻¹ * V.valuation (f.coeff i : K)
        ≤ V.valuation (a : K)⁻¹ * V.valuation (a : K) := by gcongr; exact hva i
      _ = 1 := by rw [← map_mul, inv_mul_cancel₀ ha0', map_one]
  have hgt : V.valuation (g.coeff t : K) = 1 := by
    rw [hgc, inv_mul_cancel₀ ha0', map_one]
  -- The largest index `j` with `v(b_j) = 1`.
  set J := g.support.filter (fun i => V.valuation (g.coeff i : K) = 1) with hJ
  have htJ : t ∈ J := by
    refine Finset.mem_filter.mpr ⟨mem_support_iff.mpr fun h0 => ?_, hgt⟩
    rw [h0] at hgt
    simp at hgt
  set j := J.max' ⟨t, htJ⟩
  have hj1 : V.valuation (g.coeff j : K) = 1 := (Finset.mem_filter.mp (J.max'_mem _)).2
  have hjgt : ∀ i, j < i → V.valuation (g.coeff i : K) < 1 := by
    intro i hi
    refine lt_of_le_of_ne (hvg i) fun h1 => ?_
    have hiJ : i ∈ J := by
      refine Finset.mem_filter.mpr ⟨mem_support_iff.mpr fun h0 => ?_, h1⟩
      rw [h0] at h1
      simp at h1
    exact absurd (J.le_max' i hiJ) (not_le.mpr hi)
  -- The polynomial `g` over `V₀`.
  obtain ⟨G, hG⟩ := (mem_lifts g).mp ((lifts_iff_coeff_lifts (f := algebraMap V₀ K₀) g).mpr fun n =>
    ⟨⟨_, (hV0 _).mpr ((V.valuation_le_one_iff _).mp (hvg n))⟩, rfl⟩)
  have hGc : ∀ i, algebraMap V₀ K (G.coeff i) = (g.coeff i : K) := by
    intro i
    rw [← hG, coeff_map]
    rfl
  have hGx : aeval x G = 0 := by
    rw [← aeval_map_algebraMap K₀, hG, hg, map_mul, hf, minpoly.aeval, mul_zero]
  -- The value of `u = e_j` is `1`.
  have hej : V.valuation (aeval x (divX^[j] G)) = 1 := by
    have hsmall : V.valuation (aeval x (divX^[j + 1] G) * x) <
        V.valuation (algebraMap V₀ K (G.coeff j)) := by
      rw [hGc, hj1, map_mul]
      refine lt_of_le_of_lt (mul_le_of_le_one_right' ((V.valuation_le_one_iff x).mpr hx)) ?_
      exact valuation_aeval_divX_iterate_lt_one V G hx (j + 1) fun i hi => by
        rw [hGc]
        exact hjgt i (by omega)
    rw [aeval_divX_iterate_succ G x j, Valuation.map_add_eq_of_lt_right _ hsmall, hGc, hj1]
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, Function.iterate_zero_apply, hGx, map_zero] at hej
    exact zero_ne_one hej
  set u := aeval x (divX^[j] G)
  have hu : IsIntegral V₀ u := isIntegral_aeval_divX_iterate hGx j
  have hux : IsIntegral V₀ (u * x) := by
    have h1 := aeval_divX_iterate_succ G x (j - 1)
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0)] at h1
    have h2 : u * x = aeval x (divX^[j - 1] G) - algebraMap V₀ K (G.coeff (j - 1)) := by
      rw [h1]
      ring
    rw [h2]
    exact (isIntegral_aeval_divX_iterate hGx (j - 1)).sub isIntegral_algebraMap
  obtain ⟨q, hq, hqe⟩ := hadj _
    (aeval_derivative_minpoly_mul_mem_adjoin hz.algebra_adjoin_eq_top hzi hu)
  obtain ⟨p, hp, hpe⟩ := hadj _
    (aeval_derivative_minpoly_mul_mem_adjoin hz.algebra_adjoin_eq_top hzi hux)
  refine ⟨p, q, hp, hq, ?_, ?_⟩
  · rw [hqe, map_mul, hz.valuation_derivative, hej, one_mul]
  · rw [hqe, hpe]
    ring

/-- **Volume 5, Lemma 1.3.3 (first part)** of the handbook. Let `z` be an étale generator and let `V₀ = V ∩ K₀`. Then `V` is the localization of `V₀[z]` at the center of `V`: every element of `V` is `a / c` with `a, c ∈ V₀[z]` and `v(c) = 1`. Here `V₀[z]` is the subring of `K` generated by `z` and `K₀ ∩ V`. -/
theorem centerSubring_closure_eq (hz : IsEtaleGenerator K₀ V z) :
    centerSubring V (Subring.closure (insert z ((K₀ : Set K) ∩ V))) = V.toSubring := by
  set R := Subring.closure (insert z ((K₀ : Set K) ∩ V))
  have hRV : R ≤ V.toSubring :=
    Subring.closure_le.mpr (Set.insert_subset hz.mem Set.inter_subset_right)
  have hpR : ∀ p : K₀[X], (∀ i, (p.coeff i : K) ∈ V) → aeval z p ∈ R := by
    intro p hp
    rw [aeval_eq_sum_range]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Subring.mul_mem _
      (Subring.subset_closure (Set.mem_insert_of_mem _ ⟨(p.coeff i).2, hp i⟩))
      (Subring.pow_mem _ (Subring.subset_closure (Set.mem_insert _ _)) _)
  refine le_antisymm (centerSubring_le_toSubring hRV) fun x hx => ?_
  obtain ⟨p, q, hp, hq, hv, he⟩ := hz.exists_mul_eq hx
  exact ⟨_, hpR p hp, _, hpR q hq, hv, he⟩

end IsEtaleGenerator

/-- **Lifting along an étale generator** (Volume 5, Theorem 1.3.4 of the handbook). Let `K₀` be a subfield of `K` that contains `k`, let `V` be a valuation subring of `K`, and let `z` be an étale generator of `K` over `K₀` for `V`. If `V₀ = V ∩ K₀` has local uniformization as a valuation of `K₀/k`, then `V` has local uniformization as a valuation of `K/k`. -/
theorem hasLocalUniformization_of_etaleGenerator {K₀ : IntermediateField k K}
    {V : ValuationSubring K} {z : K} (hz : IsEtaleGenerator K₀ V z)
    (h : HasLocalUniformization k (V.comap (algebraMap K₀ K))) : HasLocalUniformization k V := by
  classical
  intro s hs
  set V₀ := V.comap (algebraMap K₀ K) with hV₀
  have hV0 : ∀ c : K₀, c ∈ V₀ ↔ (c : K) ∈ V := fun c => Iff.rfl
  -- Step 1. Each `x ∈ s` is `a / c` with `a, c ∈ V₀[z]` and `v(c) = 1`.
  have hxs : ∀ x : s, ∃ p q : K₀[X], (∀ i, (p.coeff i : K) ∈ V) ∧ (∀ i, (q.coeff i : K) ∈ V) ∧
      V.valuation (aeval z q) = 1 ∧ (x : K) * aeval z q = aeval z p :=
    fun x => hz.exists_mul_eq (hs x x.2)
  choose p q hp hq hqv hpq using hxs
  set T : Finset K₀ := (minpoly K₀ z).coeffs ∪
    Finset.univ.biUnion (fun x : s => (p x).coeffs ∪ (q x).coeffs) with hT
  have hcoeffs : ∀ r : K₀[X], (∀ i, (r.coeff i : K) ∈ V) → ∀ c ∈ r.coeffs, c ∈ V₀ := by
    intro r hr c hc
    obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.mp hc
    exact (hV0 _).mpr (hr n)
  have hTV : ∀ c ∈ T, c ∈ V₀ := by
    intro c hc
    rw [hT, Finset.mem_union, Finset.mem_biUnion] at hc
    rcases hc with hc | ⟨x, -, hc⟩
    · exact hcoeffs _ hz.coeff_mem c hc
    · rcases Finset.mem_union.mp hc with hc | hc
      · exact hcoeffs _ (hp x) c hc
      · exact hcoeffs _ (hq x) c hc
  -- Step 2. A regular center of `V₀` on an affine model `A0` of `K₀/k` that contains `T`.
  obtain ⟨A0, h0, ⟨⟨G0, hG0⟩, hfrac0⟩, hTA0, hreg0⟩ := h T hTV
  have : Algebra.FiniteType k A0 := (Subalgebra.fg_iff_finiteType A0).mp ⟨G0, hG0⟩
  have : IsNoetherianRing A0 := Algebra.FiniteType.isNoetherianRing k A0
  have hcoeffA0 : ∀ r : K₀[X], r.coeffs ⊆ T → ∀ n, r.coeff n ∈ A0 := by
    intro r hr n
    by_cases hn : r.coeff n = 0
    · rw [hn]
      exact A0.zero_mem
    · exact hTA0 (Finset.mem_coe.mpr (hr (coeff_mem_coeffs hn)))
  have hlift : ∀ r : K₀[X], (∀ n, r.coeff n ∈ A0) →
      ∃ r' : A0[X], r'.map (algebraMap A0 K₀) = r :=
    fun r hr => (mem_lifts r).mp ((lifts_iff_coeff_lifts (f := algebraMap A0 K₀) r).mpr fun n => ⟨⟨_, hr n⟩, rfl⟩)
  -- Step 3. The minimal polynomial of `z` over `A0`, and the map `A0[X]/(P) → K`.
  obtain ⟨P, hPmap, -, hPmon⟩ := lifts_and_natDegree_eq_and_monic
    ((lifts_iff_coeff_lifts (f := algebraMap A0 K₀) _).mpr fun n =>
      ⟨⟨_, hcoeffA0 _ Finset.subset_union_left n⟩, rfl⟩) (minpoly.monic hz.isIntegral)
  let ι : A0 →+* K := (algebraMap K₀ K).comp (algebraMap A0 K₀)
  have hev : ∀ r' : A0[X], r'.eval₂ ι z = aeval z (r'.map (algebraMap A0 K₀)) := by
    intro r'
    rw [aeval_def, eval₂_map]
  have hPz : P.eval₂ ι z = 0 := by rw [hev, hPmap, minpoly.aeval]
  let φ : AdjoinRoot P →+* K := AdjoinRoot.lift ι z hPz
  have hφmk : ∀ r' : A0[X], φ (AdjoinRoot.mk P r') = r'.eval₂ ι z := fun r' =>
    AdjoinRoot.lift_mk hPz r'
  have hinj0 : Function.Injective (algebraMap A0 K₀) := Subtype.val_injective
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨r', rfl⟩ := AdjoinRoot.mk_surjective y
    rw [hφmk] at hy
    rw [AdjoinRoot.mk_eq_zero, ← modByMonic_eq_zero_iff_dvd hPmon]
    have hr0 : (r' %ₘ P).eval₂ ι z = 0 := by
      have h1 := modByMonic_add_div r' P
      rw [← h1, eval₂_add, eval₂_mul, hPz, zero_mul, add_zero] at hy
      exact hy
    have hrdeg : (r' %ₘ P).degree < P.degree := degree_modByMonic_lt r' hPmon
    by_contra hne
    have hmne : (r' %ₘ P).map (algebraMap A0 K₀) ≠ 0 := by
      rwa [Ne, Polynomial.map_eq_zero_iff hinj0]
    have h2 := minpoly.degree_le_of_ne_zero K₀ z hmne (by rw [← hev]; exact hr0)
    rw [← hPmap, degree_map_eq_of_injective hinj0, degree_map_eq_of_injective hinj0] at h2
    exact absurd hrdeg (not_lt.mpr h2)
  have hevmem : ∀ R : Subring K, (∀ a, ι a ∈ R) → z ∈ R → ∀ r' : A0[X], r'.eval₂ ι z ∈ R := by
    intro R hR hzR r'
    rw [eval₂_eq_sum_range]
    exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hR _) (Subring.pow_mem _ hzR _)
  have hφV : ∀ y, φ y ∈ V := by
    intro y
    obtain ⟨r', rfl⟩ := AdjoinRoot.mk_surjective y
    rw [hφmk]
    exact hevmem V.toSubring (fun a => h0 a) hz.mem r'
  -- Step 4. The center `Q` of `V` on `A0[X]/(P)`. It lies over the center of `V₀` on `A0`, and `P'(z) ∉ Q`.
  set Q : Ideal (AdjoinRoot P) := (maximalIdeal V).comap (φ.codRestrict V hφV) with hQ
  have hmemQ : ∀ y, y ∈ Q ↔ V.valuation (φ y) < 1 := fun y =>
    V.valuation_lt_one_iff ⟨φ y, hφV y⟩
  have hQd : AdjoinRoot.mk P (derivative P) ∉ Q := by
    rw [hmemQ, hφmk, hev, ← derivative_map, hPmap, hz.valuation_derivative]
    exact lt_irrefl _
  have hlt : ∀ c : K₀, V₀.valuation c < 1 ↔ V.valuation (c : K) < 1 := by
    intro c
    have h1 : ((c⁻¹ : K₀) : K) = (c : K)⁻¹ := map_inv₀ (algebraMap K₀ K) c
    have h2 : (c : K) = 0 ↔ c = 0 := ⟨fun h => Subtype.ext h, fun h => by simp [h]⟩
    rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
      ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, hV0, h1, h2]
  have hcomap : Q.comap (algebraMap A0 (AdjoinRoot P)) = valuationCenter V₀ A0 h0 := by
    ext a
    have e1 : a ∈ valuationCenter V₀ A0 h0 ↔ V₀.valuation (a : K₀) < 1 :=
      V₀.valuation_lt_one_iff ⟨_, h0 a⟩
    rw [Ideal.mem_comap, hmemQ, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of, e1, hlt]
    rfl
  -- Step 5. The local ring of `A0[X]/(P)` at `Q` is regular.
  have hregS : IsRegularLocalRing (Localization.AtPrime Q) :=
    isRegularLocalRing_localization_adjoinRoot hPmon Q hQd _ hcomap hreg0
  have hregT : IsRegularLocalRing (centerSubring V φ.range) :=
    (isRegularLocalRing_localization_iff_of_injective hφinj hφV).mp hregS
  -- Step 6. The affine model `A'` of `K/k`.
  set gens : Finset K := G0.image (fun c : K₀ => (c : K)) ∪ {z} ∪ s with hgens
  set A' : Subalgebra k K := Algebra.adjoin k (gens : Set K) with hA'
  have hmem' : ∀ w ∈ gens, w ∈ A' := fun w hw => Algebra.subset_adjoin hw
  have hιA' : ∀ a : A0, ι a ∈ A' := by
    intro a
    have ha : (a : K₀) ∈ Algebra.adjoin k (G0 : Set K₀) := by
      rw [hG0]
      exact a.2
    have hle : (Algebra.adjoin k (G0 : Set K₀)).map (IntermediateField.val K₀) ≤ A' := by
      rw [AlgHom.map_adjoin]
      refine Algebra.adjoin_le fun w hw => ?_
      obtain ⟨c, hc, rfl⟩ := hw
      exact hmem' _
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc)))
    exact hle (Subalgebra.mem_map.mpr ⟨_, ha, rfl⟩)
  have hzA' : z ∈ A' := hmem' z (by simp [hgens])
  have hrangeA' : φ.range ≤ A'.toSubring := by
    rintro y ⟨y', rfl⟩
    obtain ⟨r', rfl⟩ := AdjoinRoot.mk_surjective y'
    rw [hφmk]
    exact hevmem A'.toSubring hιA' hzA' r'
  have hrange : ∀ r : K₀[X], r.coeffs ⊆ T → aeval z r ∈ φ.range := by
    intro r hr
    obtain ⟨r', hr'⟩ := hlift r (hcoeffA0 r hr)
    exact ⟨AdjoinRoot.mk P r', by rw [hφmk, hev, hr']⟩
  have hA'T : A'.toSubring ≤ centerSubring V φ.range := by
    let TF : Subalgebra k K :=
      { centerSubring V φ.range with
        algebraMap_mem' := fun c => le_centerSubring _
          ⟨AdjoinRoot.of P (algebraMap k A0 c), by rw [AdjoinRoot.lift_of]; rfl⟩ }
    have hle : A' ≤ TF := by
      refine Algebra.adjoin_le fun w hw => ?_
      simp only [hgens, Finset.coe_union, Finset.coe_image, Finset.coe_singleton,
        Set.mem_union, Set.mem_image, Set.mem_singleton_iff, Finset.mem_coe] at hw
      rcases hw with (⟨c, hc, rfl⟩ | rfl) | hw
      · have hcA0 : c ∈ A0 := by
          rw [← hG0]
          exact Algebra.subset_adjoin hc
        exact le_centerSubring _ ⟨AdjoinRoot.of P ⟨c, hcA0⟩, by rw [AdjoinRoot.lift_of]; rfl⟩
      · exact le_centerSubring _ ⟨AdjoinRoot.root P, AdjoinRoot.lift_root hPz⟩
      · refine ⟨aeval z (p ⟨w, hw⟩), hrange _ fun c hc => ?_, aeval z (q ⟨w, hw⟩),
          hrange _ fun c hc => ?_, hqv ⟨w, hw⟩, hpq ⟨w, hw⟩⟩
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨⟨w, hw⟩, Finset.mem_univ _, Finset.mem_union_left _ hc⟩)
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨⟨w, hw⟩, Finset.mem_univ _, Finset.mem_union_right _ hc⟩)
    exact fun y hy => hle hy
  have hTeq : centerSubring V φ.range = centerSubring V A'.toSubring :=
    le_antisymm (centerSubring_mono hrangeA') (centerSubring_le hA'T)
  have hrangeV : φ.range ≤ V.toSubring := by
    rintro y ⟨y', rfl⟩
    exact hφV y'
  have hA'V : ∀ a : A', (a : K) ∈ V := fun a =>
    centerSubring_le_toSubring hrangeV (hA'T a.2)
  refine ⟨A', hA'V, ⟨⟨gens, rfl⟩, ?_⟩, fun w hw => hmem' w (Finset.mem_union_right _ hw), ?_⟩
  · -- `K` is the fraction field of `A'`.
    refine IsFractionRing.of_field A' K fun y => ?_
    have hy : y ∈ Algebra.adjoin K₀ {z} := by
      rw [hz.algebra_adjoin_eq_top]
      trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨r, rfl⟩ := hy
    obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A0) r
    set r' := IsLocalization.integerNormalization (nonZeroDivisors A0) r
    have hb0 : ι b ≠ 0 := fun h0 =>
      nonZeroDivisors.ne_zero hbM (Subtype.ext (Subtype.ext h0))
    have key : r'.eval₂ ι z = ι b * aeval z r := by
      rw [hev, hb, ← algebraMap_smul K₀ b r, map_smul, Algebra.smul_def]
      rfl
    refine ⟨⟨r'.eval₂ ι z, hevmem A'.toSubring hιA' hzA' r'⟩, ⟨ι b, hιA' b⟩, ?_⟩
    change aeval z r = r'.eval₂ ι z / ι b
    rw [key, mul_div_cancel_left₀ _ hb0]
  · -- The local ring of `A'` at the center of `V` is regular.
    exact (isRegularLocalRing_localization_iff A' hA'V).mpr
      (IsRegularLocalRing.of_ringEquiv (RingEquiv.subringCongr hTeq))

end EtaleGenerator

end Singularity
