/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The fundamental inequality and Ostrowski's lemma for degree prime to p

This file proves two results of Volume 3, Section 3.1 of the handbook.

Theorem 3.1.2 (fundamental inequality), in the case of primes of a finite extension of rings.

* `sum_ramificationIdx_mul_inertiaDeg_le_finrank`: let `S` be a finite flat algebra over a
  domain `R`, and let `p` be a prime of `R`. For each finite set of primes of `S` over `p`, the
  sum of `e * f` is at most the rank of `S` over `R`.
* `ncard_primesOver_le_finrank`: there are at most that many primes of `S` over `p`.
* `sum_ramificationIdx_mul_inertiaDeg_le_finrank_of_isDedekindDomain` and
  `ncard_primesOver_le_finrank_of_isDedekindDomain`: the same bounds by `[L : K]`, when `R` is
  a Dedekind domain with fraction field `K` and `S` is a finite domain over `R` with fraction
  field `L`. This contains the case of a discrete valuation ring `R`.

These follow from the equality `Ideal.sum_ramification_inertia_eq_finrank` of Mathlib. The
theorem for a general valuation `v` and its extensions `w_i` to `L` is not proved here. Neither
is the passage from valuations of `L` to primes of the integral closure.

Proposition 3.1.6. Let `(K, v)` be henselian, let `L / K` be finite of degree `n`, with `n`
prime to the residue characteristic, and let `e = f = 1`. Then `L = K`.

* `valuation_eq_of_aeval_minpoly_eq_zero`: Step 1. If each `K`-endomorphism of `E` maps the
  valuation ring of `w` into itself, then conjugate elements of `E` have the same value.
* `valuation_trace_le`: Step 2. Then `w (Tr y) ≤ w y` for each `y` in a finite separable `L`.
* `isSeparable_of_finrank_cast_ne_zero`: if `[L : K]` is not zero in `K`, then `L / K` is
  separable.
* `stable_of_valuationSubring_unique`: the henselian hypothesis gives the stability of Step 1.
* `finrank_eq_one_of_henselian`: Proposition 3.1.6, with Step 3 of the proof.

In the Lean statement, `E` is an algebraic closure of `K` that contains `L`, and `w` is a
valuation of `E`. The henselian hypothesis says that the valuation ring of `w` is the only
valuation ring of `E` over the valuation ring of `v`, the restriction of `w` to `K`. This is the
handbook definition for the algebraic extension `E` of `K`, and it implies the definition for
the other algebraic extensions. The condition `n` prime to `p` is the condition `w n = 1`. The
condition `e = 1` says that each value of `L` is a value of `K`. The condition `f = 1` says that
each element of `L` of value at most 1 is congruent to an element of `K` modulo the maximal
ideal. Theorem 3.1.4 (Ostrowski) is not proved.
-/

namespace Singularity

open Module

section Fundamental

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]

/-- Theorem 3.1.2 for a finite flat extension of a domain. The sum of `e * f` over a finite
set of primes over `p` is at most the rank. -/
theorem sum_ramificationIdx_mul_inertiaDeg_le_finrank [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] (T : Finset (Ideal S)) (hT : ∀ q ∈ T, q ∈ p.primesOver S) :
    ∑ q ∈ T, q.ramificationIdx R * q.inertiaDeg R ≤ finrank R S := by
  have hfin : (p.primesOver S).Finite := Algebra.QuasiFinite.finite_primesOver p
  let _ : Fintype (p.primesOver S) := hfin.fintype
  rw [← Ideal.sum_ramification_inertia_eq_finrank p S]
  rw [← Finset.sum_subtype (p.primesOver S).toFinset (fun q => by simp)
    (fun q => q.ramificationIdx R * q.inertiaDeg R)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => by simpa using hT q hq)
    (fun _ _ _ => Nat.zero_le _)

/-- A finite flat extension of a domain has at most rank many primes over a prime `p`. -/
theorem ncard_primesOver_le_finrank [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] : (p.primesOver S).ncard ≤ finrank R S := by
  have hfin : (p.primesOver S).Finite := Algebra.QuasiFinite.finite_primesOver p
  have hpos : ∀ q ∈ hfin.toFinset, 1 ≤ q.ramificationIdx R * q.inertiaDeg R := by
    intro q hq
    have hq' : q ∈ p.primesOver S := by simpa using hq
    have : q.IsPrime := hq'.1
    have h1 := Ideal.ramificationIdx_pos R q
    have h2 := Ideal.inertiaDeg_pos q R
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero h1.ne' h2.ne')
  calc (p.primesOver S).ncard = ∑ q ∈ hfin.toFinset, 1 := by
        rw [Set.ncard_eq_toFinset_card _ hfin]; simp
    _ ≤ ∑ q ∈ hfin.toFinset, q.ramificationIdx R * q.inertiaDeg R := Finset.sum_le_sum hpos
    _ ≤ finrank R S :=
        sum_ramificationIdx_mul_inertiaDeg_le_finrank p _ (fun q hq => by simpa using hq)

end Fundamental

section FundamentalDedekind

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDomain S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]

/-- Theorem 3.1.2 over a Dedekind domain: the sum of `e * f` is at most `[L : K]`. -/
theorem sum_ramificationIdx_mul_inertiaDeg_le_finrank_of_isDedekindDomain
    (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
    [IsScalarTower R K L] (p : Ideal R) [p.IsPrime] (T : Finset (Ideal S))
    (hT : ∀ q ∈ T, q ∈ p.primesOver S) :
    ∑ q ∈ T, q.ramificationIdx R * q.inertiaDeg R ≤ finrank K L := by
  rw [IsFractionRing.finrank_eq R K S L]
  exact sum_ramificationIdx_mul_inertiaDeg_le_finrank p T hT

/-- Over a Dedekind domain, there are at most `[L : K]` primes of `S` over `p`. -/
theorem ncard_primesOver_le_finrank_of_isDedekindDomain
    (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
    [IsScalarTower R K L] (p : Ideal R) [p.IsPrime] :
    (p.primesOver S).ncard ≤ finrank K L := by
  rw [IsFractionRing.finrank_eq R K S L]
  exact ncard_primesOver_le_finrank p

end FundamentalDedekind

section Henselian

open Polynomial

variable {K L E : Type*} [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]
  [Algebra L E] [IsScalarTower K L E] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/-- An endomorphism that maps the valuation ring into itself preserves the order of values. -/
theorem valuation_map_le_map_of_stable (w : Valuation E Γ) (φ : E →ₐ[K] E)
    (hφ : ∀ x, w x ≤ 1 → w (φ x) ≤ 1) {a b : E} (hab : w a ≤ w b) :
    w (φ a) ≤ w (φ b) := by
  by_cases hb : b = 0
  · subst hb
    have ha : a = 0 := by simpa using hab
    simp [ha]
  have hwb : w b ≠ 0 := by simpa using hb
  have hφb : φ b ≠ 0 := by simpa using hb
  have hwφb : w (φ b) ≠ 0 := by simpa using hφb
  have h1 : w (a / b) ≤ 1 := by
    rw [map_div₀]; exact div_le_one_of_le₀ hab zero_le
  have h2 := hφ _ h1
  rw [map_div₀, map_div₀] at h2
  exact (div_le_one₀ (zero_lt_iff.mpr hwφb)).mp h2

/-- Step 1 of Proposition 3.1.6. Let each `K`-endomorphism of `E` map the valuation ring of
`w` into itself. Then each root `z'` of the minimal polynomial of `z` has `w z' = w z`. -/
theorem valuation_eq_of_aeval_minpoly_eq_zero [IsAlgClosed E] [Algebra.IsAlgebraic K E]
    (w : Valuation E Γ) (hstab : ∀ φ : E →ₐ[K] E, ∀ x, w x ≤ 1 → w (φ x) ≤ 1) {z z' : E}
    (hz' : aeval z' (minpoly K z) = 0) : w z' = w z := by
  classical
  have hint : IsIntegral K z := (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  set f := minpoly K z
  have hf0 : f ≠ 0 := minpoly.ne_zero hint
  set R : Finset E := (f.aroots E).toFinset
  have memR : ∀ x, x ∈ R ↔ aeval x f = 0 := by
    intro x; simp [R, hf0]
  have hzR : z ∈ R := (memR z).2 (minpoly.aeval K z)
  have hz'R : z' ∈ R := (memR z').2 hz'
  obtain ⟨m, hmR, hm⟩ := R.exists_max_image (fun x => w x) ⟨z, hzR⟩
  have hsplit : ∀ s : E, IsIntegral K s ∧ ((minpoly K s).map (algebraMap K E)).Splits :=
    fun s => ⟨(Algebra.IsAlgebraic.isAlgebraic s).isIntegral, IsAlgClosed.splits _⟩
  have hminm : minpoly K m = f :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) ((memR m).1 hmR)
      (minpoly.monic hint)).symm
  have key : ∀ y ∈ R, ∀ x ∈ R, w x ≤ w y := by
    intro y hy x hx
    obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval hsplit
      (x := m) (y := y) (by rw [hminm]; exact (memR y).1 hy)
    have himage : R.image φ = R := by
      apply Finset.eq_of_subset_of_card_le
      · intro t ht
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ht
        rw [memR] at hu ⊢
        rw [Polynomial.aeval_algHom_apply, hu, map_zero]
      · exact (Finset.card_image_of_injective R φ.toRingHom.injective).ge
    rw [← himage] at hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
    rw [← hφ]
    exact valuation_map_le_map_of_stable w φ (hstab φ) (hm u hu)
  exact le_antisymm (key z hzR z' hz'R) (key z' hz'R z hzR)

/-- Step 2 of Proposition 3.1.6: under the hypothesis of Step 1, `w (Tr y) ≤ w y`. -/
theorem valuation_trace_le [IsAlgClosed E] [Algebra.IsAlgebraic K E] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] (w : Valuation E Γ)
    (hstab : ∀ φ : E →ₐ[K] E, ∀ x, w x ≤ 1 → w (φ x) ≤ 1) (y : L) :
    w (algebraMap K E (Algebra.trace K L y)) ≤ w (algebraMap L E y) := by
  rw [trace_eq_sum_embeddings E]
  apply Valuation.map_sum_le
  intro σ _
  apply le_of_eq
  apply valuation_eq_of_aeval_minpoly_eq_zero w hstab
  rw [minpoly.algebraMap_eq (algebraMap L E).injective]
  exact minpoly.aeval_algHom K σ y

/-- If the degree `[L : K]` is not zero in `K`, then `L / K` is separable. -/
theorem isSeparable_of_finrank_cast_ne_zero [FiniteDimensional K L]
    (h : (finrank K L : K) ≠ 0) : Algebra.IsSeparable K L := by
  obtain ⟨q, hq⟩ := ExpChar.exists K
  obtain ⟨k, hk⟩ := finInsepDegree_eq_pow K L q
  rw [isSeparable_iff_finInsepDegree_eq_one, hk]
  rcases hq with _ | ⟨hp⟩
  · simp
  · rcases k with _ | k
    · simp
    exfalso
    apply h
    rw [CharP.cast_eq_zero_iff K q, ← Field.finSepDegree_mul_finInsepDegree K L, hk]
    exact Dvd.dvd.mul_left (dvd_pow_self q (Nat.succ_ne_zero k)) _

/-- If the valuation ring of `w` is the only valuation ring of `E` over the valuation ring of
the restriction of `w` to `K`, then each `K`-endomorphism of `E` maps it into itself. -/
theorem stable_of_valuationSubring_unique (w : Valuation E Γ)
    (hhens : ∀ B : ValuationSubring E,
      B.comap (algebraMap K E) = (w.comap (algebraMap K E)).valuationSubring →
        B = w.valuationSubring)
    (φ : E →ₐ[K] E) (x : E) (hx : w x ≤ 1) : w (φ x) ≤ 1 := by
  have hB := hhens (w.valuationSubring.comap φ.toRingHom) (by
    ext c
    simp [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff])
  have : x ∈ w.valuationSubring.comap φ.toRingHom := by
    rw [hB]; exact hx
  exact this

/-- Proposition 3.1.6. Let `K` be henselian, let `[L : K]` be prime to the residue
characteristic, and let `e = f = 1`. Then `[L : K] = 1`. -/
theorem finrank_eq_one_of_henselian [IsAlgClosed E] [Algebra.IsAlgebraic K E]
    [FiniteDimensional K L] (w : Valuation E Γ)
    (hhens : ∀ B : ValuationSubring E,
      B.comap (algebraMap K E) = (w.comap (algebraMap K E)).valuationSubring →
        B = w.valuationSubring)
    (hn : w (finrank K L : E) = 1)
    (he : ∀ y : L, ∃ c : K, w (algebraMap L E y) = w (algebraMap K E c))
    (hf : ∀ y : L, w (algebraMap L E y) ≤ 1 →
      ∃ c : K, w (algebraMap L E y - algebraMap K E c) < 1) :
    finrank K L = 1 := by
  have hstab := stable_of_valuationSubring_unique w hhens
  set n := finrank K L with hn_def
  have hnE : (n : E) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hn; exact zero_ne_one hn
  have hnK : (n : K) ≠ 0 := by
    intro h0; apply hnE; rw [← map_natCast (algebraMap K E), h0, map_zero]
  have := isSeparable_of_finrank_cast_ne_zero hnK
  by_contra hne
  obtain ⟨z, hz⟩ : ∃ z : L, z ∉ Set.range (algebraMap K L) := by
    by_contra! hall
    apply hne
    have hbij : Function.Bijective (Algebra.ofId K L) :=
      ⟨(algebraMap K L).injective, fun z => hall z⟩
    rw [hn_def, ← (AlgEquiv.ofBijective _ hbij).toLinearEquiv.finrank_eq, finrank_self]
  set t := Algebra.trace K L z
  set z' := z - algebraMap K L (t / n) with hz'_def
  have hz'K : z' ∉ Set.range (algebraMap K L) := by
    rintro ⟨c, hc⟩
    apply hz
    refine ⟨c + t / n, ?_⟩
    rw [map_add, hc, hz'_def, sub_add_cancel]
  have hz'0 : z' ≠ 0 := fun h0 => hz'K ⟨0, by rw [map_zero, h0]⟩
  have htr : Algebra.trace K L z' = 0 := by
    rw [hz'_def, map_sub, Algebra.trace_algebraMap, nsmul_eq_mul, ← hn_def]
    field_simp
    ring
  obtain ⟨c0, hc0⟩ := he z'
  have hwz' : w (algebraMap L E z') ≠ 0 := by simpa using hz'0
  have hc0E : algebraMap K E c0 ≠ 0 := by
    intro h0; apply hwz'; rw [hc0, h0, map_zero]
  set y := z' / algebraMap K L c0 with hy_def
  have hyE : algebraMap L E y = algebraMap L E z' / algebraMap K E c0 := by
    rw [hy_def, map_div₀, ← IsScalarTower.algebraMap_apply]
  have hwy : w (algebraMap L E y) = 1 := by
    rw [hyE, map_div₀, hc0, div_self (by simpa using hc0E)]
  obtain ⟨c1, hc1⟩ := hf y hwy.le
  have hwc1 : w (algebraMap K E c1) = 1 := by
    rw [← hwy]
    apply Valuation.map_eq_of_sub_lt
    rw [Valuation.map_sub_swap, hwy]; exact hc1
  set c := c0 * c1
  have hwc : w (algebraMap K E c) = w (algebraMap L E z') := by
    rw [map_mul, map_mul, hwc1, mul_one, hc0]
  have hdiff : algebraMap L E (z' - algebraMap K L c) =
      algebraMap K E c0 * (algebraMap L E y - algebraMap K E c1) := by
    rw [hyE, map_sub, ← IsScalarTower.algebraMap_apply, map_mul]
    field_simp
  have hlt : w (algebraMap L E (z' - algebraMap K L c)) < w (algebraMap K E c) := by
    rw [hdiff, map_mul, hwc, hc0]
    calc w (algebraMap K E c0) * w (algebraMap L E y - algebraMap K E c1)
        < w (algebraMap K E c0) * 1 :=
          mul_lt_mul_of_pos_left hc1 (zero_lt_iff.mpr (by simpa using hc0E))
      _ = w (algebraMap K E c0) := mul_one _
  have hstep2 := valuation_trace_le w hstab (z' - algebraMap K L c)
  have htr2 : Algebra.trace K L (z' - algebraMap K L c) = -(n * c) := by
    rw [map_sub, htr, Algebra.trace_algebraMap, nsmul_eq_mul, ← hn_def, zero_sub]
  rw [htr2, map_neg, Valuation.map_neg, map_mul, map_mul, map_natCast, hn, one_mul] at hstep2
  exact lt_irrefl _ (hstep2.trans_lt hlt)

end Henselian

end Singularity
