/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.Regular
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# A regular local ring is integrally closed

This file proves that a regular local ring `R` is integrally closed. This is the statement of Volume 1, Section 1.3 of the handbook. The handbook cites it from the theorem of Auslander-Buchsbaum, which says that a regular local ring is a unique factorization domain. The proof here is elementary. It uses only three facts: a regular local ring is a domain, the quotient by an element `x ∈ 𝔪 \ 𝔪²` is regular of dimension one less, and the intersection theorem of Krull.

The proof gives a stronger divisibility property (D) of `R`: if `b ≠ 0`, `c ≠ 0` and `b ^ n ∣ c * a ^ n` for all `n`, then `b ∣ a`. Property (D) says that `R` is completely integrally closed. In Mathlib terms, each almost integral element (`IsAlmostIntegral`) of the fraction field is in `R`.

## Main results

* `IsDvdClosed`: property (D) of a commutative ring.
* `IsDvdClosed.mem_range_of_isAlmostIntegral` and `IsDvdClosed.isIntegrallyClosed`: a domain with property (D) is completely integrally closed, so it is integrally closed.
* `dvd_of_dvd_prime_pow_mul`: if `x` is prime, `¬ x ∣ d` and `d ∣ x ^ e * y`, then `d ∣ y`.
* `exists_eq_pow_mul_forall_pow_dvd`: the reduction step that removes the powers of a prime `x` from `b` and `c` in property (D).
* `isDvdClosed_of_isDvdClosed_quotient`: if `R` is a Noetherian local domain, `x ∈ 𝔪` is prime and `R / (x)` has property (D), then `R` has property (D).
* `dvd_of_forall_pow_dvd_mul_pow`: a regular local ring has property (D).
* `isIntegrallyClosed_of_isRegularLocalRing`: a regular local ring is integrally closed.
* `mem_range_algebraMap_of_pow_mem`: if `g` is in the fraction field of a regular local ring `R` and `g ^ n ∈ R` for some `n ≥ 1`, then `g ∈ R`.

## The proof

The proof is by induction on the dimension `d` of `R`. If `d = 0`, then `R` is a field and each `b ≠ 0` is a unit. If `d = m + 1`, choose `x ∈ 𝔪 \ 𝔪²`. Then `R / (x)` is regular of dimension `m`, so it is a domain and `x` is a prime element. By induction, `R / (x)` has property (D). It remains to lift property (D) from `R / (x)` to `R`.

Let `b ^ n ∣ c * a ^ n` for all `n`. First remove the powers of `x` from `b` and from `c`. A count of the powers of `x` shows that the power of `x` in `b` is at most the power of `x` in `a`. Thus we can assume that `x` does not divide `b` or `c`. Then we show by induction on `N` that `a = b * r + x ^ N * t` with `b ^ n ∣ c * t ^ n` for all `n`. For the step, property (D) of `R / (x)` gives `t = b * r' + x * t'`. The binomial formula and the cancellation of the prime `x` give `b ^ n ∣ c * t' ^ n`. Thus the class of `a` in `R / (b)` is in `x ^ N (R / (b))` for all `N`. The intersection theorem of Krull says that this class is zero, so `b ∣ a`.

## References

* [Mat89] H. Matsumura, *Commutative ring theory*, 1989. Theorem 19.4 and Theorem 20.3 give the classical route through the theorem of Auslander-Buchsbaum: a regular local ring is a unique factorization domain, and a unique factorization domain is integrally closed.
-/

open IsLocalRing Ideal
open scoped nonZeroDivisors

universe u

namespace Singularity.Algebra

variable {R : Type u} [CommRing R]

/-! ### 1. Property (D) -/

/-- **Property (D)**. A ring `R` has property (D) when for all `a b c : R` with `b ≠ 0` and `c ≠ 0`, if `b ^ n ∣ c * a ^ n` for all `n`, then `b ∣ a`. For a domain this says that `R` is completely integrally closed: if the powers of `a / b` have the common denominator `c`, then `a / b ∈ R`. -/
def IsDvdClosed (R : Type u) [CommRing R] : Prop :=
  ∀ a b c : R, b ≠ 0 → c ≠ 0 → (∀ n : ℕ, b ^ n ∣ c * a ^ n) → b ∣ a

/-- **Property (D) gives complete integral closure.** Let `R` be a domain with property (D) and let `K` be its fraction field. Then each almost integral element of `K` is in `R`. -/
theorem IsDvdClosed.mem_range_of_isAlmostIntegral [IsDomain R] (hD : IsDvdClosed R)
    {K : Type*} [CommRing K] [Algebra R K] [IsFractionRing R K] {g : K}
    (hg : IsAlmostIntegral R g) : g ∈ (algebraMap R K).range := by
  obtain ⟨r, hr, hrg⟩ := hg
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective R⁰ g
  have key : ∀ n : ℕ, (b : R) ^ n ∣ r * a ^ n := by
    intro n
    obtain ⟨s, hs⟩ := hrg n
    have h1 := congrArg (· ^ n) (IsLocalization.mk'_spec K a b)
    simp only [mul_pow] at h1
    refine ⟨s, IsFractionRing.injective R K ?_⟩
    rw [map_mul, map_mul, map_pow, map_pow, hs, Algebra.smul_def, ← h1]
    ring
  obtain ⟨q, hq⟩ := hD a b r (nonZeroDivisors.ne_zero b.2) (nonZeroDivisors.ne_zero hr) key
  refine ⟨q, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, hq, map_mul, mul_comm]

/-- **Property (D) gives integral closure.** A domain with property (D) is integrally closed. -/
theorem IsDvdClosed.isIntegrallyClosed [IsDomain R] (hD : IsDvdClosed R) :
    IsIntegrallyClosed R :=
  (isIntegrallyClosed_iff (FractionRing R)).mpr fun hx =>
    RingHom.mem_range.mp (hD.mem_range_of_isAlmostIntegral hx.isAlmostIntegral)

/-! ### 2. Cancellation of a prime and the reduction step -/

/-- **Cancellation of a prime.** Let `x` be a prime element of a domain and let `¬ x ∣ d`. If `d ∣ x ^ e * y`, then `d ∣ y`. -/
theorem dvd_of_dvd_prime_pow_mul [IsDomain R] {x d y : R} (hx : Prime x) (hd : ¬ x ∣ d)
    (e : ℕ) (h : d ∣ x ^ e * y) : d ∣ y := by
  induction e with
  | zero => simpa using h
  | succ e ih =>
    obtain ⟨t, ht⟩ := h
    have hxt : x ∣ d * t := ⟨x ^ e * y, by rw [← ht]; ring⟩
    obtain ⟨t', rfl⟩ := (hx.dvd_or_dvd hxt).resolve_left hd
    refine ih ⟨t', mul_left_cancel₀ hx.ne_zero ?_⟩
    linear_combination ht

/-- **The reduction step.** Let `R` be a Noetherian domain and let `x` be a prime element. Let `b = x ^ e * b'` and `c = x ^ f * c'` with `¬ x ∣ b'` and `¬ x ∣ c'`, and let `b ^ n ∣ c * a ^ n` for all `n`. Then `a = x ^ e * a'` for some `a'` with `b' ^ n ∣ c' * a' ^ n` for all `n`. -/
theorem exists_eq_pow_mul_forall_pow_dvd [IsDomain R] [IsNoetherianRing R] {x : R}
    (hx : Prime x) {a b c b' c' : R} {e f : ℕ} (hb : b = x ^ e * b') (hc : c = x ^ f * c')
    (hb' : ¬ x ∣ b') (hc' : ¬ x ∣ c') (h : ∀ n : ℕ, b ^ n ∣ c * a ^ n) :
    ∃ a' : R, a = x ^ e * a' ∧ ∀ n : ℕ, b' ^ n ∣ c' * a' ^ n := by
  subst hb hc
  by_cases ha : a = 0
  · refine ⟨0, by simp [ha], fun n => ?_⟩
    rcases n with _ | n
    · simp
    · simp
  obtain ⟨g, a'', ha'', rfl⟩ := WfDvdMonoid.max_power_factor ha hx.irreducible
  have heg : e ≤ g := by
    by_contra hlt
    push Not at hlt
    have h2 : x ^ (f + g * (f + 1)) * x ∣ x ^ (f + g * (f + 1)) * (c' * a'' ^ (f + 1)) := by
      have h3 : x ^ (f + g * (f + 1) + 1) ∣ (x ^ e * b') ^ (f + 1) := by
        rw [mul_pow, ← pow_mul]
        exact (pow_dvd_pow x (by nlinarith)).mul_right _
      rw [← pow_succ]
      exact h3.trans ((h (f + 1)).trans (dvd_of_eq (by ring)))
    rw [mul_dvd_mul_iff_left (pow_ne_zero _ hx.ne_zero)] at h2
    exact (hx.dvd_or_dvd h2).elim hc' fun h3 => ha'' (hx.dvd_of_dvd_pow h3)
  have hg : x ^ g = x ^ e * x ^ (g - e) := by rw [← pow_add, Nat.add_sub_cancel' heg]
  refine ⟨x ^ (g - e) * a'', by rw [hg, mul_assoc], fun n => ?_⟩
  refine dvd_of_dvd_prime_pow_mul hx (fun h' => hb' (hx.dvd_of_dvd_pow h')) f ?_
  have h2 := h n
  rw [hg] at h2
  have h3 : (x ^ e) ^ n * b' ^ n ∣ (x ^ e) ^ n * (x ^ f * (c' * (x ^ (g - e) * a'') ^ n)) :=
    (dvd_of_eq (by ring)).trans (h2.trans (dvd_of_eq (by ring)))
  exact (mul_dvd_mul_iff_left (pow_ne_zero _ (pow_ne_zero _ hx.ne_zero))).mp h3

/-- If `b ^ i ∣ c * u ^ i` for all `i`, then `b ^ n ∣ c * (u - b * r) ^ n` for all `n`. The proof uses the binomial formula. -/
theorem pow_dvd_mul_sub_mul_pow {b c u : R} (h : ∀ i : ℕ, b ^ i ∣ c * u ^ i) (r : R) (n : ℕ) :
    b ^ n ∣ c * (u - b * r) ^ n := by
  rw [sub_eq_add_neg, add_pow, Finset.mul_sum]
  refine Finset.dvd_sum fun i hi => ?_
  have hi : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [show b ^ n = b ^ i * b ^ (n - i) by rw [← pow_add, Nat.add_sub_cancel' hi]]
  have h2 : b ^ (n - i) ∣ (-(b * r)) ^ (n - i) := pow_dvd_pow_of_dvd ⟨-r, by ring⟩ _
  exact (mul_dvd_mul (h i) h2).trans ⟨n.choose i, by ring⟩

/-! ### 3. The main step -/

/-- **The main step.** Let `R` be a Noetherian local domain and let `x ∈ 𝔪` be a prime element. If `R / (x)` has property (D), then `R` has property (D). -/
theorem isDvdClosed_of_isDvdClosed_quotient [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {x : R} (hx : Prime x) (hxm : x ∈ maximalIdeal R) (hD : IsDvdClosed (R ⧸ span {x})) :
    IsDvdClosed R := by
  have key : ∀ a b c : R, ¬ x ∣ b → ¬ x ∣ c → (∀ n : ℕ, b ^ n ∣ c * a ^ n) → b ∣ a := by
    intro a b c hb hc h
    have hmk : ∀ y : R, ¬ x ∣ y → Ideal.Quotient.mk (span {x}) y ≠ 0 := fun y hy h0 =>
      hy (mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0))
    have claim : ∀ N : ℕ, ∃ r t : R, a = b * r + x ^ N * t ∧ ∀ n : ℕ, b ^ n ∣ c * t ^ n := by
      intro N
      induction N with
      | zero => exact ⟨0, a, by ring, h⟩
      | succ N ih =>
        obtain ⟨r, t, hrt, ht⟩ := ih
        obtain ⟨q, hq⟩ := hD (Ideal.Quotient.mk _ t) (Ideal.Quotient.mk _ b)
          (Ideal.Quotient.mk _ c) (hmk b hb) (hmk c hc) fun n => by
            simpa only [map_pow, map_mul] using map_dvd (Ideal.Quotient.mk (span {x})) (ht n)
        obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective q
        have hmem : t - b * r' ∈ span {x} := Ideal.Quotient.eq.mp (by rw [hq, map_mul])
        obtain ⟨t', ht'⟩ := mem_span_singleton'.mp hmem
        refine ⟨r + x ^ N * r', t', by linear_combination hrt - x ^ N * ht', fun n => ?_⟩
        refine dvd_of_dvd_prime_pow_mul hx (fun h' => hb (hx.dvd_of_dvd_pow h')) n ?_
        have h2 := pow_dvd_mul_sub_mul_pow ht r' n
        rw [← ht'] at h2
        exact h2.trans (dvd_of_eq (by ring))
    have hI : span {x} ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
      ((span_singleton_le_iff_mem _).mpr hxm)
    have hK := (span {x}).iInf_pow_smul_eq_bot_of_isLocalRing (M := R ⧸ span {b}) hI
    have hmem : Ideal.Quotient.mk (span {b}) a ∈
        (⨅ i : ℕ, span {x} ^ i • ⊤ : Submodule R (R ⧸ span {b})) := by
      refine Submodule.mem_iInf _ |>.mpr fun N => ?_
      obtain ⟨r, t, hrt, -⟩ := claim N
      have h1 : Ideal.Quotient.mk (span {b}) a = x ^ N • Ideal.Quotient.mk (span {b}) t := by
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq, hrt]
        exact mem_span_singleton.mpr ⟨r, by ring⟩
      rw [h1]
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (mem_span_singleton_self x) N)
        Submodule.mem_top
    rw [hK, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton] at hmem
    exact hmem
  intro a b c hb hc h
  obtain ⟨e, b', hb', rfl⟩ := WfDvdMonoid.max_power_factor hb hx.irreducible
  obtain ⟨f, c', hc', rfl⟩ := WfDvdMonoid.max_power_factor hc hx.irreducible
  obtain ⟨a', rfl, h'⟩ := exists_eq_pow_mul_forall_pow_dvd hx rfl rfl hb' hc' h
  exact mul_dvd_mul_left _ (key a' b' c' hb' hc' h')

/-! ### 4. Regular local rings -/

/-- A regular local ring of dimension `n` has property (D). The proof is by induction on `n`. -/
theorem isDvdClosed_of_isRegularLocalRing_of_ringKrullDim_eq (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R], ringKrullDim R = n → IsDvdClosed R := by
  induction n with
  | zero =>
    intro R _ _ h a b c hb _ _
    have h0 : (maximalIdeal R).spanFinrank = 0 := by
      have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
      rw [h] at this
      exact_mod_cast this
    have hbot : maximalIdeal R = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal R).fg_of_isNoetherianRing).mp h0
    have hu : IsUnit b := IsLocalRing.notMem_maximalIdeal.mp fun hm =>
      hb ((Submodule.mem_bot R).mp (hbot ▸ hm))
    exact hu.dvd
  | succ n ih =>
    intro R _ _ h
    have := isDomain_of_isRegularLocalRing R
    have hpos : 0 < ringKrullDim R := by
      rw [h]; exact_mod_cast Nat.succ_pos n
    obtain ⟨x, mem, nmem, -⟩ := exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes hpos
    obtain ⟨hQ, hdim⟩ := quotient_span_singleton mem nmem
    have := hQ
    have hQn : ringKrullDim (R ⧸ span {x}) = n := by
      obtain ⟨m, hm⟩ := exists_ringKrullDim_eq_natCast (R ⧸ span {x})
      rw [hm, h] at hdim
      have : m + 1 = n + 1 := by exact_mod_cast hdim
      rw [hm, Nat.succ_inj.mp this]
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact nmem (zero_mem _)
    have hprime : Prime x := (Ideal.span_singleton_prime hx0).mp
      ((Ideal.Quotient.isDomain_iff_prime _).mp (isDomain_of_isRegularLocalRing _))
    exact isDvdClosed_of_isDvdClosed_quotient hprime mem (ih _ hQn)

/-- **A regular local ring has property (D).** Let `R` be a regular local ring and let `a b c : R` with `b ≠ 0` and `c ≠ 0`. If `b ^ n ∣ c * a ^ n` for all `n`, then `b ∣ a`. -/
theorem dvd_of_forall_pow_dvd_mul_pow [IsRegularLocalRing R] (a b c : R) (hb : b ≠ 0)
    (hc : c ≠ 0) (h : ∀ n : ℕ, b ^ n ∣ c * a ^ n) : b ∣ a := by
  obtain ⟨n, hn⟩ := exists_ringKrullDim_eq_natCast R
  exact isDvdClosed_of_isRegularLocalRing_of_ringKrullDim_eq n R hn a b c hb hc h

/-- **A regular local ring is integrally closed** (Volume 1, Section 1.3 of the handbook). The handbook cites this from the theorem of Auslander-Buchsbaum ([Mat89, Theorem 20.3]). The proof here goes through property (D) and does not use unique factorization. -/
theorem isIntegrallyClosed_of_isRegularLocalRing (R : Type u) [CommRing R]
    [IsRegularLocalRing R] : IsIntegrallyClosed R := by
  have := isDomain_of_isRegularLocalRing R
  exact IsDvdClosed.isIntegrallyClosed fun a b c hb hc h =>
    dvd_of_forall_pow_dvd_mul_pow a b c hb hc h

/-- **Roots in a regular local ring.** Let `R` be a regular local ring with fraction field `K`, and let `g : K` with `g ^ n ∈ R` for some `n ≠ 0`. Then `g ∈ R`. -/
theorem mem_range_algebraMap_of_pow_mem [IsRegularLocalRing R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] {g : K} {n : ℕ} (hn : n ≠ 0)
    (hg : g ^ n ∈ (algebraMap R K).range) : g ∈ (algebraMap R K).range := by
  have := isDomain_of_isRegularLocalRing R
  have := isIntegrallyClosed_of_isRegularLocalRing R
  obtain ⟨y, hy⟩ := hg
  have hint : IsIntegral R g :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hy ▸ isIntegral_algebraMap)
  exact RingHom.mem_range.mpr (IsIntegrallyClosed.isIntegral_iff.mp hint)

end Singularity.Algebra
