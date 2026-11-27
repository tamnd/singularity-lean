/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.BlowupChart
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Strict transforms without a common prime factor

Let `R` be a regular local ring of dimension 2, let `x, y` be a regular system of parameters, let `B = R[y/x]` and let `R_1` be the localization of `B` at a prime. For `f ∈ R` with `f = x^a f'` in `R_1`, the element `f'` is the strict transform of `f`. This file proves Volume 5, Lemma 1.1.6 of the handbook: if `f` and `g` have no common prime factor in `R`, and `x` does not divide `f'` in `R_1`, then `f'` and `g'` have no common prime factor in `R_1`.

The proof of the handbook uses that `R` and `R_1` are unique factorization domains, and that a height 1 prime of `R_1` that does not contain `x` comes from a height 1 prime of `R`. The proof here uses only these facts.

1. `R` is a unique factorization domain.
2. `R → R_1` is injective, `R_1` is a domain and `x` is a prime of `R_1`.
3. Each `z ∈ R_1` can be written `z = r / s` with `r, s ∈ R`, where `s` is an associate of a power of `x` in `R_1`.

Property 3 holds when `R_1` is a localization of a ring `B ⊆ R_x` (`exists_mul_eq_algebraMap_of_isLocalization`). Let `p` be a prime of `R_1` that does not divide `x`. Write `s p = r` as in property 3, and let `π` be a prime factor of `r` in `R` with `p ∣ π` in `R_1`. If `p ∣ z` in `R_1` for some `z ∈ R`, then `s s' z = r r'` in `R` for some `r'` and `s'` as in property 3. The prime `π` divides `r` and does not divide `s s'`, so `π ∣ z`. Thus `π` divides `f` and `g` when `p` divides `f'` and `g'`.

The handbook asks that we are in case 2 of Proposition 1.1.3, and it uses Lemma 1.1.5 for the claim that `x` does not divide `f'` in `R_1`. Here this claim and the primality of `x` in `R_1` are hypotheses. The regularity of `R` enters only through the hypothesis that `R` is a unique factorization domain [Mat, Theorem 20.3].

## Main results

* `Singularity.exists_prime_forall_dvd_of_prime`: a prime `p` of `R_1` that does not divide `x` gives a prime `π` of `R` that divides each `z ∈ R` with `p ∣ z` in `R_1`.
* `Singularity.not_prime_dvd_transform`: the lemma under properties 1, 2 and 3.
* `Singularity.exists_mul_eq_algebraMap_of_isLocalization`: property 3 for a localization of a ring `B ⊆ R_x`.
* `Singularity.not_prime_dvd_transform_blowupChart`: the lemma for a localization `R_1` of the chart `R[𝔪/x]`.
-/

namespace Singularity

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Let `R → S` be injective, with `R` a unique factorization domain and `S` a domain. Assume that each `z ∈ S` is `r / s` with `r, s ∈ R` and `s` an associate of a power of `x` in `S`. Let `p` be a prime of `S` that does not divide `x`. Then there is a prime `π` of `R` that divides each `z ∈ R` with `p ∣ z` in `S`. -/
theorem exists_prime_forall_dvd_of_prime [IsDomain R] [UniqueFactorizationMonoid R] [IsDomain S]
    (hinj : Function.Injective (algebraMap R S)) {x : R}
    (hS : ∀ z : S, ∃ r s : R, ∃ j : ℕ,
      Associated (algebraMap R S s) (algebraMap R S x ^ j) ∧ algebraMap R S s * z = algebraMap R S r)
    {p : S} (hp : Prime p) (hpx : ¬ p ∣ algebraMap R S x) :
    ∃ π : R, Prime π ∧ ∀ z : R, p ∣ algebraMap R S z → π ∣ z := by
  have hps : ∀ t : R, (∃ i : ℕ, Associated (algebraMap R S t) (algebraMap R S x ^ i)) →
      ¬ p ∣ algebraMap R S t := by
    rintro t ⟨i, hi⟩ hpt
    exact hpx (hp.dvd_of_dvd_pow (hpt.trans hi.dvd))
  obtain ⟨r, s, j, hsj, hsp⟩ := hS p
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero] at hsp
    rcases mul_eq_zero.mp hsp with h | h
    · exact hps s ⟨j, hsj⟩ (by rw [h]; exact dvd_zero p)
    · exact hp.ne_zero h
  have hpr : p ∣ algebraMap R S r := ⟨algebraMap R S s, by rw [← hsp, mul_comm]⟩
  obtain ⟨m, hm, hmr⟩ := UniqueFactorizationMonoid.exists_prime_factors r hr0
  have hpm : p ∣ (m.map (algebraMap R S)).prod := by
    rw [← map_multiset_prod]
    exact hpr.trans (hmr.symm.map (algebraMap R S)).dvd
  obtain ⟨a, ha, hpa⟩ := hp.exists_mem_multiset_dvd hpm
  obtain ⟨π, hπ, rfl⟩ := Multiset.mem_map.mp ha
  have hπr : π ∣ r := (Multiset.dvd_prod hπ).trans hmr.dvd
  have hπt : ∀ t : R, (∃ i : ℕ, Associated (algebraMap R S t) (algebraMap R S x ^ i)) →
      ¬ π ∣ t := fun t ht hπt => hps t ht (hpa.trans (map_dvd (algebraMap R S) hπt))
  refine ⟨π, hm π hπ, fun z hz => ?_⟩
  obtain ⟨w, hw⟩ := hz
  obtain ⟨r', s', j', hs'j, hs'w⟩ := hS w
  have key : s * s' * z = r * r' := hinj (by
    simp only [map_mul]
    rw [hw, ← hsp, ← hs'w]
    ring)
  have hdvd : π ∣ s * s' * z := by
    rw [key]
    exact dvd_mul_of_dvd_left hπr r'
  rcases (hm π hπ).dvd_or_dvd hdvd with h | h
  · rcases (hm π hπ).dvd_or_dvd h with h' | h'
    · exact absurd h' (hπt s ⟨j, hsj⟩)
    · exact absurd h' (hπt s' ⟨j', hs'j⟩)
  · exact h

/-- **Volume 5, Lemma 1.1.6 of the handbook**, under properties 1, 2 and 3 of the module docstring. Let `R → R_1` be injective, with `R` a unique factorization domain, `R_1` a domain and `x` a prime of `R_1`. Assume that each `z ∈ R_1` is `r / s` with `r, s ∈ R` and `s` an associate of a power of `x` in `R_1`. Let `f = x^a f'` and `g = x^b g'` in `R_1`, with `x ∤ f'`. If `f` and `g` have no common prime factor in `R`, then `f'` and `g'` have no common prime factor in `R_1`. -/
theorem not_prime_dvd_transform [IsDomain R] [UniqueFactorizationMonoid R] [IsDomain S]
    (hinj : Function.Injective (algebraMap R S)) {x : R}
    (hS : ∀ z : S, ∃ r s : R, ∃ j : ℕ,
      Associated (algebraMap R S s) (algebraMap R S x ^ j) ∧ algebraMap R S s * z = algebraMap R S r)
    (hx : Prime (algebraMap R S x)) {f g : R} {f' g' : S} {a b : ℕ}
    (hf : algebraMap R S f = algebraMap R S x ^ a * f')
    (hg : algebraMap R S g = algebraMap R S x ^ b * g') (hf' : ¬ algebraMap R S x ∣ f')
    (hfg : ∀ π : R, Prime π → π ∣ f → π ∣ g → False) :
    ∀ p : S, Prime p → p ∣ f' → p ∣ g' → False := by
  intro p hp h1 h2
  have hpx : ¬ p ∣ algebraMap R S x := fun h =>
    hf' ((hp.associated_of_dvd hx h).symm.dvd.trans h1)
  obtain ⟨π, hπ, hdiv⟩ := exists_prime_forall_dvd_of_prime hinj hS hp hpx
  refine hfg π hπ (hdiv f ?_) (hdiv g ?_)
  · rw [hf]
    exact dvd_mul_of_dvd_right h1 _
  · rw [hg]
    exact dvd_mul_of_dvd_right h2 _

/-- Let `S` be a localization of an `R`-algebra `B`, and assume that each `b ∈ B` has `x^m b ∈ R` for some `m`, as for `B ⊆ R_x`. Then each `z ∈ S` is `r / s` with `r, s ∈ R` and `s` an associate of a power of `x` in `S`. -/
theorem exists_mul_eq_algebraMap_of_isLocalization {B : Type*} [CommRing B] [Algebra R B]
    [Algebra B S] [IsScalarTower R B S] (M : Submonoid B) [IsLocalization M S] (x : R)
    (hB : ∀ b : B, ∃ (m : ℕ) (r : R), algebraMap R B x ^ m * b = algebraMap R B r) (z : S) :
    ∃ r s : R, ∃ j : ℕ,
      Associated (algebraMap R S s) (algebraMap R S x ^ j) ∧ algebraMap R S s * z = algebraMap R S r := by
  obtain ⟨⟨b, t⟩, hz⟩ := IsLocalization.surj M z
  have hz' : z * algebraMap B S t = algebraMap B S b := hz
  obtain ⟨m, r₀, hm⟩ := hB b
  obtain ⟨l, r₁, hl⟩ := hB (t : B)
  have h₀ : algebraMap R S r₀ = algebraMap R S x ^ m * algebraMap B S b := by
    rw [IsScalarTower.algebraMap_apply R B S r₀, ← hm, map_mul, map_pow,
      ← IsScalarTower.algebraMap_apply R B S x]
  have h₁ : algebraMap R S r₁ = algebraMap R S x ^ l * algebraMap B S t := by
    rw [IsScalarTower.algebraMap_apply R B S r₁, ← hl, map_mul, map_pow,
      ← IsScalarTower.algebraMap_apply R B S x]
  have hu : IsUnit (algebraMap B S t) := IsLocalization.map_units S t
  refine ⟨x ^ l * r₀, r₁ * x ^ m, l + m, ?_, ?_⟩
  · have he : algebraMap R S (r₁ * x ^ m) = algebraMap R S x ^ (l + m) * algebraMap B S t := by
      rw [map_mul, map_pow, h₁, pow_add]
      ring
    rw [he]
    exact associated_mul_unit_left _ _ hu
  · simp only [map_mul, map_pow, h₀, h₁]
    linear_combination (algebraMap R S x ^ l * algebraMap R S x ^ m) * hz'

open IsLocalRing in
/-- **Volume 5, Lemma 1.1.6 of the handbook**, for a localization `R_1` of the chart `B = R[𝔪/x]` of the blowup. Let `R` be a local unique factorization domain, let `x ∈ 𝔪` with `x ≠ 0`, and let `R_1` be a domain that is a localization of `B` at a submonoid of nonzerodivisors, such as the localization at a prime. Let `x` be a prime of `R_1`. Let `f = x^a f'` and `g = x^b g'` in `R_1`, with `x ∤ f'`. If `f` and `g` have no common prime factor in `R`, then `f'` and `g'` have no common prime factor in `R_1`. -/
theorem not_prime_dvd_transform_blowupChart [IsDomain R] [IsLocalRing R]
    [UniqueFactorizationMonoid R] [IsDomain S] {x : R} (hx : x ∈ maximalIdeal R) (hx0 : x ≠ 0)
    [Algebra (Singularity.Algebra.blowupChart R x) S]
    [IsScalarTower R (Singularity.Algebra.blowupChart R x) S]
    (M : Submonoid (Singularity.Algebra.blowupChart R x))
    (hM : M ≤ nonZeroDivisors (Singularity.Algebra.blowupChart R x)) [IsLocalization M S]
    (hxS : Prime (algebraMap R S x)) {f g : R} {f' g' : S} {a b : ℕ}
    (hf : algebraMap R S f = algebraMap R S x ^ a * f')
    (hg : algebraMap R S g = algebraMap R S x ^ b * g') (hf' : ¬ algebraMap R S x ∣ f')
    (hfg : ∀ π : R, Prime π → π ∣ f → π ∣ g → False) :
    ∀ p : S, Prime p → p ∣ f' → p ∣ g' → False := by
  have hB : Function.Injective (algebraMap R (Singularity.Algebra.blowupChart R x)) :=
    fun c d h => Singularity.Algebra.algebraMap_away_injective hx0 (congrArg Subtype.val h)
  have hinj : Function.Injective (algebraMap R S) := by
    rw [IsScalarTower.algebraMap_eq R (Singularity.Algebra.blowupChart R x) S]
    exact (IsLocalization.injective S hM).comp hB
  have hchart : ∀ c : Singularity.Algebra.blowupChart R x, ∃ (m : ℕ) (r : R),
      algebraMap R (Singularity.Algebra.blowupChart R x) x ^ m * c =
        algebraMap R (Singularity.Algebra.blowupChart R x) r := by
    intro c
    obtain ⟨n, r, -, hr⟩ := (Singularity.Algebra.mem_blowupChart_iff hx).mp c.2
    refine ⟨n, r, Subtype.ext ?_⟩
    change algebraMap R (Localization.Away x) x ^ n * (c : Localization.Away x) =
      algebraMap R (Localization.Away x) r
    rw [mul_comm]
    exact hr
  exact not_prime_dvd_transform hinj
    (exists_mul_eq_algebraMap_of_isLocalization M x hchart) hxS hf hg hf' hfg

end Singularity
