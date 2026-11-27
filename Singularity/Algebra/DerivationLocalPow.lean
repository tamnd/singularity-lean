/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Singularity.Algebra.DerivationIdealPow

/-!
# Derivatives of an equation at a point of maximal multiplicity

This file proves Volume 6, Lemma 2.3.3 of the handbook, in its algebraic form.

Let `T` be a commutative ring, let `M` be a prime ideal of `T`, let `D` be a derivation of `T`,
and let `p ≥ 2`. If the image of `h` in the local ring `T_M` lies in `(M T_M)^p`, then
`D h ∈ M`. If moreover `D h` is the image of an element `f'` of a ring `S` under a ring map
`S → T`, then `f'` lies in the contraction of `M` to `S`.

The proof follows the handbook, but avoids extending `D` to `T_M`. The hypothesis gives
`s ∉ M` with `s * h ∈ M^p`. Volume 6, Lemma 1.2.4 (`Singularity.derivation_mem_pow_pred`) gives
`D (s * h) ∈ M^(p-1) ⊆ M`. Since `M` is prime, `h ∈ M`, so `s * D h ∈ M` by the Leibniz rule,
and `D h ∈ M`.

What is not proved here: the translation to the geometric statement of the handbook. That is,
the identification of points of multiplicity `p` with primes `M` of `S[X]/(h)` such that `h`
lies in the `p`-th power of the maximal ideal of the localization, and the extension of
`∂/∂u_i` to `S[X]` with `∂X/∂u_i = 0`. The second claim of the lemma (condition (E)) is also not
formalized. The theorems here take `T`, `D` and `h` as arguments, so they apply to that setting.

## Main results

* `Singularity.derivation_mem_of_mul_mem_pow`: `s ∉ M`, `s * h ∈ M^p`, `p ≥ 2` give `D h ∈ M`.
* `Singularity.derivation_mem_of_algebraMap_mem_pow`: the local form, with `h ∈ (M T_M)^p`.
* `Singularity.mem_comap_of_derivation_eq`: `D h = φ f'` gives `f' ∈ M.comap φ`.
-/

namespace Singularity

variable {R T : Type*} [CommSemiring R] [CommRing T] [Algebra R T]

/-- Let `M` be a prime ideal of `T`, let `D` be a derivation of `T`, and let `p ≥ 2`. If
`s * h ∈ M^p` for some `s ∉ M`, then `D h ∈ M`. This is the algebraic core of Volume 6,
Lemma 2.3.3 of the handbook, with the localization at `M` cleared by the factor `s`. -/
theorem derivation_mem_of_mul_mem_pow (D : Derivation R T T) (M : Ideal T) [M.IsPrime]
    {p : ℕ} (hp : 2 ≤ p) {s h : T} (hs : s ∉ M) (hsh : s * h ∈ M ^ p) : D h ∈ M := by
  have hle : M ^ (p - 1) ≤ M := Ideal.pow_le_self (by omega)
  have hD : D (s * h) ∈ M := hle (derivation_mem_pow_pred D M p _ hsh)
  have hM : s * h ∈ M := Ideal.pow_le_self (by omega) hsh
  have hh : h ∈ M := ((Ideal.IsPrime.mem_or_mem ‹_› hM).resolve_left hs)
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hD
  have h1 : s * D h ∈ M := by
    have := M.sub_mem hD (M.mul_mem_right (D s) hh)
    simpa using this
  exact (Ideal.IsPrime.mem_or_mem ‹_› h1).resolve_left hs

/-- Let `M` be a prime ideal of `T`, let `D` be a derivation of `T`, and let `p ≥ 2`. If
`h ∈ M^p`, then `D h ∈ M`. -/
theorem derivation_mem_of_mem_pow (D : Derivation R T T) (M : Ideal T) [M.IsPrime]
    {p : ℕ} (hp : 2 ≤ p) {h : T} (hh : h ∈ M ^ p) : D h ∈ M :=
  derivation_mem_of_mul_mem_pow D M hp (s := 1)
    (M.ne_top_iff_one.mp ‹M.IsPrime›.ne_top)
    (by simpa using hh)

/-- If the image of `h` in the local ring `T_M` lies in the `p`-th power of the maximal
ideal, then there is `s ∉ M` with `s * h ∈ M^p`. -/
theorem exists_mul_mem_pow_of_algebraMap_mem (M : Ideal T) [M.IsPrime] (p : ℕ) {h : T}
    (hh : algebraMap T (Localization.AtPrime M) h ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime M)) ^ p) :
    ∃ s ∉ M, s * h ∈ M ^ p := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow] at hh
  obtain ⟨⟨⟨a, ha⟩, ⟨t, ht⟩⟩, he⟩ :=
    (IsLocalization.mem_map_algebraMap_iff M.primeCompl (Localization.AtPrime M)).mp hh
  simp only [← map_mul] at he
  obtain ⟨⟨u, hu⟩, hu'⟩ := (IsLocalization.eq_iff_exists M.primeCompl _).mp he
  refine ⟨u * t, fun hm => ?_, ?_⟩
  · rcases (Ideal.IsPrime.mem_or_mem ‹_› hm) with h1 | h1
    exacts [hu h1, ht h1]
  · have : u * (h * t) = u * a := hu'
    rw [show u * t * h = u * (h * t) by ring, this]
    exact Ideal.mul_mem_left _ _ ha

/-- Volume 6, Lemma 2.3.3 of the handbook, local form: let `M` be a prime ideal of `T`, let
`D` be a derivation of `T`, and let `p ≥ 2`. If the image of `h` in `T_M` lies in
`(M T_M)^p`, then `D h ∈ M`. -/
theorem derivation_mem_of_algebraMap_mem_pow (D : Derivation R T T) (M : Ideal T)
    [M.IsPrime] {p : ℕ} (hp : 2 ≤ p) {h : T}
    (hh : algebraMap T (Localization.AtPrime M) h ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime M)) ^ p) : D h ∈ M := by
  obtain ⟨s, hs, hsh⟩ := exists_mul_mem_pow_of_algebraMap_mem M p hh
  exact derivation_mem_of_mul_mem_pow D M hp hs hsh

/-- Volume 6, Lemma 2.3.3 of the handbook: let `φ : S → T` be a ring map, let `M` be a prime
ideal of `T`, let `D` be a derivation of `T`, and let `p ≥ 2`. Suppose that the image of `h`
in `T_M` lies in `(M T_M)^p` and that `D h = φ f'`. Then `f'` lies in the contraction of `M`
to `S`. -/
theorem mem_comap_of_derivation_eq {S : Type*} [CommRing S] (φ : S →+* T)
    (D : Derivation R T T) (M : Ideal T) [M.IsPrime] {p : ℕ} (hp : 2 ≤ p) {h : T} {f' : S}
    (hh : algebraMap T (Localization.AtPrime M) h ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime M)) ^ p)
    (hf : D h = φ f') : f' ∈ M.comap φ := by
  rw [Ideal.mem_comap, ← hf]
  exact derivation_mem_of_algebraMap_mem_pow D M hp hh

/-- The sign variant of `mem_comap_of_derivation_eq`, matching the handbook, where
`h = X^p - f` and `∂h/∂u_i = -∂f/∂u_i`. -/
theorem mem_comap_of_derivation_eq_neg {S : Type*} [CommRing S] (φ : S →+* T)
    (D : Derivation R T T) (M : Ideal T) [M.IsPrime] {p : ℕ} (hp : 2 ≤ p) {h : T} {f' : S}
    (hh : algebraMap T (Localization.AtPrime M) h ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime M)) ^ p)
    (hf : D h = -φ f') : f' ∈ M.comap φ := by
  rw [Ideal.mem_comap, ← neg_mem_iff, ← hf]
  exact derivation_mem_of_algebraMap_mem_pow D M hp hh

end Singularity
