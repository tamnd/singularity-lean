/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Filtration
import Singularity.Invariant.Order

/-!
# The monomial part of an ideal and the monomial order reduction step

This file proves the algebraic content of two results of Volume 2, Section 3.3 of the handbook.

## Lemma 3.3.7 (monomial part), local form

The proof of Lemma 3.3.7 works at the generic point of one component `D` of the divisors.
We prove the lemma for one element `t` of a ring `R`, which plays the role of a local
equation of `D`. The ideal `(t ^ c)` plays the role of `O(-cD)`.

* `Singularity.HasDivOrd t I`: there is a largest `c` with `I ⊆ (t ^ c)`.
* `Singularity.hasDivOrd_of_noetherian`: this holds if `R` is a Noetherian domain, `t` is not a
  unit and `I ≠ 0`. This is the Krull intersection theorem.
* `Singularity.divOrd t I`: this largest `c`, the number `c_D`.
* `Singularity.monoPart t I`: the ideal `(t ^ c)`, the monomial part `M(I)`.
* `Singularity.nonmonoPart t I`: the ideal of all `x` with `t ^ c * x ∈ I`, the nonmonomial
  part `N(I)`.
* `Singularity.monoPart_mul_nonmonoPart`: part (1), `I = M(I) * N(I)`.
* `Singularity.not_nonmonoPart_le`: part (1), `N(I)` is not contained in `(t)`.
* `Singularity.eq_nonmonoPart_of_mul`: part (1), the decomposition is unique.
* `Singularity.nonmonoPart_span_pow_mul`: part (2), `N((t ^ g) * B) = N(B)`, for `g ≥ 0`.
* `Singularity.le_nonmonoPart`: part (3), `B ⊆ N(B)`.
* `Singularity.idealOrd_nonmonoPart_le`: part (3), `ord N(B) ≤ ord B` at the origin of a
  polynomial ring.

Not proved: the sheaf form with several components `D` at the same time, and the reduction of
`c_D` to the order at the generic point of `D` on a normal variety. Part (2) is proved only for
`g ≥ 0`. The case of a negative coefficient follows by exchanging the two ideals.

## Theorem 3.3.8 (order reduction for monomial ideals), the key inequalities

Let `a i` be the coefficient of the divisor `E^i` at a point `y`, and let `S` be the set of
indices of the divisors through `y`. In Step `r` the rule blows up a set `B` with `|B| = r` and
`a_B = μ ≥ m`. The new divisor gets the coefficient `μ - m`. The hypothesis `(∗_s)` for
`s < r` says `a_P < m` for all `P ⊆ S` with `|P| < r`. For `P = ∅` this is `m ≥ 1`.

* `Singularity.monomialStep_lt_mu`: if `|A| < r`, the new value `μ - m + a_A` is less than `μ`.
* `Singularity.monomialStep_lt_mark`: if `|A| + 1 < r`, the new value `μ - m + a_A` is less
  than `m`, so the properties `(∗_s)` with `s < r` are kept.

Not proved: the blowups, the monomial form of the transforms, the formula for the order of a
monomial ideal, and the termination of the rule.
-/

namespace Singularity

open Ideal

section MonomialPart

variable {R : Type*} [CommRing R]

/-- There is a largest `c` with `I ⊆ (t ^ c)`. We state it as: some `(t ^ (c + 1))` does not
contain `I`. -/
abbrev HasDivOrd (t : R) (I : Ideal R) : Prop :=
  ∃ c : ℕ, ¬ I ≤ span {t ^ (c + 1)}

open Classical in
/-- The largest `c` with `I ⊆ (t ^ c)`, the number `c_D` of Lemma 3.3.7. It is `0` if there is
no largest such `c`. -/
noncomputable def divOrd (t : R) (I : Ideal R) : ℕ :=
  if h : HasDivOrd t I then Nat.find h else 0

theorem span_pow_le_span_pow (t : R) {a b : ℕ} (h : a ≤ b) :
    span {t ^ b} ≤ span {t ^ a} :=
  span_singleton_le_span_singleton.mpr (pow_dvd_pow t h)

theorem not_le_span_pow_divOrd_succ {t : R} {I : Ideal R} (h : HasDivOrd t I) :
    ¬ I ≤ span {t ^ (divOrd t I + 1)} := by
  classical
  simp only [divOrd, h, ↓reduceDIte]
  exact Nat.find_spec h

theorem le_span_pow_divOrd {t : R} {I : Ideal R} (h : HasDivOrd t I) :
    I ≤ span {t ^ divOrd t I} := by
  classical
  simp only [divOrd, h, ↓reduceDIte]
  rcases hc : Nat.find h with _ | n
  · simp
  · have := Nat.find_min h (show n < Nat.find h by omega)
    exact not_not.mp this

/-- `divOrd t I = c` if `I ⊆ (t ^ c)` and `I ⊄ (t ^ (c + 1))`. -/
theorem divOrd_eq_of {t : R} {I : Ideal R} {c : ℕ} (h1 : I ≤ span {t ^ c})
    (h2 : ¬ I ≤ span {t ^ (c + 1)}) : divOrd t I = c := by
  classical
  have h : HasDivOrd t I := ⟨c, h2⟩
  simp only [divOrd, h, ↓reduceDIte]
  rw [Nat.find_eq_iff]
  refine ⟨h2, fun n hn hle => hle ?_⟩
  exact h1.trans (span_pow_le_span_pow t (by omega))

/-- **Krull intersection.** In a Noetherian domain, if `t` is not a unit and `I ≠ 0`, then
there is a largest `c` with `I ⊆ (t ^ c)`. -/
theorem hasDivOrd_of_noetherian [IsNoetherianRing R] [IsDomain R] {t : R} {I : Ideal R}
    (ht : ¬ IsUnit t) (hI : I ≠ ⊥) : HasDivOrd t I := by
  by_contra h
  simp only [HasDivOrd, not_exists, not_not] at h
  apply hI
  have htop : span {t} ≠ ⊤ := fun h' => ht (span_singleton_eq_top.mp h')
  rw [eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isDomain (span {t}) htop]
  refine le_iInf fun n => ?_
  rw [span_singleton_pow]
  rcases n with _ | n
  · simp
  · exact h n

/-- The monomial part `M(I) = (t ^ c)` of Lemma 3.3.7. -/
noncomputable def monoPart (t : R) (I : Ideal R) : Ideal R :=
  span {t ^ divOrd t I}

/-- The nonmonomial part `N(I)` of Lemma 3.3.7: the ideal of all `x` with `t ^ c * x ∈ I`. -/
noncomputable def nonmonoPart (t : R) (I : Ideal R) : Ideal R where
  carrier := {x | t ^ divOrd t I * x ∈ I}
  add_mem' := fun {x y} (hx : t ^ divOrd t I * x ∈ I) (hy : t ^ divOrd t I * y ∈ I) =>
    show t ^ divOrd t I * (x + y) ∈ I by rw [mul_add]; exact I.add_mem hx hy
  zero_mem' := by simp
  smul_mem' := fun c x (hx : t ^ divOrd t I * x ∈ I) =>
    show t ^ divOrd t I * (c * x) ∈ I by rw [mul_left_comm]; exact I.mul_mem_left c hx

theorem mem_nonmonoPart {t : R} {I : Ideal R} {x : R} :
    x ∈ nonmonoPart t I ↔ t ^ divOrd t I * x ∈ I :=
  Iff.rfl

/-- **Volume 2, Lemma 3.3.7 (1)**, local form: `I = M(I) * N(I)`. -/
theorem monoPart_mul_nonmonoPart {t : R} {I : Ideal R} (h : HasDivOrd t I) :
    monoPart t I * nonmonoPart t I = I := by
  ext x
  rw [monoPart, mem_span_singleton_mul]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hx
    obtain ⟨z, rfl⟩ := mem_span_singleton.mp (le_span_pow_divOrd h hx)
    exact ⟨z, hx, rfl⟩

/-- **Volume 2, Lemma 3.3.7 (1)**, local form: `N(I)` is not contained in `(t)`, the ideal of
`D`. -/
theorem not_nonmonoPart_le {t : R} {I : Ideal R} (h : HasDivOrd t I) :
    ¬ nonmonoPart t I ≤ span {t} := by
  intro hN
  apply not_le_span_pow_divOrd_succ h
  intro x hx
  obtain ⟨z, rfl⟩ := mem_span_singleton.mp (le_span_pow_divOrd h hx)
  have hz : z ∈ nonmonoPart t I := hx
  obtain ⟨w, rfl⟩ := mem_span_singleton.mp (hN hz)
  exact mem_span_singleton.mpr ⟨w, by ring⟩

variable [IsDomain R]

/-- **Volume 2, Lemma 3.3.7 (1)**, local form: the decomposition is unique. If
`I = (t ^ a) * N'` with `N' ⊄ (t)` and `t ≠ 0`, then `a = c_D` and `N' = N(I)`. -/
theorem eq_nonmonoPart_of_mul {t : R} (ht : t ≠ 0) {I N' : Ideal R} {a : ℕ}
    (hI : I = span {t ^ a} * N') (hN' : ¬ N' ≤ span {t}) :
    divOrd t I = a ∧ N' = nonmonoPart t I := by
  have hta : t ^ a ≠ 0 := pow_ne_zero a ht
  have hd : divOrd t I = a := by
    refine divOrd_eq_of
      (hI ▸ Submodule.mul_le.mpr fun x hx y _ => Ideal.mul_mem_right y _ hx) ?_
    intro hle
    apply hN'
    intro z hz
    have hmem : t ^ a * z ∈ I := hI ▸ mem_span_singleton_mul.mpr ⟨z, hz, rfl⟩
    obtain ⟨w, hw⟩ := mem_span_singleton.mp (hle hmem)
    refine mem_span_singleton.mpr ⟨w, mul_left_cancel₀ hta ?_⟩
    rw [hw]
    ring
  refine ⟨hd, ?_⟩
  ext z
  rw [mem_nonmonoPart, hd]
  constructor
  · intro hz
    exact hI ▸ mem_span_singleton_mul.mpr ⟨z, hz, rfl⟩
  · intro hz
    rw [hI, mem_span_singleton_mul] at hz
    obtain ⟨z', hz', he⟩ := hz
    rwa [← mul_left_cancel₀ hta he]

/-- **Volume 2, Lemma 3.3.7 (2)**, local form, for a coefficient `g ≥ 0`:
`N((t ^ g) * B) = N(B)`. -/
theorem nonmonoPart_span_pow_mul {t : R} (ht : t ≠ 0) {B : Ideal R} (hB : HasDivOrd t B)
    (g : ℕ) : nonmonoPart t (span {t ^ g} * B) = nonmonoPart t B := by
  have hI : span {t ^ g} * B = span {t ^ (g + divOrd t B)} * nonmonoPart t B := by
    conv_lhs => rw [← monoPart_mul_nonmonoPart hB]
    rw [monoPart, ← mul_assoc, span_singleton_mul_span_singleton, pow_add]
  exact ((eq_nonmonoPart_of_mul ht hI (not_nonmonoPart_le hB)).2).symm

/-- In the setting of Lemma 3.3.7 (2), `c_D((t ^ g) * B) = g + c_D(B)`. -/
theorem divOrd_span_pow_mul {t : R} (ht : t ≠ 0) {B : Ideal R} (hB : HasDivOrd t B)
    (g : ℕ) : divOrd t (span {t ^ g} * B) = g + divOrd t B := by
  have hI : span {t ^ g} * B = span {t ^ (g + divOrd t B)} * nonmonoPart t B := by
    conv_lhs => rw [← monoPart_mul_nonmonoPart hB]
    rw [monoPart, ← mul_assoc, span_singleton_mul_span_singleton, pow_add]
  exact (eq_nonmonoPart_of_mul ht hI (not_nonmonoPart_le hB)).1

end MonomialPart

/-- **Volume 2, Lemma 3.3.7 (3)**, local form: `B ⊆ N(B)`. -/
theorem le_nonmonoPart {R : Type*} [CommRing R] (t : R) (B : Ideal R) :
    B ≤ nonmonoPart t B :=
  fun _ hx => B.mul_mem_left _ hx

/-- **Volume 2, Lemma 3.3.7 (3)**, order form: at the origin of a polynomial ring,
`ord N(B) ≤ ord B`. -/
theorem idealOrd_nonmonoPart_le {σ R : Type*} [CommRing R] (t : MvPolynomial σ R)
    (B : Ideal (MvPolynomial σ R)) : idealOrd (nonmonoPart t B) ≤ idealOrd B :=
  idealOrd_anti (le_nonmonoPart t B)

section MonomialStep

variable {ι : Type*} (a : ι → ℕ) (m : ℕ)

/-- **Volume 2, Theorem 3.3.8**, the first case of the proof. Assume `a_P < m` for all
`P ⊆ S` with `|P| < |B|`, and `m ≤ μ = a_B`. If `A ⊆ S` and `|A| < |B|`, then the value
`μ - m + a_A` at the new divisor and `A` is less than `μ`. -/
theorem monomialStep_lt_mu {S A B : Finset ι} (hA : A ⊆ S)
    (hstar : ∀ P ⊆ S, P.card < B.card → ∑ i ∈ P, a i < m)
    (hm : m ≤ ∑ i ∈ B, a i) (hAB : A.card < B.card) :
    ∑ i ∈ B, a i - m + ∑ i ∈ A, a i < ∑ i ∈ B, a i := by
  have := hstar A hA hAB
  omega

/-- **Volume 2, Theorem 3.3.8**, the second case of the proof. Assume `a_P < m` for all
`P ⊆ S` with `|P| < |B|`, and `m ≤ μ = a_B`, with `B ⊆ S`. If `A ⊆ S` and `|A| + 1 < |B|`,
then the value `μ - m + a_A` at the new divisor and `A` is less than `m`. -/
theorem monomialStep_lt_mark [DecidableEq ι] {S A B : Finset ι} (hA : A ⊆ S) (hB : B ⊆ S)
    (hstar : ∀ P ⊆ S, P.card < B.card → ∑ i ∈ P, a i < m)
    (hm : m ≤ ∑ i ∈ B, a i) (hAB : A.card + 1 < B.card) :
    ∑ i ∈ B, a i - m + ∑ i ∈ A, a i < m := by
  obtain ⟨l, hlB, hlA⟩ : ∃ l ∈ B, l ∉ A := by
    by_contra h
    push Not at h
    have := Finset.card_le_card (fun x hx => h x hx)
    omega
  have hP := hstar (insert l A) (Finset.insert_subset (hB hlB) hA)
    (by rw [Finset.card_insert_of_notMem hlA]; omega)
  have hQ := hstar (B.erase l) ((B.erase_subset l).trans hB)
    (Finset.card_erase_lt_of_mem hlB)
  rw [Finset.sum_insert hlA] at hP
  have hsum := Finset.sum_erase_add B a hlB
  omega

end MonomialStep

end Singularity
