/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.NodeRegular
import Singularity.Algebra.RegularOrderMul

/-!
# Multiplicity one and regularity

This file proves the provable parts of Volume 1, Remark 3.3.14 of the handbook. The remark says
that the converse of Theorem 3.3.13 holds for unmixed rings (a theorem of Nagata), and that it
fails without this hypothesis.

Lemma 3.3.12 and Theorem 3.3.13 are already in the library, in
`Singularity.Algebra.MultiplicityRegular`. Lemma 3.3.12 is
`Singularity.Algebra.mem_maximalIdeal_pow_of_mul_mem`. Theorem 3.3.13 is
`Singularity.Algebra.hilbertSamuel_succ_eq_choose`, `Singularity.Algebra.length_grPiece_eq_choose`
and `Singularity.Algebra.samuelMultiplicity_regular`. This file does not repeat them.

## Main results

* `Singularity.Algebra.isRegularLocalRing_quotient_iff_samuelMultiplicity_eq_one`: the theorem of
  Nagata for a hypersurface. Let `S` be a regular local ring of dimension `n + 1`, and let
  `f ∈ 𝔪` with `f ≠ 0`. Then `S/(f)` is regular if and only if `e_n(S/(f)) = 1`.
* `Singularity.Algebra.not_isRegularLocalRing_of_mul_maximalIdeal_eq_zero`: let `x ≠ 0` with
  `x 𝔪 = 0` and `x` not a unit. Then `R` is not regular.
* `Singularity.Algebra.ringKrullDim_quotient_span_singleton_of_mul_maximalIdeal_eq_zero`: under
  the same hypotheses, `dim R/(x) = dim R`.
* `Singularity.Algebra.samuelMultiplicity_eq_one_of_mul_maximalIdeal_eq_zero`: if moreover
  `R/(x)` is regular of dimension `d + 1`, then `e_(d+1)(𝔪, R) = 1`.

The last three results are the core of the counterexample of the remark. For
`R = k[x, y]_(x, y)/(x², x y)` the element `x` has `x 𝔪 = 0`, and `R/(x) = k[y]_(y)` is a
discrete valuation ring. So `dim R = 1`, `e(R) = 1` and `R` is not regular.

## What is not proved

* The theorem of Nagata itself: an unmixed Noetherian local ring with `e(R) = 1` is regular. It
  needs the theory of unmixed rings and of reductions of ideals, which are not in the library.
* The concrete ring `k[x, y]_(x, y)/(x², x y)`. We do not construct it, and we do not check the
  hypotheses of the general results above for it. The general results give the conclusion for
  each ring that satisfies them.

## Volume 1, Section 5.3

Theorem 5.3.3 for a field is `Singularity.regularLocus_isOpen_of_field` in
`Singularity.Scheme.RegularLocus`. Proposition 5.3.4 and Corollary 5.3.5 are already in
`Singularity.Scheme.RegularLocusJ2`: `Singularity.subset_regularLocus_of_isIso_restrict`,
`Singularity.isOpen_regularLocus_of_resolution` and `Singularity.isJ2_of_resolution`.
The other cases of Theorem 5.3.3 need the theory of excellent rings (Theorem 5.2.8).
Theorem 5.3.6 of Grothendieck needs the G-ring property and is out of reach.
This file adds nothing for Section 5.3.
-/

universe u

namespace Singularity.Algebra

open Module Filter fwdDiff IsLocalRing Ideal

section Hypersurface

variable {S : Type u} [CommRing S] [IsRegularLocalRing S]

/-- **The theorem of Nagata for a hypersurface** (Volume 1, Remark 3.3.14 of the handbook, the
case of a hypersurface). Let `S` be a regular local ring of dimension `n + 1`, and let `f ∈ 𝔪`
with `f ≠ 0`. Then `S/(f)` is a regular local ring if and only if `e_n(S/(f)) = 1`. -/
theorem isRegularLocalRing_quotient_iff_samuelMultiplicity_eq_one {n : ℕ}
    (hS : ringKrullDim S = (n + 1 : ℕ)) {f : S} (hm : f ∈ maximalIdeal S) (h0 : f ≠ 0)
    [IsLocalRing (S ⧸ span {f})] :
    IsRegularLocalRing (S ⧸ span {f}) ↔
      samuelMultiplicity (maximalIdeal (S ⧸ span {f})) (S ⧸ span {f}) n = 1 := by
  classical
  rw [isRegularLocalRing_quotient_span_singleton_iff S hm h0]
  have hex : ∃ k, f ∉ maximalIdeal S ^ k := by
    by_contra h
    push Not at h
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal S)
      (maximalIdeal.isMaximal S).ne_top
    have hf : f ∈ ⨅ i, maximalIdeal S ^ i := Submodule.mem_iInf _ |>.mpr h
    rw [hbot, Submodule.mem_bot] at hf
    exact h0 hf
  have hk0 : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h, pow_zero, one_eq_top] at this
    exact this Submodule.mem_top
  have hk1 : Nat.find hex ≠ 1 := by
    intro h
    have := Nat.find_spec hex
    rw [h, pow_one] at this
    exact this hm
  obtain ⟨d, hd⟩ : ∃ d, Nat.find hex = d + 1 := Nat.exists_eq_succ_of_ne_zero hk0
  have hf' : f ∉ maximalIdeal S ^ (d + 1) := hd ▸ Nat.find_spec hex
  have hf : f ∈ maximalIdeal S ^ d := by
    by_contra h
    exact Nat.find_min hex (by omega : d < Nat.find hex) h
  rw [samuelMultiplicity_hypersurface_of_notMem hS hf hf']
  constructor
  · intro h2
    by_contra hd1
    exact h2 (Ideal.pow_le_pow_right (by omega : 2 ≤ d) hf)
  · intro hd1
    subst hd1
    exact hf'

end Hypersurface

section Socle

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- If `R/(x)` is nontrivial, then `x` is not a unit. -/
theorem mem_maximalIdeal_of_nontrivial_quotient {x : R} [Nontrivial (R ⧸ span {x})] :
    x ∈ maximalIdeal R := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h : span {x} = ⊤ := span_singleton_eq_top.mpr hu
  have : Subsingleton (R ⧸ span {x}) := Ideal.Quotient.subsingleton_iff.mpr h
  exact not_subsingleton (R ⧸ span {x}) this

/-- Volume 1, Remark 3.3.14 of the handbook, the ring is not regular. Let `x ≠ 0` with
`x 𝔪 = 0` and `R/(x)` nontrivial. Then `R` is not a regular local ring, because `x² = 0`. -/
theorem not_isRegularLocalRing_of_mul_maximalIdeal_eq_zero {x : R} (hx0 : x ≠ 0)
    (hx : ∀ y ∈ maximalIdeal R, x * y = 0) [Nontrivial (R ⧸ span {x})] :
    ¬ IsRegularLocalRing R := by
  intro h
  have : IsDomain R := isDomain_of_isRegularLocalRing R
  exact hx0 (mul_self_eq_zero.mp (hx x mem_maximalIdeal_of_nontrivial_quotient))

/-- Volume 1, Remark 3.3.14 of the handbook, the dimension. Let `x 𝔪 = 0` with `R/(x)`
nontrivial. Then `x` is nilpotent, thus `dim R/(x) = dim R`. -/
theorem ringKrullDim_quotient_span_singleton_of_mul_maximalIdeal_eq_zero {x : R}
    (hx : ∀ y ∈ maximalIdeal R, x * y = 0) [Nontrivial (R ⧸ span {x})] :
    ringKrullDim (R ⧸ span {x}) = ringKrullDim R := by
  have hmem : x ∈ maximalIdeal R := mem_maximalIdeal_of_nontrivial_quotient
  have hsub : ((span {x} : Ideal R) : Set R) ⊆ nilradical R := by
    intro y hy
    obtain ⟨c, rfl⟩ := mem_span_singleton'.mp hy
    refine mem_nilradical.mpr ⟨2, ?_⟩
    rw [pow_two, show c * x * (c * x) = c * c * (x * x) by ring, hx x hmem, mul_zero]
  rw [ringKrullDim_quotient, (PrimeSpectrum.zeroLocus_eq_univ_iff _).mpr hsub, ringKrullDim]
  exact Order.krullDim_eq_of_orderIso (OrderIso.Set.univ)

/-- The `(j + 1)`-st forward difference does not see an added constant. -/
theorem fwdDiff_iter_succ_add_const (g : ℕ → ℤ) (a : ℤ) (j : ℕ) :
    Δ_[1]^[j + 1] (fun n => g n + a) = Δ_[1]^[j + 1] g := by
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
  congr 1
  funext n
  simp only [fwdDiff]
  ring

variable [IsNoetherianRing R]

/-- **Multiplicity one without regularity** (Volume 1, Remark 3.3.14 of the handbook, the core of
the counterexample). Let `R` be a Noetherian local ring, and let `x ≠ 0` with `x 𝔪 = 0`. Assume
that `R/(x)` is a regular local ring of dimension `d + 1`. Then `e_(d+1)(𝔪, R) = 1`.

For `n` large, `x ∉ 𝔪^n` and `(𝔪^n : x) = 𝔪`. The exact sequence
`0 → R/𝔪 → R/𝔪^n → R/((x) + 𝔪^n) → 0` gives `χ_R(n) = χ_(R/(x))(n) + 1`. -/
theorem samuelMultiplicity_eq_one_of_mul_maximalIdeal_eq_zero {d : ℕ} {x : R} (hx0 : x ≠ 0)
    (hx : ∀ y ∈ maximalIdeal R, x * y = 0) [IsRegularLocalRing (R ⧸ span {x})]
    (hd : ringKrullDim (R ⧸ span {x}) = (d + 1 : ℕ)) :
    samuelMultiplicity (maximalIdeal R) R (d + 1) = 1 := by
  have hmem : x ∈ maximalIdeal R := mem_maximalIdeal_of_nontrivial_quotient
  have hex : ∃ N, x ∉ maximalIdeal R ^ N := by
    by_contra h
    push Not at h
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R)
      (maximalIdeal.isMaximal R).ne_top
    have hx' : x ∈ ⨅ i, maximalIdeal R ^ i := Submodule.mem_iInf _ |>.mpr h
    rw [hbot, Submodule.mem_bot] at hx'
    exact hx0 hx'
  obtain ⟨N, hN⟩ := hex
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_eq_top] at hN
    exact hN Submodule.mem_top
  obtain ⟨N', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  -- The value of `χ_R(k + 1)` when `x ∉ 𝔪^(k+1)`.
  have hval : ∀ k, x ∉ maximalIdeal R ^ (k + 1) →
      hilbertSamuelInt (maximalIdeal R) R (k + 1) = ((k + (d + 1)).choose (d + 1) : ℤ) + 1 := by
    intro k hk
    have hK : ∀ u, x * u ∈ maximalIdeal R ^ (k + 1) ↔ u ∈ maximalIdeal R := by
      intro u
      constructor
      · intro hu
        by_contra hu'
        rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hu'
        obtain ⟨v, rfl⟩ := hu'
        apply hk
        have h := Ideal.mul_mem_right (↑v⁻¹ : R) _ hu
        rwa [mul_assoc, Units.mul_inv, mul_one] at h
      · intro hu
        rw [hx u hu]
        exact zero_mem _
    have hlen := length_quotient_eq_add_of_colon hK
    have hres : length R (R ⧸ maximalIdeal R) = 1 := by
      have : IsSimpleModule R (R ⧸ maximalIdeal R) :=
        isSimpleModule_iff_isCoatom.mpr Ideal.IsMaximal.out
      exact length_eq_one R (R ⧸ maximalIdeal R)
    have hq := hilbertSamuel_quotient_span_singleton_eq_length x (k + 1)
    rw [hilbertSamuel_succ_eq_choose hd] at hq
    rw [hilbertSamuelInt, hilbertSamuel_self_eq, hlen, hres, ← hq, ← Nat.cast_one (R := ℕ∞),
      ← Nat.cast_add, ENat.toNat_natCast]
    push_cast
    ring
  refine samuelMultiplicity_eq_of_eventually
    ((eventually_ge_atTop (N' + 1)).mono fun n hn => ?_)
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [fwdDiff_iter_apply_add]
  have h : (fun k => hilbertSamuelInt (maximalIdeal R) R (k + (N' + 1))) =
      fun k => ((k + (N' + d + 1)).choose (0 + (d + 1)) : ℤ) + 1 := by
    funext k
    have hk : x ∉ maximalIdeal R ^ (k + N' + 1) := fun h =>
      hN (Ideal.pow_le_pow_right (by omega) h)
    rw [show k + (N' + 1) = k + N' + 1 by omega, hval _ hk, zero_add,
      show k + N' + (d + 1) = k + (N' + d + 1) by omega]
  rw [h, fwdDiff_iter_succ_add_const (fun k => ((k + (N' + d + 1)).choose (0 + (d + 1)) : ℤ)),
    fwdDiff_iter_choose_add]
  simp

end Socle

end Singularity.Algebra
