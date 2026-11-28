/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Singularity.Statements.LocalUniformization
import Singularity.Valuation.ZariskiRiemann

/-!
# Special cases of the theorems of Ostrowski and Abhyankar, and of Proposition 4.1.2

This file proves special cases of three results of Volume 3 of the handbook.

Theorem 3.1.4 (Ostrowski), in the case of a prime with a single prime above it. Then the defect
is 1, and `n = e * f`, so `n = p ^ ν * e * f` with `ν = 0`.

* `ramificationIdx_mul_inertiaDeg_eq_finrank_of_primesOver_eq`: let `S` be a finite flat
  algebra over a domain `R`, and let `p` be a prime of `R` with exactly one prime `P` of `S`
  over it. Then `e(P) * f(P)` is the rank of `S` over `R`.
* `exists_pow_mul_eq_finrank_of_primesOver_eq`: the same in the form `n = q ^ ν * e * f`.
* `primesOver_eq_maximalIdeal_of_isLocalRing`: if `S` is local and integral over `R`, and `p`
  is maximal, then the maximal ideal of `S` is the only prime over `p`.
* `ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing`: so `e * f = n` for a finite flat
  local extension `S` of a local domain `R` with maximal ideal `p`.
* `ramificationIdx_mul_inertiaDeg_eq_finrank_fractionRing` and
  `ramificationIdx_mul_inertiaDeg_eq_finrank_fractionRing_of_isLocalRing`: the same with
  `n = [L : K]`, when `R` is a Dedekind domain with fraction field `K` and `S` is a finite domain
  over `R` with fraction field `L`. If `R` is a discrete valuation ring and `S` is local, for
  example the integral closure of a complete discrete valuation ring, this is the case of a
  complete discretely valued field.

The theorem for a general henselian field is not proved. In particular, the case of a defect
`p ^ ν` with `ν > 0` does not occur here. The fact that the integral closure of a complete
discrete valuation ring in a finite extension is local is not proved here. It is a hypothesis.

Theorem 2.3.3 (Abhyankar), in two special cases.

* `ValuationSubring.eq_of_le_of_valuation_lt_one`: a valuation ring `A` that dominates a
  valuation ring `B` of the same field is equal to `B`.
* `rank_valueGroup_eq_one_of_isDiscreteValuationRing`: the value group of a valuation ring that
  is a discrete valuation ring has rank 1 over `ℤ`.
* `abhyankar_local_of_isDiscreteValuationRing`: Theorem 2.3.3 when `R` is a discrete valuation
  ring, that is, a regular local ring of dimension 1. Then `v` is the valuation of `R`, the
  rational rank is 1, the map `κ → Kv` is onto, so `trdeg(Kv/κ) = 0`, and `dim R = 1`. So
  equality holds.
* `le_of_mul_pow_le_mul_pow`: if `C N ^ k ≤ A N ^ d` for all large `N`, with `C > 0`, then
  `k ≤ d`.
* `add_le_of_choose_mul_choose_le`: the numerical part of Steps 3 and 4 of the proof. If a
  function `ℓ` has the lower bound of Step 3 and the polynomial upper bound of Step 4, then
  `r + s ≤ d`.

Theorem 2.3.3 for a general Noetherian local domain is not proved. The case of a regular local
ring of dimension 2 is not proved. The length bounds of Steps 2, 3 and 4 for a ring `R` are not
proved here. Only the numerical consequence is proved.

Proposition 4.1.2, in the affine form.

* `mem_valuationCenter_iff'`: an element is in the center if and only if its value is less
  than 1.
* `isOpen_setOf_regularCenter`: for an affine model `A`, the set of the points of `ZR(K/k)`
  with a regular center on `Spec A` is open, if the regular locus of `Spec A` is open.
* `exists_finset_affineModel_regularCenter`: Proposition 4.1.2 in the affine form. If each
  valuation of `K/k` has local uniformization, and the regular locus of each affine model is
  open, then there are finitely many affine models such that each valuation of `K/k` has a
  regular center on one of them.

The openness of the regular locus (Theorem 5.3.3 of Volume 1) is a hypothesis here. The
statement is about affine models. The proper birational morphisms `X_i → X` of the handbook are
not constructed.
-/

namespace Singularity

open Module

/-! ### Theorem 3.1.4 with one prime above -/

section Ostrowski

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Theorem 3.1.4 with one prime above `p`. Let `S` be a finite flat algebra over a domain `R`,
and let `P` be the only prime of `S` over the prime `p`. Then `e(P) * f(P)` is the rank of `S`
over `R`. -/
theorem ramificationIdx_mul_inertiaDeg_eq_finrank_of_primesOver_eq [IsDomain R]
    [Module.Finite R S] [Module.Flat R S] (p : Ideal R) [p.IsPrime] (P : Ideal S)
    (hP : p.primesOver S = {P}) :
    P.ramificationIdx R * P.inertiaDeg R = finrank R S := by
  have hfin : (p.primesOver S).Finite := hP ▸ Set.finite_singleton P
  let _ : Fintype (p.primesOver S) := hfin.fintype
  rw [← Ideal.sum_ramification_inertia_eq_finrank p S,
    ← Finset.sum_subtype (p.primesOver S).toFinset (fun q => by simp)
      (fun q => q.ramificationIdx R * q.inertiaDeg R)]
  have h : (p.primesOver S).toFinset = {P} := by
    ext q
    rw [Set.mem_toFinset, hP]
    simp
  rw [h, Finset.sum_singleton]

/-- Theorem 3.1.4 with one prime above `p`, in the form `n = q ^ ν * e * f`. Here `ν = 0` for
each `q`, because the defect is 1. -/
theorem exists_pow_mul_eq_finrank_of_primesOver_eq [IsDomain R] [Module.Finite R S]
    [Module.Flat R S] (p : Ideal R) [p.IsPrime] (P : Ideal S) (hP : p.primesOver S = {P})
    (q : ℕ) : ∃ ν : ℕ, finrank R S = q ^ ν * P.ramificationIdx R * P.inertiaDeg R :=
  ⟨0, by rw [pow_zero, one_mul, ramificationIdx_mul_inertiaDeg_eq_finrank_of_primesOver_eq p P hP]⟩

/-- If `S` is a local ring that is integral over `R`, and `p` is a maximal ideal of `R`, then the
maximal ideal of `S` is the only prime of `S` over `p`. -/
theorem primesOver_eq_maximalIdeal_of_isLocalRing [IsLocalRing S] [Algebra.IsIntegral R S]
    [FaithfulSMul R S] (p : Ideal R) [p.IsMaximal] :
    p.primesOver S = {IsLocalRing.maximalIdeal S} := by
  refine Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨?_, fun P hP => ?_⟩
  · obtain ⟨Q, hmax, hover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := S) p
    exact ⟨Q, hmax.isPrime, hover⟩
  · have : P.IsPrime := hP.1
    have : P.LiesOver p := hP.2
    exact IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.of_liesOver_isMaximal P p)

/-- Theorem 3.1.4 for a finite flat local extension. Let `S` be a local ring that is a finite flat
algebra over a domain `R`, and let `p` be a maximal ideal of `R`. Then `e * f` is the rank of `S`
over `R`. -/
theorem ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing [IsDomain R] [IsLocalRing S]
    [Module.Finite R S] [Module.Flat R S] [FaithfulSMul R S] (p : Ideal R) [p.IsMaximal] :
    (IsLocalRing.maximalIdeal S).ramificationIdx R * (IsLocalRing.maximalIdeal S).inertiaDeg R =
      finrank R S :=
  ramificationIdx_mul_inertiaDeg_eq_finrank_of_primesOver_eq p _
    (primesOver_eq_maximalIdeal_of_isLocalRing p)

end Ostrowski

section OstrowskiDedekind

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDomain S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L]
  [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]

/-- Theorem 3.1.4 over a Dedekind domain with one prime above `p`: `e * f = [L : K]`. -/
theorem ramificationIdx_mul_inertiaDeg_eq_finrank_fractionRing (p : Ideal R) [p.IsPrime]
    (P : Ideal S) (hP : p.primesOver S = {P}) :
    P.ramificationIdx R * P.inertiaDeg R = finrank K L := by
  rw [IsFractionRing.finrank_eq R K S L]
  exact ramificationIdx_mul_inertiaDeg_eq_finrank_of_primesOver_eq p P hP

/-- Theorem 3.1.4 over a Dedekind domain when `S` is local, for example a discrete valuation
ring: `e * f = [L : K]` for the maximal ideal of `S` over a maximal ideal `p` of `R`. -/
theorem ramificationIdx_mul_inertiaDeg_eq_finrank_fractionRing_of_isLocalRing [IsLocalRing S]
    (p : Ideal R) [p.IsMaximal] :
    (IsLocalRing.maximalIdeal S).ramificationIdx R * (IsLocalRing.maximalIdeal S).inertiaDeg R =
      finrank K L :=
  ramificationIdx_mul_inertiaDeg_eq_finrank_fractionRing K L p _
    (primesOver_eq_maximalIdeal_of_isLocalRing p)

end OstrowskiDedekind

/-! ### Theorem 2.3.3 for a discrete valuation ring -/

section AbhyankarDVR

variable {K : Type*} [Field K]

/-- A valuation ring `A` of `K` that dominates a valuation ring `B` of `K` is equal to `B`. The
domination says that each element of `B` with value less than 1 for `B` has value less than 1
for `A`. -/
theorem ValuationSubring.eq_of_le_of_valuation_lt_one {A B : ValuationSubring K} (hBA : B ≤ A)
    (hdom : ∀ x ∈ B, B.valuation x < 1 → A.valuation x < 1) : A = B := by
  refine le_antisymm (fun x hx => ?_) hBA
  by_contra hxB
  have hx0 : x ≠ 0 := fun h => hxB (h ▸ B.zero_mem)
  have hinv : x⁻¹ ∈ B := (B.mem_or_inv_mem x).resolve_left hxB
  have hlt : B.valuation x⁻¹ < 1 := by
    rcases lt_or_eq_of_le ((B.valuation_le_one_iff x⁻¹).mpr hinv) with h | h
    · exact h
    · exfalso
      apply hxB
      have hm : B.valuation x * B.valuation x⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hx0, map_one]
      rw [h, mul_one] at hm
      exact (B.valuation_le_one_iff x).mp hm.le
  have h1 := hdom _ hinv hlt
  have h2 : A.valuation x ≤ 1 := (A.valuation_le_one_iff x).mpr hx
  have h3 := mul_lt_one_of_lt_of_le h1 h2
  rw [← map_mul, inv_mul_cancel₀ hx0, map_one] at h3
  exact lt_irrefl _ h3

/-- The value group of a valuation ring `B` that is a discrete valuation ring is infinite cyclic,
so it has rank 1 over `ℤ`. -/
theorem rank_valueGroup_eq_one_of_isDiscreteValuationRing (B : ValuationSubring K)
    [IsDiscreteValuationRing B] : Module.rank ℤ (Additive B.ValueGroupˣ) = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hϖ0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hv0 : B.valuation (ϖ : K) ≠ 0 := by simpa using hϖ0
  let g : B.ValueGroupˣ := Units.mk0 _ hv0
  have hg : g < 1 := by
    rw [← Units.val_lt_val, Units.val_mk0, Units.val_one, ← B.valuation_lt_one_iff ϖ]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hϖ.not_isUnit
  have hpow : ∀ y : B, (y : K) ≠ 0 → ∃ n : ℕ, B.valuation (y : K) = (g : B.ValueGroup) ^ n := by
    intro y hy
    obtain ⟨n, u, hu⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (x := y)
        (fun h => hy (by rw [h]; simp)) hϖ
    refine ⟨n, ?_⟩
    rw [hu, Subring.coe_mul, Subring.coe_pow, map_mul, map_pow, B.valuation_unit, one_mul,
      Units.val_mk0]
  have hsurj : ∀ γ : B.ValueGroupˣ, ∃ n : ℤ, g ^ n = γ := by
    intro γ
    obtain ⟨z, hz⟩ := B.valuation_surjective (γ : B.ValueGroup)
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact γ.ne_zero (by simpa using hz.symm)
    rcases B.mem_or_inv_mem z with h | h
    · obtain ⟨n, hn⟩ := hpow ⟨z, h⟩ hz0
      refine ⟨n, Units.ext ?_⟩
      rw [← hz, hn, Units.val_zpow_eq_zpow_val, zpow_natCast]
    · obtain ⟨n, hn⟩ := hpow ⟨z⁻¹, h⟩ (inv_ne_zero hz0)
      refine ⟨-(n : ℤ), Units.ext ?_⟩
      rw [← hz, Units.val_zpow_eq_zpow_val, zpow_neg, zpow_natCast, ← hn, map_inv₀, inv_inv]
  let e : ℤ ≃+ Additive B.ValueGroupˣ :=
    AddEquiv.ofBijective (zmultiplesHom (Additive B.ValueGroupˣ) (Additive.ofMul g))
      ⟨fun m n hmn => (zpow_right_strictAnti hg).injective
        (by simpa using congrArg Additive.toMul hmn),
        fun γ => by
          obtain ⟨n, hn⟩ := hsurj (Additive.toMul γ)
          exact ⟨n, by
            change n • Additive.ofMul g = γ
            rw [← ofMul_zpow, hn, ofMul_toMul]⟩⟩
  have := e.toIntLinearEquiv.lift_rank_eq
  rw [rank_self, Cardinal.lift_one] at this
  simpa using this.symm

/-- Theorem 2.3.3 when `R` is a discrete valuation ring, that is, a regular local ring of
dimension 1. Let `B` be a valuation ring of `K` that is a discrete valuation ring, and let `A` be
a valuation ring of `K` that dominates `B`. Then `A = B`, the rational rank of the value group of
`A` is 1, the map from `B` to the residue field of `A` is onto, so `trdeg(Kv/κ) = 0`, and the
dimension of `B` is 1. So `rr Γ_v + trdeg(Kv/κ) = 1 = dim B`. -/
theorem abhyankar_local_of_isDiscreteValuationRing {A B : ValuationSubring K}
    [IsDiscreteValuationRing B] (hBA : B ≤ A)
    (hdom : ∀ x ∈ B, B.valuation x < 1 → A.valuation x < 1) :
    A = B ∧ Module.rank ℚ (TensorProduct ℤ ℚ (Additive A.ValueGroupˣ)) = 1 ∧
      Function.Surjective (fun b : B => IsLocalRing.residue A ⟨b, hBA b.2⟩) ∧
      ringKrullDim B = 1 := by
  have hAB := ValuationSubring.eq_of_le_of_valuation_lt_one hBA hdom
  refine ⟨hAB, ?_, ?_, IsDiscreteValuationRing.ringKrullDim_eq_one B⟩
  · rw [(TensorProduct.isBaseChange ℤ (Additive A.ValueGroupˣ) ℚ).rank_eq]
    subst hAB
    exact rank_valueGroup_eq_one_of_isDiscreteValuationRing A
  · intro y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    have ha : (a : K) ∈ B := hAB ▸ a.2
    exact ⟨⟨a, ha⟩, rfl⟩

end AbhyankarDVR

/-! ### The numerical part of the proof of Theorem 2.3.3 -/

section Numerical

/-- If `C N ^ k ≤ A N ^ d` for all `N ≥ N₀`, with `C > 0`, then `k ≤ d`. -/
theorem le_of_mul_pow_le_mul_pow (k d N₀ : ℕ) (C A : ℝ) (hC : 0 < C)
    (h : ∀ N : ℕ, N₀ ≤ N → C * (N : ℝ) ^ k ≤ A * (N : ℝ) ^ d) : k ≤ d := by
  by_contra hkd
  rw [not_le] at hkd
  set N : ℕ := max N₀ (⌈A / C⌉₊ + 1) with hNdef
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := le_trans (Nat.le_add_left 1 _) (le_max_right _ _)
    exact_mod_cast this
  have hNA : A / C < N := by
    have h1 : A / C ≤ ⌈A / C⌉₊ := Nat.le_ceil _
    have h2 : ((⌈A / C⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast le_max_right _ _
    push_cast at h2
    linarith
  have hpos : 0 < (N : ℝ) ^ d := by positivity
  have hle : (N : ℝ) ^ d * N ≤ (N : ℝ) ^ k := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ hN1 hkd
  have hCN : C * N * (N : ℝ) ^ d ≤ A * (N : ℝ) ^ d := by
    calc C * N * (N : ℝ) ^ d = C * ((N : ℝ) ^ d * N) := by ring
      _ ≤ C * (N : ℝ) ^ k := mul_le_mul_of_nonneg_left hle hC.le
      _ ≤ A * (N : ℝ) ^ d := h N (le_max_left _ _)
  have h3 : C * N ≤ A := le_of_mul_le_mul_right hCN hpos
  have h4 : A < N * C := (div_lt_iff₀ hC).mp hNA
  linarith

/-- The numerical part of Steps 3 and 4 of the proof of Theorem 2.3.3. Let `ℓ N` be a function
with the lower bound `ℓ (2 k₀ M + 1) ≥ C(M + r, r) C(M + s, s)` of Step 3 for each `M`, and with
an upper bound `ℓ N ≤ A N ^ d` for large `N`, as in Step 4. Then `r + s ≤ d`. In the proof of the
handbook, `ℓ N` is the length of `R / 𝔪 ^ N`. -/
theorem add_le_of_choose_mul_choose_le (r s d k₀ N₀ : ℕ) (hk₀ : 1 ≤ k₀) (ℓ : ℕ → ℝ) (A : ℝ)
    (hlow : ∀ M : ℕ, (((M + r).choose r * (M + s).choose s : ℕ) : ℝ) ≤ ℓ (2 * k₀ * M + 1))
    (hup : ∀ N : ℕ, N₀ ≤ N → ℓ N ≤ A * (N : ℝ) ^ d) : r + s ≤ d := by
  have hr : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hs : (0 : ℝ) < s.factorial := by exact_mod_cast Nat.factorial_pos s
  refine le_of_mul_pow_le_mul_pow (r + s) d (N₀ + 1) (1 / (r.factorial * s.factorial))
    (max A 0 * (2 * k₀ : ℝ) ^ d) (by positivity) ?_
  intro N hN
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hcr : ((M + 1 : ℕ) : ℝ) ^ r / r.factorial ≤ (M + r).choose r := by
    have := Nat.pow_le_choose (α := ℝ) r (M + r)
    rwa [show M + r + 1 - r = M + 1 by omega] at this
  have hcs : ((M + 1 : ℕ) : ℝ) ^ s / s.factorial ≤ (M + s).choose s := by
    have := Nat.pow_le_choose (α := ℝ) s (M + s)
    rwa [show M + s + 1 - s = M + 1 by omega] at this
  have hlow' := hlow M
  push_cast at hlow'
  have hupM := hup (2 * k₀ * M + 1) (by nlinarith)
  have hbig : ((2 * k₀ * M + 1 : ℕ) : ℝ) ≤ (2 * k₀ : ℝ) * ((M + 1 : ℕ) : ℝ) := by
    push_cast
    have : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk₀
    nlinarith
  have hupM' : ℓ (2 * k₀ * M + 1) ≤ max A 0 * ((2 * k₀ : ℝ) * ((M + 1 : ℕ) : ℝ)) ^ d := by
    calc ℓ (2 * k₀ * M + 1) ≤ A * ((2 * k₀ * M + 1 : ℕ) : ℝ) ^ d := hupM
      _ ≤ max A 0 * ((2 * k₀ * M + 1 : ℕ) : ℝ) ^ d :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max A 0 * ((2 * k₀ : ℝ) * ((M + 1 : ℕ) : ℝ)) ^ d :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbig d)
            (le_max_right _ _)
  calc 1 / (r.factorial * s.factorial : ℝ) * ((M + 1 : ℕ) : ℝ) ^ (r + s)
      = (((M + 1 : ℕ) : ℝ) ^ r / r.factorial) * (((M + 1 : ℕ) : ℝ) ^ s / s.factorial) := by
        rw [pow_add]; field_simp
    _ ≤ ((M + r).choose r : ℝ) * (M + s).choose s :=
        mul_le_mul hcr hcs (by positivity) (by positivity)
    _ ≤ ℓ (2 * k₀ * M + 1) := hlow'
    _ ≤ max A 0 * ((2 * k₀ : ℝ) * ((M + 1 : ℕ) : ℝ)) ^ d := hupM'
    _ = max A 0 * (2 * k₀ : ℝ) ^ d * ((M + 1 : ℕ) : ℝ) ^ d := by rw [mul_pow, mul_assoc]

end Numerical

/-! ### Proposition 4.1.2 in the affine form -/

section Cover

open TopologicalSpace

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The points of `ZR(K/k)` with a regular center on `Spec A`: the points `w` with `A ⊆ 𝒪_w` such
that the localization of `A` at the center `𝔪_w ∩ A` is a regular local ring. -/
def regularCenterSet (A : Subalgebra k K) : Set (ZariskiRiemann k K) :=
  {w | ∃ h : ∀ a : A, (a : K) ∈ w.toValuationSubring,
    IsRegularLocalRing (Localization.AtPrime (valuationCenter w.toValuationSubring A h))}

/-- An element `b` of `A` is in the center `𝔪_V ∩ A` if and only if its value is less than 1. -/
theorem mem_valuationCenter_iff' {V : ValuationSubring K} {A : Subalgebra k K}
    {h : ∀ a : A, (a : K) ∈ V} {b : A} :
    b ∈ valuationCenter V A h ↔ V.valuation (b : K) < 1 := by
  unfold valuationCenter
  rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

/-- Let `A` be a finitely generated `k`-subalgebra of `K` whose regular locus is open in
`Spec A`. Then the set of the points of `ZR(K/k)` with a regular center on `Spec A` is open. -/
theorem isOpen_setOf_regularCenter (A : Subalgebra k K) (hA : A.FG)
    (hopen : IsOpen {P : PrimeSpectrum A | IsRegularLocalRing (Localization.AtPrime P.asIdeal)}) :
    IsOpen (regularCenterSet A) := by
  classical
  obtain ⟨s, hs⟩ := hA
  rw [isOpen_iff_forall_mem_open]
  rintro w ⟨h, hreg⟩
  let P : PrimeSpectrum A := ⟨valuationCenter w.toValuationSubring A h, inferInstance⟩
  obtain ⟨_, ⟨b, rfl⟩, hPb, hbG⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens).isOpen_iff.mp hopen P hreg
  have hb1 : ¬ w.toValuationSubring.valuation (b : K) < 1 := by
    intro hlt
    apply hPb
    change b ∈ valuationCenter _ _ _
    rwa [mem_valuationCenter_iff']
  have hb : (b : K) ≠ 0 := by
    intro h0
    apply hb1
    rw [h0, map_zero]
    exact zero_lt_one
  refine ⟨ZariskiRiemann.basicOpen (s ∪ {(b : K)⁻¹}), ?_, ZariskiRiemann.isOpen_basicOpen _,
    ?_⟩
  · intro u hu
    have hsub : ∀ a : A, (a : K) ∈ u.toValuationSubring := by
      intro a
      have ha : (a : K) ∈ Algebra.adjoin k (s : Set K) := hs ▸ a.2
      exact Algebra.adjoin_le (S := { u.toValuationSubring.toSubring with
        algebraMap_mem' := fun c => u.algebraMap_mem c })
        (fun x hx => hu x (Finset.mem_union_left _ hx)) ha
    have hbinv : (b : K)⁻¹ ∈ u.toValuationSubring := hu _ (by simp)
    have hmem : (⟨valuationCenter u.toValuationSubring A hsub, inferInstance⟩ :
        PrimeSpectrum A) ∈ (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum A)) := by
      rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
      change b ∉ valuationCenter _ _ _
      rw [mem_valuationCenter_iff']
      intro hlt
      have hle : u.toValuationSubring.valuation (b : K)⁻¹ ≤ 1 :=
        (u.toValuationSubring.valuation_le_one_iff _).mpr hbinv
      have h3 := mul_lt_one_of_lt_of_le hlt hle
      rw [← map_mul, mul_inv_cancel₀ hb, map_one] at h3
      exact lt_irrefl _ h3
    exact ⟨hsub, hbG hmem⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have hxA : x ∈ A := hs ▸ Algebra.subset_adjoin hx
      exact h ⟨x, hxA⟩
    · rw [Finset.mem_singleton] at hx
      subst hx
      have hle : w.toValuationSubring.valuation (b : K) ≤ 1 :=
        (w.toValuationSubring.valuation_le_one_iff _).mpr (h b)
      have heq : w.toValuationSubring.valuation (b : K) = 1 := le_antisymm hle (not_lt.mp hb1)
      rw [← w.toValuationSubring.valuation_le_one_iff, map_inv₀, heq, inv_one]

/-- Proposition 4.1.2 in the affine form. Assume that each valuation of `K/k` has local
uniformization, and that the regular locus of each affine model of `K/k` is open. Then there are
finitely many affine models `A_1, ..., A_m` of `K/k` such that each valuation of `K/k` has a
regular center on some `Spec A_i`. -/
theorem exists_finset_affineModel_regularCenter
    (hLU : ∀ V : ValuationSubring K, (∀ c : k, algebraMap k K c ∈ V) →
      HasLocalUniformization k V)
    (hopen : ∀ A : Subalgebra k K, IsAffineModel A →
      IsOpen {P : PrimeSpectrum A | IsRegularLocalRing (Localization.AtPrime P.asIdeal)}) :
    ∃ t : Finset (Subalgebra k K), (∀ A ∈ t, IsAffineModel A) ∧
      ∀ V : ValuationSubring K, (∀ c : k, algebraMap k K c ∈ V) →
        ∃ A ∈ t, ∃ h : ∀ a : A, (a : K) ∈ V,
          IsRegularLocalRing (Localization.AtPrime (valuationCenter V A h)) := by
  classical
  have hex : ∀ w : ZariskiRiemann k K, ∃ A : Subalgebra k K, IsAffineModel A ∧
      w ∈ regularCenterSet A := by
    intro w
    obtain ⟨A, h, hA, -, hreg⟩ :=
      hLU w.toValuationSubring (fun c => w.algebraMap_mem c) ∅ (by simp)
    exact ⟨A, hA, h, hreg⟩
  choose B hB hwB using hex
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun w => regularCenterSet (B w))
    (fun w => isOpen_setOf_regularCenter (B w) (hB w).1 (hopen (B w) (hB w)))
    (fun w _ => Set.mem_iUnion.mpr ⟨w, hwB w⟩)
  refine ⟨t.image B, fun A hA => ?_, fun V hV => ?_⟩
  · obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hA
    exact hB w
  · obtain ⟨w, hw, h, hreg⟩ := by
      simpa only [Set.mem_iUnion] using ht (Set.mem_univ (ZariskiRiemann.mk V hV))
    exact ⟨B w, Finset.mem_image_of_mem B hw, h, hreg⟩

end Cover

end Singularity
