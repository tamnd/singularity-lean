/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.MultiplicityRegular
import Mathlib.RingTheory.KrullDimension.Regular

/-!
# The multiplicity of a hypersurface

This file proves Volume 1, Proposition 3.3.15 of the handbook in part.

Let `(S, 𝔪)` be a regular local ring of dimension `n + 1`, let `d ≥ 1` and let `f ∈ 𝔪^d`. Put
`R = S/(f)`. The handbook indexes the dimension as `n`; here it is `n + 1`.

## What is proved

* `Singularity.Algebra.ringKrullDim_quotient_span_singleton_of_isRegularLocalRing`: if `f ∈ 𝔪`
  and `f ≠ 0`, then `dim S/(f) = n`.
* `Singularity.Algebra.length_quotient_eq_add_of_colon`: the exact sequence
  `0 → S/(I : f) → S/I → S/((f) + I) → 0` gives `ℓ(S/I) = ℓ(S/(I : f)) + ℓ(S/((f) + I))`.
* `Singularity.Algebra.hilbertSamuel_quotient_span_singleton_eq_length`:
  `χ_R(N) = ℓ_S(S/((f) + 𝔪^N))`.
* `Singularity.Algebra.hilbertSamuel_hypersurface_of_le`: `χ_R(N) = (N + n).choose (n + 1)`
  for `N ≤ d`. This needs no further hypothesis.
* `Singularity.Algebra.hilbertSamuel_hypersurface_ge`: the lower bound
  `χ_R(N + d) + (N + n).choose (n + 1) ≥ (N + d + n).choose (n + 1)` for each `N`, with no
  further hypothesis. It comes from `𝔪^N ⊆ (𝔪^(N+d) : f)`.
* `Singularity.Algebra.hilbertSamuel_hypersurface_add`: if `(𝔪^(N+d) : f) = 𝔪^N` for each `N`,
  then `χ_R(N + d) = (N + d + n).choose (n + 1) - (N + n).choose (n + 1)`.
* `Singularity.Algebra.fwdDiff_iter_hypersurface_formula`: the combinatorial step. The `n`-th
  forward difference of `N ↦ (N + d + n).choose (n + 1) - (N + n).choose (n + 1)` is the
  constant `d`.
* `Singularity.Algebra.samuelMultiplicity_hypersurface`: under the same colon hypothesis,
  `e_n(𝔪R, R) = d`.

* `Singularity.Algebra.mem_maximalIdeal_pow_of_mul_mem_of_notMem_sq`: for `f ∈ 𝔪 \ 𝔪²` the
  colon equality `(𝔪^(N+1) : f) = 𝔪^N` holds. Thus
  `Singularity.Algebra.hilbertSamuel_and_samuelMultiplicity_of_notMem_sq` proves the whole
  proposition for `d = 1`, with `e_n(𝔪R, R) = 1`.

## What is not proved

The colon equality `(𝔪^(N+d) : f) = 𝔪^N` for `f ∈ 𝔪^d \ 𝔪^(d+1)` is taken as the hypothesis
`hcolon` in the last two results. The handbook proves it from the fact that `gr_𝔪(S)` is a
domain (Proposition 1.10.1): the initial form of `f g` is the product of the initial forms. That
fact is not in the project library nor in Mathlib. Note that `hcolon` with `N = 1` already
forces `f ∉ 𝔪^(d+1)`. Without `hcolon`, only the values `χ_R(N)` for `N ≤ d` and the lower bound
for `N ≥ d` are proved, except in the case `d = 1`, which is complete.
-/

universe u

namespace Singularity.Algebra

open Module Filter fwdDiff IsLocalRing Ideal

section Length

variable {S : Type u} [CommRing S]

/-- Let `K = (I : f)`, that is `f u ∈ I ↔ u ∈ K`. The multiplication by `f` gives an exact
sequence `0 → S/K → S/I → S/((f) + I) → 0`, thus `ℓ(S/I) = ℓ(S/K) + ℓ(S/((f) + I))`. -/
theorem length_quotient_eq_add_of_colon {f : S} {I K : Ideal S}
    (hK : ∀ u, f * u ∈ I ↔ u ∈ K) :
    length S (S ⧸ I) = length S (S ⧸ K) + length S (S ⧸ span {f} ⊔ I) := by
  have hf : K ≤ Submodule.comap (LinearMap.mulLeft S f) I := fun u hu => by
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
    exact (hK u).mpr hu
  let φ : (S ⧸ K) →ₗ[S] S ⧸ I := Submodule.mapQ _ _ (LinearMap.mulLeft S f) hf
  let g : (S ⧸ I) →ₗ[S] S ⧸ span {f} ⊔ I :=
    Submodule.mapQ _ _ LinearMap.id (le_sup_right : I ≤ span {f} ⊔ I)
  refine length_eq_add_of_exact φ g ?_ ?_ ?_
  · intro x y hxy
    induction x using Submodule.Quotient.induction_on with | _ x => ?_
    induction y using Submodule.Quotient.induction_on with | _ y => ?_
    simp only [φ, Submodule.mapQ_apply, LinearMap.mulLeft_apply, Submodule.Quotient.eq]
      at hxy ⊢
    exact (hK _).mp (by rw [mul_sub]; exact hxy)
  · intro y
    induction y using Submodule.Quotient.induction_on with | _ y => ?_
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  · intro y
    induction y using Submodule.Quotient.induction_on with | _ y => ?_
    simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hy
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨c, rfl⟩ := mem_span_singleton'.mp hp
      refine ⟨Submodule.Quotient.mk c, ?_⟩
      simp only [φ, Submodule.mapQ_apply, LinearMap.mulLeft_apply, Submodule.Quotient.eq]
      rw [show f * c - (c * f + q) = -q by ring]
      exact neg_mem hq
    · rintro ⟨x, hx⟩
      induction x using Submodule.Quotient.induction_on with | _ x => ?_
      simp only [φ, Submodule.mapQ_apply, LinearMap.mulLeft_apply, Submodule.Quotient.eq] at hx
      rw [show y = f * x - (f * x - y) by ring]
      exact sub_mem (mem_sup_left (mem_span_singleton.mpr (dvd_mul_right f x)))
        (mem_sup_right hx)

variable [IsLocalRing S]

/-- The Hilbert-Samuel function of `R = S/(f)` is `χ_R(N) = ℓ_S(S/((f) + 𝔪^N))`. -/
theorem hilbertSamuel_quotient_span_singleton_eq_length (f : S)
    [IsLocalRing (S ⧸ span {f})] (N : ℕ) :
    hilbertSamuel (maximalIdeal (S ⧸ span {f})) (S ⧸ span {f}) N =
      length S (S ⧸ span {f} ⊔ maximalIdeal S ^ N) := by
  rw [length_quotient_span_singleton_sup, Ideal.map_pow, ← maximalIdeal_quotient_eq_map,
    hilbertSamuel_self_eq]

end Length

section Hypersurface

variable {S : Type u} [CommRing S] [IsRegularLocalRing S]

/-- **The dimension of a hypersurface.** Let `S` be a regular local ring of dimension `n + 1`,
and let `f ∈ 𝔪` with `f ≠ 0`. Then `dim S/(f) = n`. -/
theorem ringKrullDim_quotient_span_singleton_of_isRegularLocalRing {n : ℕ}
    (hS : ringKrullDim S = (n + 1 : ℕ)) {f : S} (hm : f ∈ maximalIdeal S) (h0 : f ≠ 0) :
    ringKrullDim (S ⧸ span {f}) = n := by
  have : IsDomain S := isDomain_of_isRegularLocalRing S
  have := isLocalRing_quotient_of_le_maximalIdeal ((span_singleton_le_iff_mem _).mpr hm)
  have hdim : ringKrullDim (S ⧸ span {f}) + 1 = ringKrullDim S :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero h0) hm
  obtain ⟨m, hm'⟩ := exists_ringKrullDim_eq_natCast (S ⧸ span {f})
  rw [hm', hS] at hdim
  rw [hm']
  have h : m + 1 = n + 1 := by exact_mod_cast hdim
  exact_mod_cast (Nat.add_right_cancel h)

/-- Let `S` be a regular local ring of dimension `n + 1`, and let `f ∈ 𝔪^d`. Then
`χ_R(N) = (N + n).choose (n + 1)` for `N ≤ d`, where `R = S/(f)`. -/
theorem hilbertSamuel_hypersurface_of_le {n d : ℕ} (hS : ringKrullDim S = (n + 1 : ℕ)) {f : S}
    (hf : f ∈ maximalIdeal S ^ d) [IsLocalRing (S ⧸ span {f})] {N : ℕ} (hN : N ≤ d) :
    hilbertSamuel (maximalIdeal (S ⧸ span {f})) (S ⧸ span {f}) N = (N + n).choose (n + 1) := by
  have hfN : span {f} ≤ maximalIdeal S ^ N :=
    (span_singleton_le_iff_mem _).mpr (Ideal.pow_le_pow_right hN hf)
  rw [hilbertSamuel_quotient_span_singleton_eq_length, sup_eq_right.mpr hfN,
    ← hilbertSamuel_self_eq, hilbertSamuel_eq_choose hS]

/-- The exact sequence for the colon ideal `(𝔪^(N+d) : f)` in terms of lengths. -/
theorem length_pow_add_eq (f : S) (N d : ℕ) [IsLocalRing (S ⧸ span {f})] :
    length S (S ⧸ maximalIdeal S ^ (N + d)) =
      length S (S ⧸ Submodule.comap (LinearMap.mulLeft S f) (maximalIdeal S ^ (N + d))) +
        hilbertSamuel (maximalIdeal (S ⧸ span {f})) (S ⧸ span {f}) (N + d) := by
  rw [hilbertSamuel_quotient_span_singleton_eq_length]
  exact length_quotient_eq_add_of_colon fun u => by
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]

/-- **A lower bound for `χ_R`.** Let `S` be a regular local ring of dimension `n + 1`, and let
`f ∈ 𝔪^d`. Then `(N + d + n).choose (n + 1) ≤ χ_R(N + d) + (N + n).choose (n + 1)`. -/
theorem hilbertSamuel_hypersurface_ge {n d : ℕ} (hS : ringKrullDim S = (n + 1 : ℕ)) {f : S}
    (hf : f ∈ maximalIdeal S ^ d) [IsLocalRing (S ⧸ span {f})] (N : ℕ) :
    (((N + d + n).choose (n + 1) : ℕ) : ℕ∞) ≤
      hilbertSamuel (maximalIdeal (S ⧸ span {f})) (S ⧸ span {f}) (N + d) +
        (N + n).choose (n + 1) := by
  have h := length_pow_add_eq f N d
  rw [← hilbertSamuel_self_eq, hilbertSamuel_eq_choose hS] at h
  rw [h, add_comm (length S _), ← hilbertSamuel_eq_choose hS N,
    hilbertSamuel_self_eq (maximalIdeal S) N]
  have hle : maximalIdeal S ^ N ≤
      Submodule.comap (LinearMap.mulLeft S f) (maximalIdeal S ^ (N + d)) := fun u hu => by
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply, add_comm, pow_add]
    exact Ideal.mul_mem_mul hf hu
  exact add_le_add le_rfl
    (Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle))

/-- **The Hilbert-Samuel function of a hypersurface.** Let `S` be a regular local ring of
dimension `n + 1`, and let `f ∈ 𝔪^d` with `(𝔪^(N+d) : f) = 𝔪^N` for each `N`. Then
`χ_R(N + d) = (N + d + n).choose (n + 1) - (N + n).choose (n + 1)`, where `R = S/(f)`. -/
theorem hilbertSamuel_hypersurface_add {n d : ℕ} (hS : ringKrullDim S = (n + 1 : ℕ)) {f : S}
    (hf : f ∈ maximalIdeal S ^ d)
    (hcolon : ∀ N g, f * g ∈ maximalIdeal S ^ (N + d) → g ∈ maximalIdeal S ^ N)
    [IsLocalRing (S ⧸ span {f})] (N : ℕ) :
    hilbertSamuel (maximalIdeal (S ⧸ span {f})) (S ⧸ span {f}) (N + d) =
      (((N + d + n).choose (n + 1) - (N + n).choose (n + 1) : ℕ) : ℕ∞) := by
  have hK : Submodule.comap (LinearMap.mulLeft S f) (maximalIdeal S ^ (N + d)) =
      maximalIdeal S ^ N := by
    ext u
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
    refine ⟨hcolon N u, fun hu => ?_⟩
    rw [add_comm, pow_add]
    exact Ideal.mul_mem_mul hf hu
  have h := length_pow_add_eq f N d
  rw [hK, ← hilbertSamuel_self_eq, ← hilbertSamuel_self_eq, hilbertSamuel_eq_choose hS,
    hilbertSamuel_eq_choose hS] at h
  set x := hilbertSamuel (maximalIdeal (S ⧸ span {f})) (S ⧸ span {f}) (N + d)
  have hx : x ≠ ⊤ := by
    intro hx
    rw [hx, add_top] at h
    exact ENat.natCast_ne_top _ h
  lift x to ℕ using hx with m
  have h' : (N + d + n).choose (n + 1) = (N + n).choose (n + 1) + m := by exact_mod_cast h
  rw [h', Nat.add_sub_cancel_left]

end Hypersurface

section Combinatorics

/-- The forward difference commutes with a shift of the variable. -/
theorem fwdDiff_iter_apply_add (f : ℕ → ℤ) (c n M : ℕ) :
    Δ_[1]^[n] f (M + c) = Δ_[1]^[n] (fun k => f (k + c)) M := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    have h : (fun k => Δ_[1] f (k + c)) = Δ_[1] fun k => f (k + c) := by
      funext k
      simp only [fwdDiff]
      rw [show k + 1 + c = k + c + 1 by omega]
    rw [h]

/-- **The combinatorial step.** The `n`-th forward difference of
`N ↦ (N + d + n).choose (n + 1) - (N + n).choose (n + 1)` is the constant `d`. -/
theorem fwdDiff_iter_hypersurface_formula (n d M : ℕ) :
    Δ_[1]^[n] (fun N : ℕ => ((N + d + n).choose (n + 1) : ℤ) - (N + n).choose (n + 1)) M =
      d := by
  have h : (fun N : ℕ => ((N + d + n).choose (n + 1) : ℤ) - (N + n).choose (n + 1)) =
      (fun N : ℕ => ((N + (d + n)).choose (1 + n) : ℤ)) -
        fun N : ℕ => ((N + n).choose (1 + n) : ℤ) := by
    funext N
    simp only [Pi.sub_apply, add_assoc, add_comm 1 n]
  rw [h, fwdDiff_iter_sub, fwdDiff_iter_choose_add, fwdDiff_iter_choose_add]
  simp only [Pi.sub_apply, Nat.choose_one_right]
  push_cast
  ring

end Combinatorics

section Multiplicity

variable {S : Type u} [CommRing S] [IsRegularLocalRing S]

/-- **The multiplicity of a hypersurface** (Volume 1, Proposition 3.3.15 of the handbook, under
the colon hypothesis). Let `S` be a regular local ring of dimension `n + 1`, and let
`f ∈ 𝔪^d` with `(𝔪^(N+d) : f) = 𝔪^N` for each `N`. Then `e_n(𝔪R, R) = d`, where
`R = S/(f)`. -/
theorem samuelMultiplicity_hypersurface {n d : ℕ} (hS : ringKrullDim S = (n + 1 : ℕ)) {f : S}
    (hf : f ∈ maximalIdeal S ^ d)
    (hcolon : ∀ N g, f * g ∈ maximalIdeal S ^ (N + d) → g ∈ maximalIdeal S ^ N)
    [IsLocalRing (S ⧸ span {f})] :
    samuelMultiplicity (maximalIdeal (S ⧸ span {f})) (S ⧸ span {f}) n = d := by
  refine samuelMultiplicity_eq_of_eventually ((eventually_ge_atTop d).mono fun M hM => ?_)
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le' hM
  rw [fwdDiff_iter_apply_add]
  have h : (fun k => hilbertSamuelInt (maximalIdeal (S ⧸ span {f})) (S ⧸ span {f}) (k + d)) =
      fun N : ℕ => ((N + d + n).choose (n + 1) : ℤ) - (N + n).choose (n + 1) := by
    funext N
    rw [hilbertSamuelInt, hilbertSamuel_hypersurface_add hS hf hcolon, ENat.toNat_natCast,
      Nat.cast_sub (Nat.choose_le_choose _ (by omega))]
  rw [h, fwdDiff_iter_hypersurface_formula]

end Multiplicity

section Parameter

open RingTheory.Sequence

variable {S : Type u} [CommRing S] [IsRegularLocalRing S]

/-- **The colon ideal for a regular parameter.** Let `S` be a regular local ring and let
`f ∈ 𝔪 \ 𝔪²`. Then `(𝔪^(N+1) : f) = 𝔪^N`. This is the hypothesis `hcolon` for `d = 1`. -/
theorem mem_maximalIdeal_pow_of_mul_mem_of_notMem_sq {f : S} (hm : f ∈ maximalIdeal S)
    (h2 : f ∉ maximalIdeal S ^ 2) (N : ℕ) {g : S} (hg : f * g ∈ maximalIdeal S ^ (N + 1)) :
    g ∈ maximalIdeal S ^ N := by
  have : IsDomain S := isDomain_of_isRegularLocalRing S
  have := isLocalRing_quotient_of_le_maximalIdeal ((span_singleton_le_iff_mem _).mpr hm)
  have := (quotient_span_singleton hm h2).1
  obtain ⟨rs', -, hrs', hreg'⟩ := exists_isRegular_ofList_eq_maximalIdeal (S ⧸ span {f})
  let rs := rs'.map
    (Function.surjInv (f := Ideal.Quotient.mk (span {f})) Ideal.Quotient.mk_surjective)
  have hmap : rs.map (Ideal.Quotient.mk (span {f})) = rs' := by
    simp only [rs, List.map_map]
    conv_rhs => rw [← List.map_id rs']
    exact List.map_congr_left fun x _ => Function.surjInv_eq _ x
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact h2 (zero_mem _)
  have hreg : IsWeaklyRegular S (f :: rs) := by
    rw [isWeaklyRegular_cons_iff, (quotSMulTopEquivQuotSpan f).isWeaklyRegular_congr,
      ← isWeaklyRegular_map_algebraMap_iff (S ⧸ span {f}) (S ⧸ span {f}) rs,
      Ideal.Quotient.algebraMap_eq, hmap]
    exact ⟨fun x y h => mul_left_cancel₀ hf0 h, hreg'.toIsWeaklyRegular⟩
  have hofl : ofList (f :: rs) = maximalIdeal S := by
    rw [ofList_cons]
    have h1 : (ofList rs).map (Ideal.Quotient.mk (span {f})) =
        (maximalIdeal S).map (Ideal.Quotient.mk (span {f})) := by
      rw [map_ofList, hmap, hrs', maximalIdeal_quotient_eq_map]
    have h3 := congrArg (Ideal.comap (Ideal.Quotient.mk (span {f}))) h1
    rw [comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, mk_ker] at h3
    rw [sup_comm, h3]
    exact sup_eq_left.mpr ((span_singleton_le_iff_mem _).mpr hm)
  exact mem_maximalIdeal_pow_of_mul_mem hreg hofl hg

/-- **Proposition 3.3.15 for `d = 1`.** Let `S` be a regular local ring of dimension `n + 1`
and let `f ∈ 𝔪 \ 𝔪²`. Then `χ_R(N + 1) = (N + 1 + n).choose (n + 1) - (N + n).choose (n + 1)`
and `e_n(𝔪R, R) = 1`, where `R = S/(f)`. -/
theorem hilbertSamuel_and_samuelMultiplicity_of_notMem_sq {n : ℕ}
    (hS : ringKrullDim S = (n + 1 : ℕ)) {f : S} (hm : f ∈ maximalIdeal S)
    (h2 : f ∉ maximalIdeal S ^ 2) [IsLocalRing (S ⧸ span {f})] :
    (∀ N, hilbertSamuel (maximalIdeal (S ⧸ span {f})) (S ⧸ span {f}) (N + 1) =
      (((N + 1 + n).choose (n + 1) - (N + n).choose (n + 1) : ℕ) : ℕ∞)) ∧
    samuelMultiplicity (maximalIdeal (S ⧸ span {f})) (S ⧸ span {f}) n = 1 := by
  have hf : f ∈ maximalIdeal S ^ 1 := by rwa [pow_one]
  have hcolon : ∀ N g, f * g ∈ maximalIdeal S ^ (N + 1) → g ∈ maximalIdeal S ^ N :=
    fun N _ h => mem_maximalIdeal_pow_of_mul_mem_of_notMem_sq hm h2 N h
  exact ⟨hilbertSamuel_hypersurface_add hS hf hcolon,
    samuelMultiplicity_hypersurface hS hf hcolon⟩

end Parameter

end Singularity.Algebra
