/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.BlowupChart
import Singularity.Algebra.HypersurfaceMultiplicity

/-!
# The order function of a regular local ring and the multiplicity of a hypersurface

This file completes the proof of Volume 1, Proposition 3.3.15 of the handbook. It also proves
the equality case of Volume 1, Proposition 3.2.3 (4) for a regular local ring: the order
function is additive.

Let `(S, 𝔪)` be a regular local ring and let `f ∈ 𝔪^d \ 𝔪^(d+1)`. The file
`Singularity.Algebra.HypersurfaceMultiplicity` proves `e(S/(f)) = d` under the colon hypothesis
`(𝔪^(N+d) : f) = 𝔪^N`. Here this hypothesis is proved.

## Main results

* `Singularity.Algebra.mem_pow_of_mul_mem_pow_add_of_span`: the colon statement below, for given
  generators `x₀, ..., x_n` of `𝔪` with `dim S = n + 1`.
* `Singularity.Algebra.mem_maximalIdeal_pow_of_mul_mem_of_notMem_pow_succ`: let `S` be a regular
  local ring and let `f ∈ 𝔪^d \ 𝔪^(d+1)`. If `f g ∈ 𝔪^(N+d)`, then `g ∈ 𝔪^N`.
* `Singularity.Algebra.mul_notMem_maximalIdeal_pow_succ`: if `a ∈ 𝔪^p \ 𝔪^(p+1)` and
  `b ∈ 𝔪^q \ 𝔪^(q+1)`, then `a b ∉ 𝔪^(p+q+1)`. Thus `ord(a b) = ord(a) + ord(b)`.
* `Singularity.Algebra.hilbertSamuel_hypersurface_add_of_notMem`: for `dim S = n + 1` and
  `f ∈ 𝔪^d \ 𝔪^(d+1)`, `χ_R(N + d) = (N + d + n).choose (n + 1) - (N + n).choose (n + 1)`,
  where `R = S/(f)`.
* `Singularity.Algebra.samuelMultiplicity_hypersurface_of_notMem`: under the same hypotheses,
  `e_n(𝔪R, R) = d`. This is Proposition 3.3.15.

## The proof

Let `x₀, ..., x_n` generate `𝔪`. Each element of `𝔪^k` is `P(x)` for a homogeneous polynomial
`P` of degree `k` (`exists_isHomogeneous_aeval_eq`). If `P(x) ∈ 𝔪^(k+1)`, then the coefficients
of `P` are in `𝔪` (`coeff_mem_maximalIdeal_of_aeval_mem_pow`). This is Proposition 1.10.1: the
ring `gr_𝔪(S)` is a polynomial ring over the residue field `κ`.

Write `f = F(x)` with `F` homogeneous of degree `d`. Since `f ∉ 𝔪^(d+1)`, the image `F̄` of `F`
in `κ[T]` is not `0`. We prove `g ∈ 𝔪^N` by induction on `N`. Let `f g ∈ 𝔪^(N+1+d)`. By
induction `g ∈ 𝔪^N`, so `g = G(x)` with `G` homogeneous of degree `N`. Then `(F G)(x) = f g`
is in `𝔪^(d+N+1)`, so `F̄ Ḡ = 0` in `κ[T]`. This ring is a domain, thus `Ḡ = 0`. So the
coefficients of `G` are in `𝔪`, and `g ∈ 𝔪^(N+1)`.

## What is not proved

The isomorphism of graded rings between `gr_𝔪(S)` and a polynomial ring is not stated here. Only
its consequence for the order function is used. The case `d = 0` and the case `dim S = 0` are
included in the colon statement.
-/

universe u

namespace Singularity.Algebra

open Module IsLocalRing Ideal MvPolynomial RingTheory.Sequence

section Order

variable {S : Type u} [CommRing S] [IsRegularLocalRing S]

/-- The colon statement when `𝔪` has the generators `g₀, ..., g_n` and `dim S = n + 1`. -/
theorem mem_pow_of_mul_mem_pow_add_of_span {n : ℕ} (hn : ringKrullDim S = (n + 1 : ℕ))
    {x : Fin (n + 1) → S} (hx : maximalIdeal S = span (Set.range x)) {d : ℕ} {f : S}
    (hf : f ∈ maximalIdeal S ^ d) (hf' : f ∉ maximalIdeal S ^ (d + 1)) :
    ∀ N g, f * g ∈ maximalIdeal S ^ (N + d) → g ∈ maximalIdeal S ^ N := by
  have hxm : ∀ i, x i ∈ maximalIdeal S := fun i => hx ▸ subset_span ⟨i, rfl⟩
  have hcoeff : ∀ {P : MvPolynomial (Fin (n + 1)) S} {k : ℕ}, P.IsHomogeneous k →
      P.map (residue S) = 0 → aeval x P ∈ maximalIdeal S ^ (k + 1) := by
    intro P k hP h0
    have h := aeval_mem_mul_pow hxm hP fun s => by
      have h1 := congrArg (fun Q => Q.coeff s) h0
      simp only [coeff_map] at h1
      exact (residue_eq_zero_iff _).mp (by simpa using h1)
    rwa [← pow_succ'] at h
  obtain ⟨F, hF, rfl⟩ := exists_isHomogeneous_aeval_eq hx hf
  have hF0 : F.map (residue S) ≠ 0 := fun h0 => hf' (hcoeff hF h0)
  intro N
  induction N with
  | zero =>
    intro g _
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ N ih =>
    intro g hg
    have hgN := ih g (Ideal.pow_le_pow_right (by omega) hg)
    obtain ⟨G, hG, rfl⟩ := exists_isHomogeneous_aeval_eq hx hgN
    have hFG : ∀ s, (F * G).coeff s ∈ maximalIdeal S :=
      coeff_mem_maximalIdeal_of_aeval_mem_pow hn hx (hF.mul hG) (by
        rw [map_mul, show d + N + 1 = N + 1 + d by omega]
        exact hg)
    have h1 : (F * G).map (residue S) = 0 := by
      ext s
      rw [coeff_map, (residue_eq_zero_iff _).mpr (hFG s)]
      simp
    rw [map_mul] at h1
    exact hcoeff hG ((mul_eq_zero.mp h1).resolve_left hF0)

/-- **The colon ideal of an element of order `d`.** Let `S` be a regular local ring and let
`f ∈ 𝔪^d \ 𝔪^(d+1)`. If `f g ∈ 𝔪^(N+d)`, then `g ∈ 𝔪^N`. That is, `(𝔪^(N+d) : f) = 𝔪^N`. -/
theorem mem_maximalIdeal_pow_of_mul_mem_of_notMem_pow_succ {d : ℕ} {f : S}
    (hf : f ∈ maximalIdeal S ^ d) (hf' : f ∉ maximalIdeal S ^ (d + 1)) (N : ℕ) {g : S}
    (hg : f * g ∈ maximalIdeal S ^ (N + d)) : g ∈ maximalIdeal S ^ N := by
  obtain ⟨n, hn⟩ := exists_ringKrullDim_eq_natCast S
  obtain ⟨rs, hrl, hrs, -⟩ := exists_isRegular_of_ringKrullDim_eq n S hn
  cases n with
  | zero =>
    have hm : maximalIdeal S = ⊥ := by
      rw [← hrs, List.length_eq_zero_iff.mp hrl, ofList_nil]
    cases d with
    | zero =>
      rw [zero_add, pow_one] at hf'
      obtain ⟨u, rfl⟩ := IsLocalRing.notMem_maximalIdeal.mp hf'
      have h := Ideal.mul_mem_left _ (↑u⁻¹ : S) hg
      rwa [← mul_assoc, Units.inv_mul, one_mul, add_zero] at h
    | succ d =>
      exfalso
      have h : f ∈ maximalIdeal S := Ideal.pow_le_self (by omega) hf
      rw [hm, Ideal.mem_bot] at h
      exact hf' (h ▸ zero_mem _)
  | succ n =>
    let x : Fin (n + 1) → S := fun i => rs.get (Fin.cast hrl.symm i)
    have hx : maximalIdeal S = span (Set.range x) := by
      have hr : Set.range x = {r | r ∈ rs} := by
        ext y
        rw [Set.mem_range, Set.mem_ofPred_eq, List.mem_iff_get]
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨Fin.cast hrl.symm i, rfl⟩
        · rintro ⟨i, rfl⟩
          exact ⟨Fin.cast hrl i, by simp [x]⟩
      rw [hr, ← hrs]
    exact mem_pow_of_mul_mem_pow_add_of_span hn hx hf hf' N g hg

/-- **The order function is additive.** Let `S` be a regular local ring, `a ∈ 𝔪^p \ 𝔪^(p+1)`
and `b ∈ 𝔪^q \ 𝔪^(q+1)`. Then `a b ∉ 𝔪^(p+q+1)`. -/
theorem mul_notMem_maximalIdeal_pow_succ {p q : ℕ} {a b : S} (ha : a ∈ maximalIdeal S ^ p)
    (ha' : a ∉ maximalIdeal S ^ (p + 1)) (hb' : b ∉ maximalIdeal S ^ (q + 1)) :
    a * b ∉ maximalIdeal S ^ (p + q + 1) := fun h =>
  hb' (mem_maximalIdeal_pow_of_mul_mem_of_notMem_pow_succ ha ha' (q + 1)
    (by rwa [show q + 1 + p = p + q + 1 by omega]))

end Order

section Hypersurface

variable {S : Type u} [CommRing S] [IsRegularLocalRing S]

/-- **The Hilbert-Samuel function of a hypersurface.** Let `S` be a regular local ring of
dimension `n + 1` and let `f ∈ 𝔪^d \ 𝔪^(d+1)`. Then
`χ_R(N + d) = (N + d + n).choose (n + 1) - (N + n).choose (n + 1)`, where `R = S/(f)`. -/
theorem hilbertSamuel_hypersurface_add_of_notMem {n d : ℕ} (hS : ringKrullDim S = (n + 1 : ℕ))
    {f : S} (hf : f ∈ maximalIdeal S ^ d) (hf' : f ∉ maximalIdeal S ^ (d + 1))
    [IsLocalRing (S ⧸ span {f})] (N : ℕ) :
    hilbertSamuel (maximalIdeal (S ⧸ span {f})) (S ⧸ span {f}) (N + d) =
      (((N + d + n).choose (n + 1) - (N + n).choose (n + 1) : ℕ) : ℕ∞) :=
  hilbertSamuel_hypersurface_add hS hf
    (fun N _ h => mem_maximalIdeal_pow_of_mul_mem_of_notMem_pow_succ hf hf' N h) N

/-- **The multiplicity of a hypersurface** (Volume 1, Proposition 3.3.15 of the handbook). Let
`S` be a regular local ring of dimension `n + 1` and let `f ∈ 𝔪^d \ 𝔪^(d+1)`. Then
`e_n(𝔪R, R) = d`, where `R = S/(f)`. -/
theorem samuelMultiplicity_hypersurface_of_notMem {n d : ℕ} (hS : ringKrullDim S = (n + 1 : ℕ))
    {f : S} (hf : f ∈ maximalIdeal S ^ d) (hf' : f ∉ maximalIdeal S ^ (d + 1))
    [IsLocalRing (S ⧸ span {f})] :
    samuelMultiplicity (maximalIdeal (S ⧸ span {f})) (S ⧸ span {f}) n = d :=
  samuelMultiplicity_hypersurface hS hf
    (fun N _ h => mem_maximalIdeal_pow_of_mul_mem_of_notMem_pow_succ hf hf' N h)

end Hypersurface

end Singularity.Algebra
