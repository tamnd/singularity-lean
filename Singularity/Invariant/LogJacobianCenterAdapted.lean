/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianCenterNonincrease
import Singularity.Invariant.LogJacobianCoordinates

/-!
# `ρ` does not go up under the blowup of a centre in adapted coordinates

Theorem 3.16 of research note 03 says that `ρ` does not go up under the blowup of a regular
centre `C` that is permissible for `g` and has normal crossings with the divisor
`E = V(∏_{i ∈ Δ} x_i)`. The library proves this for a coordinate centre `C = V(x_i : i ∈ S)`
(`logJacobianOrder_cleanPart_le_center`). This file proves it for each centre that is a coordinate
centre in adapted coordinates of `k[x]` that fix the origin.

Let `φ` and `ψ` be inverse endomorphisms of `k[x]` with `φ(x_l) = c_l x_l` for each `l ∈ Δ`, and
with `φ(x_i)(0) = ψ(x_i)(0) = 0` for each `i`. Let `y_i = ψ(x_i)`. These are new coordinates that
are adapted to `E`, and the centre is `C = V(y_i : i ∈ S)`, with ideal `J = ψ((x_i : i ∈ S))`.
Let `F` be a representative of `g` in the coordinates `y`: a clean polynomial with
`Θ(F) = φ(Θ(g))`, for example `F = φ(g)` (`logJacobianOrder_cleanPart_le_center_map_of_adapted`).
The chart of the blowup of `C` is `centerChart S j t ∘ φ`. Let `centerChart S j t F = x_j^p g'`.

The conditions (H1) and (H2) of the handbook are stated in the coordinates of `g`, with the
ideal `J` of the centre.

* (H1) Each element of `Θ(g)` is `x^r` times an element of `J^ρ`.
* (H2) Each element of `Θ_C(g)` is `x^r` times an element of `J^(ρ+1)`, or `Θ_C(g)` has an
  element `x^r h₀` with `ord h₀ = ρ`.

Here `Θ_C(g) = ψ(Θ_C(F))` is the ideal `logJacobianCenter Δ S F` of the coordinates `y`, carried
back by `ψ`. Then the clean part `g'_c` of `g'` is not `0`, and `ρ(g'_c) ≤ ρ(g)` for the new
divisor `centerDivisor Δ S j t` (`logJacobianOrder_cleanPart_le_center_of_adapted`).

The proof. An adapted change of coordinates that fixes the origin keeps `r` and `ρ`
(`divisorExponent_cleanPart_eq_of_adapted`, `logJacobianOrder_cleanPart_eq_of_adapted`). It maps
`x^r` to `c x^r` with `c ≠ 0` (`exists_map_monomial_eq_of_adapted`), and it maps `J` to
`(x_i : i ∈ S)`. So (H1) and (H2) for `g` give (H1) and (H2) for `F`, and the theorem for the
coordinate centre gives the result.

The centres that are coordinate centres only in coordinates of the power series ring, and the
definition of `Θ_C(g)` by the derivations that are tangent to `C` and `E`, are not covered.

## Main results

* `exists_map_monomial_eq_of_adapted`: `φ(x^s) = c x^s` with `c ≠ 0`.
* `map_span_monomial_eq_of_adapted`: `φ((x^s)) = (x^s)`.
* `logJacobianOrder_cleanPart_le_center_of_adapted`: Theorem 3.16 for a centre that is a
  coordinate centre in adapted coordinates of `k[x]`.
* `logJacobianOrder_cleanPart_le_center_map_of_adapted`: the same result for `F = φ(g)`.

## References

* Research note 03, Section 3.6: Theorem 3.16.
* Volume 7, Section 3.4 of the handbook, Theorem 3.4.5.
-/

open MvPolynomial

namespace Singularity

section Monomial

variable {σ k : Type*} [Field k] {Δ : Finset σ}
  {φ ψ : MvPolynomial σ k →ₐ[k] MvPolynomial σ k}

/-- An adapted change of coordinates maps a monomial in the coordinates of `Δ` to a nonzero
multiple of itself: `φ(x^s) = c x^s` with `c ≠ 0`, if `s` is supported in `Δ`. -/
theorem exists_map_monomial_eq_of_adapted (hψφ : ∀ h, ψ (φ h) = h)
    (hφ : ∀ l ∈ Δ, ∃ c : k, φ (X l) = C c * X l) (s : σ →₀ ℕ) (hs : ∀ i, i ∉ Δ → s i = 0) :
    ∃ c : k, c ≠ 0 ∧ φ (monomial s 1) = C c * monomial s 1 := by
  induction s using Finsupp.induction with
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | single_add a n f ha hn ih =>
    have hsum : ∀ i, i ∉ Δ → Finsupp.single a n i = 0 ∧ f i = 0 := fun i hi =>
      Nat.add_eq_zero_iff.mp (by rw [← Finsupp.add_apply]; exact hs i hi)
    obtain ⟨c, hc0, hc⟩ := ih fun i hi => (hsum i hi).2
    have haΔ : a ∈ Δ := by
      by_contra h
      have h1 := (hsum a h).1
      rw [Finsupp.single_eq_same] at h1
      exact hn h1
    obtain ⟨b, hb⟩ := hφ a haΔ
    have hb0 : b ≠ 0 := by
      intro h0
      apply X_ne_zero (R := k) a
      rw [← hψφ (X a), hb, h0, map_zero, zero_mul, map_zero]
    refine ⟨b ^ n * c, mul_ne_zero (pow_ne_zero n hb0) hc0, ?_⟩
    rw [← mul_one (1 : k), ← monomial_mul_monomial, ← X_pow_eq_monomial, map_mul φ, hc, map_pow, hb,
      mul_pow, map_mul C, map_pow C]
    ring

/-- An adapted change of coordinates keeps the ideal of a monomial in the coordinates of `Δ`:
`φ((x^s)) = (x^s)`. -/
theorem map_span_monomial_eq_of_adapted (hψφ : ∀ h, ψ (φ h) = h)
    (hφ : ∀ l ∈ Δ, ∃ c : k, φ (X l) = C c * X l) (s : σ →₀ ℕ) (hs : ∀ i, i ∉ Δ → s i = 0) :
    Ideal.map φ (Ideal.span {monomial s (1 : k)}) = Ideal.span {monomial s (1 : k)} := by
  obtain ⟨c, hc0, hc⟩ := exists_map_monomial_eq_of_adapted hψφ hφ s hs
  rw [Ideal.map_span, Set.image_singleton, hc]
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_singleton_le_span_singleton]
    exact Dvd.intro_left _ rfl
  · rw [Ideal.span_singleton_le_span_singleton]
    refine ⟨C c⁻¹, ?_⟩
    rw [mul_comm (C c), mul_assoc, ← C_mul, mul_inv_cancel₀ hc0, C_1, mul_one]

/-- An endomorphism with an inverse that fixes the origin keeps the order of polynomials. -/
theorem ord_map_eq_of_inverse (hψφ : ∀ h, ψ (φ h) = h)
    (hφ : ∀ i, constantCoeff (φ (X i)) = 0) (hψ : ∀ i, constantCoeff (ψ (X i)) = 0)
    (q : MvPolynomial σ k) : ord (φ q) = ord q := by
  have h := idealOrd_map_eq_of_inverse hψφ hφ hψ (Ideal.span {q})
  rwa [Ideal.map_span, Set.image_singleton, idealOrd_span_singleton,
    idealOrd_span_singleton] at h

end Monomial

section Center

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] (p : ℕ) [CharP k p]
  {Δ S : Finset σ} {j : σ} {t : σ → k} {φ ψ : MvPolynomial σ k →ₐ[k] MvPolynomial σ k}
  {g F g' : MvPolynomial σ k}

/-- The set of the `x^r q` with `q ∈ I` is the ideal `(x^r) I`. -/
theorem forall_mem_exists_eq_monomial_mul_iff (s : σ →₀ ℕ) (I L : Ideal (MvPolynomial σ k)) :
    (∀ f ∈ L, ∃ q ∈ I, f = monomial s 1 * q) ↔ L ≤ Ideal.span {monomial s (1 : k)} * I := by
  constructor
  · intro H f hf
    obtain ⟨q, hq, rfl⟩ := H f hf
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hq
  · intro H f hf
    obtain ⟨q, hq, e⟩ := Ideal.mem_span_singleton_mul.mp (H hf)
    exact ⟨q, hq, e.symm⟩

/-- The transport of the conditions (H1) and (H2) to the new coordinates: if
`L ⊆ (x^s) ψ(I)^n`, then `φ(L) ⊆ (x^s) I^n`. -/
theorem map_le_span_monomial_mul_of_adapted (hψφ : ∀ h, ψ (φ h) = h) (hφψ : ∀ h, φ (ψ h) = h)
    (hφ : ∀ l ∈ Δ, ∃ c : k, φ (X l) = C c * X l) {s : σ →₀ ℕ} (hs : ∀ i, i ∉ Δ → s i = 0)
    (I L : Ideal (MvPolynomial σ k)) (n : ℕ)
    (hL : L ≤ Ideal.span {monomial s (1 : k)} * Ideal.map ψ I ^ n) :
    Ideal.map φ L ≤ Ideal.span {monomial s (1 : k)} * I ^ n := by
  refine (Ideal.map_mono hL).trans (le_of_eq ?_)
  rw [Ideal.map_mul, Ideal.map_pow, map_map_of_inverse hφψ,
    map_span_monomial_eq_of_adapted hψφ hφ s hs]

/-- **Theorem 3.16 of research note 03 for a centre that is a coordinate centre in adapted
coordinates.** Let `φ` and `ψ` be inverse endomorphisms of `k[x]` that fix the origin, with
`φ(x_l) = c_l x_l` for each `l ∈ Δ`. Let `J = ψ((x_i : i ∈ S))` be the ideal of the centre
`C = V(ψ(x_i) : i ∈ S)`. Let `g ≠ 0` be clean, and let `F` be clean with `Θ(F) = φ(Θ(g))` and
`F ∈ (x_i : i ∈ S)^p`. Let `j ∈ S` and `centerChart S j t F = x_j^p g'`. Let `r` be the divisor
exponent of `g` and `ρ = logJacobianOrder Δ g`. Assume the conditions of the handbook.

* (H1) Each element of `Θ(g)` is `x^r` times an element of `J^ρ`.
* (H2) Each element of `Θ_C(g) = ψ(Θ_C(F))` is `x^r` times an element of `J^(ρ+1)`, or `Θ_C(g)`
  has an element `x^r h₀` with `ord h₀ = ρ`.

Then the clean part `g'_c` of `g'` is not `0`, and `ρ(g'_c) ≤ ρ(g)` for the new divisor
`centerDivisor Δ S j t`. -/
theorem logJacobianOrder_cleanPart_le_center_of_adapted (hψφ : ∀ h, ψ (φ h) = h)
    (hφψ : ∀ h, φ (ψ h) = h) (hφ : ∀ l ∈ Δ, ∃ c : k, φ (X l) = C c * X l)
    (h0φ : ∀ i, constantCoeff (φ (X i)) = 0) (h0ψ : ∀ i, constantCoeff (ψ (X i)) = 0)
    (hg : g ≠ 0) (hc : IsClean p g) (hF : logJacobian Δ F = Ideal.map φ (logJacobian Δ g))
    (hcF : IsClean p F) (hj : j ∈ S) (hFS : F ∈ Ideal.span (X '' (S : Set σ)) ^ p)
    (h : centerChart S j t F = X j ^ p * g') {ρ : ℕ} (hρ : logJacobianOrder Δ g = ρ)
    (H1 : ∀ f ∈ logJacobian Δ g, ∃ q ∈ Ideal.map ψ (Ideal.span (X '' (S : Set σ))) ^ ρ,
      f = monomial (divisorExponent Δ g) 1 * q)
    (H2 : (∀ f ∈ Ideal.map ψ (logJacobianCenter Δ S F),
        ∃ q ∈ Ideal.map ψ (Ideal.span (X '' (S : Set σ))) ^ (ρ + 1),
          f = monomial (divisorExponent Δ g) 1 * q) ∨
      ∃ q, monomial (divisorExponent Δ g) 1 * q ∈ Ideal.map ψ (logJacobianCenter Δ S F) ∧
        ord q = ρ) :
    cleanPart p g' ≠ 0 ∧
      logJacobianOrder (centerDivisor Δ S j t) (cleanPart p g') ≤ logJacobianOrder Δ g := by
  have hr : divisorExponent Δ F = divisorExponent Δ g := by
    have h1 := divisorExponent_cleanPart_eq_of_adapted p hψφ hφ hg hc hF
    rwa [cleanPart_eq_self hcF] at h1
  have hρF : logJacobianOrder Δ F = ρ := by
    have h1 := logJacobianOrder_cleanPart_eq_of_adapted p hψφ hφ h0φ h0ψ hg hc hF
    rwa [cleanPart_eq_self hcF, hρ] at h1
  have hs : ∀ i, i ∉ Δ → divisorExponent Δ g i = 0 := divisorExponent_eq_zero_of_notMem Δ g
  rw [hρ, ← hρF]
  refine logJacobianOrder_cleanPart_le_center p hj hFS h hρF ?_ ?_
  · rw [hr, forall_mem_exists_eq_monomial_mul_iff, hF]
    exact map_le_span_monomial_mul_of_adapted hψφ hφψ hφ hs _ _ ρ
      ((forall_mem_exists_eq_monomial_mul_iff _ _ _).mp H1)
  · rw [hr]
    rcases H2 with H2 | ⟨q, hq, hqρ⟩
    · left
      rw [forall_mem_exists_eq_monomial_mul_iff, ← map_map_of_inverse hφψ (logJacobianCenter Δ S F)]
      exact map_le_span_monomial_mul_of_adapted hψφ hφψ hφ hs _ _ (ρ + 1)
        ((forall_mem_exists_eq_monomial_mul_iff _ _ _).mp H2)
    · right
      obtain ⟨c, hc0, hcm⟩ := exists_map_monomial_eq_of_adapted hψφ hφ _ hs
      refine ⟨C c * φ q, ?_, ?_⟩
      · have h1 := Ideal.mem_map_of_mem φ hq
        rw [map_map_of_inverse hφψ, map_mul, hcm] at h1
        rwa [mul_left_comm, ← mul_assoc]
      · rw [ord_mul, ord_C hc0, zero_add, ord_map_eq_of_inverse hψφ h0φ h0ψ, hqρ]

/-- **Theorem 3.16 of research note 03 for `F = φ(g)`.** Let `φ` and `ψ` be inverse adapted
endomorphisms of `k[x]` that fix the origin, and let `g ≠ 0` be clean with `g ∈ J^p` for the ideal
`J = ψ((x_i : i ∈ S))` of the centre. Let `φ(g)` be clean, let `j ∈ S`, and let
`centerChart S j t (φ(g)) = x_j^p g'`. Under the conditions (H1) and (H2) of
`logJacobianOrder_cleanPart_le_center_of_adapted`, the clean part `g'_c` of `g'` is not `0`, and
`ρ(g'_c) ≤ ρ(g)`. -/
theorem logJacobianOrder_cleanPart_le_center_map_of_adapted [Fintype σ] (hψφ : ∀ h, ψ (φ h) = h)
    (hφψ : ∀ h, φ (ψ h) = h) (hφ : ∀ l ∈ Δ, ∃ c : k, φ (X l) = C c * X l)
    (h0φ : ∀ i, constantCoeff (φ (X i)) = 0) (h0ψ : ∀ i, constantCoeff (ψ (X i)) = 0)
    (hg : g ≠ 0) (hc : IsClean p g) (hcF : IsClean p (φ g)) (hj : j ∈ S)
    (hgS : g ∈ Ideal.map ψ (Ideal.span (X '' (S : Set σ))) ^ p)
    (h : centerChart S j t (φ g) = X j ^ p * g') {ρ : ℕ} (hρ : logJacobianOrder Δ g = ρ)
    (H1 : ∀ f ∈ logJacobian Δ g, ∃ q ∈ Ideal.map ψ (Ideal.span (X '' (S : Set σ))) ^ ρ,
      f = monomial (divisorExponent Δ g) 1 * q)
    (H2 : (∀ f ∈ Ideal.map ψ (logJacobianCenter Δ S (φ g)),
        ∃ q ∈ Ideal.map ψ (Ideal.span (X '' (S : Set σ))) ^ (ρ + 1),
          f = monomial (divisorExponent Δ g) 1 * q) ∨
      ∃ q, monomial (divisorExponent Δ g) 1 * q ∈ Ideal.map ψ (logJacobianCenter Δ S (φ g)) ∧
        ord q = ρ) :
    cleanPart p g' ≠ 0 ∧
      logJacobianOrder (centerDivisor Δ S j t) (cleanPart p g') ≤ logJacobianOrder Δ g := by
  have hFS : φ g ∈ Ideal.span (X '' (S : Set σ)) ^ p := by
    have h1 := Ideal.mem_map_of_mem φ hgS
    rwa [Ideal.map_pow, map_map_of_inverse hφψ] at h1
  exact logJacobianOrder_cleanPart_le_center_of_adapted p hψφ hφψ hφ h0φ h0ψ hg hc
    (map_logJacobian_eq_of_adapted hψφ hφψ hφ g).symm hcF hj hFS h hρ H1 H2

end Center

end Singularity
