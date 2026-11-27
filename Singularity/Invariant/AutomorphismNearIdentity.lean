/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.DerivativeOrder
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Automorphisms close to the identity

This file proves Volume 2, Proposition 3.2.10 of the handbook for the polynomial ring `K[x_1, ..., x_n]` over a field `K` of characteristic `0`, and the last step of Corollary 3.2.11.

Let `I` and `B` be ideals with `B · D(I) ⊆ I`, and let `φ` be a `K`-algebra automorphism with `φ(x_i) - x_i ∈ B` for each `i`. Then `φ(I) = I`, and `φ(r) - r ∈ B` for each `r`.

The proof is the proof of the handbook. First, `B · D^(a+1)(I) ⊆ D^a(I)` for each `a` (`mul_derivIdeal_iterate_succ_le`), so `B^k · D^k(I) ⊆ I`. The handbook then uses the Taylor formula. Here the Taylor formula is replaced by the polynomial `f(x + t b)` in one more variable `t`. Its derivative in `t` is `∑ b_i (∂_i f)(x + t b)` (`derivative_shiftT`). So the coefficient of `t^k` lies in `B^k · D^k(I)` if `f ∈ I` (`coeff_shiftT_mem`), and the value at `t = 1` is `φ(f)`. The division by `k + 1` uses the characteristic `0`. The polynomial ring is Noetherian, so `φ(I) ⊆ I` gives `φ(I) = I` (`map_ringEquiv_eq_of_le`).

## Main results

* `Singularity.mul_derivIdeal_iterate_succ_le`: the first step of the proof.
* `Singularity.aeval_add_mem_chain`: the Taylor step, for a chain of ideals.
* `Singularity.map_ringEquiv_eq_of_le`: an automorphism `e` of a Noetherian ring with `e(I) ⊆ I` has `e(I) = I`.
* `Singularity.map_algEquiv_eq_of_mul_derivIdeal_le`: Proposition 3.2.10 for polynomials.
* `Singularity.maximalContact_change`: the step of Corollary 3.2.11 after the choice of the coordinates.

## Gaps

The handbook works in the power series ring `K[[x_1, ..., x_n]]`, where more maps are automorphisms. Here the ring is the polynomial ring, so the condition `B ⊆ 𝔪` is not necessary and the closedness of ideals is not used. For Corollary 3.2.11, the choice of the coordinates `h, e_2, ..., x_n` and the condition that `I` is MC-invariant are not in Lean. The theorem takes the automorphism with `φ(x_j) = x_j + c` and the inclusion `B · D(I) ⊆ I` as hypotheses.
-/

open MvPolynomial

namespace Singularity

section Chain

variable {σ R : Type*} [CommRing R]

/-- The first step of the proof of Volume 2, Proposition 3.2.10 of the handbook. If `B · D(J) ⊆ J`, then `B · D(D(J)) ⊆ D(J)`. -/
theorem mul_derivIdeal_derivIdeal_le {J B : Ideal (MvPolynomial σ R)} (h : B * derivIdeal J ≤ J) :
    B * derivIdeal (derivIdeal J) ≤ derivIdeal J := by
  rw [Ideal.mul_le]
  intro b hb s hs
  have hsup : s ∈ derivIdeal J ⊔ Ideal.span {g | ∃ i, ∃ f ∈ derivIdeal J, g = pderiv i f} := hs
  rw [Submodule.mem_sup] at hsup
  obtain ⟨y, hy, z, hz, rfl⟩ := hsup
  clear hs
  rw [mul_add]
  refine add_mem (le_derivIdeal J (h (Ideal.mul_mem_mul hb hy))) ?_
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, f, hf, rfl⟩ := hx
    have h1 : b * pderiv i f = pderiv i (b * f) - pderiv i b * f := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
    rw [h1]
    refine sub_mem (pderiv_mem_derivIdeal (h (Ideal.mul_mem_mul hb hf)) i) ?_
    exact Ideal.mul_mem_left _ _ hf
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hx

/-- If `B · D(I) ⊆ I`, then `B · D^(a+1)(I) ⊆ D^a(I)` for every `a`. -/
theorem mul_derivIdeal_iterate_succ_le {I B : Ideal (MvPolynomial σ R)} (h : B * derivIdeal I ≤ I)
    (a : ℕ) : B * derivIdeal^[a + 1] I ≤ derivIdeal^[a] I := by
  induction a with
  | zero => simpa using h
  | succ a ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [Function.iterate_succ_apply'] at ih
    exact mul_derivIdeal_derivIdeal_le ih

/-- A chain `I 0 ⊆ I 1 ⊆ ...` with `B · I (a+1) ⊆ I a` has `B^k · I (a+k) ⊆ I a`. -/
theorem pow_mul_chain_le {A : Type*} [CommRing A] {I : ℕ → Ideal A} {B : Ideal A}
    (hB : ∀ a, B * I (a + 1) ≤ I a) (k a : ℕ) : B ^ k * I (a + k) ≤ I a := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    calc B ^ (k + 1) * I (a + (k + 1)) = B ^ k * (B * I ((a + k) + 1)) := by
          rw [pow_succ, mul_assoc, Nat.add_assoc]
      _ ≤ B ^ k * I (a + k) := Ideal.mul_mono_right (hB _)
      _ ≤ I a := ih a

end Chain

section Taylor

variable {σ R : Type*} [CommRing R]

/-- The substitution `x_i ↦ x_i + t b_i` into the polynomial ring in `t` over `R[x]`. -/
noncomputable def shiftT (b : σ → MvPolynomial σ R) :
    MvPolynomial σ R →ₐ[R] Polynomial (MvPolynomial σ R) :=
  aeval fun i => Polynomial.C (X i) + Polynomial.C (b i) * Polynomial.X

theorem shiftT_X (b : σ → MvPolynomial σ R) (i : σ) :
    shiftT b (X i) = Polynomial.C (X i) + Polynomial.C (b i) * Polynomial.X := by
  simp [shiftT]

/-- The chain rule for the substitution: `d/dt f(x + t b) = ∑ b_i (∂_i f)(x + t b)`. -/
theorem derivative_shiftT [Fintype σ] (b : σ → MvPolynomial σ R) (f : MvPolynomial σ R) :
    Polynomial.derivative (shiftT b f) =
      ∑ i, Polynomial.C (b i) * shiftT b (pderiv i f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have : shiftT b (C a) = Polynomial.C (C a) := by simp [shiftT, MvPolynomial.algebraMap_eq]
    simp [this]
  | add p q hp hq =>
    simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p n hp =>
    classical
    rw [map_mul, Polynomial.derivative_mul, hp]
    have hX : Polynomial.derivative (shiftT b (X n)) = Polynomial.C (b n) := by
      rw [shiftT_X]; simp
    rw [hX]
    have key : ∀ i, Polynomial.C (b i) * shiftT b (pderiv i (p * X n)) =
        Polynomial.C (b i) * shiftT b (pderiv i p) * shiftT b (X n) +
          (if i = n then Polynomial.C (b n) * shiftT b p else 0) := by
      intro i
      rw [pderiv_mul, map_add, map_mul, map_mul, pderiv_X]
      by_cases h : i = n
      · subst h; simp; ring
      · simp [Ne.symm h, h, mul_assoc]
    rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, Finset.sum_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring

theorem coeff_zero_shiftT (b : σ → MvPolynomial σ R) (f : MvPolynomial σ R) :
    (shiftT b f).coeff 0 = f := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  induction f using MvPolynomial.induction_on with
  | C a => simp [shiftT, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp, shiftT_X]

theorem eval_one_shiftT (b : σ → MvPolynomial σ R) (f : MvPolynomial σ R) :
    (shiftT b f).eval 1 = aeval (fun i => X i + b i) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [shiftT, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp, shiftT_X]

end Taylor

section Main

variable {σ K : Type*} [Field K] [CharZero K]

/-- The coefficient of `t^k` in `f(x + t b)` lies in `B^k · I_(c+k)` if `f ∈ I_c`. Here `(I_a)` is a chain with `∂_i I_a ⊆ I_(a+1)` and each `b_i ∈ B`. -/
theorem coeff_shiftT_mem [Fintype σ] {I : ℕ → Ideal (MvPolynomial σ K)} {B : Ideal (MvPolynomial σ K)}
    (hD : ∀ a f i, f ∈ I a → pderiv i f ∈ I (a + 1)) {b : σ → MvPolynomial σ K} (hb : ∀ i, b i ∈ B)
    (k : ℕ) : ∀ c f, f ∈ I c → (shiftT b f).coeff k ∈ B ^ k * I (c + k) := by
  induction k with
  | zero =>
    intro c f hf
    simpa [coeff_zero_shiftT] using hf
  | succ k ih =>
    intro c f hf
    have hcoeff := congrArg (fun p => Polynomial.coeff p k) (derivative_shiftT b f)
    simp only [Polynomial.coeff_derivative, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul] at hcoeff
    have hsum : (shiftT b f).coeff (k + 1) * ((k : MvPolynomial σ K) + 1) ∈
        B ^ (k + 1) * I (c + (k + 1)) := by
      rw [hcoeff]
      refine sum_mem fun i _ => ?_
      have h1 := ih (c + 1) _ (hD c f i hf)
      rw [show c + 1 + k = c + (k + 1) by omega] at h1
      rw [pow_succ', mul_assoc]
      exact Ideal.mul_mem_mul (hb i) h1
    have hu : ((k : MvPolynomial σ K) + 1) = C ((k : K) + 1) := by simp
    have hne : ((k : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have := Ideal.mul_mem_right (C ((k : K) + 1)⁻¹) _ hsum
    rwa [hu, mul_assoc, ← map_mul, mul_inv_cancel₀ hne, map_one, mul_one] at this

/-- The Taylor step of Volume 2, Proposition 3.2.10 of the handbook, for polynomials. Let `(I_a)` be a chain with `∂_i I_a ⊆ I_(a+1)` and `B · I_(a+1) ⊆ I_a`, and let `b_i ∈ B`. Then `f(x + b) ∈ I_c` for each `f ∈ I_c`. -/
theorem aeval_add_mem_chain [Fintype σ] {I : ℕ → Ideal (MvPolynomial σ K)} {B : Ideal (MvPolynomial σ K)}
    (hD : ∀ a f i, f ∈ I a → pderiv i f ∈ I (a + 1)) (hB : ∀ a, B * I (a + 1) ≤ I a)
    {b : σ → MvPolynomial σ K} (hb : ∀ i, b i ∈ B) {c : ℕ} {f : MvPolynomial σ K} (hf : f ∈ I c) :
    aeval (fun i => X i + b i) f ∈ I c := by
  rw [← eval_one_shiftT, Polynomial.eval_eq_sum, Polynomial.sum_def]
  refine sum_mem fun k _ => ?_
  rw [one_pow, mul_one]
  exact pow_mul_chain_le hB k c (coeff_shiftT_mem hD hb k c f hf)

/-- An automorphism `e` of a Noetherian ring with `e(I) ⊆ I` has `e(I) = I`. -/
theorem map_ringEquiv_eq_of_le {A : Type*} [CommRing A] [IsNoetherianRing A] (e : A ≃+* A)
    {I : Ideal A} (h : I.map e ≤ I) : I.map e = I := by
  let J : ℕ → Ideal A := fun k => Nat.rec I (fun _ J => J.comap e) k
  have hJs : ∀ k, J (k + 1) = (J k).comap e := fun k => rfl
  have h0 : I ≤ I.comap e := Ideal.map_le_iff_le_comap.mp h
  have hmono : ∀ k, J k ≤ J (k + 1) := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih => rw [hJs (k + 1), hJs k]; exact Ideal.comap_mono ih
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian A A)
    ⟨J, monotone_nat_of_le_succ hmono⟩
  have hinj : ∀ X Y : Ideal A, X.comap e = Y.comap e → X = Y := by
    intro X Y hXY
    have hX := Ideal.map_comap_of_surjective e e.surjective X
    have hY := Ideal.map_comap_of_surjective e e.surjective Y
    rw [← hX, ← hY]
    exact congrArg _ hXY
  have hstep : ∀ k, J (k + 1) = J (k + 2) → J k = J (k + 1) := by
    intro k hk
    rw [hJs (k + 1), hJs k] at hk
    exact hinj _ _ (by rw [← hJs k]; exact hk)
  have hall : ∀ k ≤ n, J k = J (k + 1) := by
    intro k hk
    induction h' : n - k generalizing k with
    | zero =>
      have : k = n := by omega
      subst this
      exact hn (k + 1) (Nat.le_succ k)
    | succ d ih => exact hstep k (ih (k + 1) (by omega) (by omega))
  have h01 : I = I.comap e := hall 0 (Nat.zero_le n)
  calc I.map e = (I.comap e).map e := congrArg (Ideal.map e) h01
    _ = I := Ideal.map_comap_of_surjective e e.surjective I

/-- **Volume 2, Proposition 3.2.10 of the handbook**, for the polynomial ring `K[x_1, ..., x_n]` in characteristic `0`. Let `B · D(I) ⊆ I`, and let `φ` be a `K`-algebra automorphism with `φ(x_i) - x_i ∈ B` for each `i`. Then `φ(I) = I`, and `φ(r) - r ∈ B` for each `r`. -/
theorem map_algEquiv_eq_of_mul_derivIdeal_le [Fintype σ] {I B : Ideal (MvPolynomial σ K)}
    (hB : B * derivIdeal I ≤ I) (φ : MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K)
    (hφ : ∀ i, φ (X i) - X i ∈ B) :
    I.map φ = I ∧ ∀ r, φ r - r ∈ B := by
  have hφeq : ∀ f, φ f = aeval (fun i => X i + (φ (X i) - X i)) f := by
    intro f
    have : (φ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) =
        aeval (fun i => X i + (φ (X i) - X i)) := by
      apply MvPolynomial.algHom_ext; intro i; simp
    exact congrArg (fun g : MvPolynomial σ K →ₐ[K] MvPolynomial σ K => g f) this
  refine ⟨?_, ?_⟩
  · apply map_ringEquiv_eq_of_le (φ : MvPolynomial σ K ≃+* MvPolynomial σ K)
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    show φ f ∈ I
    rw [hφeq]
    have hD : ∀ a f i, f ∈ derivIdeal^[a] I → pderiv i f ∈ derivIdeal^[a + 1] I := by
      intro a f i hf
      rw [Function.iterate_succ_apply']
      exact pderiv_mem_derivIdeal hf i
    exact aeval_add_mem_chain (I := fun a => derivIdeal^[a] I) hD
      (mul_derivIdeal_iterate_succ_le hB) hφ (c := 0) hf
  · intro r
    rw [hφeq]
    induction r using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq =>
      rw [map_add, add_sub_add_comm]; exact add_mem hp hq
    | mul_X p n hp =>
      have : aeval (fun i => X i + (φ (X i) - X i)) (p * X n) - p * X n =
          (aeval (fun i => X i + (φ (X i) - X i)) p - p) * X n +
            aeval (fun i => X i + (φ (X i) - X i)) p * (φ (X n) - X n) := by
        simp only [map_mul, aeval_X]; ring
      rw [this]
      exact add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ (hφ n))

/-- The last step of Volume 2, Corollary 3.2.11 of the handbook, after the choice of the coordinates, for polynomials in characteristic `0`. Let `B · D(I) ⊆ I`, let `c ∈ B`, and let `φ` be a `K`-algebra automorphism with `φ(x_j) = x_j + c` that fixes the other variables. Then `φ(I) = I`, `φ` maps the ideal `(x_j)` to `(x_j + c)`, it maps each ideal `(x_i)` with `i ≠ j` to itself, and `φ(r) - r ∈ B` for each `r`. -/
theorem maximalContact_change [Fintype σ] [DecidableEq σ] {I B : Ideal (MvPolynomial σ K)}
    (hB : B * derivIdeal I ≤ I) {j : σ} {c : MvPolynomial σ K} (hc : c ∈ B)
    (φ : MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K) (hj : φ (X j) = X j + c)
    (hi : ∀ i, i ≠ j → φ (X i) = X i) :
    I.map φ = I ∧ (Ideal.span {X j}).map φ = Ideal.span {X j + c} ∧
      (∀ i, i ≠ j → (Ideal.span {X i}).map φ = Ideal.span {X i}) ∧ ∀ r, φ r - r ∈ B := by
  have hφ : ∀ i, φ (X i) - X i ∈ B := by
    intro i
    by_cases h : i = j
    · subst h; rw [hj, add_sub_cancel_left]; exact hc
    · rw [hi i h, sub_self]; exact B.zero_mem
  obtain ⟨h1, h2⟩ := map_algEquiv_eq_of_mul_derivIdeal_le hB φ hφ
  refine ⟨h1, ?_, ?_, h2⟩
  · rw [Ideal.map_span, Set.image_singleton]; simp [hj]
  · intro i hij
    rw [Ideal.map_span, Set.image_singleton]; simp [hi i hij]

end Main

end Singularity
