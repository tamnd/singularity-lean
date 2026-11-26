/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# The normalization of the cusp, the node and the Whitney umbrella

This file proves the algebra of Volume 1, Examples 2.5.8, 2.5.9 and 2.5.10 of the handbook. Each of the three rings is a subalgebra `B` of a polynomial ring `C` over a field `k`, and the polynomial ring is the normalization of `B`.

The general step is `isFractionRing_of_mul_mem` and `isIntegralClosure_of_isIntegral`. Let `C` be a domain with field of fractions `K` and let `B` be a subalgebra of `C`. If there is `c ≠ 0` in `C` with `c C ⊆ B`, then `K` is also the field of fractions of `B`. If `C` is integrally closed and integral over `B`, then `C` is the integral closure of `B` in `K`.

* `Singularity.Example.cusp_normalization`: the ring `A = k[t^2, t^3]` has the field of fractions `k(t)`, and `k[t]` is the integral closure of `A` in `k(t)` (Volume 1, Example 2.5.8 of the handbook).
* `Singularity.Example.mem_cusp_iff`: `p ∈ k[t^2, t^3]` if and only if the coefficient of `t` in `p` is `0`.
* `Singularity.Example.mul_mem_cusp_iff`: the conductor of `A` in `k[t]` is `t^2 k[t]`.
* `Singularity.Example.node_normalization`: the same for `A = k[t^2 - 1, t^3 - t]` (Volume 1, Example 2.5.9 of the handbook).
* `Singularity.Example.mem_node_iff` and `Singularity.Example.mul_mem_node_iff`: if `2 ≠ 0` in `k`, then `p ∈ A` if and only if `p(1) = p(-1)`, and the conductor of `A` in `k[t]` is `(t^2 - 1) k[t]`.
* `Singularity.Example.umbrella_normalization`: the same for `A = k[y, yt, t^2] ⊆ k[y, t]` (Volume 1, Example 2.5.10 of the handbook). Here `y k[y, t]` is in the conductor (`umbrella_mul_mem`).

The handbook defines the node and the Whitney umbrella as quotients of a polynomial ring, and it shows that the quotients are isomorphic to these subalgebras. This file starts from the subalgebras, so it does not prove the computation of the kernels.
-/

namespace Singularity.Example

section General

variable {R C K : Type*} [CommRing R] [CommRing C] [IsDomain C] [Algebra R C] [Field K]
  [Algebra C K] [IsFractionRing C K]

/-- Let `C` be a domain with field of fractions `K`, and let `B` be a subalgebra of `C`. If there is `c ≠ 0` in `C` with `c C ⊆ B`, then `K` is the field of fractions of `B`. -/
theorem isFractionRing_of_mul_mem (B : Subalgebra R C) {c : C} (hc : c ≠ 0)
    (hcB : ∀ g : C, c * g ∈ B) : IsFractionRing B K := by
  have hinj : Function.Injective (algebraMap B K) := by
    rw [Subalgebra.algebraMap_eq]
    exact (IsFractionRing.injective C K).comp Subtype.val_injective
  have : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).mpr hinj
  refine IsFractionRing.of_field B K fun z => ?_
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := C) z
  refine ⟨⟨c * x, hcB x⟩, ⟨c * y, hcB y⟩, ?_⟩
  simp only [Subalgebra.algebraMap_mk, map_mul]
  rw [mul_div_mul_left _ _ ((map_ne_zero_iff _ (IsFractionRing.injective C K)).mpr hc)]

/-- Let `C` be an integrally closed domain with field of fractions `K`, and let `B` be a subalgebra of `C` such that `C` is integral over `B`. Then `C` is the integral closure of `B` in `K`. -/
theorem isIntegralClosure_of_isIntegral [IsIntegrallyClosed C] (B : Subalgebra R C)
    [Algebra.IsIntegral B C] : IsIntegralClosure C B K where
  algebraMap_injective := IsFractionRing.injective C K
  isIntegral_iff {x} := by
    constructor
    · intro hx
      exact IsIntegrallyClosed.isIntegral_iff.mp (hx.tower_top (A := C))
    · rintro ⟨y, rfl⟩
      exact (Algebra.IsIntegral.isIntegral (R := B) y).map (IsScalarTower.toAlgHom B C K)

/-- An element of a subalgebra is integral over it. -/
theorem isIntegral_of_mem (B : Subalgebra R C) {x : C} (hx : x ∈ B) : IsIntegral B x := by
  simpa using isIntegral_algebraMap (R := B) (A := C) (x := ⟨x, hx⟩)

end General

section Polynomial

open Polynomial

variable {k : Type*} [Field k]

theorem C_mem (B : Subalgebra k k[X]) (a : k) : C a ∈ B := by
  rw [← Polynomial.algebraMap_eq]
  exact B.algebraMap_mem a

/-- Let `B` be a subalgebra of `k[t]` that contains `c k[t]` for some `c ≠ 0`, and let `t` be integral over `B`. Then `B` has the field of fractions `k(t)`, and `k[t]` is the integral closure of `B` in `k(t)`: the normalization of `B` is `k[t]`. -/
theorem polynomial_normalization (B : Subalgebra k k[X]) {c : k[X]} (hc : c ≠ 0)
    (hcB : ∀ g : k[X], c * g ∈ B) (hX : IsIntegral B (X : k[X])) :
    IsFractionRing B (RatFunc k) ∧ IsIntegralClosure k[X] B (RatFunc k) := by
  have : Algebra.IsIntegral B k[X] := by
    constructor
    intro p
    refine Polynomial.induction_on p (fun a => isIntegral_of_mem B (C_mem B a))
      (fun p q hp hq => hp.add hq) (fun n a h => ?_)
    rw [pow_succ, ← mul_assoc]
    exact h.mul hX
  exact ⟨isFractionRing_of_mul_mem B hc hcB, isIntegralClosure_of_isIntegral B⟩

/-! ### The cusp -/

variable (k) in
/-- The ring `k[t^2, t^3]` of the cusp, as a subalgebra of `k[t]`. -/
noncomputable def cusp : Subalgebra k k[X] := Algebra.adjoin k {X ^ 2, X ^ 3}

theorem X_sq_mem_cusp : (X ^ 2 : k[X]) ∈ cusp k := by
  unfold cusp
  exact Algebra.subset_adjoin (by simp)

theorem X_cube_mem_cusp : (X ^ 3 : k[X]) ∈ cusp k := by
  unfold cusp
  exact Algebra.subset_adjoin (by simp)

theorem X_sq_mul_X_pow_mem_cusp : ∀ n : ℕ, (X ^ 2 * X ^ n : k[X]) ∈ cusp k
  | 0 => by simpa using X_sq_mem_cusp
  | 1 => by
      rw [← pow_add]
      exact X_cube_mem_cusp
  | n + 2 => by
      rw [pow_add X n 2, ← mul_assoc]
      exact mul_mem (X_sq_mul_X_pow_mem_cusp n) X_sq_mem_cusp

/-- The ideal `t^2 k[t]` is in `k[t^2, t^3]`. -/
theorem X_sq_mul_mem_cusp (g : k[X]) : X ^ 2 * g ∈ cusp k := by
  refine Polynomial.induction_on' g (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [mul_add]
    exact add_mem hp hq
  · rw [← C_mul_X_pow_eq_monomial, mul_left_comm]
    exact mul_mem (C_mem _ a) (X_sq_mul_X_pow_mem_cusp n)

theorem coeff_one_mul (p q : k[X]) :
    (p * q).coeff 1 = p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0 := by
  rw [coeff_mul, show (1 : ℕ) = 0 + 1 from rfl, Finset.Nat.sum_antidiagonal_succ]
  simp

variable (k) in
/-- The polynomials without a term in `t`. -/
noncomputable def coeffOneZero : Subalgebra k k[X] where
  carrier := {p | p.coeff 1 = 0}
  mul_mem' {p q} hp hq := by
    simp only [Set.mem_setOf_eq] at hp hq ⊢
    rw [coeff_one_mul, hp, hq]
    ring
  add_mem' {p q} hp hq := by
    simp only [Set.mem_setOf_eq] at hp hq ⊢
    rw [coeff_add, hp, hq, add_zero]
  algebraMap_mem' a := by
    simp [Polynomial.algebraMap_eq, coeff_C]

theorem mem_coeffOneZero {p : k[X]} : p ∈ coeffOneZero k ↔ p.coeff 1 = 0 :=
  Iff.rfl

/-- A polynomial is in `k[t^2, t^3]` if and only if its coefficient of `t` is `0`. -/
theorem mem_cusp_iff {p : k[X]} : p ∈ cusp k ↔ p.coeff 1 = 0 := by
  constructor
  · intro hp
    have hle : cusp k ≤ coeffOneZero k := by
      unfold cusp
      refine Algebra.adjoin_le ?_
      rintro _ (rfl | rfl) <;> simp [mem_coeffOneZero, coeff_X_pow]
    exact mem_coeffOneZero.mp (hle hp)
  · intro hp
    have hdvd : X ^ 2 ∣ p - C (p.coeff 0) := by
      rw [X_pow_dvd_iff]
      intro d hd
      interval_cases d <;> simp [hp, coeff_C]
    obtain ⟨q, hq⟩ := hdvd
    rw [show p = C (p.coeff 0) + X ^ 2 * q by rw [← hq]; ring]
    exact add_mem (C_mem _ _) (X_sq_mul_mem_cusp q)

/-- The element `t` is not in `k[t^2, t^3]`. -/
theorem X_not_mem_cusp : (X : k[X]) ∉ cusp k := by
  simp [mem_cusp_iff]

/-- The conductor of `k[t^2, t^3]` in `k[t]` is `t^2 k[t]` (Volume 1, Example 2.5.8 of the handbook). An element `g` of `k[t]` satisfies `g k[t] ⊆ k[t^2, t^3]` if and only if `t^2` divides `g`. -/
theorem mul_mem_cusp_iff (g : k[X]) : (∀ p : k[X], g * p ∈ cusp k) ↔ X ^ 2 ∣ g := by
  constructor
  · intro h
    have h1 : g.coeff 1 = 0 := by simpa [mem_cusp_iff] using h 1
    have h0 : g.coeff 0 = 0 := by
      have := mem_cusp_iff.mp (h X)
      have h' : (g * X).coeff 1 = g.coeff 0 := Polynomial.coeff_mul_X g 0
      rw [h'] at this
      exact this
    rw [X_pow_dvd_iff]
    intro d hd
    interval_cases d
    · exact h0
    · exact h1
  · rintro ⟨q, rfl⟩ p
    rw [mul_assoc]
    exact X_sq_mul_mem_cusp _

/-- The normalization of the cusp (Volume 1, Example 2.5.8 of the handbook). Let `A = k[t^2, t^3]`. Then the field of fractions of `A` is `k(t)`, and `k[t]` is the integral closure of `A` in `k(t)`. So the normalization of `A` is `k[t]`. -/
theorem cusp_normalization :
    IsFractionRing (cusp k) (RatFunc k) ∧ IsIntegralClosure k[X] (cusp k) (RatFunc k) :=
  polynomial_normalization (cusp k) (pow_ne_zero 2 X_ne_zero) X_sq_mul_mem_cusp
    (IsIntegral.of_pow two_pos (isIntegral_of_mem _ X_sq_mem_cusp))

/-! ### The node -/

variable (k) in
/-- The ring `k[t^2 - 1, t^3 - t]` of the node, as a subalgebra of `k[t]`. -/
noncomputable def node : Subalgebra k k[X] := Algebra.adjoin k {X ^ 2 - 1, X ^ 3 - X}

theorem x_mem_node : (X ^ 2 - 1 : k[X]) ∈ node k := by
  unfold node
  exact Algebra.subset_adjoin (by simp)

theorem y_mem_node : (X ^ 3 - X : k[X]) ∈ node k := by
  unfold node
  exact Algebra.subset_adjoin (by simp)

theorem x_mul_X_pow_mem_node : ∀ n : ℕ, ((X ^ 2 - 1) * X ^ n : k[X]) ∈ node k
  | 0 => by simpa using x_mem_node
  | 1 => by
      rw [show ((X ^ 2 - 1) * X ^ 1 : k[X]) = X ^ 3 - X by ring]
      exact y_mem_node
  | n + 2 => by
      rw [show ((X ^ 2 - 1) * X ^ (n + 2) : k[X]) = (1 + (X ^ 2 - 1)) * ((X ^ 2 - 1) * X ^ n) by
        ring]
      exact mul_mem (add_mem (one_mem _) x_mem_node) (x_mul_X_pow_mem_node n)

/-- The ideal `(t^2 - 1) k[t]` is in `k[t^2 - 1, t^3 - t]`. -/
theorem x_mul_mem_node (g : k[X]) : (X ^ 2 - 1) * g ∈ node k := by
  refine Polynomial.induction_on' g (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [mul_add]
    exact add_mem hp hq
  · rw [← C_mul_X_pow_eq_monomial, mul_left_comm]
    exact mul_mem (C_mem _ a) (x_mul_X_pow_mem_node n)

/-- The normalization of the node (Volume 1, Example 2.5.9 of the handbook). Let `A = k[t^2 - 1, t^3 - t]`. Then the field of fractions of `A` is `k(t)`, and `k[t]` is the integral closure of `A` in `k(t)`. -/
theorem node_normalization :
    IsFractionRing (node k) (RatFunc k) ∧ IsIntegralClosure k[X] (node k) (RatFunc k) := by
  refine polynomial_normalization (node k) (c := X ^ 2 - 1) ?_ x_mul_mem_node ?_
  · intro h
    have := congrArg (Polynomial.eval 0) h
    simp at this
  · refine IsIntegral.of_pow two_pos (isIntegral_of_mem _ ?_)
    rw [show (X ^ 2 : k[X]) = (X ^ 2 - 1) + 1 by ring]
    exact add_mem x_mem_node (one_mem _)

/-- A polynomial with roots `1` and `-1` is divisible by `t^2 - 1`, when `2 ≠ 0`. -/
theorem X_sq_sub_one_dvd (h2 : (2 : k) ≠ 0) {q : k[X]} (h1 : q.eval 1 = 0)
    (hm : q.eval (-1) = 0) : X ^ 2 - 1 ∣ q := by
  obtain ⟨r, hr⟩ := dvd_iff_isRoot.mpr h1
  have hr' : r.eval (-1) = 0 := by
    rw [hr] at hm
    simp only [eval_mul, eval_sub, eval_X, eval_C] at hm
    have h : (-1 - 1 : k) ≠ 0 := by
      intro h
      apply h2
      linear_combination -h
    exact (mul_eq_zero.mp hm).resolve_left h
  obtain ⟨s, hs⟩ := dvd_iff_isRoot.mpr hr'
  refine ⟨s, ?_⟩
  rw [hr, hs]
  simp only [map_one, map_neg]
  ring

/-- If `2 ≠ 0` in `k`, a polynomial `p` is in `k[t^2 - 1, t^3 - t]` if and only if `p(1) = p(-1)`. -/
theorem mem_node_iff (h2 : (2 : k) ≠ 0) {p : k[X]} : p ∈ node k ↔ p.eval 1 = p.eval (-1) := by
  constructor
  · intro hp
    have hle : node k ≤ AlgHom.equalizer (Polynomial.aeval (R := k) (1 : k))
        (Polynomial.aeval (R := k) (-1 : k)) := by
      unfold node
      refine Algebra.adjoin_le ?_
      rintro _ (rfl | rfl) <;>
        simp only [SetLike.mem_coe, AlgHom.mem_equalizer, map_sub, map_pow, Polynomial.aeval_X,
          map_one] <;> ring
    have := (AlgHom.mem_equalizer _ _ _).mp (hle hp)
    simpa using this
  · intro hp
    have hdvd : X ^ 2 - 1 ∣ p - C (p.eval 1) := by
      refine X_sq_sub_one_dvd h2 ?_ ?_
      · simp
      · simp [hp]
    obtain ⟨q, hq⟩ := hdvd
    rw [show p = C (p.eval 1) + (X ^ 2 - 1) * q by rw [← hq]; ring]
    exact add_mem (C_mem _ _) (x_mul_mem_node q)

/-- The conductor of `k[t^2 - 1, t^3 - t]` in `k[t]` is `(t^2 - 1) k[t]`, when `2 ≠ 0` in `k` (Volume 1, Example 2.5.9 of the handbook). -/
theorem mul_mem_node_iff (h2 : (2 : k) ≠ 0) (g : k[X]) :
    (∀ p : k[X], g * p ∈ node k) ↔ X ^ 2 - 1 ∣ g := by
  constructor
  · intro h
    have e1 : g.eval 1 = g.eval (-1) := by simpa using (mem_node_iff h2).mp (h 1)
    have e2 : g.eval 1 = -g.eval (-1) := by simpa using (mem_node_iff h2).mp (h X)
    have h1 : g.eval 1 = 0 := by
      have : (2 : k) * g.eval 1 = 0 := by linear_combination e1 + e2
      exact (mul_eq_zero.mp this).resolve_left h2
    exact X_sq_sub_one_dvd h2 h1 (by rw [← e1, h1])
  · rintro ⟨q, rfl⟩ p
    rw [mul_assoc]
    exact x_mul_mem_node _

end Polynomial

/-! ### The Whitney umbrella -/

section Umbrella

open MvPolynomial

variable (k : Type*) [Field k]

/-- The ring `k[y, yt, t^2]` of the Whitney umbrella, as a subalgebra of `k[y, t]`. The variable `y` is `X 0` and the variable `t` is `X 1`. -/
noncomputable def umbrella : Subalgebra k (MvPolynomial (Fin 2) k) :=
  Algebra.adjoin k {X 0, X 0 * X 1, X 1 ^ 2}

variable {k}

theorem y_mem_umbrella : (X 0 : MvPolynomial (Fin 2) k) ∈ umbrella k := by
  unfold umbrella
  exact Algebra.subset_adjoin (by simp)

theorem yt_mem_umbrella : (X 0 * X 1 : MvPolynomial (Fin 2) k) ∈ umbrella k := by
  unfold umbrella
  exact Algebra.subset_adjoin (by simp)

theorem t_sq_mem_umbrella : (X 1 ^ 2 : MvPolynomial (Fin 2) k) ∈ umbrella k := by
  unfold umbrella
  exact Algebra.subset_adjoin (by simp)

theorem C_mem_umbrella (a : k) : (MvPolynomial.C a : MvPolynomial (Fin 2) k) ∈ umbrella k := by
  rw [← MvPolynomial.algebraMap_eq]
  exact (umbrella k).algebraMap_mem a

theorem umbrella_mul_mem_aux (g : MvPolynomial (Fin 2) k) :
    X 0 * g ∈ umbrella k ∧ X 0 * X 1 * g ∈ umbrella k := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    refine ⟨?_, ?_⟩
    · rw [mul_comm]
      exact mul_mem (C_mem_umbrella a) y_mem_umbrella
    · rw [mul_comm]
      exact mul_mem (C_mem_umbrella a) yt_mem_umbrella
  | add p q hp hq =>
    rw [mul_add, mul_add]
    exact ⟨add_mem hp.1 hq.1, add_mem hp.2 hq.2⟩
  | mul_X p n hp =>
    obtain rfl | rfl : n = 0 ∨ n = 1 := by fin_cases n <;> simp
    · refine ⟨?_, ?_⟩
      · rw [show X 0 * (p * X 0) = X 0 * p * X 0 by ring]
        exact mul_mem hp.1 y_mem_umbrella
      · rw [show X 0 * X 1 * (p * X 0) = X 0 * X 1 * p * X 0 by ring]
        exact mul_mem hp.2 y_mem_umbrella
    · refine ⟨?_, ?_⟩
      · rw [show X 0 * (p * X 1) = X 0 * X 1 * p by ring]
        exact hp.2
      · rw [show X 0 * X 1 * (p * X 1) = X 0 * p * X 1 ^ 2 by ring]
        exact mul_mem hp.1 t_sq_mem_umbrella

/-- The ideal `y k[y, t]` is in `k[y, yt, t^2]`, so it is in the conductor (Volume 1, Example 2.5.10 of the handbook). -/
theorem umbrella_mul_mem (g : MvPolynomial (Fin 2) k) : X 0 * g ∈ umbrella k :=
  (umbrella_mul_mem_aux g).1

instance : Algebra.IsIntegral (umbrella k) (MvPolynomial (Fin 2) k) := by
  constructor
  intro p
  induction p using MvPolynomial.induction_on with
  | C a => exact isIntegral_of_mem _ (C_mem_umbrella a)
  | add p q hp hq => exact hp.add hq
  | mul_X p n hp =>
    refine hp.mul ?_
    obtain rfl | rfl : n = 0 ∨ n = 1 := by fin_cases n <;> simp
    · exact isIntegral_of_mem _ y_mem_umbrella
    · exact IsIntegral.of_pow two_pos (isIntegral_of_mem _ t_sq_mem_umbrella)

/-- The normalization of the Whitney umbrella (Volume 1, Example 2.5.10 of the handbook). Let `A = k[y, yt, t^2] ⊆ k[y, t]`. Then `A` and `k[y, t]` have the same field of fractions `K`, and `k[y, t]` is the integral closure of `A` in `K`. So the normalization of `A` is the plane. -/
theorem umbrella_normalization :
    IsFractionRing (umbrella k) (FractionRing (MvPolynomial (Fin 2) k)) ∧
      IsIntegralClosure (MvPolynomial (Fin 2) k) (umbrella k)
        (FractionRing (MvPolynomial (Fin 2) k)) :=
  ⟨isFractionRing_of_mul_mem (umbrella k) (X_ne_zero 0) umbrella_mul_mem,
    isIntegralClosure_of_isIntegral (umbrella k)⟩

end Umbrella

end Singularity.Example
