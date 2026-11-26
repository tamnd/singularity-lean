/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Div
import Singularity.Algebra.HilbertSamuel

/-!
# The order of the cusp

This file proves Volume 1, Example 3.2.6 of the handbook. Let `k` be a field, let `A = k[x, y]`, let `𝔫 = (x, y)` be the ideal of the origin and let `R = A_𝔫` with maximal ideal `𝔪`. Let `f = y^2 - x^3`. Then `f ∈ 𝔪^2` and `f ∉ 𝔪^3`, so `ord_𝔪(f) = 2` (`Singularity.Example.order_cusp`).

In Lean, `x` is `X 0` and `y` is `X 1`, and `𝔫` is the kernel of the constant coefficient (`originIdeal`), that is, the polynomials that vanish at the origin. The order is `Singularity.Algebra.order` of `Singularity/Algebra/HilbertSamuel.lean`.

The proof that `f ∉ 𝔪^3` is not the proof of the handbook. Assume `s f ∈ 𝔫^3` for some `s ∉ 𝔫`. The substitution `x ↦ 0`, `y ↦ t` maps `𝔫` into `(t)` and `f` to `t^2`. So `t^3` divides `t^2 s(0, t)`, and `s(0, 0) = 0`. This is not possible.
-/

namespace Singularity.Example

open MvPolynomial

variable (k : Type*) [Field k]

/-- The ideal of the origin of `k[x, y]`: the kernel of the constant coefficient. -/
noncomputable def originIdeal : Ideal (MvPolynomial (Fin 2) k) :=
  RingHom.ker (MvPolynomial.constantCoeff (σ := Fin 2) (R := k))

instance originIdeal_isMaximal : (originIdeal k).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun a => ⟨MvPolynomial.C a, by simp⟩

variable {k}

theorem mem_originIdeal {g : MvPolynomial (Fin 2) k} :
    g ∈ originIdeal k ↔ constantCoeff g = 0 :=
  RingHom.mem_ker

theorem X_mem_originIdeal (i : Fin 2) : (X i : MvPolynomial (Fin 2) k) ∈ originIdeal k := by
  simp [mem_originIdeal]

/-- The substitution `x ↦ 0`, `y ↦ t` from `k[x, y]` to `k[t]`. -/
noncomputable def substXZero : MvPolynomial (Fin 2) k →+* Polynomial k :=
  eval₂Hom Polynomial.C ![0, Polynomial.X]

theorem eval_zero_substXZero (g : MvPolynomial (Fin 2) k) :
    (substXZero g).eval 0 = constantCoeff g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [substXZero]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
    obtain rfl | rfl : n = 0 ∨ n = 1 := by fin_cases n <;> simp
    · simp [substXZero]
    · simp [substXZero]

theorem map_originIdeal_le :
    (originIdeal k).map substXZero ≤ Ideal.span {(Polynomial.X : Polynomial k)} := by
  rw [Ideal.map_le_iff_le_comap]
  intro g hg
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, Polynomial.X_dvd_iff,
    Polynomial.coeff_zero_eq_eval_zero, eval_zero_substXZero]
  exact mem_originIdeal.mp hg

/-- The polynomial `f = y^2 - x^3` of the cusp. -/
noncomputable def cuspEq : MvPolynomial (Fin 2) k := X 1 ^ 2 - X 0 ^ 3

theorem cuspEq_mem_sq : cuspEq ∈ originIdeal k ^ 2 := by
  refine sub_mem (Ideal.pow_mem_pow (X_mem_originIdeal 1) 2) ?_
  exact Ideal.pow_le_pow_right (by norm_num) (Ideal.pow_mem_pow (X_mem_originIdeal 0) 3)

theorem substXZero_cuspEq : substXZero (cuspEq : MvPolynomial (Fin 2) k) = Polynomial.X ^ 2 := by
  rw [cuspEq, map_sub, map_pow, map_pow]
  simp [substXZero]

/-- Let `s ∉ 𝔫`. Then `s f ∉ 𝔫^3`. -/
theorem mul_cuspEq_not_mem_cube {s : MvPolynomial (Fin 2) k} (hs : s ∉ originIdeal k) :
    s * cuspEq ∉ originIdeal k ^ 3 := by
  intro h
  have h1 : substXZero (s * cuspEq) ∈ Ideal.span {(Polynomial.X : Polynomial k) ^ 3} := by
    rw [← Ideal.span_singleton_pow]
    refine Ideal.pow_right_mono map_originIdeal_le 3 ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ h
  rw [Ideal.mem_span_singleton, map_mul, substXZero_cuspEq,
    show (Polynomial.X : Polynomial k) ^ 3 = Polynomial.X * Polynomial.X ^ 2 by ring] at h1
  have h2 := (mul_dvd_mul_iff_right (pow_ne_zero 2 (Polynomial.X_ne_zero (R := k)))).mp h1
  rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero, eval_zero_substXZero] at h2
  exact hs (mem_originIdeal.mpr h2)

/-- The order of the cusp (Volume 1, Example 3.2.6 of the handbook). Let `R` be the local ring of `k[x, y]` at the origin, with maximal ideal `𝔪`. Then the order of `f = y^2 - x^3` is `ord_𝔪(f) = 2`. -/
theorem order_cusp :
    Singularity.Algebra.order (IsLocalRing.maximalIdeal (Localization.AtPrime (originIdeal k)))
      (algebraMap (MvPolynomial (Fin 2) k) (Localization.AtPrime (originIdeal k)) cuspEq) = 2 := by
  set R := Localization.AtPrime (originIdeal k)
  have hmax : IsLocalRing.maximalIdeal R =
      (originIdeal k).map (algebraMap (MvPolynomial (Fin 2) k) R) :=
    (IsLocalization.AtPrime.map_eq_maximalIdeal (originIdeal k) R).symm
  have h2 : algebraMap (MvPolynomial (Fin 2) k) R cuspEq ∈ IsLocalRing.maximalIdeal R ^ 2 := by
    rw [hmax, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ cuspEq_mem_sq
  have h3 : algebraMap (MvPolynomial (Fin 2) k) R cuspEq ∉ IsLocalRing.maximalIdeal R ^ 3 := by
    rw [hmax, ← Ideal.map_pow]
    intro h
    obtain ⟨x, h⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (M := (originIdeal k).primeCompl) (S := R)).mp h
    rw [← map_mul] at h
    obtain ⟨c, hc⟩ :=
      (IsLocalization.eq_iff_exists (M := (originIdeal k).primeCompl) (S := R)).mp h
    have hcs : (c : MvPolynomial (Fin 2) k) * x.2 ∉ originIdeal k :=
      (originIdeal k).primeCompl.mul_mem c.2 x.2.2
    apply mul_cuspEq_not_mem_cube hcs
    have hx : ((c : MvPolynomial (Fin 2) k) * (x.2 : MvPolynomial (Fin 2) k)) *
        (cuspEq : MvPolynomial (Fin 2) k) =
        (c : MvPolynomial (Fin 2) k) * (x.1 : MvPolynomial (Fin 2) k) := by
      rw [← hc]
      ring
    rw [hx]
    exact Ideal.mul_mem_left _ _ x.1.2
  have hle2 : ((2 : ℕ) : ℕ∞) ≤ Singularity.Algebra.order (IsLocalRing.maximalIdeal R)
      (algebraMap (MvPolynomial (Fin 2) k) R cuspEq) := Singularity.Algebra.le_order_of_mem h2
  have hlt3 : Singularity.Algebra.order (IsLocalRing.maximalIdeal R)
      (algebraMap (MvPolynomial (Fin 2) k) R cuspEq) < ((3 : ℕ) : ℕ∞) :=
    not_le.mp fun h => h3 (Singularity.Algebra.le_order_iff.mp h)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt3)
  rw [← hm] at hle2 hlt3 ⊢
  norm_cast at hle2 hlt3 ⊢
  omega

end Singularity.Example
