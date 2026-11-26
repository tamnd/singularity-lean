/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianCurveRuns

/-!
# Runs on a surface

This file proves that the two examples of Volume 7, Section 3.13 of the handbook are infinite
runs (`RhoStep` at each step). The proofs are symbolic in the exponents.

* Example 3.13.10. The field is `ZMod p` for a prime `p`. The variables `x, y, z` are the
  indices `0, 1, 2` of `Fin 3`, the divisor is `{y, z}` and `g = x^p y^a z^b` with
  `gcd(a, b) = 1`. The origin of the `y`-chart sends `g` to `y^p x^p y^(a+b) z^b`, and the origin
  of the `z`-chart sends `g` to `z^p x^p y^a z^(a+b)`. No cleaning is necessary, and `ρ = p` at
  each point (`rhoStep_surfacePoint_y`, `rhoStep_surfacePoint_z`). From `(a, b) = (1, 1)`, each
  sequence of the two charts is an infinite run, and its points are distinct
  (`surfaceRun_of_charts`). The run where the two charts alternate is `surfaceRun`.
* Example 3.13.11 (Cossart and Piltant, Example 3.18). The field is `ZMod 2`. The variables
  `x_1, x_2, x_3, x_4` are the indices `0, 1, 2, 3` of `Fin 4`, the divisor is `{x_1, x_2}` and
  `g_k = x_2^k (x_2^2 x_3^2 x_4 + x_1^2 x_3)`. The origin of the `x_2`-chart sends `g_k` to
  `x_2^2 g_(k+1)`, and `ρ = 2` at each point (`cpRun`). If `2` divides `k + 1`, the point
  `x_4 = 1` of the `x_2`-chart also gives `g_(k+1)`: the chart adds a square to `x_2^2 g_(k+1)`,
  and the cleaning removes it (`rhoStep_cpPoint_translate`).

The handbook also shows that the run of Example 3.13.10 follows no formal curve. This file does
not prove this statement.

## Main definitions

* `SurfaceRuns.surfacePoint p a b`: the point `({y, z}, x^p y^a z^b)` of Example 3.13.10.
* `SurfaceRuns.surfaceSeq c`: the exponents `(a, b)` of the run of Example 3.13.10 that takes
  the charts `c`.
* `SurfaceRuns.surfaceRunPoint p c k`: the point `k` of this run.
* `SurfaceRuns.cpPoint k`: the point `({x_1, x_2}, g_k)` of Example 3.13.11.

## Main results

* `SurfaceRuns.rhoStep_surfacePoint_y` and `SurfaceRuns.rhoStep_surfacePoint_z`: the two steps
  of Example 3.13.10.
* `SurfaceRuns.surfaceRun_of_charts`: Example 3.13.10, each sequence of the charts is an
  infinite run.
* `SurfaceRuns.surfaceRun`: Example 3.13.10, the run where the charts alternate.
* `SurfaceRuns.rhoStep_cpPoint` and `SurfaceRuns.rhoStep_cpPoint_translate`: the steps of
  Example 3.13.11.
* `SurfaceRuns.cpRun`: Example 3.13.11, the infinite run.

## References

* Volume 7, Section 3.13 of the handbook: Examples 3.13.10 and 3.13.11.
* [CP19] V. Cossart and O. Piltant, Example 3.18.
-/

open MvPolynomial Finsupp

namespace Singularity

namespace SurfaceRuns

/-! ### The order of an ideal given by generators -/

theorem idealOrd_span_eq' {σ R : Type*} [CommSemiring R] {S : Set (MvPolynomial σ R)} {n : ℕ}
    (h : ∀ s ∈ S, (n : ℕ∞) ≤ ord s) {f : MvPolynomial σ R} (hf : f ∈ S) (hfn : ord f = n) :
    idealOrd (Ideal.span S) = n := by
  refine le_antisymm (hfn ▸ idealOrd_le_ord (Ideal.subset_span hf)) ?_
  exact le_idealOrd_iff.mpr (Ideal.span_le.mpr fun s hs => le_ord_iff_mem_pow.mp (h s hs))

/-! ### Example 3.13.10: a run on the surface `x = 0` -/

section Surface

variable (p : ℕ) [Fact p.Prime]

/-- The polynomial `x^p y^a z^b` of Example 3.13.10. -/
noncomputable def surfacePoly (a b : ℕ) : MvPolynomial (Fin 3) (ZMod p) :=
  X 0 ^ p * X 1 ^ a * X 2 ^ b

/-- The point `({y, z}, x^p y^a z^b)` of Example 3.13.10. -/
noncomputable def surfacePoint (a b : ℕ) : Finset (Fin 3) × MvPolynomial (Fin 3) (ZMod p) :=
  ({1, 2}, surfacePoly p a b)

variable {p}

theorem surfacePoly_eq_monomial (a b : ℕ) :
    surfacePoly p a b = monomial (single 0 p + single 1 a + single 2 b) 1 := by
  rw [surfacePoly, X_pow_eq_monomial, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial,
    monomial_mul_monomial, one_mul, one_mul]

theorem surfacePoly_eq_mul (a b : ℕ) :
    surfacePoly p a b = monomial (single 1 a + single 2 b) 1 * X 0 ^ p := by
  have h : (X 1 ^ a * X 2 ^ b : MvPolynomial (Fin 3) (ZMod p)) =
      monomial (single 1 a + single 2 b) 1 := by
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul]
  rw [← h, surfacePoly]
  ring

theorem surface_hr (a b : ℕ) :
    ∀ i, i ∉ ({1, 2} : Finset (Fin 3)) → (single 1 a + single 2 b : Fin 3 →₀ ℕ) i = 0 := by
  intro i hi
  fin_cases i <;> simp_all

theorem surface_hG :
    ∀ i ∈ ({1, 2} : Finset (Fin 3)), ∃ d ∈ (X 0 ^ p : MvPolynomial (Fin 3) (ZMod p)).support,
      d i = 0 := by
  intro i hi
  refine ⟨single 0 p, ?_, ?_⟩
  · rw [X_pow_eq_monomial, support_monomial, ite_eq_right one_ne_zero]
    exact Finset.mem_singleton_self _
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp

theorem divisorExponent_surfacePoly (a b : ℕ) :
    divisorExponent {1, 2} (surfacePoly p a b) = single 1 a + single 2 b := by
  rw [surfacePoly_eq_mul]
  exact KangarooCounterexample.divisorExponent_monomial_mul' (surface_hr a b) surface_hG

theorem residualFactor_surfacePoly (a b : ℕ) :
    residualFactor {1, 2} (surfacePoly p a b) = X 0 ^ p := by
  rw [surfacePoly_eq_mul]
  exact residualFactor_monomial_mul (surface_hr a b) surface_hG

theorem surfacePoly_ne_zero (a b : ℕ) : surfacePoly p a b ≠ 0 := by
  rw [surfacePoly_eq_monomial]
  exact fun h => one_ne_zero (monomial_eq_zero.mp h)

/-- If `p` does not divide both `a` and `b`, then `x^p y^a z^b` is clean. -/
theorem isClean_surfacePoly {a b : ℕ} (h : ¬ (p ∣ a ∧ p ∣ b)) :
    IsClean p (surfacePoly p a b) := by
  intro d hd hall
  rw [surfacePoly_eq_monomial, support_monomial, ite_eq_right one_ne_zero,
    Finset.mem_singleton] at hd
  subst hd
  exact h ⟨by simpa using hall 1, by simpa using hall 2⟩

theorem le_ord_surfacePoly (a b : ℕ) : (p : ℕ∞) ≤ ord (surfacePoly p a b) := by
  rw [surfacePoly, ord_mul, ord_mul, ord_X_pow, ord_X_pow, ord_X_pow, add_assoc]
  exact le_self_add

theorem pderiv_X_zero_pow (i : Fin 3) : pderiv i (X 0 ^ p : MvPolynomial (Fin 3) (ZMod p)) = 0 := by
  rw [Derivation.leibniz_pow, pderiv_X]
  by_cases hi : (0 : Fin 3) = i
  · subst hi
    simp
  · simp [Ne.symm hi]

theorem ord_smul_X_zero_pow {c : ZMod p} (hc : c ≠ 0) :
    ord (c • (X 0 ^ p : MvPolynomial (Fin 3) (ZMod p))) = p := by
  rw [smul_eq_C_mul, ord_mul, ord_C hc, ord_X_pow, zero_add]

/-- If `p` does not divide both `a` and `b`, then `ρ = p` at `({y, z}, x^p y^a z^b)`. -/
theorem logJacobianOrder_surfacePoly {a b : ℕ} (h : ¬ (p ∣ a ∧ p ∣ b)) :
    logJacobianOrder ({1, 2} : Finset (Fin 3)) (surfacePoly p a b) = p := by
  rw [logJacobianOrder, divisorExponent_surfacePoly, residualFactor_surfacePoly,
    residualLogJacobian]
  have hgen : ∀ i : Fin 3, (((single 1 a + single 2 b : Fin 3 →₀ ℕ) i : ℕ) : ZMod p) •
      (X 0 ^ p : MvPolynomial (Fin 3) (ZMod p)) + X i * pderiv i (X 0 ^ p) =
      (((single 1 a + single 2 b : Fin 3 →₀ ℕ) i : ℕ) : ZMod p) • X 0 ^ p := by
    intro i
    rw [pderiv_X_zero_pow, mul_zero, add_zero]
  by_cases ha : p ∣ a
  · have hb : ¬ p ∣ b := fun hb => h ⟨ha, hb⟩
    have hb' : ((b : ℕ) : ZMod p) ≠ 0 := by
      rwa [Ne, ZMod.natCast_eq_zero_iff]
    refine idealOrd_span_eq' ?_ (Or.inl ⟨2, by simp, rfl⟩) ?_
    · rintro s (⟨i, -, rfl⟩ | ⟨i, -, rfl⟩)
      · dsimp only
        rw [hgen]
        exact (ord_X_pow 0 p).ge.trans (le_ord_smul _ _)
      · dsimp only
        rw [pderiv_X_zero_pow, ord_zero]
        exact le_top
    · dsimp only
      rw [hgen]
      simpa using ord_smul_X_zero_pow hb'
  · have ha' : ((a : ℕ) : ZMod p) ≠ 0 := by
      rwa [Ne, ZMod.natCast_eq_zero_iff]
    refine idealOrd_span_eq' ?_ (Or.inl ⟨1, by simp, rfl⟩) ?_
    · rintro s (⟨i, -, rfl⟩ | ⟨i, -, rfl⟩)
      · dsimp only
        rw [hgen]
        exact (ord_X_pow 0 p).ge.trans (le_ord_smul _ _)
      · dsimp only
        rw [pderiv_X_zero_pow, ord_zero]
        exact le_top
    · dsimp only
      rw [hgen]
      simpa using ord_smul_X_zero_pow ha'

theorem not_dvd_and_dvd_of_coprime {a b : ℕ} (h : Nat.Coprime a b) : ¬ (p ∣ a ∧ p ∣ b) := by
  rintro ⟨ha, hb⟩
  have h1 : p ∣ 1 := h ▸ Nat.dvd_gcd ha hb
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h1)

theorem blowupDivisor_surface_y :
    blowupDivisor ({1, 2} : Finset (Fin 3)) 1 (0 : Fin 3 → ZMod p) = {1, 2} := by
  ext i
  fin_cases i <;> simp [blowupDivisor]

theorem blowupDivisor_surface_z :
    blowupDivisor ({1, 2} : Finset (Fin 3)) 2 (0 : Fin 3 → ZMod p) = {1, 2} := by
  ext i
  fin_cases i <;> simp [blowupDivisor]

theorem pointChart_surfacePoly_y (a b : ℕ) :
    pointChart 1 0 (surfacePoly p a b) = X 1 ^ p * surfacePoly p (a + b) b := by
  have hx : pointChart (1 : Fin 3) 0 (X 0 : MvPolynomial (Fin 3) (ZMod p)) = X 1 * X 0 := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  have hz : pointChart (1 : Fin 3) 0 (X 2 : MvPolynomial (Fin 3) (ZMod p)) = X 1 * X 2 := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  simp only [surfacePoly, map_mul, map_pow, hx, hz, pointChart_X_self]
  ring

theorem pointChart_surfacePoly_z (a b : ℕ) :
    pointChart 2 0 (surfacePoly p a b) = X 2 ^ p * surfacePoly p a (a + b) := by
  have hx : pointChart (2 : Fin 3) 0 (X 0 : MvPolynomial (Fin 3) (ZMod p)) = X 2 * X 0 := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  have hy : pointChart (2 : Fin 3) 0 (X 1 : MvPolynomial (Fin 3) (ZMod p)) = X 2 * X 1 := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  simp only [surfacePoly, map_mul, map_pow, hx, hy, pointChart_X_self]
  ring

/-- **The `y`-chart of Example 3.13.10.** If `gcd(a, b) = 1`, the origin of the `y`-chart sends
`x^p y^a z^b` to `y^p x^p y^(a+b) z^b`, no cleaning is necessary, and `ρ = p` at both points. -/
theorem rhoStep_surfacePoint_y {a b : ℕ} (h : Nat.Coprime a b) :
    RhoStep p p (surfacePoint p a b) (surfacePoint p (a + b) b) := by
  have h' : Nat.Coprime (a + b) b := Nat.coprime_add_self_left.mpr h
  refine ⟨1, 0, surfacePoly p (a + b) b, surfacePoly_ne_zero a b,
    isClean_surfacePoly (not_dvd_and_dvd_of_coprime h), le_ord_surfacePoly a b,
    pointChart_surfacePoly_y a b, ?_, logJacobianOrder_surfacePoly (not_dvd_and_dvd_of_coprime h),
    logJacobianOrder_surfacePoly (not_dvd_and_dvd_of_coprime h')⟩
  show ((({1, 2} : Finset (Fin 3)), surfacePoly p (a + b) b) :
      Finset (Fin 3) × MvPolynomial (Fin 3) (ZMod p)) =
    (blowupDivisor ({1, 2} : Finset (Fin 3)) 1 0, cleanPart p (surfacePoly p (a + b) b))
  rw [blowupDivisor_surface_y,
    cleanPart_eq_self (isClean_surfacePoly (not_dvd_and_dvd_of_coprime h'))]

/-- **The `z`-chart of Example 3.13.10.** If `gcd(a, b) = 1`, the origin of the `z`-chart sends
`x^p y^a z^b` to `z^p x^p y^a z^(a+b)`, no cleaning is necessary, and `ρ = p` at both points. -/
theorem rhoStep_surfacePoint_z {a b : ℕ} (h : Nat.Coprime a b) :
    RhoStep p p (surfacePoint p a b) (surfacePoint p a (a + b)) := by
  have h' : Nat.Coprime a (a + b) := Nat.coprime_self_add_right.mpr h
  refine ⟨2, 0, surfacePoly p a (a + b), surfacePoly_ne_zero a b,
    isClean_surfacePoly (not_dvd_and_dvd_of_coprime h), le_ord_surfacePoly a b,
    pointChart_surfacePoly_z a b, ?_, logJacobianOrder_surfacePoly (not_dvd_and_dvd_of_coprime h),
    logJacobianOrder_surfacePoly (not_dvd_and_dvd_of_coprime h')⟩
  show ((({1, 2} : Finset (Fin 3)), surfacePoly p a (a + b)) :
      Finset (Fin 3) × MvPolynomial (Fin 3) (ZMod p)) =
    (blowupDivisor ({1, 2} : Finset (Fin 3)) 2 0, cleanPart p (surfacePoly p a (a + b)))
  rw [blowupDivisor_surface_z,
    cleanPart_eq_self (isClean_surfacePoly (not_dvd_and_dvd_of_coprime h'))]

end Surface

/-- The exponents `(a, b)` of a run of Example 3.13.10. The run starts at `(1, 1)`. At step `k`
it takes the `y`-chart if `c k` is true, and the `z`-chart if not. -/
def surfaceSeq (c : ℕ → Bool) : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | k + 1 =>
    if c k then ((surfaceSeq c k).1 + (surfaceSeq c k).2, (surfaceSeq c k).2)
    else ((surfaceSeq c k).1, (surfaceSeq c k).1 + (surfaceSeq c k).2)

/-- The choice of the charts that alternate: the `y`-chart at the even steps and the `z`-chart at
the odd steps. The exponents are `(1, 1), (2, 1), (2, 3), (5, 3), (5, 8), …`. -/
def alternate (k : ℕ) : Bool := decide (Even k)

theorem surfaceSeq_succ_of_true {c : ℕ → Bool} {k : ℕ} (hk : c k = true) :
    surfaceSeq c (k + 1) = ((surfaceSeq c k).1 + (surfaceSeq c k).2, (surfaceSeq c k).2) := by
  rw [surfaceSeq, ite_eq_left hk]

theorem surfaceSeq_succ_of_false {c : ℕ → Bool} {k : ℕ} (hk : c k = false) :
    surfaceSeq c (k + 1) = ((surfaceSeq c k).1, (surfaceSeq c k).1 + (surfaceSeq c k).2) := by
  rw [surfaceSeq, ite_eq_right (by simp [hk])]

/-- The exponents of a run are coprime and positive. -/
theorem surfaceSeq_spec (c : ℕ → Bool) (k : ℕ) :
    Nat.Coprime (surfaceSeq c k).1 (surfaceSeq c k).2 ∧
      1 ≤ (surfaceSeq c k).1 ∧ 1 ≤ (surfaceSeq c k).2 := by
  induction k with
  | zero => exact ⟨Nat.coprime_one_left 1, le_rfl, le_rfl⟩
  | succ k ih =>
    obtain ⟨h, ha, hb⟩ := ih
    cases hk : c k
    · rw [surfaceSeq_succ_of_false hk]
      exact ⟨Nat.coprime_self_add_right.mpr h, ha, by omega⟩
    · rw [surfaceSeq_succ_of_true hk]
      exact ⟨Nat.coprime_add_self_left.mpr h, by omega, hb⟩

theorem surfaceSeq_sum_lt (c : ℕ → Bool) (k : ℕ) :
    (surfaceSeq c k).1 + (surfaceSeq c k).2 <
      (surfaceSeq c (k + 1)).1 + (surfaceSeq c (k + 1)).2 := by
  obtain ⟨-, ha, hb⟩ := surfaceSeq_spec c k
  cases hk : c k
  · rw [surfaceSeq_succ_of_false hk]
    dsimp only
    omega
  · rw [surfaceSeq_succ_of_true hk]
    dsimp only
    omega

theorem surfaceSeq_injective (c : ℕ → Bool) : Function.Injective (surfaceSeq c) := by
  have hm : StrictMono fun k => (surfaceSeq c k).1 + (surfaceSeq c k).2 :=
    strictMono_nat_of_lt_succ (surfaceSeq_sum_lt c)
  intro k l h
  exact hm.injective (by simp only [h])

section SurfaceRun

variable (p : ℕ) [Fact p.Prime]

/-- The point `P_k = ({y, z}, x^p y^a z^b)` of a run of Example 3.13.10, with
`(a, b) = surfaceSeq c k`. -/
noncomputable def surfaceRunPoint (c : ℕ → Bool) (k : ℕ) :
    Finset (Fin 3) × MvPolynomial (Fin 3) (ZMod p) :=
  surfacePoint p (surfaceSeq c k).1 (surfaceSeq c k).2

variable {p}

theorem rhoStep_surfaceRunPoint (c : ℕ → Bool) (k : ℕ) :
    RhoStep p p (surfaceRunPoint p c k) (surfaceRunPoint p c (k + 1)) := by
  obtain ⟨h, -, -⟩ := surfaceSeq_spec c k
  cases hk : c k
  · rw [surfaceRunPoint, surfaceRunPoint, surfaceSeq_succ_of_false hk]
    exact rhoStep_surfacePoint_z h
  · rw [surfaceRunPoint, surfaceRunPoint, surfaceSeq_succ_of_true hk]
    exact rhoStep_surfacePoint_y h

theorem surfaceRunPoint_injective (c : ℕ → Bool) : Function.Injective (surfaceRunPoint p c) := by
  intro k l h
  have h1 := congrArg (fun P => divisorExponent P.1 P.2 1) h
  have h2 := congrArg (fun P => divisorExponent P.1 P.2 2) h
  simp only [surfaceRunPoint, surfacePoint, divisorExponent_surfacePoly] at h1 h2
  simp at h1 h2
  exact surfaceSeq_injective c (Prod.ext h1 h2)

/-- **Example 3.13.10, each sequence of the charts.** Let `p` be a prime, `Δ = {y, z}` and
`g = x^p y^a z^b`. From `(a, b) = (1, 1)`, each sequence of the `y`-chart and the `z`-chart at
the origin is an infinite run, `ρ = p` at each point, and the points are distinct. -/
theorem surfaceRun_of_charts (c : ℕ → Bool) :
    (∀ k, RhoStep p p (surfaceRunPoint p c k) (surfaceRunPoint p c (k + 1))) ∧
    (∀ k, logJacobianOrder (surfaceRunPoint p c k).1 (surfaceRunPoint p c k).2 = p) ∧
    Function.Injective (surfaceRunPoint p c) :=
  ⟨rhoStep_surfaceRunPoint c,
    fun k => logJacobianOrder_surfacePoly (not_dvd_and_dvd_of_coprime (surfaceSeq_spec c k).1),
    surfaceRunPoint_injective c⟩

/-- **Example 3.13.10** (Volume 7, Section 3.13 of the handbook). Let `p` be a prime, `Δ = {y, z}`
and `g = x^p y^a z^b`. From `(a, b) = (1, 1)`, the `y`-chart and the `z`-chart at the origin
alternate. So `P_0, P_1, P_2, …` is an infinite run, `ρ = p` at each point, and the points are
distinct. -/
theorem surfaceRun :
    (∀ k, RhoStep p p (surfaceRunPoint p alternate k) (surfaceRunPoint p alternate (k + 1))) ∧
    (∀ k, logJacobianOrder (surfaceRunPoint p alternate k).1
      (surfaceRunPoint p alternate k).2 = p) ∧
    Function.Injective (surfaceRunPoint p alternate) :=
  surfaceRun_of_charts alternate

end SurfaceRun

/-- **Example 3.13.10 for `p = 2`.** -/
theorem surfaceRun_two :
    (∀ k, RhoStep 2 2 (surfaceRunPoint 2 alternate k) (surfaceRunPoint 2 alternate (k + 1))) ∧
    (∀ k, logJacobianOrder (surfaceRunPoint 2 alternate k).1
      (surfaceRunPoint 2 alternate k).2 = 2) ∧
    Function.Injective (surfaceRunPoint 2 alternate) :=
  surfaceRun

/-! ### Example 3.13.11: the example of Cossart and Piltant -/

/-- The polynomial ring `𝔽_2[x_1, x_2, x_3, x_4]`. The variable `x_(i+1)` is `X i`. -/
abbrev Poly4 := MvPolynomial (Fin 4) (ZMod 2)

/-- The residual factor `G = x_2^2 x_3^2 x_4 + x_1^2 x_3` of Example 3.13.11. -/
noncomputable def cpG : Poly4 := X 1 ^ 2 * X 2 ^ 2 * X 3 + X 0 ^ 2 * X 2

/-- The polynomial `g_k = x_2^k (x_2^2 x_3^2 x_4 + x_1^2 x_3)` of Example 3.13.11. -/
noncomputable def cpPoly (k : ℕ) : Poly4 := X 1 ^ k * cpG

/-- The point `P_k = ({x_1, x_2}, g_k)` of Example 3.13.11. -/
noncomputable def cpPoint (k : ℕ) : Finset (Fin 4) × Poly4 := ({0, 1}, cpPoly k)

/-- The exponent of `x_2^(k+2) x_3^2 x_4`. -/
noncomputable def cpE1 (k : ℕ) : Fin 4 →₀ ℕ := single 1 (k + 2) + single 2 2 + single 3 1

/-- The exponent of `x_1^2 x_2^k x_3`. -/
noncomputable def cpE2 (k : ℕ) : Fin 4 →₀ ℕ := single 0 2 + single 1 k + single 2 1

theorem cpPoly_eq (k : ℕ) : cpPoly k = monomial (cpE1 k) 1 + monomial (cpE2 k) 1 := by
  simp only [cpPoly, cpG, cpE1, cpE2, X, monomial_pow, monomial_mul_monomial, one_pow, mul_one,
    mul_add]
  refine congrArg₂ (· + ·) (congrArg (monomial · 1) ?_) (congrArg (monomial · 1) ?_) <;>
    ext i <;> fin_cases i <;> simp

theorem cpE2_ne_cpE1 (k l : ℕ) : cpE2 k ≠ cpE1 l := by
  intro h
  have := congrArg (· 0) h
  simp [cpE1, cpE2] at this

theorem coeff_cpPoly_cpE1 (k : ℕ) : (cpPoly k).coeff (cpE1 k) = 1 := by
  rw [cpPoly_eq, coeff_add_apply, coeff_monomial, coeff_monomial, ite_eq_left rfl,
    ite_eq_right (cpE2_ne_cpE1 k k), add_zero]

theorem cpPoly_ne_zero (k : ℕ) : cpPoly k ≠ 0 := by
  intro h
  have := coeff_cpPoly_cpE1 k
  rw [h] at this
  simp at this

theorem isClean_cpPoly (k : ℕ) : IsClean 2 (cpPoly k) := by
  intro d hd hall
  have hc := MvPolynomial.mem_support_iff.mp hd
  rw [cpPoly_eq, coeff_add_apply, coeff_monomial, coeff_monomial] at hc
  by_cases h1 : cpE1 k = d
  · subst h1
    have := hall 3
    simp [cpE1] at this
  · by_cases h2 : cpE2 k = d
    · subst h2
      have := hall 2
      simp [cpE2] at this
    · rw [ite_eq_right h1, ite_eq_right h2, add_zero] at hc
      exact hc rfl

theorem le_ord_cpG : ((3 : ℕ) : ℕ∞) ≤ ord cpG := by
  refine le_ord_add ?_ ?_
  · rw [ord_mul, ord_mul, ord_X_pow, ord_X_pow, ord_X]
    norm_num
  · rw [ord_mul, ord_X_pow, ord_X]
    norm_num

theorem le_ord_cpPoly (k : ℕ) : ((2 : ℕ) : ℕ∞) ≤ ord (cpPoly k) := by
  refine le_trans ?_ (le_ord_mul _ _)
  refine le_trans ?_ le_add_self
  exact le_trans (by norm_num) le_ord_cpG

theorem cpPoly_eq_mul (k : ℕ) : cpPoly k = monomial (single 1 k) 1 * cpG := by
  rw [cpPoly, X_pow_eq_monomial]

theorem cp_hr (k : ℕ) : ∀ i, i ∉ ({0, 1} : Finset (Fin 4)) → (single 1 k : Fin 4 →₀ ℕ) i = 0 := by
  intro i hi
  fin_cases i <;> simp_all

theorem cpG_eq : cpG = monomial (cpE1 0) 1 + monomial (cpE2 0) 1 := by
  have := cpPoly_eq 0
  rwa [cpPoly, pow_zero, one_mul] at this

theorem cp_hG : ∀ i ∈ ({0, 1} : Finset (Fin 4)), ∃ d ∈ cpG.support, d i = 0 := by
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · refine ⟨cpE1 0, MvPolynomial.mem_support_iff.mpr ?_, by simp [cpE1]⟩
    have := coeff_cpPoly_cpE1 0
    rw [cpPoly, pow_zero, one_mul] at this
    rw [this]
    exact one_ne_zero
  · refine ⟨cpE2 0, MvPolynomial.mem_support_iff.mpr ?_, by simp [cpE2]⟩
    rw [cpG_eq, coeff_add_apply, coeff_monomial, coeff_monomial,
      ite_eq_right (cpE2_ne_cpE1 0 0).symm,
      ite_eq_left rfl, zero_add]
    exact one_ne_zero

theorem divisorExponent_cpPoly (k : ℕ) : divisorExponent {0, 1} (cpPoly k) = single 1 k := by
  rw [cpPoly_eq_mul]
  exact KangarooCounterexample.divisorExponent_monomial_mul' (cp_hr k) cp_hG

theorem residualFactor_cpPoly (k : ℕ) : residualFactor {0, 1} (cpPoly k) = cpG := by
  rw [cpPoly_eq_mul]
  exact residualFactor_monomial_mul (cp_hr k) cp_hG

theorem two_poly4 : (2 : Poly4) = 0 := by
  have := CharP.cast_eq_zero Poly4 2
  simpa using this

/-- The derivative `∂_3 G = 2 x_2^2 x_3 x_4 + x_1^2` is `x_1^2`. -/
theorem pderiv_two_cpG : pderiv 2 cpG = X 0 ^ 2 := by
  simp [cpG, Derivation.leibniz, Derivation.leibniz_pow, pderiv_X]
  exact two_poly4

/-- The order `ρ` is `2` at `({x_1, x_2}, g_k)`. The generator `∂_3 G = x_1^2` has the order `2`,
and the order of `G` is `3`. -/
theorem logJacobianOrder_cpPoly (k : ℕ) :
    logJacobianOrder ({0, 1} : Finset (Fin 4)) (cpPoly k) = ((2 : ℕ) : ℕ∞) := by
  rw [logJacobianOrder, divisorExponent_cpPoly, residualFactor_cpPoly, residualLogJacobian]
  refine idealOrd_span_eq' ?_ (Or.inr ⟨2, by simp, rfl⟩) ?_
  · rintro s (⟨i, -, rfl⟩ | ⟨i, -, rfl⟩)
    · exact le_ord_smul_add_X_mul_pderiv ((by norm_num : ((2 : ℕ) : ℕ∞) ≤ 3).trans le_ord_cpG)
        _ i
    · exact le_ord_pderiv le_ord_cpG i
  · dsimp only
    rw [pderiv_two_cpG, ord_X_pow]

theorem blowupDivisor_cp :
    blowupDivisor ({0, 1} : Finset (Fin 4)) 1 (0 : Fin 4 → ZMod 2) = {0, 1} := by
  unfold blowupDivisor
  decide

theorem pointChart_cpPoly (k : ℕ) : pointChart 1 0 (cpPoly k) = X 1 ^ 2 * cpPoly (k + 1) := by
  have h0 : pointChart (1 : Fin 4) 0 (X 0 : Poly4) = X 1 * X 0 := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  have h2 : pointChart (1 : Fin 4) 0 (X 2 : Poly4) = X 1 * X 2 := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  have h3 : pointChart (1 : Fin 4) 0 (X 3 : Poly4) = X 1 * X 3 := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  simp only [cpPoly, cpG, map_add, map_mul, map_pow, h0, h2, h3, pointChart_X_self]
  ring

/-- **One step of the run of Example 3.13.11.** The origin of the `x_2`-chart sends `g_k` to
`x_2^2 g_(k+1)`, no cleaning is necessary, and `ρ = 2` at both points. -/
theorem rhoStep_cpPoint (k : ℕ) : RhoStep 2 2 (cpPoint k) (cpPoint (k + 1)) := by
  refine ⟨1, 0, cpPoly (k + 1), cpPoly_ne_zero k, isClean_cpPoly k, le_ord_cpPoly k,
    pointChart_cpPoly k, ?_, logJacobianOrder_cpPoly k, logJacobianOrder_cpPoly (k + 1)⟩
  show ((({0, 1} : Finset (Fin 4)), cpPoly (k + 1)) : Finset (Fin 4) × Poly4) =
    (blowupDivisor ({0, 1} : Finset (Fin 4)) 1 0, cleanPart 2 (cpPoly (k + 1)))
  rw [blowupDivisor_cp, cleanPart_eq_self (isClean_cpPoly (k + 1))]

/-- The translation `x_4 = 1` of the `x_2`-chart. -/
def cpTranslate : Fin 4 → ZMod 2 := ![0, 0, 0, 1]

theorem blowupDivisor_cp_translate :
    blowupDivisor ({0, 1} : Finset (Fin 4)) 1 cpTranslate = {0, 1} := by
  unfold blowupDivisor cpTranslate
  decide

theorem pointChart_cpPoly_translate (m : ℕ) :
    pointChart 1 cpTranslate (cpPoly (2 * m + 1)) =
      X 1 ^ 2 * (cpPoly (2 * m + 2) + (X 1 ^ (m + 2) * X 2) ^ 2) := by
  have h0 : pointChart (1 : Fin 4) cpTranslate (X 0 : Poly4) = X 1 * X 0 := by
    rw [pointChart_X_of_ne _ (by decide)]
    simp [cpTranslate]
  have h2 : pointChart (1 : Fin 4) cpTranslate (X 2 : Poly4) = X 1 * X 2 := by
    rw [pointChart_X_of_ne _ (by decide)]
    simp [cpTranslate]
  have h3 : pointChart (1 : Fin 4) cpTranslate (X 3 : Poly4) = X 1 * (X 3 + 1) := by
    rw [pointChart_X_of_ne _ (by decide)]
    simp [cpTranslate]
  simp only [cpPoly, cpG, map_add, map_mul, map_pow, h0, h2, h3, pointChart_X_self]
  ring

/-- **A step of Example 3.13.11 with a translation.** If `2` divides `k + 1`, the point `x_4 = 1`
of the `x_2`-chart sends `g_k` to `x_2^2 (g_(k+1) + x_2^(k+3) x_3^2)`. The term
`x_2^(k+3) x_3^2` is a square, and the cleaning removes it. So the new point is `P_(k+1)`, and
`ρ = 2` at both points. -/
theorem rhoStep_cpPoint_translate {k : ℕ} (hk : 2 ∣ k + 1) :
    RhoStep 2 2 (cpPoint k) (cpPoint (k + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
  refine ⟨1, cpTranslate, cpPoly (2 * m + 2) + (X 1 ^ (m + 2) * X 2) ^ 2, cpPoly_ne_zero _,
    isClean_cpPoly _, le_ord_cpPoly _, pointChart_cpPoly_translate m, ?_,
    logJacobianOrder_cpPoly _, logJacobianOrder_cpPoly _⟩
  have hc := cleanPart_add_pow 2 1 (cpPoly (2 * m + 2)) (X 1 ^ (m + 2) * X 2)
  rw [pow_one] at hc
  show ((({0, 1} : Finset (Fin 4)), cpPoly (2 * m + 2)) : Finset (Fin 4) × Poly4) =
    (blowupDivisor ({0, 1} : Finset (Fin 4)) 1 cpTranslate,
      cleanPart 2 (cpPoly (2 * m + 2) + (X 1 ^ (m + 2) * X 2) ^ 2))
  rw [blowupDivisor_cp_translate, hc, cleanPart_eq_self (isClean_cpPoly _)]

theorem cpPoint_injective : Function.Injective cpPoint := by
  intro k l h
  have h1 := congrArg (fun P => divisorExponent P.1 P.2 1) h
  simpa [cpPoint, divisorExponent_cpPoly] using h1

/-- **Example 3.13.11** (Volume 7, Section 3.13 of the handbook, and Cossart and Piltant,
Example 3.18). For `p = 2`, `Δ = {x_1, x_2}` and `g_k = x_2^k (x_2^2 x_3^2 x_4 + x_1^2 x_3)`, the
origin of the `x_2`-chart of the blowup of `P_k` is `P_(k+1)`, and `ρ = 2` at each point. So
`P_0, P_1, P_2, …` is an infinite run, and its points are distinct. -/
theorem cpRun : (∀ k, RhoStep 2 2 (cpPoint k) (cpPoint (k + 1))) ∧
    (∀ k, logJacobianOrder (cpPoint k).1 (cpPoint k).2 = 2) ∧
    Function.Injective cpPoint :=
  ⟨rhoStep_cpPoint, fun k => by exact_mod_cast logJacobianOrder_cpPoly k, cpPoint_injective⟩

end SurfaceRuns

end Singularity
