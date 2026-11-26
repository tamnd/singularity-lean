/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianKangarooCounterexample

/-!
# Runs along a curve

A run is a sequence of points `P_0, P_1, P_2, …` where each `P_{i+1}` comes from `P_i` by a chart
of the blowup of the origin, after the cleaning, and `ρ` stays (`RhoStep`). This file proves that
the two examples of Volume 7, Section 3.12 of the handbook are infinite runs. The field is
`ZMod 2`, so `p = 2`. The variables `x, y, z` are the indices `0, 1, 2` of `Fin 3`. The proofs
are symbolic in `k`.

* Example 3.12.2. The divisor is `{y}` and `g_k = x^4 y^(2k+1) + x^2 y^(3k+1) z^3`. The origin of
  the `y`-chart sends `g_k` to `y^2 g_(k+1)`, and `ρ = 4` at each point (`curveRun`). At the point
  `(0, 1, 0)` of the curve `x = z = 0`, the order `ρ` of `g_0` is also `4`
  (`logJacobianOrder_localPoint_curvePoint`).
* Example 3.12.4. The divisor is `{x, z}` and `g_k = x^(5+3k) y^2 z^3 + x^(10+3k) y^3 z^2`. The
  origin of the `x`-chart sends `g_k` to `x^2 g_(k+1)`, and `ρ = 3` at each point
  (`isolatedRun`). At the point `(1, 0, 0)` of the `x`-axis, the order `ρ` of `g_0` is `2`
  (`logJacobianOrder_localPoint_isolatedPoint`).

The points of a run are distinct, since the exponent of `y` (or of `x`) in `g_k` goes up with `k`.
So the runs are not cycles.

## The point at `a`

The library has no notion of the data at a point `a ≠ 0` of the affine space. This file gives a
simple form of it (`localPoint`). The divisor at `a` is the set of the components `x_i = 0` of
`Δ` with `a_i = 0`. The polynomial at `a` is the clean part of `g(x + a)`. This is the form of
the handbook in the proof of Example 3.12.4, part 4. The form uses only the points of `k^σ`, so
over `ZMod 2` it does not give the isolation statement of Example 3.12.4 over an algebraically
closed field.

## Main definitions

* `localPoint p a P`: the point `P` seen at the point `a`.
* `CurveRuns.curvePoint k`: the point `({y}, g_k)` of Example 3.12.2.
* `CurveRuns.isolatedPoint k`: the point `({x, z}, g_k)` of Example 3.12.4.

## Main results

* `CurveRuns.curveRun`: Example 3.12.2, parts 1 and 2.
* `CurveRuns.logJacobianOrder_localPoint_curvePoint`: Example 3.12.2, part 3, at `(0, 1, 0)`.
* `CurveRuns.isolatedRun`: Example 3.12.4, parts 1 and 2.
* `CurveRuns.logJacobianOrder_localPoint_isolatedPoint`: Example 3.12.4, part 4, at `(1, 0, 0)`.

## References

* Volume 7, Section 3.12 of the handbook: Examples 3.12.2 and 3.12.4.
-/

open MvPolynomial Finsupp

namespace Singularity

section LocalPoint

variable {σ k : Type*} [Field k] [DecidableEq k]

/-- **The point `P = (Δ, g)` seen at the point `a` of `k^σ`.** The divisor is the set of the
components `x_i = 0` of `Δ` that pass through `a`, that is the `i ∈ Δ` with `a_i = 0`. The
polynomial is the clean part of `g(x + a)`. -/
noncomputable def localPoint (p : ℕ) (a : σ → k) (P : Finset σ × MvPolynomial σ k) :
    Finset σ × MvPolynomial σ k :=
  (P.1.filter fun i => a i = 0, cleanPart p (aeval (fun i => X i + C (a i)) P.2))

end LocalPoint

namespace CurveRuns

open KangarooCounterexample

/-! ### Monomials with symbolic exponents -/

theorem X_mul_pderiv_zero_mono (a b c : ℕ) :
    X 0 * pderiv 0 (mono a b c) = (a : Poly) * mono a b c := by
  rw [pderiv_zero_mono]
  rcases a with _ | a
  · simp
  · simp only [mono, Nat.add_sub_cancel]
    push_cast
    ring

theorem X_mul_pderiv_one_mono (a b c : ℕ) :
    X 1 * pderiv 1 (mono a b c) = (b : Poly) * mono a b c := by
  rw [pderiv_one_mono]
  rcases b with _ | b
  · simp
  · simp only [mono, Nat.add_sub_cancel]
    push_cast
    ring

theorem X_mul_pderiv_two_mono (a b c : ℕ) :
    X 2 * pderiv 2 (mono a b c) = (c : Poly) * mono a b c := by
  rw [pderiv_two_mono]
  rcases c with _ | c
  · simp
  · simp only [mono, Nat.add_sub_cancel]
    push_cast
    ring

theorem ord_mono (a b c : ℕ) : ord (mono a b c) = ((a + b + c : ℕ) : ℕ∞) := by
  rw [mono_eq, ord_monomial one_ne_zero, degree_expo]

theorem le_ord_mono {n a b c : ℕ} (h : n ≤ a + b + c) : (n : ℕ∞) ≤ ord (mono a b c) := by
  rw [ord_mono]
  exact_mod_cast h

theorem le_ord_natCast_mul {n : ℕ} {f : Poly} (h : (n : ℕ∞) ≤ ord f) (m : ℕ) :
    (n : ℕ∞) ≤ ord ((m : Poly) * f) :=
  h.trans (le_add_self.trans (le_ord_mul _ _))

theorem isClean_mono_add_mono {a b c a' b' c' : ℕ} (h : ¬ (2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c))
    (h' : ¬ (2 ∣ a' ∧ 2 ∣ b' ∧ 2 ∣ c')) : IsClean 2 (mono a b c + mono a' b' c') := by
  intro d hd hall
  have hc := MvPolynomial.mem_support_iff.mp hd
  rw [coeff_add_apply, coeff_mono, coeff_mono] at hc
  by_cases h1 : d 0 = a ∧ d 1 = b ∧ d 2 = c
  · exact h ⟨h1.1 ▸ hall 0, h1.2.1 ▸ hall 1, h1.2.2 ▸ hall 2⟩
  · by_cases h2 : d 0 = a' ∧ d 1 = b' ∧ d 2 = c'
    · exact h' ⟨h2.1 ▸ hall 0, h2.2.1 ▸ hall 1, h2.2.2 ▸ hall 2⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2),
        add_zero] at hc
      exact hc rfl

theorem coeff_mono_add_mono {a b c a' b' c' : ℕ} (h : ¬ (a = a' ∧ b = b' ∧ c = c')) :
    (mono a b c + mono a' b' c').coeff (expo a b c) = 1 := by
  rw [coeff_add_apply, coeff_mono, coeff_mono]
  simp only [expo_apply_zero, expo_apply_one, expo_apply_two]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
  simp

theorem mono_add_mono_ne_zero {a b c a' b' c' : ℕ} (h : ¬ (a = a' ∧ b = b' ∧ c = c')) :
    mono a b c + mono a' b' c' ≠ 0 := by
  intro h0
  have := coeff_mono_add_mono h
  rw [h0] at this
  simp at this

theorem natCast_two_mul_add_one (k : ℕ) : ((2 * k + 1 : ℕ) : ZMod 2) = 1 := by
  push_cast
  rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]

theorem natCast_two_poly : ((2 : ℕ) : Poly) = 0 := by
  exact_mod_cast num2

theorem natCast_four_poly : ((4 : ℕ) : Poly) = 0 := by
  exact_mod_cast num4

/-! ### Example 3.12.2: a run along the curve `x = z = 0` -/

/-- The polynomial `g_k = x^4 y^(2k+1) + x^2 y^(3k+1) z^3` of Example 3.12.2. -/
noncomputable def curvePoly (k : ℕ) : MvPolynomial (Fin 3) (ZMod 2) :=
  X 0 ^ 4 * X 1 ^ (2 * k + 1) + X 0 ^ 2 * X 1 ^ (3 * k + 1) * X 2 ^ 3

/-- The point `P_k = ({y}, g_k)` of Example 3.12.2. -/
noncomputable def curvePoint (k : ℕ) : Finset (Fin 3) × MvPolynomial (Fin 3) (ZMod 2) :=
  ({1}, curvePoly k)

/-- The residual factor `G_k = x^4 + x^2 y^k z^3` of `g_k = y^(2k+1) G_k`. -/
noncomputable def curveG (k : ℕ) : Poly := mono 4 0 0 + mono 2 k 3

theorem curvePoly_eq (k : ℕ) : curvePoly k = mono 4 (2 * k + 1) 0 + mono 2 (3 * k + 1) 3 := by
  simp only [curvePoly, mono, pow_zero, mul_one]

theorem curvePoly_eq_mul (k : ℕ) :
    curvePoly k = monomial (expo 0 (2 * k + 1) 0) 1 * curveG k := by
  rw [← mono_eq, curvePoly, curveG]
  simp only [mono]
  ring

theorem curveG_support {k : ℕ} :
    ∀ i ∈ ({1} : Finset (Fin 3)), ∃ d ∈ (curveG k).support, d i = 0 := by
  intro i hi
  simp only [Finset.mem_singleton] at hi
  subst hi
  refine ⟨expo 4 0 0, MvPolynomial.mem_support_iff.mpr ?_, by simp⟩
  rw [curveG, coeff_mono_add_mono (by omega)]
  exact one_ne_zero

theorem divisorExponent_curvePoly (k : ℕ) :
    divisorExponent {1} (curvePoly k) = expo 0 (2 * k + 1) 0 := by
  rw [curvePoly_eq_mul]
  exact divisorExponent_monomial_mul' (hr1 _) curveG_support

theorem residualFactor_curvePoly (k : ℕ) : residualFactor {1} (curvePoly k) = curveG k := by
  rw [curvePoly_eq_mul]
  exact residualFactor_monomial_mul (hr1 _) curveG_support

theorem curvePoly_ne_zero (k : ℕ) : curvePoly k ≠ 0 := by
  rw [curvePoly_eq]
  exact mono_add_mono_ne_zero (by omega)

theorem isClean_curvePoly (k : ℕ) : IsClean 2 (curvePoly k) := by
  rw [curvePoly_eq]
  exact isClean_mono_add_mono (by omega) (by omega)

theorem le_ord_curvePoly (k : ℕ) : ((2 : ℕ) : ℕ∞) ≤ ord (curvePoly k) := by
  rw [curvePoly_eq]
  exact le_ord_add (le_ord_mono (by omega)) (le_ord_mono (by omega))

theorem pointChart_curvePoly (k : ℕ) :
    pointChart 1 0 (curvePoly k) = X 1 ^ 2 * curvePoly (k + 1) := by
  have hx : pointChart (1 : Fin 3) 0 (X 0) = (X 1 * X 0 : Poly) := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  have hz : pointChart (1 : Fin 3) 0 (X 2) = (X 1 * X 2 : Poly) := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  simp only [curvePoly, map_add, map_mul, map_pow, hx, hz, pointChart_X_self]
  ring

theorem blowupDivisor_curve :
    blowupDivisor ({1} : Finset (Fin 3)) 1 (0 : Fin 3 → ZMod 2) = {1} := by
  unfold blowupDivisor
  decide

/-- The generator `e_y = (2k+1) G_k + y ∂_y G_k` has order `4`. -/
theorem ord_curve_ey (k : ℕ) :
    ord (((expo 0 (2 * k + 1) 0 1 : ℕ) : ZMod 2) • curveG k + X 1 * pderiv 1 (curveG k)) =
      ((4 : ℕ) : ℕ∞) := by
  rw [expo_apply_one, natCast_two_mul_add_one, one_smul, curveG, map_add, mul_add,
    X_mul_pderiv_one_mono, X_mul_pderiv_one_mono, Nat.cast_zero, zero_mul, zero_add, add_assoc,
    ord_add_of_lt, ord_mono]
  rw [ord_mono]
  exact lt_of_lt_of_le (Nat.cast_lt.mpr (by norm_num : 4 + 0 + 0 < 5))
    (le_ord_add (le_ord_mono (by omega)) (le_ord_natCast_mul (le_ord_mono (by omega)) _))

theorem pderiv_zero_curveG (k : ℕ) : pderiv 0 (curveG k) = 0 := by
  rw [curveG, map_add, pderiv_zero_mono, pderiv_zero_mono, Nat.cast_ofNat, Nat.cast_ofNat, num4,
    num2, zero_mul, zero_mul, add_zero]

theorem logJacobianOrder_curvePoly (k : ℕ) :
    logJacobianOrder ({1} : Finset (Fin 3)) (curvePoly k) = ((4 : ℕ) : ℕ∞) := by
  rw [logJacobianOrder, divisorExponent_curvePoly, residualFactor_curvePoly, residualLogJacobian]
  refine idealOrd_span_eq ?_ (Or.inl ⟨1, by simp, rfl⟩) (ord_curve_ey k)
  rintro s (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
  · simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hi
    subst hi
    exact (ord_curve_ey k).ge
  · have : i = 0 ∨ i = 2 := by
      simp only [Finset.coe_singleton, Set.mem_compl_iff, Set.mem_singleton_iff] at hi
      fin_cases i <;> simp_all
    dsimp only
    rcases this with rfl | rfl
    · rw [pderiv_zero_curveG, ord_zero]
      exact le_top
    · rw [curveG, map_add, pderiv_two_mono, pderiv_two_mono]
      exact le_ord_add (le_ord_natCast_mul (le_ord_mono (by omega)) _)
        (le_ord_natCast_mul (le_ord_mono (by omega)) _)

/-- **One step of the run of Example 3.12.2.** The origin of the `y`-chart sends `g_k` to
`y^2 g_(k+1)`, no cleaning is necessary, and `ρ = 4` at both points. -/
theorem rhoStep_curvePoint (k : ℕ) : RhoStep 2 4 (curvePoint k) (curvePoint (k + 1)) := by
  refine ⟨1, 0, curvePoly (k + 1), curvePoly_ne_zero k, isClean_curvePoly k, le_ord_curvePoly k,
    pointChart_curvePoly k, ?_, logJacobianOrder_curvePoly k, logJacobianOrder_curvePoly (k + 1)⟩
  show ((({1} : Finset (Fin 3)), curvePoly (k + 1)) : Finset (Fin 3) × Poly) =
    (blowupDivisor ({1} : Finset (Fin 3)) 1 0, cleanPart 2 (curvePoly (k + 1)))
  rw [blowupDivisor_curve, cleanPart_eq_self (isClean_curvePoly (k + 1))]

theorem curvePoint_injective : Function.Injective curvePoint := by
  intro k l h
  have h1 := congrArg (fun P => divisorExponent P.1 P.2 1) h
  simp only [curvePoint, divisorExponent_curvePoly, expo_apply_one] at h1
  omega

/-- **Example 3.12.2** (Volume 7, Section 3.12 of the handbook). For `p = 2`, `Δ = {y}` and
`g_k = x^4 y^(2k+1) + x^2 y^(3k+1) z^3`, the origin of the `y`-chart of the blowup of `P_k` is
`P_(k+1)`, and `ρ = 4` at each point. So `P_0, P_1, P_2, …` is an infinite run, and its points
are distinct. -/
theorem curveRun : (∀ k, RhoStep 2 4 (curvePoint k) (curvePoint (k + 1))) ∧
    (∀ k, logJacobianOrder (curvePoint k).1 (curvePoint k).2 = 4) ∧
    Function.Injective curvePoint :=
  ⟨rhoStep_curvePoint, fun k => by exact_mod_cast logJacobianOrder_curvePoly k,
    curvePoint_injective⟩

/-! ### Example 3.12.2 at the point `(0, 1, 0)` of the curve -/

/-- The clean part `x^4 y + x^2 y z^3 + x^2 z^3` of `g_0(x, y + 1, z)`. -/
noncomputable def curveLocal : Poly := poly [(4, 1, 0), (2, 1, 3), (2, 0, 3)]

theorem localPoint_curvePoint :
    localPoint 2 ![0, 1, 0] (curvePoint 0) = ((∅ : Finset (Fin 3)), curveLocal) := by
  have hf : ({1} : Finset (Fin 3)).filter
      (fun i => (![0, 1, 0] : Fin 3 → ZMod 2) i = 0) = ∅ := by
    decide
  have ht : aeval (fun i => X i + C ((![0, 1, 0] : Fin 3 → ZMod 2) i)) (curvePoly 0) =
      curveLocal + mono 2 0 0 ^ 2 ^ 1 := by
    simp only [curvePoly, curveLocal, poly_cons, poly_nil, mono, map_add, map_mul, map_pow,
      aeval_X]
    simp
    ring
  have hc := cleanPart_add_pow 2 1 curveLocal (mono 2 0 0)
  rw [pow_one] at hc
  rw [localPoint, curvePoint, hf, ht, pow_one, hc,
    cleanPart_eq_self (show IsClean 2 curveLocal from isClean_poly _ (by decide))]

theorem curveLocal_eq_mul : curveLocal = monomial 0 1 * curveLocal := by
  rw [← C_apply, map_one, one_mul]

theorem logJacobianOrder_curveLocal :
    logJacobianOrder (∅ : Finset (Fin 3)) curveLocal = ((4 : ℕ) : ℕ∞) := by
  have hr : ∀ i, i ∉ (∅ : Finset (Fin 3)) → (0 : Fin 3 →₀ ℕ) i = 0 := fun _ _ => rfl
  have hG : ∀ i ∈ (∅ : Finset (Fin 3)), ∃ d ∈ curveLocal.support, d i = 0 := by simp
  have hd : divisorExponent ∅ curveLocal = 0 := by
    rw [curveLocal_eq_mul]
    exact divisorExponent_monomial_mul' hr hG
  have hres : residualFactor ∅ curveLocal = curveLocal := by
    conv_lhs => rw [curveLocal_eq_mul]
    exact residualFactor_monomial_mul hr hG
  have h0 : pderiv 0 curveLocal = 0 := by
    simp only [curveLocal, poly_cons, poly_nil, add_zero, map_add, pderiv_zero_mono]
    simp only [mono]
    char2
  have h1 : pderiv 1 curveLocal = poly [(4, 0, 0), (2, 0, 3)] := by
    simp only [curveLocal, poly_cons, poly_nil, add_zero, map_add, pderiv_one_mono]
    simp only [mono]
    char2
  have h2 : pderiv 2 curveLocal = poly [(2, 1, 2), (2, 0, 2)] := by
    simp only [curveLocal, poly_cons, poly_nil, add_zero, map_add, pderiv_two_mono]
    simp only [mono]
    char2
  rw [logJacobianOrder, hd, hres, residualLogJacobian]
  refine idealOrd_span_eq ?_ (Or.inr ⟨1, by simp, rfl⟩) ?_
  · rintro s (⟨i, hi, rfl⟩ | ⟨i, -, rfl⟩)
    · simp at hi
    · dsimp only
      fin_cases i
      · rw [show ((⟨0, by decide⟩ : Fin 3)) = 0 from rfl, h0, ord_zero]
        exact le_top
      · rw [show ((⟨1, by decide⟩ : Fin 3)) = 1 from rfl, h1]
        exact le_ord_poly _ _ (by decide)
      · rw [show ((⟨2, by decide⟩ : Fin 3)) = 2 from rfl, h2]
        exact le_ord_poly _ _ (by decide)
  · dsimp only
    rw [h1]
    exact ord_poly_eq 4 0 0 (by decide) (by decide)

/-- **Example 3.12.2, part 3, at the point `(0, 1, 0)`.** At this point of the curve `x = z = 0`,
the divisor is empty, and the order `ρ` of the clean part of `g_0(x, y + 1, z)` is `4`, as at the
origin. -/
theorem logJacobianOrder_localPoint_curvePoint :
    logJacobianOrder (localPoint 2 ![0, 1, 0] (curvePoint 0)).1
      (localPoint 2 ![0, 1, 0] (curvePoint 0)).2 = 4 := by
  rw [localPoint_curvePoint]
  exact_mod_cast logJacobianOrder_curveLocal

/-! ### Example 3.12.4: a run at an isolated point of the locus of `ρ` -/

/-- The polynomial `g_k = x^(5+3k) y^2 z^3 + x^(10+3k) y^3 z^2` of Example 3.12.4. -/
noncomputable def isolatedPoly (k : ℕ) : MvPolynomial (Fin 3) (ZMod 2) :=
  X 0 ^ (5 + 3 * k) * X 1 ^ 2 * X 2 ^ 3 + X 0 ^ (10 + 3 * k) * X 1 ^ 3 * X 2 ^ 2

/-- The point `P_k = ({x, z}, g_k)` of Example 3.12.4. -/
noncomputable def isolatedPoint (k : ℕ) : Finset (Fin 3) × MvPolynomial (Fin 3) (ZMod 2) :=
  ({0, 2}, isolatedPoly k)

/-- The residual factor `G = y^2 z + x^5 y^3` of `g_k = x^(5+3k) z^2 G`. -/
noncomputable def isolatedG : Poly := mono 0 2 1 + mono 5 3 0

theorem isolatedPoly_eq (k : ℕ) :
    isolatedPoly k = mono (5 + 3 * k) 2 3 + mono (10 + 3 * k) 3 2 := rfl

theorem isolatedPoly_eq_mul (k : ℕ) :
    isolatedPoly k = monomial (expo (5 + 3 * k) 0 2) 1 * isolatedG := by
  rw [← mono_eq, isolatedPoly, isolatedG]
  simp only [mono]
  ring

theorem isolated_hr (k : ℕ) :
    ∀ i, i ∉ ({0, 2} : Finset (Fin 3)) → expo (5 + 3 * k) 0 2 i = 0 := by
  intro i hi
  fin_cases i <;> simp_all

theorem isolatedG_support :
    ∀ i ∈ ({0, 2} : Finset (Fin 3)), ∃ d ∈ isolatedG.support, d i = 0 := by
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · refine ⟨expo 0 2 1, MvPolynomial.mem_support_iff.mpr ?_, by simp⟩
    rw [isolatedG, coeff_mono_add_mono (by omega)]
    exact one_ne_zero
  · refine ⟨expo 5 3 0, MvPolynomial.mem_support_iff.mpr ?_, by simp⟩
    rw [isolatedG, add_comm, coeff_mono_add_mono (by omega)]
    exact one_ne_zero

theorem divisorExponent_isolatedPoly (k : ℕ) :
    divisorExponent {0, 2} (isolatedPoly k) = expo (5 + 3 * k) 0 2 := by
  rw [isolatedPoly_eq_mul]
  exact divisorExponent_monomial_mul' (isolated_hr k) isolatedG_support

theorem residualFactor_isolatedPoly (k : ℕ) :
    residualFactor {0, 2} (isolatedPoly k) = isolatedG := by
  rw [isolatedPoly_eq_mul]
  exact residualFactor_monomial_mul (isolated_hr k) isolatedG_support

theorem isolatedPoly_ne_zero (k : ℕ) : isolatedPoly k ≠ 0 := by
  rw [isolatedPoly_eq]
  exact mono_add_mono_ne_zero (by omega)

theorem isClean_isolatedPoly (k : ℕ) : IsClean 2 (isolatedPoly k) := by
  rw [isolatedPoly_eq]
  exact isClean_mono_add_mono (by omega) (by omega)

theorem le_ord_isolatedPoly (k : ℕ) : ((2 : ℕ) : ℕ∞) ≤ ord (isolatedPoly k) := by
  rw [isolatedPoly_eq]
  exact le_ord_add (le_ord_mono (by omega)) (le_ord_mono (by omega))

theorem pointChart_isolatedPoly (k : ℕ) :
    pointChart 0 0 (isolatedPoly k) = X 0 ^ 2 * isolatedPoly (k + 1) := by
  have hy : pointChart (0 : Fin 3) 0 (X 1) = (X 0 * X 1 : Poly) := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  have hz : pointChart (0 : Fin 3) 0 (X 2) = (X 0 * X 2 : Poly) := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  simp only [isolatedPoly, map_add, map_mul, map_pow, hy, hz, pointChart_X_self]
  ring

theorem blowupDivisor_isolated :
    blowupDivisor ({0, 2} : Finset (Fin 3)) 0 (0 : Fin 3 → ZMod 2) = {0, 2} := by
  unfold blowupDivisor
  decide

theorem le_ord_isolatedG : ((3 : ℕ) : ℕ∞) ≤ ord isolatedG :=
  le_ord_add (le_ord_mono (by omega)) (le_ord_mono (by omega))

/-- The generator `e_z = 2 G + z ∂_z G = y^2 z` has order `3`. -/
theorem ord_isolated_ez (k : ℕ) :
    ord (((expo (5 + 3 * k) 0 2 2 : ℕ) : ZMod 2) • isolatedG + X 2 * pderiv 2 isolatedG) =
      ((3 : ℕ) : ℕ∞) := by
  rw [expo_apply_two, show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_smul, zero_add, isolatedG,
    map_add, mul_add, X_mul_pderiv_two_mono, X_mul_pderiv_two_mono, Nat.cast_one, one_mul,
    Nat.cast_zero, zero_mul, add_zero, ord_mono]

theorem logJacobianOrder_isolatedPoly (k : ℕ) :
    logJacobianOrder ({0, 2} : Finset (Fin 3)) (isolatedPoly k) = ((3 : ℕ) : ℕ∞) := by
  rw [logJacobianOrder, divisorExponent_isolatedPoly, residualFactor_isolatedPoly,
    residualLogJacobian]
  refine idealOrd_span_eq ?_ (Or.inl ⟨2, by simp, rfl⟩) (ord_isolated_ez k)
  rintro s (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
  · simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hi
    dsimp only
    rcases hi with rfl | rfl
    · refine le_ord_add (le_ord_isolatedG.trans (le_ord_smul _ _)) ?_
      rw [isolatedG, map_add, mul_add, X_mul_pderiv_zero_mono, X_mul_pderiv_zero_mono]
      exact le_ord_add (le_ord_natCast_mul (le_ord_mono (by omega)) _)
        (le_ord_natCast_mul (le_ord_mono (by omega)) _)
    · exact (ord_isolated_ez k).ge
  · have : i = 1 := by
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_compl_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hi
      fin_cases i <;> simp_all
    subst this
    dsimp only
    rw [isolatedG, map_add, pderiv_one_mono, pderiv_one_mono, natCast_two_poly, zero_mul,
      zero_add]
    exact le_ord_natCast_mul (le_ord_mono (by omega)) _

/-- **One step of the run of Example 3.12.4.** The origin of the `x`-chart sends `g_k` to
`x^2 g_(k+1)`, no cleaning is necessary, and `ρ = 3` at both points. -/
theorem rhoStep_isolatedPoint (k : ℕ) :
    RhoStep 2 3 (isolatedPoint k) (isolatedPoint (k + 1)) := by
  refine ⟨0, 0, isolatedPoly (k + 1), isolatedPoly_ne_zero k, isClean_isolatedPoly k,
    le_ord_isolatedPoly k, pointChart_isolatedPoly k, ?_, logJacobianOrder_isolatedPoly k,
    logJacobianOrder_isolatedPoly (k + 1)⟩
  show ((({0, 2} : Finset (Fin 3)), isolatedPoly (k + 1)) : Finset (Fin 3) × Poly) =
    (blowupDivisor ({0, 2} : Finset (Fin 3)) 0 0, cleanPart 2 (isolatedPoly (k + 1)))
  rw [blowupDivisor_isolated, cleanPart_eq_self (isClean_isolatedPoly (k + 1))]

theorem isolatedPoint_injective : Function.Injective isolatedPoint := by
  intro k l h
  have h1 := congrArg (fun P => divisorExponent P.1 P.2 0) h
  simp only [isolatedPoint, divisorExponent_isolatedPoly, expo_apply_zero] at h1
  omega

/-- **Example 3.12.4** (Volume 7, Section 3.12 of the handbook). For `p = 2`, `Δ = {x, z}` and
`g_k = x^(5+3k) y^2 z^3 + x^(10+3k) y^3 z^2`, the origin of the `x`-chart of the blowup of `P_k`
is `P_(k+1)`, and `ρ = 3` at each point. So `P_0, P_1, P_2, …` is an infinite run, and its points
are distinct. -/
theorem isolatedRun : (∀ k, RhoStep 2 3 (isolatedPoint k) (isolatedPoint (k + 1))) ∧
    (∀ k, logJacobianOrder (isolatedPoint k).1 (isolatedPoint k).2 = 3) ∧
    Function.Injective isolatedPoint :=
  ⟨rhoStep_isolatedPoint, fun k => by exact_mod_cast logJacobianOrder_isolatedPoly k,
    isolatedPoint_injective⟩

/-! ### Example 3.12.4 at the point `(1, 0, 0)` of the `x`-axis -/

/-- The polynomial `g_0(x + 1, y, z)`. It is clean. -/
noncomputable def isolatedLocal : Poly :=
  poly [(5, 2, 3), (4, 2, 3), (1, 2, 3), (0, 2, 3), (10, 3, 2), (8, 3, 2), (2, 3, 2), (0, 3, 2)]

/-- The residual factor of `isolatedLocal = z^2 G'`. -/
noncomputable def isolatedLocalG : Poly :=
  poly [(5, 2, 1), (4, 2, 1), (1, 2, 1), (0, 2, 1), (10, 3, 0), (8, 3, 0), (2, 3, 0), (0, 3, 0)]

theorem add_one_pow_five : ((X 0 + 1) ^ 5 : Poly) = X 0 ^ 5 + X 0 ^ 4 + X 0 + 1 := by
  char2

theorem localPoint_isolatedPoint :
    localPoint 2 ![1, 0, 0] (isolatedPoint 0) = (({2} : Finset (Fin 3)), isolatedLocal) := by
  have hf : ({0, 2} : Finset (Fin 3)).filter
      (fun i => (![1, 0, 0] : Fin 3 → ZMod 2) i = 0) = {2} := by
    decide
  have ht : aeval (fun i => X i + C ((![1, 0, 0] : Fin 3 → ZMod 2) i)) (isolatedPoly 0) =
      isolatedLocal := by
    simp only [isolatedPoly, isolatedLocal, poly_cons, poly_nil, mono, map_add, map_mul, map_pow,
      aeval_X]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, map_one, map_zero, add_zero, mul_zero]
    rw [show (X 0 + 1 : Poly) ^ (10 + 3 * 0) = ((X 0 + 1) ^ 5) ^ 2 by ring,
      show (X 0 + 1 : Poly) ^ (5 + 3 * 0) = (X 0 + 1) ^ 5 by ring, add_one_pow_five]
    char2
  rw [localPoint, isolatedPoint, hf, ht,
    cleanPart_eq_self (show IsClean 2 isolatedLocal from isClean_poly _ (by decide))]

theorem isolatedLocal_eq_mul : isolatedLocal = monomial (expo 0 0 2) 1 * isolatedLocalG := by
  rw [← mono_eq]
  simp only [isolatedLocal, isolatedLocalG, poly_cons, poly_nil, mono]
  ring

theorem logJacobianOrder_isolatedLocal :
    logJacobianOrder ({2} : Finset (Fin 3)) isolatedLocal = ((2 : ℕ) : ℕ∞) := by
  have hr : ∀ i, i ∉ ({2} : Finset (Fin 3)) → expo 0 0 2 i = 0 := by
    intro i hi
    fin_cases i <;> simp_all
  have hG : ∀ i ∈ ({2} : Finset (Fin 3)), ∃ d ∈ isolatedLocalG.support, d i = 0 := by
    intro i hi
    simp only [Finset.mem_singleton] at hi
    subst hi
    exact ⟨expo 0 3 0, MvPolynomial.mem_support_iff.mpr (coeff_poly_ne_zero (by decide)),
      by simp⟩
  have hd : divisorExponent {2} isolatedLocal = expo 0 0 2 := by
    rw [isolatedLocal_eq_mul]
    exact divisorExponent_monomial_mul' hr hG
  have hres : residualFactor {2} isolatedLocal = isolatedLocalG := by
    rw [isolatedLocal_eq_mul]
    exact residualFactor_monomial_mul hr hG
  have h2 : ((expo 0 0 2 2 : ℕ) : ZMod 2) • isolatedLocalG + X 2 * pderiv 2 isolatedLocalG =
      poly [(5, 2, 1), (4, 2, 1), (1, 2, 1), (0, 2, 1)] := by
    simp only [expo_apply_two, isolatedLocalG, poly_cons, poly_nil, add_zero, map_add,
      pderiv_two_mono, smul_eq_C_mul, map_natCast]
    simp only [mono]
    char2
  have h0 : pderiv 0 isolatedLocalG = poly [(4, 2, 1), (0, 2, 1)] := by
    simp only [isolatedLocalG, poly_cons, poly_nil, add_zero, map_add, pderiv_zero_mono]
    simp only [mono]
    char2
  have h1 : pderiv 1 isolatedLocalG = poly [(10, 2, 0), (8, 2, 0), (2, 2, 0), (0, 2, 0)] := by
    simp only [isolatedLocalG, poly_cons, poly_nil, add_zero, map_add, pderiv_one_mono]
    simp only [mono]
    char2
  rw [logJacobianOrder, hd, hres, residualLogJacobian]
  refine idealOrd_span_eq ?_ (Or.inr ⟨1, by simp, rfl⟩) ?_
  · rintro s (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hi
      subst hi
      dsimp only
      rw [h2]
      exact le_ord_poly _ _ (by decide)
    · have : i = 0 ∨ i = 1 := by
        simp only [Finset.coe_singleton, Set.mem_compl_iff, Set.mem_singleton_iff] at hi
        fin_cases i <;> simp_all
      dsimp only
      rcases this with rfl | rfl
      · rw [h0]
        exact le_ord_poly _ _ (by decide)
      · rw [h1]
        exact le_ord_poly _ _ (by decide)
  · dsimp only
    rw [h1]
    exact ord_poly_eq 0 2 0 (by decide) (by decide)

/-- **Example 3.12.4, part 4, at the point `(1, 0, 0)`.** At this point of the `x`-axis, the
divisor is `{z}`, the polynomial `g_0(x + 1, y, z)` is clean, and its order `ρ` is `2`. At the
origin `ρ = 3`. -/
theorem logJacobianOrder_localPoint_isolatedPoint :
    logJacobianOrder (localPoint 2 ![1, 0, 0] (isolatedPoint 0)).1
      (localPoint 2 ![1, 0, 0] (isolatedPoint 0)).2 = 2 := by
  rw [localPoint_isolatedPoint]
  exact_mod_cast logJacobianOrder_isolatedLocal

end CurveRuns

end Singularity
